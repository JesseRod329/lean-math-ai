#!/usr/bin/env python3
"""
llm-formalize-v2.py
Generate REAL Lean 4 formalizations from theorem candidates
Uses better models and improved prompting
"""

import argparse
import json
import re
import os

# Try different LLM backends
try:
    from mlx_lm import load, generate
    MLX_AVAILABLE = True
except ImportError:
    MLX_AVAILABLE = False

try:
    from openai import OpenAI
    OPENAI_AVAILABLE = True
except ImportError:
    OPENAI_AVAILABLE = False

try:
    import anthropic
    ANTHROPIC_AVAILABLE = True
except ImportError:
    ANTHROPIC_AVAILABLE = False

# Enhanced prompt for better formalization
LEAN_PROVER_PROMPT = """You are an expert mathematician and Lean 4 proof engineer. 

Your task: Write a complete, rigorous, compilable Lean 4 proof of the following theorem.

=== THEOREM INFORMATION ===
Name: {name}
Statement: {statement}
Mathematical Objects: {objects}
Difficulty: {difficulty}
Paper: {paper_title}
Category: {category}

=== LEAN 4 REQUIREMENTS ===
1. Write a REAL theorem statement (not `True`)
2. Use appropriate types from mathlib4
3. Provide a working proof with tactics
4. If you can't prove it fully, use `sorry` but write the correct statement
5. Add helpful comments explaining the proof strategy

=== MATHLIB4 REFERENCES ===
Graph theory: import Mathlib.Combinatorics.SimpleGraph.Basic
Number theory: import Mathlib.Data.Nat.Prime, Mathlib.NumberTheory.Divisors
Analysis: import Mathlib.Data.Real.Basic, Mathlib.Topology.Basic
Algebra: import Mathlib.Algebra.Group.Basic, Mathlib.LinearAlgebra.Matrix

=== EXAMPLE OUTPUT FORMAT ===
```lean4
import Mathlib
import Mathlib.Combinatorics.SimpleGraph.Basic

/-
Theorem: Every connected graph with n vertices has at least n-1 edges.

This is a fundamental result in graph theory.
-

-- The theorem statement
example (V : Type) [Fintype V] (G : SimpleGraph V) :
    G.edgeSet.ncard ≥ Fintype.card V - 1 := by
  sorry -- Proof goes here
```

=== YOUR TASK ===
Provide ONLY the Lean 4 code. Do not explain. Do not apologize. Just write valid Lean 4.

Write a theorem with the ACTUAL mathematical content, not a placeholder."""

def extract_lean_code(text):
    """Extract Lean code from various formats"""
    patterns = [
        r'```lean4\s*(.*?)\s*```',
        r'```lean\s*(.*?)\s*```',
        r'```\s*(import.*?)\s*```',
    ]
    
    for pattern in patterns:
        match = re.search(pattern, text, re.DOTALL)
        if match:
            return match.group(1).strip()
    
    # If no code blocks, look for import statements
    if 'import' in text:
        lines = text.split('\n')
        code_lines = []
        in_code = False
        for line in lines:
            if line.strip().startswith('import') or in_code:
                in_code = True
                code_lines.append(line)
        if code_lines:
            return '\n'.join(code_lines)
    
    return None

def generate_with_openai(prompt, model="gpt-4o"):
    """Use OpenAI API"""
    if not OPENAI_AVAILABLE:
        return None
    
    api_key = os.environ.get('OPENAI_API_KEY')
    if not api_key:
        print("⚠️  OPENAI_API_KEY not set")
        return None
    
    try:
        client = OpenAI(api_key=api_key)
        response = client.chat.completions.create(
            model=model,
            messages=[
                {"role": "system", "content": "You are an expert Lean 4 proof engineer."},
                {"role": "user", "content": prompt}
            ],
            temperature=0.1,
            max_tokens=4096
        )
        return response.choices[0].message.content
    except Exception as e:
        print(f"OpenAI error: {e}")
        return None

def generate_with_anthropic(prompt, model="claude-3-5-sonnet-20241022"):
    """Use Anthropic Claude"""
    if not ANTHROPIC_AVAILABLE:
        return None
    
    api_key = os.environ.get('ANTHROPIC_API_KEY')
    if not api_key:
        print("⚠️  ANTHROPIC_API_KEY not set")
        return None
    
    try:
        client = anthropic.Anthropic(api_key=api_key)
        response = client.messages.create(
            model=model,
            max_tokens=4096,
            messages=[{"role": "user", "content": prompt}]
        )
        return response.content[0].text
    except Exception as e:
        print(f"Anthropic error: {e}")
        return None

def generate_with_mlx(prompt, model_path):
    """Use local MLX model"""
    if not MLX_AVAILABLE:
        return None
    
    try:
        print(f"Loading {model_path}...")
        model, tokenizer = load(model_path)
        
        response = generate(
            model,
            tokenizer,
            prompt=prompt,
            max_tokens=4096
        )
        return response
    except Exception as e:
        print(f"MLX error: {e}")
        return None

def generate_improved_code(candidate, model_path=None, attempts=3):
    """Generate better Lean 4 code"""
    
    # Sanitize theorem name
    theorem_name = re.sub(r'[^a-zA-Z0-9]', '_', candidate.get('name', 'theorem'))
    theorem_name = theorem_name[:50]
    if theorem_name[0].isdigit():
        theorem_name = 'thm_' + theorem_name
    
    # Build enhanced prompt
    prompt = LEAN_PROVER_PROMPT.format(
        name=candidate.get('name', 'Unknown'),
        statement=candidate.get('statement', ''),
        objects=', '.join(candidate.get('objects', [])),
        difficulty=candidate.get('difficulty', 'Medium'),
        paper_title=candidate.get('source_paper', {}).get('title', 'Unknown'),
        category=', '.join(candidate.get('source_paper', {}).get('categories', []))
    )
    
    # Try different backends in order of quality
    backends = []
    
    # Check which backends are available
    if OPENAI_AVAILABLE and os.environ.get('OPENAI_API_KEY'):
        backends.append(('OpenAI GPT-4o', lambda p: generate_with_openai(p)))
    
    if ANTHROPIC_AVAILABLE and os.environ.get('ANTHROPIC_API_KEY'):
        backends.append(('Claude 3.5', lambda p: generate_with_anthropic(p)))
    
    if MLX_AVAILABLE and model_path:
        backends.append(('Local MLX', lambda p: generate_with_mlx(p, model_path)))
    
    # Try each backend
    for backend_name, backend_fn in backends:
        for attempt in range(attempts):
            try:
                print(f"  Trying {backend_name} (attempt {attempt + 1}/{attempts})...")
                response = backend_fn(prompt)
                
                if response:
                    code = extract_lean_code(response)
                    if code and 'theorem' in code.lower():
                        # Validate it's not just a template
                        if 'True := by' not in code or 'sorry' in code:
                            print(f"  ✓ Generated with {backend_name}")
                            return code
            except Exception as e:
                print(f"  ✗ {backend_name} failed: {e}")
                continue
    
    # Fallback: generate improved template
    print("  ⚠️  All backends failed, using improved template")
    return generate_improved_template(candidate, theorem_name)

def generate_improved_template(candidate, theorem_name):
    """Generate a better template with actual structure"""
    
    name = candidate.get('name', 'Unknown')
    statement = candidate.get('statement', '')
    objects = candidate.get('objects', [])
    paper = candidate.get('source_paper', {})
    
    # Determine appropriate imports and structure
    imports = ["import Mathlib"]
    theorem_body = ""
    
    if any('graph' in obj.lower() for obj in objects):
        imports.append("import Mathlib.Combinatorics.SimpleGraph.Basic")
        imports.append("import Mathlib.Combinatorics.SimpleGraph.Connectivity")
        theorem_body = """
-- Define the graph property from the paper
variable {{V : Type}} [Fintype V] [DecidableEq V]

/-- 
TODO: Formalize the exact statement from:
{title}
by {authors}
-
theorem {name} (G : SimpleGraph V) :
    -- Add formal statement here based on paper analysis
    True := by
  -- Proof requires understanding the paper's main result
  sorry
""".format(
            title=paper.get('title', 'Unknown'),
            authors=', '.join(paper.get('authors', [])[:2]),
            name=theorem_name
        )
    
    elif any('prime' in obj.lower() for obj in objects):
        imports.append("import Mathlib.Data.Nat.Prime")
        imports.append("import Mathlib.NumberTheory.Divisors")
        theorem_body = """
/--
TODO: Formalize from:
{title}
by {authors}
-
theorem {name} (n : ℕ) :
    -- Add number theory statement here
    True := by
  -- Proof requires analyzing the arithmetic function
  sorry
""".format(
            title=paper.get('title', 'Unknown'),
            authors=', '.join(paper.get('authors', [])[:2]),
            name=theorem_name
        )
    else:
        theorem_body = f"""
/-
TODO: Formalize the theorem from:
{paper.get('title', 'Unknown')}

Original statement: {statement}

Reference: arXiv:{paper.get('id', 'unknown')}
-
theorem {theorem_name} :
    -- Formal statement needed
    True := by
  sorry
"""
    
    imports_str = '\n'.join(imports)
    
    return f"""{imports_str}

/-
{name}

Statement: {statement}

Mathematical objects: {', '.join(objects)}
Source: {paper.get('title', 'Unknown')}
arXiv: {paper.get('id', 'unknown')}

Status: Template - requires manual formalization
The paper's main result needs to be carefully extracted and translated to Lean 4.
This template provides the structure; the actual formalization requires:
1. Reading the paper's definitions carefully
2. Translating the statement to Lean 4 types
3. Implementing the proof strategy
-

{theorem_body}
"""

def main():
    parser = argparse.ArgumentParser(description="Generate improved Lean 4 formalizations")
    parser.add_argument("--candidate", required=True, help="JSON string with candidate info")
    parser.add_argument("--output", required=True, help="Output .lean file")
    parser.add_argument("--attempts", type=int, default=3, help="Number of attempts")
    parser.add_argument("--model", default="mlx-community/DeepSeek-Coder-V2-Lite-Instruct-4bit",
                       help="MLX model to use")
    parser.add_argument("--backend", choices=['auto', 'openai', 'anthropic', 'mlx'], 
                       default='auto', help="LLM backend to use")
    
    args = parser.parse_args()
    
    # Parse candidate
    candidate = json.loads(args.candidate)
    print(f"Formalizing: {candidate.get('name', 'Unknown')}")
    
    # Generate improved code
    code = generate_improved_code(candidate, args.model, args.attempts)
    
    # Write output
    with open(args.output, 'w') as f:
        f.write(code)
    
    print(f"✓ Generated {args.output}")

if __name__ == "__main__":
    main()
