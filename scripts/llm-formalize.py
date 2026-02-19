#!/usr/bin/env python3
"""
llm-formalize.py
Generate Lean 4 formalizations from theorem candidates
"""

import argparse
import json
import re

try:
    from mlx_lm import load, generate
    MLX_AVAILABLE = True
except ImportError:
    MLX_AVAILABLE = False

# Prompt template for Lean formalization
LEAN_FORMALIZATION_PROMPT = """You are an expert Lean 4 proof engineer. Your task is to write a complete, compilable Lean 4 formalization of the following mathematical theorem.

THEOREM TO FORMALIZE:
Name: {name}
Statement: {statement}
Mathematical Objects: {objects}
Difficulty: {difficulty}
Hints: {hints}

LEAN 4 FORMALIZATION REQUIREMENTS:
1. Use proper Lean 4 syntax with mathlib4 imports
2. Include all necessary imports at the top
3. State the theorem clearly with proper types
4. Provide a proof using appropriate tactics
5. Add docstrings and comments explaining the mathematics
6. Make sure the code is syntactically correct Lean 4

MATHLIB4 IMPORTS YOU CAN USE:
- import Mathlib (general mathematics)
- import Mathlib.Data.Nat.Basic (natural numbers)
- import Mathlib.Data.Nat.Prime (prime numbers)
- import Mathlib.Data.Real.Basic (real numbers)
- import Mathlib.Algebra.Group.Basic (group theory)
- import Mathlib.Combinatorics.SimpleGraph.Basic (graph theory)
- import Mathlib.NumberTheory.Divisors (number theory)

RESPONSE FORMAT:
Provide ONLY the Lean 4 code, wrapped in a markdown code block:

```lean4
import Mathlib

/-
{name}

{statement}

This theorem states that...

Proof approach:
1. First we establish...
2. Then we apply...
-/

theorem {theorem_name} : 
  -- Formal statement here
  := by
  -- Proof tactics here
  sorry -- Replace with actual proof
```

Important:
- Use `sorry` as a placeholder for unfinished proofs
- Make sure all types are explicitly declared
- Use mathlib4 lemmas when available
- Keep proofs simple but rigorous
- If the theorem is too complex, formalize a simplified version"""

def generate_lean_code(candidate, model=None, tokenizer=None, attempts=3):
    """Generate Lean 4 code for a theorem candidate"""
    
    # Sanitize theorem name for Lean
    theorem_name = re.sub(r'[^a-zA-Z0-9]', '_', candidate.get('name', 'theorem'))
    theorem_name = theorem_name[:50]  # Limit length
    if theorem_name[0].isdigit():
        theorem_name = 'thm_' + theorem_name
    
    prompt = LEAN_FORMALIZATION_PROMPT.format(
        name=candidate.get('name', 'Unknown Theorem'),
        statement=candidate.get('statement', ''),
        objects=', '.join(candidate.get('objects', [])),
        difficulty=candidate.get('difficulty', 'Medium'),
        hints=candidate.get('formalization_hints', ''),
        theorem_name=theorem_name
    )
    
    for attempt in range(attempts):
        try:
            if MLX_AVAILABLE and model is not None:
                response = generate(
                    model,
                    tokenizer,
                    prompt=prompt,
                    max_tokens=4096,
                    temp=0.2  # Lower temp for more precise code
                )
            else:
                # Fallback: generate template code
                return generate_template_code(candidate, theorem_name)
            
            # Extract Lean code from markdown
            code_match = re.search(r'```lean4?\s*(.*?)\s*```', response, re.DOTALL)
            if code_match:
                return code_match.group(1).strip()
            else:
                # Try without language tag
                code_match = re.search(r'```\s*(import.*)', response, re.DOTALL)
                if code_match:
                    return code_match.group(1).strip()
                
        except Exception as e:
            print(f"Attempt {attempt + 1} failed: {e}")
            if attempt == attempts - 1:
                return generate_template_code(candidate, theorem_name)
    
    return generate_template_code(candidate, theorem_name)

def generate_template_code(candidate, theorem_name):
    """Generate a template Lean file when LLM fails"""
    
    name = candidate.get('name', 'Unknown Theorem')
    statement = candidate.get('statement', '')
    objects = candidate.get('objects', [])
    
    # Determine imports based on objects
    imports = ["import Mathlib"]
    if any('prime' in obj.lower() for obj in objects):
        imports.append("import Mathlib.Data.Nat.Prime")
    if any('graph' in obj.lower() for obj in objects):
        imports.append("import Mathlib.Combinatorics.SimpleGraph.Basic")
    if any('real' in obj.lower() for obj in objects):
        imports.append("import Mathlib.Data.Real.Basic")
    
    imports_str = '\n'.join(imports)
    
    code = f"""{imports_str}

/-
{name}

Statement: {statement}

Mathematical objects: {', '.join(objects)}

This is a template generated for the theorem formalization.
The actual formalization requires careful analysis of the paper.
-/

-- TODO: Replace with proper formalization
theorem {theorem_name} : True := by
  trivial
"""
    
    return code

def main():
    parser = argparse.ArgumentParser(description="Generate Lean 4 formalizations")
    parser.add_argument("--candidate", required=True, help="JSON string with candidate info")
    parser.add_argument("--output", required=True, help="Output .lean file")
    parser.add_argument("--attempts", type=int, default=3, help="Number of attempts")
    parser.add_argument("--model", default="mlx-community/Qwen2.5-7B-Instruct-4bit",
                       help="MLX model to use")
    
    args = parser.parse_args()
    
    # Parse candidate
    candidate = json.loads(args.candidate)
    
    print(f"Formalizing: {candidate.get('name', 'Unknown')}")
    
    # Load model
    model = None
    tokenizer = None
    if MLX_AVAILABLE:
        try:
            print("Loading model...")
            model, tokenizer = load(args.model)
        except Exception as e:
            print(f"Model load failed: {e}")
    
    # Generate code
    code = generate_lean_code(candidate, model, tokenizer, args.attempts)
    
    # Write output
    with open(args.output, 'w') as f:
        f.write(code)
    
    print(f"✓ Generated {args.output}")

if __name__ == "__main__":
    main()
