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
import sys

# Add scripts dir to path for importing search module
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

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

Your task: Write a complete, rigorous, compilable Lean 4 formalization of the following theorem.

=== THEOREM INFORMATION ===
Name: {name}
Statement: {statement}
Mathematical Objects: {objects}
Difficulty: {difficulty}
Paper: {paper_title}
Category: {category}

=== PAPER ABSTRACT ===
{abstract_excerpt}

=== CRITICAL LEAN 4 SYNTAX RULES ===
You MUST write valid Lean 4 syntax. NEVER use Lean 3 syntax.

WRONG (Lean 3 — DO NOT USE):
  theorem foo : P := begin sorry end
  theorem foo : P := by {{ sorry }}

CORRECT (Lean 4 — USE THIS):
  theorem foo : P := by sorry
  theorem foo : P := by
    sorry

Other critical rules:
- The theorem's TYPE must be a proposition (e.g., `n > 0`, `∃ x, P x`), NOT `Prop` itself
- WRONG: `theorem foo : Prop := by sorry`  (Prop is not a proposition)
- CORRECT: `theorem foo : n > 0 := by sorry`
- WRONG: `theorem foo : False := by sorry`  (unprovable)
- Always start with `import Mathlib`
- Use `by` for tactic blocks, `where` for term-mode definitions
- Do NOT generate repetitive placeholder hypotheses

=== LEAN 4 REQUIREMENTS ===
1. Write a REAL theorem statement (NOT `True`, NOT a placeholder)
2. Use appropriate types from mathlib4
3. Provide a working proof with tactics if possible
4. If you can't prove it fully, use `sorry` but write the CORRECT statement
5. The theorem statement must reflect the actual mathematical content from the paper

=== MATHLIB4 REFERENCES ===
Graph theory: import Mathlib.Combinatorics.SimpleGraph.Basic
Number theory: import Mathlib.Data.Nat.Prime, Mathlib.NumberTheory.Divisors
Analysis: import Mathlib.Data.Real.Basic, Mathlib.Topology.Basic
Algebra: import Mathlib.Algebra.Group.Basic
Combinatorics: import Mathlib.Combinatorics.SimpleGraph.Coloring
Finite sets: import Mathlib.Data.Finset.Basic, Mathlib.Data.Fintype.Basic

=== EXAMPLE OUTPUT ===
```lean4
import Mathlib
import Mathlib.Combinatorics.SimpleGraph.Basic

/-- Every connected graph with n vertices has at least n-1 edges. -/
theorem connected_graph_min_edges (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) :
    G.edgeFinset.card ≥ Fintype.card V - 1 := by
  sorry
```

=== YOUR TASK ===
Provide ONLY the Lean 4 code. Do not explain. Do not apologize. Just write valid Lean 4.

Write a theorem with the ACTUAL mathematical content from the paper, not a placeholder."""

# Module-level model cache to avoid reloading
_mlx_model_cache = {}

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

def generate_with_openai(prompt, model="gpt-4o", max_tokens=4096, temperature=0.1):
    """Use OpenAI API"""
    if not OPENAI_AVAILABLE:
        return None

    api_key = os.environ.get('OPENAI_API_KEY')
    if not api_key:
        return None

    try:
        client = OpenAI(api_key=api_key)
        response = client.chat.completions.create(
            model=model,
            messages=[
                {"role": "system", "content": "You are an expert Lean 4 proof engineer. Write only valid Lean 4 code. NEVER use Lean 3 syntax (begin/end). Always use 'by' for tactic blocks."},
                {"role": "user", "content": prompt}
            ],
            temperature=temperature,
            max_tokens=max_tokens
        )
        return response.choices[0].message.content
    except Exception as e:
        print(f"    OpenAI error: {e}")
        return None

def generate_with_anthropic(prompt, model="claude-sonnet-4-20250514", max_tokens=4096, temperature=0.1):
    """Use Anthropic Claude"""
    if not ANTHROPIC_AVAILABLE:
        return None

    api_key = os.environ.get('ANTHROPIC_API_KEY')
    if not api_key:
        return None

    try:
        client = anthropic.Anthropic(api_key=api_key)
        response = client.messages.create(
            model=model,
            max_tokens=max_tokens,
            messages=[{"role": "user", "content": prompt}]
        )
        return response.content[0].text
    except Exception as e:
        print(f"    Anthropic error: {e}")
        return None

def generate_with_mlx(prompt, model_path, max_tokens=4096):
    """Use local MLX model with caching"""
    if not MLX_AVAILABLE:
        return None

    try:
        # Use cached model if available
        if model_path in _mlx_model_cache:
            model, tokenizer = _mlx_model_cache[model_path]
        else:
            print(f"    Loading {model_path}...")
            model, tokenizer = load(model_path)
            _mlx_model_cache[model_path] = (model, tokenizer)

        # Use chat template for instruct models
        messages = [
            {"role": "system", "content": "You are an expert Lean 4 proof engineer. Write only valid, compilable Lean 4 code. NEVER use begin/end (Lean 3). Always use 'by' for tactic blocks."},
            {"role": "user", "content": prompt}
        ]
        formatted_prompt = tokenizer.apply_chat_template(
            messages, tokenize=False, add_generation_prompt=True
        )

        response = generate(
            model,
            tokenizer,
            prompt=formatted_prompt,
            max_tokens=max_tokens
        )
        return response
    except Exception as e:
        print(f"    MLX error: {e}")
        return None

def validate_lean4_syntax(code):
    """Pre-validate Lean 4 code before compilation. Returns (is_valid, issues)."""
    issues = []

    # Check for Lean 3 syntax
    if re.search(r'\bbegin\b', code):
        issues.append("Contains Lean 3 'begin' keyword — must use 'by' instead")
    if re.search(r'\bend\b', code) and not re.search(r'--.*\bend\b', code):
        # Check it's not just in a comment
        for line in code.split('\n'):
            stripped = line.strip()
            if stripped == 'end' or re.match(r'end\s', stripped):
                if not stripped.startswith('--'):
                    issues.append("Contains Lean 3 'end' keyword")
                    break

    # Check for Prop as return type (not a proposition)
    if re.search(r':\s*Prop\s*:=', code):
        issues.append("Theorem type is 'Prop' itself — must be an actual proposition")

    # Check for False as goal (unprovable)
    if re.search(r':\s*False\s*:=', code):
        issues.append("Theorem tries to prove False — unprovable without contradiction context")

    # Check for missing import
    if 'import' not in code:
        issues.append("Missing import statement")

    # Check for hallucinated repetitive blocks (>5 identical lines)
    lines = code.split('\n')
    if len(lines) > 10:
        line_counts = {}
        for line in lines:
            stripped = line.strip()
            if stripped and not stripped.startswith('--') and len(stripped) > 20:
                line_counts[stripped] = line_counts.get(stripped, 0) + 1
        for line_text, count in line_counts.items():
            if count > 5:
                issues.append(f"Hallucinated repetitive code: '{line_text[:50]}...' repeated {count} times")
                break

    return (len(issues) == 0, issues)


def has_real_math_content(code):
    """Check if generated Lean code contains real mathematical content, not just True placeholders"""
    # Reject if all theorems prove True
    theorem_lines = [l for l in code.split('\n') if re.match(r'\s*(theorem|lemma|example)\b', l)]
    if not theorem_lines:
        return False
    # Check if any theorem has a non-True conclusion
    true_pattern = re.compile(r':\s*True\s*:=')
    for line in code.split('\n'):
        if true_pattern.search(line):
            continue
        if re.match(r'\s*(theorem|lemma|example)\b', line):
            return True  # Found a real theorem
    # All theorems prove True
    return False


def generate_improved_code(candidate, model_path=None, attempts=3, mathlib_map=None,
                           backend='auto', max_tokens=4096, temperature=0.1):
    """Generate better Lean 4 code"""

    # Sanitize theorem name
    theorem_name = re.sub(r'[^a-zA-Z0-9]', '_', candidate.get('name', 'theorem'))
    theorem_name = theorem_name[:50]
    if theorem_name[0].isdigit():
        theorem_name = 'thm_' + theorem_name

    # Load mathlib library map if available
    mathlib_refs = ""
    if mathlib_map:
        mathlib_refs = mathlib_map
    else:
        # Try to load from cached index
        index_path = os.path.join(os.path.dirname(__file__), '..', 'MathAI', '.lake', 'mathlib-index.json')
        if os.path.exists(index_path):
            try:
                with open(index_path, 'r') as f:
                    index = json.load(f)
                # Filter relevant theorems based on paper category
                categories = candidate.get('source_paper', {}).get('categories', [])
                mathlib_refs = _filter_mathlib_refs(index, categories, candidate.get('statement', ''))
            except Exception:
                pass

    # Build enhanced prompt with abstract content
    prompt = LEAN_PROVER_PROMPT.format(
        name=candidate.get('name', 'Unknown'),
        statement=candidate.get('statement', ''),
        objects=', '.join(candidate.get('objects', [])),
        difficulty=candidate.get('difficulty', 'Medium'),
        paper_title=candidate.get('source_paper', {}).get('title', 'Unknown'),
        category=', '.join(candidate.get('source_paper', {}).get('categories', [])),
        abstract_excerpt=candidate.get('abstract_excerpt', 'Not available')
    )

    # Append mathlib references if available
    if mathlib_refs:
        prompt += f"\n\n=== AVAILABLE MATHLIB THEOREMS (use these exact names) ===\n{mathlib_refs}"

    # Build backend list based on --backend flag
    backends = []

    if backend in ('auto', 'anthropic'):
        if ANTHROPIC_AVAILABLE and os.environ.get('ANTHROPIC_API_KEY'):
            anthropic_model = model_path if backend == 'anthropic' else 'claude-sonnet-4-20250514'
            backends.append(('Claude', lambda p, m=anthropic_model: generate_with_anthropic(p, model=m, max_tokens=max_tokens, temperature=temperature)))

    if backend in ('auto', 'openai'):
        if OPENAI_AVAILABLE and os.environ.get('OPENAI_API_KEY'):
            openai_model = model_path if backend == 'openai' else 'gpt-4o'
            backends.append(('OpenAI', lambda p, m=openai_model: generate_with_openai(p, model=m, max_tokens=max_tokens, temperature=temperature)))

    if backend in ('auto', 'mlx'):
        if MLX_AVAILABLE and model_path:
            backends.append(('Local MLX', lambda p: generate_with_mlx(p, model_path, max_tokens=max_tokens)))

    best_fallback = None

    # Try each backend
    for backend_name, backend_fn in backends:
        for attempt in range(attempts):
            try:
                print(f"  Trying {backend_name} (attempt {attempt + 1}/{attempts})...")
                response = backend_fn(prompt)

                if response:
                    code = extract_lean_code(response)
                    if code and 'theorem' in code.lower():
                        # Validate Lean 4 syntax before accepting
                        is_valid, issues = validate_lean4_syntax(code)
                        if not is_valid:
                            print(f"  ~ {backend_name} syntax issues: {'; '.join(issues)}")
                            if best_fallback is None:
                                best_fallback = code
                            continue

                        if has_real_math_content(code):
                            print(f"  ✓ Generated real theorem with {backend_name}")
                            return code
                        else:
                            print(f"  ~ {backend_name} generated True placeholder, trying again...")
                            if best_fallback is None:
                                best_fallback = code
            except Exception as e:
                print(f"  ✗ {backend_name} error: {e}")
                continue

    # If we have a True-placeholder fallback, use it with TEMPLATE marker
    if best_fallback:
        print("  ⚠️  No real math generated, using best placeholder as template")
        return f"-- STATUS: TEMPLATE_FALLBACK\n{best_fallback}"

    # Final fallback: generate improved template
    print("  ⚠️  All backends failed, using improved template")
    return generate_improved_template(candidate, theorem_name)


def _filter_mathlib_refs(index, categories, statement):
    """Filter mathlib index to relevant theorems using semantic search if available"""
    # Try semantic search first (much better results)
    try:
        from build_mathlib_index import search_mathlib
        refs = search_mathlib(statement, top_k=30)
        if refs:
            return refs
    except ImportError:
        pass

    # Fallback: category-based filtering
    relevant_domains = []
    for cat in categories:
        if 'CO' in cat:
            relevant_domains.extend(['Combinatorics', 'Data.Finset', 'Data.Fintype'])
        if 'NT' in cat:
            relevant_domains.extend(['NumberTheory', 'Data.Nat.Prime', 'Data.Int'])
        if 'AG' in cat:
            relevant_domains.extend(['AlgebraicGeometry', 'RingTheory'])
        if 'GR' in cat:
            relevant_domains.extend(['GroupTheory', 'Algebra.Group'])

    if not relevant_domains:
        relevant_domains = ['Data.Nat', 'Data.Int', 'Algebra']

    lines = []
    count = 0
    for domain, entries in index.items():
        if count >= 50:
            break
        if any(d in domain for d in relevant_domains):
            module = entries.get('module', domain)
            lines.append(f"-- import {module}")
            for thm in entries.get('theorems', [])[:5]:
                lines.append(f"--   {thm['name']}: {thm.get('sig', '')[:80]}")
                count += 1

    return '\n'.join(lines) if lines else ""

def generate_improved_template(candidate, theorem_name):
    """Generate a better template with actual structure"""

    name = candidate.get('name', 'Unknown')
    statement = candidate.get('statement', '')
    objects = candidate.get('objects', [])
    paper = candidate.get('source_paper', {})
    abstract = candidate.get('abstract_excerpt', '')

    # Determine appropriate imports and structure
    imports = ["import Mathlib"]
    theorem_body = ""

    paper_title = paper.get('title', 'Unknown')
    paper_authors = ', '.join(paper.get('authors', [])[:2])
    paper_id = paper.get('id', 'unknown')

    if any('graph' in obj.lower() for obj in objects):
        imports.append("import Mathlib.Combinatorics.SimpleGraph.Basic")
        imports.append("import Mathlib.Combinatorics.SimpleGraph.Connectivity")
        theorem_body = f"""
-- Define the graph property from the paper
variable {{V : Type}} [Fintype V] [DecidableEq V]

/--
TODO: Formalize the exact statement from:
{paper_title}
by {paper_authors}
arXiv: {paper_id}
-/
theorem {theorem_name} (G : SimpleGraph V) :
    -- Statement needed: {statement[:100]}
    True := by
  sorry
"""
    elif any('prime' in obj.lower() for obj in objects):
        imports.append("import Mathlib.Data.Nat.Prime.Basic")
        imports.append("import Mathlib.NumberTheory.Divisors")
        theorem_body = f"""
/--
TODO: Formalize from:
{paper_title}
by {paper_authors}
arXiv: {paper_id}
-/
theorem {theorem_name} (n : ℕ) :
    -- Statement needed: {statement[:100]}
    True := by
  sorry
"""
    else:
        theorem_body = f"""
/--
TODO: Formalize the theorem from:
{paper_title}
by {paper_authors}
arXiv: {paper_id}

Original statement: {statement[:200]}
-/
theorem {theorem_name} :
    -- Formal statement needed
    True := by
  sorry
"""

    imports_str = '\n'.join(imports)

    return f"""-- STATUS: TEMPLATE_FALLBACK
{imports_str}

/-!
# {name}

Statement: {statement[:300]}

Mathematical objects: {', '.join(objects)}
Source: {paper_title}
arXiv: {paper_id}

Status: Template - requires manual formalization.
-/

{theorem_body}
"""

def main():
    parser = argparse.ArgumentParser(description="Generate improved Lean 4 formalizations")
    parser.add_argument("--candidate", required=True, help="JSON string with candidate info")
    parser.add_argument("--output", required=True, help="Output .lean file")
    parser.add_argument("--attempts", type=int, default=3, help="Number of attempts")
    parser.add_argument("--model", default="mlx-community/DeepSeek-Coder-V2-Lite-Instruct-4bit",
                       help="Model to use")
    parser.add_argument("--backend", choices=['auto', 'openai', 'anthropic', 'mlx'],
                       default='auto', help="LLM backend to use")
    parser.add_argument("--max-tokens", type=int, default=4096, help="Max tokens for generation")
    parser.add_argument("--temperature", type=float, default=0.1, help="Temperature for generation")

    args = parser.parse_args()

    # Parse candidate
    candidate = json.loads(args.candidate)
    print(f"Formalizing: {candidate.get('name', 'Unknown')} [backend={args.backend}, model={args.model}]")

    # Generate improved code
    code = generate_improved_code(
        candidate,
        model_path=args.model,
        attempts=args.attempts,
        backend=args.backend,
        max_tokens=args.max_tokens,
        temperature=args.temperature
    )

    # Write output
    os.makedirs(os.path.dirname(args.output), exist_ok=True)
    with open(args.output, 'w') as f:
        f.write(code)

    print(f"Generated {args.output}")

if __name__ == "__main__":
    main()
