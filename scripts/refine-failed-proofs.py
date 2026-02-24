#!/usr/bin/env python3
"""
refine-failed-proofs.py
Scan failed/formalized proofs, extract Lean compiler errors, and send back to LLM
for a refinement pass. Can promote FAILED → FORMALIZED or FORMALIZED → PROVEN.
"""

import argparse
import glob
import json
import os
import re
import subprocess

# Reuse backends from llm-formalize-v2
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

# Module-level model cache
_mlx_model_cache = {}

REFINEMENT_PROMPT = """You are an expert Lean 4 proof engineer fixing compilation errors.

=== ORIGINAL CODE ===
{original_code}

=== LEAN COMPILER ERRORS ===
{error_output}

=== CRITICAL LEAN 4 SYNTAX RULES ===
- NEVER use `begin`/`end` (that is Lean 3). Use `by` for tactic blocks.
- The theorem type must be an actual proposition, NOT `Prop` itself.
- WRONG: `theorem foo : Prop := by sorry`
- CORRECT: `theorem foo : n > 0 := by sorry`
- Always start with `import Mathlib`

=== INSTRUCTIONS ===
1. Fix the specific errors shown above
2. Keep the theorem statement the same (or improve it if the type signature is wrong)
3. Fix import paths — use exact mathlib4 module names
4. If you can't fully prove it, use `sorry` but make the statement compile
5. Do NOT replace the theorem with `True := by trivial`
6. Do NOT use begin/end — use `by` for all tactic blocks

{mathlib_refs}

Write ONLY the corrected Lean 4 code. No explanation."""

PROJECT_DIR = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MATHAI_DIR = os.path.join(PROJECT_DIR, 'MathAI')


def get_lean_errors(filepath):
    """Run lean on a file and capture compiler errors"""
    # Ensure absolute path
    filepath = os.path.abspath(filepath)

    env = os.environ.copy()
    env['PATH'] = os.path.expanduser('~/.elan/bin') + ':' + env.get('PATH', '')

    if not os.path.isdir(MATHAI_DIR):
        return f"ERROR: MathAI directory not found at {MATHAI_DIR}"

    try:
        result = subprocess.run(
            ['lake', 'env', 'lean', filepath],
            capture_output=True, text=True, timeout=120,
            cwd=MATHAI_DIR, env=env
        )
        if result.returncode != 0:
            errors = result.stderr[:3000] if result.stderr else result.stdout[:3000]
            return errors if errors.strip() else f"Lean exited with code {result.returncode}"
        return None  # No errors
    except subprocess.TimeoutExpired:
        return "TIMEOUT: Lean compilation exceeded 120 seconds"
    except FileNotFoundError:
        return "ERROR: 'lake' command not found. Ensure elan/lean is installed."
    except Exception as e:
        return f"ERROR: {e}"


def check_has_sorry(filepath):
    """Check if a file contains sorry"""
    try:
        with open(filepath, 'r') as f:
            return 'sorry' in f.read()
    except:
        return False


def check_is_trivial(filepath):
    """Check if a file only proves True"""
    try:
        with open(filepath, 'r') as f:
            content = f.read()
        return bool(re.search(r':\s*True\s*:=', content))
    except:
        return False


def generate_refinement(original_code, error_output, model_path=None, mathlib_refs=""):
    """Send original code + errors to LLM for refinement"""

    prompt = REFINEMENT_PROMPT.format(
        original_code=original_code,
        error_output=error_output,
        mathlib_refs=f"=== AVAILABLE MATHLIB THEOREMS ===\n{mathlib_refs}" if mathlib_refs else ""
    )

    # Try backends in order
    backends = []

    if OPENAI_AVAILABLE and os.environ.get('OPENAI_API_KEY'):
        backends.append(('OpenAI', lambda: _call_openai(prompt)))

    if ANTHROPIC_AVAILABLE and os.environ.get('ANTHROPIC_API_KEY'):
        backends.append(('Anthropic', lambda: _call_anthropic(prompt)))

    if MLX_AVAILABLE and model_path:
        backends.append(('MLX', lambda: _call_mlx(prompt, model_path)))

    for name, fn in backends:
        try:
            print(f"    Trying {name}...")
            response = fn()
            if response:
                code = _extract_lean_code(response)
                if code:
                    return code
        except Exception as e:
            print(f"    {name} error: {e}")

    return None


def _call_openai(prompt):
    client = OpenAI(api_key=os.environ['OPENAI_API_KEY'])
    response = client.chat.completions.create(
        model="gpt-4o",
        messages=[
            {"role": "system", "content": "Fix the Lean 4 compilation errors. Return only valid Lean 4 code."},
            {"role": "user", "content": prompt}
        ],
        temperature=0.1, max_tokens=4096
    )
    return response.choices[0].message.content


def _call_anthropic(prompt):
    client = anthropic.Anthropic(api_key=os.environ['ANTHROPIC_API_KEY'])
    response = client.messages.create(
        model="claude-sonnet-4-20250514",
        max_tokens=4096,
        messages=[{"role": "user", "content": prompt}]
    )
    return response.content[0].text


def _call_mlx(prompt, model_path):
    if model_path in _mlx_model_cache:
        model, tokenizer = _mlx_model_cache[model_path]
    else:
        model, tokenizer = load(model_path)
        _mlx_model_cache[model_path] = (model, tokenizer)

    messages = [
        {"role": "system", "content": "Fix the Lean 4 compilation errors. Return only valid Lean 4 code."},
        {"role": "user", "content": prompt}
    ]
    formatted = tokenizer.apply_chat_template(messages, tokenize=False, add_generation_prompt=True)
    return generate(model, tokenizer, prompt=formatted, max_tokens=4096)


def _extract_lean_code(text):
    """Extract Lean code from LLM response"""
    patterns = [r'```lean4?\s*(.*?)\s*```', r'```\s*(import.*?)\s*```']
    for pattern in patterns:
        match = re.search(pattern, text, re.DOTALL)
        if match:
            return match.group(1).strip()

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


def load_mathlib_refs(categories=None):
    """Load relevant mathlib references for the refinement prompt"""
    index_path = os.path.join(PROJECT_DIR, 'MathAI', '.lake', 'mathlib-index.json')
    if not os.path.exists(index_path):
        return ""

    try:
        with open(index_path) as f:
            index = json.load(f)

        lines = []
        count = 0
        for domain, entries in index.items():
            if count >= 30:
                break
            for thm in entries.get('theorems', [])[:3]:
                lines.append(f"-- {thm['name']}: {thm.get('sig', '')[:60]}")
                count += 1

        return '\n'.join(lines)
    except:
        return ""


def main():
    parser = argparse.ArgumentParser(description="Refine failed Lean proofs using LLM")
    parser.add_argument("--proofs-dir", default=None,
                       help="Directory containing .lean files to refine")
    parser.add_argument("--failed-dir", default=os.path.join(PROJECT_DIR, 'failed-attempts'),
                       help="Directory with failed attempt records")
    parser.add_argument("--max-attempts", type=int, default=2,
                       help="Max refinement attempts per file")
    parser.add_argument("--model", default="mlx-community/DeepSeek-Coder-V2-Lite-Instruct-4bit",
                       help="MLX model for refinement")
    parser.add_argument("--date", default=None,
                       help="Date to process (YYYY-MM-DD), defaults to today's proofs")

    args = parser.parse_args()

    # Find proof files to refine
    proof_files = []

    if args.proofs_dir:
        proof_files = sorted(glob.glob(os.path.join(args.proofs_dir, '*.lean')))
    elif args.date:
        proof_dir = os.path.join(PROJECT_DIR, 'proofs', args.date)
        proof_files = sorted(glob.glob(os.path.join(proof_dir, '**', '*.lean'), recursive=True))
    else:
        # Find most recent date
        proof_base = os.path.join(PROJECT_DIR, 'proofs')
        if os.path.isdir(proof_base):
            dates = sorted([d for d in os.listdir(proof_base) if os.path.isdir(os.path.join(proof_base, d))])
            if dates:
                proof_dir = os.path.join(proof_base, dates[-1])
                proof_files = sorted(glob.glob(os.path.join(proof_dir, '**', '*.lean'), recursive=True))

    if not proof_files:
        print("No proof files found to refine")
        return

    print(f"Found {len(proof_files)} proof files to check")

    # Load mathlib references
    mathlib_refs = load_mathlib_refs()

    refined_count = 0
    promoted_count = 0

    for filepath in proof_files:
        basename = os.path.basename(filepath)

        # Skip already-refined files
        if '_v' in basename and basename.split('_v')[-1].split('.')[0].isdigit():
            continue

        # Skip trivial proofs
        if check_is_trivial(filepath):
            print(f"  SKIP (trivial): {basename}")
            continue

        # Check current status
        errors = get_lean_errors(filepath)
        has_sorry = check_has_sorry(filepath)

        if errors is None and not has_sorry:
            print(f"  OK (already proven): {basename}")
            continue

        if errors is None and has_sorry:
            status = "FORMALIZED"
        elif errors:
            status = "FAILED"
        else:
            continue

        print(f"  Refining ({status}): {basename}")

        # Read original code
        with open(filepath, 'r') as f:
            original_code = f.read()

        # Build error context
        error_context = errors if errors else "Compiles but has `sorry` placeholders. Try to fill in the proofs."

        # Try refinement
        for attempt in range(1, args.max_attempts + 1):
            print(f"    Attempt {attempt}/{args.max_attempts}...")

            refined_code = generate_refinement(
                original_code, error_context,
                model_path=args.model,
                mathlib_refs=mathlib_refs
            )

            if not refined_code:
                print(f"    No refinement generated")
                continue

            # Check for trivial output
            if re.search(r':\s*True\s*:=', refined_code):
                print(f"    Rejected: refined code is trivial (True :=)")
                continue

            # Write refined version
            version = attempt
            refined_path = filepath.replace('.lean', f'_v{version}.lean')
            with open(refined_path, 'w') as f:
                f.write(refined_code)

            # Verify refined version
            new_errors = get_lean_errors(refined_path)
            new_has_sorry = check_has_sorry(refined_path)

            if new_errors is None and not new_has_sorry:
                print(f"    ✓ PROVEN! {basename} → {os.path.basename(refined_path)}")
                promoted_count += 1
                refined_count += 1
                break
            elif new_errors is None and new_has_sorry:
                if status == "FAILED":
                    print(f"    ↑ Promoted FAILED → FORMALIZED: {os.path.basename(refined_path)}")
                    promoted_count += 1
                else:
                    print(f"    ~ Still formalized (sorry remains)")
                refined_count += 1
                # Update error context for next attempt
                error_context = "Compiles but has `sorry` placeholders. Try to fill in the proofs."
                original_code = refined_code
            else:
                print(f"    ✗ Still failing: {new_errors[:100]}...")
                # Use new errors for next attempt
                error_context = new_errors
                original_code = refined_code

    print(f"\nRefinement complete: {refined_count} refined, {promoted_count} promoted")


if __name__ == "__main__":
    main()
