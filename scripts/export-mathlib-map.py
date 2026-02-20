#!/usr/bin/env python3
"""
export-mathlib-map.py
Extract theorem/lemma/def names and signatures from the local mathlib source tree.
Outputs a JSON index for use in LLM prompts.
"""

import argparse
import json
import os
import re
from pathlib import Path

# Map arXiv categories to mathlib directories
CATEGORY_TO_DIRS = {
    'math.CO': ['Combinatorics', 'Data/Finset', 'Data/Fintype', 'Data/Multiset'],
    'math.NT': ['NumberTheory', 'Data/Nat/Prime', 'Data/Nat/GCD', 'Data/Int', 'Data/ZMod'],
    'math.AG': ['AlgebraicGeometry', 'RingTheory', 'FieldTheory'],
    'math.GR': ['GroupTheory', 'Algebra/Group'],
    'math.AT': ['AlgebraicTopology', 'Topology'],
    'math.GT': ['Geometry', 'Topology'],
    'math.AC': ['RingTheory', 'Algebra/Ring', 'Algebra/Order'],
    'math.RA': ['Algebra', 'RingTheory', 'LinearAlgebra'],
    'math.DG': ['Geometry/Manifold', 'Topology/Algebra'],
    'cs.DM': ['Combinatorics', 'Data/Finset', 'Data/Fintype', 'Order'],
    'cs.DS': ['Combinatorics', 'Data', 'Order'],
}

# Regex patterns for declarations
DECL_PATTERN = re.compile(
    r'^(theorem|lemma|def|instance|noncomputable def|protected theorem|protected lemma|protected def)\s+'
    r'(\S+)',
    re.MULTILINE
)

# Pattern for extracting type signature (everything between name and := or where)
SIG_PATTERN = re.compile(
    r'^(?:theorem|lemma|def|instance|noncomputable def|protected theorem|protected lemma|protected def)\s+\S+\s*(.*?)(?:\s*:=\s*|\s*where\s*|\s*\|\s*)',
    re.MULTILINE | re.DOTALL
)

# Docstring pattern (matches /-- ... -/)
DOC_PATTERN = re.compile(r'/--\s*(.*?)\s*-/', re.DOTALL)


def module_path_from_file(filepath, mathlib_root):
    """Convert file path to Lean module path (e.g., Mathlib.Data.Nat.Prime.Basic)"""
    rel = os.path.relpath(filepath, os.path.dirname(mathlib_root))
    # Remove .lean extension and convert / to .
    module = rel.replace('.lean', '').replace(os.sep, '.')
    return module


def extract_declarations(filepath):
    """Extract theorem/lemma/def declarations from a Lean source file"""
    declarations = []
    try:
        with open(filepath, 'r', encoding='utf-8', errors='replace') as f:
            content = f.read()
    except (OSError, UnicodeDecodeError):
        return declarations

    # Find all docstrings and their positions
    docstrings = {}
    for m in DOC_PATTERN.finditer(content):
        # Associate docstring with the next declaration after it
        docstrings[m.end()] = m.group(1).strip()[:200]

    # Find all declarations
    for m in DECL_PATTERN.finditer(content):
        decl_type = m.group(1)
        name = m.group(2)

        # Skip private/internal names
        if name.startswith('_') or name.startswith('aux_'):
            continue

        # Extract signature (first line after name, up to 120 chars)
        sig_start = m.end()
        sig_end = content.find('\n', sig_start)
        if sig_end == -1:
            sig_end = min(sig_start + 120, len(content))
        sig = content[sig_start:sig_end].strip()[:120]

        # Find associated docstring (look for closest docstring ending before this declaration)
        doc = ""
        best_pos = -1
        for pos, text in docstrings.items():
            if pos <= m.start() and pos > best_pos:
                # Check that there's not too much gap (max 200 chars of whitespace/newlines)
                gap = content[pos:m.start()].strip()
                if len(gap) < 50:
                    best_pos = pos
                    doc = text

        declarations.append({
            'name': name,
            'type': decl_type.split()[-1],  # theorem/lemma/def
            'sig': sig,
            'doc': doc[:150] if doc else ''
        })

    return declarations


def build_index(mathlib_root, target_dirs=None):
    """Build the mathlib index from source files"""
    index = {}
    mathlib_dir = os.path.join(mathlib_root, 'Mathlib')

    if not os.path.isdir(mathlib_dir):
        print(f"ERROR: Mathlib directory not found: {mathlib_dir}")
        return index

    # Walk target directories or all of Mathlib
    if target_dirs:
        dirs_to_scan = []
        for d in target_dirs:
            full_path = os.path.join(mathlib_dir, d)
            if os.path.isdir(full_path):
                dirs_to_scan.append(full_path)
            elif os.path.isfile(full_path + '.lean'):
                dirs_to_scan.append(full_path + '.lean')
    else:
        dirs_to_scan = [mathlib_dir]

    files_scanned = 0
    decls_found = 0

    for scan_path in dirs_to_scan:
        if os.path.isfile(scan_path):
            files = [scan_path]
        else:
            files = sorted(Path(scan_path).rglob('*.lean'))

        for filepath in files:
            filepath = str(filepath)
            module = module_path_from_file(filepath, mathlib_dir)
            declarations = extract_declarations(filepath)

            if declarations:
                # Group by domain (top-level directory under Mathlib/)
                rel = os.path.relpath(filepath, mathlib_dir)
                parts = rel.split(os.sep)
                domain = parts[0] if len(parts) > 1 else 'Root'

                if domain not in index:
                    index[domain] = {
                        'module': f"Mathlib.{domain}",
                        'files': [],
                        'theorems': []
                    }

                index[domain]['files'].append(module)
                for decl in declarations:
                    index[domain]['theorems'].append({
                        'name': decl['name'],
                        'type': decl['type'],
                        'sig': decl['sig'],
                        'doc': decl['doc'],
                        'module': module
                    })

                files_scanned += 1
                decls_found += len(declarations)

    print(f"Scanned {files_scanned} files, found {decls_found} declarations")
    return index


def main():
    parser = argparse.ArgumentParser(description="Export Mathlib theorem index")
    parser.add_argument("--mathlib-root",
                       default=os.path.join(os.path.dirname(__file__), '..', 'MathAI', '.lake', 'packages', 'mathlib'),
                       help="Path to mathlib root directory")
    parser.add_argument("--output",
                       default=os.path.join(os.path.dirname(__file__), '..', 'MathAI', '.lake', 'mathlib-index.json'),
                       help="Output JSON index file")
    parser.add_argument("--categories", nargs='+', default=['math.CO', 'math.NT'],
                       help="arXiv categories to index (determines which mathlib dirs to scan)")
    parser.add_argument("--all", action="store_true",
                       help="Index ALL mathlib directories (slow, ~8000 files)")

    args = parser.parse_args()

    print(f"Building Mathlib index from: {args.mathlib_root}")

    # Determine which directories to scan
    target_dirs = None
    if not args.all:
        target_dirs = set()
        for cat in args.categories:
            dirs = CATEGORY_TO_DIRS.get(cat, [])
            target_dirs.update(dirs)
        target_dirs = sorted(target_dirs)
        print(f"Scanning directories: {target_dirs}")

    index = build_index(args.mathlib_root, target_dirs)

    # Write index
    os.makedirs(os.path.dirname(args.output), exist_ok=True)
    with open(args.output, 'w') as f:
        json.dump(index, f, indent=2)

    total_theorems = sum(len(v.get('theorems', [])) for v in index.values())
    print(f"✓ Exported {total_theorems} declarations across {len(index)} domains to {args.output}")


if __name__ == "__main__":
    main()
