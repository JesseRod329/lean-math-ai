#!/usr/bin/env python3
"""
extract-theorems.py
Use LLM to identify theorems suitable for Lean formalization
"""

import argparse
import json
import re

try:
    from mlx_lm import load, generate
    MLX_AVAILABLE = True
except ImportError:
    MLX_AVAILABLE = False
    print("Warning: mlx_lm not available. Install with: pip install mlx-lm")

# Prompt template for theorem extraction
THEOREM_EXTRACTION_PROMPT = """You are a mathematics formalization expert. Your task is to identify theorems in the following mathematical text that would be suitable for formalization in Lean 4 with mathlib4.

TEXT TO ANALYZE:
Title: {title}
Abstract: {summary}

INSTRUCTIONS:
1. Identify 1-3 theorems or lemmas that could be formalized in Lean 4
2. Focus on theorems that:
   - Have clear, precise statements
   - Use standard mathematical concepts (numbers, sets, functions, etc.)
   - Don't require heavy machinery (avoid deep category theory, complex algebraic geometry)
   - Would fit well in mathlib4 (combinatorics, number theory, basic analysis)
3. For each theorem, provide:
   - A clear statement in natural language
   - The mathematical objects involved
   - An estimate of difficulty (Easy/Medium/Hard)
   - Why it would be valuable to formalize

RESPONSE FORMAT (JSON):
{{
  "candidates": [
    {{
      "name": "Theorem Name or Description",
      "statement": "Clear mathematical statement",
      "objects": ["list", "of", "mathematical", "objects"],
      "difficulty": "Easy|Medium|Hard",
      "value": "Why formalize this?",
      "formalization_hints": "Hints for Lean formalization"
    }}
  ]
}}

Respond ONLY with the JSON. No markdown, no explanation."""

def extract_theorems_from_paper(paper, model=None, tokenizer=None):
    """Use LLM to extract formalizable theorems from a paper"""

    prompt_text = THEOREM_EXTRACTION_PROMPT.format(
        title=paper.get('title', ''),
        summary=paper.get('summary', '')[:2000]
    )

    extraction_method = "heuristic"

    if MLX_AVAILABLE and model is not None and tokenizer is not None:
        try:
            # Use chat template for instruct models
            messages = [
                {"role": "system", "content": "You are a mathematics formalization expert. Respond only with valid JSON."},
                {"role": "user", "content": prompt_text}
            ]
            formatted_prompt = tokenizer.apply_chat_template(
                messages, tokenize=False, add_generation_prompt=True
            )

            response = generate(
                model,
                tokenizer,
                prompt=formatted_prompt,
                max_tokens=2048
            )
            extraction_method = "llm"
        except Exception as e:
            print(f"  WARNING: LLM extraction failed for {paper.get('id', 'unknown')}: {e}")
            print(f"  Falling back to heuristic extraction")
            candidates = simulate_extraction(paper)
            for c in candidates:
                c['extraction_method'] = 'heuristic'
            return candidates
    else:
        if not MLX_AVAILABLE:
            print(f"  INFO: MLX not available, using heuristic extraction for {paper.get('id', 'unknown')}")
        elif model is None:
            print(f"  INFO: No model loaded, using heuristic extraction for {paper.get('id', 'unknown')}")
        candidates = simulate_extraction(paper)
        for c in candidates:
            c['extraction_method'] = 'heuristic'
        return candidates

    # Parse JSON response
    try:
        # Try to extract JSON from response (handle markdown code blocks)
        json_match = re.search(r'```json\s*(\{.*?\})\s*```', response, re.DOTALL)
        if json_match:
            response = json_match.group(1)
        else:
            # Strip everything before first { and after last }
            first_brace = response.find('{')
            last_brace = response.rfind('}')
            if first_brace != -1 and last_brace != -1:
                response = response[first_brace:last_brace + 1]

        # Fix LaTeX escapes that break JSON parsing (\textbf, \in, etc.)
        response = re.sub(r'\\(?!["\\/bfnrtu])', r'\\\\', response)
        result = json.loads(response)

        # Add paper metadata and abstract to each candidate
        abstract_excerpt = paper.get('summary', '')[:1500]
        for candidate in result.get('candidates', []):
            candidate['source_paper'] = {
                'id': paper.get('id'),
                'title': paper.get('title'),
                'authors': paper.get('authors', [])[:3],
                'categories': paper.get('categories', [])
            }
            candidate['abstract_excerpt'] = abstract_excerpt
            candidate['extraction_method'] = extraction_method
            # Generate stable ID from name
            safe_name = re.sub(r'[^a-zA-Z0-9]', '_', candidate.get('name', 'unknown'))[:30]
            candidate['id'] = f"{paper.get('id', 'unknown')}_{safe_name}"

        return result.get('candidates', [])

    except json.JSONDecodeError as e:
        print(f"  Failed to parse LLM response: {e}")
        print(f"  Raw response: {response[:200]}...")
        candidates = simulate_extraction(paper)
        for c in candidates:
            c['extraction_method'] = 'heuristic'
        return candidates

def simulate_extraction(paper):
    """Fallback: extract theorem-indicator sentences from abstract as candidates"""
    candidates = []

    title = paper.get('title', '')
    summary = paper.get('summary', '')
    abstract_excerpt = summary[:1500]

    # Find sentences containing theorem-indicator words
    sentences = re.split(r'(?<=[.!?])\s+', summary)
    theorem_sentences = [s.strip() for s in sentences
                         if any(w in s.lower() for w in
                                ['prove', 'show', 'establish', 'theorem',
                                 'result', 'bound', 'inequality', 'conjecture',
                                 'characterize', 'classify', 'determine'])]

    # Build paper metadata once
    source_paper = {
        "id": paper.get('id'),
        "title": title,
        "authors": paper.get('authors', [])[:3],
        "categories": paper.get('categories', [])
    }

    # Detect mathematical objects from content
    text_lower = (title + ' ' + summary).lower()
    objects = []
    hints_parts = []

    if 'prime' in text_lower or 'divisor' in text_lower or 'arithmetic' in text_lower:
        objects.extend(["prime numbers", "integers", "arithmetic functions"])
        hints_parts.append("Use Nat.Prime and related lemmas from mathlib4")
    if 'graph' in text_lower or 'vertex' in text_lower or 'edge' in text_lower:
        objects.extend(["graphs", "vertices", "edges"])
        hints_parts.append("Use SimpleGraph from mathlib4")
    if 'combinat' in text_lower or 'partition' in text_lower or 'permutation' in text_lower:
        objects.extend(["finite sets", "combinatorial structures"])
        hints_parts.append("Use Finset and Fintype from mathlib4")
    if not objects:
        objects = ["mathematical structures"]
        hints_parts = ["Requires careful analysis of paper"]

    # Create one candidate per theorem sentence found (up to 3)
    if theorem_sentences:
        for i, stmt in enumerate(theorem_sentences[:3]):
            safe_name = re.sub(r'[^a-zA-Z0-9]', '_', title[:40])
            candidates.append({
                "name": f"{title[:60]}",
                "statement": stmt,
                "objects": objects,
                "difficulty": "Medium",
                "value": f"Formalizes result from {title[:40]}",
                "formalization_hints": "; ".join(hints_parts),
                "source_paper": source_paper,
                "abstract_excerpt": abstract_excerpt,
                "id": f"{paper.get('id', 'unknown')}_{safe_name}_{i}"
            })
    else:
        # No theorem sentences found — use the full abstract as context
        candidates.append({
            "name": f"{title[:60]}",
            "statement": f"Main result from: {title}. {summary[:200]}",
            "objects": objects,
            "difficulty": "Hard",
            "value": f"Formalizes result from {title[:40]}",
            "formalization_hints": "; ".join(hints_parts),
            "source_paper": source_paper,
            "abstract_excerpt": abstract_excerpt,
            "id": f"{paper.get('id', 'unknown')}_result"
        })

    return candidates

def main():
    parser = argparse.ArgumentParser(description="Extract formalizable theorems from papers")
    parser.add_argument("--input", required=True, help="Input JSON file with papers")
    parser.add_argument("--output", required=True, help="Output JSON file for candidates")
    parser.add_argument("--max-candidates", type=int, default=10,
                       help="Maximum candidates to extract")
    parser.add_argument("--model", default="mlx-community/DeepSeek-Coder-V2-Lite-Instruct-4bit",
                       help="MLX model to use for extraction")
    parser.add_argument("--skip-llm", action="store_true",
                       help="Skip LLM and use heuristic extraction only")

    args = parser.parse_args()

    # Load papers
    with open(args.input, 'r') as f:
        data = json.load(f)

    papers = data.get('papers', [])
    print(f"Processing {len(papers)} papers...")

    # Load model if available and not skipped
    model = None
    tokenizer = None
    if MLX_AVAILABLE and not args.skip_llm:
        print(f"Loading model: {args.model}")
        try:
            model, tokenizer = load(args.model)
            print("✓ Model loaded")
        except Exception as e:
            print(f"Failed to load model: {e}")
            print("Falling back to heuristic mode")

    # Extract theorems from each paper
    all_candidates = []
    for i, paper in enumerate(papers):
        print(f"Processing paper {i+1}/{len(papers)}: {paper.get('id', 'unknown')}")

        candidates = extract_theorems_from_paper(paper, model, tokenizer)
        all_candidates.extend(candidates)

        if len(all_candidates) >= args.max_candidates:
            break

    # Limit candidates
    all_candidates = all_candidates[:args.max_candidates]

    # Save results
    output = {
        "extraction_date": data.get('fetch_date'),
        "total_papers": len(papers),
        "candidates_found": len(all_candidates),
        "candidates": all_candidates
    }

    with open(args.output, 'w') as f:
        json.dump(output, f, indent=2)

    print(f"✓ Extracted {len(all_candidates)} candidates to {args.output}")

if __name__ == "__main__":
    main()
