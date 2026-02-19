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
    
    prompt = THEOREM_EXTRACTION_PROMPT.format(
        title=paper.get('title', ''),
        summary=paper.get('summary', '')[:2000]  # Limit summary length
    )
    
    if MLX_AVAILABLE and model is not None:
        # Use local MLX model
        response = generate(
            model,
            tokenizer,
            prompt=prompt,
            max_tokens=2048,
            temp=0.3
        )
    else:
        # Fallback: simulate extraction with regex (for testing)
        return simulate_extraction(paper)
    
    # Parse JSON response
    try:
        # Extract JSON from response (handle markdown code blocks)
        json_match = re.search(r'```json\s*(\{.*?\})\s*```', response, re.DOTALL)
        if json_match:
            response = json_match.group(1)
        
        result = json.loads(response)
        
        # Add paper metadata
        for candidate in result.get('candidates', []):
            candidate['source_paper'] = {
                'id': paper.get('id'),
                'title': paper.get('title'),
                'authors': paper.get('authors', [])[:3],  # First 3 authors
                'categories': paper.get('categories', [])
            }
            candidate['id'] = f"{paper.get('id', 'unknown')}_{hash(candidate['name']) % 10000}"
        
        return result.get('candidates', [])
        
    except json.JSONDecodeError as e:
        print(f"Failed to parse LLM response: {e}")
        return []

def simulate_extraction(paper):
    """Simulate theorem extraction for testing without LLM"""
    # Simple heuristic extraction for testing
    candidates = []
    
    title = paper.get('title', '').lower()
    summary = paper.get('summary', '').lower()
    
    # Pattern matching for common theorem types
    if 'prime' in title or 'prime' in summary:
        candidates.append({
            "name": f"Prime-related result from {paper.get('id', 'unknown')}",
            "statement": "A property about prime numbers mentioned in the paper",
            "objects": ["prime numbers", "integers"],
            "difficulty": "Medium",
            "value": "Extends number theory library",
            "formalization_hints": "Use Nat.Prime and related lemmas",
            "source_paper": {
                "id": paper.get('id'),
                "title": paper.get('title'),
                "authors": paper.get('authors', [])[:3],
                "categories": paper.get('categories', [])
            },
            "id": f"{paper.get('id', 'unknown')}_prime"
        })
    
    if 'graph' in title or 'graph' in summary:
        candidates.append({
            "name": f"Graph theory result from {paper.get('id', 'unknown')}",
            "statement": "A property of graphs mentioned in the paper",
            "objects": ["graphs", "vertices", "edges"],
            "difficulty": "Medium",
            "value": "Extends graph theory library",
            "formalization_hints": "Use SimpleGraph from mathlib4",
            "source_paper": {
                "id": paper.get('id'),
                "title": paper.get('title'),
                "authors": paper.get('authors', [])[:3],
                "categories": paper.get('categories', [])
            },
            "id": f"{paper.get('id', 'unknown')}_graph"
        })
    
    return candidates

def main():
    parser = argparse.ArgumentParser(description="Extract formalizable theorems from papers")
    parser.add_argument("--input", required=True, help="Input JSON file with papers")
    parser.add_argument("--output", required=True, help="Output JSON file for candidates")
    parser.add_argument("--max-candidates", type=int, default=10, 
                       help="Maximum candidates to extract")
    parser.add_argument("--model", default="mlx-community/Qwen2.5-7B-Instruct-4bit",
                       help="MLX model to use for extraction")
    
    args = parser.parse_args()
    
    # Load papers
    with open(args.input, 'r') as f:
        data = json.load(f)
    
    papers = data.get('papers', [])
    print(f"Processing {len(papers)} papers...")
    
    # Load model if available
    model = None
    tokenizer = None
    if MLX_AVAILABLE:
        print(f"Loading model: {args.model}")
        try:
            model, tokenizer = load(args.model)
            print("✓ Model loaded")
        except Exception as e:
            print(f"Failed to load model: {e}")
            print("Falling back to simulation mode")
    
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
