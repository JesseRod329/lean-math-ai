#!/usr/bin/env python3
"""
build-mathlib-index.py
Build a keyword-searchable index of Mathlib theorems for pseudo-RAG.
Uses TF-IDF-style scoring with Python stdlib only (no numpy/sklearn).
"""

import argparse
import json
import math
import os
import re
from collections import Counter, defaultdict


def tokenize(text):
    """Tokenize text into lowercase keywords, splitting CamelCase and dots"""
    # Split on dots and underscores
    parts = re.split(r'[._/]', text)
    tokens = []
    for part in parts:
        # Split CamelCase
        camel_parts = re.sub(r'([a-z])([A-Z])', r'\1 \2', part).split()
        for cp in camel_parts:
            token = cp.lower().strip()
            if len(token) > 1 and not token.isdigit():
                tokens.append(token)
    return tokens


def build_inverted_index(mathlib_index_path):
    """Build an inverted index from the mathlib JSON index"""
    with open(mathlib_index_path) as f:
        index = json.load(f)

    # Document = each theorem entry
    documents = []  # list of (name, sig, doc, module, domain)
    for domain, info in index.items():
        for thm in info.get('theorems', []):
            documents.append({
                'name': thm['name'],
                'sig': thm.get('sig', ''),
                'doc': thm.get('doc', ''),
                'module': thm.get('module', info.get('module', '')),
                'domain': domain,
                'type': thm.get('type', 'theorem')
            })

    # Build inverted index: token -> list of doc indices
    inv_index = defaultdict(list)
    doc_token_counts = []  # token counts per document

    for i, doc in enumerate(documents):
        # Combine name + sig + doc for tokenization
        text = f"{doc['name']} {doc['sig']} {doc['doc']}"
        tokens = tokenize(text)
        counts = Counter(tokens)
        doc_token_counts.append(counts)

        for token in set(tokens):
            inv_index[token].append(i)

    # Compute IDF scores
    num_docs = len(documents)
    idf = {}
    for token, doc_ids in inv_index.items():
        idf[token] = math.log(num_docs / (1 + len(doc_ids)))

    return documents, inv_index, doc_token_counts, idf


def search(query, documents, inv_index, doc_token_counts, idf, top_k=30):
    """Search the index for theorems relevant to a query"""
    query_tokens = tokenize(query)
    if not query_tokens:
        return []

    # Score each matching document
    scores = defaultdict(float)
    for token in query_tokens:
        if token not in inv_index:
            continue
        token_idf = idf.get(token, 0)
        for doc_idx in inv_index[token]:
            tf = doc_token_counts[doc_idx].get(token, 0)
            scores[doc_idx] += tf * token_idf

    # Sort by score
    ranked = sorted(scores.items(), key=lambda x: -x[1])

    results = []
    for doc_idx, score in ranked[:top_k]:
        doc = documents[doc_idx]
        results.append({
            'name': doc['name'],
            'sig': doc['sig'],
            'doc': doc['doc'],
            'module': doc['module'],
            'domain': doc['domain'],
            'type': doc['type'],
            'score': round(score, 2)
        })

    return results


def search_mathlib(query, top_k=30, index_path=None):
    """Convenience function for use by other scripts"""
    if index_path is None:
        index_path = os.path.join(
            os.path.dirname(__file__), '..', 'MathAI', '.lake', 'mathlib-index.json'
        )

    if not os.path.exists(index_path):
        return ""

    documents, inv_index, doc_token_counts, idf = build_inverted_index(index_path)
    results = search(query, documents, inv_index, doc_token_counts, idf, top_k)

    lines = []
    for r in results:
        lines.append(f"-- import {r['module']}")
        sig_preview = r['sig'][:80] if r['sig'] else ''
        lines.append(f"--   {r['type']} {r['name']}{': ' + sig_preview if sig_preview else ''}")
        if r['doc']:
            lines.append(f"--   ({r['doc'][:60]})")

    return '\n'.join(lines)


def main():
    parser = argparse.ArgumentParser(description="Build and query Mathlib search index")
    parser.add_argument("--index-path",
                       default=os.path.join(os.path.dirname(__file__), '..', 'MathAI', '.lake', 'mathlib-index.json'),
                       help="Path to mathlib-index.json")
    parser.add_argument("--query", default=None,
                       help="Search query (if provided, runs a search instead of just building)")
    parser.add_argument("--top-k", type=int, default=30,
                       help="Number of results to return")

    args = parser.parse_args()

    if not os.path.exists(args.index_path):
        print(f"Index not found at {args.index_path}")
        print("Run export-mathlib-map.py first to build the index")
        return

    print(f"Loading index from {args.index_path}...")
    documents, inv_index, doc_token_counts, idf = build_inverted_index(args.index_path)
    print(f"Indexed {len(documents)} declarations, {len(inv_index)} unique tokens")

    if args.query:
        print(f"\nSearching for: {args.query}")
        print("=" * 60)
        results = search(args.query, documents, inv_index, doc_token_counts, idf, args.top_k)
        for i, r in enumerate(results, 1):
            print(f"{i:3d}. [{r['score']:5.1f}] {r['type']} {r['name']}")
            if r['sig']:
                print(f"     {r['sig'][:80]}")
            if r['doc']:
                print(f"     -- {r['doc'][:60]}")
            print(f"     module: {r['module']}")
            print()
    else:
        print("Use --query to search. Example:")
        print(f"  python3 {__file__} --query 'prime number divisor'")


if __name__ == "__main__":
    main()
