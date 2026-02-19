#!/usr/bin/env python3
"""
generate-report.py
Generate daily report of formalization attempts
"""

import argparse
import json
from datetime import datetime

def count_lines(filepath):
    """Count lines in a file"""
    try:
        with open(filepath, 'r') as f:
            return sum(1 for _ in f)
    except FileNotFoundError:
        return 0

def generate_report(date, output_file):
    """Generate markdown report for the day"""
    
    # Count results
    proven_count = count_lines(f"completed-proofs/proven-{date}.jsonl")
    failed_count = count_lines(f"failed-attempts/failed-{date}.jsonl")
    
    # Read candidates
    try:
        with open(f"target-theorems/candidates-{date}.json", 'r') as f:
            candidates_data = json.load(f)
            candidates = candidates_data.get('candidates', [])
    except FileNotFoundError:
        candidates = []
    
    # Generate report
    report = f"""# Daily Mathematics Report - {date}

## Summary

| Metric | Count |
|--------|-------|
| **Theorems Proven** | {proven_count} |
| **Attempts Failed** | {failed_count} |
| **Total Candidates** | {len(candidates)} |
| **Success Rate** | {(proven_count / (proven_count + failed_count) * 100) if (proven_count + failed_count) > 0 else 0:.1f}% |

---

## Candidate Theorems

"""
    
    for i, candidate in enumerate(candidates, 1):
        source = candidate.get('source_paper', {})
        report += f"""### {i}. {candidate.get('name', 'Unnamed Theorem')}

**Source:** [{source.get('title', 'Unknown')}](https://arxiv.org/abs/{source.get('id', '')})

**Statement:** {candidate.get('statement', 'No statement provided')}

**Mathematical Objects:** {', '.join(candidate.get('objects', []))}

**Difficulty:** {candidate.get('difficulty', 'Unknown')}

**Value:** {candidate.get('value', 'No value statement')}

---

"""
    
    # Add proven theorems section
    if proven_count > 0:
        report += """## ✅ Proven Theorems

"""
        try:
            with open(f"completed-proofs/proven-{date}.jsonl", 'r') as f:
                content = f.read()
                # Handle JSONL with potential multi-line entries
                decoder = json.JSONDecoder()
                idx = 0
                while idx < len(content.strip()):
                    try:
                        theorem, end = decoder.raw_decode(content, idx)
                        report += f"- **{theorem.get('name', 'Unknown')}** ({theorem.get('difficulty', 'Unknown')})\n"
                        idx = content.find('{', end)
                        if idx == -1:
                            break
                    except json.JSONDecodeError:
                        break
        except FileNotFoundError:
            pass
        
        report += "\n"
    
    # Add failed attempts section
    if failed_count > 0:
        report += """## ❌ Failed Attempts

"""
        try:
            with open(f"failed-attempts/failed-{date}.jsonl", 'r') as f:
                content = f.read()
                decoder = json.JSONDecoder()
                idx = 0
                while idx < len(content.strip()):
                    try:
                        theorem, end = decoder.raw_decode(content, idx)
                        report += f"- **{theorem.get('name', 'Unknown')}** ({theorem.get('difficulty', 'Unknown')})\n"
                        idx = content.find('{', end)
                        if idx == -1:
                            break
                    except json.JSONDecodeError:
                        break
        except FileNotFoundError:
            pass
        
        report += "\n"
    
    # Add next steps
    report += f"""## Next Steps

1. Review the formalized proofs in `proofs/{date}/`
2. For successful proofs: Clean up and consider submitting to mathlib4
3. For failed attempts: Analyze errors and retry with different approaches
4. Continue monitoring arXiv for new candidates

---

*Generated at {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}*
"""
    
    # Write report
    with open(output_file, 'w') as f:
        f.write(report)
    
    print(f"Report generated: {output_file}")

def main():
    parser = argparse.ArgumentParser(description="Generate daily report")
    parser.add_argument("--date", required=True, help="Date (YYYY-MM-DD)")
    parser.add_argument("--output", required=True, help="Output markdown file")
    
    args = parser.parse_args()
    
    generate_report(args.date, args.output)

if __name__ == "__main__":
    main()
