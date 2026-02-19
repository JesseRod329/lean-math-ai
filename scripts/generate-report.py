#!/usr/bin/env python3
"""
generate-report.py
Generate daily report of formalization attempts with honest status categories
"""

import argparse
import json
from datetime import datetime

def read_json_records(filepath):
    """Read all JSON records from a multi-line JSONL file"""
    records = []
    try:
        with open(filepath, 'r') as f:
            content = f.read().strip()
        if not content:
            return records
        decoder = json.JSONDecoder()
        idx = 0
        while idx < len(content):
            try:
                record, end = decoder.raw_decode(content, idx)
                records.append(record)
                next_brace = content.find('{', end)
                if next_brace == -1:
                    break
                idx = next_brace
            except json.JSONDecodeError:
                break
    except FileNotFoundError:
        pass
    return records

def generate_report(date, output_file):
    """Generate markdown report for the day"""

    # Read results by category
    proven = read_json_records(f"completed-proofs/proven-{date}.jsonl")
    formalized = read_json_records(f"completed-proofs/formalized-{date}.jsonl")
    failed = read_json_records(f"failed-attempts/failed-{date}.jsonl")
    templates = read_json_records(f"failed-attempts/templates-{date}.jsonl")
    trivial = read_json_records(f"failed-attempts/trivial-{date}.jsonl")

    total = len(proven) + len(formalized) + len(failed) + len(templates) + len(trivial)
    real_success = len(proven) + len(formalized)
    success_rate = (real_success / total * 100) if total > 0 else 0

    # Read candidates
    try:
        with open(f"target-theorems/candidates-{date}.json", 'r') as f:
            candidates_data = json.load(f)
            candidates = candidates_data.get('candidates', [])
    except FileNotFoundError:
        candidates = []

    report = f"""# Daily Mathematics Report - {date}

## Summary

| Metric | Count |
|--------|-------|
| **Proven** (compiles, no sorry) | {len(proven)} |
| **Formalized** (compiles, has sorry) | {len(formalized)} |
| **Failed** (does not compile) | {len(failed)} |
| **Templates** (LLM fallback) | {len(templates)} |
| **Trivial** (True := by) | {len(trivial)} |
| | |
| **Real Success Rate** | {success_rate:.1f}% ({real_success}/{total}) |

---

## Candidate Theorems

"""

    for i, candidate in enumerate(candidates, 1):
        source = candidate.get('source_paper', {})
        report += f"""### {i}. {candidate.get('name', 'Unnamed Theorem')}

**Source:** [{source.get('title', 'Unknown')}](https://arxiv.org/abs/{source.get('id', '')})

**Statement:** {candidate.get('statement', 'No statement provided')}

**Difficulty:** {candidate.get('difficulty', 'Unknown')} | **Objects:** {', '.join(candidate.get('objects', []))}

---

"""

    if proven:
        report += "## ✅ Proven Theorems (No Sorry)\n\n"
        for r in proven:
            report += f"- **{r.get('name', 'Unknown')}** ({r.get('difficulty', 'Unknown')})\n"
        report += "\n"

    if formalized:
        report += "## 🔶 Formalized Theorems (Has Sorry)\n\n"
        for r in formalized:
            report += f"- **{r.get('name', 'Unknown')}** ({r.get('difficulty', 'Unknown')})\n"
        report += "\n"

    if failed:
        report += "## ❌ Failed Attempts\n\n"
        for r in failed:
            report += f"- **{r.get('name', 'Unknown')}** ({r.get('difficulty', 'Unknown')})\n"
        report += "\n"

    if templates or trivial:
        report += f"## ⚠️ Not Real ({len(templates)} templates, {len(trivial)} trivial)\n\n"
        report += "These used fallback templates and don't contain real mathematical content.\n\n"

    report += f"""## Next Steps

1. Review formalized proofs in `proofs/{date}/`
2. For proven: Clean up and consider submitting to mathlib4
3. For formalized (sorry): Fill in the proof tactics
4. For failed: Analyze Lean errors and fix syntax
5. For templates: Need better LLM or manual formalization

---

*Generated at {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}*
"""

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
