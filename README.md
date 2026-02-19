<p align="center">
  <img src="https://img.shields.io/badge/Lean_4-v4.29.0-blue?style=for-the-badge&logo=data:image/svg+xml;base64,PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHZpZXdCb3g9IjAgMCAyNCAyNCI+PHBhdGggZD0iTTEyIDJMMyAyMGgxOEwxMiAyeiIgZmlsbD0id2hpdGUiLz48L3N2Zz4=" alt="Lean 4">
  <img src="https://img.shields.io/badge/mathlib4-8025_files-green?style=for-the-badge" alt="mathlib4">
  <img src="https://img.shields.io/badge/arXiv-daily_sync-red?style=for-the-badge&logo=arxiv" alt="arXiv">
  <img src="https://img.shields.io/badge/LLM-DeepSeek_Coder_V2-purple?style=for-the-badge" alt="LLM">
  <img src="https://img.shields.io/badge/license-MIT-yellow?style=for-the-badge" alt="License">
</p>

<h1 align="center">Lean Math AI</h1>

<p align="center">
  <strong>Autonomous formal mathematics research that runs while you sleep.</strong><br>
  AI reads today's math papers, extracts theorems, writes Lean 4 proofs, and verifies them — every hour, automatically.
</p>

<p align="center">
  <a href="#quick-start">Quick Start</a> &bull;
  <a href="#how-it-works">How It Works</a> &bull;
  <a href="#why-this-matters">Why This Matters</a> &bull;
  <a href="#results">Results</a> &bull;
  <a href="#contributing">Contributing</a>
</p>

---

## Why This Matters

Mathematics has a verification crisis. Published proofs can contain errors that go undetected for years. Formal verification in proof assistants like Lean 4 is the gold standard — but manually formalizing a single theorem can take days or weeks.

**Lean Math AI bridges this gap.** It continuously:

1. Monitors arXiv for new mathematical results
2. Uses AI to understand and extract theorem statements
3. Generates formal Lean 4 code with machine-checkable proofs
4. Verifies every step with the Lean compiler
5. Reports results honestly — no fake "proven" claims

This is infrastructure for **accelerating mathematical knowledge**. Every theorem that gets formally verified becomes permanently trustworthy, machine-readable, and composable with the rest of mathematics.

## Demo: Real Output

The AI reads a paper about K5-minor-free graph colorings and generates:

```lean
import Mathlib
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring

/-- For every K₅-minor-free graph G and every correspondence 6-cover M of G,
    there exist 3 pairwise disjoint M-colorings of G. -/
theorem disjoint_correspondence_colorings
    (V : Type) [Fintype V] (G : SimpleGraph V)
    [DecidableEq V] [Fintype (G.edgeSet)] :
    ∃ (φ1 φ2 φ3 : G.Coloring (Fin 6)),
    ∀ v, φ1 v ≠ φ2 v ∧ φ1 v ≠ φ3 v ∧ φ2 v ≠ φ3 v := by
  sorry -- Proof requires deep graph theory
```

Compare to what most systems produce: `theorem X : True := by trivial`

**This system generates real mathematics, not placeholders.**

## How It Works

```
    ┌─────────────┐     ┌──────────────┐     ┌───────────────┐
    │   arXiv API  │────▸│  LLM Reads    │────▸│  Lean 4 Code  │
    │  50 papers   │     │  Abstracts    │     │  Generation   │
    │  per night   │     │  Extracts     │     │  Real theorem │
    └─────────────┘     │  Theorems     │     │  statements   │
                        └──────────────┘     └───────┬───────┘
                                                     │
    ┌─────────────┐     ┌──────────────┐             │
    │   Morning    │◂────│  Honest      │◂────────────┘
    │   Report     │     │  Verification│
    │   Markdown   │     │  5-tier      │
    └─────────────┘     │  classify    │
                        └──────────────┘
```

### The Pipeline

| Phase | Time | What Happens |
|-------|------|-------------|
| **Paper Ingest** | Hourly | Downloads 50 papers from arXiv (math.NT, math.CO) |
| **Theorem Extraction** | Hourly | LLM reads abstracts, identifies formalizable claims |
| **Formalization** | Hourly | Generates Lean 4 code with real theorem statements |
| **Verification** | Hourly | `lake env lean` checks each file individually |
| **Reporting** | Hourly | Markdown report with honest status categories |

### Honest 5-Tier Verification

Most AI proof systems claim everything works. We don't.

| Status | Meaning | Icon |
|--------|---------|------|
| **PROVEN** | Compiles with no `sorry` — fully verified | ✅ |
| **FORMALIZED** | Compiles with `sorry` — statement correct, proof incomplete | 🔶 |
| **FAILED** | Does not compile — needs syntax fixes | ❌ |
| **TEMPLATE** | LLM fallback — not real AI output | ⚠️ |
| **TRIVIAL** | `True := by trivial` — meaningless | 🚫 |

## Quick Start

### Prerequisites

- macOS with Apple Silicon (M1/M2/M3/M4)
- 16GB+ RAM (for local LLM)
- Python 3.10+
- Git

### 1. Clone & Setup

```bash
git clone https://github.com/JesseRod329/lean-math-ai.git
cd lean-math-ai
./scripts/setup-lean-math.sh
```

This installs Lean 4, mathlib4 (8,025 cached files), and the DeepSeek-Coder-V2-Lite LLM.

> First run takes 10-20 minutes for mathlib4 cache download.

### 2. Run Once

```bash
./scripts/nightly-math-loop.sh
```

Watch as the system:
- Downloads today's papers from arXiv
- Extracts theorem candidates using AI
- Generates Lean 4 formalizations
- Verifies each proof individually
- Generates a report

### 3. Enable Hourly Automation

```bash
# Install launchd job (macOS)
cp scripts/com.lean-math-ai.hourly.plist ~/Library/LaunchAgents/
launchctl load ~/Library/LaunchAgents/com.lean-math-ai.hourly.plist
```

The system now runs every hour, automatically. Check status:

```bash
# View latest results
cat daily-reports/report-$(date +%Y-%m-%d).md

# Watch live
tail -f logs/hourly-$(date +%Y-%m-%d).log

# Dashboard
open http://localhost:8765
```

## Architecture

```
lean-math-ai/
├── MathAI/                          # Lean 4 project (mathlib4)
│   ├── lakefile.toml                # Dependencies
│   └── lean-toolchain               # Lean 4 v4.29.0-rc1
├── scripts/
│   ├── fetch-arxiv-papers.py        # arXiv API client
│   ├── extract-theorems.py          # LLM theorem extraction
│   ├── llm-formalize-v2.py          # Multi-backend proof generation
│   ├── verify-proof.sh              # 5-tier verification
│   ├── generate-report.py           # Honest reporting
│   ├── nightly-math-loop.sh         # Full pipeline
│   ├── hourly-math-loop.sh          # Incremental pipeline
│   └── setup-lean-math.sh           # One-time setup
├── proofs/                          # Generated .lean files
├── completed-proofs/                # Verified results (JSONL)
├── failed-attempts/                 # Failed/template results
├── papers/                          # Downloaded arXiv papers
├── target-theorems/                 # Extracted candidates
├── daily-reports/                   # Markdown reports
├── dashboard/                       # Visual web dashboard
└── logs/                            # Execution logs
```

## LLM Backends

The system supports multiple backends, tried in order:

| Backend | Quality | Cost | Speed |
|---------|---------|------|-------|
| OpenAI GPT-4o | Best | ~$0.03/proof | Fast |
| Claude 3.5 Sonnet | Excellent | ~$0.03/proof | Fast |
| **DeepSeek-Coder-V2-Lite** | Good | **Free (local)** | Medium |
| Template fallback | Basic | Free | Instant |

Default: **DeepSeek-Coder-V2-Lite 16B** running locally on Apple Silicon via MLX. No API keys needed.

To use cloud APIs for better results:

```bash
export OPENAI_API_KEY="sk-..."      # Optional
export ANTHROPIC_API_KEY="sk-ant-..." # Optional
```

## Configuration

### arXiv Categories

```python
# In scripts/fetch-arxiv-papers.py
# Default: Number Theory + Combinatorics
categories = ["math.NT", "math.CO"]

# Add more:
categories = ["math.NT", "math.CO", "math.GR", "math.AG", "cs.DM"]
```

### LLM Model

```bash
# Default (16B, good balance)
--model mlx-community/DeepSeek-Coder-V2-Lite-Instruct-4bit

# Larger, smarter (needs 32GB RAM)
--model mlx-community/Qwen2.5-32B-Instruct-4bit

# Smaller, faster (needs 8GB RAM)
--model mlx-community/Qwen2.5-7B-Instruct-4bit
```

### Automation Schedule

```bash
# Hourly (default)
launchctl load ~/Library/LaunchAgents/com.lean-math-ai.hourly.plist

# Or use cron
crontab -e
0 * * * * cd /path/to/lean-math-ai && ./scripts/hourly-math-loop.sh
```

## Results

### Sample Daily Report

```
| Metric                              | Count          |
|--------------------------------------|----------------|
| Proven (compiles, no sorry)          | 0              |
| Formalized (compiles, has sorry)     | 3              |
| Failed (does not compile)            | 5              |
| Templates (LLM fallback)            | 2              |
| Real Success Rate                    | 30% (3/10)     |
```

This is **honest**. Most AI math systems would report 100% by proving `True`.

### What Success Looks Like

- **Week 1**: Pipeline running, generating real theorem statements
- **Month 1**: First proofs that compile without `sorry`
- **Month 3**: Consistent formalization rate, contributing to mathlib4
- **Month 6**: Novel results, academic recognition

## The Vision

Mathematics is humanity's most reliable form of knowledge — but only when verified. Today:

- **~2 million** math papers exist on arXiv
- **< 1%** have been formally verified
- **Errors** in published proofs go undetected for years
- **Mathlib4** has ~120K theorems — we need millions more

Lean Math AI is a step toward **automated formal mathematics at scale**. Every theorem we formalize:

- Becomes permanently trustworthy
- Can be composed with other verified results
- Is machine-readable for future AI systems
- Helps catch errors in published mathematics

This isn't just a tool — it's infrastructure for **making mathematical knowledge more reliable for everyone**.

## Contributing

We welcome contributions at every level:

- **Run it**: Just running the system and sharing results helps
- **Fix proofs**: Take a FORMALIZED proof (compiles with sorry) and fill in the proof
- **Improve prompts**: Better LLM prompts = better theorem extraction
- **Add categories**: Extend to new areas of mathematics
- **Submit to mathlib4**: Clean up verified proofs and contribute upstream

```bash
# Fork, clone, and run
git clone https://github.com/YOUR_USERNAME/lean-math-ai.git
cd lean-math-ai
./scripts/setup-lean-math.sh
./scripts/nightly-math-loop.sh
```

## Troubleshooting

<details>
<summary><strong>Lean build fails</strong></summary>

```bash
cd MathAI && lake clean && lake update && lake exe cache get
```
</details>

<details>
<summary><strong>LLM model won't load</strong></summary>

```bash
# Check MLX
python3 -c "from mlx_lm import load; print('OK')"

# Re-install
pip3 install --break-system-packages mlx-lm
```
</details>

<details>
<summary><strong>No papers downloaded</strong></summary>

Check internet connection and arXiv API accessibility:
```bash
curl -s "http://export.arxiv.org/api/query?search_query=cat:math.NT&max_results=1" | head -5
```
</details>

<details>
<summary><strong>All proofs fail verification</strong></summary>

This is expected early on. The 16B local model generates reasonable theorem statements but often uses incorrect mathlib4 API names. Solutions:
- Use a larger model (32B) or cloud API (GPT-4o, Claude)
- Focus on simpler theorems (filter by difficulty: Easy)
- Manually fix common patterns in generated code
</details>

## Resources

- [Lean 4 Manual](https://lean-lang.org/lean4/doc/)
- [Mathlib4 Documentation](https://leanprover-community.github.io/mathlib4_docs/)
- [arXiv API](https://arxiv.org/help/api)
- [Lean Zulip Chat](https://leanprover.zulipchat.com/)
- [MLX Documentation](https://ml-explore.github.io/mlx/)

## License

MIT

---

<p align="center">
  <strong>Proving mathematics while you sleep.</strong><br>
  <sub>Built with Lean 4, mathlib4, and local LLMs on Apple Silicon.</sub>
</p>
