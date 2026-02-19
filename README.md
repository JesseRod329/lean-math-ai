# Lean 4 + LLM Mathematics Automation 🎯🔬

Autonomous formal mathematics research using Lean 4 and local LLMs on your M4 Mac.

## 🌙 The "Sleep & Prove" System

While you sleep, this system:
1. Downloads latest math papers from arXiv
2. Identifies theorems suitable for formalization
3. Generates Lean 4 proofs using local LLM
4. Verifies proofs with Lean compiler
5. Generates morning report with results

## 📁 Directory Structure

```
lean-math-ai/
├── MathAI/                    # Lean 4 project with mathlib4
│   ├── MathAI.lean
│   └── lake-manifest.json
├── scripts/
│   ├── setup-lean-math.sh     # One-time setup
│   ├── nightly-math-loop.sh   # Main automation loop
│   ├── fetch-arxiv-papers.py  # Download papers
│   ├── extract-theorems.py    # Identify theorems with LLM
│   ├── llm-formalize.py       # Generate Lean code
│   └── generate-report.py     # Create daily reports
├── papers/                    # Downloaded arXiv papers
├── target-theorems/           # Theorem candidates
├── proofs/                    # Generated Lean proofs
├── completed-proofs/          # Successfully verified proofs
├── failed-attempts/           # Failed proof attempts
├── daily-reports/             # Morning reports
└── logs/                      # Execution logs
```

## 🚀 Quick Start

### 1. Run Setup (One Time)

```bash
cd /Users/Jesse/clawd/lean-math-ai
./scripts/setup-lean-math.sh
```

This will:
- Install elan (Lean version manager)
- Install Lean 4 v4.16.0
- Create MathAI project with mathlib4
- Install Python dependencies (mlx-lm, openai, etc.)

**Note:** The mathlib4 setup takes 10-20 minutes on first run.

### 2. Test the Pipeline

```bash
# Run a single iteration manually
./scripts/nightly-math-loop.sh
```

### 3. Set Up Nightly Automation

Add to crontab (runs at 11 PM nightly):

```bash
# Edit crontab
crontab -e

# Add this line:
0 23 * * * cd /Users/Jesse/clawd/lean-math-ai && ./scripts/nightly-math-loop.sh >> logs/cron.log 2>&1
```

Or use launchd on macOS (recommended):

```bash
# Create plist file
cat > ~/Library/LaunchAgents/com.lean-math-ai.nightly.plist << 'EOF'
<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0">
<dict>
    <key>Label</key>
    <string>com.lean-math-ai.nightly</string>
    <key>ProgramArguments</key>
    <array>
        <string>/Users/Jesse/clawd/lean-math-ai/scripts/nightly-math-loop.sh</string>
    </array>
    <key>StartCalendarInterval</key>
    <dict>
        <key>Hour</key>
        <integer>23</integer>
        <key>Minute</key>
        <integer>0</integer>
    </dict>
    <key>WorkingDirectory</key>
    <string>/Users/Jesse/clawd/lean-math-ai</string>
    <key>StandardOutPath</key>
    <string>/Users/Jesse/clawd/lean-math-ai/logs/cron.log</string>
    <key>StandardErrorPath</key>
    <string>/Users/Jesse/clawd/lean-math-ai/logs/cron-error.log</string>
</dict>
</plist>
EOF

# Load the job
launchctl load ~/Library/LaunchAgents/com.lean-math-ai.nightly.plist
```

## 📊 What to Expect

### Success Metrics

| Phase | Expected Output |
|-------|----------------|
| Paper Ingest | 20-50 papers downloaded |
| Theorem ID | 5-10 candidates identified |
| Formalization | 2-5 Lean files generated |
| Verification | 1-3 proofs compile |
| Report | Morning markdown summary |

### First Target Theorem

To test the system immediately, here's a concrete first target:

**Theorem:** Every even integer greater than 2 can be expressed as the sum of two primes.

Wait — that's Goldbach's conjecture (unsolved). Let's pick something provable:

**Actual First Target:** The infinitude of primes (classic, well-documented, fits in mathlib4)

Or better yet, let the system find its own targets from recent papers!

## 🔧 Configuration

### Customize Categories

Edit `scripts/fetch-arxiv-papers.py` to change which arXiv categories to monitor:

```python
# Current categories
categories = ["math.NT", "math.CO"]  # Number Theory, Combinatorics

# Add more:
categories = ["math.NT", "math.CO", "math.GR", "math.AT", "cs.DM"]
```

### Change LLM Model

Edit model in scripts:

```python
# Current: Qwen 2.5 7B (fast, fits in 24GB)
model = "mlx-community/Qwen2.5-7B-Instruct-4bit"

# Alternative: Llama 3.2 8B
model = "mlx-community/Llama-3.2-8B-Instruct-4bit"

# Larger: Qwen 2.5 14B (slower but smarter)
model = "mlx-community/Qwen2.5-14B-Instruct-4bit"
```

### Adjust Difficulty Filter

Edit `scripts/extract-theorems.py` to change which theorems to target:

```python
# Only target "Easy" theorems for higher success rate
if candidate.get('difficulty') == 'Easy':
    process(candidate)
```

## 📈 Tracking Progress

### Daily Review Checklist

```markdown
## Morning Review Process

1. [ ] Read daily-reports/report-YYYY-MM-DD.md
2. [ ] Review completed-proofs/proven-YYYY-MM-DD.jsonl
3. [ ] Check proofs/YYYY-MM-DD/ for Lean files
4. [ ] For each proven theorem:
   - [ ] Verify proof is mathematically correct
   - [ ] Clean up code style
   - [ ] Consider submitting to mathlib4
5. [ ] For failed attempts:
   - [ ] Analyze error patterns
   - [ ] Retry with different approaches if promising
6. [ ] Commit progress to git
```

### Long-term Goals

| Milestone | Target | Recognition |
|-----------|--------|-------------|
| First Proof | Week 1 | Personal achievement |
| 10 Proofs | Month 1 | GitHub portfolio |
| 50 Proofs | Month 3 | Mathlib contributions |
| 100 Proofs | Month 6 | Research recognition |
| Novel Result | Month 6+ | Academic co-authorship |

## 🐛 Troubleshooting

### Lean Build Fails

```bash
cd MathAI
lake clean
lake update
lake exe cache get
lake build
```

### LLM Generation Fails

- Check MLX installation: `python3 -c "import mlx_lm; print('OK')"`
- Reduce model size: Use 7B instead of 14B
- Check RAM: Ensure 8GB+ available for model

### No Papers Downloaded

- Check internet connection
- Verify arXiv API is accessible
- Try different categories

### All Proofs Fail

- Check Lean installation: `lean --version`
- Verify mathlib4 is properly set up
- Start with easier theorems (difficulty: Easy)
- Review logs: `logs/nightly-YYYY-MM-DD.log`

## 🎯 Next Steps

1. **Run setup**: `./scripts/setup-lean-math.sh`
2. **Test pipeline**: `./scripts/nightly-math-loop.sh`
3. **Review results**: Check `daily-reports/`
4. **Iterate**: Adjust parameters based on results
5. **Contribute**: Submit working proofs to mathlib4

## 📚 Resources

- [Lean 4 Manual](https://lean-lang.org/lean4/doc/)
- [Mathlib4 Documentation](https://leanprover-community.github.io/mathlib4_docs/)
- [arXiv API](https://arxiv.org/help/api)
- [Formal Mathematics Zulip](https://leanprover.zulipchat.com/)

## 🏆 Success Criteria

You'll know this is working when:
- ✅ Morning reports show completed proofs
- ✅ Lean files compile without errors
- ✅ Proofs are mathematically meaningful
- ✅ Git history shows consistent progress
- ✅ Mathlib community recognizes your contributions

---

*Start proving while you sleep!* 🌙📐
