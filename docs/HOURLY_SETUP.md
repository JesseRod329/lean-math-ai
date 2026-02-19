# Hourly Math Automation Setup

Run your Lean Math AI system **every hour** instead of nightly.

---

## 🚀 Quick Start (Choose One)

### Option A: launchd (Recommended for macOS)

```bash
cd /Users/Jesse/clawd/lean-math-ai

# Install the hourly job
cp scripts/com.lean-math-ai.hourly.plist ~/Library/LaunchAgents/
launchctl load ~/Library/LaunchAgents/com.lean-math-ai.hourly.plist

# Start immediately
launchctl start com.lean-math-ai.hourly
```

**Status:**
```bash
launchctl list | grep lean-math-ai
```

**Stop:**
```bash
launchctl stop com.lean-math-ai.hourly
launchctl unload ~/Library/LaunchAgents/com.lean-math-ai.hourly.plist
```

---

### Option B: Cron (Works everywhere)

```bash
# Edit crontab
crontab -e

# Add this line (runs every hour at minute 0):
0 * * * * cd /Users/Jesse/clawd/lean-math-ai && ./scripts/hourly-math-loop.sh >> logs/cron.log 2>&1
```

**Check:**
```bash
crontab -l
```

---

### Option C: Manual (For testing)

```bash
cd /Users/Jesse/clawd/lean-math-ai
./scripts/hourly-math-loop.sh
```

---

## 📊 What Happens Every Hour

| Minute | Action |
|--------|--------|
| 00 | Check for new papers (download once/day) |
| 02 | Extract theorem candidates |
| 05 | Process **1-2 unprocessed** theorems with AI |
| 10 | Verify proofs with Lean compiler |
| 15 | Update dashboard |

**Rate limit:** 2 theorems per hour (prevents overwhelming your system)

---

## 📁 File Organization

```
proofs/
├── 2026-02-19/
│   ├── 20260219_130000/     ← Hour 13:00
│   │   ├── 2602.16692v1.lean
│   │   └── 2602.16605v1.lean
│   ├── 20260219_140000/     ← Hour 14:00
│   │   ├── 2602.16333v1.lean
│   │   └── ...
```

---

## 🎨 Dashboard Updates

The dashboard at `http://localhost:8765` shows:
- ✅ Last update timestamp
- ✅ Papers processed today
- ✅ Theorems in queue
- ✅ Proofs completed this hour
- ✅ Real-time status

---

## 💡 Tips

1. **Start manually first** to verify everything works:
   ```bash
   ./scripts/hourly-math-loop.sh
   ```

2. **Check logs** if something breaks:
   ```bash
   tail -f logs/hourly-$(date +%Y-%m-%d).log
   ```

3. **Monitor progress**:
   ```bash
   watch -n 30 'ls -1 proofs/$(date +%Y-%m-%d)/*/ | wc -l'
   ```

4. **Adjust rate limit** (edit `hourly-math-loop.sh` line 77):
   ```bash
   max_per_hour=5  # Increase if you want more per hour
   ```

---

## 📈 Expected Output

With 10 theorems and 2 per hour:
- **10:00** - 2 proofs generated
- **11:00** - 2 proofs generated  
- **12:00** - 2 proofs generated
- **13:00** - 2 proofs generated
- **14:00** - 2 proofs generated
- **Total:** All 10 done in ~5 hours

---

## 🔧 Troubleshooting

| Problem | Solution |
|---------|----------|
| Job not running | Check `logs/hourly-launchd-error.log` |
| Lean not found | Make sure `source ~/.elan/env` is in your shell profile |
| MLX errors | First run downloads model (~10GB), be patient |
| Too many proofs | Lower `max_per_hour` in the script |

---

## 🚀 Advanced: Mix Both Systems

**Nightly** (full batch):
```bash
# Run at 11 PM daily
0 23 * * * ./scripts/nightly-math-loop.sh
```

**Hourly** (continuous):
```bash
# Already running via launchd
```

This gives you:
- Nightly: Bulk download and identify
- Hourly: Steady proof generation throughout the day

---

*Your math robot now works 24/7* 🧧📐
