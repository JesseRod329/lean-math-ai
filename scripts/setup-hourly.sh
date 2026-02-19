#!/bin/bash
# setup-hourly.sh - Setup hourly Lean Math AI automation

echo "🚀 Setting up Hourly Lean Math AI Automation"
echo ""

PROJECT_DIR="/Users/Jesse/clawd/lean-math-ai"
cd "$PROJECT_DIR"

# Create necessary directories
mkdir -p logs
mkdir -p dashboard/data

# Option 1: launchd (Recommended for macOS)
echo "Option 1: launchd (macOS native, recommended)"
echo "=============================================="
echo ""
echo "To install:"
echo "  cp scripts/com.lean-math-ai.hourly.plist ~/Library/LaunchAgents/"
echo "  launchctl load ~/Library/LaunchAgents/com.lean-math-ai.hourly.plist"
echo ""
echo "To start immediately:"
echo "  launchctl start com.lean-math-ai.hourly"
echo ""
echo "To check status:"
echo "  launchctl list | grep lean-math-ai"
echo ""
echo "To stop:"
echo "  launchctl stop com.lean-math-ai.hourly"
echo "  launchctl unload ~/Library/LaunchAgents/com.lean-math-ai.hourly.plist"
echo ""

# Option 2: Cron (Universal)
echo "Option 2: Cron (works on Linux/macOS)"
echo "======================================"
echo ""
echo "To install, run:"
echo "  crontab -e"
echo ""
echo "Add this line:"
echo "  0 * * * * cd $PROJECT_DIR && ./scripts/hourly-math-loop.sh >> logs/cron.log 2>&1"
echo ""
echo "This runs at minute 0 of every hour."
echo ""

# Option 3: Manual run
echo "Option 3: Manual / Testing"
echo "==========================="
echo ""
echo "To run once manually:"
echo "  cd $PROJECT_DIR"
echo "  ./scripts/hourly-math-loop.sh"
echo ""

# Check current status
echo "Current Status:"
echo "==============="
if launchctl list | grep -q "com.lean-math-ai.hourly"; then
    echo "✓ Hourly job is LOADED in launchd"
    launchctl list | grep "com.lean-math-ai.hourly"
else
    echo "✗ Hourly job not loaded yet"
fi

echo ""
echo "Papers today: $(ls -1 papers/papers-*.json 2>/dev/null | wc -l)"
echo "Proofs generated: $(find proofs -name '*.lean' 2>/dev/null | wc -l)"
echo ""
