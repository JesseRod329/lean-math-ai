#!/bin/bash
# start-dashboard.sh
# Start the Lean Math AI Dashboard server

PROJECT_DIR="/Users/Jesse/clawd/lean-math-ai"
DASHBOARD_PORT="8765"

echo "🌙 Starting Lean Math AI Dashboard..."
echo ""

# Check if Python is available
if command -v python3 &> /dev/null; then
    PYTHON="python3"
elif command -v python &> /dev/null; then
    PYTHON="python"
else
    echo "❌ Python not found. Please install Python."
    exit 1
fi

cd "$PROJECT_DIR/dashboard"

echo "📊 Dashboard available at:"
echo "   http://localhost:$DASHBOARD_PORT"
echo ""
echo "🚀 Starting server... (Press Ctrl+C to stop)"
echo ""

$PYTHON -m http.server $DASHBOARD_PORT
