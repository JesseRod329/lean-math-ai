#!/bin/bash
# update-mathlib.sh
# Update mathlib4 and regenerate the theorem index

set -e

PROJECT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
MATHAI_DIR="$PROJECT_DIR/MathAI"

export PATH="$HOME/.elan/bin:$PATH"

echo "Updating mathlib4..."
cd "$MATHAI_DIR"

# Update lake dependencies
lake update
echo "Building (fetching cache)..."
lake exe cache get
lake build

echo ""
echo "Regenerating mathlib index..."
cd "$PROJECT_DIR"
python3 scripts/export-mathlib-map.py \
    --categories math.CO math.NT \
    --output MathAI/.lake/mathlib-index.json

echo ""
echo "Done. Review changes:"
echo "  git diff MathAI/lake-manifest.json"
echo "  git diff MathAI/lean-toolchain"
echo ""
echo "If satisfied, commit:"
echo "  git add MathAI/lake-manifest.json MathAI/lean-toolchain"
echo "  git commit -m 'chore: update mathlib4'"
