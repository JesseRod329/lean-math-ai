#!/bin/bash
# verify-proof.sh - Verify a single Lean 4 proof file against MathAI/mathlib4
#
# Usage: bash scripts/verify-proof.sh <proof-file.lean>
#
# Exit codes:
#   0 = PROVEN     (compiles, no sorry)
#   1 = FORMALIZED (compiles, has sorry — statement correct, proof incomplete)
#   2 = FAILED     (does not compile)
#   4 = TEMPLATE   (has TEMPLATE_FALLBACK marker — not real LLM output)
#   5 = TRIVIAL    (has True := by — meaningless proof)

PROOF_FILE="$1"
PROJECT_DIR="/Users/Jesse/clawd/lean-math-ai"
MATHAI_DIR="$PROJECT_DIR/MathAI"

# Verify file exists
if [ ! -f "$PROOF_FILE" ]; then
    echo "ERROR: File not found: $PROOF_FILE"
    exit 3
fi

# Make path absolute
case "$PROOF_FILE" in
    /*) ;; # already absolute
    *) PROOF_FILE="$(pwd)/$PROOF_FILE" ;;
esac

# Check for template fallback marker
if grep -q "STATUS: TEMPLATE_FALLBACK" "$PROOF_FILE" 2>/dev/null; then
    echo "TEMPLATE: $(basename $PROOF_FILE)"
    exit 4
fi

# Check for trivial proof (True := by trivial or True := by)
if grep -q "True := by" "$PROOF_FILE" 2>/dev/null; then
    # Only flag as trivial if there's no real theorem alongside it
    sorry_count=$(grep -c "sorry" "$PROOF_FILE" 2>/dev/null || true)
    sorry_count=${sorry_count:-0}
    if [ "$sorry_count" -eq 0 ]; then
        echo "TRIVIAL: $(basename $PROOF_FILE)"
        exit 5
    fi
fi

# Check for sorry
HAS_SORRY=$(grep -c "sorry" "$PROOF_FILE" 2>/dev/null || true)
HAS_SORRY=${HAS_SORRY:-0}

# Set up Lean environment
export PATH="$HOME/.elan/bin:$PATH"

# Run lean on the file using the MathAI lake environment
cd "$MATHAI_DIR"
LEAN_OUTPUT=$(lake env lean "$PROOF_FILE" 2>&1)
LEAN_EXIT=$?

if [ $LEAN_EXIT -eq 0 ]; then
    if [ "$HAS_SORRY" -gt 0 ]; then
        echo "FORMALIZED: $(basename $PROOF_FILE) (compiles with sorry)"
        exit 1
    else
        echo "PROVEN: $(basename $PROOF_FILE) (compiles, no sorry!)"
        exit 0
    fi
else
    echo "FAILED: $(basename $PROOF_FILE)"
    # Show first few error lines for debugging
    echo "$LEAN_OUTPUT" | grep -E "error|Error" | head -5
    exit 2
fi
