#!/bin/bash
# nightly-math-loop.sh
# Main automation loop for overnight mathematics research

set -e

PROJECT_DIR="/Users/Jesse/clawd/lean-math-ai"
MATHAI_DIR="$PROJECT_DIR/MathAI"
LOG_DIR="$PROJECT_DIR/logs"
DATE=$(date +%Y-%m-%d)
TIME=$(date +%H:%M:%S)

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

log() {
    echo -e "${BLUE}[$(date '+%H:%M:%S')]${NC} $1" | tee -a "$LOG_DIR/nightly-$DATE.log"
}

error() {
    echo -e "${RED}[ERROR]${NC} $1" | tee -a "$LOG_DIR/nightly-$DATE.log"
}

success() {
    echo -e "${GREEN}[SUCCESS]${NC} $1" | tee -a "$LOG_DIR/nightly-$DATE.log"
}

warning() {
    echo -e "${YELLOW}[WARNING]${NC} $1" | tee -a "$LOG_DIR/nightly-$DATE.log"
}

export PATH="$HOME/.elan/bin:$PATH"
cd "$PROJECT_DIR"

log "🌙 Starting Nightly Mathematics Automation Loop"
log "Date: $DATE"
log "Project: $PROJECT_DIR"
echo ""

# Phase 1: Paper Ingest (11:00 PM)
log "═══════════════════════════════════════════════════"
log "PHASE 1: Paper Ingest (11:00 PM)"
log "═══════════════════════════════════════════════════"
python3 scripts/fetch-arxiv-papers.py --category math.NT --category math.CO --days 1 --output papers/papers-$DATE.json
PAPER_COUNT=$(jq '. | length' papers/papers-$DATE.json 2>/dev/null || echo "0")
log "Downloaded $PAPER_COUNT papers"

# Phase 2: Candidate Identification (12:00 AM)
log ""
log "═══════════════════════════════════════════════════"
log "PHASE 2: Candidate Identification (12:00 AM)"
log "═══════════════════════════════════════════════════"
python3 scripts/extract-theorems.py \
    --input papers/papers-$DATE.json \
    --output target-theorems/candidates-$DATE.json \
    --max-candidates 10 \
    --model mlx-community/DeepSeek-Coder-V2-Lite-Instruct-4bit
candidates=$(jq '.candidates | length' target-theorems/candidates-$DATE.json 2>/dev/null || echo "0")
log "Identified $candidates theorem candidates"

# Phase 3: Formalization Attempts (1:00 AM - 3:00 AM)
log ""
log "═══════════════════════════════════════════════════"
log "PHASE 3: Formalization Attempts (1:00 AM - 3:00 AM)"
log "═══════════════════════════════════════════════════"

mkdir -p proofs/$DATE

# Track counts
proven_count=0
formalized_count=0
failed_count=0
template_count=0
trivial_count=0

# Process each candidate (use process substitution to avoid subshell)
while read -r candidate; do
    theorem_id=$(echo "$candidate" | jq -r '.id')
    theorem_name=$(echo "$candidate" | jq -r '.name')

    log "Processing: $theorem_name ($theorem_id)"

    # Generate Lean formalization with v2 script
    python3 scripts/llm-formalize-v2.py \
        --candidate "$candidate" \
        --output proofs/$DATE/${theorem_id}.lean \
        --model mlx-community/DeepSeek-Coder-V2-Lite-Instruct-4bit \
        --attempts 3

    if [ -f "proofs/$DATE/${theorem_id}.lean" ]; then
        # Verify with Lean (individual file check)
        log "Verifying $theorem_id with Lean..."

        VERIFY_OUTPUT=$(bash scripts/verify-proof.sh "proofs/$DATE/${theorem_id}.lean" 2>&1)
        VERIFY_EXIT=$?

        case $VERIFY_EXIT in
            0)
                success "PROVEN: $theorem_name (compiles, no sorry!)"
                echo "$candidate" | jq '. + {"status": "proven", "date": "'"$DATE"'"}' >> completed-proofs/proven-$DATE.jsonl
                ((proven_count++)) || true
                ;;
            1)
                success "FORMALIZED: $theorem_name (compiles with sorry)"
                echo "$candidate" | jq '. + {"status": "formalized", "date": "'"$DATE"'"}' >> completed-proofs/formalized-$DATE.jsonl
                ((formalized_count++)) || true
                ;;
            2)
                error "FAILED: $theorem_name (does not compile)"
                echo "$candidate" | jq '. + {"status": "failed", "date": "'"$DATE"'"}' >> failed-attempts/failed-$DATE.jsonl
                ((failed_count++)) || true
                ;;
            4)
                warning "TEMPLATE: $theorem_name (LLM fallback)"
                echo "$candidate" | jq '. + {"status": "template", "date": "'"$DATE"'"}' >> failed-attempts/templates-$DATE.jsonl
                ((template_count++)) || true
                ;;
            5)
                warning "TRIVIAL: $theorem_name (True := by, not real math)"
                echo "$candidate" | jq '. + {"status": "trivial", "date": "'"$DATE"'"}' >> failed-attempts/trivial-$DATE.jsonl
                ((trivial_count++)) || true
                ;;
        esac

        log "  $VERIFY_OUTPUT"
    fi
done < <(jq -c '.candidates[]' target-theorems/candidates-$DATE.json 2>/dev/null)

# Phase 4: Documentation (5:00 AM)
log ""
log "═══════════════════════════════════════════════════"
log "PHASE 4: Documentation (5:00 AM)"
log "═══════════════════════════════════════════════════"

python3 scripts/generate-report.py \
    --date $DATE \
    --output daily-reports/report-$DATE.md

success "Daily report generated: daily-reports/report-$DATE.md"

# Phase 5: Summary
log ""
log "═══════════════════════════════════════════════════"
log "PHASE 5: Nightly Summary"
log "═══════════════════════════════════════════════════"

log "Session Complete!"
log "  Proven (no sorry):    $proven_count"
log "  Formalized (sorry):   $formalized_count"
log "  Failed (bad syntax):  $failed_count"
log "  Templates (fallback): $template_count"
log "  Trivial (True):       $trivial_count"
log "Report: daily-reports/report-$DATE.md"

success "🌅 Nightly loop complete. Review the report in the morning!"
