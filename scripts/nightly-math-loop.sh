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
python3 scripts/extract-theorems.py --input papers/papers-$DATE.json --output target-theorems/candidates-$DATE.json --max-candidates 10
candidates=$(jq '.candidates | length' target-theorems/candidates-$DATE.json 2>/dev/null || echo "0")
log "Identified $candidates theorem candidates"

# Phase 3: Formalization Attempts (1:00 AM - 3:00 AM)
log ""
log "═══════════════════════════════════════════════════"
log "PHASE 3: Formalization Attempts (1:00 AM - 3:00 AM)"
log "═══════════════════════════════════════════════════"

mkdir -p proofs/$DATE

# Process each candidate
jq -c '.candidates[]' target-theorems/candidates-$DATE.json 2>/dev/null | while read -r candidate; do
    theorem_id=$(echo "$candidate" | jq -r '.id')
    theorem_name=$(echo "$candidate" | jq -r '.name')
    
    log "Processing: $theorem_name ($theorem_id)"
    
    # Generate Lean formalization
    python3 scripts/llm-formalize.py \
        --candidate "$candidate" \
        --output proofs/$DATE/${theorem_id}.lean \
        --attempts 3
    
    if [ -f "proofs/$DATE/${theorem_id}.lean" ]; then
        # Verify with Lean
        log "Verifying $theorem_id with Lean..."
        
        cd "$MATHAI_DIR"
        if lake build 2>&1 | grep -q "Build completed"; then
            success "✓ $theorem_name formalized and verified"
            echo "$candidate" | jq '. + {"status": "proven", "date": "'$DATE'"}' >> ../completed-proofs/proven-$DATE.jsonl
        else
            error "✗ $theorem_name failed verification"
            echo "$candidate" | jq '. + {"status": "failed", "date": "'$DATE'"}' >> ../failed-attempts/failed-$DATE.jsonl
        fi
        cd "$PROJECT_DIR"
    fi
done

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

PROVEN_COUNT=$(wc -l < completed-proofs/proven-$DATE.jsonl 2>/dev/null || echo "0")
FAILED_COUNT=$(wc -l < failed-attempts/failed-$DATE.jsonl 2>/dev/null || echo "0")

log "Session Complete!"
log "Theorems proven: $PROVEN_COUNT"
log "Attempts failed: $FAILED_COUNT"
log "Report: daily-reports/report-$DATE.md"

success "🌅 Nightly loop complete. Review the report in the morning!"
