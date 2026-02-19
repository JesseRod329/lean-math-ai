#!/bin/bash
# hourly-math-loop.sh
# Run math automation every hour with duplicate prevention

set -e

PROJECT_DIR="/Users/Jesse/clawd/lean-math-ai"
LOG_DIR="$PROJECT_DIR/logs"
DATE=$(date +%Y-%m-%d)
HOUR=$(date +%H:%M)
TIMESTAMP=$(date +%Y%m%d_%H%M%S)

cd "$PROJECT_DIR"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

log() {
    echo -e "${BLUE}[$(date '+%H:%M:%S')]${NC} $1" | tee -a "$LOG_DIR/hourly-$DATE.log"
}

error() {
    echo -e "${RED}[ERROR]${NC} $1" | tee -a "$LOG_DIR/hourly-$DATE.log"
}

success() {
    echo -e "${GREEN}[SUCCESS]${NC} $1" | tee -a "$LOG_DIR/hourly-$DATE.log"
}

warning() {
    echo -e "${YELLOW}[WARNING]${NC} $1" | tee -a "$LOG_DIR/hourly-$DATE.log"
}

log "🌙 Starting Hourly Mathematics Automation Loop"
log "Date: $DATE, Hour: $HOUR"
log "Project: $PROJECT_DIR"
echo ""

# Create timestamped directories for this run
RUN_DIR="proofs/$DATE/$TIMESTAMP"
mkdir -p "$RUN_DIR"

# Phase 1: Paper Ingest (only if not already downloaded today)
log "═══════════════════════════════════════════════════"
log "PHASE 1: Paper Ingest (if needed)"
log "══════════════════════════════════════════════════="

if [ -f "papers/papers-$DATE.json" ]; then
    warning "Papers already downloaded today, skipping fetch"
    PAPER_COUNT=$(jq '. | length' papers/papers-$DATE.json 2>/dev/null || echo "0")
    log "Using existing $PAPER_COUNT papers"
else
    python3 scripts/fetch-arxiv-papers.py --category math.NT --category math.CO --days 1 --output papers/papers-$DATE.json
    PAPER_COUNT=$(jq '. | length' papers/papers-$DATE.json 2>/dev/null || echo "0")
    log "Downloaded $PAPER_COUNT new papers"
fi

# Phase 2: Candidate Identification (only if not already done)
log ""
log "═══════════════════════════════════════════════════"
log "PHASE 2: Candidate Identification"
log "═══════════════════════════════════════════════════"

if [ -f "target-theorems/candidates-$DATE.json" ]; then
    warning "Candidates already extracted today, checking for unprocessed..."
else
    python3 scripts/extract-theorems.py --input papers/papers-$DATE.json --output target-theorems/candidates-$DATE.json --max-candidates 10
fi

CANDIDATES_FILE="target-theorems/candidates-$DATE.json"
candidates=$(jq '.candidates | length' $CANDIDATES_FILE 2>/dev/null || echo "0")
log "Total candidates available: $candidates"

# Phase 3: Formalization Attempts (process 1-2 candidates per hour)
log ""
log "═══════════════════════════════════════════════════"
log "PHASE 3: Hourly Formalization (1-2 candidates)"
log "═══════════════════════════════════════════════════"

# Find candidates not yet processed
processed_count=0
max_per_hour=2

jq -c '.candidates[]' $CANDIDATES_FILE 2>/dev/null | while read -r candidate; do
    theorem_id=$(echo "$candidate" | jq -r '.id')
    theorem_name=$(echo "$candidate" | jq -r '.name')
    
    # Check if already processed today
    if find proofs/$DATE -name "${theorem_id}.lean" -type f 2>/dev/null | grep -q .; then
        continue
    fi
    
    if [ "$processed_count" -ge "$max_per_hour" ]; then
        log "Reached hourly limit ($max_per_hour), stopping..."
        break
    fi
    
    log "Processing: $theorem_name ($theorem_id)"
    
    # Generate Lean formalization with improved v2 script
    python3 scripts/llm-formalize-v2.py \
        --candidate "$candidate" \
        --output "$RUN_DIR/${theorem_id}.lean" \
        --model mlx-community/DeepSeek-Coder-V2-Lite-Instruct-4bit \
        --attempts 2
    
    if [ -f "$RUN_DIR/${theorem_id}.lean" ]; then
        # Verify with Lean
        log "Verifying $theorem_id with Lean..."
        
        source "$HOME/.elan/env"
        cd MathAI
        
        # Copy proof to MathAI for verification
        cp "$RUN_DIR/${theorem_id}.lean" "MathAI/${theorem_id}.lean"
        
        if lake build 2>&1 | grep -q "Build completed"; then
            success "✓ $theorem_name formalized and verified"
            echo "$candidate" | jq '. + {"status": "proven", "date": "'$DATE'", "hour": "'$HOUR'"}' >> ../completed-proofs/proven-$DATE.jsonl
            ((processed_count++))
        else
            error "✗ $theorem_name failed verification"
            echo "$candidate" | jq '. + {"status": "failed", "date": "'$DATE'", "hour": "'$HOUR'"}' >> ../failed-attempts/failed-$DATE.jsonl
        fi
        
        cd "$PROJECT_DIR"
    fi
done

# Phase 4: Update Dashboard
log ""
log "═══════════════════════════════════════════════════"
log "PHASE 4: Update Dashboard"
log "═══════════════════════════════════════════════════"

# Generate simple hourly report
REPORT_FILE="daily-reports/hourly-$TIMESTAMP.md"
cat > "$REPORT_FILE" << EOF
# Hourly Report — $DATE $HOUR

## Summary
- **Papers**: $PAPER_COUNT available
- **Candidates**: $candidates total
- **Processed this hour**: $processed_count
- **Run directory**: \`$RUN_DIR\`

## Files Generated
\`\`\`
$(ls -1 $RUN_DIR/)
\`\`\`

## Next Run
Next hourly batch in 60 minutes.
EOF

success "✓ Hourly report: $REPORT_FILE"

# Update dashboard data (optional - create a JSON for the dashboard)
DASHBOARD_DATA="dashboard/data/latest.json"
mkdir -p "dashboard/data"
cat > "$DASHBOARD_DATA" << EOF
{
  "last_update": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "date": "$DATE",
  "hour": "$HOUR",
  "papers": $PAPER_COUNT,
  "candidates": $candidates,
  "processed_this_hour": $processed_count,
  "total_proven_today": $(wc -l < completed-proofs/proven-$DATE.jsonl 2>/dev/null || echo "0"),
  "status": "running"
}
EOF

log ""
success "🎉 Hourly automation complete!"
log "Next run: $(date -v+1H '+%H:%M')"
log "Dashboard: http://localhost:8765"

# Auto-commit to git (optional - uncomment to enable)
# if [ -d .git ]; then
#     git add proofs/ daily-reports/ completed-proofs/ dashboard/data/
#     git diff --cached --quiet || git commit -m "auto: $(date '+%H:%M') - $processed_count proofs"
#     git push origin main 2>/dev/null || true
# fi
