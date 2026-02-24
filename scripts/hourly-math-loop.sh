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
export PATH="$HOME/.elan/bin:$PATH"

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
    python3 scripts/extract-theorems.py \
        --input papers/papers-$DATE.json \
        --output target-theorems/candidates-$DATE.json \
        --max-candidates 10 \
        --model mlx-community/DeepSeek-Coder-V2-Lite-Instruct-4bit
fi

CANDIDATES_FILE="target-theorems/candidates-$DATE.json"
candidates=$(jq '.candidates | length' $CANDIDATES_FILE 2>/dev/null || echo "0")
log "Total candidates available: $candidates"

# Phase 3: Formalization Attempts (process 1-2 candidates per hour)
log ""
log "═══════════════════════════════════════════════════"
log "PHASE 3: Hourly Formalization (1-2 candidates)"
log "═══════════════════════════════════════════════════"

# Track counts (use process substitution to avoid subshell variable scope)
processed_count=0
max_per_hour=2

while read -r candidate; do
    theorem_id=$(echo "$candidate" | jq -r '.id')
    theorem_name=$(echo "$candidate" | jq -r '.name')

    # Check if already processed today (search all subdirs)
    if find proofs/$DATE -name "${theorem_id}.lean" -type f 2>/dev/null | grep -q .; then
        continue
    fi

    if [ "$processed_count" -ge "$max_per_hour" ]; then
        log "Reached hourly limit ($max_per_hour), stopping..."
        break
    fi

    log "Processing: $theorem_name ($theorem_id)"

    # Generate Lean formalization with v2 script
    python3 scripts/llm-formalize-v2.py \
        --candidate "$candidate" \
        --output "$RUN_DIR/${theorem_id}.lean" \
        --model mlx-community/DeepSeek-Coder-V2-Lite-Instruct-4bit \
        --attempts 2

    if [ -f "$RUN_DIR/${theorem_id}.lean" ]; then
        # Verify with Lean (individual file check)
        log "Verifying $theorem_id with Lean..."

        VERIFY_EXIT=0
        VERIFY_OUTPUT=$(bash scripts/verify-proof.sh "$RUN_DIR/${theorem_id}.lean" 2>&1) || VERIFY_EXIT=$?

        case $VERIFY_EXIT in
            0)
                success "PROVEN: $theorem_name"
                echo "$candidate" | jq '. + {"status": "proven", "date": "'"$DATE"'", "hour": "'"$HOUR"'"}' >> completed-proofs/proven-$DATE.jsonl
                ;;
            1)
                success "FORMALIZED: $theorem_name (compiles with sorry)"
                echo "$candidate" | jq '. + {"status": "formalized", "date": "'"$DATE"'", "hour": "'"$HOUR"'"}' >> completed-proofs/formalized-$DATE.jsonl
                ;;
            2)
                error "FAILED: $theorem_name (does not compile)"
                echo "$candidate" | jq '. + {"status": "failed", "date": "'"$DATE"'", "hour": "'"$HOUR"'"}' >> failed-attempts/failed-$DATE.jsonl
                ;;
            4)
                warning "TEMPLATE: $theorem_name (LLM fallback)"
                echo "$candidate" | jq '. + {"status": "template", "date": "'"$DATE"'", "hour": "'"$HOUR"'"}' >> failed-attempts/templates-$DATE.jsonl
                ;;
            5)
                warning "TRIVIAL: $theorem_name (True := by)"
                echo "$candidate" | jq '. + {"status": "trivial", "date": "'"$DATE"'", "hour": "'"$HOUR"'"}' >> failed-attempts/trivial-$DATE.jsonl
                ;;
        esac

        log "  $VERIFY_OUTPUT"
        ((processed_count++)) || true
    fi
done < <(jq -c '.candidates[]' $CANDIDATES_FILE 2>/dev/null)

# Phase 3.5: Refinement Pass (retry failed/formalized proofs)
log ""
log "═══════════════════════════════════════════════════"
log "PHASE 3.5: Refinement Pass"
log "═══════════════════════════════════════════════════"

if [ -d "$RUN_DIR" ] && ls "$RUN_DIR"/*.lean 1>/dev/null 2>&1; then
    python3 scripts/refine-failed-proofs.py \
        --proofs-dir "$RUN_DIR" \
        --max-attempts 2 \
        --model mlx-community/DeepSeek-Coder-V2-Lite-Instruct-4bit 2>&1 | tee -a "$LOG_DIR/hourly-$DATE.log"
else
    log "No proof files to refine"
fi

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
$(ls -1 $RUN_DIR/ 2>/dev/null || echo "none")
\`\`\`

## Next Run
Next hourly batch in 60 minutes.
EOF

success "✓ Hourly report: $REPORT_FILE"

# Count each status for dashboard
proven_today=$(cat completed-proofs/proven-$DATE.jsonl 2>/dev/null | python3 -c "import sys,json; d=json.JSONDecoder(); c=sys.stdin.read(); i=0; n=0
while i<len(c.strip()):
 try: _,i2=d.raw_decode(c,i); n+=1; j=c.find('{',i2); i=j if j!=-1 else len(c)
 except: break
print(n)" 2>/dev/null || echo "0")
formalized_today=$(cat completed-proofs/formalized-$DATE.jsonl 2>/dev/null | python3 -c "import sys,json; d=json.JSONDecoder(); c=sys.stdin.read(); i=0; n=0
while i<len(c.strip()):
 try: _,i2=d.raw_decode(c,i); n+=1; j=c.find('{',i2); i=j if j!=-1 else len(c)
 except: break
print(n)" 2>/dev/null || echo "0")

# Update dashboard data
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
  "proven_today": $proven_today,
  "formalized_today": $formalized_today,
  "status": "running"
}
EOF

# Generate proof listing for dashboard
python3 -c "
import json, os, glob, subprocess, re

proofs = []
proof_dir = 'proofs/$DATE'
if os.path.isdir(proof_dir):
    for lean_file in sorted(glob.glob(os.path.join(proof_dir, '**', '*.lean'), recursive=True)):
        name = os.path.basename(lean_file).replace('.lean', '')
        abs_path = os.path.abspath(lean_file)

        # Determine status from content
        with open(lean_file, 'r') as f:
            content = f.read()

        if 'STATUS: TEMPLATE_FALLBACK' in content:
            status = 'template'
        elif re.search(r':\s*True\s*:=', content):
            status = 'trivial'
        elif 'sorry' in content:
            status = 'formalized'
        else:
            status = 'unknown'  # Will be updated by verification

        proofs.append({
            'id': name,
            'path': abs_path,
            'status': status,
            'vscode_url': f'vscode://file/{abs_path}'
        })

with open('dashboard/data/proofs.json', 'w') as f:
    json.dump(proofs, f, indent=2)
print(f'Generated dashboard proof listing: {len(proofs)} proofs')
" 2>&1 | tee -a "$LOG_DIR/hourly-$DATE.log"

log ""
success "🎉 Hourly automation complete!"
log "Next run: $(date -v+1H '+%H:%M')"
log "Dashboard: http://localhost:8765"

# Auto-commit to git
cd "$PROJECT_DIR"
if [ -d .git ]; then
    git add proofs/ daily-reports/ completed-proofs/ failed-attempts/ dashboard/data/ 2>/dev/null
    git diff --cached --quiet || git commit -m "auto: $(date '+%H:%M') - $processed_count processed (proven:$proven_today formalized:$formalized_today)"
    git push origin main 2>/dev/null || warning "Git push failed (no network?)"
fi
