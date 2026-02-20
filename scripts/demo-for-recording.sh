#!/bin/bash
# demo-for-recording.sh — Simulated pipeline run for README GIF recording
# This shows realistic output at a pace good for a GIF

set -e

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
CYAN='\033[0;36m'
BOLD='\033[1m'
DIM='\033[2m'
NC='\033[0m'

# Typing effect
type_text() {
    echo -ne "${DIM}\$ ${NC}"
    for (( i=0; i<${#1}; i++ )); do
        echo -n "${1:$i:1}"
        sleep 0.03
    done
    echo ""
    sleep 0.3
}

slow_echo() {
    echo -e "$1"
    sleep "${2:-0.15}"
}

clear
sleep 0.5

# Show command being typed
type_text "./scripts/nightly-math-loop.sh"

sleep 0.3
echo ""
slow_echo "${BOLD}${CYAN}╔══════════════════════════════════════════════════╗${NC}" 0.1
slow_echo "${BOLD}${CYAN}║        Lean Math AI — Nightly Pipeline           ║${NC}" 0.1
slow_echo "${BOLD}${CYAN}╚══════════════════════════════════════════════════╝${NC}" 0.3
echo ""

# Phase 1: Paper Ingest
slow_echo "${BLUE}[00:01]${NC} ═══ PHASE 1: Paper Ingest ═══" 0.3
slow_echo "${BLUE}[00:01]${NC} Fetching from arXiv (math.NT, math.CO)..." 0.8
slow_echo "${BLUE}[00:03]${NC} Downloaded ${GREEN}47 papers${NC} from 2026-02-20" 0.2
slow_echo "${DIM}         • 23 number theory, 24 combinatorics${NC}" 0.4
echo ""

# Phase 2: Theorem Extraction
slow_echo "${BLUE}[00:04]${NC} ═══ PHASE 2: Theorem Extraction ═══" 0.3
slow_echo "${BLUE}[00:04]${NC} Analyzing abstracts with LLM..." 0.5

papers=(
    "Disjoint Correspondence Colorings for K₅-Minor-free Graphs"
    "On the Distribution of Primes in Short Intervals"
    "Ramsey Numbers for Graph Minors and Tree-Width"
    "Arithmetic Progressions in Dense Subsets of Integers"
    "Chromatic Symmetric Functions of Unit Interval Graphs"
)

theorems=(
    "For every K₅-minor-free graph G, there exist 3 pairwise disjoint M-colorings"
    "For x sufficiently large, π(x+y) - π(x) ≥ cy/log(x) for y ≥ x^0.55"
    "r(Kₜ-minor-free, s) ≤ c·t·√(log t)·s for fixed t"
    "Every subset A ⊆ [N] with |A| ≥ N/log(log N) contains a 3-term AP"
    "The chromatic symmetric function distinguishes unit interval graphs"
)

for i in 0 1 2 3 4; do
    slow_echo "${BLUE}[00:0$((4+i))]${NC}   📄 ${papers[$i]}" 0.15
    slow_echo "${DIM}           → ${theorems[$i]}${NC}" 0.3
done

slow_echo "${GREEN}[00:09]${NC} Extracted ${GREEN}8 candidates${NC} from 47 papers" 0.4
echo ""

# Phase 3: Formalization
slow_echo "${BLUE}[00:10]${NC} ═══ PHASE 3: Lean 4 Formalization ═══" 0.3
slow_echo "${BLUE}[00:10]${NC} Loading mathlib index (15,640 theorems)..." 0.5
slow_echo "${BLUE}[00:11]${NC} Searching relevant mathlib theorems via RAG..." 0.3

# Show formalization attempts
slow_echo "" 0.1
slow_echo "${BLUE}[00:12]${NC} Formalizing: ${BOLD}K₅-minor-free colorings${NC}" 0.2
slow_echo "${DIM}         Trying Claude 3.5 (attempt 1/3)...${NC}" 0.8
slow_echo "${GREEN}         ✓ Generated real theorem with Claude 3.5${NC}" 0.3

slow_echo "${BLUE}[00:15]${NC} Formalizing: ${BOLD}Primes in short intervals${NC}" 0.2
slow_echo "${DIM}         Trying Claude 3.5 (attempt 1/3)...${NC}" 0.8
slow_echo "${GREEN}         ✓ Generated real theorem with Claude 3.5${NC}" 0.3

slow_echo "${BLUE}[00:18]${NC} Formalizing: ${BOLD}Ramsey numbers for minors${NC}" 0.2
slow_echo "${DIM}         Trying Claude 3.5 (attempt 1/3)...${NC}" 0.6
slow_echo "${YELLOW}         ~ True placeholder, trying again...${NC}" 0.3
slow_echo "${DIM}         Trying Claude 3.5 (attempt 2/3)...${NC}" 0.6
slow_echo "${GREEN}         ✓ Generated real theorem with Claude 3.5${NC}" 0.3

slow_echo "${BLUE}[00:22]${NC} Formalizing: ${BOLD}Arithmetic progressions${NC}" 0.2
slow_echo "${DIM}         Trying Claude 3.5 (attempt 1/3)...${NC}" 0.8
slow_echo "${GREEN}         ✓ Generated real theorem with Claude 3.5${NC}" 0.3
echo ""

# Phase 4: Verification
slow_echo "${BLUE}[00:25]${NC} ═══ PHASE 4: Lean 4 Verification ═══" 0.3
slow_echo "${BLUE}[00:25]${NC} Running ${CYAN}lake env lean${NC} on each proof..." 0.5

results=(
    "FORMALIZED"
    "FORMALIZED"
    "FAILED"
    "FORMALIZED"
)
colors=("$YELLOW" "$YELLOW" "$RED" "$YELLOW")
icons=("🔶" "🔶" "❌" "🔶")
names=("K5_minor_free_colorings" "primes_short_intervals" "ramsey_minors" "arithmetic_progressions")
msgs=("compiles with sorry" "compiles with sorry" "does not compile" "compiles with sorry")

for i in 0 1 2 3; do
    slow_echo "${BLUE}[00:$((26+i*2))]${NC}   ${icons[$i]} ${colors[$i]}${results[$i]}${NC}: ${names[$i]}" 0.15
    slow_echo "${DIM}           ${msgs[$i]}${NC}" 0.3
done
echo ""

# Phase 3.5: Refinement
slow_echo "${BLUE}[00:34]${NC} ═══ PHASE 3.5: Refinement Pass ═══" 0.3
slow_echo "${BLUE}[00:34]${NC} Attempting to fix failed proofs..." 0.4
slow_echo "${DIM}         ramsey_minors.lean: 2 errors found${NC}" 0.3
slow_echo "${DIM}         → unknown identifier 'SimpleGraph.minorFree'${NC}" 0.2
slow_echo "${DIM}         → searching mathlib for alternative...${NC}" 0.5
slow_echo "${GREEN}         ✓ Refined: FAILED → FORMALIZED${NC}" 0.4
echo ""

# Final Report
slow_echo "${BLUE}[00:38]${NC} ═══ PHASE 5: Report ═══" 0.3
echo ""
slow_echo "${BOLD}┌──────────────────────────────────────────────────┐${NC}" 0.1
slow_echo "${BOLD}│           Daily Report — 2026-02-20              │${NC}" 0.1
slow_echo "${BOLD}├──────────────────────────────────────────────────┤${NC}" 0.1
slow_echo "${BOLD}│${NC}  Papers analyzed:         ${CYAN}47${NC}                     ${BOLD}│${NC}" 0.1
slow_echo "${BOLD}│${NC}  Candidates extracted:    ${CYAN}8${NC}                      ${BOLD}│${NC}" 0.1
slow_echo "${BOLD}│${NC}  Proven (no sorry):       ${GREEN}0${NC}                      ${BOLD}│${NC}" 0.1
slow_echo "${BOLD}│${NC}  Formalized (with sorry): ${YELLOW}4${NC}                      ${BOLD}│${NC}" 0.1
slow_echo "${BOLD}│${NC}  Failed:                  ${RED}0${NC}  ${DIM}(1 refined)${NC}         ${BOLD}│${NC}" 0.1
slow_echo "${BOLD}│${NC}  Real success rate:       ${GREEN}50%${NC} (4/8)              ${BOLD}│${NC}" 0.1
slow_echo "${BOLD}├──────────────────────────────────────────────────┤${NC}" 0.1
slow_echo "${BOLD}│${NC}  ${DIM}Trivial rejected: 0  Templates: 0${NC}              ${BOLD}│${NC}" 0.1
slow_echo "${BOLD}└──────────────────────────────────────────────────┘${NC}" 0.3
echo ""
slow_echo "${GREEN}[00:38]${NC} ${GREEN}✓${NC} Report: daily-reports/report-2026-02-20.md" 0.2
slow_echo "${GREEN}[00:38]${NC} ${GREEN}✓${NC} Dashboard: http://localhost:8765" 0.2
slow_echo "${GREEN}[00:38]${NC} ${GREEN}✓${NC} Committed and pushed to GitHub" 0.3
echo ""
slow_echo "${BOLD}${GREEN}🎉 Nightly automation complete!${NC}" 0.2
slow_echo "${DIM}   Next run in 60 minutes.${NC}" 0.5
echo ""

sleep 1.5
