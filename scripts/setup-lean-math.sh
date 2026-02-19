#!/bin/bash
# setup-lean-math.sh
# One-time setup for Lean 4 + LLM Mathematics Automation

set -e

echo "🎯 Setting up Lean 4 + LLM Mathematics Automation..."

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m'

PROJECT_DIR="/Users/Jesse/clawd/lean-math-ai"
cd "$PROJECT_DIR"

# Check if elan (Lean version manager) is installed
if ! command -v elan &> /dev/null; then
    echo -e "${YELLOW}Installing elan (Lean version manager)...${NC}"
    curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
    export PATH="$HOME/.elan/bin:$PATH"
else
    echo -e "${GREEN}✓ elan already installed${NC}"
fi

# Install latest Lean 4
echo -e "${YELLOW}Installing Lean 4...${NC}"
elan toolchain install leanprover/lean4:v4.16.0
elan default leanprover/lean4:v4.16.0

# Install lake (Lean package manager)
if ! command -v lake &> /dev/null; then
    echo -e "${YELLOW}Setting up lake...${NC}"
    export PATH="$HOME/.elan/bin:$PATH"
fi

# Create new Lean project with mathlib4
echo -e "${YELLOW}Creating Lean project with mathlib4...${NC}"
if [ ! -d "MathAI" ]; then
    lake +leanprover/lean4:v4.16.0 new MathAI math
    cd MathAI
    
    # Update to latest mathlib4
    echo -e "${YELLOW}Updating mathlib4 (this may take 10-20 minutes)...${NC}"
    lake update
    lake exe cache get
    
    echo -e "${GREEN}✓ MathAI project created with mathlib4${NC}"
else
    echo -e "${GREEN}✓ MathAI project already exists${NC}"
    cd MathAI
fi

# Install Python dependencies for LLM integration
echo -e "${YELLOW}Installing Python dependencies...${NC}"
pip3 install --user -q openai anthropic requests aiohttp

# Check for MLX (local LLM)
if ! python3 -c "import mlx_lm" 2>/dev/null; then
    echo -e "${YELLOW}Installing MLX for local LLMs...${NC}"
    pip3 install --user -q mlx-lm
fi

echo -e "${GREEN}✓ Python dependencies installed${NC}"

# Create directory structure
mkdir -p ../{target-theorems,completed-proofs,failed-attempts,daily-reports}

echo ""
echo -e "${GREEN}🎉 Setup complete!${NC}"
echo ""
echo "Next steps:"
echo "  1. cd $PROJECT_DIR"
echo "  2. ./scripts/nightly-math-loop.sh"
echo ""
