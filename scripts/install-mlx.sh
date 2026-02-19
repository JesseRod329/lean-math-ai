#!/bin/bash
# install-mlx.sh - Install MLX for local LLM inference

echo "🚀 Installing MLX and downloading theorem-proving model..."

# Install mlx-lm
pip3 install --user mlx-lm

# Download a better model for theorem proving
MODEL_DIR="$HOME/.cache/mlx_models"
mkdir -p "$MODEL_DIR"

echo "📥 Downloading DeepSeek-Coder-V2-Lite (16B, optimized for code)..."
# This will be cached on first use via mlx-lm

echo "✅ MLX installed!"
echo ""
echo "Next steps:"
echo "1. Run: ./scripts/nightly-math-loop.sh"
echo "2. Or use --model flag with specific model:"
echo "   python3 scripts/llm-formalize.py --model mlx-community/DeepSeek-Coder-V2-Lite-Instruct-4bit ..."
