#!/bin/bash
# publish-to-github.sh - Publish your proofs to GitHub

echo "🚀 Publishing Lean Math AI to GitHub"
echo ""

PROJECT_DIR="/Users/Jesse/clawd/lean-math-ai"
cd "$PROJECT_DIR"

# Check if git is initialized
if [ ! -d .git ]; then
    echo "📦 Initializing git repository..."
    git init
    
    # Create .gitignore
    cat > .gitignore << 'EOF'
# Ignore build artifacts and cache
MathAI/.lake/
MathAI/build/
*.olean
.cache/

# Ignore large files
*.tar.gz
*.zip

# Ignore logs (keep structure)
logs/*.log
!logs/.gitkeep

# Ignore Python cache
__pycache__/
*.pyc
*.pyo

# But keep our important files
!proofs/
!daily-reports/
!completed-proofs/
!docs/
!scripts/
!dashboard/
EOF
    
    # Create .gitkeep for empty directories
    touch logs/.gitkeep
    
    git add .gitignore
    git commit -m "Initial commit: Add .gitignore"
fi

# Add all current files
echo "📁 Adding files to git..."
git add README.md
git add scripts/
git add dashboard/
git add docs/
git add proofs/ 2>/dev/null || true
git add daily-reports/ 2>/dev/null || true
git add completed-proofs/ 2>/dev/null || true

# Check if there are changes to commit
if git diff --cached --quiet; then
    echo "✓ No new changes to commit"
else
    git commit -m "$(date '+%Y-%m-%d %H:%M'): Update proofs and reports"
    echo "✓ Committed changes"
fi

# Check if remote exists
if ! git remote get-url origin >/dev/null 2>&1; then
    echo ""
    echo "⚠️  No GitHub remote configured"
    echo ""
    echo "To set up:"
    echo "1. Create repo at https://github.com/new"
    echo "2. Run: git remote add origin https://github.com/YOUR_USERNAME/lean-math-ai.git"
    echo "3. Run: git branch -M main"
    echo "4. Run: git push -u origin main"
else
    echo ""
    echo "📤 Pushing to GitHub..."
    git push origin main
    echo "✅ Published!"
    git remote get-url origin
fi

echo ""
echo "🎉 Setup complete!"
echo ""
echo "To auto-publish every hour, add this to scripts/hourly-math-loop.sh:"
echo "  ./scripts/publish-to-github.sh"
