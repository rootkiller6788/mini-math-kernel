#!/usr/bin/env bash
# MiniProofKernel Build Check Script (Bash)
# Usage: ./scripts/check.sh

set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJ_DIR="$(dirname "$SCRIPT_DIR")"

echo "══ MiniProofKernel Build Check ══"

# Check that lean-toolchain exists
if [ ! -f "$PROJ_DIR/lean-toolchain" ]; then
    echo "[FAIL] Missing lean-toolchain"
    exit 1
fi
echo "[OK] lean-toolchain found"

# Check that lakefile.lean exists
if [ ! -f "$PROJ_DIR/lakefile.lean" ]; then
    echo "[FAIL] Missing lakefile.lean"
    exit 1
fi
echo "[OK] lakefile.lean found"

# Check that MiniProofKernel.lean exists
if [ ! -f "$PROJ_DIR/MiniProofKernel.lean" ]; then
    echo "[FAIL] Missing MiniProofKernel.lean"
    exit 1
fi
echo "[OK] MiniProofKernel.lean found"

# Count .lean files in MiniProofKernel directory
LEAN_COUNT=$(find "$PROJ_DIR/MiniProofKernel" -name "*.lean" -type f | wc -l)
echo "[OK] Found $LEAN_COUNT .lean files in MiniProofKernel/"

# List modules
echo ""
echo "══ Module List ══"
find "$PROJ_DIR/MiniProofKernel" -name "*.lean" -type f | sort | while read -r f; do
    rel="${f#$PROJ_DIR/}"
    echo "  $rel"
done

echo ""
echo "══ Build ══"
cd "$PROJ_DIR"
if lake build; then
    echo "[OK] Build succeeded"
else
    echo "[FAIL] Build failed"
    exit 1
fi

echo "══ ALL CHECKS PASSED ══"
