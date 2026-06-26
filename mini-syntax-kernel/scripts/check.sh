#!/usr/bin/env bash
# Check script for mini-syntax-kernel (bash)
# Usage: ./scripts/check.sh

set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BASE_DIR="$(dirname "$SCRIPT_DIR")"

echo "=== mini-syntax-kernel: build check ==="

cd "$BASE_DIR"

echo "Running lake build..."
lake build
echo "Build OK."

echo ""
echo "Running smoke tests..."
lake env lean --run Test/Smoke.lean
echo "Smoke tests OK."
