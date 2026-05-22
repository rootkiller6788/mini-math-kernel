#!/usr/bin/env bash
# Lint the mini-axiom-kernel package
set -euo pipefail

echo "Linting mini-axiom-kernel..."
cd "$(dirname "$0")/.."

lake build --no-build

echo "Lint complete."
