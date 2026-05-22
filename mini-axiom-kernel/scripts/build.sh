#!/usr/bin/env bash
# Build the mini-axiom-kernel package
set -euo pipefail

echo "Building mini-axiom-kernel..."
cd "$(dirname "$0")/.."

lake build

echo "Build complete."
