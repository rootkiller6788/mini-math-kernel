#!/bin/bash
# Smoke check script for mini-construction-kernel
echo "mini-construction-kernel check..."
lake build 2>&1 && echo "BUILD OK" || echo "BUILD FAILED"
