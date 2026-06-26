#!/bin/bash
# Smoke check script for mini-theory-dependency-kernel
echo "mini-theory-dependency-kernel check..."
lake build 2>&1 && echo "BUILD OK" || echo "BUILD FAILED"
