#!/bin/bash
# Smoke check script for mini-object-kernel
echo "mini-object-kernel check..."
lake build 2>&1 && echo "BUILD OK" || echo "BUILD FAILED"
