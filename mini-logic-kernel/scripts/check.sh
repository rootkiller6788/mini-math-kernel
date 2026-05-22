#!/bin/bash
# Smoke check script for mini-logic-kernel
echo "mini-logic-kernel check..."
lake build 2>&1 && echo "BUILD OK" || echo "BUILD FAILED"
