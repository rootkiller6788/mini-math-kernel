# Smoke check script for mini-logic-kernel
Write-Output "mini-logic-kernel check..."
lake build 2>&1
if ($LASTEXITCODE -eq 0) { Write-Output "BUILD OK" } else { Write-Output "BUILD FAILED" }
