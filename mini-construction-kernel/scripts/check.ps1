# Smoke check script for mini-construction-kernel
Write-Output "mini-construction-kernel check..."
lake build 2>&1
if ($LASTEXITCODE -eq 0) { Write-Output "BUILD OK" } else { Write-Output "BUILD FAILED" }
