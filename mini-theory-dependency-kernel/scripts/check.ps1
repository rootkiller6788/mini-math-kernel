# Smoke check script for mini-theory-dependency-kernel
Write-Output "mini-theory-dependency-kernel check..."
lake build 2>&1
if ($LASTEXITCODE -eq 0) { Write-Output "BUILD OK" } else { Write-Output "BUILD FAILED" }
