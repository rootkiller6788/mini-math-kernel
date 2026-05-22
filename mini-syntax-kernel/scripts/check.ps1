# Check script for mini-syntax-kernel (PowerShell)
# Usage: ./scripts/check.ps1

$ErrorActionPreference = "Stop"
$baseDir = Split-Path -Parent $PSScriptRoot

Write-Host "=== mini-syntax-kernel: build check ==="

Push-Location $baseDir
try {
    Write-Host "Running lake build..."
    lake build
    if ($LASTEXITCODE -eq 0) {
        Write-Host "Build OK."
    } else {
        Write-Host "Build FAILED with exit code $LASTEXITCODE."
        exit 1
    }

    Write-Host ""
    Write-Host "Running smoke tests..."
    lake env lean --run Test/Smoke.lean
    if ($LASTEXITCODE -eq 0) {
        Write-Host "Smoke tests OK."
    } else {
        Write-Host "Smoke tests FAILED."
        exit 1
    }
} finally {
    Pop-Location
}
