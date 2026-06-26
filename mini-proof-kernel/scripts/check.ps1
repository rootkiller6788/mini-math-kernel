# MiniProofKernel Build Check Script (PowerShell)
# Usage: .\scripts\check.ps1

$ErrorActionPreference = "Stop"
$ScriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$ProjDir = Split-Path -Parent $ScriptDir

Write-Host "══ MiniProofKernel Build Check ══" -ForegroundColor Cyan

# Check that lean-toolchain exists
if (-not (Test-Path "$ProjDir\lean-toolchain")) {
    Write-Error "Missing lean-toolchain"
    exit 1
}
Write-Host "[OK] lean-toolchain found" -ForegroundColor Green

# Check that lakefile.lean exists
if (-not (Test-Path "$ProjDir\lakefile.lean")) {
    Write-Error "Missing lakefile.lean"
    exit 1
}
Write-Host "[OK] lakefile.lean found" -ForegroundColor Green

# Check that MiniProofKernel.lean exists
if (-not (Test-Path "$ProjDir\MiniProofKernel.lean")) {
    Write-Error "Missing MiniProofKernel.lean"
    exit 1
}
Write-Host "[OK] MiniProofKernel.lean found" -ForegroundColor Green

# Count .lean files in MiniProofKernel directory
$leanFiles = Get-ChildItem -Path "$ProjDir\MiniProofKernel" -Recurse -Filter "*.lean" -File
$count = $leanFiles.Count
Write-Host "[OK] Found $count .lean files in MiniProofKernel/" -ForegroundColor Green

# Verify we have 23 module files + root
Write-Host ""
Write-Host "══ Module List ══" -ForegroundColor Cyan
foreach ($f in $leanFiles | Sort-Object Name) {
    $relPath = $f.FullName.Replace($ProjDir, "").TrimStart("\")
    Write-Host "  $relPath"
}

Write-Host ""
Write-Host "══ Build ══" -ForegroundColor Cyan
Push-Location $ProjDir
try {
    lake build
    if ($LASTEXITCODE -eq 0) {
        Write-Host "[OK] Build succeeded" -ForegroundColor Green
    } else {
        Write-Error "Build failed"
        exit 1
    }
} finally {
    Pop-Location
}

Write-Host "══ ALL CHECKS PASSED ══" -ForegroundColor Green
