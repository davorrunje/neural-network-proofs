#Requires -Version 5.1
<#
.SYNOPSIS
  Full dev-environment bootstrap for the NeuralNetworkProofs repo on native Windows.
  On Linux/macOS/WSL/Codespaces use scripts/setup-dev.sh instead.
.PARAMETER Pdf     Also install a LaTeX distribution (MiKTeX).
.PARAMETER NoBuild Skip 'lake build'.
.PARAMETER NoCache Skip 'lake exe cache get'.
#>
[CmdletBinding()]
param([switch]$Pdf, [switch]$NoBuild, [switch]$NoCache)
$ErrorActionPreference = 'Stop'

$LeanblueprintVersion = '0.0.20'
$PlastexUrl    = 'git+https://github.com/plastex/plastex.git'
$PlastexCommit = '4fe23e25565a4788f07077076211d21630a81cb0'
$PlastexSpec   = "plastex @ $PlastexUrl@$PlastexCommit"

$RepoRoot = Split-Path -Parent $PSScriptRoot
Set-Location $RepoRoot

function Log($m) { Write-Host "==> $m" -ForegroundColor Blue }

function Ensure-Winget($id) {
  $present = winget list --id $id -e 2>$null | Select-String -SimpleMatch $id
  if (-not $present) {
    Log "Installing $id"
    winget install --id $id -e --accept-source-agreements --accept-package-agreements
  } else { Log "$id already installed" }
}

Log 'Installing system dependencies (Git, Graphviz) via winget'
Ensure-Winget 'Git.Git'
Ensure-Winget 'Graphviz.Graphviz'

if (-not (Get-Command uv -ErrorAction SilentlyContinue)) {
  Log 'Installing uv'
  Invoke-RestMethod https://astral.sh/uv/install.ps1 | Invoke-Expression
}
$env:Path = [Environment]::GetEnvironmentVariable('Path','User') + ';' +
            [Environment]::GetEnvironmentVariable('Path','Machine')

if (-not (Get-Command elan -ErrorAction SilentlyContinue)) {
  Log 'Installing elan (Lean). If this fails, see https://leanprover-community.github.io/'
  # elan provides a Windows init script; fall back to scoop if unavailable.
  $init = Join-Path $env:TEMP 'elan-init.ps1'
  Invoke-RestMethod https://elan.lean-lang.org/elan-init.ps1 -OutFile $init
  powershell -ExecutionPolicy Bypass -File $init -y --default-toolchain none
}
$env:Path = [Environment]::GetEnvironmentVariable('Path','User') + ';' +
            [Environment]::GetEnvironmentVariable('Path','Machine')

Log 'Installing the blueprint toolchain into a repo-local venv (.venv)'
if (-not (Test-Path "$RepoRoot\.venv")) { uv venv "$RepoRoot\.venv" }
$py = "$RepoRoot\.venv\Scripts\python.exe"
uv pip install --python $py "leanblueprint==$LeanblueprintVersion"
uv pip install --python $py --reinstall-package plastex $PlastexSpec

if ($Pdf) { Log 'Installing LaTeX (MiKTeX)'; Ensure-Winget 'MiKTeX.MiKTeX' }
if (-not $NoCache) { Log 'Fetching Mathlib cache'; lake exe cache get }
if (-not $NoBuild) { Log 'Building project'; lake build }

Log "Done. Add '$RepoRoot\.venv\Scripts' to PATH, then preview with:"
Log '  leanblueprint web ; leanblueprint serve'
