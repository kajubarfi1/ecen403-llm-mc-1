<#
run_flow.ps1 -- one command to run the whole LLM-MC flow on this machine.

    .\run_flow.ps1 --preset balanced --dry-run
    .\run_flow.ps1 --preset balanced
    .\run_flow.ps1 "DDR3-1600 x8, two byte lanes, balanced"
    .\run_flow.ps1 --resume runs\20261105-...     # continue a halted run
    .\run_flow.ps1 --preset balanced --skip-backend

Why this exists: flow.py uses `sys.executable` for every subsystem, so one
interpreter has to satisfy Frontend (langgraph, anthropic), Backend
(langgraph, langchain-core, jsonschema) and Validation (paramiko). It also
reads credentials from each subsystem's own env file. This script points at
a venv that has all of it and loads the env files, so there is nothing to
remember per session.

Credentials are NOT duplicated. The Anthropic key is read from the backend's
existing .env where it already lives; this script never copies or prints it.
Olympus credentials come from Validation\setup.env, which you fill in.

Override any path by setting the variable before running, e.g.
    $env:LLMMC_VENV = "C:\some\other\venv\Scripts\python.exe"
#>

$ErrorActionPreference = "Stop"

$Venv = $env:LLMMC_VENV
if (-not $Venv) { $Venv = "C:\Users\dawca\llmmc_flow_venv\Scripts\python.exe" }

$BackendEnv = $env:LLMMC_BACKEND_ENV
if (-not $BackendEnv) { $BackendEnv = "C:\Users\dawca\OneDrive\Desktop\ddr3_backend\agents\.env" }

$Repo = $PSScriptRoot
$ValEnv = Join-Path $Repo "Validation\setup.env"

if (-not (Test-Path $Venv)) {
    Write-Host "FATAL: flow venv not found at $Venv" -ForegroundColor Red
    Write-Host "  Create it with:" -ForegroundColor Yellow
    Write-Host '    py -3 -m venv C:\Users\dawca\llmmc_flow_venv'
    Write-Host '    C:\Users\dawca\llmmc_flow_venv\Scripts\python.exe -m pip install "langgraph==1.0.10" "langchain-core==1.2.17" "jsonschema==4.26.0" paramiko anthropic'
    exit 2
}

# Load an env file into this process. Existing values win, matching the
# precedence flow.py and the backend pipeline both use (os.environ.setdefault).
function Import-EnvFile($path, $label) {
    if (-not (Test-Path $path)) {
        Write-Host "  (no $label at $path)" -ForegroundColor DarkGray
        return
    }
    $n = 0
    foreach ($line in Get-Content $path) {
        $t = $line.Trim()
        if ($t -eq "" -or $t.StartsWith("#") -or (-not $t.Contains("="))) { continue }
        $i = $t.IndexOf("=")
        $k = $t.Substring(0, $i).Trim()
        $v = $t.Substring($i + 1).Trim().Trim('"').Trim("'")
        if ($v -eq "") { continue }
        if (-not [Environment]::GetEnvironmentVariable($k)) {
            [Environment]::SetEnvironmentVariable($k, $v)
            $n++
        }
    }
    Write-Host "  loaded $n setting(s) from $label" -ForegroundColor DarkGray
}

Write-Host "LLM-MC flow" -ForegroundColor Cyan
Import-EnvFile $BackendEnv "backend .env"
Import-EnvFile $ValEnv "Validation\setup.env"

# The backend refuses to run unless this is exactly 1 (it drives ORFS in Docker).
if (-not $env:USE_DOCKER) { $env:USE_DOCKER = "1" }

# Report readiness without printing any secret value.
function Show-Ready($name, $hint) {
    $v = [Environment]::GetEnvironmentVariable($name)
    if ($v) { Write-Host "  $name OK" -ForegroundColor Green }
    else    { Write-Host "  $name MISSING -- $hint" -ForegroundColor Yellow }
}
Show-Ready "ANTHROPIC_API_KEY" "Frontend spec synthesis and all repair agents need it"
Show-Ready "OLYMPUS_USER"      "your TAMU NetID; set it in Validation\setup.env"
Show-Ready "OLYMPUS_KEY"       "path to a passphrase-less private key; see Validation\setup.env"
Show-Ready "ORFS_DIR"          "OpenROAD-flow-scripts checkout, from the backend .env"

$key = [Environment]::GetEnvironmentVariable("OLYMPUS_KEY")
if ($key -and -not (Test-Path $key)) {
    Write-Host "  WARNING: OLYMPUS_KEY points at a file that does not exist: $key" -ForegroundColor Yellow
}

Write-Host ""
& $Venv (Join-Path $Repo "flow.py") @args
exit $LASTEXITCODE
