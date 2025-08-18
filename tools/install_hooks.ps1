Param()
$hookDir = ".git\hooks"
if (!(Test-Path $hookDir)) { New-Item -ItemType Directory -Path $hookDir | Out-Null }
$preCommit = @'
#!/usr/bin/env pwsh
Write-Host "Running pre-commit checks..."
python tools/ci_check.py
if ($LASTEXITCODE -ne 0) { Write-Error "Pre-commit checks failed."; exit 1 }
'@
Set-Content -Path "$hookDir\pre-commit" -Value $preCommit -NoNewline
Write-Host "Installed pre-commit hook." 