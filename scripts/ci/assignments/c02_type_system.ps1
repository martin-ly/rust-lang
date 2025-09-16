Write-Host "[c02] Running type system assignments..."
Set-Location "$PSScriptRoot/../../../"
cargo test -p c02_type_system -- --nocapture
if ($LASTEXITCODE -ne 0) { Write-Error "c02 assignments failed"; exit 1 }
Write-Host "[c02] OK"

