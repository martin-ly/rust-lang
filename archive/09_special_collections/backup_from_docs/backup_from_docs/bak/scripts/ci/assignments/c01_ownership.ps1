Write-Host "[c01] Running ownership/borrow/scope assignments..."
Set-Location "$PSScriptRoot/../../../"
cargo test -p c01_ownership_borrow_scope -- --nocapture
if ($LASTEXITCODE -ne 0) { Write-Error "c01 assignments failed"; exit 1 }
Write-Host "[c01] OK"

