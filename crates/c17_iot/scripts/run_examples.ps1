param(
  [string]$Example = "",
  [switch]$Compose
)

Set-Location -Path (Split-Path $MyInvocation.MyCommand.Path -Parent) | Out-Null
Set-Location ..

if ($Compose) {
  Push-Location examples\_compose
  docker compose up -d
  Pop-Location
}

if ($Example -ne "") {
  cargo run --example $Example
  exit $LASTEXITCODE
}

Write-Output "Running sample examples..."
cargo run --example ota_simulate
cargo run --example ditto_shadow
cargo run --example edge_ingest
cargo run --example prom_stdout

Write-Output "Done."


