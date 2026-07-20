param(
  [string]$ComposeDir = "deploy/observability"
)

Push-Location $PSScriptRoot/../../
docker compose -f "$ComposeDir/docker-compose.yml" down -v
Pop-Location
Write-Host "Observability stack stopped and volumes removed."

