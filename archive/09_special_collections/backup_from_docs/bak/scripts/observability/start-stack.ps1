param(
  [string]$ComposeDir = "deploy/observability"
)

Push-Location $PSScriptRoot/../../
docker compose -f "$ComposeDir/docker-compose.yml" up -d
Pop-Location
Write-Host "Observability stack started (Grafana: http://localhost:3000, Prometheus: http://localhost:9090)"

