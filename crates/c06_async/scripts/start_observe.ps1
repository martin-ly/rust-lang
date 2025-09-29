Param(
  [switch]$Gateway,
  [switch]$Hybrid
)

Write-Host "Starting examples..."

if ($Hybrid) {
  Start-Process -NoNewWindow powershell -ArgumentList "-NoProfile","-Command","cargo run --example actor_csp_hybrid_advanced" | Out-Null
}
if ($Gateway) {
  Start-Process -NoNewWindow powershell -ArgumentList "-NoProfile","-Command","cargo run --example async_api_gateway_2025" | Out-Null
}

Write-Host "Starting Prometheus + Grafana..."
docker compose -f ../deployment/docker-compose.observability.yml up -d | Out-Null

Start-Sleep -Seconds 2
Start-Process "http://localhost:9090"
Start-Process "http://localhost:3000"

Write-Host "Done."

