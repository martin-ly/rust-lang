param(
  [string]$ServiceCmd = "cargo run -p c13_microservice --example simple_observability_demo",
  [int]$WarmupSeconds = 5,
  [int]$DurationSeconds = 20
)

Write-Host "Starting observability stack..."
& "$PSScriptRoot/start-stack.ps1"

$env:OTEL_EXPORTER_OTLP_ENDPOINT = "http://localhost:4317"
$env:OTEL_TRACES_SAMPLER = "parentbased_always_on"
$env:OTEL_SERVICE_NAME = "e2e-demo"

Write-Host "Starting service: $ServiceCmd"
$service = Start-Process powershell -ArgumentList "-NoProfile","-Command",$ServiceCmd -PassThru

Start-Sleep -Seconds $WarmupSeconds

Write-Host "Generating traffic..."
try {
  for ($i=0; $i -lt $DurationSeconds; $i++) {
    try { Invoke-WebRequest -UseBasicParsing http://localhost:3000/health | Out-Null } catch {}
    Start-Sleep -Milliseconds 500
  }
} finally {
  Write-Host "Stopping service..."
  if ($service -and -not $service.HasExited) { $service.Kill() }
}

Write-Host "E2E verification completed. Check Grafana http://localhost:3000 and Prometheus http://localhost:9090"

