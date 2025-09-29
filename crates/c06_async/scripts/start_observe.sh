#!/usr/bin/env bash
set -euo pipefail

gateway=false
hybrid=false

while [[ $# -gt 0 ]]; do
  case "$1" in
    --gateway) gateway=true; shift ;;
    --hybrid) hybrid=true; shift ;;
    *) shift ;;
  esac
done

if $hybrid; then
  (cargo run --example actor_csp_hybrid_advanced &) 
fi
if $gateway; then
  (cargo run --example async_api_gateway_2025 &) 
fi

docker compose -f ../deployment/docker-compose.observability.yml up -d
sleep 2
echo "Prometheus: http://localhost:9090"
echo "Grafana:    http://localhost:3000 (admin/admin)"

