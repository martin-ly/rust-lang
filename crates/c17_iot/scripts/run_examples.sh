#!/usr/bin/env bash
set -euo pipefail

EXAMPLE="${1:-}"
COMPOSE="${COMPOSE:-}" # set to 1 to start compose

cd "$(dirname "$0")"/..

if [[ "${COMPOSE}" == "1" ]]; then
  (cd examples/_compose && docker compose up -d)
fi

if [[ -n "${EXAMPLE}" ]]; then
  cargo run --example "${EXAMPLE}"
  exit $?
fi

echo "Running sample examples..."
cargo run --example ota_simulate
cargo run --example ditto_shadow
cargo run --example edge_ingest
cargo run --example prom_stdout
echo "Done."


