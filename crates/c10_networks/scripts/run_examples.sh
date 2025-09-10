#!/usr/bin/env bash
set -euo pipefail

DOMAIN="${1:-example.com}"
echo "Running DNS examples for domain: ${DOMAIN}"

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
pushd "${SCRIPT_DIR}/.." >/dev/null

: "${C10_SKIP_NETWORK_TESTS:=}"

cargo run --example dns_lookup -- "${DOMAIN}"
cargo run --example dns_doh_dot -- "${DOMAIN}"
cargo run --example dns_custom_ns -- internal.service.local || true
cargo run --example dns_records -- "${DOMAIN}"
cargo run --example dns_ptr
cargo run --example dns_negative_cache -- nonexistent.example.invalid || true

if [[ "${C10_SKIP_NETWORK_TESTS}" == "1" ]]; then
  cargo test
else
  echo "Tip: export C10_SKIP_NETWORK_TESTS=1 to skip network tests in CI."
fi

popd >/dev/null


