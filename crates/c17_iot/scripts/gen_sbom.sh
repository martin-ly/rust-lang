#!/usr/bin/env bash
set -euo pipefail

# 需要安装 cyclonedx-cargo：cargo install cyclonedx-cargo
cargo cyclonedx -o sbom.json
echo "SBOM generated at sbom.json"


