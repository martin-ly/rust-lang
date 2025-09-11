$ErrorActionPreference = "Stop"

# 需要安装 cyclonedx-cargo：cargo install cyclonedx-cargo
& cargo cyclonedx -o sbom.json
Write-Output "SBOM generated at sbom.json"


