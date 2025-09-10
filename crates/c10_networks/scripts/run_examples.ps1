Param(
    [string]$Domain = "example.com",
    [switch]$SkipNetTests
)

Write-Host "Running DNS examples for domain: $Domain"

Push-Location (Split-Path $MyInvocation.MyCommand.Path -Parent)\..

if ($SkipNetTests) {
    $env:C10_SKIP_NETWORK_TESTS = "1"
}

cargo run --example dns_lookup -- $Domain
cargo run --example dns_doh_dot -- $Domain
cargo run --example dns_custom_ns -- internal.service.local
cargo run --example dns_records -- $Domain
cargo run --example dns_ptr
cargo run --example dns_negative_cache -- nonexistent.example.invalid

if ($SkipNetTests) {
    cargo test
} else {
    Write-Host "Tip: set -SkipNetTests to skip network tests in CI."
}

Pop-Location


