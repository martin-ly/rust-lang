param(
  [switch]$VerboseMode
)

# Usage:
# - Run repo-wide checks:   scripts/ci/grade.ps1
# - Run c01 assignments:    scripts/ci/assignments/c01_ownership.ps1
# - Run c02 assignments:    scripts/ci/assignments/c02_type_system.ps1

Write-Host "Running grading pipeline..."

# format
cargo fmt --all -- --check | Out-Null
if ($LASTEXITCODE -ne 0) { Write-Error "fmt failed"; exit 1 }

# clippy
cargo clippy --all-targets --workspace -- -D warnings | Out-Null
if ($LASTEXITCODE -ne 0) { Write-Error "clippy failed"; exit 1 }

# tests (nextest if available)
if (Get-Command cargo-nextest -ErrorAction SilentlyContinue) {
  cargo nextest run --workspace --all-features --failure-output=immediate
} else {
  cargo test --workspace --all-features -- --nocapture
}
if ($LASTEXITCODE -ne 0) { Write-Error "tests failed"; exit 1 }

Write-Host "Grading pipeline completed successfully."

