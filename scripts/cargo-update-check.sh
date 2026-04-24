#!/usr/bin/env bash
set -euo pipefail

# cargo-update-check.sh
# Cargo update automation check script for Linux CI
# Usage: ./scripts/cargo-update-check.sh [--dry-run]

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${PROJECT_ROOT}"

DRY_RUN=false
if [[ "${1:-}" == "--dry-run" ]]; then
    DRY_RUN=true
fi

REPORT_LINES=()
report() {
    REPORT_LINES+=("$1")
    echo "$1"
}

report "========================================"
report "Cargo Update Check Report"
report "Date: $(date '+%Y-%m-%d %H:%M:%S')"
report "Project: ${PROJECT_ROOT}"
report "Mode: $([ "$DRY_RUN" = true ] && echo 'DRY-RUN' || echo 'LIVE')"
report "========================================"
report ""

# Verify cargo
if ! command -v cargo >/dev/null 2>&1; then
    echo "ERROR: cargo not found" >&2
    exit 1
fi
report "Cargo: $(cargo --version)"

# Outdated check
report ""
report "--- Outdated Packages ---"
if command -v cargo-outdated >/dev/null 2>&1; then
    if ! cargo outdated -R 2>&1 | tee /dev/stderr | grep -q "up to date"; then
        report "See above for outdated packages."
    else
        report "All root dependencies are up to date."
    fi
else
    report "Note: cargo-outdated not installed"
fi

# Cargo update
report ""
report "--- cargo update $([ "$DRY_RUN" = true ] && echo '--dry-run') ---"
UPDATE_ARGS=()
if [ "$DRY_RUN" = true ]; then
    UPDATE_ARGS+=("--dry-run")
fi

UPDATED_PKGS=()
LOCKED_COUNT=0
while IFS= read -r line; do
    if echo "$line" | grep -qE '^\s+Updating\s+\S+\s+v?[0-9]'; then
        UPDATED_PKGS+=("$line")
    elif echo "$line" | grep -qE '^\s+Locking\s'; then
        LOCKED_COUNT=$((LOCKED_COUNT + 1))
    fi
done < <(cargo update "${UPDATE_ARGS[@]}" 2>&1 || true)

if [ ${#UPDATED_PKGS[@]} -gt 0 ]; then
    report "Packages Updated:"
    for pkg in "${UPDATED_PKGS[@]}"; do
        report "  $pkg"
    done
else
    report "No packages were updated."
fi
if [ "$LOCKED_COUNT" -gt 0 ]; then
    report "Locked/Unchanged count: ${LOCKED_COUNT}"
fi

# Audit
report ""
report "--- Security Audit ---"
if command -v cargo-audit >/dev/null 2>&1; then
    if ! cargo audit 2>&1 | tee /dev/stderr | while IFS= read -r l; do
        REPORT_LINES+=("$l")
    done; then
        report "Audit completed with warnings (see above)."
    else
        report "No security advisories found."
    fi
else
    report "Note: cargo-audit not installed"
fi

# Recommendations
report ""
report "--- Recommendations ---"
report "  libp2p  - verify hickory-resolver compatibility before upgrading to 0.56+"
report "  dioxus  - check for stable releases when upgrading from RC"
report "  sea-orm - 2.0.0 is still in RC; verify API stability before upgrading"
report "  bincode - keep pinned at 2.0.1 until 3.0 stable is released"

report ""
report "========================================"
report "Report Complete"
report "========================================"

# Save report
mkdir -p "${PROJECT_ROOT}/target"
REPORT_FILE="${PROJECT_ROOT}/target/cargo-update-report-$(date '+%Y%m%d-%H%M%S').txt"
printf "%s\n" "${REPORT_LINES[@]}" > "$REPORT_FILE"
report ""
report "Report saved to: ${REPORT_FILE}"
