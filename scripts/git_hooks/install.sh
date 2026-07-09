#!/usr/bin/env bash
# Install the pre-commit hook for this repository.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
HOOK_SRC="$ROOT/scripts/git_hooks/pre-commit"
HOOK_DST="$ROOT/.git/hooks/pre-commit"

cp "$HOOK_SRC" "$HOOK_DST"
chmod +x "$HOOK_DST"

echo "Installed pre-commit hook to $HOOK_DST"
