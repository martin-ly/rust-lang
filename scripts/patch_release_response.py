#!/usr/bin/env python3
"""Patch Release Response Helper

Automated checklist for responding to a Rust patch release (e.g. 1.97.2)
or a critical security advisory (RUSTSEC/CVE). Verifies the repository state
against AGENTS.md §7 Patch Release Response workflow.

Usage:
    python scripts/patch_release_response.py 1.97.2
    python scripts/patch_release_response.py 1.97.2 --check-gates

Exit code:
    0 if all verifiable checks pass
    1 otherwise
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
from pathlib import Path
from typing import List, Tuple

ROOT = Path(__file__).resolve().parent.parent


def run(cmd: List[str], cwd: Path = ROOT) -> Tuple[int, str, str]:
    p = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, encoding="utf-8")
    return p.returncode, p.stdout, p.stderr


def read_file(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8")
    except Exception:
        return ""


def check_rust_version(version: str) -> List[str]:
    """Verify rust-version in root Cargo.toml, rust-toolchain.toml, .clippy.toml."""
    issues: List[str] = []
    files = {
        "Cargo.toml": ROOT / "Cargo.toml",
        "rust-toolchain.toml": ROOT / "rust-toolchain.toml",
        ".clippy.toml": ROOT / ".clippy.toml",
    }
    for name, path in files.items():
        text = read_file(path)
        if not text:
            issues.append(f"{name}: file missing")
            continue
        # Match rust-version = "1.97.0", channel = "...", or msrv = "1.97.0" (.clippy.toml)
        m = re.search(r'(?:rust-version|channel|msrv)\s*=\s*"([^"]+)"', text)
        if not m:
            issues.append(f"{name}: rust-version/channel/msrv not found")
            continue
        declared = m.group(1)
        # "stable" channel is acceptable for rust-toolchain.toml; exact version required for Cargo.toml/.clippy.toml
        if name == "rust-toolchain.toml" and declared == "stable":
            continue
        if declared != version:
            issues.append(f"{name}: declared {declared}, expected {version}")
    return issues


def check_version_tracking_page(version: str) -> List[str]:
    """Check that patch authority page exists and is non-stub."""
    issues: List[str] = []
    normalized = version.replace(".", "_")
    patch_page = ROOT / "concept" / "07_future" / "00_version_tracking" / f"rust_{normalized}.md"
    if not patch_page.exists():
        issues.append(f"missing patch authority page: {patch_page.relative_to(ROOT)}")
        return issues
    text = read_file(patch_page)
    if len(text.strip()) < 200:
        issues.append(f"patch authority page looks like a stub: {patch_page.relative_to(ROOT)}")
    return issues


def check_stabilized_page_reference(version: str) -> List[str]:
    """Check that the minor stabilized page references the patch."""
    issues: List[str] = []
    major_minor = "_".join(version.split(".")[:2])
    stabilized = ROOT / "concept" / "07_future" / "00_version_tracking" / f"rust_{major_minor}_stabilized.md"
    if not stabilized.exists():
        issues.append(f"missing stabilized page: {stabilized.relative_to(ROOT)}")
        return issues
    text = read_file(stabilized)
    if version not in text:
        issues.append(f"stabilized page does not reference patch {version}: {stabilized.relative_to(ROOT)}")
    return issues


def check_summary_reference(version: str) -> List[str]:
    """Check that concept/SUMMARY.md references the patch page."""
    issues: List[str] = []
    summary = ROOT / "concept" / "SUMMARY.md"
    text = read_file(summary)
    normalized = version.replace(".", "_")
    if f"rust_{normalized}.md" not in text and normalized not in text:
        issues.append(f"concept/SUMMARY.md does not reference rust_{normalized}.md")
    return issues


def check_msrv_consistency() -> List[str]:
    issues: List[str] = []
    rc, out, err = run([sys.executable, "scripts/check_msrv_consistency.py", "--strict"])
    if rc != 0:
        issues.append(f"check_msrv_consistency.py --strict failed (exit {rc})\n{out[:500]}{err[:500]}")
    return issues


def run_blocking_gates() -> List[str]:
    """Run a subset of fast blocking gates. Full run should use run_quality_gates.sh."""
    issues: List[str] = []
    checks = [
        ([sys.executable, "scripts/kb_auditor.py", "--link-check"], "KB auditor link check"),
        ([sys.executable, "scripts/check_metadata_consistency.py", "--strict"], "metadata consistency"),
        ([sys.executable, "scripts/concept_consistency_auditor.py", "--strict"], "concept consistency"),
        ([sys.executable, "scripts/check_concept_authority_coverage.py", "--strict", "--include-crates"], "authority coverage"),
    ]
    for cmd, name in checks:
        rc, out, err = run(cmd)
        if rc != 0:
            issues.append(f"{name} failed (exit {rc})\n{out[:300]}{err[:300]}")
    return issues


def main() -> int:
    parser = argparse.ArgumentParser(description="Patch release response helper")
    parser.add_argument("version", help="Rust patch version, e.g. 1.97.2")
    parser.add_argument("--check-gates", action="store_true", help="Also run a subset of blocking quality gates")
    args = parser.parse_args()

    print(f"[patch-release] Checking response readiness for Rust {args.version}")
    print("-" * 60)

    all_issues: List[str] = []
    steps = [
        ("rust-version declarations", check_rust_version(args.version)),
        ("patch authority page", check_version_tracking_page(args.version)),
        ("stabilized page reference", check_stabilized_page_reference(args.version)),
        ("SUMMARY.md reference", check_summary_reference(args.version)),
        ("MSRV consistency", check_msrv_consistency()),
    ]

    if args.check_gates:
        steps.append(("subset of blocking gates", run_blocking_gates()))

    for name, issues in steps:
        if issues:
            print(f"\n❌ {name}")
            for i in issues:
                print(f"   - {i}")
            all_issues.extend(issues)
        else:
            print(f"✅ {name}")

    print("-" * 60)
    if all_issues:
        print(f"[patch-release] ❌ {len(all_issues)} issue(s) found. Please remediate before declaring response complete.")
        return 1
    print("[patch-release] ✅ All verifiable checks passed.")
    print("Reminder: manually confirm official Release Notes / RUSTSEC impact range and run scripts/run_quality_gates.sh for full coverage.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
