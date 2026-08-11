#!/usr/bin/env python3
"""Monitor Rust stable/beta/nightly releases and emit a trigger signal.

This tool is used by the P1-1 Patch Release Response workflow.  It checks
whether a requested Rust release channel/version is available on GitHub and/or
in the official RELEASES.md file.

Examples::

    # Check whether Rust 1.98.0 stable has been released
    python tools/rust_release_monitor.py --channel stable --version 1.98.0

    # Same, but only use the GitHub API (fastest)
    python tools/rust_release_monitor.py --channel stable --version 1.98.0 --source github

    # Check the latest stable release (ignores --version)
    python tools/rust_release_monitor.py --channel stable --latest

    # Cron-friendly: exit 0 if released, exit 1 otherwise
    python tools/rust_release_monitor.py --channel stable --version 1.98.0 --check

The script writes a marker file when a new release is detected so that other
automation (e.g. cron jobs or CI) can avoid duplicate work.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import sys
import urllib.error
import urllib.request
from datetime import datetime, timezone
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
MARKER_DIR = REPO_ROOT / "tmp" / "rust_release_markers"
RELEASES_MD_URL = "https://raw.githubusercontent.com/rust-lang/rust/master/RELEASES.md"
GITHUB_API_LATEST = "https://api.github.com/repos/rust-lang/rust/releases/latest"
GITHUB_API_TAGS = "https://api.github.com/repos/rust-lang/rust/tags?per_page=100"


def _http_get(url: str, timeout: int = 30) -> bytes:
    req = urllib.request.Request(
        url,
        headers={
            "User-Agent": "rust-lang-kb-release-monitor/1.0",
            "Accept": "application/vnd.github+json",
        },
    )
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        return resp.read()


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Monitor Rust releases and emit trigger signals."
    )
    parser.add_argument(
        "--channel",
        choices=["stable", "beta", "nightly"],
        default="stable",
        help="Release channel to monitor (default: stable).",
    )
    parser.add_argument(
        "--version",
        type=str,
        default=None,
        help="Exact version to check, e.g. 1.98.0. Ignored when --latest is set.",
    )
    parser.add_argument(
        "--latest",
        action="store_true",
        help="Report the latest release for the channel instead of a specific version.",
    )
    parser.add_argument(
        "--source",
        choices=["github", "releases-md", "auto"],
        default="auto",
        help=(
            "Where to look for release information. "
            "'auto' tries GitHub first and falls back to RELEASES.md."
        ),
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help=(
            "Cron-friendly mode: exit 0 if the requested release is available, "
            "exit 1 otherwise."
        ),
    )
    parser.add_argument(
        "--write-marker",
        action="store_true",
        help="Write a marker file in tmp/rust_release_markers/ when a release is detected.",
    )
    parser.add_argument(
        "--marker-dir",
        type=Path,
        default=MARKER_DIR,
        help="Directory used for release marker files.",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Output the result as JSON.",
    )
    return parser.parse_args()


def _latest_from_github(channel: str) -> dict[str, str] | None:
    """Return the latest release metadata from the GitHub API."""
    try:
        data = json.loads(_http_get(GITHUB_API_LATEST))
    except (urllib.error.URLError, json.JSONDecodeError):
        return None

    tag = data.get("tag_name", "")
    # GitHub latest is the most recent release; stable tags look like 1.98.0.
    version_match = re.search(r"(\d+\.\d+\.\d+)", tag)
    if not version_match:
        return None
    return {
        "channel": channel,
        "version": version_match.group(1),
        "tag": tag,
        "published_at": data.get("published_at", ""),
        "html_url": data.get("html_url", ""),
        "source": "github-api",
    }


def _version_from_github_tags(version: str) -> dict[str, str] | None:
    """Check whether a specific version tag exists on GitHub."""
    try:
        data = json.loads(_http_get(GITHUB_API_TAGS))
    except (urllib.error.URLError, json.JSONDecodeError):
        return None

    expected = f"{version}"
    for tag_info in data:
        tag = tag_info.get("name", "")
        if tag == expected or tag.lstrip("v") == expected:
            return {
                "channel": "stable",
                "version": version,
                "tag": tag,
                "source": "github-tags",
            }
    return None


def _version_from_releases_md(version: str) -> dict[str, str] | None:
    """Check whether RELEASES.md contains a section for the requested version."""
    try:
        text = _http_get(RELEASES_MD_URL).decode("utf-8", errors="replace")
    except urllib.error.URLError:
        return None

    # RELEASES.md uses headers like "Version 1.98.0 (2026-08-20)\n=============="
    pattern = re.compile(
        rf"^Version\s+{re.escape(version)}\s*\([^)]*\)\s*$",
        re.MULTILINE,
    )
    if pattern.search(text):
        return {
            "channel": "stable",
            "version": version,
            "source": "releases-md",
        }
    return None


def _check_release(
    channel: str,
    version: str | None,
    source: str,
    latest: bool,
) -> dict[str, str] | None:
    if latest:
        if source in ("auto", "github"):
            result = _latest_from_github(channel)
            if result:
                return result
        if source in ("auto", "releases-md"):
            # Fallback: parse the first Version header from RELEASES.md.
            try:
                text = _http_get(RELEASES_MD_URL).decode("utf-8", errors="replace")
            except urllib.error.URLError:
                return None
            match = re.search(r"^Version\s+(\d+\.\d+\.\d+)\s*\([^)]*\)", text, re.MULTILINE)
            if match:
                return {
                    "channel": channel,
                    "version": match.group(1),
                    "source": "releases-md",
                }
        return None

    # Specific version check
    if version is None:
        raise ValueError("--version is required unless --latest is set")

    if source in ("auto", "github"):
        result = _version_from_github_tags(version)
        if result:
            return result
    if source in ("auto", "releases-md"):
        result = _version_from_releases_md(version)
        if result:
            return result
    return None


def _write_marker(marker_dir: Path, channel: str, version: str) -> Path:
    marker_dir.mkdir(parents=True, exist_ok=True)
    marker = marker_dir / f"{channel}_{version}.released"
    now = datetime.now(timezone.utc).isoformat()
    marker.write_text(now, encoding="utf-8")
    return marker


def _already_marked(marker_dir: Path, channel: str, version: str) -> bool:
    return (marker_dir / f"{channel}_{version}.released").exists()


def main() -> int:
    args = _parse_args()

    try:
        result = _check_release(args.channel, args.version, args.source, args.latest)
    except Exception as exc:  # noqa: BLE001
        result = None
        error_msg = str(exc)
    else:
        error_msg = None

    output: dict[str, Any] = {
        "checked_at": datetime.now(timezone.utc).isoformat(),
        "channel": args.channel,
        "version": args.version,
        "latest": args.latest,
        "released": result is not None,
    }
    if result:
        output["release"] = result
    if error_msg:
        output["error"] = error_msg

    if args.json:
        print(json.dumps(output, indent=2))
    else:
        status = "released" if result else "not released"
        print(f"Rust {args.channel} {args.version or '(latest)'}: {status}")
        if result:
            for key, value in result.items():
                print(f"  {key}: {value}")
        if error_msg:
            print(f"  error: {error_msg}")

    if args.write_marker and result and args.version:
        marker = _write_marker(args.marker_dir, args.channel, args.version)
        if not args.json:
            print(f"  marker: {marker}")

    if args.check:
        return 0 if result else 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
