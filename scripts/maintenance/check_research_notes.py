#!/usr/bin/env python3
"""
Check docs/12_research_notes structural and metadata consistency.

Runs the following checks:
1. No empty directories under docs/12_research_notes (unless explicitly allowed).
2. Every .md file contains at least one authority source marker.
3. Top metadata block uses Rust 1.96.0+ (Edition 2024) where present.
4. README/INDEX/organization files are up-to-date with actual structure.
5-12. Informational checks: archive links, broken internal links, metadata coverage,
      counterexample coverage, authority URL coverage, RFC counterexample mapping,
      i18n terminology reference coverage, code example anchor coverage.

Usage:
    python scripts/maintenance/check_research_notes.py
"""

import os
import re
import sys
from pathlib import Path

try:
    import yaml
except ImportError:  # pragma: no cover
    yaml = None  # type: ignore[assignment]

PROJECT_ROOT = Path(__file__).resolve().parents[2]
RESEARCH_NOTES = PROJECT_ROOT / "docs" / "research_notes"

# Directories that are allowed to be empty (none by default).
ALLOWED_EMPTY_DIRS: set[str] = set()


def find_empty_dirs() -> list[Path]:
    empty: list[Path] = []
    for root, dirs, files in os.walk(RESEARCH_NOTES):
        # A directory is empty if it has no files and no subdirectories.
        if not dirs and not files:
            rel = Path(root).relative_to(PROJECT_ROOT)
            if str(rel) not in ALLOWED_EMPTY_DIRS:
                empty.append(rel)
    return empty


def iter_md_files() -> list[Path]:
    return sorted(RESEARCH_NOTES.rglob("*.md"))


def check_authority_source(path: Path) -> bool:
    """Return True if the file contains at least one authority source marker."""
    content = path.read_text(encoding="utf-8")
    # Match lines like:
    # > **来源:** [Name](URL)
    # > **权威来源**: [Name](URL)
    # > **权威来源**: [Name](URL) | [Name2](URL2)
    return bool(re.search(r">\s*\*\*(来源|权威来源)\*\*[:：]", content))


def check_rust_version(path: Path) -> tuple[bool, str | None]:
    """Check whether the top metadata block mentions Rust 1.96+ if present."""
    content = path.read_text(encoding="utf-8")
    match = re.search(r">\s*\*\*Rust 版本\*\*[:：]\s*(.+)", content)
    if not match:
        return True, None  # no version metadata; not an error
    version = match.group(1).strip()
    # Allow 1.96.0+ / 1.96.0 / 1.97+ etc.
    ok = bool(re.search(r"1\.9[6-9]", version)) or bool(re.search(r"1\.[1-9][0-9]", version))
    # Allow files explicitly marked as historical version analysis
    if not ok and ("历史声明" in version or "历史版本" in version):
        ok = True
    return ok, version


def check_index_consistency() -> list[str]:
    """Check that INDEX.md links point to existing files for migrated sections."""
    issues: list[str] = []
    index_path = RESEARCH_NOTES / "INDEX.md"
    index_content = index_path.read_text(encoding="utf-8")

    # Look for relative markdown links inside docs/research_notes.
    links = re.findall(r"\]\((docs/12_research_notes/[^)]+\.md)\)", index_content)
    for link in links:
        target = PROJECT_ROOT / link
        if not target.exists():
            issues.append(f"INDEX.md links to missing file: {link}")

    return issues


def check_archive_links() -> tuple[list[str], list[str], list[str]]:
    """
    Scan all .md files for links pointing to archive/research_notes_2026_06_25/.
    Returns (replaceable, archive_only, missing_both) where:
    - replaceable: target exists in current docs/12_research_notes/
    - archive_only: target only exists in archive
    - missing_both: target exists in neither
    """
    archive_root = PROJECT_ROOT / "archive" / "research_notes_2026_06_25"
    current_files = {p.resolve() for p in RESEARCH_NOTES.rglob("*.md")}
    archive_files = {p.resolve() for p in archive_root.rglob("*.md")} if archive_root.exists() else set()

    replaceable: list[str] = []
    archive_only: list[str] = []
    missing_both: list[str] = []

    archive_prefix = "archive/research_notes_2026_06_25/"

    for f in RESEARCH_NOTES.rglob("*.md"):
        text = f.read_text(encoding="utf-8", errors="ignore")
        rel = f.relative_to(PROJECT_ROOT).as_posix()
        for m in re.finditer(r"!?\[[^\]]*\]\(([^)]+)\)", text):
            link = m.group(1)
            if archive_prefix not in link:
                continue
            base = link.split("#")[0]
            cur_dir = f.parent
            archive_target = (cur_dir / base).resolve()
            try:
                suffix = archive_target.relative_to(archive_root).as_posix()
            except ValueError:
                continue
            current_target = (RESEARCH_NOTES / suffix).resolve()
            in_current = current_target in current_files
            in_archive = archive_target in archive_files
            if in_current:
                replaceable.append(f"{rel} -> {link}")
            elif in_archive:
                archive_only.append(f"{rel} -> {link}")
            else:
                missing_both.append(f"{rel} -> {link}")

    return replaceable, archive_only, missing_both


def check_broken_internal_links() -> list[str]:
    """Check that relative markdown links *inside* docs/12_research_notes point to existing files."""
    issues: list[str] = []
    current_files = {p.resolve() for p in RESEARCH_NOTES.rglob("*.md")}

    for f in RESEARCH_NOTES.rglob("*.md"):
        text = f.read_text(encoding="utf-8", errors="ignore")
        rel = f.relative_to(PROJECT_ROOT).as_posix()
        for m in re.finditer(r"!?\[[^\]]*\]\(([^)]+)\)", text):
            link = m.group(1)
            # Skip external, archive, anchor-only, and absolute links
            if (
                link.startswith("http")
                or link.startswith("#")
                or link.startswith("/")
                or "archive/" in link
            ):
                continue
            base = link.split("#")[0]
            if not base or not base.endswith(".md"):
                continue
            cur_dir = f.parent
            target = (cur_dir / base).resolve()
            # Only report links whose target is inside docs/12_research_notes
            try:
                target.relative_to(RESEARCH_NOTES.resolve())
            except ValueError:
                continue
            if target not in current_files:
                issues.append(f"{rel} -> {link}")

    return issues


def check_level_metadata() -> list[str]:
    """Check that every .md file has a level metadata marker (warning only)."""
    issues: list[str] = []
    for f in RESEARCH_NOTES.rglob("*.md"):
        text = f.read_text(encoding="utf-8", errors="ignore")
        rel = f.relative_to(PROJECT_ROOT).as_posix()
        if not re.search(r">\s*\*\*(层级|Bloom 层级)\*\*[:：]", text):
            issues.append(rel)
    return issues


def check_concept_family_metadata() -> list[str]:
    """Check that every .md file has a concept family metadata marker (warning only)."""
    issues: list[str] = []
    for f in RESEARCH_NOTES.rglob("*.md"):
        text = f.read_text(encoding="utf-8", errors="ignore")
        rel = f.relative_to(PROJECT_ROOT).as_posix()
        if not re.search(r">\s*\*\*概念族\*\*[:：]", text):
            issues.append(rel)
    return issues


def check_counterexample_coverage() -> list[str]:
    """
    Check that core concept families have counterexample coverage (warning only).
    Looks for either a dedicated counterexample file or a '反例' section.
    """
    core_families = [
        "所有权 / 借用",
        "类型系统 / Trait",
        "并发安全 / Send/Sync",
        "异步 / Pin",
        "模块",
        "unsafe",
    ]
    issues: list[str] = []
    # Simple heuristic: look for counterexample keywords in filenames/sections
    counterexample_files = {p for p in RESEARCH_NOTES.rglob("*.md") if "counter" in p.name.lower() or "反例" in p.name}
    for family in core_families:
        # Heuristic check: family name appears in any counterexample file content
        found = False
        for cf in counterexample_files:
            content = cf.read_text(encoding="utf-8", errors="ignore")
            if family.split(" / ")[0] in content or family.split(" / ")[-1] in content:
                found = True
                break
        if not found:
            issues.append(family)
    return issues


def check_rfc_counterexample_mapping() -> list[Path]:
    """
    Scan counterexample files under docs/12_research_notes/ for RFC authority URLs.
    Returns a list of files that do not reference any RFC URL (informational).
    """
    rfc_patterns = [
        r"rust-lang\.github\.io/rfcs/",
        r"github\.com/rust-lang/rfcs",
    ]
    regex = re.compile("|".join(rfc_patterns))
    issues: list[Path] = []

    for f in RESEARCH_NOTES.rglob("*.md"):
        name = f.name.lower()
        if "counterexample" not in name and "反例" not in name:
            continue
        content = f.read_text(encoding="utf-8", errors="ignore")
        if not regex.search(content):
            issues.append(f.relative_to(PROJECT_ROOT))

    return issues


def check_i18n_terminology() -> list[Path]:
    """
    Check that i18n-related research notes reference the terminology library.
    Returns a list of i18n-related files that do not mention i18n_terminology.yaml.
    This is informational only and should not affect the exit code.
    """
    terminology_file = PROJECT_ROOT / "data" / "i18n_terminology.yaml"
    if yaml is None or not terminology_file.exists():
        return []

    # Basic validation: ensure the file is parseable YAML with a terms list.
    try:
        data = yaml.safe_load(terminology_file.read_text(encoding="utf-8"))
        if not isinstance(data, dict) or not isinstance(data.get("terms"), list):
            return []
    except yaml.YAMLError:
        return []

    missing_reference: list[Path] = []
    for f in RESEARCH_NOTES.rglob("*.md"):
        content = f.read_text(encoding="utf-8", errors="ignore")
        concept_family_match = re.search(r">\s*\*\*概念族\*\*[:：]\s*(.+)", content)
        if not concept_family_match:
            continue
        concept_family = concept_family_match.group(1)
        if "i18n" not in concept_family and "国际化" not in concept_family:
            continue
        rel = f.relative_to(PROJECT_ROOT)
        if "i18n_terminology.yaml" not in content:
            missing_reference.append(rel)

    return missing_reference


def check_authority_url_coverage() -> list[Path]:
    """
    Check that .md files reference at least one international authoritative URL (informational).
    """
    authority_patterns = [
        r"doc\.rust-lang\.org",
        r"rust-lang\.github\.io",
        r"github\.com/rust-lang",
        r"github\.com/diesel-rs",
        r"github\.com/launchbadge",
        r"github\.com/SeaQL",
        r"github\.com/rusqlite",
        r"github\.com/redis-rs",
        r"github\.com/mongodb",
        r"github\.com/kube-rs",
        r"github\.com/nats-io",
        r"github\.com/ferrous-systems",
        r"github\.com/probe-rs",
        r"github\.com/hyperium",
        r"github\.com/tower-rs",
        r"github\.com/actix",
        r"github\.com/SergioBenitez",
        r"github\.com/tokio-rs/axum",
        r"github\.com/tokio-rs/mini-redis",
        r"github\.com/quinn-rs",
        r"github\.com/dtolnay",
        r"github\.com/EmbarkStudios",
        r"github\.com/rustsec",
        r"github\.com/rust-lang/cargo-vet",
        r"github\.com/ulid",
        r"github\.com/model-checking",
        r"github\.com/creusot-rs",
        r"github\.com/formal-land",
        r"github\.com/sosnek",
        r"spec\.ferrocene\.dev",
        r"rustc-dev-guide\.rust-lang\.org",
        r"plv\.mpi-sws\.org",
        r"aeneas-verification\.github\.io",
        r"link\.springer\.com",
        r"plf\.inf\.ethz\.ch",
        r"nnethercote\.github\.io",
        r"rust-unofficial\.github\.io",
        r"rust-lang\.github\.io/api-guidelines",
        r"releases\.rs",
        r"this-week-in-rust\.org",
        r"blog\.rust-lang\.org",
        r"kaisery\.github\.io/trpl-zh-cn",
        r"doc\.rust-jp\.rs",
        r"rustcc\.cn",
        r"course\.rs",
        r"microservices\.io",
        r"dataintensive\.net",
        r"ryhl\.io",
        r"docs\.rs/tokio",
        r"docs\.rs",
        r"crates\.io",
        r"opentelemetry\.io",
        r"prometheus\.io",
        r"kubernetes\.io",
        r"sigstore\.dev",
        r"slsa\.dev",
        r"spdx\.dev",
        r"arxiv\.org",
        r"acm\.org",
        r"dl\.acm\.org",
        r"ieee\.org",
        r"springer\.com",
    ]
    regex = re.compile("|".join(authority_patterns))
    issues: list[Path] = []
    for f in RESEARCH_NOTES.rglob("*.md"):
        content = f.read_text(encoding="utf-8", errors="ignore")
        if not regex.search(content):
            issues.append(f.relative_to(PROJECT_ROOT))
    return issues


def check_code_example_anchors() -> list[str]:
    """
    Scan docs/12_research_notes/*.md for relative links to local .rs files.

    Checks that relative links pointing to Rust source files (e.g.
    ../examples/..., ../../crates/.../*.rs, ../crates/.../*.rs) resolve to
    existing files under the project root. Returns a list of broken or
    missing anchors in the form "<source.md> -> <link>". This check is
    informational and should not affect the exit code.
    """
    issues: list[str] = []
    link_pattern = re.compile(r"!?\[[^\]]*\]\(([^)]+)\)")

    for f in RESEARCH_NOTES.rglob("*.md"):
        text = f.read_text(encoding="utf-8", errors="ignore")
        rel = f.relative_to(PROJECT_ROOT).as_posix()
        for m in link_pattern.finditer(text):
            link = m.group(1)
            # Skip external, archive, anchor-only, and absolute links.
            if (
                link.startswith("http")
                or link.startswith("mailto:")
                or link.startswith("#")
                or link.startswith("/")
                or "archive/" in link
            ):
                continue
            base = link.split("#")[0].split("?")[0]
            if not base or not base.endswith(".rs"):
                continue
            target = (f.parent / base).resolve()
            # Only report links whose target is inside the project root.
            try:
                target.relative_to(PROJECT_ROOT.resolve())
            except ValueError:
                continue
            if not target.exists():
                issues.append(f"{rel} -> {link}")

    return sorted(set(issues))


def main() -> int:
    exit_code = 0

    print("=" * 60)
    print("docs/12_research_notes consistency check")
    print("=" * 60)

    # 1. Empty directories
    empty_dirs = find_empty_dirs()
    print(f"\n[1/12] Empty directories: {len(empty_dirs)}")
    if empty_dirs:
        exit_code = 1
        for d in empty_dirs:
            print(f"  ❌ {d}")
    else:
        print("  ✅ No empty directories")

    # 2. Authority sources
    md_files = iter_md_files()
    missing_source: list[Path] = []
    for md in md_files:
        if not check_authority_source(md):
            missing_source.append(md.relative_to(PROJECT_ROOT))

    print(f"\n[2/12] Markdown files missing authority source: {len(missing_source)}")
    if missing_source:
        exit_code = 1
        for p in missing_source:
            print(f"  ❌ {p}")
    else:
        print("  ✅ All markdown files have authority source markers")

    # 3. Rust version metadata
    wrong_version: list[tuple[Path, str]] = []
    for md in md_files:
        ok, version = check_rust_version(md)
        if not ok:
            wrong_version.append((md.relative_to(PROJECT_ROOT), version or "N/A"))

    print(f"\n[3/12] Files with outdated Rust version metadata: {len(wrong_version)}")
    if wrong_version:
        exit_code = 1
        for p, version in wrong_version:
            print(f"  ❌ {p} -> {version}")
    else:
        print("  ✅ Rust version metadata is up-to-date")

    # 4. INDEX consistency
    index_issues = check_index_consistency()
    print(f"\n[4/12] INDEX.md consistency issues: {len(index_issues)}")
    if index_issues:
        exit_code = 1
        for issue in index_issues:
            print(f"  ❌ {issue}")
    else:
        print("  ✅ INDEX.md links are consistent")

    # 5. Archive link audit (informational/warning)
    replaceable, archive_only, missing_both = check_archive_links()
    print(f"\n[5/12] Archive link audit:")
    print(f"  ℹ️  Replaceable links (target exists in current dir): {len(replaceable)}")
    print(f"  ℹ️  Archive-only links (target only in archive): {len(archive_only)}")
    print(f"  ℹ️  Missing both sides: {len(missing_both)}")
    if replaceable:
        for item in replaceable[:10]:
            print(f"    ⚠️  {item}")
        if len(replaceable) > 10:
            print(f"    ... and {len(replaceable) - 10} more")
    if missing_both:
        for item in missing_both[:10]:
            print(f"    ❌ {item}")
        if len(missing_both) > 10:
            print(f"    ... and {len(missing_both) - 10} more")

    # 6. Broken internal links (error)
    broken_links = check_broken_internal_links()
    print(f"\n[6/12] Broken internal markdown links: {len(broken_links)}")
    if broken_links:
        exit_code = 1
        for item in broken_links[:20]:
            print(f"  ❌ {item}")
        if len(broken_links) > 20:
            print(f"  ... and {len(broken_links) - 20} more")
    else:
        print("  ✅ No broken internal markdown links")

    # 7. Metadata coverage (warning)
    missing_level = check_level_metadata()
    missing_family = check_concept_family_metadata()
    print(f"\n[7/12] Metadata coverage (informational):")
    print(f"  ℹ️  Files missing level metadata: {len(missing_level)}")
    if missing_level:
        for item in missing_level[:10]:
            print(f"    ⚠️  {item}")
        if len(missing_level) > 10:
            print(f"    ... and {len(missing_level) - 10} more")
    print(f"  ℹ️  Files missing concept family metadata: {len(missing_family)}")
    if missing_family:
        for item in missing_family[:10]:
            print(f"    ⚠️  {item}")
        if len(missing_family) > 10:
            print(f"    ... and {len(missing_family) - 10} more")

    # 8. Counterexample coverage (warning)
    missing_counterexample = check_counterexample_coverage()
    print(f"\n[8/12] Counterexample coverage (informational):")
    if missing_counterexample:
        print(f"  ℹ️  Core families without clear counterexample coverage: {len(missing_counterexample)}")
        for item in missing_counterexample:
            print(f"    ⚠️  {item}")
    else:
        print("  ✅ Core concept families have counterexample coverage")

    # 9. Authority URL coverage (informational)
    missing_auth_url = check_authority_url_coverage()
    print(f"\n[9/12] Authority URL coverage (informational):")
    print(f"  ℹ️  Files without international authority URL: {len(missing_auth_url)}")
    if missing_auth_url:
        for item in missing_auth_url[:10]:
            print(f"    ⚠️  {item}")
        if len(missing_auth_url) > 10:
            print(f"    ... and {len(missing_auth_url) - 10} more")
    else:
        print("  ✅ All files reference at least one authority URL")

    # 10. RFC counterexample mapping (informational)
    missing_rfc_link = check_rfc_counterexample_mapping()
    print(f"\n[10/12] RFC counterexample mapping (informational):")
    print(f"  ℹ️  Counterexample files without RFC URL: {len(missing_rfc_link)}")
    if missing_rfc_link:
        for item in missing_rfc_link[:10]:
            print(f"    ⚠️  {item}")
        if len(missing_rfc_link) > 10:
            print(f"    ... and {len(missing_rfc_link) - 10} more")
    else:
        print("  ✅ All counterexample files reference at least one RFC URL")

    # 11. i18n terminology reference coverage (informational)
    missing_terminology_ref = check_i18n_terminology()
    print(f"\n[11/12] i18n terminology reference coverage (informational):")
    print(f"  ℹ️  i18n files not referencing terminology library: {len(missing_terminology_ref)}")
    if missing_terminology_ref:
        for item in missing_terminology_ref[:10]:
            print(f"    ⚠️  {item}")
        if len(missing_terminology_ref) > 10:
            print(f"    ... and {len(missing_terminology_ref) - 10} more")
    else:
        print("  ✅ All i18n files reference the terminology library")

    # 12. Code example anchor coverage (informational)
    broken_code_anchors = check_code_example_anchors()
    print(f"\n[12/12] Code example anchor coverage (informational):")
    print(f"  ℹ️  Broken code example anchors: {len(broken_code_anchors)}")
    if broken_code_anchors:
        for item in broken_code_anchors[:10]:
            print(f"    ⚠️  {item}")
        if len(broken_code_anchors) > 10:
            print(f"    ... and {len(broken_code_anchors) - 10} more")
    else:
        print("  ✅ All referenced code example files exist")

    print("\n" + "=" * 60)
    if exit_code == 0:
        print("All required checks passed ✅")
    else:
        print("Some required checks failed ❌")
    print("=" * 60)
    return exit_code


if __name__ == "__main__":
    sys.exit(main())
