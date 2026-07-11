#!/usr/bin/env python3
"""
Bulk append an '## 权威来源参考' section to counterexample Markdown files in
docs/research_notes/ that lack the required P1/P1.5/P2 authority URLs.

Idempotent: skips files that already contain a '## 权威来源参考' heading.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parents[2]
RESEARCH_NOTES = PROJECT_ROOT / "docs" / "research_notes"

SECTION_HEADING = "## 权威来源参考"

# Map relative file paths (as POSIX strings) to the required authority links.
# All links are written as Markdown list items.
AUTHORITY_LINKS: dict[str, list[str]] = {
    "formal_methods/60_ownership_counterexamples.md": [
        "- [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)",
        "- [Stacked Borrows](https://plv.mpi-sws.org/rustbos/)",
        "- [Tree Borrows](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html)",
    ],
    "type_theory/60_type_system_counterexamples.md": [
        "- [RustSEM](https://link.springer.com/article/10.1007/s10703-024-00460-3)",
        "- [Oxide](https://arxiv.org/abs/1903.00982)",
    ],
    "formal_methods/60_concurrency_async_counterexamples.md": [
        "- [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)",
        "- [Tokio Docs](https://docs.rs/tokio/)",
        "- [Async Book](https://rust-lang.github.io/async-book/)",
    ],
    "formal_methods/60_unsafe_counterexamples.md": [
        "- [Unsafe Code Guidelines](https://rust-lang.github.io/unsafe-code-guidelines/)",
        "- [Rustonomicon](https://doc.rust-lang.org/nomicon/)",
        "- [RustSEM](https://link.springer.com/article/10.1007/s10703-024-00460-3)",
    ],
    "formal_modules/60_module_counterexamples.md": [
        "- [RFC 2126: Path clarity](https://rust-lang.github.io/rfcs/2126-path-clarity.html)",
        "- [Rust Reference Modules](https://doc.rust-lang.org/reference/items/modules.html)",
    ],
    "software_design_theory/01_design_patterns_formal/60_design_patterns_counterexamples.md": [
        "- [Rust Design Patterns](https://rust-unofficial.github.io/patterns/)",
        "- [Refactoring Guru](https://refactoring.guru/design-patterns)",
    ],
    "software_design_theory/60_workflow_compositional_distributed_counterexamples.md": [
        "- [microservices.io](https://microservices.io/)",
        "- [Release It!](https://pragprog.com/titles/mnee2/release-it-second-edition/)",
    ],
    "software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md": [
        "- [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/)",
        "- [Rust Design Patterns](https://rust-unofficial.github.io/patterns/)",
    ],
    "experiments/60_experiments_counterexamples.md": [
        "- [Rust Performance Book](https://nnethercote.github.io/perf-book/)",
        "- [This Week in Rust](https://this-week-in-rust.org/)",
    ],
    "10_version_evolution_counterexamples.md": [
        "- [Rust Release Blog](https://blog.rust-lang.org/)",
        "- [This Week in Rust](https://this-week-in-rust.org/)",
    ],
}

EXCLUDED_FILES = {
    "10_rfc_to_counterexample_mapping.md",
    "10_rust_193_counterexamples_index.md",
}


def discover_counterexample_files() -> list[Path]:
    """Return all counterexample/反例 .md files, excluding the two index files."""
    files: list[Path] = []
    for f in sorted(RESEARCH_NOTES.rglob("*.md")):
        rel = f.relative_to(RESEARCH_NOTES).as_posix()
        if rel in EXCLUDED_FILES:
            continue
        if "counterexample" in f.name.lower() or "反例" in f.name:
            files.append(f)
    return files


def needs_section(content: str, required_links: list[str]) -> bool:
    """Return True if the file lacks the dedicated authority section."""
    if SECTION_HEADING in content:
        return False
    # If every required URL is already present somewhere in the file, treat as
    # already covered and do not append a redundant section.
    return not all(link.split("](", 1)[1].rstrip(")") in content for link in required_links)


def append_section(path: Path, required_links: list[str]) -> None:
    content = path.read_text(encoding="utf-8")

    # Trim trailing whitespace/newlines so we add exactly one blank line before
    # the new section.
    content = content.rstrip("\n") + "\n\n"

    content += SECTION_HEADING + "\n\n"
    content += "本反例汇编参考以下 P1/P1.5/P2 权威来源：\n\n"
    content += "\n".join(required_links) + "\n"

    path.write_text(content, encoding="utf-8")


def main() -> int:
    files = discover_counterexample_files()
    modified: list[str] = []
    skipped: list[str] = []

    for f in files:
        rel = f.relative_to(RESEARCH_NOTES).as_posix()
        required_links = AUTHORITY_LINKS.get(rel)
        if not required_links:
            print(f"⚠️  No authority link mapping for {rel}; skipping.")
            continue

        content = f.read_text(encoding="utf-8")
        if needs_section(content, required_links):
            append_section(f, required_links)
            modified.append(rel)
        else:
            skipped.append(rel)

    print("=" * 70)
    print("Counterexample authority-source append complete")
    print("=" * 70)
    print(f"\nModified ({len(modified)}):")
    for p in modified:
        print(f"  + {p}")
    print(f"\nSkipped/Already present ({len(skipped)}):")
    for p in skipped:
        print(f"  = {p}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
