#!/usr/bin/env python3
"""修复 docs/ 中剩余的可纠正文件不存在链接。"""
from pathlib import Path

REPLACEMENTS = [
    # (file, old_url, new_url)
    (
        "docs/research_notes/10_cargo_book_alignment.md",
        "](Cargo.toml",
        "](../../Cargo.toml",
    ),
    (
        "docs/research_notes/10_knowledge_graph_index.md",
        "](../10_safe_unsafe_comprehensive_analysis.md",
        "](./10_safe_unsafe_comprehensive_analysis.md",
    ),
    (
        "docs/research_notes/10_rustc_dev_guide_alignment.md",
        "](../software_design_theory/07_crate_architectures/README.md",
        "](../software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md",
    ),
    (
        "docs/research_notes/10_rust_193_language_features_comprehensive_analysis.md",
        "](../../archive/2026_05_historical_docs/10_rust_1.89_to_1.93_cumulative_features_overview.md",
        "](../../archive/docs/2026_05_historical_docs/10_rust_1.89_to_1.93_cumulative_features_overview.md",
    ),
    (
        "docs/research_notes/10_rust_194_195_feature_matrix.md",
        "](06_toolchain/",
        "](../../06_toolchain/",
    ),
    (
        "docs/research_notes/formal_methods/README.md",
        "](../../rust-ownership-decidability/actor-specialty/ACTOR_MODEL_DEEP_DIVE.md",
        "](../../../archive/rust-ownership-decidability/actor-specialty/ACTOR_MODEL_DEEP_DIVE.md",
    ),
    (
        "docs/research_notes/type_theory/10_type_system_foundations.md",
        "](../../rust-ownership-decidability/formal-foundations",
        "](../../../archive/rust-ownership-decidability/formal-foundations/README.md",
    ),
    (
        "docs/research_notes/type_theory/README.md",
        "](../../formal_methods/00_completeness_gaps.md",
        "](../formal_methods/00_completeness_gaps.md",
    ),
]

# Remove .rustfmt.toml link in 10_toolchain_ecosystem_alignment.md
RUSTFMT_FILE = Path("docs/research_notes/10_toolchain_ecosystem_alignment.md")

def remove_rustfmt_link(path: Path):
    content = path.read_text(encoding="utf-8")
    lines = content.splitlines()
    new_lines = [line for line in lines if ".rustfmt.toml" not in line]
    if len(new_lines) < len(lines):
        path.write_text("\n".join(new_lines), encoding="utf-8")
        print(f"移除 .rustfmt.toml 链接: {path}")


def main():
    for rel_path, old, new in REPLACEMENTS:
        path = Path(rel_path)
        if not path.exists():
            print(f"不存在: {path}")
            continue
        content = path.read_text(encoding="utf-8")
        if old not in content:
            print(f"未找到 {old} in {path}")
            continue
        content = content.replace(old, new)
        path.write_text(content, encoding="utf-8")
        print(f"已修复: {path} ({old} -> {new})")

    if RUSTFMT_FILE.exists():
        remove_rustfmt_link(RUSTFMT_FILE)


if __name__ == "__main__":
    main()
