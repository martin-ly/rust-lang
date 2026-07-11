#!/usr/bin/env python3
"""
修复 docs/research_notes/ 及其子目录中因相对路径深度错误导致的文件不存在链接。

策略：
- 对 docs/research_notes/*.md：所有指向项目根目录一级资源（crates/、archive/、data/、deprecated/、
  examples/、.github/、exercises/、rust-ownership-decidability/、.clippy.toml、.rustfmt.toml、Cargo.toml、
  .vscode/）的 `../xxx` 改为 `../../xxx`。
- 对 docs/research_notes/software_design_theory/07_crate_architectures/*.md：
  `../../../crates/` 改为 `../../../../crates/`。
- 对 docs/research_notes/type_theory/README.md：修正 `../../../../../../../formal_methods/` 与
  `../../10_formal_proof_system_guide.md` 的路径深度。
- 对 docs/research_notes/*.md 中指向 `coq_skeleton/` 的文件改为 `../../archive/deprecated/coq_skeleton/`。
"""
import re
from pathlib import Path

BASE = Path("docs/research_notes")

# Mapping for docs/research_notes/*.md: prefix -> replacement
DEPTH1_MAP = {
    "../crates/": "../../crates/",
    "../archive/": "../../archive/",
    "../data/": "../../data/",
    "../deprecated/": "../../archive/deprecated/",
    "../examples/": "../../examples/",
    "../.github/": "../../.github/",
    "../exercises/": "../../exercises/",
    "../rust-ownership-decidability/": "../../rust-ownership-decidability/",
    "../.clippy.toml": "../../.clippy.toml",
    "../.rustfmt.toml": "../../.rustfmt.toml",
    "../Cargo.toml": "../../Cargo.toml",
    "../.vscode/": "../../.vscode/",
    # coq_skeleton references (relative to docs/research_notes/)
    "coq_skeleton/": "../../archive/deprecated/coq_skeleton/",
}

# For docs/research_notes/software_design_theory/07_crate_architectures/*.md
CRATE_ARCH_MAP = {
    "../../../crates/": "../../../../crates/",
}


def fix_file(path: Path, mapping: dict) -> int:
    content = path.read_text(encoding="utf-8")
    original = content
    for old, new in mapping.items():
        # Only replace in markdown links to avoid accidental text changes
        content = re.sub(
            re.escape("](" + old) + r"([^)\s]*)",
            f"]({new}\\1",
            content,
        )
    if content != original:
        path.write_text(content, encoding="utf-8")
        return 1
    return 0


def main():
    fixed_files = 0

    # Depth-1 files
    for md in sorted(BASE.glob("*.md")):
        fixed_files += fix_file(md, DEPTH1_MAP)

    # Crate architecture files
    crate_arch_dir = BASE / "software_design_theory/07_crate_architectures"
    if crate_arch_dir.exists():
        for md in sorted(crate_arch_dir.glob("*.md")):
            fixed_files += fix_file(md, CRATE_ARCH_MAP)

    # Special: type_theory/README.md
    type_theory_readme = BASE / "type_theory/README.md"
    if type_theory_readme.exists():
        content = type_theory_readme.read_text(encoding="utf-8")
        original = content
        # ../../../../../../../formal_methods/ -> ../../formal_methods/ (still likely missing, but correct depth)
        content = content.replace("../../../../../../../formal_methods/", "../../formal_methods/")
        # ../../10_formal_proof_system_guide.md -> ../10_formal_proof_system_guide.md
        content = content.replace("](../../10_formal_proof_system_guide.md", "](../10_formal_proof_system_guide.md")
        if content != original:
            type_theory_readme.write_text(content, encoding="utf-8")
            fixed_files += 1

    print(f"总计修复文件: {fixed_files}")


if __name__ == "__main__":
    main()
