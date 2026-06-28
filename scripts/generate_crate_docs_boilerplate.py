#!/usr/bin/env python3
"""
根据模板为 crates/*/docs/ 生成 boilerplate 文档。

本脚本默认使用 dry-run 模式，不会修改任何文件；使用 --yes 后才会实际生成缺失文件。
已存在的文件不会被覆盖。

用法:
    python scripts/generate_crate_docs_boilerplate.py          # dry-run
    python scripts/generate_crate_docs_boilerplate.py --yes    # 实际生成
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TEMPLATES_DIR = ROOT / "scripts" / "templates" / "crate_docs"
CRATES_DIR = ROOT / "crates"

# 默认生成的 boilerplate 文件列表
DEFAULT_BOILERPLATE = [
    "README.md",
    "ONE_PAGE_SUMMARY.md",
    "00_MASTER_INDEX.md",
    "FAQ.md",
    "Glossary.md",
    "PENDING_ITEMS.md",
    "MIND_MAP.md",
]


def to_human_name(crate_name: str) -> str:
    """将 crate 名称转换为可读标题。"""
    # c08_algorithms -> C08 Algorithms
    parts = crate_name.split("_")
    if parts and parts[0].startswith("c") and parts[0][1:].isdigit():
        parts[0] = parts[0][0].upper() + parts[0][1:]
    return " ".join(p.capitalize() for p in parts)


def read_cargo_toml(crate_dir: Path) -> dict[str, str]:
    """从 crate 的 Cargo.toml 读取基本信息。"""
    cargo_toml = crate_dir / "Cargo.toml"
    info = {
        "version": "0.1.0",
        "rust_version": "1.96.0",
        "description": "a Rust learning crate",
    }
    if not cargo_toml.exists():
        return info

    content = cargo_toml.read_text(encoding="utf-8")

    version_match = re.search(r'^version\s*=\s*"([^"]+)"', content, re.MULTILINE)
    if version_match:
        info["version"] = version_match.group(1)

    rust_version_match = re.search(r'^rust-version\s*=\s*"([^"]+)"', content, re.MULTILINE)
    if rust_version_match:
        info["rust_version"] = rust_version_match.group(1)

    desc_match = re.search(r'^description\s*=\s*"([^"]+)"', content, re.MULTILINE)
    if desc_match:
        info["description"] = desc_match.group(1)

    return info


def render_template(template_path: Path, crate_name: str, info: dict[str, str]) -> str:
    """渲染模板，替换占位符。"""
    content = template_path.read_text(encoding="utf-8")
    human = to_human_name(crate_name)
    content = content.replace("{{CRATE_NAME}}", crate_name)
    content = content.replace("{{CRATE_HUMAN_NAME}}", human)
    content = content.replace("{{CRATE_DESCRIPTION}}", info["description"])
    content = content.replace("{{VERSION}}", info["version"])
    content = content.replace("{{RUST_VERSION}}", info["rust_version"])
    return content


def main() -> int:
    parser = argparse.ArgumentParser(
        description="生成 crates/*/docs/ boilerplate 文档（默认 dry-run）"
    )
    parser.add_argument(
        "--yes",
        action="store_true",
        help="实际生成缺失文件；否则仅打印将要生成的文件",
    )
    parser.add_argument(
        "--crate",
        help="仅处理指定 crate",
    )
    parser.add_argument(
        "--file",
        action="append",
        choices=DEFAULT_BOILERPLATE,
        help="仅生成指定的 boilerplate 文件（可多次使用）",
    )
    args = parser.parse_args()

    targets = [args.file] if args.file else DEFAULT_BOILERPLATE
    if args.file is None:
        targets = DEFAULT_BOILERPLATE
    else:
        targets = args.file

    crates_to_process: list[Path] = []
    for crate_dir in sorted(CRATES_DIR.iterdir()):
        if not crate_dir.is_dir():
            continue
        if args.crate and crate_dir.name != args.crate:
            continue
        crates_to_process.append(crate_dir)

    if not crates_to_process:
        print("未找到需要处理的 crate")
        return 1

    generated: list[tuple[str, str]] = []
    skipped_existing: list[tuple[str, str]] = []

    for crate_dir in crates_to_process:
        crate_name = crate_dir.name
        docs_dir = crate_dir / "docs"
        info = read_cargo_toml(crate_dir)

        for filename in targets:
            template_path = TEMPLATES_DIR / filename
            if not template_path.exists():
                print(f"⚠️ 模板不存在: {template_path}", file=sys.stderr)
                continue

            dest_path = docs_dir / filename
            if dest_path.exists():
                skipped_existing.append((crate_name, filename))
                continue

            rendered = render_template(template_path, crate_name, info)
            generated.append((crate_name, filename))

            if args.yes:
                docs_dir.mkdir(parents=True, exist_ok=True)
                dest_path.write_text(rendered, encoding="utf-8")

    mode = "实际生成" if args.yes else "dry-run（将生成）"
    print(f"=== {mode} 报告 ===")
    print(f"处理 crate 数: {len(crates_to_process)}")
    print(f"计划生成文件数: {len(generated)}")
    print(f"已存在跳过数: {len(skipped_existing)}")

    if generated:
        print("\n计划生成:")
        for crate_name, filename in generated:
            print(f"  - crates/{crate_name}/docs/{filename}")

    if skipped_existing:
        print("\n已存在跳过:")
        for crate_name, filename in skipped_existing[:10]:
            print(f"  - crates/{crate_name}/docs/{filename}")
        if len(skipped_existing) > 10:
            print(f"  ... 还有 {len(skipped_existing) - 10} 个")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
