#!/usr/bin/env python3
"""
归档生命周期脚本

将指定文件从活跃目录移动到 archive/ 归档目录，并在原位置生成重定向 stub。

用法:
    python scripts/archive_file.py <source_file> [--target-dir <archive_subdir>]

示例:
    python scripts/archive_file.py docs/research_notes/10_old_report.md
    python scripts/archive_file.py docs/research_notes/10_old_report.md --target-dir archive/research_notes
"""

import argparse
import sys
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parent.parent


def make_redirect_stub(source_rel: Path, archive_rel: Path, title: str) -> str:
    """生成重定向 stub 内容"""
    depth = len(source_rel.parent.parts)
    prefix = "../" * depth
    archive_link = f"{prefix}{archive_rel.as_posix()}"

    # 尝试找一个 concept/ 权威来源链接
    # 简单启发：如果文件标题包含 Rust 1.XX，指向对应 concept/07_future 页面
    canonical_link = ""
    import re
    version_match = re.search(r"Rust\s+1\.(\d+)", title)
    if version_match:
        minor = int(version_match.group(1))
        # 1.95/1.96 有 stabilized 页，其他用 preview
        if minor >= 95:
            canonical_rel = f"concept/07_future/rust_1_{minor}_stabilized.md"
        else:
            canonical_rel = f"concept/07_future/rust_1_{minor}_preview.md"
        if (PROJECT_ROOT / canonical_rel).exists():
            canonical_link = f"\n> 权威来源：[{canonical_rel}]({prefix}{canonical_rel})"

    return f"""# {title}

> **归档说明**: 本文档已迁移到 `{archive_rel.as_posix()}`。{canonical_link}
> 历史版本存档：[{archive_rel.as_posix()}]({archive_link})

---

**历史内容已迁移**：本文件不再维护，请点击上方链接查看历史存档或权威来源。
"""


def archive_file(source_path: Path, target_dir: Path | None = None) -> tuple[Path, Path]:
    """归档文件并生成重定向 stub"""
    if not source_path.exists():
        raise FileNotFoundError(f"源文件不存在: {source_path}")

    source_rel = source_path.relative_to(PROJECT_ROOT)

    # 确定归档目标目录
    if target_dir is None:
        # 默认：archive/<原顶层目录>/<原相对路径>
        top_dir = source_rel.parts[0]
        target_dir = PROJECT_ROOT / "archive" / top_dir

    target_dir.mkdir(parents=True, exist_ok=True)
    archive_path = target_dir / source_path.name

    # 如果目标已存在，添加序号
    counter = 1
    original_archive_path = archive_path
    while archive_path.exists():
        stem = original_archive_path.stem
        suffix = original_archive_path.suffix
        archive_path = target_dir / f"{stem}_{counter:02d}{suffix}"
        counter += 1

    # 读取标题
    try:
        content = source_path.read_text(encoding="utf-8")
        title = content.splitlines()[0].lstrip("# ").strip() if content else source_path.stem
    except Exception:
        title = source_path.stem

    # 移动文件
    archive_path.write_text(content, encoding="utf-8")
    source_path.unlink()

    # 生成重定向 stub
    archive_rel = archive_path.relative_to(PROJECT_ROOT)
    stub_content = make_redirect_stub(source_rel, archive_rel, title)
    source_path.write_text(stub_content, encoding="utf-8")

    return archive_path, source_path


def main():
    parser = argparse.ArgumentParser(description="归档文件并在原位置生成重定向 stub")
    parser.add_argument("source", help="要归档的源文件路径（相对项目根目录）")
    parser.add_argument(
        "--target-dir",
        help="归档目标子目录（相对项目根目录），默认 archive/<顶层目录>/",
        default=None,
    )
    args = parser.parse_args()

    source_path = PROJECT_ROOT / args.source
    target_dir = PROJECT_ROOT / args.target_dir if args.target_dir else None

    try:
        archive_path, stub_path = archive_file(source_path, target_dir)
        print(f"✅ 已归档: {archive_path.relative_to(PROJECT_ROOT)}")
        print(f"✅ 重定向 stub: {stub_path.relative_to(PROJECT_ROOT)}")
    except Exception as e:
        print(f"❌ 错误: {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
