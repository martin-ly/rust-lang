#!/usr/bin/env python3
"""
归档迁移脚本：修复 docs/archive/c_class_audit_2026_06_08/ 内文件因归档导致的相对链接损坏。
策略：按文件原始位置（去掉 archive/c_class_audit_2026_06_08/ 后）解析相对链接，
若目标存在，则重写到从当前归档位置到该目标的相对路径。
"""
import os
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
ARCHIVE_DIR = ROOT / "docs" / "archive" / "c_class_audit_2026_06_08"
LINK_RE = re.compile(r"\[([^\]]+)\]\(([^)]+)\)")


def relative_to(source: Path, target: Path) -> str:
    return Path(os.path.relpath(target, source.parent)).as_posix()


def fix_file(md: Path) -> int:
    text = md.read_text(encoding="utf-8")
    new_text = text
    changed = 0

    # 计算该文件的原始位置
    try:
        rel_to_archive = md.relative_to(ARCHIVE_DIR)
    except ValueError:
        return 0
    original_source = ROOT / "docs" / rel_to_archive

    for match in LINK_RE.finditer(text):
        link_text, url = match.group(1), match.group(2)
        # 跳过外部、纯锚点、绝对路径、已存在目标
        if re.match(r"^[a-z]+://", url) or url.startswith("mailto:"):
            continue
        if url.startswith("#"):
            continue
        if url.startswith("/"):
            continue

        # 当前解析目标
        current_target = (md.parent / url).resolve()
        if current_target.exists():
            continue

        # 按原始位置解析
        orig_target = (original_source.parent / url).resolve()
        if not orig_target.exists():
            continue

        new_url = relative_to(md, orig_target)
        # 保留锚点
        if "#" in url:
            new_url += "#" + url.split("#", 1)[1]

        old = match.group(0)
        new = f"[{link_text}]({new_url})"
        if old in new_text:
            new_text = new_text.replace(old, new, 1)
            changed += 1
        else:
            # 处理重复或已被替换
            pass

    if new_text != text:
        md.write_text(new_text, encoding="utf-8")
    return changed


def main():
    total = 0
    for md in sorted(ARCHIVE_DIR.rglob("*.md")):
        total += fix_file(md)
    print(f"修复归档链接: {total} 处")


if __name__ == "__main__":
    main()
