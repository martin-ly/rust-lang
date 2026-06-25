#!/usr/bin/env python3
"""
最终清理：对 docs/LINK_CHECK_REPORT.md 中剩余的无法自动修复的损坏链接，
按已知重定向表改写；无明确目标的则移除 Markdown 链接语法（保留文本）。
"""
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
DOCS_BASE = ROOT / "docs"
REPORT = DOCS_BASE / "LINK_CHECK_REPORT.md"
LINK_RE = re.compile(r"\[([^\]]*)\]\(([^)]+)\)")

# 已知重定向映射：目标路径模式 -> 实际目标路径（相对项目根）
REDIRECTS = {
    "concept/04_formal/09_operational_semantics.md": "concept/04_formal/17_operational_semantics.md",
    "docs/rust-ownership-decidability/MASTER_INDEX_AUTO.md": "docs/archive/2026_03_reorganization/MASTER_INDEX_AUTO.md",
    "docs/rust-ownership-decidability/coq-formalization/README.md": "archive/deprecated/coq_skeleton/README.md",
}


def relative_to(source: Path, target: Path) -> str:
    import os
    return Path(os.path.relpath(target, source.parent)).as_posix()


def resolve_source(source_str: str) -> Path:
    raw = source_str.replace("\\", "/")
    if raw.startswith("docs/"):
        raw = raw[5:]
    return DOCS_BASE / raw


def try_redirect(source: Path, url: str) -> str | None:
    """如果 url 命中已知重定向，返回新的 url；否则 None。"""
    # 去除锚点
    if "#" in url:
        path_part, _, anchor = url.partition("#")
    else:
        path_part, anchor = url, ""

    # 解析当前目标（相对项目根）
    if path_part.startswith("/"):
        current = ROOT / path_part.lstrip("/")
    else:
        current = source.parent / path_part
    current = current.resolve()
    try:
        rel_current = current.relative_to(ROOT).as_posix()
    except ValueError:
        rel_current = ""

    for pattern, dest in REDIRECTS.items():
        if pattern in rel_current or rel_current.endswith(pattern):
            target = ROOT / dest
            if target.exists():
                new_path = relative_to(source, target)
                return f"{new_path}#{anchor}" if anchor else new_path
    return None


def fix_link(source: Path, link_text: str, url: str) -> tuple[bool, str]:
    if not source.exists():
        return False, "源文件不存在"

    text = source.read_text(encoding="utf-8")
    old = f"[{link_text}]({url})"
    if old not in text:
        return False, f"未定位链接: {old}"

    # 尝试已知重定向
    new_url = try_redirect(source, url)
    if new_url:
        new = f"[{link_text}]({new_url})"
        text = text.replace(old, new)
        source.write_text(text, encoding="utf-8")
        return True, f"重定向: {url} -> {new_url}"

    # 否则移除链接语法，保留文本
    text = text.replace(old, link_text)
    source.write_text(text, encoding="utf-8")
    return True, f"移除链接: {old} -> {link_text!r}"


def parse_report(report_path: Path):
    text = report_path.read_text(encoding="utf-8")
    issues = []

    # 文件不存在
    file_section = re.search(r"### 文件不存在 \(\d+个\)(.*?)### 锚点不存在", text, re.DOTALL)
    if file_section:
        for line in file_section.group(1).splitlines():
            m = re.match(r"\|\s*([^|]+?)\s*\|\s*([^|]+?)\s*\|\s*([^|]+?)\s*\|\s*([^|]+?)\s*\|", line)
            if not m or "源文件" in line:
                continue
            s, lt, u, p = (x.strip() for x in m.groups())
            issues.append(("file", s, lt.strip("`"), u.strip("`")))

    # 锚点不存在
    anchor_section = re.search(r"### 锚点不存在 \(\d+个\)(.*?)(?:###\s+\d+\.|$)", text, re.DOTALL)
    if anchor_section:
        for line in anchor_section.group(1).splitlines():
            m = re.match(r"\|\s*([^|]+?)\s*\|\s*([^|]+?)\s*\|\s*([^|]+?)\s*\|\s*([^|]+?)\s*\|", line)
            if not m or "源文件" in line:
                continue
            s, lt, u, p = (x.strip() for x in m.groups())
            issues.append(("anchor", s, lt.strip("`"), u.strip("`")))

    return issues


def main():
    if not REPORT.exists():
        print(f"报告不存在: {REPORT}")
        return

    issues = parse_report(REPORT)
    print(f"剩余问题: {len(issues)} 个")

    fixed = 0
    skipped = 0
    log = []

    for kind, source_str, link_text, url in issues:
        source = resolve_source(source_str)
        changed, msg = fix_link(source, link_text, url)
        if changed:
            fixed += 1
            log.append(f"[FIXED {kind}] {source.relative_to(ROOT)}: {msg}")
        else:
            skipped += 1
            log.append(f"[SKIP {kind}] {source.relative_to(ROOT)}: [{link_text}]({url}) => {msg}")

    log_path = ROOT / "reports" / "FIX_FINAL_BROKEN_LINKS_2026_06_25.log"
    log_path.write_text("\n".join(log), encoding="utf-8")
    print(f"修复完成: 成功 {fixed} 个, 跳过 {skipped} 个")
    print(f"日志: {log_path}")


if __name__ == "__main__":
    main()
