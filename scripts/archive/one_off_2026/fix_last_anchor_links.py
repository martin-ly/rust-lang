#!/usr/bin/env python3
"""移除 docs/link_check_report.md 中最后剩余的无法修复的锚点链接的 Markdown 语法。"""
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
DOCS_BASE = ROOT / "docs"
REPORT = DOCS_BASE / "LINK_CHECK_REPORT.md"


def resolve_source(source_str: str) -> Path:
    raw = source_str.replace("\\", "/")
    if raw.startswith("docs/"):
        raw = raw[5:]
    return DOCS_BASE / raw


def parse_anchors(report_path: Path):
    text = report_path.read_text(encoding="utf-8")
    issues = []
    section = re.search(r"### 锚点不存在 \(\d+个\)(.*?)(?=###\s+[^#]|$)", text, re.DOTALL)
    if not section:
        return issues
    for line in section.group(1).splitlines():
        if not line.startswith("|") or "源文件" in line:
            continue
        parts = [p.strip() for p in line.split("|")]
        # 去掉首空列（因 line 以 | 开头）
        parts = [p for p in parts if p != ""]
        if len(parts) < 4:
            continue
        source, link_text, url, *_ = parts
        # link_text 可能含 |，重新组合中间所有列
        if len(parts) > 4:
            link_text = " | ".join(parts[1:-2])
            url = parts[-2]
        issues.append((resolve_source(source), link_text.strip("`"), url.strip("`")))
    return issues


def remove_link_by_url(text: str, url: str) -> tuple[str, bool, str]:
    """通过 URL 定位并移除 Markdown 链接，返回新文本、是否修改、被移除的完整链接。"""
    suffix = f"]({url})"
    pos = text.find(suffix)
    if pos == -1:
        return text, False, ""
    # 向前查找匹配的 [
    bracket_open = text.rfind("[", 0, pos)
    if bracket_open == -1:
        return text, False, ""
    full = text[bracket_open:pos + len(suffix)]
    link_text = text[bracket_open + 1:pos]
    new_text = text[:bracket_open] + link_text.strip() + text[pos + len(suffix):]
    return new_text, True, full


def main():
    issues = parse_anchors(REPORT)
    print(f"最后剩余锚点问题: {len(issues)} 个")
    removed = 0
    for source, link_text, url in issues:
        if not source.exists():
            continue
        text = source.read_text(encoding="utf-8")
        changed_any = False
        while True:
            new_text, changed, full = remove_link_by_url(text, url)
            if not changed:
                break
            changed_any = True
            removed += 1
            text = new_text
            print(f"removed link in {source.relative_to(ROOT)}: {full}")
        if changed_any:
            source.write_text(text, encoding="utf-8")
        else:
            print(f"not found: {source.relative_to(ROOT)} [{link_text}]({url})")
    print(f"\n共移除 {removed} 个链接")


if __name__ == "__main__":
    main()
