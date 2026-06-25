#!/usr/bin/env python3
"""
为 docs/LINK_CHECK_REPORT.md 中剩余的“锚点不存在”问题，在对应位置插入 HTML 锚点。
适用于链接指向的文本不是 Markdown 标题（如元数据行、列表项、加粗说明）的情况。
"""
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
DOCS_BASE = ROOT / "docs"
REPORT = DOCS_BASE / "LINK_CHECK_REPORT.md"
LINK_RE = re.compile(r"\[([^\]]+)\]\(([^)]+)\)")


def normalize_text(text: str) -> str:
    """移除 markdown 格式标记和首尾空白，用于子串匹配。"""
    t = re.sub(r"(\*\*|__|~~|`)", "", text)
    # 移除显式 {#id}
    t = re.sub(r"\s*\{#[^}]+\}\s*", "", t)
    return t.strip().lower()


def resolve_target(source: Path, url: str) -> Path | None:
    """解析带路径的锚点链接的目标文件。"""
    if "#" in url:
        path_part = url.split("#", 1)[0]
    else:
        path_part = url
    if not path_part:
        return source
    target = (source.parent / path_part).resolve()
    if target.exists():
        return target
    return None


def fix_anchor(source: Path, target: Path, anchor_id: str, link_text: str) -> tuple[bool, str]:
    if not target.exists():
        return False, "目标文件不存在"

    text = target.read_text(encoding="utf-8")
    if f'id="{anchor_id}"' in text or f"id='{anchor_id}'" in text:
        return False, "锚点已存在"

    norm_link = normalize_text(link_text)
    if not norm_link:
        return False, "链接文本为空"

    lines = text.splitlines(keepends=True)
    found_idx = -1
    for i, line in enumerate(lines):
        norm_line = normalize_text(line)
        if norm_link in norm_line:
            found_idx = i
            break

    if found_idx == -1:
        return False, f"未找到包含文本的行: {link_text!r}"

    # 检查前一行是否已经是相同锚点
    if found_idx > 0 and f'id="{anchor_id}"' in lines[found_idx - 1]:
        return False, "前一行已存在相同锚点"

    anchor_line = f'<a id="{anchor_id}"></a>\n'
    lines.insert(found_idx, anchor_line)
    target.write_text("".join(lines), encoding="utf-8")
    return True, f"在 {target.relative_to(ROOT)} 第 {found_idx + 1} 行前插入锚点"


def parse_report(report_path: Path):
    text = report_path.read_text(encoding="utf-8")
    issues = []
    section = re.search(r"### 锚点不存在 \(\d+个\)(.*?)(?=###\s+[^#]|$)", text, re.DOTALL)
    if not section:
        return issues
    for line in section.group(1).splitlines():
        m = re.match(r"\|\s*([^|]+?)\s*\|\s*([^|]+?)\s*\|\s*([^|]+?)\s*\|\s*([^|]+?)\s*\|", line)
        if not m or "源文件" in line:
            continue
        source, link_text, url, problem = (x.strip() for x in m.groups())
        link_text = link_text.strip("`")
        url = url.strip("`")
        if "#" not in url:
            continue
        anchor_id = url.split("#", 1)[1]
        issues.append({
            "source": source,
            "link_text": link_text,
            "url": url,
            "anchor_id": anchor_id,
        })
    return issues


def main():
    if not REPORT.exists():
        print(f"报告不存在: {REPORT}")
        return

    issues = parse_report(REPORT)
    print(f"剩余锚点问题: {len(issues)} 个")

    fixed = 0
    skipped = 0
    log = []

    for item in issues:
        raw = item["source"].replace("\\", "/")
        if raw.startswith("docs/"):
            raw = raw[5:]
        source = DOCS_BASE / raw
        target = resolve_target(source, item["url"])
        if target is None:
            skipped += 1
            log.append(f"[SKIP] {source.relative_to(ROOT)}: 无法解析目标 {item['url']}")
            continue

        changed, msg = fix_anchor(source, target, item["anchor_id"], item["link_text"])
        if changed:
            fixed += 1
            log.append(f"[FIXED] {source.relative_to(ROOT)} -> {target.relative_to(ROOT)}#{item['anchor_id']}: {msg}")
        else:
            skipped += 1
            log.append(f"[SKIP] {source.relative_to(ROOT)} -> {target.relative_to(ROOT)}#{item['anchor_id']}: {msg}")

    log_path = ROOT / "reports" / "FIX_REMAINING_ANCHORS_2026_06_25.log"
    log_path.write_text("\n".join(log), encoding="utf-8")
    print(f"修复完成: 成功 {fixed} 个, 跳过 {skipped} 个")
    print(f"日志: {log_path}")


if __name__ == "__main__":
    main()
