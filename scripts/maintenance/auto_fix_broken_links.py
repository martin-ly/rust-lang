#!/usr/bin/env python3
"""
根据 docs/LINK_CHECK_REPORT.md 自动修复 docs/ 目录下的损坏链接。

修复策略：
1. 锚点不存在（同文件 / 跨文件）：通过链接文本匹配 Markdown 标题，重新计算 GitHub 风格锚点。
2. 文件不存在：
   - 以 '/' 开头的根相对链接，转为从源文件到项目根目标的相对路径。
   - 相对链接如果目标不存在，则在项目中按文件名搜索；若唯一命中，则重写到实际位置。
   - 目标在 archive/ 下的，优先指向 archive 路径。

只修改有把握修复的链接，所有改动都会打印日志。
"""
import os
import re
import sys
from pathlib import Path
from urllib.parse import urlparse, unquote

ROOT = Path(__file__).resolve().parent.parent.parent
DOCS_BASE = ROOT / "docs"
REPORT = DOCS_BASE / "LINK_CHECK_REPORT.md"


def slugify(text: str) -> str:
    """与 scripts/check_links.py 保持一致的 GitHub 风格锚点生成。"""
    # 移除显式 {#id}
    text = re.sub(r"\s*\{#[^}]+\}\s*$", "", text)
    # 移除非 word/空白/连字符字符，转小写，空白替换为 -
    anchor = re.sub(r"[^\w\s-]", "", text).strip().lower().replace(" ", "-")
    return anchor.strip("-")


def normalize_heading(text: str) -> str:
    """用于比较标题文本，忽略 markdown 格式、emoji、标点、首尾空白。"""
    # 移除粗体/斜体/删除线/行内代码标记
    t = re.sub(r"(\*\*|__|~~|`)", "", text)
    # 移除显式 {#id}
    t = re.sub(r"\s*\{#[^}]+\}\s*", "", t)
    # 移除非 word/空白字符
    return re.sub(r"[^\w\s]", "", t).strip().lower()


def find_heading(content: str, link_text: str):
    """
    在 Markdown 内容中寻找与链接文本匹配的标题。
    返回 (原始标题行, 生成的正确锚点) 或 (None, None)。
    """
    candidates = [
        link_text,
        link_text.strip(),
        re.sub(r"^[^\w]+", "", link_text),  # 去掉开头的 emoji/标点
    ]
    norm_candidates = [normalize_heading(t) for t in candidates if normalize_heading(t)]

    headers = re.findall(r"^#{1,6}\s+(.+)$", content, re.MULTILINE)
    for h in headers:
        h_clean = re.sub(r"\s*\{#[^}]+\}\s*$", "", h)
        h_norm = normalize_heading(h_clean)
        for norm in norm_candidates:
            if h_norm == norm:
                return h, slugify(h_clean)
        # 也尝试子串匹配（链接文本是标题的一部分）
        for norm in norm_candidates:
            if norm and norm in h_norm:
                return h, slugify(h_clean)
    return None, None


def search_target(filename: str) -> Path | None:
    """在项目范围内按文件名搜索目标文件，返回唯一命中或 None。"""
    matches = []
    for p in ROOT.rglob(filename):
        if p.is_file() and ".git" not in p.parts:
            matches.append(p)
    if len(matches) == 1:
        return matches[0]
    # 如果多个，优先 docs/ 下路径
    docs_matches = [m for m in matches if DOCS_BASE in m.parents or m.parent == DOCS_BASE]
    if len(docs_matches) == 1:
        return docs_matches[0]
    return None


def relative_link(source: Path, target: Path) -> str:
    """计算从 source 所在目录到 target 的相对路径（URL 风格）。"""
    return Path(os.path.relpath(target, source.parent)).as_posix()


def fix_anchor_in_file(source_file: Path, url: str, link_text: str) -> tuple[bool, str]:
    """尝试修复锚点链接。返回 (是否修改, 日志信息)。"""
    if not source_file.exists():
        return False, f"源文件不存在: {source_file}"

    content = source_file.read_text(encoding="utf-8")
    path_part, sep, anchor = url.partition("#")
    if not anchor:
        return False, "非锚点链接"

    h, correct_anchor = find_heading(content, link_text)
    if not correct_anchor:
        return False, f"未找到匹配标题: {link_text!r}"

    if correct_anchor == anchor:
        return False, "锚点已正确"

    new_url = f"{path_part}#{correct_anchor}" if path_part else f"#{correct_anchor}"

    old = f"[{link_text}]({url})"
    new = f"[{link_text}]({new_url})"
    if old not in content:
        return False, f"未定位到链接: {old}"

    new_content = content.replace(old, new)
    source_file.write_text(new_content, encoding="utf-8")
    return True, f"锚点: {anchor!r} -> {correct_anchor!r}"


def fix_file_link_in_file(source_file: Path, url: str, link_text: str) -> tuple[bool, str]:
    """尝试修复文件不存在链接。返回 (是否修改, 日志信息)。"""
    if not source_file.exists():
        return False, f"源文件不存在: {source_file}"

    content = source_file.read_text(encoding="utf-8")
    path_part, sep, anchor = url.partition("#")

    # 根相对路径 /xxx -> 项目根
    if path_part.startswith("/"):
        target = ROOT / path_part.lstrip("/")
        if not target.exists():
            # 按文件名搜索
            target = search_target(Path(path_part).name)
            if not target:
                return False, f"根相对目标未找到: {path_part!r}"
        new_path = relative_link(source_file, target)
        new_url = f"{new_path}#{anchor}" if anchor else new_path
        old = f"[{link_text}]({url})"
        new = f"[{link_text}]({new_url})"
        if old not in content:
            return False, f"未定位到链接: {old}"
        new_content = content.replace(old, new)
        source_file.write_text(new_content, encoding="utf-8")
        return True, f"根相对: {url!r} -> {new_url!r}"

    # 相对路径：先按源文件解析
    candidate = (source_file.parent / path_part).resolve()
    if candidate.exists():
        return False, "目标文件实际存在（可能报告已过时）"

    # 在项目中搜索文件名
    target = search_target(Path(path_part).name)
    if not target:
        return False, f"未找到目标文件: {path_part!r}"

    new_path = relative_link(source_file, target)
    new_url = f"{new_path}#{anchor}" if anchor else new_path
    old = f"[{link_text}]({url})"
    new = f"[{link_text}]({new_url})"
    if old not in content:
        return False, f"未定位到链接: {old}"
    new_content = content.replace(old, new)
    source_file.write_text(new_content, encoding="utf-8")
    return True, f"文件: {path_part!r} -> {new_path!r}"


def resolve_source(source_str: str) -> Path:
    """将报告中的源文件路径解析为绝对 Path。"""
    raw = source_str.replace("\\", "/")
    if raw.startswith("docs/"):
        raw = raw[5:]
    return DOCS_BASE / raw


def parse_report(report_path: Path):
    """解析链接检查报告，返回 (anchor_issues, file_issues) 两个列表。"""
    text = report_path.read_text(encoding="utf-8")

    anchor_issues = []
    file_issues = []

    # 锚点不存在段
    anchor_section = re.search(r"### 锚点不存在 \(\d+个\)(.*?)### 文件不存在", text, re.DOTALL)
    if anchor_section:
        for line in anchor_section.group(1).splitlines():
            m = re.match(r"\|\s*([^|]+?)\s*\|\s*([^|]+?)\s*\|\s*([^|]+?)\s*\|\s*([^|]+?)\s*\|", line)
            if not m or "源文件" in line:
                continue
            source, link_text, url, problem = (x.strip() for x in m.groups())
            link_text = link_text.strip("`")
            url = url.strip("`")
            anchor_issues.append({"source": source, "link_text": link_text, "url": url, "problem": problem})

    # 文件不存在段
    file_section = re.search(r"### 文件不存在 \(\d+个\)(.*?)(?:###\s+\d+\.|$)", text, re.DOTALL)
    if file_section:
        for line in file_section.group(1).splitlines():
            m = re.match(r"\|\s*([^|]+?)\s*\|\s*([^|]+?)\s*\|\s*([^|]+?)\s*\|\s*([^|]+?)\s*\|", line)
            if not m or "源文件" in line:
                continue
            source, link_text, url, problem = (x.strip() for x in m.groups())
            link_text = link_text.strip("`")
            url = url.strip("`")
            file_issues.append({"source": source, "link_text": link_text, "url": url, "problem": problem})

    return anchor_issues, file_issues


def main():
    if not REPORT.exists():
        print(f"报告不存在: {REPORT}")
        sys.exit(1)

    anchor_issues, file_issues = parse_report(REPORT)
    print(f"解析到锚点问题: {len(anchor_issues)} 个")
    print(f"解析到文件问题: {len(file_issues)} 个")

    fixed = 0
    skipped = 0
    log_lines = []

    # 先处理锚点问题
    for item in anchor_issues:
        source_file = resolve_source(item["source"])
        changed, msg = fix_anchor_in_file(source_file, item["url"], item["link_text"])
        if changed:
            fixed += 1
            log_lines.append(f"[FIXED anchor] {source_file.relative_to(ROOT)}: {msg}")
        else:
            skipped += 1
            log_lines.append(f"[SKIP anchor] {source_file.relative_to(ROOT)}: [{item['link_text']}]({item['url']}) => {msg}")

    # 再处理文件问题
    for item in file_issues:
        source_file = resolve_source(item["source"])
        changed, msg = fix_file_link_in_file(source_file, item["url"], item["link_text"])
        if changed:
            fixed += 1
            log_lines.append(f"[FIXED file] {source_file.relative_to(ROOT)}: {msg}")
        else:
            skipped += 1
            log_lines.append(f"[SKIP file] {source_file.relative_to(ROOT)}: [{item['link_text']}]({item['url']}) => {msg}")

    log_path = ROOT / "reports" / "AUTO_FIX_BROKEN_LINKS_2026_06_25.log"
    log_path.write_text("\n".join(log_lines), encoding="utf-8")
    print(f"\n修复完成: 成功 {fixed} 个, 跳过 {skipped} 个")
    print(f"详细日志: {log_path}")


if __name__ == "__main__":
    main()
