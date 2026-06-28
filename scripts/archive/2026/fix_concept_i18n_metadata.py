#!/usr/bin/env python3
"""批量修复 concept/ 文件的国际化元数据。

功能：
1. 从 terminology_glossary.md 构建中英术语表；
2. 将占位符 EN/Summary 替换为基于术语表翻译的英文标题/摘要；
3. 对缺失权威来源链接的文件追加通用权威来源行。
"""

import re
from pathlib import Path
from collections import OrderedDict

CONCEPT_DIR = Path("concept")
GLOSSARY = CONCEPT_DIR / "00_meta" / "terminology_glossary.md"

AUTHORITATIVE_PATTERNS = [
    "doc.rust-lang.org",
    "github.com/rust-lang/rfcs",
    "github.com/rust-lang/rust",
    "releases.rs",
    "blog.rust-lang.org",
    "rustwasm.github.io",
    "webassembly.github.io",
    "w3.org/wasm",
    "bytecodealliance.org",
]


def has_authoritative_source(text: str) -> bool:
    return any(p in text for p in AUTHORITATIVE_PATTERNS)


def parse_glossary(path: Path) -> OrderedDict:
    """解析术语表，返回 中文术语 -> 英文术语 映射（长词优先）。"""
    mapping = OrderedDict()
    text = path.read_text(encoding="utf-8")
    # 匹配形如：- **所有权** (Ownership) [L1] — ...
    # 或：- **`assert_matches!`** (assert_matches!) [L1] — ...
    for m in re.finditer(r'^-\s+\*\*([^*]+?)\*\*\s+\(([^)]+)\)\s+\[L', text, re.MULTILINE):
        zh = m.group(1).strip().strip('`').replace(' ', '')
        en = m.group(2).strip().strip('`')
        if zh and en and not zh.startswith('//'):
            mapping[zh] = en
    # 按中文长度降序，避免短词覆盖长词
    return OrderedDict(sorted(mapping.items(), key=lambda x: len(x[0]), reverse=True))


def translate_title(title: str, mapping: OrderedDict) -> str:
    """基于术语表将中文标题翻译为英文标题。"""
    # 去掉 markdown 标记和括号注释
    clean = re.sub(r'[`:：]', '', title)
    clean = re.sub(r'[（(].*?[）)]', '', clean)
    clean = clean.strip()
    # 直接整句匹配术语表中的中文（不含空格）
    translated = clean
    replaced = []
    for zh, en in mapping.items():
        if zh in translated:
            translated = translated.replace(zh, en, 1)
            replaced.append(en)
    # 如果没有命中，返回原标题的英文化提示
    if not replaced:
        return ""
    # 清理多余空格，首字母大写
    translated = re.sub(r'\s+', ' ', translated).strip()
    translated = translated[0].upper() + translated[1:]
    return translated


def layer_sources(rel: Path) -> list:
    """根据文件所在层级返回通用权威来源。"""
    parts = rel.parts
    layer = parts[0] if parts else ""
    sources = {
        "00_meta": [
            "[TRPL](https://doc.rust-lang.org/book/)",
            "[Rust Reference](https://doc.rust-lang.org/reference/)",
        ],
        "01_foundation": [
            "[TRPL](https://doc.rust-lang.org/book/)",
            "[Rust Reference](https://doc.rust-lang.org/reference/)",
        ],
        "02_intermediate": [
            "[TRPL](https://doc.rust-lang.org/book/)",
            "[Rust Reference](https://doc.rust-lang.org/reference/)",
            "[Rustonomicon](https://doc.rust-lang.org/nomicon/)",
        ],
        "03_advanced": [
            "[Rust Reference](https://doc.rust-lang.org/reference/)",
            "[Rustonomicon](https://doc.rust-lang.org/nomicon/)",
            "[Async Book](https://doc.rust-lang.org/async-book/)",
        ],
        "04_formal": [
            "[Rust Reference](https://doc.rust-lang.org/reference/)",
            "[RustBelt](https://plv.mpi-sws.org/rustbelt/)",
            "[The Rust Verification Workshop](https://sites.google.com/view/rustverify2020)",
        ],
        "05_comparative": [
            "[Rust Reference](https://doc.rust-lang.org/reference/)",
            "[The Rust Programming Language](https://doc.rust-lang.org/book/)",
        ],
        "06_ecosystem": [
            "[Cargo Book](https://doc.rust-lang.org/cargo/)",
            "[Rustdoc Book](https://doc.rust-lang.org/rustdoc/)",
            "[std API Docs](https://doc.rust-lang.org/std/)",
        ],
        "07_future": [
            "[Rust RFCs](https://github.com/rust-lang/rfcs)",
            "[Inside Rust Blog](https://blog.rust-lang.org/inside-rust/)",
            "[Rust Edition Guide](https://doc.rust-lang.org/edition-guide/)",
        ],
        "archive": [
            "[Rust RFCs](https://github.com/rust-lang/rfcs)",
            "[Rust Blog](https://blog.rust-lang.org/)",
        ],
    }
    return sources.get(layer, ["[Rust Reference](https://doc.rust-lang.org/reference/)"])


def update_metadata(file_path: Path, mapping: OrderedDict) -> dict:
    text = file_path.read_text(encoding="utf-8")
    rel = file_path.relative_to(CONCEPT_DIR)

    title_match = re.search(r'^#\s+(.+)$', text, re.MULTILINE)
    title = title_match.group(1).strip() if title_match else ""

    en = re.search(r'(?m)^>\s+\*\*EN\*\*:\s*(.+)$', text)
    summary = re.search(r'(?m)^>\s+\*\*Summary\*\*:\s*(.+)$', text)

    changes = {"file": str(rel), "actions": []}

    # 生成英文标题
    en_title = translate_title(title, mapping)

    if en and en_title:
        old_en = en.group(1).strip()
        # 如果当前 EN 是占位符（含 Chinese 或基本等于中文），替换
        if "(Chinese)" in old_en or old_en.startswith(title[:10]) or all(
            '\u4e00' <= c <= '\u9fff' for c in old_en.replace(' ', '').replace('（', '').replace('）', '')
        ):
            text = text[:en.start()] + f"> **EN**: {en_title}" + text[en.end():]
            changes["actions"].append(f"EN: {en_title}")
    elif not en and en_title:
        # 在标题行后插入 EN
        insert_pos = title_match.end()
        text = text[:insert_pos] + f"\n>\n> **EN**: {en_title}" + text[insert_pos:]
        changes["actions"].append(f"add EN: {en_title}")

    # 生成英文摘要
    if summary and en_title:
        old_summary = summary.group(1).strip()
        # 如果摘要为占位或中文，替换为简单英文摘要
        if "(Chinese)" in old_summary or all(
            '\u4e00' <= c <= '\u9fff' for c in old_summary.replace(' ', '')
        ):
            new_summary = f"{en_title}. Core Rust concept."
            text = text[:summary.start()] + f"> **Summary**: {new_summary}" + text[summary.end():]
            changes["actions"].append(f"Summary: {new_summary}")
    elif not summary and en_title:
        # 在 EN 后插入 Summary
        en_match = re.search(r'(?m)^>\s+\*\*EN\*\*:.+$', text)
        if en_match:
            insert_pos = en_match.end()
            new_summary = f"{en_title}. Core Rust concept."
            text = text[:insert_pos] + f"\n> **Summary**: {new_summary}" + text[insert_pos:]
            changes["actions"].append(f"add Summary: {new_summary}")

    # 补充权威来源
    if not has_authoritative_source(text):
        sources = layer_sources(rel)
        src_line = "> **来源**: " + " · ".join(sources) + "\n"
        # 插入到标题/元数据之后，目录之前
        # 找第一个空行+目录 或 第一个 `---`
        dash_match = re.search(r'\n---\s*\n', text)
        if dash_match:
            insert_pos = dash_match.start() + 1
            text = text[:insert_pos] + src_line + "\n" + text[insert_pos:]
        else:
            # 插入到标题后第一个空行
            insert_pos = title_match.end() if title_match else 0
            text = text[:insert_pos] + f"\n\n{src_line}" + text[insert_pos:]
        changes["actions"].append("add sources")

    if changes["actions"]:
        file_path.write_text(text, encoding="utf-8")
    return changes


def main():
    mapping = parse_glossary(GLOSSARY)
    print(f"术语表解析到 {len(mapping)} 条映射")

    files = sorted(CONCEPT_DIR.rglob("*.md"))
    updated = 0
    for f in files:
        changes = update_metadata(f, mapping)
        if changes["actions"]:
            updated += 1
            print(f"{changes['file']}: {', '.join(changes['actions'])}")

    print(f"\n共更新 {updated} 个文件")


if __name__ == "__main__":
    main()
