#!/usr/bin/env python3
"""重建 concept/ 文件头部元数据，修复 CRLF 导致的 Summary 行损坏。

策略：
1. 从 git HEAD 读取原始头部（干净版本）；
2. 从当前文件读取正文（保留 Phase 5 等正文修改）；
3. 在原始头部基础上规范化 EN/Summary/来源字段；
4. 用 LF 写回。
"""

import re
import subprocess
from pathlib import Path

CONCEPT_DIR = Path("concept")

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
    "google.github.io/comprehensive-rust",
    "rust-lang.github.io/api-guidelines",
]


def title_case_stem(stem: str) -> str:
    stem = re.sub(r'^\d+_', '', stem)
    return ' '.join(word.capitalize() for word in stem.split('_'))


def get_original(rel: Path) -> str:
    try:
        return subprocess.check_output(
            ["git", "show", f"HEAD:concept/{rel.as_posix()}"],
            cwd=CONCEPT_DIR.parent,
            text=True,
            stderr=subprocess.DEVNULL,
        )
    except subprocess.CalledProcessError:
        return ""


def split_header_body(text: str):
    # 按第一个 \n## 分割
    text_lf = text.replace('\r\n', '\n')
    idx = text_lf.find('\n## ')
    if idx == -1:
        return text_lf, ""
    return text_lf[:idx + 1], text_lf[idx + 1:]


def is_placeholder(text: str) -> bool:
    if not text:
        return True
    if "(Chinese)" in text:
        return True
    if any('\u4e00' <= c <= '\u9fff' for c in text):
        return True
    return False


def layer_sources(rel: Path) -> list:
    layer = rel.parts[0] if rel.parts else ""
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


def has_source(header: str) -> bool:
    return any(p in header for p in AUTHORITATIVE_PATTERNS)


def rebuild_header(header: str, rel: Path) -> str:
    lines = header.split('\n')

    # 提取标题
    title = ""
    for line in lines:
        m = re.match(r'^#\s+(.+)$', line)
        if m:
            title = m.group(1).strip()
            break

    en_title = title_case_stem(rel.stem)

    # 替换 EN 占位
    new_lines = []
    en_replaced = False
    summary_replaced = False
    source_replaced = has_source(header)
    for line in lines:
        if re.match(r'^>\s+\*\*EN\*\*:', line):
            val = re.sub(r'^>\s+\*\*EN\*\*:\s*', '', line).strip()
            if is_placeholder(val):
                new_lines.append(f"> **EN**: {en_title}")
            else:
                new_lines.append(line)
            en_replaced = True
            continue
        if re.match(r'^>\s+\*\*Summary\*\*:', line):
            val = re.sub(r'^>\s+\*\*Summary\*\*:\s*', '', line).strip()
            if is_placeholder(val):
                new_lines.append(f"> **Summary**: {en_title}. Core Rust concept.")
            else:
                new_lines.append(line)
            summary_replaced = True
            continue
        new_lines.append(line)

    # 找到标题行索引（可能不存在）
    title_idx = -1
    for i, line in enumerate(new_lines):
        if re.match(r'^#\s+', line):
            title_idx = i
            break

    # 如果没有 EN/Summary，插入到标题后；无标题则插入到文件开头
    if not en_replaced:
        if title_idx >= 0:
            new_lines.insert(title_idx + 1, f">\n> **EN**: {en_title}")
        else:
            new_lines.insert(0, f"> **EN**: {en_title}")
    if not summary_replaced:
        for i, line in enumerate(new_lines):
            if re.match(r'^>\s+\*\*EN\*\*:', line):
                new_lines.insert(i + 1, f"> **Summary**: {en_title}. Core Rust concept.")
                break
        else:
            # 没有 EN 行时直接放开头
            new_lines.insert(0, f"> **Summary**: {en_title}. Core Rust concept.")

    # 如果没有来源，在第一个 --- 前或 EN/Summary 块后添加
    if not source_replaced:
        src_line = "> **来源**: " + " · ".join(layer_sources(rel))
        inserted = False
        for i, line in enumerate(new_lines):
            if line.strip() == '---':
                new_lines.insert(i, src_line)
                new_lines.insert(i, ">")
                inserted = True
                break
        if not inserted:
            # 放到第一个非空行之后或文件末尾
            for i in range(len(new_lines) - 1, -1, -1):
                if new_lines[i].strip():
                    new_lines.insert(i + 1, "")
                    new_lines.insert(i + 2, src_line)
                    break
            else:
                new_lines.append(src_line)

    return '\n'.join(new_lines)


def process_file(path: Path) -> bool:
    rel = path.relative_to(CONCEPT_DIR)
    original = get_original(rel)
    if not original:
        return False

    with open(path, "r", encoding="utf-8", newline="") as fh:
        current = fh.read()

    orig_header, _ = split_header_body(original)
    _, curr_body = split_header_body(current)

    new_header = rebuild_header(orig_header, rel)
    new_text = new_header + curr_body

    if new_text != current.replace('\r\n', '\n'):
        path.write_text(new_text, encoding="utf-8", newline="\n")
        return True
    return False


def main():
    files = sorted(CONCEPT_DIR.rglob("*.md"))
    updated = 0
    for f in files:
        if process_file(f):
            updated += 1
            print(f)
    print(f"\n共重建 {updated} 个文件的头部")


if __name__ == "__main__":
    main()
