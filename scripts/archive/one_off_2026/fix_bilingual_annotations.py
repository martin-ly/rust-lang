#!/usr/bin/env python3
"""Fix remaining bilingual annotation mismatches in concept/ Markdown files.

Scans the uncovered-terms JSON produced by add_bilingual_annotations.py and
corrects or adds English annotations for each term occurrence.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

TERMS = [
    ("所有权", "Ownership"),
    ("可变借用", "Mutable Borrow"),
    ("不可变借用", "Immutable Borrow"),
    ("借用", "Borrowing"),
    ("生命周期", "Lifetimes"),
    ("可变引用", "Mutable Reference"),
    ("不可变引用", "Immutable Reference"),
    ("引用", "Reference"),
    ("字符串切片", "String Slice"),
    ("切片", "Slice"),
    ("结构体", "Struct"),
    ("枚举", "Enum"),
    ("模式匹配", "Pattern Matching"),
    ("闭包", "Closures"),
    ("迭代器", "Iterator"),
    ("泛型", "Generics"),
    ("trait对象", "Trait Object"),
    ("trait", "Trait"),
    ("Box", "Box"),
    ("Vec", "Vec"),
    ("HashMap", "HashMap"),
    ("Result", "Result"),
    ("Option", "Option"),
    ("panic", "Panic"),
    ("错误处理", "Error Handling"),
    ("智能指针", "Smart Pointer"),
    ("原子操作", "Atomic Operations"),
    ("异步", "Async"),
    ("Future", "Future"),
    ("运行时", "Runtime"),
    ("原始指针", "Raw Pointer"),
    ("内联汇编", "Inline Assembly"),
    ("FFI", "FFI"),
    ("声明宏", "Declarative Macro"),
    ("过程宏", "Procedural Macro"),
    ("宏", "Macro"),
    ("模块", "Module"),
    ("crate", "Crate"),
    ("Cargo", "Cargo"),
    ("零成本抽象", "Zero-Cost Abstraction"),
    ("RAII", "RAII"),
    ("类型系统", "Type System"),
    ("类型推断", "Type Inference"),
    ("内存安全", "Memory Safety"),
    ("并发安全", "Concurrency Safety"),
    ("Send", "Send"),
    ("Sync", "Sync"),
    ("unsafe", "Unsafe"),
    ("Pin", "Pin"),
    ("生命周期省略", "Lifetime Elision"),
    ("孤儿规则", "Orphan Rule"),
    ("一致性", "Coherence"),
    ("单态化", "Monomorphization"),
]

TERM_EN = {cn: en for cn, en in TERMS}

LINK_PLACEHOLDER = "\x00LINK\x00"
CODE_PLACEHOLDER = "\x00CODE\x00"


def mask_links_and_code(line: str) -> tuple[str, list[str], list[str]]:
    links: list[str] = []
    codes: list[str] = []

    def link_repl(m: re.Match) -> str:
        links.append(m.group(0))
        return LINK_PLACEHOLDER

    def code_repl(m: re.Match) -> str:
        codes.append(m.group(0))
        return CODE_PLACEHOLDER

    line = re.sub(r"`[^`]+`", code_repl, line)
    line = re.sub(r"\]\([^)]+\)", link_repl, line)
    return line, links, codes


def unmask(line: str, links: list[str], codes: list[str]) -> str:
    parts = line.split(LINK_PLACEHOLDER)
    out = ""
    link_idx = 0
    for i, part in enumerate(parts):
        out += part
        if i < len(parts) - 1:
            out += links[link_idx]
            link_idx += 1
    parts = out.split(CODE_PLACEHOLDER)
    out = ""
    code_idx = 0
    for i, part in enumerate(parts):
        out += part
        if i < len(parts) - 1:
            out += codes[code_idx]
            code_idx += 1
    return out


def collect_text_blocks(content: str) -> str:
    blocks = []
    in_code = False
    for line in content.splitlines():
        if line.lstrip().startswith("```"):
            in_code = not in_code
            continue
        if in_code:
            continue
        blocks.append(line)
    return "\n".join(blocks)


def has_bilingual_annotation(text: str, cn: str, en: str) -> bool:
    if re.search(rf"{re.escape(cn)}\s*[（(]{re.escape(en)}[）)]", text):
        return True
    if re.search(rf"\b{re.escape(en)}\b", text, re.IGNORECASE):
        return True
    return False


def fix_line(line: str, needed_terms: set[str]) -> tuple[str, bool]:
    if line.lstrip().startswith("#"):
        return line, False
    masked, links, codes = mask_links_and_code(line)
    original = masked
    changed = False

    for cn in needed_terms:
        en = TERM_EN[cn]
        # Already correctly annotated (term immediately followed by correct English)?
        if re.search(rf"{re.escape(cn)}\s*[（(]{re.escape(en)}[）)]", masked):
            continue
        # Fix wrong English annotation after the term
        wrong_en_re = re.compile(rf"({re.escape(cn)})\s*[（(][A-Za-z][^）)]*[）)]")
        new_masked, n = wrong_en_re.subn(rf"\1（{en}）", masked)
        if n > 0:
            masked = new_masked
            changed = True
            continue
        # Add annotation if the correct English is not already present nearby
        if re.search(rf"\b{re.escape(en)}\b", masked, re.IGNORECASE):
            continue
        pattern = re.compile(rf"(?<![A-Za-z0-9_])({re.escape(cn)})(?![A-Za-z0-9_])(?!\s*[（(])")
        new_masked, n = pattern.subn(rf"\1（{en}）", masked, count=1)
        if n > 0:
            masked = new_masked
            changed = True

    if not changed:
        return line, False
    return unmask(masked, links, codes), True


def fix_code_comment(line: str, needed_terms: set[str]) -> tuple[str, bool]:
    """Annotate terms inside code-block comments (lines starting with // inside ```rust)."""
    stripped = line.lstrip()
    if not stripped.startswith("//"):
        return line, False
    comment_start = line.find("//")
    prefix = line[:comment_start]
    comment = line[comment_start:]
    changed = False
    for cn in needed_terms:
        en = TERM_EN[cn]
        if re.search(rf"{re.escape(cn)}\s*[（(]{re.escape(en)}[）)]", comment):
            continue
        pattern = re.compile(rf"(?<![A-Za-z0-9_])({re.escape(cn)})(?![A-Za-z0-9_])(?!\s*[（(])")
        new_comment, n = pattern.subn(rf"\1（{en}）", comment, count=1)
        if n > 0:
            comment = new_comment
            changed = True
    if not changed:
        return line, False
    return prefix + comment, True


def fix_file(path: Path, needed_terms: set[str]) -> int:
    content = path.read_text(encoding="utf-8")
    original = content
    in_code = False
    code_lang = ""
    lines: list[str] = []
    changes = 0

    for line in content.splitlines(keepends=True):
        if line.lstrip().startswith("```"):
            in_code = not in_code
            code_lang = line.lstrip()[3:].strip().lower() if in_code else ""
            lines.append(line)
            continue
        if in_code and code_lang in ("rust", "rs", "", "text"):
            new_line, changed = fix_code_comment(line, needed_terms)
            if changed:
                changes += 1
            lines.append(new_line)
            continue
        if in_code:
            lines.append(line)
            continue

        new_line, changed = fix_line(line, needed_terms)
        if changed:
            changes += 1
        lines.append(new_line)

    new_content = "".join(lines)
    if new_content != original:
        path.write_text(new_content, encoding="utf-8")
    return changes


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--uncovered", required=True, help="Path to uncovered_terms JSON")
    args = parser.parse_args()

    data = json.loads(Path(args.uncovered).read_text(encoding="utf-8"))
    total_changes = 0
    for term, files in data.items():
        if term not in TERM_EN:
            continue
        for f in files:
            p = Path(f)
            if not p.exists():
                continue
            content = p.read_text(encoding="utf-8")
            text = collect_text_blocks(content)
            if not re.search(rf"(?<![A-Za-z0-9_]){re.escape(term)}(?![A-Za-z0-9_])", text):
                continue
            if has_bilingual_annotation(text, term, TERM_EN[term]):
                continue
            changes = fix_file(p, {term})
            if changes:
                total_changes += changes
                print(f"fixed {p}: {term} ({changes} changes)")

    print(f"\nTotal changes: {total_changes}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
