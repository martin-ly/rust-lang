#!/usr/bin/env python3
"""Final pass: add bilingual annotations for remaining uncovered terms.

This script is more aggressive than add_bilingual_annotations.py:
- it annotates terms in code-block comments
- it corrects wrong English annotations
- it adds annotations to plain text occurrences
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

TERMS = {
    "所有权": "Ownership",
    "可变借用": "Mutable Borrow",
    "不可变借用": "Immutable Borrow",
    "借用": "Borrowing",
    "生命周期": "Lifetimes",
    "可变引用": "Mutable Reference",
    "不可变引用": "Immutable Reference",
    "引用": "Reference",
    "字符串切片": "String Slice",
    "切片": "Slice",
    "结构体": "Struct",
    "枚举": "Enum",
    "模式匹配": "Pattern Matching",
    "闭包": "Closures",
    "迭代器": "Iterator",
    "泛型": "Generics",
    "trait对象": "Trait Object",
    "trait": "Trait",
    "Box": "Box",
    "Vec": "Vec",
    "HashMap": "HashMap",
    "Result": "Result",
    "Option": "Option",
    "panic": "Panic",
    "错误处理": "Error Handling",
    "智能指针": "Smart Pointer",
    "原子操作": "Atomic Operations",
    "异步": "Async",
    "Future": "Future",
    "运行时": "Runtime",
    "原始指针": "Raw Pointer",
    "内联汇编": "Inline Assembly",
    "FFI": "FFI",
    "声明宏": "Declarative Macro",
    "过程宏": "Procedural Macro",
    "宏": "Macro",
    "模块": "Module",
    "crate": "Crate",
    "Cargo": "Cargo",
    "零成本抽象": "Zero-Cost Abstraction",
    "RAII": "RAII",
    "类型系统": "Type System",
    "类型推断": "Type Inference",
    "内存安全": "Memory Safety",
    "并发安全": "Concurrency Safety",
    "Send": "Send",
    "Sync": "Sync",
    "unsafe": "Unsafe",
    "Pin": "Pin",
    "生命周期省略": "Lifetime Elision",
    "孤儿规则": "Orphan Rule",
    "一致性": "Coherence",
    "单态化": "Monomorphization",
}


def term_word_re(cn: str) -> re.Pattern:
    return re.compile(rf"(?<![A-Za-z0-9_])({re.escape(cn)})(?![A-Za-z0-9_])")


def already_correct(text: str, cn: str, en: str) -> bool:
    return bool(re.search(rf"{re.escape(cn)}\s*[（(]{re.escape(en)}[）)]", text))


def fix_text_line(line: str, cn: str, en: str) -> tuple[str, bool]:
    if line.lstrip().startswith("#"):
        return line, False
    # Protect inline code spans and link URLs
    codes: list[str] = []
    links: list[str] = []

    def code_repl(m: re.Match) -> str:
        codes.append(m.group(0))
        return "\x00CODE\x00"

    def link_repl(m: re.Match) -> str:
        links.append(m.group(0))
        return "\x00LINK\x00"

    masked = re.sub(r"`[^`]+`", code_repl, line)
    masked = re.sub(r"\]\([^)]+\)", link_repl, masked)

    if already_correct(masked, cn, en):
        return line, False

    # Correct wrong English annotation
    wrong_re = re.compile(rf"({re.escape(cn)})\s*[（(][A-Za-z][^）)]*[）)]")
    new_masked, n = wrong_re.subn(rf"\1（{en}）", masked)
    if n > 0:
        masked = new_masked
    else:
        # If correct English already appears in line, skip adding annotation
        if re.search(rf"\b{re.escape(en)}\b", masked, re.IGNORECASE):
            return line, False
        pattern = term_word_re(cn)
        new_masked, n = pattern.subn(rf"\1（{en}）", masked, count=1)
        if n == 0:
            return line, False
        masked = new_masked

    # Unmask
    parts = masked.split("\x00LINK\x00")
    out = ""
    for i, part in enumerate(parts):
        out += part
        if i < len(parts) - 1:
            out += links.pop(0)
    parts = out.split("\x00CODE\x00")
    out = ""
    for i, part in enumerate(parts):
        out += part
        if i < len(parts) - 1:
            out += codes.pop(0)
    return out, True


def fix_code_comment_line(line: str, cn: str, en: str) -> tuple[str, bool]:
    stripped = line.lstrip()
    if not (stripped.startswith("//") or stripped.startswith("/*") or stripped.startswith("*")):
        return line, False
    comment_start = len(line) - len(stripped)
    prefix = line[:comment_start]
    comment = line[comment_start:]
    if already_correct(comment, cn, en):
        return line, False
    pattern = term_word_re(cn)
    new_comment, n = pattern.subn(rf"\1（{en}）", comment, count=1)
    if n == 0:
        return line, False
    return prefix + new_comment, True


def fix_file(path: Path, term: str) -> int:
    cn = term
    en = TERMS[term]
    content = path.read_text(encoding="utf-8")
    original = content
    in_code = False
    lines: list[str] = []
    changes = 0

    for line in content.splitlines(keepends=True):
        if line.lstrip().startswith("```"):
            in_code = not in_code
            lines.append(line)
            continue
        if in_code:
            new_line, changed = fix_code_comment_line(line, cn, en)
        else:
            new_line, changed = fix_text_line(line, cn, en)
        if changed:
            changes += 1
        lines.append(new_line)

    new_content = "".join(lines)
    if new_content != original:
        path.write_text(new_content, encoding="utf-8")
    return changes


def main() -> int:
    if len(sys.argv) < 2:
        print("Usage: final_bilingual_fix.py <uncovered_terms.json>")
        return 1

    data = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
    total = 0
    for term, files in data.items():
        if term not in TERMS:
            continue
        for f in files:
            p = Path(f)
            if not p.exists():
                continue
            content = p.read_text(encoding="utf-8")
            if not term_word_re(term).search(content):
                continue
            changes = fix_file(p, term)
            if changes:
                total += changes
                print(f"fixed {p}: {term} ({changes})")

    print(f"\nTotal changes: {total}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
