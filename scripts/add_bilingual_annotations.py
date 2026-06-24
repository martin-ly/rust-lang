#!/usr/bin/env python3
"""为 concept/01_foundation、02_intermediate、03_advanced 中的 Markdown 文件
添加关键术语中英双语标注（首次出现且未标注时）。

规则：
- 跳过代码块、行内代码、Markdown 链接和图片。
- 跳过标题行（# ...）。
- 仅当同一行没有明显英文对照时才标注。
- 每文件每个术语只标注第一次出现。
"""

from pathlib import Path
import re

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
    ("Trait", "Trait"),
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
]

DIRS = [
    Path("concept/01_foundation"),
    Path("concept/02_intermediate"),
    Path("concept/03_advanced"),
]

# 占位符模板
LINK_PLACEHOLDER = "\x00LINK\x00"
CODE_PLACEHOLDER = "\x00CODE\x00"


def mask_links_and_code(line: str) -> tuple[str, list[str], list[str]]:
    """屏蔽 Markdown 链接、行内代码，返回处理后的行及占位符列表。"""
    links: list[str] = []
    codes: list[str] = []

    def link_repl(m: re.Match) -> str:
        links.append(m.group(0))
        return LINK_PLACEHOLDER

    def code_repl(m: re.Match) -> str:
        codes.append(m.group(0))
        return CODE_PLACEHOLDER

    # 先屏蔽行内代码，避免代码中的 [ 被误识别
    line = re.sub(r"`[^`]+`", code_repl, line)
    # 屏蔽 Markdown 链接 [text](url) 和 ![alt](url)
    line = re.sub(r"!?\[[^\]]*\]\([^)]+\)", link_repl, line)
    return line, links, codes


def unmask(line: str, links: list[str], codes: list[str]) -> str:
    """恢复链接和代码占位符。"""
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


def annotate_line(line: str, seen_terms: set[str]) -> tuple[str, bool]:
    """对单行文本进行术语标注，返回新行和是否修改。"""
    masked, links, codes = mask_links_and_code(line)
    original_masked = masked

    for cn, en in TERMS:
        if cn in seen_terms:
            continue
        # 跳过标题行
        if masked.lstrip().startswith("#"):
            continue
        # 如果本行已包含对应英文术语，则不标注
        if re.search(rf"\b{re.escape(en)}\b", masked, re.IGNORECASE):
            continue
        # 如果该术语后已紧跟英文括号标注，跳过
        if re.search(rf"{re.escape(cn)}\s*[\(（][A-Za-z]", masked):
            continue
        # 查找首次出现且后面不紧跟英文括号的位置
        pattern = re.compile(
            rf"(?<![A-Za-z0-9_\u4e00-\u9fff])({re.escape(cn)})(?![A-Za-z0-9_\u4e00-\u9fff])"
        )

        def repl(m: re.Match) -> str:
            # 检查后面紧跟的括号里是否已有英文
            tail = masked[m.end() : m.end() + 30]
            if re.match(r"[\(（][A-Za-z]", tail):
                return m.group(1)
            # 避免在纯中文括号内嵌套英文括号，如“（生命周期）”
            before = masked[m.start() - 1] if m.start() > 0 else ""
            after = masked[m.end()] if m.end() < len(masked) else ""
            if before in "（(" and after in "）)":
                return m.group(1)
            return f"{m.group(1)}（{en}）"

        new_masked, count = pattern.subn(repl, masked, count=1)
        if count > 0:
            masked = new_masked
            seen_terms.add(cn)

    if masked == original_masked:
        return line, False
    return unmask(masked, links, codes), True


def process_file(path: Path) -> bool:
    raw = path.read_bytes()
    has_bom = raw.startswith(b"\xef\xbb\xbf")
    original = raw.decode("utf-8-sig")

    parts = []
    in_code = False
    seen_terms: set[str] = set()
    changed = False

    for line in original.splitlines(keepends=True):
        if line.lstrip().startswith("```"):
            in_code = not in_code
            parts.append(line)
            continue

        if in_code:
            parts.append(line)
            continue

        new_line, line_changed = annotate_line(line, seen_terms)
        if line_changed:
            changed = True
        parts.append(new_line)

    if changed:
        out = "".join(parts)
        data = out.encode("utf-8")
        if has_bom:
            data = b"\xef\xbb\xbf" + data
        path.write_bytes(data)
    return changed


def main() -> int:
    modified = 0
    for directory in DIRS:
        if not directory.exists():
            continue
        for path in sorted(directory.rglob("*.md")):
            if process_file(path):
                print(f"+ {path}")
                modified += 1
    print(f"\n共修改 {modified} 个文件")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
