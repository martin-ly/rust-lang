#!/usr/bin/env python3
"""
将 concept/ 中指向 placeholder_generic.md 的内部链接替换为真实文件链接或纯文本。
"""
import re
from pathlib import Path
import os

ROOT = Path("e:/_src/rust-lang/concept")

# 链接文本 -> 目标路径（相对 ROOT）
CONCEPT_MAP = {
    "类型系统（Type System）": "01_foundation/04_type_system.md",
    "所有权（Ownership）": "01_foundation/01_ownership.md",
    "L1 所有权（Ownership）": "01_foundation/01_ownership.md",
    "借用（Borrowing）": "01_foundation/02_borrowing.md",
    "L1 借用（Borrowing）": "01_foundation/02_borrowing.md",
    "生命周期（Lifetimes）": "01_foundation/03_lifetimes.md",
    "生命周期（Lifetimes）高级主题：从 HRTB 到自引用（Reference）类型": "01_foundation/01_ownership_borrow_lifetime/30_lifetimes_advanced.md",  # 2026-07-12: 原 02_intermediate/18_lifetimes_advanced.md 已合并重定向
    "泛型（Generics）": "02_intermediate/02_generics.md",
    "L2 泛型（Generics）": "02_intermediate/02_generics.md",
    "Trait": "02_intermediate/01_traits.md",
    "L2 Trait": "02_intermediate/01_traits.md",
    "错误处理（Error Handling）": "01_foundation/10_error_handling_basics.md",
    "Unsafe Rust": "03_advanced/03_unsafe.md",
    "并发编程": "03_advanced/01_concurrency.md",
    "Async": "03_advanced/02_async.md",
    "属性与声明宏（Declarative Macro）：编译期元编程基础": "01_foundation/12_attributes_and_macros.md",
    "零成本抽象（Zero-Cost Abstraction）：Rust 的性能哲学": "01_foundation/06_zero_cost_abstractions.md",
    "闭包（Closures）基础：捕获环境与匿名函数": "01_foundation/15_closure_basics.md",
    "迭代器（Iterator）模式：Rust 的惰性计算与零成本抽象（Zero-Cost Abstraction）": "02_intermediate/16_iterator_patterns.md",
    "Rust for Linux ：操作系统内核中的内存安全（Memory Safety）": "07_future/19_rust_for_linux.md",
    "L4 所有权（Ownership）形式化": "04_formal/03_ownership_formal.md",
    "所有权（Ownership）形式化": "04_formal/03_ownership_formal.md",
    "Miri": "04_formal/31_miri.md",
    "../02_intermediate/02_generics.md": "02_intermediate/02_generics.md",
}

# 来源链接映射：链接文本（去掉“来源:”前缀） -> 外部 URL
SOURCE_MAP = {
    "The Rust Programming Language": "https://doc.rust-lang.org/book/",
    "TRPL": "https://doc.rust-lang.org/book/",
    "Rust Standard Library": "https://doc.rust-lang.org/std/",
    "Rust Reference": "https://doc.rust-lang.org/reference/",
    "Rustonomicon": "https://doc.rust-lang.org/nomicon/",
    "The Rustonomicon": "https://doc.rust-lang.org/nomicon/",
    "Rust Design Patterns": "https://rust-unofficial.github.io/patterns/",
    "Rust API Guidelines": "https://rust-lang.github.io/api-guidelines/",
}

PLACEHOLDER_RE = re.compile(
    r'\[(?P<text>[^\]]+)\]\((?P<path>[^)]*placeholder_generic\.md[^)]*)\)'
)


def relative_path(from_file: Path, to_file: Path) -> str:
    return os.path.relpath(to_file, from_file.parent).replace("\\", "/")


def resolve_link(text: str, current_file: Path):
    # 处理嵌套来源语法: [来源: [XXX](...)] 或 [来源: XXX](...)
    inner_match = re.search(r'\[(?:来源:\s*)?(?:\[(?P<inner_text>[^\]]+)\]\([^)]+\)|(?P<plain_text>[^\]]+))\]', text)
    if inner_match:
        inner_text = inner_match.group('inner_text') or inner_match.group('plain_text')
    else:
        inner_text = text.strip()
        # 去掉常见前缀
        for prefix in ["来源: ", "来源："]:
            if inner_text.startswith(prefix):
                inner_text = inner_text[len(prefix):]

    if inner_text in CONCEPT_MAP:
        target = ROOT / CONCEPT_MAP[inner_text]
        if target.exists():
            rel = relative_path(current_file, target)
            return f"[{text}]({rel})"
    if inner_text in SOURCE_MAP:
        return f"[{text}]({SOURCE_MAP[inner_text]})"
    # 无法解析 -> 纯文本
    return text


def process_file(path: Path):
    content = path.read_text(encoding="utf-8")
    new_content = PLACEHOLDER_RE.sub(lambda m: resolve_link(m.group("text"), path), content)
    if new_content != content:
        path.write_text(new_content, encoding="utf-8")
        return True
    return False


def main():
    changed = 0
    for md in ROOT.rglob("*.md"):
        if process_file(md):
            changed += 1
    print(f"Modified {changed} files")


if __name__ == "__main__":
    main()
