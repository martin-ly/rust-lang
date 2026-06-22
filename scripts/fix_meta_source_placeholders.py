#!/usr/bin/env python3
"""修复 concept/00_meta/ 中纯文本占位来源引用，替换为带 URL 的 Markdown 链接。

仅处理未带链接的 `[名称]` 形式，避免重复修改已链接的引用。
"""

import re
from pathlib import Path

ROOT = Path("concept/00_meta")

# 占位符 -> 替换后的 Markdown 链接（保持原显示文本）
REPLACEMENTS = {
    "[Rust Reference]": "[Rust Reference](https://doc.rust-lang.org/reference/)",
    "[Rust Internals]": "[Rust Internals Forum](https://internals.rust-lang.org/)",
    "[Rust RFCs]": "[Rust RFCs](https://rust-lang.github.io/rfcs/)",
    "[RFCs]": "[Rust RFCs](https://rust-lang.github.io/rfcs/)",
    "[RustBelt/Oxide]": "[RustBelt / Oxide](https://plv.mpi-sws.org/rustbelt/)",
    "[POPL 类型论文]": "[POPL Papers](https://dblp.org/db/conf/popl/index.html)",
    "[计算理论]": "[Theory of Computation](https://en.wikipedia.org/wiki/Theory_of_computation)",
    "[Felleisen 表达力理论]": "[Felleisen — On the Expressive Power of Programming Languages](https://doi.org/10.1007/BF00119822)",
    "[PL 语义学经典]": "[Programming Language Semantics](https://en.wikipedia.org/wiki/Semantics_(computer_science))",
    "[concept/知识体系规范]": "[concept/知识体系规范](./authority_source_map.md)",
    "[Bloom Taxonomy 2001]": "[Bloom's Taxonomy (2001 Revision)](https://en.wikipedia.org/wiki/Bloom%27s_taxonomy)",
    "[TRPL]": "[The Rust Programming Language](https://doc.rust-lang.org/book/)",
}


def replace_placeholders(text: str) -> tuple[str, int]:
    count = 0
    for old, new in REPLACEMENTS.items():
        # 仅替换 old 后面不紧跟 '(' 的实例（即未链接的占位符）
        pattern = re.escape(old) + r"(?!\()"
        new_text, n = re.subn(pattern, new, text)
        if n:
            text = new_text
            count += n
    return text, count


def main():
    dry_run = "--dry-run" in __import__("sys").argv
    total = 0
    changed_files = []
    for p in sorted(ROOT.rglob("*.md")):
        text = p.read_text(encoding="utf-8", errors="ignore")
        new_text, n = replace_placeholders(text)
        if n:
            total += n
            changed_files.append((p, n))
            if not dry_run:
                p.write_text(new_text, encoding="utf-8")
    print(f"{'[dry-run] ' if dry_run else ''}发现 {len(changed_files)} 个文件，共 {total} 处占位来源引用")
    for p, n in changed_files:
        print(f"  {p.relative_to(ROOT)}: {n}")


if __name__ == "__main__":
    main()
