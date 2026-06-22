#!/usr/bin/env python3
"""审计 concept/ 文件的国际化元数据覆盖情况。

检查项：
- 是否有英文标题 (EN)
- 是否有英文摘要 (Summary)
- 是否有权威来源链接 (doc.rust-lang.org / RFC / releases.rs)
- 英文标题/摘要是否为占位符（与中文相同或过于简短）
"""

import re
from pathlib import Path
from collections import Counter

CONCEPT_DIR = Path("concept")

# 权威来源域名/路径（按项目 source hierarchy 扩展：官方 Rust + 学术/工业 + 社区权威）
AUTHORITATIVE_PATTERNS = [
    # Rust 官方
    "doc.rust-lang.org",
    "github.com/rust-lang/rfcs",
    "github.com/rust-lang/rust",
    "github.com/rust-lang/miri",
    "rust-lang.github.io",
    "rustc-dev-guide.rust-lang.org",
    "forge.rust-lang.org",
    "www.rust-lang.org",
    "foundation.rust-lang.org",
    "blog.rust-lang.org",
    "releases.rs",
    "rustwasm.github.io",
    "webassembly.github.io",
    "w3.org/wasm",
    "bytecodealliance.org",
    # 国际权威教学/工业
    "google.github.io/comprehensive-rust",
    "rust-book.cs.brown.edu",
    "doc.rust-embedded.org",
    "tokio.rs",
    "diesel.rs",
    "sea-ql.org",
    "docs.rs",
    "crates.io",
    "martinfowler.com",
    "semver.org",
    # 形式化/学术
    "plv.mpi-sws.org/rustbelt",
    "perso.crans.org/vanille/treebor",
    "github.com/rust-lang/a-mir-formality",
    "github.com/model-checking",
    "github.com/verus-lang",
    "github.com/safer-rust",
    "borrowsanitizer.com",
    "dl.acm.org",
    "arxiv.org",
    "doi.org",
    # 通用权威参考
    "en.wikipedia.org",
]


def has_authoritative_source(text: str) -> bool:
    return any(p in text for p in AUTHORITATIVE_PATTERNS)


def extract_en(text: str):
    m = re.search(r'\*\*EN\*\*:\s*(.+)', text)
    return m.group(1).strip() if m else None


def extract_summary(text: str):
    m = re.search(r'\*\*Summary\*\*:\s*(.+)', text)
    return m.group(1).strip() if m else None


def is_placeholder(en: str, title: str) -> bool:
    if not en:
        return True
    # 如果 EN 与中文标题基本相同，或者是中文，视为占位
    if en == title or en.startswith(title) or all('\u4e00' <= c <= '\u9fff' for c in en.replace(' ', '')):
        return True
    if len(en) < 5:
        return True
    return False


def main():
    files = sorted(CONCEPT_DIR.rglob("*.md"))
    total = len(files)
    missing_en = []
    missing_summary = []
    placeholder_en = []
    placeholder_summary = []
    missing_source = []

    for f in files:
        text = f.read_text(encoding="utf-8")
        # 取第一个一级标题作为中文标题
        title_match = re.search(r'^#\s+(.+)$', text, re.MULTILINE)
        title = title_match.group(1).strip() if title_match else ""

        en = extract_en(text)
        summary = extract_summary(text)
        source_ok = has_authoritative_source(text)

        if not en:
            missing_en.append(f)
        elif is_placeholder(en, title):
            placeholder_en.append((f, en))

        if not summary:
            missing_summary.append(f)
        elif is_placeholder(summary, title):
            placeholder_summary.append((f, summary))

        if not source_ok:
            missing_source.append(f)

    def pct(n):
        return f"{n / total * 100:.1f}%"

    print(f"扫描 concept/ 下的 {total} 个 Markdown 文件\n")
    print("| 指标 | 数量 | 占比 |")
    print("|:---|---:|---:|")
    print(f"| 有英文标题 (EN) | {total - len(missing_en)} | {pct(total - len(missing_en))} |")
    print(f"| 英文标题为占位符 | {len(placeholder_en)} | {pct(len(placeholder_en))} |")
    print(f"| 有英文摘要 (Summary) | {total - len(missing_summary)} | {pct(total - len(missing_summary))} |")
    print(f"| 英文摘要为占位符 | {len(placeholder_summary)} | {pct(len(placeholder_summary))} |")
    print(f"| 有权威来源链接 | {total - len(missing_source)} | {pct(total - len(missing_source))} |")

    print("\n## 缺失权威来源链接的文件（前 30）\n")
    for f in missing_source[:30]:
        print(f"- {f}")

    print("\n## 英文标题为占位符的文件（前 30）\n")
    for f, en in placeholder_en[:30]:
        print(f"- {f}: `{en}`")


if __name__ == "__main__":
    main()
