#!/usr/bin/env python3
"""将 concept/ 中指向官方文档根 URL 的链接替换为具体入口或主题锚点。"""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent.parent
CONCEPT_DIR = ROOT / "concept"

# 默认根 URL -> 具体入口页面
ROOT_TO_ENTRY = {
    "https://doc.rust-lang.org/reference/": "https://doc.rust-lang.org/reference/introduction.html",
    "https://doc.rust-lang.org/book/": "https://doc.rust-lang.org/book/title-page.html",
    "https://doc.rust-lang.org/nomicon/": "https://doc.rust-lang.org/nomicon/index.html",
    "https://doc.rust-lang.org/rust-by-example/": "https://doc.rust-lang.org/rust-by-example/index.html",
    "https://doc.rust-lang.org/edition-guide/": "https://doc.rust-lang.org/edition-guide/index.html",
    "https://doc.rust-lang.org/cargo/": "https://doc.rust-lang.org/cargo/index.html",
    "https://doc.rust-lang.org/std/": "https://doc.rust-lang.org/std/index.html",
    "https://doc.rust-lang.org/embedded-book/": "https://doc.rust-lang.org/embedded-book/index.html",
    "https://rust-lang.github.io/async-book/": "https://rust-lang.github.io/async-book/index.html",
    "https://rust-lang.github.io/rfcs/": "https://rust-lang.github.io/rfcs/index.html",
    "https://rustwasm.github.io/book/": "https://rustwasm.github.io/docs/book/index.html",
    "https://rust-cli.github.io/book/": "https://rust-cli.github.io/book/index.html",
    "https://aya-rs.dev/book/": "https://aya-rs.dev/book/index.html",
    "https://docs.rust-embedded.org/book/": "https://docs.rust-embedded.org/book/index.html",
}

# 根据链接文本中的关键词强制映射到具体章节（大小写不敏感）
LABEL_OVERRIDES = [
    (r"coherence\s+rules", "https://doc.rust-lang.org/reference/items/implementations.html#coherence"),
    (r"diverging\s+functions", "https://doc.rust-lang.org/reference/types/never.html"),
    (r"impl\s+trait", "https://doc.rust-lang.org/reference/types/impl-trait.html"),
    (r"behavior\s+considered\s+undefined", "https://doc.rust-lang.org/reference/behavior-considered-undefined.html"),
]

ROOT_RE = re.compile(r"\]\((" + "|".join(re.escape(u) for u in ROOT_TO_ENTRY) + r")\)")
LINK_RE = re.compile(r"\[([^\]]+)\]\((https?://[^\)]+)\)")


def target_url(label: str, original_url: str) -> str:
    label_lower = label.lower()
    for pat, url in LABEL_OVERRIDES:
        if re.search(pat, label_lower):
            return url
    return ROOT_TO_ENTRY.get(original_url, original_url)


def fix_file(path: Path) -> int:
    text = path.read_text(encoding="utf-8")
    original = text

    # 1) 基于链接文本的精确覆盖
    def label_repl(m):
        label, url = m.group(1), m.group(2)
        new_url = target_url(label, url)
        if new_url != url:
            return f"[{label}]({new_url})"
        return m.group(0)

    text = LINK_RE.sub(label_repl, text)

    # 2) 兜底：纯根 URL 替换
    def root_repl(m):
        return "](" + ROOT_TO_ENTRY[m.group(1)] + ")"

    text = ROOT_RE.sub(root_repl, text)

    if text != original:
        path.write_text(text, encoding="utf-8", newline="\n")
        return 1
    return 0


def main():
    files = list(CONCEPT_DIR.rglob("*.md"))
    changed = sum(fix_file(p) for p in files)
    print(f"已处理 {len(files)} 个文件，修改 {changed} 个。")


if __name__ == "__main__":
    main()
