#!/usr/bin/env python3
"""修复上一轮替换后仍失效的官方链接."""
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent / "concept"

REPLACEMENTS = [
    ("https://doc.rust-lang.org/book/ch17-03-ffo.html", "https://doc.rust-lang.org/book/ch17-02-concurrency-with-async.html"),
    ("https://doc.rust-lang.org/std/macro.assert_matches.htmlmacro.assert_matches.html", "https://doc.rust-lang.org/std/macro.assert_matches.html"),
    ("https://doc.rust-lang.org/std/num/NonZeroU32.html", "https://doc.rust-lang.org/std/num/type.NonZeroU32.html"),
    ("https://doc.rust-lang.org/std/sync/atomic/AtomicPtr.html", "https://doc.rust-lang.org/std/sync/atomic/type.AtomicPtr.html"),
    ("https://doc.rust-lang.org/std/sync/atomic/AtomicUsize.html", "https://doc.rust-lang.org/std/sync/atomic/type.AtomicUsize.html"),
    ("https://doc.rust-lang.org/style/", "https://doc.rust-lang.org/nightly/style-guide/"),
]


def main():
    changed = 0
    for p in sorted(ROOT.rglob('*.md')):
        text = p.read_text(encoding='utf-8')
        new_text = text
        for old, new in REPLACEMENTS:
            new_text = new_text.replace(old, new)
        if new_text != text:
            p.write_text(new_text, encoding='utf-8')
            changed += 1
    print(f'updated {changed} files')


if __name__ == '__main__':
    main()
