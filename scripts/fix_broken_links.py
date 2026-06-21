#!/usr/bin/env python3
"""修复概念文件中已确认 404 的官方来源链接."""
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent / "concept"

REPLACEMENTS = {
    r"https://doc\.rust-lang\.org/async-book/": "https://rust-lang.github.io/async-book/",
    r"https://doc\.rust-lang\.org/book/ch04-00-ownership\.html": "https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html",
    r"https://doc\.rust-lang\.org/book/ch13-00-closures\.html": "https://doc.rust-lang.org/book/ch13-01-closures.html",
    r"https://doc\.rust-lang\.org/book/ch19-02-advanced-lifetimes\.html": "https://doc.rust-lang.org/book/ch10-03-lifetime-syntax.html",
    r"https://doc\.rust-lang\.org/cargo/reference/commands/index\.html": "https://doc.rust-lang.org/cargo/commands/cargo.html",
    r"https://doc\.rust-lang\.org/cargo/reference/scripts\.html": "https://doc.rust-lang.org/cargo/reference/unstable.html#script",
    r"https://doc\.rust-lang\.org/reference/allocator-api\.html": "https://doc.rust-lang.org/std/alloc/trait.GlobalAlloc.html",
    r"https://doc\.rust-lang\.org/reference/errors\.html": "https://doc.rust-lang.org/std/result/enum.Result.html",
    r"https://doc\.rust-lang\.org/reference/items/lifetimes\.html": "https://doc.rust-lang.org/reference/items/generics.html",
    r"https://doc\.rust-lang\.org/reference/subtyping-and-variance\.html": "https://doc.rust-lang.org/reference/subtyping.html",
    r"https://doc\.rust-lang\.org/reference/types/pin\.html": "https://doc.rust-lang.org/std/pin/index.html",
    r"https://doc\.rust-lang\.org/reference/unsafe\.html": "https://doc.rust-lang.org/reference/unsafe-blocks.html",
    r"https://rust-lang\.github\.io/rfcs/3894-unnamed-enum-variants\.html": "https://github.com/rust-lang/rust/issues/156628",
    r"https://rust-lang\.github\.io/stable-mir/": "https://github.com/rust-lang/project-stable-mir",
    r"https://rust-lang\.github\.io/rfcs/2632-const-trait-impl\.html": "https://github.com/rust-lang/rust/issues/67792",
    r"https://www\.rust-lang\.org/production": "https://www.rust-lang.org/",
    r"https://rust-lang\.github\.io/rust-project-goals/2026/BorrowSanitizer\.html": "https://rust-lang.github.io/rust-project-goals/2026/borrowsanitizer.html",
}


def main():
    for p in sorted(ROOT.rglob("*.md")):
        text = p.read_text(encoding="utf-8")
        new_text = text
        changed = False
        for pattern, repl in REPLACEMENTS.items():
            new_text, n = re.subn(pattern, repl, new_text)
            if n:
                changed = True
        if changed:
            p.write_text(new_text, encoding="utf-8")
            print(f"fixed: {p.relative_to(ROOT).as_posix()}")


if __name__ == "__main__":
    main()
