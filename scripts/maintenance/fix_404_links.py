#!/usr/bin/env python3
"""Fix known 404/broken external links across active documentation."""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
SELF_PATH = Path(__file__).resolve()

# Map: old URL -> new URL
# NOTE: list longer/more-specific URLs before shorter ones to avoid partial matches.
REPLACEMENTS = {
    # RFC 1584 slug correction
    "https://rust-lang.github.io/rfcs/1584-macros-literal-matcher.html":
        "https://rust-lang.github.io/rfcs/1584-macros.html",
    # Rust Reference pages removed/merged
    "https://doc.rust-lang.org/reference/type-inference.html":
        "https://doc.rust-lang.org/reference/statements.html",
    "https://doc.rust-lang.org/reference/nll.html":
        "https://doc.rust-lang.org/reference/statements.html",
    # Rust for Linux safety-standard subpage does not exist
    "https://rust-for-linux.com/safety-standard":
        "https://rust-for-linux.com/",
    # Async Book rewrite moved cancellation chapter
    "https://rust-lang.github.io/async-book/03_async_await/02_cancellation.html":
        "https://rust-lang.github.io/async-book/part-reference/cancellation.html",
    # Rust Design Patterns moved to rust-unofficial org
    "https://rust-lang.github.io/design-patterns/":
        "https://rust-unofficial.github.io/patterns/",
    # Rust production page removed; link to official homepage as fallback
    "https://www.rust-lang.org/production/users":
        "https://www.rust-lang.org/",
    "https://www.rust-lang.org/production":
        "https://www.rust-lang.org/",
    # Fix botched intermediate state from earlier runs
    "https://www.rust-lang.org//users":
        "https://www.rust-lang.org/",
    # TRPL chapter slugs changed in recent editions
    "https://doc.rust-lang.org/book/ch10-00-generic-types-traits-and-lifetimes.html":
        "https://doc.rust-lang.org/book/ch10-00-generics.html",
    "https://doc.rust-lang.org/book/ch06-00-enums-and-pattern-matching.html":
        "https://doc.rust-lang.org/book/ch06-00-enums.html",
    "https://doc.rust-lang.org/book/ch04-00-ownership.html":
        "https://doc.rust-lang.org/book/ch04-01-what-is-ownership.html",
    # Rust Edition Guide 2024 path fixes
    "https://doc.rust-lang.org/edition-guide/rust-2024/precise-capturing.html":
        "https://doc.rust-lang.org/edition-guide/rust-2024/rpit-lifetime-capture.html",
    "https://doc.rust-lang.org/edition-guide/rust-2024/unsafe-attribute.html":
        "https://doc.rust-lang.org/edition-guide/rust-2024/unsafe-attributes.html",
    "https://doc.rust-lang.org/edition-guide/rust-2024/unsafe-extern-blocks.html":
        "https://doc.rust-lang.org/edition-guide/rust-2024/unsafe-extern.html",
    # Rustonomicon pages merged/renamed
    "https://doc.rust-lang.org/nomicon/pin.html":
        "https://doc.rust-lang.org/std/pin/struct.Pin.html",
    "https://doc.rust-lang.org/nomicon/unions.html":
        "https://doc.rust-lang.org/nomicon/other-reprs.html",
}

# Regex replacements for RFC duplicate slugs like /rfcs/0243-0243-... -> /rfcs/0243-...
RFC_DUPLICATE_RE = re.compile(
    r"https://rust-lang\.github\.io/rfcs/(\d{4})-\1-([^/\s\"]+)",
    flags=re.IGNORECASE,
)

EXCLUDE_DIRS = {
    ".git",
    "target",
    "node_modules",
    "__pycache__",
}


def should_process(path: Path) -> bool:
    if path.suffix.lower() not in {".md", ".rs", ".toml", ".py", ".json", ".yaml", ".yml"}:
        return False
    for part in path.parts:
        if part in EXCLUDE_DIRS:
            return False
    return True


def fix_text(text: str) -> tuple[str, bool]:
    new_text = text
    changed = False

    # Explicit URL replacements
    for old, new in REPLACEMENTS.items():
        if old in new_text:
            new_text = new_text.replace(old, new)
            changed = True

    # RFC duplicate slug normalization
    def _rfc_repl(m: re.Match) -> str:
        return f"https://rust-lang.github.io/rfcs/{m.group(1)}-{m.group(2)}"

    new_text, n = RFC_DUPLICATE_RE.subn(_rfc_repl, new_text)
    if n:
        changed = True

    return new_text, changed


def main() -> None:
    changed_files = set()
    for p in ROOT.rglob("*"):
        if not p.is_file() or not should_process(p):
            continue
        if p.resolve() == SELF_PATH:
            continue
        try:
            text = p.read_text(encoding="utf-8")
        except Exception:
            continue
        new_text, changed = fix_text(text)
        if changed:
            p.write_text(new_text, encoding="utf-8")
            changed_files.add(p.relative_to(ROOT))

    if changed_files:
        print("Updated files:")
        for f in sorted(changed_files):
            print(f"  {f}")
    else:
        print("No replacements needed.")


if __name__ == "__main__":
    main()
