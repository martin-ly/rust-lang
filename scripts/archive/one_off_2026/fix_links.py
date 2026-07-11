#!/usr/bin/env python3
"""Fix broken or mislabeled authoritative links in the upgraded cheatsheets."""

from pathlib import Path

ROOT = Path("e:/_src/rust-lang/docs/research_notes")

REPLACEMENTS = {
    "10_quick_reference.md": [
        # Broken Reference ownership link -> Memory model lifetime section
        (
            "- [Reference - Ownership](https://doc.rust-lang.org/reference/ownership.html)",
            "- [Reference - Memory allocation and lifetime](https://doc.rust-lang.org/reference/memory-model.html#memory-allocation-and-lifetime)",
        ),
    ],
    "10_quick_find.md": [
        (
            "- [Reference - Ownership](https://doc.rust-lang.org/reference/ownership.html)",
            "- [Reference - Memory allocation and lifetime](https://doc.rust-lang.org/reference/memory-model.html#memory-allocation-and-lifetime)",
        ),
    ],
    "10_concurrency_cheatsheet.md": [
        # Wrong RFC numbers/labels -> correct ones
        (
            "- [RFC 803 - Send / Sync](https://rust-lang.github.io/rfcs/0803-type-ascription.html)",
            "- [RFC 0458 - Send trait improvements](https://rust-lang.github.io/rfcs/0458-send-improvements.html)",
        ),
        (
            "- [RFC 1506 - Closures / Fn* traits](https://rust-lang.github.io/rfcs/1506-adt-kinds.html)",
            "- [RFC 1543 - Integer atomics](https://rust-lang.github.io/rfcs/1543-integer_atomics.html)",
        ),
        # Add more concurrency RFCs after Miri
        (
            "- [Miri README](https://github.com/rust-lang/miri/blob/master/README.md)\n",
            "- [Miri README](https://github.com/rust-lang/miri/blob/master/README.md)\n- [RFC 2394 - async/await](https://rust-lang.github.io/rfcs/2394-async_await.html)\n- [RFC 3151 - Scoped threads](https://rust-lang.github.io/rfcs/3151-scoped-threads.html)\n",
        ),
    ],
    "10_error_handling_cheatsheet.md": [
        # RFC 2504 is actually "fix-error" (Error trait improvements), not Try trait
        (
            "- [RFC 2504 - Try Trait / `?`](https://rust-lang.github.io/rfcs/2504-try-trait.html)",
            "- [RFC 2504 - Error trait improvements (source / backtrace)](https://rust-lang.github.io/rfcs/2504-fix-error.html)\n- [RFC 1859 - Try trait / `?` operator](https://rust-lang.github.io/rfcs/1859-try-trait.html)",
        ),
    ],
}


def main() -> None:
    for filename, reps in REPLACEMENTS.items():
        path = ROOT / filename
        text = path.read_text(encoding="utf-8")
        for old, new in reps:
            if old in text:
                text = text.replace(old, new, 1)
            else:
                print(f"  [warn] pattern not found in {filename}: {old[:60]}...")
        path.write_text(text, encoding="utf-8")
        print(f"Fixed links in {filename}")


if __name__ == "__main__":
    main()
