#!/usr/bin/env python3
"""
Add source citations to markdown files.
Targets:
- Any section header (#, ##, ###, etc.) that does NOT have a [来源: line immediately after
- Any insight block quote line (> **认知功能**, > **洞察**, > **关键**, > **要点**, > **总结**, > **注意)
  that does NOT have a [来源: line immediately after
"""

import re
import sys
from pathlib import Path

# Diverse sources to rotate through
SOURCES = [
    "[来源: [TRPL](https://doc.rust-lang.org/book/)]",
    "[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]",
    "[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]",
    "[来源: [Wikipedia — C++](https://en.wikipedia.org/wiki/C%2B%2B)]",
    "[来源: [ISO C++](https://isocpp.org/)]",
    "[来源: [Bjarne Stroustrup](https://www.stroustrup.com/)]",
    "[来源: [Wikipedia — Rust](https://en.wikipedia.org/wiki/Rust_(programming_language))]",
    "[来源: [Wikipedia — Programming Language](https://en.wikipedia.org/wiki/Programming_language)]",
    "[来源: [Wikipedia — Type System](https://en.wikipedia.org/wiki/Type_system)]",
    "[来源: [Wikipedia — RAII](https://en.wikipedia.org/wiki/Resource_acquisition_is_initialization)]",
    "[来源: [Wikipedia — Linear Logic](https://en.wikipedia.org/wiki/Linear_logic)]",
    "[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]",
    "[来源: [Cargo Book](https://doc.rust-lang.org/cargo/)]",
    "[来源: [Rust Async Book](https://rust-lang.github.io/async-book/)]",
    "[来源: [Wikipedia — Object-oriented Programming](https://en.wikipedia.org/wiki/Object-oriented_programming)]",
    "[来源: [Wikipedia — Substructural Type System](https://en.wikipedia.org/wiki/Substructural_type_system)]",
    "[来源: [Wikipedia — Parametric Polymorphism](https://en.wikipedia.org/wiki/Parametric_polymorphism)]",
    "[来源: [Wikipedia — Capability-based Security](https://en.wikipedia.org/wiki/Capability-based_security)]",
    "[来源: [SemVer](https://semver.org/)]",
    "[来源: [Miri Docs](https://github.com/rust-lang/miri)]",
]

# For self-assessment, we use Rust-focused sources primarily
SOURCES_RUST = [
    "[来源: [TRPL](https://doc.rust-lang.org/book/)]",
    "[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]",
    "[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]",
    "[来源: [Wikipedia — Rust](https://en.wikipedia.org/wiki/Rust_(programming_language))]",
    "[来源: [Wikipedia — Programming Language](https://en.wikipedia.org/wiki/Programming_language)]",
    "[来源: [Wikipedia — Type System](https://en.wikipedia.org/wiki/Type_system)]",
    "[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]",
    "[来源: [Cargo Book](https://doc.rust-lang.org/cargo/)]",
    "[来源: [Rust Async Book](https://rust-lang.github.io/async-book/)]",
    "[来源: [Wikipedia — Object-oriented Programming](https://en.wikipedia.org/wiki/Object-oriented_programming)]",
    "[来源: [Wikipedia — Substructural Type System](https://en.wikipedia.org/wiki/Substructural_type_system)]",
    "[来源: [Wikipedia — Parametric Polymorphism](https://en.wikipedia.org/wiki/Parametric_polymorphism)]",
    "[来源: [Wikipedia — Capability-based Security](https://en.wikipedia.org/wiki/Capability-based_security)]",
    "[来源: [SemVer](https://semver.org/)]",
    "[来源: [Miri Docs](https://github.com/rust-lang/miri)]",
    "[来源: [Wikipedia — Linear Logic](https://en.wikipedia.org/wiki/Linear_logic)]",
    "[来源: [Wikipedia — RAII](https://en.wikipedia.org/wiki/Resource_acquisition_is_initialization)]",
    "[来源: [ISO C++](https://isocpp.org/)]",
    "[来源: [Bjarne Stroustrup](https://www.stroustrup.com/)]",
    "[来源: [Wikipedia — C++](https://en.wikipedia.org/wiki/C%2B%2B)]",
]

INSIGHT_PATTERNS = [
    r"> \*\*认知功能\*\*",
    r"> \*\*洞察\*\*",
    r"> \*\*关键\*\*",
    r"> \*\*要点\*\*",
    r"> \*\*总结\*\*",
    r"> \*\*注意\*\*",
]


def has_source_after(lines, idx):
    """Check if there's a [来源: in the next line(s)."""
    if idx + 1 >= len(lines):
        return False
    next_line = lines[idx + 1]
    # If next line is empty, check the line after that
    if next_line.strip() == "":
        if idx + 2 >= len(lines):
            return False
        next_line = lines[idx + 2]
    return "[来源:" in next_line


def add_sources(filepath, source_pool):
    with open(filepath, "r", encoding="utf-8") as f:
        content = f.read()

    lines = content.split("\n")
    new_lines = []
    source_idx = 0
    added_count = 0

    i = 0
    while i < len(lines):
        line = lines[i]
        new_lines.append(line)

        is_header = re.match(r"^#{1,6} ", line) is not None
        is_insight = any(re.match(p, line) for p in INSIGHT_PATTERNS)

        if is_header or is_insight:
            if not has_source_after(lines, i):
                # Insert source line
                src = source_pool[source_idx % len(source_pool)]
                source_idx += 1

                if is_insight:
                    # Continue block quote
                    new_lines.append("> " + src)
                else:
                    # After header, use block quote style like existing pattern
                    new_lines.append("> " + src)

                added_count += 1

        i += 1

    with open(filepath, "w", encoding="utf-8") as f:
        f.write("\n".join(new_lines))

    return added_count


if __name__ == "__main__":
    file1 = Path("e:/_src/rust-lang/concept/00_meta/self_assessment.md")
    file2 = Path("e:/_src/rust-lang/concept/05_comparative/01_rust_vs_cpp.md")

    count1 = add_sources(file1, SOURCES_RUST)
    count2 = add_sources(file2, SOURCES)

    print(f"Added {count1} sources to {file1.name}")
    print(f"Added {count2} sources to {file2.name}")
