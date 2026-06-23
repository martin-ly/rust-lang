#!/usr/bin/env python3
"""修复 concept/ 核心概念页中未带 URL 的来源占位符。

处理范围：concept/01_foundation ~ 07_future（不含 archive）。
仅替换未链接的 `[Text]` 占位符；已带 URL 的保持不变。
"""

import re
import sys
from pathlib import Path
from urllib.parse import quote

ROOT = Path("concept")
TARGET_LAYERS = ["01_foundation", "02_intermediate", "03_advanced", "04_formal", "05_comparative", "06_ecosystem", "07_future"]

TRPL_CHAPTERS = {
    "1": "ch01-00-getting-started",
    "2": "ch02-00-guessing-game-tutorial",
    "3": "ch03-00-common-programming-concepts",
    "3.2": "ch03-02-data-types",
    "4": "ch04-00-ownership",
    "4.1": "ch04-01-what-is-ownership",
    "4.2": "ch04-02-references-and-borrowing",
    "5": "ch05-00-structs",
    "6": "ch06-00-enums-and-pattern-matching",
    "7": "ch07-00-managing-growing-projects-with-packages-crates-and-modules",
    "8": "ch08-00-common-collections",
    "9": "ch09-00-error-handling",
    "9.2": "ch09-02-recoverable-errors-with-result",
    "10": "ch10-00-generic-types-traits-and-lifetimes",
    "10.2": "ch10-02-traits",
    "10.3": "ch10-03-lifetime-syntax",
    "11": "ch11-00-testing",
    "13": "ch13-00-functional-features-of-rust",
    "15": "ch15-00-smart-pointers",
    "15.2": "ch15-02-deref",
    "15.4": "ch15-04-rc",
    "16": "ch16-00-concurrency",
    "16.0": "ch16-00-concurrency",
    "17": "ch17-00-async-await",
    "19": "ch19-00-advanced-features",
    "19.1": "ch19-01-unsafe-rust",
    "19.5": "ch19-05-advanced-functions-and-closures",
    "20": "ch20-00-final-project-a-web-server",
}

RUST_REFERENCE_TOPICS = {
    "ownership": "https://doc.rust-lang.org/reference/",
    "references": "https://doc.rust-lang.org/reference/types/pointer.html#reference-types",
    "reference types": "https://doc.rust-lang.org/reference/types/pointer.html#reference-types",
    "lifetimes": "https://doc.rust-lang.org/reference/lifetime-elision.html",
    "lifetime elision": "https://doc.rust-lang.org/reference/lifetime-elision.html",
    "lifetime elision §the rules": "https://doc.rust-lang.org/reference/lifetime-elision.html#the-rules",
    "types": "https://doc.rust-lang.org/reference/types.html",
    "type layout": "https://doc.rust-lang.org/reference/type-layout.html",
    "type inference": "https://doc.rust-lang.org/reference/statements.html",
    "unions": "https://doc.rust-lang.org/reference/items/unions.html",
    "enums": "https://doc.rust-lang.org/reference/items/enumerations.html",
    "string": "https://doc.rust-lang.org/std/string/struct.String.html",
    "vec": "https://doc.rust-lang.org/std/vec/struct.Vec.html",
    "pin": "https://doc.rust-lang.org/std/pin/struct.Pin.html",
    "waker": "https://doc.rust-lang.org/std/task/struct.Waker.html",
    "manuallydrop": "https://doc.rust-lang.org/std/mem/struct.ManuallyDrop.html",
    "std::mem::forget": "https://doc.rust-lang.org/std/mem/fn.forget.html",
    "send and sync": "https://doc.rust-lang.org/reference/special-types-and-traits.html",
    "trait objects": "https://doc.rust-lang.org/reference/types/trait-object.html",
    "monomorphization": "https://doc.rust-lang.org/reference/items/generics.html",
    "subtyping": "https://doc.rust-lang.org/reference/subtyping.html",
    "macros": "https://doc.rust-lang.org/reference/macros.html",
    "macros by example": "https://doc.rust-lang.org/reference/macros-by-example.html",
    "procedural macros": "https://doc.rust-lang.org/reference/procedural-macros.html",
    "hygiene": "https://doc.rust-lang.org/reference/macros-by-example.html#hygiene",
    "the ? operator": "https://doc.rust-lang.org/reference/expressions/operator-expr.html#the-question-mark-operator",
    "async": "https://doc.rust-lang.org/reference/items/functions.html#async-functions",
    "async fn desugaring": "https://doc.rust-lang.org/reference/items/functions.html#async-functions",
    "behavior considered undefined": "https://doc.rust-lang.org/reference/behavior-considered-undefined.html",
    "safety": "https://doc.rust-lang.org/reference/unsafe-blocks.html",
    "unsafe": "https://doc.rust-lang.org/reference/unsafe-blocks.html",
    "copy": "https://doc.rust-lang.org/reference/special-types-and-traits.html#copy",
    "drop": "https://doc.rust-lang.org/reference/special-types-and-traits.html#drop",
    "deref": "https://doc.rust-lang.org/reference/items/traits.html",
    "asref": "https://doc.rust-lang.org/reference/items/traits.html",
    "interior mutability": "https://doc.rust-lang.org/reference/interior-mutability.html",
    "nll": "https://doc.rust-lang.org/reference/statements.html",
    "const generics": "https://doc.rust-lang.org/reference/items/generics.html#const-generics",
    "inline assembly": "https://doc.rust-lang.org/reference/inline-assembly.html",
    "cfg": "https://doc.rust-lang.org/reference/conditional-compilation.html",
    "attributes": "https://doc.rust-lang.org/reference/attributes.html",
    "extern functions": "https://doc.rust-lang.org/reference/items/external-blocks.html",
    "unsafe blocks": "https://doc.rust-lang.org/reference/unsafe-blocks.html",
    "functions": "https://doc.rust-lang.org/reference/items/functions.html",
    "closures": "https://doc.rust-lang.org/reference/expressions/closure-expr.html",
    "patterns": "https://doc.rust-lang.org/reference/patterns.html",
    "trait upcasting": "https://doc.rust-lang.org/reference/types/trait-object.html",
}

RUSTONOMICON_TOPICS = {
    "what is unsafe?": "https://doc.rust-lang.org/nomicon/what-unsafe-does.html",
    "ffi": "https://doc.rust-lang.org/nomicon/ffi.html",
    "drop flags": "https://doc.rust-lang.org/nomicon/destructors.html",
    "untyped memory": "https://doc.rust-lang.org/nomicon/repr-rust.html",
    "pinning": "https://doc.rust-lang.org/std/pin/struct.Pin.html",
    "concurrency": "https://doc.rust-lang.org/nomicon/concurrency.html",
    "atomics": "https://doc.rust-lang.org/nomicon/atomics.html",
    "ownership": "https://doc.rust-lang.org/nomicon/ownership.html",
    "unions": "https://doc.rust-lang.org/nomicon/other-reprs.html",
}

ASYNC_BOOK_TOPICS = {
    "cancellation": "https://rust-lang.github.io/async-book/part-reference/cancellation.html",
    "waker": "https://rust-lang.github.io/async-book/02_execution/03_wakeups.html",
    "executors": "https://rust-lang.github.io/async-book/02_execution/02_future.html",
    "execution model": "https://rust-lang.github.io/async-book/02_execution/01_chapter.html",
    "streams": "https://rust-lang.github.io/async-book/05_streams/01_chapter.html",
}

RFC_NUMBERS = {
    "1023": "1023-rebalancing-coherence",
    "1566": "1566-proc-macros",
    "1584": "1584-macros-literal-matcher",  # approximate
    "2000": "2000-const-generics",
    "2094": "2094-nll",
    "2289": "2289-associated-type-bounds",
    "2349": "2349-pin",
    "2394": "2394-async_await",
    "243": "0243-trait-based-exception-handling",
    "2484": "2484-trait-from-tryfrom",
    "2585": "2585-unsafe-block-in-unsafe-fn",
    "3185": "3185-cargo-weak-namespaced-features",
    "430": "0430-finalizing-naming-conventions",
}


def trpl_url(chapter: str) -> str:
    slug = TRPL_CHAPTERS.get(chapter, "")
    if slug:
        return f"https://doc.rust-lang.org/book/{slug}.html"
    return "https://doc.rust-lang.org/book/"


def rfc_url(num: str) -> str:
    slug = RFC_NUMBERS.get(num)
    if slug:
        return f"https://rust-lang.github.io/rfcs/{num.rjust(4, '0')}-{slug}.html"
    return f"https://github.com/rust-lang/rfcs/pull/{num}"


def wikipedia_url(topic: str) -> str:
    page = topic.replace(" ", "_").replace("-", "_")
    return f"https://en.wikipedia.org/wiki/{quote(page, safe='/()')}"


def lookup(ref: str) -> str | None:
    ref_norm = ref.strip()
    lowered = ref_norm.lower()

    # Handle "[来源: ...]" / "[学术来源: ...]" wrappers
    source_prefix_match = re.match(r"(?:学术)?来源[:：]\s*(.+)", ref_norm, re.IGNORECASE)
    if source_prefix_match:
        inner = source_prefix_match.group(1).strip()
        inner_repl = lookup(inner)
        if inner_repl:
            # preserve the 来源: prefix and turn the inner placeholder into a link
            return f"来源: {inner_repl}"
        # try to linkify multi-source list separated by / ; · 、 ,
        delim_re = re.compile(r"(\s*[,;·、/]\s*)")
        parts = delim_re.split(inner)
        changed = False
        out = []
        for part in parts:
            repl = lookup(part.strip())
            if repl:
                changed = True
                # repl includes brackets; restore surrounding spaces if part had them
                out.append(repl)
            else:
                out.append(part)
        if changed:
            return f"来源: {''.join(out)}"
        return None

    # TRPL chapters (various notations)
    m = re.match(r"TRPL(?:\s+3rd\s+Ed)?[:\s]*Ch(?:apter)?\.?\s*(\d+(?:\.\d+)?)", ref_norm, re.IGNORECASE)
    if m:
        return f"[{ref_norm}]({trpl_url(m.group(1))})"
    m = re.match(r"TRPL\s+§\s*(\d+(?:\.\d+)?)", ref_norm, re.IGNORECASE)
    if m:
        return f"[{ref_norm}]({trpl_url(m.group(1))})"
    m = re.match(r"TRPL\s*[—–-]\s*(.+)", ref_norm, re.IGNORECASE)
    if m:
        return f"[{ref_norm}](https://doc.rust-lang.org/book/)"
    if lowered in ("trpl", "the rust programming language", "trpl 惯用章节"):
        return "[The Rust Programming Language](https://doc.rust-lang.org/book/)"

    # Rust Reference
    m = re.match(r"Rust\s+Reference[:\s—\-]+(.+)", ref_norm, re.IGNORECASE)
    if m:
        topic = m.group(1).strip().lower().rstrip(".")
        url = RUST_REFERENCE_TOPICS.get(topic, "https://doc.rust-lang.org/reference/")
        return f"[{ref_norm}]({url})"
    m = re.match(r"Rust\s+Reference\s+§\s*(.+)", ref_norm, re.IGNORECASE)
    if m:
        return f"[{ref_norm}](https://doc.rust-lang.org/reference/)"
    if lowered == "rust reference" or lowered == "rust reference §4.2.1":
        return "[Rust Reference](https://doc.rust-lang.org/reference/)"

    # Rustonomicon (also accept "The Rustonomicon")
    m = re.match(r"(?:The\s+)?Rustonomicon[:\s—\-]+(.+)", ref_norm, re.IGNORECASE)
    if m:
        topic = m.group(1).strip().lower().rstrip(".")
        url = RUSTONOMICON_TOPICS.get(topic, "https://doc.rust-lang.org/nomicon/")
        return f"[{ref_norm}]({url})"
    m = re.match(r"(?:The\s+)?Rustonomicon\s+§\s*(.+)", ref_norm, re.IGNORECASE)
    if m:
        return f"[{ref_norm}](https://doc.rust-lang.org/nomicon/)"
    if lowered in ("rustonomicon", "the rustonomicon"):
        return "[Rustonomicon](https://doc.rust-lang.org/nomicon/)"

    # Async Book
    m = re.match(r"(?:Rust\s+)?Async\s+Book[:\s—\-]+(.+)", ref_norm, re.IGNORECASE)
    if m:
        topic = m.group(1).strip().lower().rstrip(".")
        url = ASYNC_BOOK_TOPICS.get(topic, "https://rust-lang.github.io/async-book/")
        return f"[{ref_norm}]({url})"
    if lowered in ("async book", "rust async book"):
        return "[The Rust Async Book](https://rust-lang.github.io/async-book/)"

    # Cargo Book
    if re.match(r"Cargo\s+Book", ref_norm, re.IGNORECASE):
        return "[The Cargo Book](https://doc.rust-lang.org/cargo/)"

    # Rust API Guidelines
    if re.match(r"Rust\s+API\s+Guidelines", ref_norm, re.IGNORECASE):
        return "[Rust API Guidelines](https://rust-lang.github.io/api-guidelines/)"

    # Rust By Example
    if lowered == "rust by example":
        return "[Rust By Example](https://doc.rust-lang.org/rust-by-example/)"

    # Miri Book
    if re.match(r"Miri\s+Book", ref_norm, re.IGNORECASE):
        return "[Miri Book](https://github.com/rust-lang/miri)"
    if re.match(r"Miri:\s*Tree\s+Borrows", ref_norm, re.IGNORECASE):
        return "[Miri: Tree Borrows](https://github.com/rust-lang/miri)"

    # Brown / Google
    if lowered == "brown university interactive book":
        return "[Brown University Interactive Rust Book](https://rust-book.cs.brown.edu/)"
    if lowered == "google comprehensive rust":
        return "[Google Comprehensive Rust](https://google.github.io/comprehensive-rust/)"

    # RFCs (also "Rust RFC NNNN")
    m = re.match(r"(?:Rust\s+)?RFC\s*#?(\d+)(?::\s*(.+))?", ref_norm, re.IGNORECASE)
    if m:
        num = m.group(1)
        return f"[{ref_norm}]({rfc_url(num)})"
    if re.match(r"RFC:\s*(.+)", ref_norm, re.IGNORECASE):
        return "[Rust RFCs](https://github.com/rust-lang/rfcs)"
    if re.match(r"Rust\s+RFC:\s*\D", ref_norm, re.IGNORECASE):
        return "[Rust RFCs](https://github.com/rust-lang/rfcs)"
    if lowered == "rfc 流程" or lowered == "rust rfcs repo" or lowered.startswith("rfc 流程"):
        return "[Rust RFCs](https://github.com/rust-lang/rfcs)"

    # Wikipedia (colon / hyphen / en-dash / em-dash)
    m = re.match(r"Wikipedia\s*[:\-—–]\s*(.+)", ref_norm, re.IGNORECASE)
    if m:
        topic = m.group(1).strip()
        return f"[{ref_norm}]({wikipedia_url(topic)})"
    if lowered == "wikipedia":
        return "[Wikipedia](https://en.wikipedia.org/wiki/Main_Page)"

    # RustBelt
    if re.match(r"RustBelt(?::\s*POPL\s*2018)?", ref_norm, re.IGNORECASE):
        return "[RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/)"
    if re.match(r"RustBelt\s*POPL\s*2018", ref_norm, re.IGNORECASE):
        return "[RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/)"
    if re.match(r"RustBelt\s*POPL\s*2017", ref_norm, re.IGNORECASE):
        return "[RustBelt](https://plv.mpi-sws.org/rustbelt/)"
    if re.match(r"(?:ETH\s+)?RustBelt", ref_norm, re.IGNORECASE):
        return "[RustBelt](https://plv.mpi-sws.org/rustbelt/)"
    if re.match(r"ETH\s+Zurich:\s*RustBelt\s+Project", ref_norm, re.IGNORECASE):
        return "[RustBelt](https://plv.mpi-sws.org/rustbelt/)"
    if lowered == "rustbelt":
        return "[RustBelt](https://plv.mpi-sws.org/rustbelt/)"

    # Borrows
    if re.match(r"Tree\s+Borrows", ref_norm, re.IGNORECASE):
        return "[Tree Borrows — PLDI 2025](https://perso.crans.org/vanille/treebor/)"
    if re.match(r"Stacked\s+Borrows", ref_norm, re.IGNORECASE):
        return "[Stacked Borrows](https://plv.mpi-sws.org/rustbelt/stacked-borrows/)"
    if re.match(r"Jung\s+et\s+al\.\s*.*Stacked\s+Borrows", ref_norm, re.IGNORECASE):
        return "[Stacked Borrows — POPL 2021](https://plv.mpi-sws.org/rustbelt/stacked-borrows/)"

    # Project Goals
    if re.match(r"(?:Rust\s+)?Project\s+Goals\s+2026", ref_norm, re.IGNORECASE):
        return "[Rust Project Goals 2026](https://rust-lang.github.io/rust-project-goals/2026/)"
    if re.match(r"Rust\s+Project\s+Goals\s+2025H1", ref_norm, re.IGNORECASE):
        return "[Rust Project Goals 2025H1](https://rust-lang.github.io/rust-project-goals/2025h1/)"
    if re.match(r"Rust\s+Project\s+Goals\s+Update", ref_norm, re.IGNORECASE):
        return "[Rust Project Goals Update](https://rust-lang.github.io/rust-project-goals/)"

    # Rust RFCs repo / generic references
    if re.match(r"Rust\s+RFCs(?:\s+-\s+github\.com/rust-lang/rfcs)?", ref_norm, re.IGNORECASE):
        return "[Rust RFCs](https://github.com/rust-lang/rfcs)"
    if lowered == "the rust programming language (trpl)":
        return "[The Rust Programming Language](https://doc.rust-lang.org/book/)"

    # POPL 2018 / RustBelt citations
    if re.match(r"POPL\s+2018\s*[-–—]?\s*RustBelt", ref_norm, re.IGNORECASE):
        return "[RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/)"
    if re.match(r"Jung\s+et\s+al\.,?\s*\*?RustBelt", ref_norm, re.IGNORECASE):
        return "[RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/)"
    if re.match(r"Jung\s+et\s+al\.\s+2017\s+POPL", ref_norm, re.IGNORECASE):
        return "[RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/)"

    # Miri / Tree Borrows citations
    if re.match(r"Miri\s*[-–—]\s*Tree\s+Borrows", ref_norm, re.IGNORECASE):
        return "[Miri Tree Borrows](https://github.com/rust-lang/miri)"
    if re.match(r"Ralf\s+Jung\s+et\s+al\.,?\s*.*Stacked\s+Borrows", ref_norm, re.IGNORECASE):
        return "[Stacked Borrows — POPL 2021](https://plv.mpi-sws.org/rustbelt/stacked-borrows/)"
    if re.match(r"Ralf\s+Jung,\s*.*Tree\s+Borrows", ref_norm, re.IGNORECASE):
        return "[Tree Borrows](https://perso.crans.org/vanille/treebor/)"
    if re.match(r"Pichon-Pharabod\s+&\s+Dreyer,\s*.*Tree\s+Borrows", ref_norm, re.IGNORECASE):
        return "[Tree Borrows — PLDI 2025](https://perso.crans.org/vanille/treebor/)"

    # Rust Blog / Lang Team Blog
    if re.match(r"Rust\s+Blog\s*[—–-]\s*Project\s+Goals\s+Update", ref_norm, re.IGNORECASE):
        return "[Rust Blog](https://blog.rust-lang.org/)"
    if re.match(r"Lang\s+Team\s+Blog", ref_norm, re.IGNORECASE):
        return "[Lang Team Blog](https://lang-team.rust-lang.org/)"

    # Slash-separated source pairs, e.g. "Stacked/Tree Borrows", "λRust / RustBelt"
    if "/" in ref_norm:
        parts = [p.strip() for p in ref_norm.split("/")]
        mapped = []
        changed = False
        for p in parts:
            r = lookup(p)
            if r:
                changed = True
                mapped.append(r)
            else:
                mapped.append(p)
        if changed:
            return " / ".join(mapped)

    return None


PATTERN = re.compile(r"\[([^\]]+)\](?!\()")

# Handle nested `[来源: [Text]]` where inner Text is a known source placeholder
NESTED_SOURCE_PAT = re.compile(
    r"\[(?:学术)?来源[:：]\s*\[([A-Za-z0-9\s\-—–/]+?)\]\]",
    re.IGNORECASE,
)


def process_file(text: str) -> tuple[str, int, list[str]]:
    unknown = []
    actual = 0

    def repl(m):
        nonlocal actual
        ref = m.group(1)
        replacement = lookup(ref)
        if replacement:
            actual += 1
            return replacement
        # unknown source-like placeholder
        if ref.startswith("来源类型:") or ref.startswith("来源类型："):
            return m.group(0)
        if any(k in ref for k in ["TRPL", "Rust Reference", "Rustonomicon", "RFC", "Wikipedia", "RustBelt", "Tree Borrows", "Stacked Borrows", "Cargo Book", "Async Book", "Miri Book", "Rust API Guidelines", "Brown University", "Google Comprehensive", "Project Goals"]):
            unknown.append(ref)
        return m.group(0)

    # Nested source brackets pass
    def nested_repl(m):
        nonlocal actual
        inner = m.group(1).strip()
        repl = lookup(inner)
        if repl:
            actual += 1
            return f"[来源: {repl}]"
        return m.group(0)

    text = NESTED_SOURCE_PAT.sub(nested_repl, text)
    new_text = PATTERN.sub(repl, text)
    return new_text, actual, unknown


def main():
    dry_run = "--dry-run" in sys.argv
    total_files = 0
    total_repl = 0
    unknown_all = []
    for layer in TARGET_LAYERS:
        layer_dir = ROOT / layer
        if not layer_dir.exists():
            continue
        for p in sorted(layer_dir.rglob("*.md")):
            if "archive" in p.parts:
                continue
            text = p.read_text(encoding="utf-8", errors="ignore")
            new_text, n, unknown = process_file(text)
            if n:
                total_files += 1
                total_repl += n
                unknown_all.extend(unknown)
                if dry_run:
                    print(f"[dry-run] {p}: {n} replacements")
                else:
                    p.write_text(new_text, encoding="utf-8")
                    print(f"updated: {p}: {n} replacements")

    print(f"\n{'[dry-run] ' if dry_run else ''}Total: {total_files} files, {total_repl} replacements")
    if unknown_all:
        print(f"\nUnknown placeholders ({len(unknown_all)}):")
        for u in sorted(set(unknown_all)):
            print(f"  - {u}")


if __name__ == "__main__":
    main()
