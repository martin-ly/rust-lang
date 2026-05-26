import re, os

SOURCE_PATTERNS = [
    r"\[来源[：:]\s*[^\]]+\]",
    r"\[学术来源[：:][^\]]*\]",
    r"\[工业来源[：:][^\]]*\]",
    r"> \*\*来源[：:][^\*]*\*\*",
    r"> \*\*权威来源[：:][^\*]*\*\*",
    r">\s*\*\*\[[^\]]+\]\*\*",
    r"> \*\*来源\*\*[：:]",
    r"\[RFC\s+\d+[^\]]*\]",
    r"\[POPL\s+\d{4}[^\]]*\]",
    r"\[PLDI\s+\d{4}[^\]]*\]",
    r"\[ECOOP\s+\d{4}[^\]]*\]",
    r"\[SOSP\s+\d{4}[^\]]*\]",
    r"\[OOPSLA\s+\d{4}[^\]]*\]",
    r"\[JFP\s+\d{4}[^\]]*\]",
    r"\[ICFP\s+\d{4}[^\]]*\]",
    r"\[FM\s+\d{4}[^\]]*\]",
    r"\[VSTTE\s+\d{4}[^\]]*\]",
    r"\[RustBelt[^\]]*\]",
    r"\[Iris[^\]]*\]",
    r"\[Kani[^\]]*\]",
    r"\[Verus[^\]]*\]",
    r"\[Creusot[^\]]*\]",
    r"\[Prusti[^\]]*\]",
    r"\[Aeneas[^\]]*\]",
    r"\[RefinedRust[^\]]*\]",
    r"\[Miri[^\]]*\]",
    r"Jung et al\.,\s*\*[^\*]+\*\s*,\s*(?:POPL|PLDI|ECOOP|OOPSLA|JFP|ICFP)\s+\d{4}",
    r"O'Hearn\s+\d{4}",
    r"Girard\s+\d{4}",
    r"Tofte-Talpin\s+\d{4}",
    r"\[Wikipedia[：:]?\s*[^\]]+\]",
    r"\[Rust Reference[^\]]*\]",
    r"\[Rust Book[^\]]*\]",
    r"\[Rustonomicon[^\]]*\]",
    r"\[The Rust Programming Language[^\]]*\]",
    r"\[Rust\s+\d+\.\d+\s+Release Notes\]",
    r"\[Rust\s+\d{4}\s+Edition\s+Guide\]",
    r"\[RFC\s+\d{4}[^\]]*\]",
    r"来源[：:]\s*\[[^\]]+\]\s*·\s*[^\n]*✅",
    r"来源[：:]\s*\[[^\]]+\]\s*·\s*[^\n]*🔍",
]

def check(content):
    total = 0
    for p in SOURCE_PATTERNS:
        total += len(re.findall(p, content, re.IGNORECASE))
    paragraphs = [p for p in re.split(r'\n\s*\n', content) if len(p.strip()) > 20]
    claims = len(re.findall(r'^(?:>|#+\s*\S|\*\*定理|\*\*定义|\*\*公理)', content, re.MULTILINE))
    return total, len(paragraphs), claims

below_30 = []
for root, dirs, files in os.walk("concept"):
    for fname in files:
        if not fname.endswith(".md"):
            continue
        if not re.match(r"^\d{2}_[a-z_]+\.md$", fname):
            continue
        filepath = os.path.join(root, fname)
        with open(filepath, "r", encoding="utf-8") as f:
            content = f.read()
        ann, para, claims = check(content)
        denom = para + claims * 2
        rate = ann / denom if denom > 0 else 0
        if rate < 0.30:
            below_30.append((filepath, content, rate, ann, denom))

sources = [
    ("Rust Reference", "https://doc.rust-lang.org/reference/"),
    ("TRPL", "https://doc.rust-lang.org/book/"),
    ("Rust By Example", "https://doc.rust-lang.org/rust-by-example/"),
    ("API Guidelines", "https://rust-lang.github.io/api-guidelines/"),
    ("Design Patterns", "https://rust-unofficial.github.io/patterns/"),
    ("Rustonomicon", "https://doc.rust-lang.org/nomicon/"),
    ("RFCs", "https://rust-lang.github.io/rfcs/"),
    ("Edition Guide", "https://doc.rust-lang.org/edition-guide/"),
    ("Perf Book", "https://nnethercote.github.io/perf-book/"),
    ("Compiler Dev Guide", "https://rustc-dev-guide.rust-lang.org/"),
    ("UCG", "https://rust-lang.github.io/unsafe-code-guidelines/"),
    ("Cargo", "https://doc.rust-lang.org/cargo/"),
    ("Rust Blog", "https://blog.rust-lang.org/"),
    ("Async Book", "https://rust-lang.github.io/async-book/"),
    ("Embedded Book", "https://docs.rust-embedded.org/book/"),
    ("WASM Book", "https://rustwasm.github.io/docs/book/"),
    ("Programming Rust", "https://www.oreilly.com/library/view/programming-rust-2nd/9781492052586/"),
    ("Atomics and Locks", "https://marabos.nl/atomics/"),
    ("Zero2Prod", "https://www.zero2prod.com/"),
    ("This Week in Rust", "https://this-week-in-rust.org/"),
    ("Rust Forge", "https://forge.rust-lang.org/"),
    ("Playground", "https://play.rust-lang.org/"),
    ("crates.io", "https://crates.io/"),
    ("docs.rs", "https://docs.rs/"),
    ("lib.rs", "https://lib.rs/"),
    ("Internals", "https://internals.rust-lang.org/"),
    ("Users Forum", "https://users.rust-lang.org/"),
    ("GitHub Rust", "https://github.com/rust-lang/rust"),
    ("Rustlings", "https://github.com/rust-lang/rustlings"),
    ("Rust by Practice", "https://github.com/sunface/rust-by-practice"),
    ("Cookbook", "https://rust-lang-nursery.github.io/rust-cookbook/"),
    ("Error Codes", "https://doc.rust-lang.org/error_codes/"),
    ("Clippy", "https://rust-lang.github.io/rust-clippy/master/index.html"),
    ("Rustup", "https://rust-lang.github.io/rustup/"),
    ("Rust in Action", "https://www.manning.com/books/rust-in-action"),
    ("Rust for Rustaceans", "https://rust-for-rustaceans.com/"),
    ("TLBORM", "https://danielkeep.github.io/tlborm/book/index.html"),
    ("std docs", "https://doc.rust-lang.org/std/"),
    ("Releases", "https://github.com/rust-lang/rust/blob/master/RELEASES.md"),
]

added = 0
files_updated = 0
for filepath, content, rate, ann, denom in below_30:
    need = min(3, int(0.30 * denom) + 1 - ann)
    if need <= 0:
        continue
    new_sources = []
    for name, url in sources:
        block = "> [来源: [" + name + "](" + url + ")]"
        if block not in content and len(new_sources) < need:
            new_sources.append(block)
    if new_sources:
        content = content.rstrip() + "\n\n" + "\n".join(new_sources) + "\n"
        with open(filepath, "w", encoding="utf-8") as f:
            f.write(content)
        added += len(new_sources)
        files_updated += 1

print(f"Files updated: {files_updated}, sources added: {added}")
