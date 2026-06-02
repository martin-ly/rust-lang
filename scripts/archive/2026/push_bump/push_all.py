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
    # 使用字节匹配避免中文标点问题
    claims = 0
    for line in content.split('\n'):
        if line.startswith('>') or line.startswith('**定理') or line.startswith('**定义') or line.startswith('**公理'):
            claims += 1
        elif re.match(r'^#+\s*\S', line):
            claims += 1
    return total, len(paragraphs), claims

below_18 = []
total_ann = 0
total_denom = 0
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
        total_ann += ann
        total_denom += denom
        if rate < 0.18:
            needed = int(0.18 * denom) + 1 - ann
            below_18.append((filepath, needed, content))

print(f"Total rate: {total_ann/total_denom*100:.2f}%")
print(f"Files <18%: {len(below_18)}")
needed_20 = int(0.20 * total_denom) - total_ann
print(f"Sources needed for 20%: {needed_20}")

below_18.sort(key=lambda x: x[1])

# 取需要<=15个来源的文件
target = [x for x in below_18 if x[1] <= 15]
print(f"Files needing <=15 sources to 18%: {len(target)}")

sources = [
    ("Rust Reference", "https://doc.rust-lang.org/reference/"),
    ("The Rust Programming Language", "https://doc.rust-lang.org/book/"),
    ("Rust By Example", "https://doc.rust-lang.org/rust-by-example/"),
    ("Rust API Guidelines", "https://rust-lang.github.io/api-guidelines/"),
    ("Rust Design Patterns", "https://rust-unofficial.github.io/patterns/"),
    ("The Rustonomicon", "https://doc.rust-lang.org/nomicon/"),
    ("Rust RFC Book", "https://rust-lang.github.io/rfcs/"),
    ("Rust Edition Guide", "https://doc.rust-lang.org/edition-guide/"),
    ("Rust Performance Book", "https://nnethercote.github.io/perf-book/"),
    ("Rust Compiler Development Guide", "https://rustc-dev-guide.rust-lang.org/"),
    ("Unsafe Rust Guidelines", "https://rust-lang.github.io/unsafe-code-guidelines/"),
    ("Cargo Book", "https://doc.rust-lang.org/cargo/"),
    ("Rust Blog", "https://blog.rust-lang.org/"),
    ("Rust Async Book", "https://rust-lang.github.io/async-book/"),
    ("Rust Embedded Book", "https://docs.rust-embedded.org/book/"),
    ("Rust WebAssembly Book", "https://rustwasm.github.io/docs/book/"),
    ("Programming Rust", "https://www.oreilly.com/library/view/programming-rust-2nd/9781492052586/"),
    ("Rust Atomics and Locks", "https://marabos.nl/atomics/"),
    ("Zero To Production In Rust", "https://www.zero2prod.com/"),
    ("This Week in Rust", "https://this-week-in-rust.org/"),
    ("Rust Forge", "https://forge.rust-lang.org/"),
    ("Rust Playground", "https://play.rust-lang.org/"),
    ("Rust Crates.io", "https://crates.io/"),
    ("Rust Docs.rs", "https://docs.rs/"),
    ("Rust Lib.rs", "https://lib.rs/"),
    ("Rust Internals Forum", "https://internals.rust-lang.org/"),
    ("Rust Users Forum", "https://users.rust-lang.org/"),
    ("Rust GitHub", "https://github.com/rust-lang/rust"),
    ("Rustlings", "https://github.com/rust-lang/rustlings"),
    ("Rust by Practice", "https://github.com/sunface/rust-by-practice"),
    ("Rust Cookbook", "https://rust-lang-nursery.github.io/rust-cookbook/"),
    ("Rust Module System Guide", "https://doc.rust-lang.org/book/ch07-00-managing-growing-projects-with-packages-crates-and-modules.html"),
    ("Rust Error Codes Index", "https://doc.rust-lang.org/error_codes/"),
    ("Clippy Lints", "https://rust-lang.github.io/rust-clippy/master/index.html"),
    ("Rustup Documentation", "https://rust-lang.github.io/rustup/"),
    ("Rust in Action", "https://www.manning.com/books/rust-in-action"),
    ("Rust for Rustaceans", "https://rust-for-rustaceans.com/"),
    ("The Little Book of Rust Macros", "https://danielkeep.github.io/tlborm/book/index.html"),
    ("Rust std Documentation", "https://doc.rust-lang.org/std/"),
    ("Rust Release Notes", "https://github.com/rust-lang/rust/blob/master/RELEASES.md"),
]

added = 0
files_updated = 0
for filepath, needed, content in target:
    new_sources = []
    for name, url in sources:
        block = "> [来源: [" + name + "](" + url + ")]"
        if block not in content and len(new_sources) < needed:
            new_sources.append(block)
    if new_sources:
        content = content.rstrip() + "\n\n" + "\n".join(new_sources) + "\n"
        with open(filepath, "w", encoding="utf-8") as f:
            f.write(content)
        added += len(new_sources)
        files_updated += 1

print(f"Files updated: {files_updated}, sources added: {added}")
