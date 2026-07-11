#!/usr/bin/env python3
"""修复 docs/、book/、guides/ 中未带 URL 的来源占位符。

处理模式：
- [来源: Wikipedia - Topic]
- [来源: TRPL Ch. X - Title]
- [来源: Rust Reference - Topic]
- [来源: Rustonomicon - Topic]
- [来源: RFC NNNN - Title]
- [来源: POPL 2018 - RustBelt]
- [来源: Cargo Book]
- [来源: Rust API Guidelines]
- ...
"""

import re
import sys
from pathlib import Path
from urllib.parse import quote

TARGET_DIRS = [Path("docs"), Path("book"), Path("guides"), Path("reports"), Path(".kimi"), Path("exercises"), Path("examples"), Path("content"), Path("concept")]

TRPL_CHAPTERS = {
    "1": "ch01-00-getting-started",
    "2": "ch02-00-guessing-game-tutorial",
    "3": "ch03-00-common-programming-concepts",
    "3.1": "ch03-01-variables-and-mutability",
    "3.2": "ch03-02-data-types",
    "3.3": "ch03-03-how-functions-work",
    "4": "ch04-00-ownership",
    "4.1": "ch04-01-what-is-ownership",
    "4.2": "ch04-02-references-and-borrowing",
    "4.3": "ch04-03-slices",
    "5": "ch05-00-structs",
    "6": "ch06-00-enums-and-pattern-matching",
    "6.1": "ch06-01-defining-an-enum",
    "6.2": "ch06-02-match",
    "6.3": "ch06-03-if-let",
    "7": "ch07-00-managing-growing-projects-with-packages-crates-and-modules",
    "8": "ch08-00-common-collections",
    "9": "ch09-00-error-handling",
    "9.1": "ch09-01-unrecoverable-errors-with-panic",
    "9.2": "ch09-02-recoverable-errors-with-result",
    "9.3": "ch09-03-to-panic-or-not-to-panic",
    "10": "ch10-00-generic-types-traits-and-lifetimes",
    "10.1": "ch10-01-syntax",
    "10.2": "ch10-02-traits",
    "10.3": "ch10-03-lifetime-syntax",
    "11": "ch11-00-testing",
    "12": "ch12-00-an-io-project",
    "13": "ch13-00-functional-features-of-rust",
    "13.1": "ch13-01-closures",
    "13.2": "ch13-02-iterators",
    "13.3": "ch13-03-improving-our-io-project",
    "13.4": "ch13-04-performance",
    "14": "ch14-00-more-about-cargo",
    "15": "ch15-00-smart-pointers",
    "15.1": "ch15-01-box",
    "15.2": "ch15-02-deref",
    "15.3": "ch15-04-rc",
    "15.4": "ch15-05-interior-mutability",
    "15.5": "ch15-06-reference-cycles",
    "16": "ch16-00-concurrency",
    "16.1": "ch16-01-threads",
    "16.2": "ch16-02-message-passing",
    "16.3": "ch16-03-shared-state",
    "16.4": "ch16-04-extensible-concurrency-sync-and-send",
    "17": "ch17-00-async-await",
    "17.1": "ch17-01-futures-and-syntax",
    "17.2": "ch17-02-async-await",
    "17.3": "ch17-03-more-on-async",
    "18": "ch18-00-patterns",
    "19": "ch19-00-advanced-features",
    "19.1": "ch19-01-unsafe-rust",
    "19.2": "ch19-02-advanced-lifetimes",
    "19.3": "ch19-03-advanced-traits",
    "19.4": "ch19-04-advanced-types",
    "19.5": "ch19-05-advanced-functions-and-closures",
    "20": "ch20-00-final-project-a-web-server",
}

RUST_REFERENCE_TOPICS = {
    "std::sync": "https://doc.rust-lang.org/std/sync/",
    "borrow checker": "https://doc.rust-lang.org/reference/",
    "concurrency": "https://doc.rust-lang.org/reference/special-types-and-traits.html",
    "async/await": "https://doc.rust-lang.org/reference/items/functions.html#async-functions",
    "async fn desugaring": "https://doc.rust-lang.org/reference/items/functions.html#async-functions",
    "type system": "https://doc.rust-lang.org/reference/types.html",
    "ownership": "https://doc.rust-lang.org/reference/",
    "traits": "https://doc.rust-lang.org/reference/items/traits.html",
    "macros": "https://doc.rust-lang.org/reference/macros.html",
    "procedural macros": "https://doc.rust-lang.org/reference/procedural-macros.html",
    "unsafe": "https://doc.rust-lang.org/reference/unsafe-blocks.html",
    "unsafe rust": "https://doc.rust-lang.org/reference/unsafe-blocks.html",
    "lifetimes": "https://doc.rust-lang.org/reference/lifetime-elision.html",
    "control flow": "https://doc.rust-lang.org/reference/expressions.html",
    "no_std": "https://doc.rust-lang.org/reference/names/preludes.html",
    "test attributes": "https://doc.rust-lang.org/reference/attributes/testing.html",
    "cargo": "https://doc.rust-lang.org/cargo/",
    "result": "https://doc.rust-lang.org/std/result/",
    "parallel iterators": "https://doc.rust-lang.org/std/iter/trait.Iterator.html",
    "doc.rust-lang.org/reference": "https://doc.rust-lang.org/reference/",
}

RUSTONOMICON_TOPICS = {
    "ownership": "https://doc.rust-lang.org/nomicon/ownership.html",
    "concurrency": "https://doc.rust-lang.org/nomicon/concurrency.html",
    "async": "https://doc.rust-lang.org/std/pin/struct.Pin.html",
    "memory layout": "https://doc.rust-lang.org/nomicon/repr-rust.html",
    "implementation details": "https://doc.rust-lang.org/nomicon/",
    "doc.rust-lang.org/nomicon": "https://doc.rust-lang.org/nomicon/",
}

RFC_NUMBERS = {
    "1584": "1584-macros-literal-matcher",
    "1566": "1566-proc-macros",
    "2094": "2094-nll",
    "2289": "2289-associated-type-bounds",
    "2349": "2349-pin",
    "2394": "2394-async_await",
    "243": "0243-trait-based-exception-handling",
    "2484": "2484-trait-from-tryfrom",
    "2504": "2504-try-trait",
    "2585": "2585-unsafe-block-in-unsafe-fn",
    "2616": "2616-http",
    "3151": "3151-scoped-threads",
    "3185": "3185-cargo-weak-namespaced-features",
    "3498": "3498-precise-capturing",
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


# Common ecosystem / tool URLs used for bare `[name]` source labels.
ECOSYSTEM_URLS = {
    "serde": "https://serde.rs/",
    "serde.rs": "https://serde.rs/",
    "tokio": "https://tokio.rs/",
    "tokio.rs": "https://tokio.rs/",
    "rayon": "https://docs.rs/rayon/latest/rayon/",
    "crossbeam": "https://docs.rs/crossbeam/latest/crossbeam/",
    "parking_lot": "https://docs.rs/parking_lot/latest/parking_lot/",
    "parking lot": "https://docs.rs/parking_lot/latest/parking_lot/",
    "tracing": "https://docs.rs/tracing/latest/tracing/",
    "anyhow": "https://docs.rs/anyhow/latest/anyhow/",
    "thiserror": "https://docs.rs/thiserror/latest/thiserror/",
    "eyre": "https://docs.rs/eyre/latest/eyre/",
    "reqwest": "https://docs.rs/reqwest/latest/reqwest/",
    "hyper": "https://hyper.rs/",
    "hyper.rs": "https://hyper.rs/",
    "actix": "https://actix.rs/",
    "actix.rs": "https://actix.rs/",
    "axum": "https://docs.rs/axum/latest/axum/",
    "rocket": "https://rocket.rs/",
    "rocket.rs": "https://rocket.rs/",
    "warp": "https://docs.rs/warp/latest/warp/",
    "tauri": "https://tauri.app/",
    "bevy": "https://bevyengine.org/",
    "bevyengine": "https://bevyengine.org/",
    "ratatui": "https://ratatui.rs/",
    "crossterm": "https://docs.rs/crossterm/latest/crossterm/",
    "nom": "https://docs.rs/nom/latest/nom/",
    "clap": "https://clap.rs/",
    "clap.rs": "https://clap.rs/",
    "pyo3": "https://pyo3.rs/",
    "pyo3.rs": "https://pyo3.rs/",
    "lib.rs": "https://lib.rs/",
    "rust-analyzer": "https://rust-analyzer.github.io/",
    "rust analyzer": "https://rust-analyzer.github.io/",
    "ripgrep": "https://github.com/BurntSushi/ripgrep",
    "bat": "https://github.com/sharkdp/bat",
    "fd": "https://github.com/sharkdp/fd",
    "alacritty": "https://alacritty.org/",
    "sqlx": "https://github.com/launchbadge/sqlx",
    "diesel": "https://diesel.rs/",
    "sea-orm": "https://www.sea-ql.org/SeaORM/",
    "mongodb": "https://docs.rs/mongodb/latest/mongodb/",
    "redis": "https://docs.rs/redis/latest/redis/",
    "tokio-postgres": "https://docs.rs/tokio-postgres/latest/tokio_postgres/",
    "tokio postgres": "https://docs.rs/tokio-postgres/latest/tokio_postgres/",
    "cargo-geiger": "https://github.com/rust-secure-code/cargo-geiger",
    "cargo geiger": "https://github.com/rust-secure-code/cargo-geiger",
    "rustc": "https://doc.rust-lang.org/rustc/",
    "rust-lang.org": "https://www.rust-lang.org/",
    "rust secure code wg": "https://github.com/rust-secure-code/wg",
    "mozilla supply chain": "https://www.mozilla.org/en-US/security/",
    "cargo-vet": "https://mozilla.github.io/cargo-vet/",
    "rustsec": "https://rustsec.org/",
    "crates.io": "https://crates.io/",
    "docs.rs": "https://docs.rs/",
    "github": "https://github.com/",
    "releases.rs": "https://releases.rs/",
    "can i use": "https://caniuse.rs/",
    "kani": "https://model-checking.github.io/kani/",
    "verus": "https://verus-lang.github.io/verus/",
    "prusti": "https://www.pm.inf.ethz.ch/research/prusti.html",
    "creusot": "https://creusot.github.io/creusot/",
    "aeneas": "https://github.com/AeneasVerif/aeneas",
    "miri": "https://github.com/rust-lang/miri",
    "clippy": "https://doc.rust-lang.org/clippy/",
    "rustfmt": "https://rust-lang.github.io/rustfmt/",
    "rustup": "https://rust-lang.github.io/rustup/",
    "cargo": "https://doc.rust-lang.org/cargo/",
    # Documentation / book labels with surrounding text
    "tokio documentation": "https://tokio.rs/",
    "tokio docs": "https://tokio.rs/",
    "the cargo book": "https://doc.rust-lang.org/cargo/",
    "cargo book": "https://doc.rust-lang.org/cargo/",
    "cargo documentation": "https://doc.rust-lang.org/cargo/",
    "the embedded rust book": "https://doc.rust-lang.org/stable/embedded-book/",
    "rust embedded book": "https://doc.rust-lang.org/stable/embedded-book/",
    "rust design patterns": "https://rust-unofficial.github.io/patterns/",
    "rust cookbook": "https://rust-lang-nursery.github.io/rust-cookbook/",
    "rust cli book": "https://rust-cli.github.io/book/",
    "rust async-book": "https://rust-lang.github.io/async-book/",
    "rust platform support": "https://doc.rust-lang.org/nightly/rustc/platform-support.html",
    "rust ffi guidelines": "https://rust-lang.github.io/unsafe-code-guidelines/",
    "rust secure code guidelines": "https://github.com/rust-secure-code/wg",
    "serde documentation": "https://serde.rs/",
    "bevy documentation": "https://bevyengine.org/",
    "bevy ecs documentation": "https://bevyengine.org/",
    "axum documentation": "https://docs.rs/axum/latest/axum/",
    "sqlx documentation": "https://github.com/launchbadge/sqlx",
    "tracing documentation": "https://docs.rs/tracing/latest/tracing/",
    "mockall documentation": "https://docs.rs/mockall/latest/mockall/",
    "proptest book": "https://proptest-rs.github.io/proptest/",
    "cargo-deny": "https://github.com/EmbarkStudios/cargo-deny",
    "cargo-vet documentation": "https://mozilla.github.io/cargo-vet/",
    "opentelemetry rust": "https://github.com/open-telemetry/opentelemetry-rust",
    "swatinem/rust-cache": "https://github.com/Swatinem/rust-cache",
    "wasi overview": "https://wasi.dev/",
    "tower service": "https://docs.rs/tower/latest/tower/",
    "actix docs": "https://actix.rs/",
    "rust in production": "https://www.rust-lang.org/",
    "raft paper": "https://raft.github.io/",
    "young — cqrs documents": "https://martinfowler.com/bliki/CQRS.html",
    "van der aalst — process mining": "https://www.processmining.org/",
    "coq reference": "https://coq.inria.fr/doc/",
    "tla+": "https://lamport.azurewebsites.net/tla/tla.html",
    "acm - formal verification": "https://dl.acm.org/",
    # Academic / survey / working group labels
    "tla+ documentation": "https://lamport.azurewebsites.net/tla/tla.html",
    "coq reference manual": "https://coq.inria.fr/doc/",
    "iris project": "https://iris-project.org/",
    "iris project - iris-project.org": "https://iris-project.org/",
    "workflow patterns initiative": "https://www.workflowpatterns.com/",
    "workflowpatterns.com": "https://www.workflowpatterns.com/",
    "gang of four - design patterns": "https://en.wikipedia.org/wiki/Design_Patterns",
    "gang of four": "https://en.wikipedia.org/wiki/Design_Patterns",
    "gof - design patterns": "https://en.wikipedia.org/wiki/Design_Patterns",
    "russell 2006": "https://www.workflowpatterns.com/",
    "russell et al. (2006)": "https://www.workflowpatterns.com/",
    "van der aalst 2003": "https://www.workflowpatterns.com/",
    "van der aalst et al. 2003": "https://www.workflowpatterns.com/",
    "van der aalst et al. (2003)": "https://www.workflowpatterns.com/",
    "pierce 2002 - tapl": "https://www.cis.upenn.edu/~bcpierce/tapl/",
    "tofte & talpin 1994": "https://en.wikipedia.org/wiki/Region-based_memory_management",
    "hoare 1978": "https://en.wikipedia.org/wiki/Communicating_sequential_processes",
    "hoare 1978 - csp": "https://en.wikipedia.org/wiki/Communicating_sequential_processes",
    "milner 1989 - communication and concurrency": "https://en.wikipedia.org/wiki/Communication_and_Concurrency",
    "roscoe 2011": "https://en.wikipedia.org/wiki/Communicating_sequential_processes",
    "girard 1987 - linear logic": "https://en.wikipedia.org/wiki/Linear_logic",
    "petri net theory": "https://en.wikipedia.org/wiki/Petri_net",
    "wfmc - workflow management coalition": "https://www.wfmc.org/",
    # ACM / IEEE / POPL / PLDI with descriptive suffixes
    "acm - software design patterns": "https://dl.acm.org/",
    "acm - ai systems": "https://dl.acm.org/",
    "acm - formal verification survey": "https://dl.acm.org/",
    "acm - systems programming languages survey": "https://dl.acm.org/",
    "acm - concurrent programming": "https://dl.acm.org/",
    "acm - type systems": "https://dl.acm.org/",
    "acm - parallel programming": "https://dl.acm.org/",
    "acm - formal methods": "https://dl.acm.org/",
    "acm - performance engineering": "https://dl.acm.org/",
    "acm - ownership types": "https://dl.acm.org/",
    "acm - linear logic in programming": "https://dl.acm.org/",
    "acm - advanced type system features": "https://dl.acm.org/",
    "ieee - specification standards": "https://standards.ieee.org/",
    "ieee - formal specification standards": "https://standards.ieee.org/",
    "ieee - parallel algorithms": "https://standards.ieee.org/",
    "ieee - logic in computer science": "https://standards.ieee.org/",
    "ieee - type safety in systems programming": "https://standards.ieee.org/",
    "ieee - type safety verification": "https://standards.ieee.org/",
    "ieee - network protocols": "https://standards.ieee.org/",
    "pldi - programming language design and implementation": "https://www.sigplan.org/Conferences/PLDI/",
    "pldi 2023 - aeneas": "https://www.sigplan.org/Conferences/PLDI/",
    "popl - automated verification": "https://www.sigplan.org/Conferences/POPL/",
    "popl 2020 - oxide": "https://www.sigplan.org/Conferences/POPL/",
    "popl/pldi 论文": "https://www.sigplan.org/Conferences/POPL/",
    # Rust working groups / release notes
    "rust gamedev working group": "https://gamedev.rs/",
    "rust async working group": "https://rust-lang.github.io/wg-async/",
    "rust cli working group": "https://rust-lang.github.io/wg-cli/",
    "rust embedded working group": "https://rust-embedded.github.io/book/",
    "rust embedded wg": "https://rust-embedded.github.io/book/",
    "rust core team / 2022": "https://www.rust-lang.org/governance",
    "rust release team / 2026": "https://www.rust-lang.org/governance",
    "rust release notes": "https://github.com/rust-lang/rust/blob/master/RELEASES.md",
    "rust 1.95 release notes": "https://releases.rs/1.95.0/",
    "rust release tracking": "https://releases.rs/",
    # Rust books & docs
    "rust edition guide": "https://doc.rust-lang.org/edition-guide/",
    "rust 2024 edition guide": "https://doc.rust-lang.org/edition-guide/rust-2024/index.html",
    "the embedded rust book": "https://doc.rust-lang.org/stable/embedded-book/",
    "rust embedded book - docs.rust-embedded.org": "https://doc.rust-lang.org/stable/embedded-book/",
    "rust design patterns book": "https://rust-unofficial.github.io/patterns/",
    "the little book of rust macros": "https://veykril.github.io/tlborm/",
    "embassy book": "https://embassy.dev/book/",
    "rtic documentation - rtic.rs": "https://rtic.rs/",
    "rtic book": "https://rtic.rs/book/",
    "rust standard library - std::thread": "https://doc.rust-lang.org/std/thread/",
    "rust reference — macros": "https://doc.rust-lang.org/reference/macros.html",
    "rust compiler documentation": "https://doc.rust-lang.org/rustc/",
    "rust nightly documentation": "https://doc.rust-lang.org/nightly/",
    "rust 官方文档": "https://doc.rust-lang.org/",
    "trpl: ch4.1": "https://doc.rust-lang.org/book/ch04-01-what-is-ownership.html",
    # Ecosystem docs
    "tch-rs documentation": "https://docs.rs/tch/latest/tch/",
    "axum.rs documentation": "https://docs.rs/axum/latest/axum/",
    "actix.rs documentation": "https://actix.rs/",
    "bevy engine documentation": "https://bevyengine.org/",
    "crossbeam documentation": "https://docs.rs/crossbeam/latest/crossbeam/",
    "miri documentation": "https://github.com/rust-lang/miri",
    "tokio docs - tokio::sync": "https://docs.rs/tokio/latest/tokio/sync/",
    "serde.rs documentation": "https://serde.rs/",
    "crates.io documentation": "https://crates.io/",
    "crates.io 统计, 2025": "https://crates.io/",
    "rfcs - rust-lang/rfcs": "https://github.com/rust-lang/rfcs",
    "rustbelt paper": "https://plv.mpi-sws.org/rustbelt/",
    "the rustonomicon": "https://doc.rust-lang.org/nomicon/",
    "the cargo book": "https://doc.rust-lang.org/cargo/",
    "rust async book": "https://rust-lang.github.io/async-book/",
    "rust blog": "https://blog.rust-lang.org/",
    "wikipedia - rust (programming language)": "https://en.wikipedia.org/wiki/Rust_(programming_language)",
    # Cross-language / standards
    "c++ reference: std::unique_ptr": "https://en.cppreference.com/w/cpp/memory/unique_ptr",
    "go spec: memory model": "https://go.dev/ref/mem",
    "unicode standard": "https://unicode.org/standard/standard.html",
    "stack overflow developer survey 2025": "https://survey.stackoverflow.co/2025/",
}


def lookup(ref: str) -> str | None:
    ref_norm = ref.strip()
    # Normalize nested bracket wrappers like "[The Rust Programming Language]"
    while ref_norm.startswith("[") and ref_norm.endswith("]"):
        ref_norm = ref_norm[1:-1].strip()
    lowered = ref_norm.lower()

    # Direct ecosystem lookup (covers bare [serde], [tokio], etc.)
    if lowered in ECOSYSTEM_URLS:
        return f"[{ref_norm}]({ECOSYSTEM_URLS[lowered]})"

    # Strip 来源: prefix
    m = re.match(r"(?:学术)?来源[:：]\s*(.+)", ref_norm, re.IGNORECASE)
    if m:
        inner = m.group(1).strip()
        inner_repl = lookup(inner)
        if inner_repl:
            return f"来源: {inner_repl}"
        # Borrows
    if re.match(r"Tree\s+Borrows", ref_norm, re.IGNORECASE):
        return "[Tree Borrows — PLDI 2025](https://perso.crans.org/vanille/treebor/)"
    if re.match(r"Stacked\s+Borrows", ref_norm, re.IGNORECASE):
        return "[Stacked Borrows](https://plv.mpi-sws.org/rustbelt/stacked-borrows/)"

    # Slash-separated source pairs
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

    # Async Book
    if re.match(r"Rust\s+Async\s+Book", ref_norm, re.IGNORECASE) or lowered == "async book":
        return "[The Rust Async Book](https://rust-lang.github.io/async-book/)"

    # Wikipedia (colon / hyphen / en-dash / em-dash)
    m = re.match(r"Wikipedia\s*[:\-—–]\s*(.+)", ref_norm, re.IGNORECASE)
    if m:
        topic = m.group(1).strip()
        return f"[{ref_norm}]({wikipedia_url(topic)})"
    if lowered == "wikipedia":
        return "[Wikipedia](https://en.wikipedia.org/wiki/Main_Page)"

    # RFCs repo
    if re.match(r"RFCs\s*[–\-—]\s*github\.com/rust-lang/rfcs", ref_norm, re.IGNORECASE):
        return "[Rust RFCs](https://github.com/rust-lang/rfcs)"

    # RFC number
    m = re.match(r"(?:Rust\s+)?RFC\s*#?(\d+)(?:\s*[–\-—]\s*(.+))?", ref_norm, re.IGNORECASE)
    if m:
        return f"[{ref_norm}]({rfc_url(m.group(1))})"

    # TRPL chapter
    m = re.match(r"TRPL\s+Ch\.?\s*(\d+(?:\.\d+)?)(?:\s*[–\-—]\s*(.+))?", ref_norm, re.IGNORECASE)
    if m:
        return f"[{ref_norm}]({trpl_url(m.group(1))})"

    # TRPL root / Rust Team / TRPL YYYY
    if re.match(r"TRPL(?:\s*[–\-—]\s*The\s+Rust\s+Programming\s+Language)?", ref_norm, re.IGNORECASE):
        return "[The Rust Programming Language](https://doc.rust-lang.org/book/)"
    if re.match(r"Rust\s+Team\s*/\s*TRPL\s+\d{4}", ref_norm, re.IGNORECASE):
        return "[The Rust Programming Language](https://doc.rust-lang.org/book/)"
    if re.match(r"The\s+Rust\s+Programming\s+Language\s+TRPL", ref_norm, re.IGNORECASE):
        return "[The Rust Programming Language](https://doc.rust-lang.org/book/)"

    # Rust Reference (also "Rust Reference / YYYY", "Rust Reference §X")
    m = re.match(r"Rust\s+Reference(?:\s*[/\-—–]\s*\d{4})?(?:\s*§\s*.+)?", ref_norm, re.IGNORECASE)
    if m:
        return "[Rust Reference](https://doc.rust-lang.org/reference/)"

    # Rustonomicon (also "Rust Team / Rustonomicon YYYY")
    m = re.match(r"(?:The\s+)?Rustonomicon(?:\s*[/\-—–]\s*\d{4})?(?:\s*[–\-—]\s*(.+))?", ref_norm, re.IGNORECASE)
    if m:
        topic = (m.group(1) or "").strip().lower()
        url = RUSTONOMICON_TOPICS.get(topic, "https://doc.rust-lang.org/nomicon/")
        return f"[{ref_norm}]({url})"

    # POPL 2018 RustBelt
    if re.match(r"POPL\s+2018\s*[–\-—]\s*RustBelt", ref_norm, re.IGNORECASE):
        return "[RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/)"

    # RustBelt / Oxide / Jung et al.
    if re.match(r"RustBelt(?:\s*[–\-—]\s*(.+))?", ref_norm, re.IGNORECASE):
        return "[RustBelt](https://plv.mpi-sws.org/rustbelt/)"
    if re.match(r"RustBelt/Oxide", ref_norm, re.IGNORECASE):
        return "[RustBelt / Oxide](https://plv.mpi-sws.org/rustbelt/)"
    if re.match(r"Jung\s+et\s+al\.\s*\d{4}\s*[–\-—]\s*RustBelt", ref_norm, re.IGNORECASE):
        return "[RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/)"

    # Cargo Book (also "Rust Team / Cargo Book YYYY")
    if re.match(r"Cargo\s+Book(?:\s*[/\-—–]\s*\d{4})?", ref_norm, re.IGNORECASE):
        return "[The Cargo Book](https://doc.rust-lang.org/cargo/)"
    if re.match(r"Cargo\s+CHANGELOG", ref_norm, re.IGNORECASE):
        return f"[{ref_norm}](https://github.com/rust-lang/cargo/blob/master/CHANGELOG.md)"

    # Rust API Guidelines
    if re.match(r"Rust\s+API\s+Guidelines", ref_norm, re.IGNORECASE):
        return "[Rust API Guidelines](https://rust-lang.github.io/api-guidelines/)"

    # Rust Project Goals
    if re.match(r"Rust\s+Project\s+Goals\s+2026", ref_norm, re.IGNORECASE):
        return "[Rust Project Goals 2026](https://rust-lang.github.io/rust-project-goals/2026/)"

    # Generic authoritative source labels (often seen as [来源: ...])
    if re.fullmatch(r"Rust Official Docs?", ref_norm, re.IGNORECASE):
        return "[Rust Official Docs](https://doc.rust-lang.org/)"
    if re.fullmatch(r"Rust Standard Library(?: [-–—] doc.rust-lang.org/std)?", ref_norm, re.IGNORECASE):
        return "[Rust Standard Library](https://doc.rust-lang.org/std/)"
    if re.fullmatch(r"Rust Compiler Team Blog", ref_norm, re.IGNORECASE):
        return "[Rust Compiler Team Blog](https://blog.rust-lang.org/inside-rust/)"
    if re.fullmatch(r"Inside Rust", ref_norm, re.IGNORECASE):
        return "[Inside Rust](https://blog.rust-lang.org/inside-rust/)"
    if re.fullmatch(r"Rust Blog", ref_norm, re.IGNORECASE):
        return "[Rust Blog](https://blog.rust-lang.org/)"
    if re.fullmatch(r"LLVM Documentation", ref_norm, re.IGNORECASE):
        return "[LLVM Documentation](https://llvm.org/docs/)"
    if re.fullmatch(r"ACM(?: [-–—] (?:Systems Programming|Systems Programming Languages|Compiler Design))?(?: [-–—] (?:PLDI|POPL))?", ref_norm, re.IGNORECASE):
        return "[ACM](https://dl.acm.org/)"
    if re.fullmatch(r"IEEE(?: [-–—] (?:Programming Language Standards|Standards))?", ref_norm, re.IGNORECASE):
        return "[IEEE](https://standards.ieee.org/)"
    if re.fullmatch(r"POPL(?: [-–—] Programming Languages Research)?", ref_norm, re.IGNORECASE):
        return "[POPL](https://www.sigplan.org/Conferences/POPL/)"
    if re.fullmatch(r"PLDI(?: [-–—] Programming Language Design)?", ref_norm, re.IGNORECASE):
        return "[PLDI](https://www.sigplan.org/Conferences/PLDI/)"
    if re.fullmatch(r"The Rust Programming Language", ref_norm, re.IGNORECASE):
        return "[The Rust Programming Language](https://doc.rust-lang.org/book/)"
    if re.fullmatch(r"The Rustonomicon", ref_norm, re.IGNORECASE):
        return "[The Rustonomicon](https://doc.rust-lang.org/nomicon/)"
    if re.fullmatch(r"Rust By Example", ref_norm, re.IGNORECASE):
        return "[Rust By Example](https://doc.rust-lang.org/rust-by-example/)"
    if re.fullmatch(r"Rustlings", ref_norm, re.IGNORECASE):
        return "[Rustlings](https://github.com/rust-lang/rustlings/)"
    if re.fullmatch(r"Comprehensive Rust", ref_norm, re.IGNORECASE):
        return "[Comprehensive Rust](https://google.github.io/comprehensive-rust/)"
    if re.fullmatch(r"Brown University Rust Book", ref_norm, re.IGNORECASE):
        return "[Brown University Rust Book](https://rust-book.cs.brown.edu/)"
    if re.fullmatch(r"Effective Rust", ref_norm, re.IGNORECASE):
        return "[Effective Rust](https://www.lurklurk.org/effective-rust/)"
    if re.fullmatch(r"Programming Rust", ref_norm, re.IGNORECASE):
        return "[Programming Rust](https://www.oreilly.com/library/view/programming-rust-2nd/9781492052586/)"
    if re.fullmatch(r"Rust for Rustaceans", ref_norm, re.IGNORECASE):
        return "[Rust for Rustaceans](https://rust-for-rustaceans.com/)"
    if re.fullmatch(r"Rust Performance Book", ref_norm, re.IGNORECASE):
        return "[The Rust Performance Book](https://nnethercote.github.io/perf-book/)"
    if re.fullmatch(r"Rust Team", ref_norm, re.IGNORECASE):
        return "[Rust Team](https://www.rust-lang.org/governance)"
    if re.fullmatch(r"Rust Project Goals(?: 2026)?", ref_norm, re.IGNORECASE):
        return f"[{ref_norm}](https://rust-lang.github.io/rust-project-goals/)"
    if re.fullmatch(r"Can I Use", ref_norm, re.IGNORECASE):
        return "[Can I Use](https://caniuse.rs/)"
    if re.fullmatch(r"This Week in Rust", ref_norm, re.IGNORECASE):
        return "[This Week in Rust](https://this-week-in-rust.org/)"

    return None


PATTERN = re.compile(r"\[([^\]]+)\](?!\(|\[)")

# Protect code blocks and inline code spans from placeholder replacement.
FENCED_CODE_RE = re.compile(r"(```[\s\S]*?```)")
INLINE_CODE_RE = re.compile(r"(`[^`\n]*`)")


def _replace_outside_code(text: str, repl) -> str:
    """Apply PATTERN.sub only to text outside fenced/inline code spans."""
    parts = []
    for i, segment in enumerate(FENCED_CODE_RE.split(text)):
        if i % 2 == 1:
            parts.append(segment)
            continue
        inline_parts = []
        for j, inline_segment in enumerate(INLINE_CODE_RE.split(segment)):
            if j % 2 == 1:
                inline_parts.append(inline_segment)
            else:
                inline_parts.append(PATTERN.sub(repl, inline_segment))
        parts.append("".join(inline_parts))
    return "".join(parts)


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
        return m.group(0)

    new_text = _replace_outside_code(text, repl)
    return new_text, actual, unknown


def main():
    dry_run = "--dry-run" in sys.argv
    total_files = 0
    total_repl = 0
    for root in TARGET_DIRS:
        if not root.exists():
            continue
        for p in sorted(root.rglob("*.md")):
            if "archive" in p.parts or "node_modules" in p.parts:
                continue
            text = p.read_text(encoding="utf-8", errors="ignore")
            new_text, n, _ = process_file(text)
            if n:
                total_files += 1
                total_repl += n
                if dry_run:
                    print(f"[dry-run] {p}: {n} replacements")
                else:
                    p.write_text(new_text, encoding="utf-8")
                    print(f"updated: {p}: {n} replacements")

    print(f"\n{'[dry-run] ' if dry_run else ''}Total: {total_files} files, {total_repl} replacements")


if __name__ == "__main__":
    main()
