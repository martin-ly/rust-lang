#!/usr/bin/env python3
"""批量修复最常见的未链接来源占位符。"""
import re
import os
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TARGET_DIRS = [
    Path("docs"), Path("book"), Path("guides"), Path("reports"),
    Path(".kimi"), Path("exercises"), Path("examples"), Path("content"),
    Path("concept"), Path("knowledge"),
]

INDEX_TARGET = Path("concept/00_meta/02_sources/international_authority_index.md")
METHOD_TARGET = Path("concept/00_meta/00_framework/methodology.md")

BRACKETED_RE = re.compile(r"\[来源[：:]\s*([^\]]+)\]")
BARE_RE = re.compile(r"(?<!\[)来源[：:]\s*([^\n\[\]]+?)(?=\s*$|\s+[,，;；]|\s*\|)")


def relative_path(from_file: Path, to_target: Path) -> str:
    return os.path.relpath(to_target, from_file.parent).replace("\\", "/")


def transform_label(label: str, index_link: str, method_link: str) -> str | None:
    s = label.strip()

    # 1) Rust 官方文档
    if s in ("Rust Official Docs", "Rust 官方文档"):
        return "[Rust Official Docs](https://doc.rust-lang.org/)"

    # 2) 内部 Sprint / Alignment 占位符 -> 指向权威来源索引
    m = re.fullmatch(r"Authority Source Sprint Batch\s+(\d+)", s)
    if m:
        return f"[Authority Source Sprint Batch {m.group(1)}]({index_link})"
    m = re.fullmatch(r"Web Authority Alignment\s+(Sprint|Batch)\s*(\d+)?", s)
    if m:
        suffix = f" {m.group(2)}" if m.group(2) else ""
        return f"[Web Authority Alignment {m.group(1)}{suffix}]({index_link})"
    if s in ("P2 Deep Content Sprint",):
        return f"[{s}]({index_link})"

    # 3) 原创分析 -> 方法论页（内部原创说明）
    if s in ("💡 原创分析", "💡 原创实现"):
        return f"[{s}]({method_link})"

    return None


def transform_exact(label: str) -> str | None:
    """可复用的精确外部权威映射。"""
    s = label.strip()

    exact = {
        # Rust 官方文档
        "Rust Nightly Documentation": "https://doc.rust-lang.org/nightly/unstable-book/index.html",
        "Rust Standard Library / 2025": "https://doc.rust-lang.org/std/index.html",
        "Rust Standard Library — Unstable Features": "https://doc.rust-lang.org/beta/unstable-book/index.html",
        "Rust Standard Library: Backtrace": "https://doc.rust-lang.org/std/backtrace/struct.Backtrace.html",
        "Rust Release Team / 2026": "https://blog.rust-lang.org/",
        "Rust Release Tracking": "https://releases.rs/",
        "Rust 1.88 Release Notes": "https://releases.rs/docs/1.88.0/",
        "Rust 1.97 Release Notes": "https://releases.rs/docs/1.97.0/",
        "Rust Edition Guide": "https://doc.rust-lang.org/edition-guide/index.html",
        "Cargo Documentation": "https://doc.rust-lang.org/cargo/index.html",
        "Cargo Book — Source Replacement": "https://doc.rust-lang.org/cargo/reference/source-replacement.html",
        "Rust Reference — Const Generics": "https://doc.rust-lang.org/reference/items/generics.html#const-generics",
        "Rust Reference — Const Evaluation": "https://doc.rust-lang.org/reference/const_eval.html",
        "Rustc Dev Guide — UI tests": "https://rustc-dev-guide.rust-lang.org/tests/ui.html",
        "Rust By Example, \"Flow Control\"": "https://doc.rust-lang.org/rust-by-example/flow_control.html",
        "Rust Internals Forum, \"Let Chains Gotchas\"": "https://internals.rust-lang.org/",
        "Rust Keyword Generics Initiative — Extending Rust's Effect System (2024-02-09)": "https://rust-lang.github.io/keyword-generics-initiative/updates/2024-02-09-extending-rusts-effect-system.html",
        "RFC 3513 — gen blocks": "https://github.com/rust-lang/rfcs/pull/3513",
        "RFCs - Edition RFCs": "https://rust-lang.github.io/rfcs/index.html",
        "Inside Rust 2026-05-26": "https://blog.rust-lang.org/inside-rust/",
        "Inside Rust 2026-05/06": "https://blog.rust-lang.org/inside-rust/",
        "Inside Rust 2026-02/03/04": "https://blog.rust-lang.org/inside-rust/",
        "Rust Blog 2026-02-13": "https://blog.rust-lang.org/",
        "Rust Blog 2026-02-13; rust-gcc.github.io 2026-03-18": "https://blog.rust-lang.org/",
        "Rust in Production; Rust Foundation; Ferrous Systems; AWS/Google/Microsoft Rust Blogs": "https://foundation.rust-lang.org/",
        "RustSec Advisory DB 2026-06-05": "https://rustsec.org/",
        "RustSec Advisory DB 2026-06-05; releases.rs 2026-06-08": "https://rustsec.org/",
        "releases.rs 2026-06-06": "https://releases.rs/",
        "releases.rs 2026-06-06; RustSec Advisory DB 2026-06-04": "https://releases.rs/",
        "VeriContest arXiv 2026-05-08": "https://arxiv.org/",
        "LPC 2025 Rust for Linux 幻灯片": "https://rust-for-linux.com/",
        "ByteIota 2026-05-25; rust-lang/rust#156628": "https://github.com/rust-lang/rust/pull/156628",
        # 学术
        "Nicholas Nethercote - How to Speed Up the Rust Compiler": "https://nnethercote.github.io/2022/10/27/how-to-speed-up-the-rust-compiler-in-october-2022.html",
        "Rice 1953": "https://doi.org/10.2307/2268381",
        'Pierce, "Types and Programming Languages" (TAPL)': "https://www.cis.upenn.edu/~bcpierce/tapl/",
        "Pierce 2002, Ch.11": "https://www.cis.upenn.edu/~bcpierce/tapl/",
        "Linux Foundation": "https://www.linuxfoundation.org/",
        "Rust Learning Resources": "https://www.rust-lang.org/learn",
        # 生态库文档
        "Criterion.rs Documentation": "https://bheisler.github.io/criterion.rs/book/index.html",
        "thiserror docs": "https://docs.rs/thiserror/latest/thiserror/",
        "Rocket docs": "https://docs.rs/rocket/latest/rocket/",
        "Poem docs": "https://docs.rs/poem/latest/poem/",
        "embedded-hal 文档": "https://docs.rs/embedded-hal/latest/embedded_hal/",
        "svd2rust 文档": "https://docs.rs/svd2rust/latest/svd2rust/",
        "defmt 文档": "https://docs.rs/defmt/latest/defmt/",
        "tokio-uring": "https://docs.rs/tokio-uring/latest/tokio_uring/",
        "quinn crate": "https://docs.rs/quinn/latest/quinn/",
        "rust-libp2p crate": "https://docs.rs/libp2p/latest/libp2p/",
        "Protocol Labs - libp2p": "https://libp2p.io/",
        "libp2p Specification": "https://specs.libp2p.io/",
        # 测试/安全
        "AFL - American Fuzzy Lop": "https://github.com/google/AFL",
        "LLVM libFuzzer": "https://llvm.org/docs/LibFuzzer.html",
        "Rust Fuzzing Book - fuzzingbook.com": "https://rust-fuzz.github.io/book/introduction.html",
        "Linux Kernel Documentation": "https://docs.kernel.org/",
        "Linux Kernel io_uring 性能基准测试": "https://docs.kernel.org/io_uring.html",
        # 跨语言参考
        "Go Spec: Concurrency": "https://go.dev/ref/spec#Go_statements",
        "Go Spec: Errors": "https://go.dev/ref/spec#Errors",
        "Go Spec: Types": "https://go.dev/ref/spec#Types",
        "C++ Reference: thread": "https://en.cppreference.com/w/cpp/thread",
        "C++ Reference: Exception handling": "https://en.cppreference.com/w/cpp/language/exceptions",
        "C++ Reference: Templates": "https://en.cppreference.com/w/cpp/templates",
        # 失效/占位链接保留原 URL
        "[Rust 中文社区 [已失效]]<!-- 原链接: https://rustcc.cn/ -->": "https://rustcc.cn/",
        "[Rust Blog [已失效]]<!-- 原链接: https://blog.rust-lang.org/2026/01/xx/Rust-1.93.0/ -->": "https://blog.rust-lang.org/",
        # 学术
        "Honda, *Types for Dyadic Interaction*, 1993": "https://doi.org/10.1007/3-540-57208-2_35",
        "Gamma et al. 1994 - Design Patterns": "https://en.wikipedia.org/wiki/Design_Patterns",
        "Bloom Taxonomy 2001": "https://cft.vanderbilt.edu/guides-sub-pages/blooms-taxonomy/",
        "Tony Buzan - Mind Mapping": "https://www.tonybuzan.com/",
        # Rust 团队/治理
        "Rust Team / Cargo Book 2025": "https://doc.rust-lang.org/cargo/index.html",
        "Rust Team / TRPL 2025": "https://doc.rust-lang.org/book/title-page.html",
        "Rust Team / Rustonomicon 2025": "https://doc.rust-lang.org/nomicon/index.html",
        "Rust Core Team / 2017": "https://blog.rust-lang.org/2017/",
        "Rust Core Team / 2022": "https://blog.rust-lang.org/2022/",
        "Rust Reference / 2025": "https://doc.rust-lang.org/reference/introduction.html",
        "Rust Compiler Team": "https://www.rust-lang.org/governance/teams/compiler",
        "Rust Compiler Development Guide": "https://rustc-dev-guide.rust-lang.org/",
        "Rust Compiler Team Benchmarks": "https://perf.rust-lang.org/",
        "Rust Tools Team": "https://www.rust-lang.org/governance/teams/dev-tools",
        "Rust Project Guidelines": "https://www.rust-lang.org/policies",
        "Rust CI Best Practices": "https://rustc-dev-guide.rust-lang.org/tests/intro.html",
        "RFC 未正式发布，社区长期需求": "https://github.com/rust-lang/rfcs/pulls",
        "rustc_parallel_frontend 跟踪 Issue": "https://github.com/rust-lang/rust/issues/48685",
        "Wikipedia - Rust (programming language)": "https://en.wikipedia.org/wiki/Rust_(programming_language)",
        "Mozilla - sccache": "https://github.com/mozilla/sccache",
        "Google Style Guides": "https://google.github.io/styleguide/",
        "Microsoft Secure Coding Guidelines": "https://learn.microsoft.com/en-us/azure/security/develop/secure-design",
        # 安全认证
        "Ferrocene": "https://ferrocene.dev/",
        "Ferrocene Language Specification": "https://spec.ferrocene.dev/",
        "Ferrocene 26.02.0 Release Notes": "https://ferrocene.dev/",
        "MISRA": "https://www.misra.org.uk/",
        "MISRA Rust Guidelines": "https://www.misra.org.uk/",
        "IEC 61508": "https://webstore.iec.ch/publication/66912",
        "IEC 61508 - Safety Standards": "https://webstore.iec.ch/publication/66912",
        "ISO 26262": "https://www.iso.org/standard/68383.html",
        "ISO 26262 - Functional Safety": "https://www.iso.org/standard/68383.html",
        "DO-178C": "https://www.rtca.org/product/307",
        # 通用/会议
        "PLDI 2024/2025 Compiler-Guided Code Generation": "https://pldi24.sigplan.org/",
        "anyhow.rs Documentation": "https://docs.rs/anyhow/latest/anyhow/",
    }
    if s in exact:
        return f"[{s}]({exact[s]})"

    # ACM / IEEE 通用入口
    if s.startswith("ACM -"):
        return f"[{s}](https://dl.acm.org/)"
    if s.startswith("IEEE -"):
        return f"[{s}](https://ieeexplore.ieee.org/)"

    return None


def fix_file(path: Path) -> int:
    text = path.read_text(encoding="utf-8", errors="ignore")
    original = text
    index_link = relative_path(path, INDEX_TARGET)
    method_link = relative_path(path, METHOD_TARGET)

    def bracket_repl(m):
        label = m.group(1)
        if re.search(r"\]\(", label):
            return m.group(0)
        new = transform_label(label, index_link, method_link)
        if not new:
            new = transform_exact(label)
        return new if new else m.group(0)

    text = BRACKETED_RE.sub(bracket_repl, text)

    def bare_repl(m):
        label = m.group(1)
        if re.search(r"\]\(", label):
            return m.group(0)
        new = transform_label(label, index_link, method_link)
        if not new:
            new = transform_exact(label)
        return new if new else m.group(0)

    text = BARE_RE.sub(bare_repl, text)

    if text != original:
        path.write_text(text, encoding="utf-8", errors="ignore", newline="\n")
        return 1
    return 0


def main():
    changed = 0
    files = 0
    for d in TARGET_DIRS:
        full = ROOT / d
        if not full.exists():
            continue
        for p in sorted(full.rglob("*.md")):
            if "archive" in p.parts or "node_modules" in p.parts:
                continue
            files += 1
            changed += fix_file(p)
    print(f"已扫描 {files} 个文件，修改 {changed} 个。")


if __name__ == "__main__":
    main()
