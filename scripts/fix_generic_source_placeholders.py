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

BARE_RE = re.compile(r"(?<!\[)来源[：:]\s*([^\n\[\]]+?)(?=\s*$|\s+[,，;；]|\s*\|)")
LINK_RE = re.compile(r"\]\(")


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
        "Rust Reference — Traits": "https://doc.rust-lang.org/reference/items/traits.html",
        "Rust Reference — Closure types": "https://doc.rust-lang.org/reference/types/closure.html",
        "Rust Reference — Ownership and Borrowing": "https://doc.rust-lang.org/reference/introduction.html",
        "Rust Reference — Dead Code Elimination": "https://doc.rust-lang.org/reference/introduction.html",
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
        # TRPL
        "TRPL — Trait 与泛型": "https://doc.rust-lang.org/book/ch10-00-generic-types-traits-and-lifetimes.html",
        "TRPL 第 16 章 — Fearless Concurrency": "https://doc.rust-lang.org/book/ch16-00-concurrency.html",
        # 学术
        "Nicholas Nethercote - How to Speed Up the Rust Compiler": "https://nnethercote.github.io/2022/10/27/how-to-speed-up-the-rust-compiler-in-october-2022.html",
        "Rice 1953": "https://doi.org/10.2307/2268381",
        "Honda, *Types for Dyadic Interaction*, 1993": "https://doi.org/10.1007/3-540-57208-2_35",
        'Pierce, "Types and Programming Languages" (TAPL)': "https://www.cis.upenn.edu/~bcpierce/tapl/",
        "Pierce 2002, Ch.11": "https://www.cis.upenn.edu/~bcpierce/tapl/",
        "Linux Foundation": "https://www.linuxfoundation.org/",
        "Rust Learning Resources": "https://www.rust-lang.org/learn",
        "Bloom Taxonomy 2001": "https://cft.vanderbilt.edu/guides-sub-pages/blooms-taxonomy/",
        "Tony Buzan - Mind Mapping": "https://www.tonybuzan.com/",
        "Gamma et al. 1994 - Design Patterns": "https://en.wikipedia.org/wiki/Design_Patterns",
        "Martin Fowler - Patterns of Enterprise Application Architecture": "https://martinfowler.com/books/eaa.html",
        "Martin Fowler - Event Sourcing": "https://martinfowler.com/eaaDev/EventSourcing.html",
        "Academic Paper — \"Data-Oriented Design and C++\" by Mike Acton, CppCon 2014": "https://www.youtube.com/watch?v=rX0ItVEVjHc",
        '"Scheduling Multithreaded Computations by Work Stealing" — Blumofe & Leiserson, 1999': "https://doi.org/10.1145/324133.324234",
        'Fraser, K. (2004). "Practical Lock-Freedom". PhD thesis, University of Cambridge': "https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-579.pdf",
        'Brown, T. (2015). "Reclaiming Memory for Lock-Free Data Structures". TAAPS': "https://arxiv.org/abs/1507.06891",
        'Herlihy & Shavit (2011). "The Art of Multiprocessor Programming". Chapter 10': "https://www.cs.brown.edu/~mph/HerlihyShavit/",
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
        # 失效/占位链接保留原 URL
        "[Rust 中文社区 [已失效]]<!-- 原链接: https://rustcc.cn/ -->": "https://rustcc.cn/",
        "[Rust Blog [已失效]]<!-- 原链接: https://blog.rust-lang.org/2026/01/xx/Rust-1.93.0/ -->": "https://blog.rust-lang.org/",
        # 生态库官方文档（中文标签）
        "Reqwest 官方文档": "https://docs.rs/reqwest/latest/reqwest/",
        "reqwest-middleware crate 文档": "https://docs.rs/reqwest-middleware/latest/reqwest_middleware/",
        "Hyper 官方文档 — Client": "https://docs.rs/hyper/latest/hyper/",
        "serde 官方文档": "https://serde.rs/",
        "Wgpu 官方文档": "https://docs.rs/wgpu/latest/wgpu/",
        "Naga 文档": "https://docs.rs/naga/latest/naga/",
        "WebGPU 标准 — Resource Usages": "https://www.w3.org/TR/webgpu/",
        "Wgpu Wiki — Async Initialization": "https://github.com/gfx-rs/wgpu/wiki/",
        "Actix-web 官方文档": "https://actix.rs/",
        "Actix actor 框架文档": "https://actix.rs/actors/",
        "Actix-web 文档 — Architecture Overview": "https://actix.rs/docs/architecture",
        "Actix-web 源码 — `actix-web/src/server.rs`": "https://github.com/actix/actix-web/blob/master/actix-web/src/server.rs",
        "Actix-web 文档 — Middleware": "https://actix.rs/docs/middleware",
        "Actix-web GitHub — Performance Benchmarks": "https://github.com/actix/actix-web#benchmarks",
        "Axum 文档 — Comparison with other frameworks": "https://docs.rs/axum/latest/axum/",
        "Rayon 官方文档": "https://docs.rs/rayon/latest/rayon/",
        "Rayon README — \"Data parallelism library for Rust\"": "https://docs.rs/rayon/latest/rayon/",
        "Rayon 文档 — ThreadPool": "https://docs.rs/rayon/latest/rayon/struct.ThreadPool.html",
        "Rayon 文档 — `ParallelSliceMut`": "https://docs.rs/rayon/latest/rayon/slice/trait.ParallelSliceMut.html",
        "Rayon 文档 — `scope`": "https://docs.rs/rayon/latest/rayon/fn.scope.html",
        "nalgebra 官方文档": "https://docs.rs/nalgebra/latest/nalgebra/",
        "ndarray 官方文档": "https://docs.rs/ndarray/latest/ndarray/",
        "nalgebra 文档 — Overview": "https://docs.rs/nalgebra/latest/nalgebra/",
        "ndarray 文档 — ArrayBase": "https://docs.rs/ndarray/latest/ndarray/struct.ArrayBase.html",
        "nalgebra 文档 — Const generics": "https://docs.rs/nalgebra/latest/nalgebra/",
        "ndarray 源码 — `src/lib.rs`": "https://github.com/rust-ndarray/ndarray/blob/master/src/lib.rs",
        "NumPy 文档 — Broadcasting": "https://numpy.org/doc/stable/user/basics.broadcasting.html",
        "Tracing Docs — Core Concepts": "https://docs.rs/tracing/latest/tracing/",
        "Tokio Blog — Introducing Tracing": "https://tokio.rs/blog/2019-08-tracing",
        "Tracing Docs — Subscriber": "https://docs.rs/tracing/latest/tracing/subscriber/index.html",
        "Tracing Docs — `#[instrument]`": "https://docs.rs/tracing/latest/tracing/attr.instrument.html",
        "Tracing Docs — Performance": "https://docs.rs/tracing/latest/tracing/",
        "Tracing Docs — Thread Safety": "https://docs.rs/tracing/latest/tracing/",
        "OpenTelemetry Rust Docs": "https://docs.rs/opentelemetry/latest/opentelemetry/",
        "Tracing OpenTelemetry Integration": "https://docs.rs/tracing-opentelemetry/latest/tracing_opentelemetry/",
        "Tracing Benchmarks": "https://github.com/tokio-rs/tracing#performance",
        "Rust log crate comparison": "https://docs.rs/log/latest/log/",
        "Crossbeam Docs — Overview": "https://docs.rs/crossbeam/latest/crossbeam/",
        "Crossbeam Epoch — Guard": "https://docs.rs/crossbeam-epoch/latest/crossbeam_epoch/struct.Guard.html",
        "Crossbeam Queue Docs": "https://docs.rs/crossbeam-queue/latest/crossbeam_queue/",
        "Crossbeam Queue — ArrayQueue": "https://docs.rs/crossbeam-queue/latest/crossbeam_queue/struct.ArrayQueue.html",
        "Rustnomicon — Memory Ordering": "https://doc.rust-lang.org/nomicon/atomics.html",
        "Rustnomicon — Zero-Cost Abstractions": "https://doc.rust-lang.org/nomicon/",
        "Tokio Cargo.toml": "https://github.com/tokio-rs/tokio/blob/master/tokio/Cargo.toml",
        "Rayon Cargo.toml": "https://github.com/rayon-rs/rayon/blob/master/Cargo.toml",
        "Ratatui Docs — Overview": "https://docs.rs/ratatui/latest/ratatui/",
        "Ratatui GitHub — Architecture": "https://github.com/ratatui/ratatui",
        "Ratatui Docs — Concepts": "https://docs.rs/ratatui/latest/ratatui/",
        "Ratatui Widget Docs": "https://docs.rs/ratatui/latest/ratatui/widgets/index.html",
        "Ratatui Layout Docs": "https://docs.rs/ratatui/latest/ratatui/layout/index.html",
        "Ratatui Backend Docs": "https://docs.rs/ratatui/latest/ratatui/backend/index.html",
        "Ratatui Async Guide": "https://docs.rs/ratatui/latest/ratatui/",
        "mio Docs — Getting Started": "https://docs.rs/mio/latest/mio/",
        "Tokio Docs — mio Integration": "https://docs.rs/tokio/latest/tokio/",
        "mio Docs — Poll": "https://docs.rs/mio/latest/mio/struct.Poll.html",
        "mio — Platform Notes": "https://docs.rs/mio/latest/mio/",
        "man 7 epoll": "https://man7.org/linux/man-pages/man7/epoll.7.html",
        "man 2 kqueue": "https://man.freebsd.org/cgi/man.cgi?query=kqueue&sektion=2",
        "mio Docs — Interest": "https://docs.rs/mio/latest/mio/struct.Interest.html",
        "mio Docs — Waker": "https://docs.rs/mio/latest/mio/struct.Waker.html",
        "Linux man 2 eventfd": "https://man7.org/linux/man-pages/man2/eventfd.2.html",
        "redis-rs Documentation": "https://docs.rs/redis/latest/redis/",
        "redis-rs GitHub Repository": "https://github.com/redis-rs/redis-rs",
        "redis-rs Connection Docs": "https://docs.rs/redis/latest/redis/",
        "redis-rs aio Module": "https://docs.rs/redis/latest/redis/aio/index.html",
        "redis-rs MultiplexedConnection": "https://docs.rs/redis/latest/redis/aio/struct.MultiplexedConnection.html",
        "redis-rs Streams": "https://docs.rs/redis/latest/redis/streams/index.html",
        "redis-rs Pipeline": "https://docs.rs/redis/latest/redis/struct.Pipeline.html",
        "Redis 官方 Commands": "https://redis.io/commands/",
        "redis-rs FromRedisValue": "https://docs.rs/redis/latest/redis/trait.FromRedisValue.html",
        "mongodb-rust-driver docs.rs": "https://docs.rs/mongodb/latest/mongodb/",
        "wasm-bindgen 源码, crates/macro-support/src/parser.rs": "https://github.com/rustwasm/wasm-bindgen/blob/main/crates/macro-support/src/parser.rs",
        # Bevy
        "Bevy Engine Official Docs — ECS Core Concepts": "https://bevyengine.org/learn/book/ecs/",
        "Bevy 0.15 Docs — System Ordering": "https://docs.rs/bevy/latest/bevy/",
        "Bevy Docs — States": "https://bevyengine.org/learn/book/states/",
        "Bevy Docs — Resources": "https://bevyengine.org/learn/book/resources/",
        "Bevy Community Discussions — When not to use ECS": "https://github.com/bevyengine/bevy/discussions/",
        "Game Programming Patterns — Command Pattern by Robert Nystrom": "https://gameprogrammingpatterns.com/command.html",
        # crates.io / 生态统计
        "Rust Crate Ecosystem Analysis · crates.io download statistics": "https://crates.io/",
        "crates.io download statistics · docs.rs API documentation": "https://crates.io/",
    }
    if s in exact:
        return f"[{s}]({exact[s]})"

    # ACM / IEEE 通用入口
    if s.startswith("ACM -"):
        return f"[{s}](https://dl.acm.org/)"
    if s.startswith("IEEE -"):
        return f"[{s}](https://ieeexplore.ieee.org/)"

    return None


def replace_bracketed_sources(text: str, index_link: str, method_link: str) -> str:
    """处理 [来源: ...] 占位符，支持一层嵌套方括号。"""
    result = []
    i = 0
    while i < len(text):
        m = re.search(r"\[来源[：:]\s*", text[i:])
        if not m:
            result.append(text[i:])
            break
        start = i + m.start()
        result.append(text[i:start])
        inner_start = i + m.end()
        # 查找匹配的 ]，允许一层嵌套 [ ... ]
        depth = 0
        pos = inner_start
        found = False
        while pos < len(text):
            ch = text[pos]
            if ch == "[":
                depth += 1
            elif ch == "]":
                if depth == 0:
                    found = True
                    break
                depth -= 1
            pos += 1
        if not found:
            result.append(text[start:])
            break
        content = text[inner_start:pos]
        whole = text[start : pos + 1]
        # 如果内容里已经有 ]( 链接，视为已映射
        if not LINK_RE.search(whole):
            label = content.strip()
            while label.startswith("[") and label.endswith("]"):
                label = label[1:-1].strip()
            new = transform_label(label, index_link, method_link)
            if not new:
                new = transform_exact(label)
            if new:
                result.append(new)
                i = pos + 1
                continue
        result.append(whole)
        i = pos + 1
    return "".join(result)


def fix_file(path: Path) -> int:
    text = path.read_text(encoding="utf-8", errors="ignore")
    original = text
    index_link = relative_path(path, INDEX_TARGET)
    method_link = relative_path(path, METHOD_TARGET)

    text = replace_bracketed_sources(text, index_link, method_link)

    def bare_repl(m):
        label = m.group(1)
        if LINK_RE.search(label):
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
