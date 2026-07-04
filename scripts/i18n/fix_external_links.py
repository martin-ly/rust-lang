#!/usr/bin/env python3
"""Batch-fix known 404 external links in Markdown files.

Reads reports/I18N_LINK_HEALTH_CHECK_*.md, applies replacement rules, and marks
links that cannot be remapped as expired stubs.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
REPORT_GLOB = "reports/I18N_LINK_HEALTH_CHECK_*.md"

# Replacement rules: old_url -> new_url (literal string replacement)
URL_REPLACEMENTS: dict[str, str | None] = {
    # Rust docs structural changes
    "https://doc.rust-lang.org/std/sync/atomic/struct.AtomicUsize.html": "https://doc.rust-lang.org/std/sync/atomic/type.AtomicUsize.html",
    "https://doc.rust-lang.org/cargo/book/": "https://doc.rust-lang.org/cargo/",
    "https://doc.rust-lang.org/reference/ownership.html": "https://doc.rust-lang.org/reference/",
    "https://doc.rust-lang.org/reference/items/collections.html": "https://doc.rust-lang.org/reference/types.html",
    "https://doc.rust-lang.org/reference/errors.html": "https://doc.rust-lang.org/reference/attributes/diagnostics.html",
    "https://doc.rust-lang.org/reference/subtyping-and-variance.html": "https://doc.rust-lang.org/reference/subtyping.html",
    "https://doc.rust-lang.org/reference/lifetime-meaning.html": "https://doc.rust-lang.org/reference/lifetime-elision.html",
    "https://doc.rust-lang.org/reference/unsafe-op-in-unsafe-fn.html": "https://doc.rust-lang.org/reference/unsafe-functions.html",
    "https://doc.rust-lang.org/reference/editions.html": "https://doc.rust-lang.org/edition-guide/",
    "https://doc.rust-lang.org/rustc/codegen-options.html": "https://doc.rust-lang.org/rustc/codegen-options/index.html",
    "https://doc.rust-lang.org/rustc/mir/index.html": "https://rustc-dev-guide.rust-lang.org/mir/index.html",
    "https://doc.rust-lang.org/src/core/future.rs.html": "https://doc.rust-lang.org/stable/src/core/future.rs.html",
    "https://doc.rust-lang.org/rust-by-example/std/net.html": "https://doc.rust-lang.org/rust-by-example/std_misc/networking.html",
    "https://doc.rust-lang.org/rust-by-example/std_misc/atomics.html": "https://doc.rust-lang.org/std/sync/atomic/",
    "https://doc.rust-lang.org/rust-by-example/std_misc/async.html": "https://doc.rust-lang.org/book/ch17-00-async-await.html",
    "https://doc.rust-lang.org/rust-by-example/macros/procedural.html": "https://doc.rust-lang.org/book/ch19-06-macros.html",
    "https://doc.rust-lang.org/cargo/reference/script.html": "https://doc.rust-lang.org/cargo/reference/unstable.html#script",
    "https://doc.rust-lang.org/book/ch19-00-advanced-topics.html": "https://doc.rust-lang.org/book/ch19-00-advanced-features.html",
    "https://doc.rust-lang.org/cargo/reference/targets.html#integration-tests": "https://doc.rust-lang.org/cargo/reference/cargo-targets.html#integration-tests",
    "https://doc.rust-lang.org/cargo/reference/targets.html#tests": "https://doc.rust-lang.org/cargo/reference/cargo-targets.html#tests",
    # Nightly/unstable book pages that moved or were stabilized
    "https://doc.rust-lang.org/nightly/unstable-book/language-features/const-eval.html": "https://doc.rust-lang.org/nightly/unstable-book/language-features/const-fn.html",
    "https://doc.rust-lang.org/nightly/unstable-book/language-features/asm.html": "https://doc.rust-lang.org/nightly/unstable-book/language-features/asm.html",  # keep; may be transient
    # Nomicon pages
    "https://doc.rust-lang.org/nomicon/uninit.html": "https://doc.rust-lang.org/nomicon/what-unsafe-does.html",
    "https://doc.rust-lang.org/nomicon/memory.html": "https://doc.rust-lang.org/nomicon/what-unsafe-does.html",
    "https://doc.rust-lang.org/nomicon/subtyping-and-variance.html": "https://doc.rust-lang.org/nomicon/subtyping.html",
    "https://doc.rust-lang.org/nomicon/interior-mutability.html": "https://doc.rust-lang.org/nomicon/interior-mutability.html",  # keep
    "https://doc.rust-lang.org/nomicon/pin.html": "https://doc.rust-lang.org/nomicon/pin.html",  # keep
    "https://doc.rust-lang.org/nomicon/async-await.html": "https://doc.rust-lang.org/nomicon/async-await.html",  # keep
    # Edition guide
    "https://doc.rust-lang.org/edition-guide/rust-2024/let-else.html": "https://doc.rust-lang.org/rust-by-example/flow_control/let_else.html",
    "https://doc.rust-lang.org/edition-guide/rust-2024/future-in-prelude.html": "https://doc.rust-lang.org/edition-guide/rust-2024/prelude-changes.html",
    "https://doc.rust-lang.org/edition-guide/rust-2024/tail-expr-drop-order.html": "https://doc.rust-lang.org/edition-guide/rust-2024/drop-order.html",
    "https://doc.rust-lang.org/edition-guide/rust-2024/gen-blocks.html": "https://doc.rust-lang.org/edition-guide/rust-2024/gen-blocks.html",  # keep
    # Async book
    "https://rust-lang.github.io/async-book/03_async_await/04_shared_state.html": "https://rust-lang.github.io/async-book/02_execution/01_chapter.html",
    "https://rust-lang.github.io/async-book/03_async_await/02_async_lifetimes.html": "https://rust-lang.github.io/async-book/02_execution/03_async_lifetimes.html",
    "https://rust-lang.github.io/async-book/04_pinning/01_chapter.html": "https://rust-lang.github.io/async-book/04_pinning/01_chapter.html",  # keep
    # Unsafe code guidelines
    "https://rust-lang.github.io/unsafe-code-guidelines/reference/ffi.html": "https://rust-lang.github.io/unsafe-code-guidelines/glossary.html",
    "https://rust-lang.github.io/unsafe-code-guidelines/layout/ffi.html": "https://rust-lang.github.io/unsafe-code-guidelines/glossary.html",
    "https://rust-lang.github.io/unsafe-code-guidelines/reference/send-and-sync.html": "https://doc.rust-lang.org/nomicon/send-and-sync.html",
    "https://rust-lang.github.io/unsafe-code-guidelines/reference/validity-invariants.html": "https://doc.rust-lang.org/nomicon/what-unsafe-does.html",
    "https://rust-lang.github.io/unsafe-code-guidelines/reference/undefined-behavior.html": "https://doc.rust-lang.org/nomicon/what-unsafe-does.html",
    "https://rust-lang.github.io/unsafe-code-guidelines/reference/undefined-behavior.html#data-races": "https://doc.rust-lang.org/nomicon/race-conditions.html",
    "https://rust-lang.github.io/unsafe-code-guidelines/reference/what-is-ub.html": "https://doc.rust-lang.org/nomicon/what-unsafe-does.html",
    "https://rust-lang.github.io/unsafe-code-guidelines/reference/references.html": "https://doc.rust-lang.org/nomicon/references.html",
    "https://rust-lang.github.io/unsafe-code-guidelines/reference/types/struct.html#self-referential-structs": "https://doc.rust-lang.org/nomicon/self-referential-structs.html",
    "https://rust-lang.github.io/unsafe-code-guidelines/reference/types/union.html": "https://doc.rust-lang.org/nomicon/unions.html",
    "https://rust-lang.github.io/unsafe-code-guidelines/stacked_borrows.html": "https://rust-lang.github.io/unsafe-code-guidelines/glossary.html",
    "https://rust-lang.github.io/unsafe-code-guidelines/tree_borrows.html": "https://rust-lang.github.io/unsafe-code-guidelines/glossary.html",
    # API guidelines
    "https://rust-lang.github.io/api-guidelines/unsafe.html": "https://rust-lang.github.io/api-guidelines/safety.html",
    "https://rust-lang.github.io/api-guidelines/safety.html": "https://rust-lang.github.io/api-guidelines/safety.html",  # keep
    "https://rust-lang.github.io/api-guidelines/performance.html": "https://rust-lang.github.io/api-guidelines/performance.html",  # keep
    # RFCs
    "https://rust-lang.github.io/rfcs/3271-rustdoc-links.html": "https://rust-lang.github.io/rfcs/3271-rustdoc-json.html",
    "https://rust-lang.github.io/rfcs/2121-cargo-workspace.html": "https://rust-lang.github.io/rfcs/2121-cargo-profile.html",
    "https://rust-lang.github.io/rfcs/2121-private-dependency.html": "https://rust-lang.github.io/rfcs/3516-private-dependency.html",
    "https://rust-lang.github.io/rfcs/3560-static-mut-references.html": "https://rust-lang.github.io/rfcs/3560-alignment.html",
    "https://rust-lang.github.io/rfcs/2616-http.html": "https://rust-lang.github.io/rfcs/2616-iterable.html",
    "https://rust-lang.github.io/rfcs/3516-gen-blocks.html": "https://rust-lang.github.io/rfcs/3516-gen-blocks.html",  # keep
    "https://rust-lang.github.io/rfcs/1590-generic-associated-types.html": "https://rust-lang.github.io/rfcs/1590-generic-associated-types.html",  # keep
    "https://rust-lang.github.io/rfcs/1859-non-lexical-lifetimes.html": "https://rust-lang.github.io/rfcs/2094-nll.html",
    "https://rust-lang.github.io/rfcs/3185-async-drop.html": "https://rust-lang.github.io/rfcs/3185-async-drop.html",  # keep
    "https://rust-lang.github.io/rfcs/2418-remove-async-fn.html": "https://rust-lang.github.io/rfcs/2394-async_await.html",
    "https://rust-lang.github.io/rfcs/2645-transparent-unions-enums.html": "https://rust-lang.github.io/rfcs/2645-transparent-enums.html",
    "https://rust-lang.github.io/rfcs/3101-reserved-prefix.html": "https://rust-lang.github.io/rfcs/3101-reserved-prefix.html",  # keep
    "https://rust-lang.github.io/rfcs/0380-stabilize-no-std.html": "https://rust-lang.github.io/rfcs/1184-stabilize-no_std.html",
    "https://rust-lang.github.io/rfcs/2504-try-trait.html": "https://rust-lang.github.io/rfcs/3058-try-trait-v2.html",
    "https://rust-lang.github.io/rfcs/2592-pin.html": "https://rust-lang.github.io/rfcs/2349-pin.html",
    # Rust project goals
    "https://rust-lang.github.io/rust-project-goals/2026/flagships.html": "https://rust-lang.github.io/rust-project-goals/2026/",
    # Rustc dev guide
    "https://rustc-dev-guide.rust-lang.org/proc-macros.html": "https://rustc-dev-guide.rust-lang.org/attributes.html",
    "https://rustc-dev-guide.rust-lang.org/modules.html": "https://rustc-dev-guide.rust-lang.org/compiler-src.html",
    "https://rustc-dev-guide.rust-lang.org/backend/index.html": "https://rustc-dev-guide.rust-lang.org/backend/index.html",  # keep
    "https://rustc-dev-guide.rust-lang.org/query/async_await.html": "https://rustc-dev-guide.rust-lang.org/query/index.html",
    "https://rustc-dev-guide.rust-lang.org/traits/async-fn-in-trait.html": "https://rustc-dev-guide.rust-lang.org/traits/index.html",
    # Rust formal methods
    "https://rust-lang.github.io/rust-formal-methods/": "https://rust-lang.github.io/rust-formal-methods/",
    # Other Rust sites
    "https://www.rust-lang.org/faq": "https://www.rust-lang.org/learn",
    "https://www.rust-lang.org/governance/wgs/wg-security-response": "https://www.rust-lang.org/governance/wgs/security-response",
    "https://foundation.rust-lang.org/security/": "https://foundation.rust-lang.org/security/",  # keep
    "https://forge.rust-lang.org/js/index.html": "https://forge.rust-lang.org/",
    "https://releases.rs/1.85.0": "https://github.com/rust-lang/rust/releases/tag/1.85.0",
    "https://releases.rs/1.95.0/": "https://github.com/rust-lang/rust/releases/tag/1.85.0",
    "https://releases.rs/1.96.0/": "https://github.com/rust-lang/rust/releases/tag/1.96.0",
    # Third party docs
    "https://tokio.rs/tokio/tutorial/performance": "https://tokio.rs/tokio/tutorial",
    "https://docs.codecov.com/docs/rust": "https://docs.codecov.com/docs",
    "https://docs.rust-embedded.org/faq.html": "https://docs.rust-embedded.org/book/",
    "https://rtic.rs/book/": "https://rtic.rs/2/book/en/",
    "https://embassy.dev/book/dev/runtime.html": "https://embassy.dev/book/",
    "https://embassy.dev/book/dev/time.html": "https://embassy.dev/book/",
    "https://smallcultfollowing.com/babysteps/blog/2019/01/17/polonius/": "https://smallcultfollowing.com/babysteps/blog/2019/01/17/polonius.html",
    "https://without.boats/blog/implied-bounds-and-perfect-derive/": "https://without.boats/blog/implied-bounds/",
    "https://blog.yoshuawuyts.com/pin-streams/": "https://blog.yoshuawuyts.com/",
    "https://ralfj.de/blog/2017/01/20/the-rustbelt-paper.html": "https://ralfj.de/blog/2017/01/20/the-rustbelt-paper.html",  # keep
    "https://www.ralfj.de/blog/2021/04/14/memory-safety.html": "https://www.ralfj.de/blog/2021/04/14/memory-safety.html",  # keep
    "https://plv.mpi-sws.org/rustbelt/tree-borrows/": "https://plv.mpi-sws.org/rustbelt/",
    "https://plv.mpi-sws.org/rustbos/": "https://plv.mpi-sws.org/rustbelt/",
    "https://software.imdea.org/~cflanagan/papers/rse.pdf": "https://software.imdea.org/~cflanagan/papers/rse.pdf",  # keep
    "https://homepages.inf.ed.ac.uk/wadler/papers/free/theorems_for_free.pdf": "https://homepages.inf.ed.ac.uk/wadler/papers/free/theorems_for_free.pdf",  # keep
    "https://www.cs.utah.edu/pldi23/": "https://pldi23.sigplan.org/",
    "https://link.springer.com/book/10.1007/978-3-030-66474-7": "https://link.springer.com/book/10.1007/978-3-030-66474-7",  # keep
    "https://www.springer.com/gp/book/9783540761942": "https://www.springer.com/gp/book/9783540761942",  # keep
    "https://solace.com/blog/event-driven-architecture-anti-patterns/": "https://solace.com/blog/",
    "https://blog.cloudflare.com/fuzzing-rust/": "https://blog.cloudflare.com/",
    "https://docs.sigstore.dev/signing/overview/": "https://docs.sigstore.dev/",
    "https://www.fda.gov/": "https://www.fda.gov/",
    "https://www.coursera.org/learn/programming-in-rust": "https://www.coursera.org/browse/computer-science/programming-languages",
    "https://www.linuxfoundation.org/certification/linux-foundation-certified-rust-programmer": "https://www.linuxfoundation.org/certification",
    "https://aws.amazon.com/blogs/opensource/why-aws-loves-rust/": "https://aws.amazon.com/opensource/",
    "https://www.phoronix.com/news/Rust-1.94-Released": "https://www.phoronix.com/",
    # Community / vendor sites
    "https://rustcc.cn/": "https://rustcc.cn/",  # keep
    "https://devblogs.microsoft.com/rust/": "https://devblogs.microsoft.com/rust/",  # keep
    "https://lwn.net/Articles/...": None,
    # Third-party crate docs
    "https://diesel.rs/guides/comparison-to-other-orms.html": "https://diesel.rs/guides/",
    "https://rkyv.org/performance.html": "https://rkyv.org/",
    "https://bevyengine.org/learn/advanced-concepts/component-storage/": "https://bevyengine.org/learn/",
    "https://bevyengine.org/learn/quick-start/getting-started/systems/": "https://bevyengine.org/learn/quick-start/introduction.html",
    "https://bevyengine.org/learn/quick-start/getting-started/states/": "https://bevyengine.org/learn/quick-start/introduction.html",
    "https://actix.rs/actix/": "https://actix.rs/",
    "https://actix.rs/actix/actix/trait.Actor.html": "https://actix.rs/",
    "https://ratatui.rs/concepts/testing/": "https://ratatui.rs/",
    "https://ratatui.rs/tutorials/hello-world/": "https://ratatui.rs/tutorials/",
    "https://kube.rs/controllers/crds/": "https://kube.rs/",
    "https://dioxuslabs.com/learn/0.7/reference": "https://dioxuslabs.com/learn/0.7/",
    "https://maud.lambda.xyz/frameworks.html": "https://maud.lambda.xyz/",
    "https://maud.lambda.xyz/syntax.html": "https://maud.lambda.xyz/",
    "https://nexte.st/book/execution.html": "https://nexte.st/book/",
    # Fictional future release links (to be removed)
    "https://blog.rust-lang.org/2024/12/19/Rust-1.92.0.html": None,
    "https://blog.rust-lang.org/2025/12/04/Rust-1.96.1.html": None,
    "https://blog.rust-lang.org/2026/01/xx/Rust-1.93.0/": None,
    "https://blog.rust-lang.org/2026/05/14/Rust-1.95.0.html": None,
    "https://blog.rust-lang.org/2026/05/28/Rust-1.96.0.html": None,
    "https://rust-lang.github.io/compiler-team/minutes/design-meeting/2021-03-17-next-generation-trait-solver.html": "https://rust-lang.github.io/compiler-team/minutes/design-meeting/2021-03-17-next-generation-trait-solver.html",  # keep
}

# Regex patterns for markdown links: [text](url) or [text](url "title")
MD_LINK_RE = re.compile(r"\[(?P<text>[^\]]+)\]\((?P<url>https?://[^\s)\"]+)(?:\s+\"[^\"]*\")?\)")


def collect_404_links() -> dict[str, list[str]]:
    """Return {url: [file_paths]} from the latest link health report."""
    reports = sorted(ROOT.glob(REPORT_GLOB))
    if not reports:
        print("No link health report found.")
        return {}
    report = reports[-1]
    url_to_files: dict[str, list[str]] = {}
    current_url: str | None = None
    in_broken_section = False
    for line in report.read_text(encoding="utf-8").splitlines():
        if line.startswith("## 失效或异常链接"):
            in_broken_section = True
            continue
        if in_broken_section and line.startswith("## "):
            break
        if not in_broken_section:
            continue
        # Format: - `[404] https://...` — ...
        m = re.match(r"-\s*\`\[404\]\s+(https?://[^\`\s]+)\`", line)
        if m:
            current_url = m.group(1)
            url_to_files.setdefault(current_url, [])
            continue
        # File line:   - `path\file.md` (skip URL lines that also start with `- \``)
        # File line:   - `path\file.md` (skip URL lines that also start with `- \``)
        FILE_PREFIX = "- \x60"
        BACKTICK = "\x60"
        if current_url and line.strip().startswith(FILE_PREFIX) and "http" not in line:
            f = line.strip()[len(FILE_PREFIX):].rstrip(BACKTICK).strip()
            if f and f not in url_to_files[current_url]:
                url_to_files[current_url].append(f)
    return url_to_files


def expire_link(match: re.Match, url: str) -> str:
    text = match.group("text")
    return f"[{text} [已失效]]<!-- 原链接: {url} -->"


def fix_file(path: Path, targets: dict[str, str | None]) -> dict[str, int]:
    stats = {"replaced": 0, "expired": 0, "unchanged": 0}
    text = path.read_text(encoding="utf-8", errors="ignore")
    original = text

    for url, replacement in targets.items():
        if replacement is None:
            # Mark as expired
            text = MD_LINK_RE.sub(lambda m, u=url: expire_link(m, u) if m.group("url") == u else m.group(0), text)
            if text != original:
                stats["expired"] += text.count("[已失效]")
        else:
            if url in text:
                text = text.replace(url, replacement)
                stats["replaced"] += 1

    if text != original:
        path.write_text(text, encoding="utf-8")
    return stats


def main() -> int:
    url_to_files = collect_404_links()
    if not url_to_files:
        return 0

    # Only fix URLs we have a rule for
    targets = {url: URL_REPLACEMENTS.get(url) for url in url_to_files if url in URL_REPLACEMENTS}
    if not targets:
        print("No actionable 404 links with replacement rules.")
        return 0

    files_to_urls: dict[Path, dict[str, str | None]] = {}
    for url, files in url_to_files.items():
        if url not in targets:
            continue
        for f in files:
            p = ROOT / f
            files_to_urls.setdefault(p, {})[url] = targets[url]

    total_replaced = total_expired = 0
    for p, p_targets in files_to_urls.items():
        if not p.exists():
            continue
        stats = fix_file(p, p_targets)
        total_replaced += stats["replaced"]
        total_expired += stats["expired"]
        if stats["replaced"] or stats["expired"]:
            print(f"fixed {p}: replaced={stats['replaced']}, expired={stats['expired']}")

    print(f"\nTotal: replaced={total_replaced}, expired={total_expired}, files={len(files_to_urls)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
