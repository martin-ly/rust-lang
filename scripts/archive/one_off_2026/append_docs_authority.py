#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""对 docs/research_notes 中『无 P0/P1/P2 权威 URL』的文件，文末追加主题化权威来源小节。

只追加（idempotent：已含『## 权威来源』则跳过），不删/改正文。URL 取自 concept 已核验
的 authority_source_map 映射与 P0/P1/P2 官方/生态域，不虚构。--dry-run 预览。
"""
from __future__ import annotations

import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DRY = "--dry-run" in sys.argv

# 主题关键词 -> 权威来源小节（绝对 URL，命中 P0/P1/P2 域）
THEMES = [
    (["borrow_checker", "ownership_safety", "lifetimes"],
     [("P0 官方 — TRPL Ch4 Ownership", "https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html"),
      ("P0 官方 — TRPL Ch10 Lifetimes", "https://doc.rust-lang.org/book/ch10-03-lifetime-syntax.html"),
      ("P0 Reference", "https://doc.rust-lang.org/reference/"),
      ("P0 Nomicon", "https://doc.rust-lang.org/nomicon/"),
      ("P1 RustBelt / Stacked & Tree Borrows (Jung et al.)", "https://plv.mpi-sws.org/rustbelt/")]),
    (["concurrency_models"],
     [("P0 官方", "https://doc.rust-lang.org/book/ch16-00-concurrency.html"),
      ("P0 Reference — Send/Sync", "https://doc.rust-lang.org/reference/"),
      ("P0 Nomicon — Concurrency", "https://doc.rust-lang.org/nomicon/"),
      ("P1 RustBelt — Data Race Freedom", "https://plv.mpi-sws.org/rustbelt/"),
      ("P2 tokio", "https://docs.rs/tokio/")]),
    (["type_system"],
     [("P0 Reference — Types", "https://doc.rust-lang.org/reference/types.html"),
      ("P0 RFCs", "https://rust-lang.github.io/rfcs/"),
      ("P1 TAPL (Pierce)", "https://www.cis.upenn.edu/~bcpierce/tapl/")]),
    (["tokio_architecture"],
     [("P2 tokio (docs.rs)", "https://docs.rs/tokio/"),
      ("P2 tokio 官方", "https://tokio.rs/"),
      ("P0 Reference", "https://doc.rust-lang.org/reference/")]),
    (["axum_architecture"],
     [("P2 axum (docs.rs)", "https://docs.rs/axum/"),
      ("P2 tokio (docs.rs)", "https://docs.rs/tokio/"),
      ("P2 hyper (docs.rs)", "https://docs.rs/hyper/")]),
    (["sqlx_architecture", "sqlx_advanced"],
     [("P2 SQLx (docs.rs)", "https://docs.rs/sqlx/"),
      ("P2 SQLx 官方", "https://github.com/launchbadge/sqlx"),
      ("P2 SeaQL", "https://www.sea-ql.org/")]),
    (["distributed_patterns_matrix"],
     [("P2 Microservices Patterns", "https://microservices.io/patterns/"),
      ("P0 Reference", "https://doc.rust-lang.org/reference/"),
      ("P2 docs.rs", "https://docs.rs/")]),
    (["workflow_engine_matrix"],
     [("P2 Microservices / Workflow", "https://microservices.io/"),
      ("P2 Temporal", "https://docs.temporal.io/"),
      ("P0 Reference", "https://doc.rust-lang.org/reference/")]),
]

TARGETS = [
    "docs/research_notes/10_distributed_patterns_matrix.md",
    "docs/research_notes/10_tutorial_borrow_checker.md",
    "docs/research_notes/10_tutorial_concurrency_models.md",
    "docs/research_notes/10_tutorial_lifetimes.md",
    "docs/research_notes/10_tutorial_ownership_safety.md",
    "docs/research_notes/10_tutorial_type_system.md",
    "docs/research_notes/10_workflow_engine_matrix.md",
    "docs/research_notes/software_design_theory/07_crate_architectures/06_tokio_architecture.md",
    "docs/research_notes/software_design_theory/07_crate_architectures/07_axum_architecture.md",
    "docs/research_notes/software_design_theory/07_crate_architectures/09_sqlx_architecture.md",
    "docs/research_notes/software_design_theory/07_crate_architectures/15_sqlx_advanced_architecture.md",
]


def pick_theme(name):
    base = os.path.basename(name).lower()
    for keys, refs in THEMES:
        if any(k in base for k in keys):
            return refs
    return [("P0 Reference", "https://doc.rust-lang.org/reference/")]


def section(refs):
    lines = ["", "---", "", "## 权威来源（References · 国际权威对齐）", "",
             "> 仅追加来源链接以闭合权威覆盖，不改本文正文；通用概念请以 `concept/` 权威页为准（AGENTS.md §2）。", ""]
    for label, url in refs:
        lines.append(f"- **{label}**: <{url}>")
    lines.append("")
    return "\n".join(lines)


def main():
    done = skipped = 0
    for rel in TARGETS:
        p = os.path.join(ROOT, rel.replace("/", os.sep))
        if not os.path.exists(p):
            print(f"  MISS {rel}"); continue
        t = open(p, encoding="utf-8", errors="ignore").read()
        if "## 权威来源" in t or "## References" in t or "权威来源（References" in t:
            print(f"  skip(has-refs) {rel}"); skipped += 1; continue
        refs = pick_theme(rel)
        sec = section(refs)
        print(f"  {'DRY ' if DRY else ''}append {rel}  (+{len(refs)} refs)")
        if not DRY:
            open(p, "w", encoding="utf-8", newline="\n").write(t.rstrip() + "\n" + sec)
        done += 1
    print(f"[append-docs-authority] appended={done} skipped={skipped} dry={DRY}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
