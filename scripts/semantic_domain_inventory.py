#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
scripts/semantic_domain_inventory.py

P10-1 语义领域盘点脚本。
扫描 concept/**/*.md，按语义领域分类，抽取元数据、国际权威来源、思维表征，
并与嵌入式 P10 预期清单对比，输出 JSON 盘点、Markdown 矩阵与 stdout 摘要。

仅使用 Python 标准库。
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any


CONCEPT_ROOT = Path("concept")
TMP_DIR = Path("tmp")
OUT_JSON = TMP_DIR / "semantic_domain_inventory.json"
OUT_MATRIX = TMP_DIR / "semantic_domain_matrix.md"

# ---------------------------------------------------------------------------
# 语义领域定义
# ---------------------------------------------------------------------------
DOMAIN_LABELS: dict[str, str] = {
    "ownership_borrow_lifetime": "所有权 / 借用 / 生命周期",
    "type_system": "类型系统",
    "traits": "Trait 系统",
    "generics": "泛型",
    "macros": "宏与元编程",
    "concurrency_async": "并发 / 异步 / 并行",
    "unsafe_ffi": "Unsafe / FFI / 底层",
    "embedded_no_std": "嵌入式 / no_std / 裸机",
    "error_handling": "错误处理",
    "performance_zero_cost": "性能 / 零成本抽象",
    "formal_methods": "形式方法 / 计算语义模型",
    "ecosystem_toolchain": "生态 / 工具链 / 惯用法",
    "enterprise_architecture": "企业架构 / 标准",
    "meta_navigation": "元数据 / 导航 / RAG",
}

SOURCE_CATEGORIES: dict[str, dict[str, list[str]]] = {
    "official_docs": {
        "label": "官方文档",
        "urls": [
            r"doc\.rust-lang\.org/book",
            r"doc\.rust-lang\.org/reference",
            r"doc\.rust-lang\.org/nomicon",
            r"doc\.rust-lang\.org/rust-by-example",
            r"doc\.rust-lang\.org/edition-guide",
            r"rust-lang\.github\.io/async-book",
            r"rust-lang\.github\.io/rfcs",
            r"doc\.rust-lang\.org/std",
            r"doc\.rust-lang\.org/cargo",
            r"rust-lang\.github\.io/api-guidelines",
            r"rust-lang\.github\.io/unsafe-code-guidelines",
            r"rustc-dev-guide\.rust-lang\.org",
            r"doc\.rust-lang\.org/rustdoc",
            r"doc\.rust-lang\.org/rustc",
        ],
        "tokens": [],
    },
    "formal_verification": {
        "label": "形式化 / 验证工具",
        "urls": [
            r"plv\.mpi-sws\.org/rustbelt",
            r"github\.com/RalfJung",
            r"github\.com/AeneasVerif",
            r"verus-lang\.github\.io",
            r"model-checking\.github\.io/kani",
            r"github\.com/rust-lang/miri",
            r"flux-rs\.github\.io",
            r"creusot-rs\.github\.io",
            r"pm\.inf\.ethz\.ch/research/prusti",
            r"iris-project\.org",
            r"github\.com/rust-lang/a-mir-formality",
            r"minirust",
        ],
        "tokens": ["rustbelt", "aeneas", "verus", "kani", "miri", "flux", "creusot", "prusti", "iris", "a-mir-formality", "minirust", "borrow sanitizer"],
    },
    "embedded_safety": {
        "label": "嵌入式 / 安全关键",
        "urls": [
            r"doc\.rust-lang\.org/embedded-book",
            r"docs\.rust-embedded\.org",
            r"ferrocene\.dev",
            r"ferrous-systems\.com",
            r"rustfoundation\.org/safety-critical",
            r"github\.com/embassy-rs/embassy",
            r"rtic\.rs",
            r"github\.com/oxidecomputer/hubris",
            r"github\.com/tock/tock",
            r"docs\.rs/cortex-m",
            r"docs\.rs/riscv-rt",
            r"github\.com/knurling-rs/probe-rs",
            r"github\.com/knurling-rs/flip-link",
            r"arxiv\.org/html/2605\.23490",
            r"developer\.arm\.com",
            r"docs\.kernel\.org/rust",
        ],
        "tokens": ["embedded rust book", "embedonomicon", "ferrocene", "embassy", "rtic", "hubris", "tock", "cortex-m", "riscv-rt", "probe-rs", "flip-link", "misra-rust", "safety-critical rust", "rust for linux", "bare metal"],
    },
    "industrial_ecosystem": {
        "label": "工业生态库",
        "urls": [
            r"tokio\.rs",
            r"docs\.rs/tokio",
            r"actix\.rs",
            r"docs\.rs/axum",
            r"serde\.rs",
            r"docs\.rs/serde",
            r"docs\.rs/anyhow",
            r"docs\.rs/thiserror",
            r"docs\.rs/tracing",
            r"docs\.rs/clap",
            r"docs\.rs/reqwest",
            r"github\.com/hyperium/tonic",
            r"github\.com/quinn-rs/quinn",
            r"docs\.rs/crossbeam",
            r"docs\.rs/rayon",
            r"docs\.rs/parking_lot",
            r"sea-ql\.org",
            r"github\.com/launchbadge/sqlx",
            r"diesel\.rs",
            r"bevyengine\.org",
            r"wgpu\.rs",
            r"tauri\.app",
            r"dioxuslabs\.com",
            r"leptos\.dev",
            r"egui\.rs",
            r"iced\.rs",
            r"rust-bindgen",
            r"cbindgen",
            r"pyo3\.rs",
            r"wasm-bindgen",
            r"github\.com/briansmith/ring",
            r"github\.com/rustls/rustls",
        ],
        "tokens": ["tokio", "serde", "anyhow", "thiserror", "tracing", "clap", "reqwest", "tonic", "quinn", "crossbeam", "rayon", "sqlx", "diesel", "bevy", "wgpu", "tauri", "dioxus", "leptos", "egui", "iced", "bindgen", "pyo3", "wasm-bindgen", "ring", "rustls"],
    },
    "design_patterns_perf": {
        "label": "设计模式 / 性能 / 惯用法",
        "urls": [
            r"rust-unofficial\.github\.io/patterns",
            r"nnethercote\.github\.io/perf-book",
            r"zero2prod\.com",
            r"lurklurk\.org/effective-rust",
            r"manning\.com/books/idiomatic-rust",
            r"docs\.rs/scopeguard",
        ],
        "tokens": ["rust design patterns", "rust performance book", "zero to production", "effective rust", "idiomatic rust", "scopeguard"],
    },
    "academic": {
        "label": "学术论文",
        "urls": [
            r"doi\.org",
            r"arxiv\.org",
            r"cis\.upenn\.edu/~bcpierce/tapl",
            r"softwarefoundations\.cis\.upenn\.edu",
            r"cl\.cam\.ac\.uk/~gw104",
            r"dl\.acm\.org",
            r"research\.pm\.inf\.ethz\.ch/prusti",
        ],
        "tokens": ["tapl", "software foundations", "winskel", "wadler", "herlihy", "reynolds", "theorems for free", "types abstraction and parametric polymorphism", "art of multiprocessor programming"],
    },
    "standards_enterprise": {
        "label": "标准 / 企业架构",
        "urls": [
            r"iso\.org/standard",
            r"ieee\.org/standard",
            r"opengroup\.org/togaf",
            r"cmmiinstitute\.com",
            r"c4model\.com",
            r"adr\.github\.io",
            r"incose\.org",
            r"omgsysml\.org",
            r"omg\.org/spec",
            r"webstore\.iec\.ch",
            r"rtca\.org/product/do-178c",
            r"misra\.org\.uk",
        ],
        "tokens": ["togaf", "cmmi", "iso/iec", "ieee", "incose", "sysml", "do-178c", "misra c", "iso 26262", "iec 61508", "42010"],
    },
    "community_blog": {
        "label": "社区博客 / 演讲",
        "urls": [
            r"smallcultfollowing\.com",
            r"tokio\.rs/blog",
            r"without\.boats",
            r"thesquareplanet\.com",
            r"ralfj\.de",
            r"github\.com/dtolnay",
        ],
        "tokens": ["niko matsakis", "carl lerche", "without boats", "jon gjengset", "ralf jung", "dtolnay"],
    },
}

# ---------------------------------------------------------------------------
# 预期主题清单（P10 优先级 + 核心域基线）
# ---------------------------------------------------------------------------
EXPECTED_TOPICS: list[dict[str, Any]] = [
    # embedded / no_std
    {"group": "embedded_no_std", "domain": "embedded_no_std", "topic": "no_std allocators / panic handlers", "keywords": ["allocator", "panic handler", "global_allocator", "#[panic_handler]"], "priority": "P0", "source": "The Embedonomicon / Embedded Rust Book", "target": "concept/06_ecosystem/05_systems_and_embedded/52_no_std_allocators_and_panic_handlers.md"},
    {"group": "embedded_no_std", "domain": "embedded_no_std", "topic": "critical sections & sync on bare metal", "keywords": ["critical section", "bare metal sync", "cortex-m-interrupt", "critical-section"], "priority": "P0", "source": "cortex-m / critical-section crate / Rust Atomics and Locks", "target": "concept/06_ecosystem/05_systems_and_embedded/53_critical_sections_and_sync_on_bare_metal.md"},
    {"group": "embedded_no_std", "domain": "embedded_no_std", "topic": "linker scripts & memory layout", "keywords": ["linker script", "memory.x", "scatter file", "memory layout"], "priority": "P0", "source": "The Embedonomicon / ARM scatter files", "target": "concept/06_ecosystem/05_systems_and_embedded/54_linker_scripts_and_memory_layout.md"},
    {"group": "embedded_no_std", "domain": "embedded_no_std", "topic": "RTIC vs Embassy real-time frameworks", "keywords": ["rtic", "embassy", "real-time framework"], "priority": "P0", "source": "RTIC Book / Embassy docs", "target": "concept/06_ecosystem/05_systems_and_embedded/55_rtic_vs_embassy_real_time_frameworks.md"},
    {"group": "embedded_no_std", "domain": "embedded_no_std", "topic": "Rust for Linux kernel module basics", "keywords": ["rust for linux", "kernel module", "linux kernel rust"], "priority": "P1", "source": "Rust for Linux / kernel docs", "target": "concept/06_ecosystem/05_systems_and_embedded/56_rust_for_linux_kernel_module_basics.md"},

    # idioms / patterns / architecture
    {"group": "idioms_patterns_architecture", "domain": "ecosystem_toolchain", "topic": "iterator chains", "keywords": ["iterator chain", "iterator patterns"], "priority": "P1", "source": "std::iter / Rust Design Patterns", "target": "concept/05_comparative/05_idioms_patterns_architecture/01_idioms/01_iterator_chains.md"},
    {"group": "idioms_patterns_architecture", "domain": "ecosystem_toolchain", "topic": "error propagation / ? operator", "keywords": ["? operator", "error propagation", "try operator"], "priority": "P1", "source": "TRPL Ch.9 / Rust Design Patterns", "target": "concept/05_comparative/05_idioms_patterns_architecture/01_idioms/02_error_propagation.md"},
    {"group": "idioms_patterns_architecture", "domain": "ecosystem_toolchain", "topic": "Into / From / AsRef", "keywords": ["into/from", "asref", "from trait"], "priority": "P1", "source": "std docs / API Guidelines", "target": "concept/05_comparative/05_idioms_patterns_architecture/01_idioms/03_into_from_asref.md"},
    {"group": "idioms_patterns_architecture", "domain": "ecosystem_toolchain", "topic": "Newtype", "keywords": ["newtype"], "priority": "P1", "source": "Rust Design Patterns", "target": "concept/05_comparative/05_idioms_patterns_architecture/01_idioms/04_newtype.md"},
    {"group": "idioms_patterns_architecture", "domain": "ecosystem_toolchain", "topic": "Typestate", "keywords": ["typestate"], "priority": "P1", "source": "Rust Design Patterns / Strom & Yemini 1986", "target": "concept/05_comparative/05_idioms_patterns_architecture/01_idioms/05_typestate.md"},
    {"group": "idioms_patterns_architecture", "domain": "ecosystem_toolchain", "topic": "RAII / defer / scope guard", "keywords": ["raii", "scope guard", "deferred cleanup", "defer"], "priority": "P1", "source": "Rustonomicon / scopeguard crate", "target": "concept/05_comparative/05_idioms_patterns_architecture/01_idioms/06_raii_cleanup.md"},
    {"group": "idioms_patterns_architecture", "domain": "ecosystem_toolchain", "topic": "Strategy pattern", "keywords": ["strategy pattern"], "priority": "P2", "source": "GoF / Rust Design Patterns", "target": "concept/05_comparative/05_idioms_patterns_architecture/03_design_patterns/01_strategy.md"},
    {"group": "idioms_patterns_architecture", "domain": "ecosystem_toolchain", "topic": "Command pattern", "keywords": ["command pattern"], "priority": "P2", "source": "GoF / Rust Design Patterns", "target": "concept/05_comparative/05_idioms_patterns_architecture/03_design_patterns/02_command.md"},
    {"group": "idioms_patterns_architecture", "domain": "ecosystem_toolchain", "topic": "Visitor pattern", "keywords": ["visitor pattern"], "priority": "P2", "source": "GoF / Rust Design Patterns", "target": "concept/05_comparative/05_idioms_patterns_architecture/03_design_patterns/03_visitor.md"},
    {"group": "idioms_patterns_architecture", "domain": "ecosystem_toolchain", "topic": "State Machine pattern", "keywords": ["state machine"], "priority": "P2", "source": "Rust Design Patterns / typestate", "target": "concept/05_comparative/05_idioms_patterns_architecture/03_design_patterns/04_state_machine.md"},
    {"group": "idioms_patterns_architecture", "domain": "ecosystem_toolchain", "topic": "Builder pattern", "keywords": ["builder pattern", "builder"], "priority": "P2", "source": "Rust Design Patterns / API Guidelines", "target": "concept/05_comparative/05_idioms_patterns_architecture/01_idioms/07_builder.md"},
    {"group": "idioms_patterns_architecture", "domain": "ecosystem_toolchain", "topic": "Adapter pattern", "keywords": ["adapter pattern"], "priority": "P2", "source": "GoF / Rust Design Patterns", "target": "concept/05_comparative/05_idioms_patterns_architecture/03_design_patterns/05_adapter.md"},
    {"group": "idioms_patterns_architecture", "domain": "ecosystem_toolchain", "topic": "Decorator pattern", "keywords": ["decorator pattern"], "priority": "P2", "source": "GoF / Rust Design Patterns", "target": "concept/05_comparative/05_idioms_patterns_architecture/03_design_patterns/06_decorator.md"},
    {"group": "idioms_patterns_architecture", "domain": "ecosystem_toolchain", "topic": "Hexagonal / Clean Architecture", "keywords": ["hexagonal architecture", "clean architecture", "ports and adapters"], "priority": "P2", "source": "microservices.io / Rust enterprise architecture pages", "target": "concept/05_comparative/05_idioms_patterns_architecture/04_architecture/01_hexagonal_clean_architecture.md"},
    {"group": "idioms_patterns_architecture", "domain": "ecosystem_toolchain", "topic": "CQRS / Event Sourcing", "keywords": ["cqrs", "event sourcing"], "priority": "P2", "source": "microservices.io / eventstore", "target": "concept/05_comparative/05_idioms_patterns_architecture/04_architecture/02_cqrs_event_sourcing.md"},
    {"group": "idioms_patterns_architecture", "domain": "ecosystem_toolchain", "topic": "Microservices", "keywords": ["microservices"], "priority": "P2", "source": "microservices.io / AWS architecture patterns", "target": "concept/05_comparative/05_idioms_patterns_architecture/04_architecture/03_microservices.md"},
    {"group": "idioms_patterns_architecture", "domain": "ecosystem_toolchain", "topic": "Actor model", "keywords": ["actor pattern", "actor model"], "priority": "P2", "source": "Tokio actors / Rust Design Patterns", "target": "concept/05_comparative/05_idioms_patterns_architecture/04_architecture/04_actor.md"},
    {"group": "idioms_patterns_architecture", "domain": "ecosystem_toolchain", "topic": "Plugin system", "keywords": ["plugin system", "plugin_system"], "priority": "P3", "source": "Rust Design Patterns / libloading docs", "target": "concept/05_comparative/05_idioms_patterns_architecture/04_architecture/05_plugin_system.md"},
    {"group": "idioms_patterns_architecture", "domain": "ecosystem_toolchain", "topic": "Event bus", "keywords": ["event bus", "event_bus"], "priority": "P3", "source": "Rust async / tokio broadcast", "target": "concept/05_comparative/05_idioms_patterns_architecture/04_architecture/06_event_bus.md"},

    # formal computational models
    {"group": "formal_computational_models", "domain": "formal_methods", "topic": "linear logic & ownership", "keywords": ["linear logic"], "priority": "P1", "source": "RustBelt / Girard linear logic", "target": "concept/04_formal/11_computational_models/12_linear_logic_and_ownership.md"},
    {"group": "formal_computational_models", "domain": "formal_methods", "topic": "session types & Rust channels", "keywords": ["session type"], "priority": "P1", "source": "session-types literature / Wadler", "target": "concept/04_formal/11_computational_models/13_session_types_and_rust_channels.md"},
    {"group": "formal_computational_models", "domain": "formal_methods", "topic": "effect handlers & Rust limited effects", "keywords": ["effect handler"], "priority": "P1", "source": "effects-system RFC / ICFP literature", "target": "concept/04_formal/11_computational_models/14_effect_handlers_and_rust_limited_effects.md"},
    {"group": "formal_computational_models", "domain": "formal_methods", "topic": "refinement types & Flux", "keywords": ["refinement type", "flux"], "priority": "P1", "source": "Flux OOPSLA 2023", "target": "concept/04_formal/11_computational_models/15_refinement_types_and_flux.md"},
    {"group": "formal_computational_models", "domain": "formal_methods", "topic": "RustBelt ownership logic", "keywords": ["rustbelt"], "priority": "P0", "source": "RustBelt POPL 2018 / Iris", "target": "concept/04_formal/11_computational_models/16_rustbelt_ownership_logic.md"},
    {"group": "formal_computational_models", "domain": "formal_methods", "topic": "Aeneas verification pipeline", "keywords": ["aeneas"], "priority": "P1", "source": "Aeneas ICFP 2022 / Charon", "target": "concept/04_formal/11_computational_models/17_aeneas_verification_pipeline.md"},

    # RAG production
    {"group": "rag_production", "domain": "meta_navigation", "topic": "golden query set ≥200", "keywords": ["golden query"], "priority": "P2", "source": "P10 RAG evaluation plan", "target": "tools/kg_rag/golden_query_set_v1.json"},
    {"group": "rag_production", "domain": "meta_navigation", "topic": "embedding fine-tuning pipeline", "keywords": ["embedding fine-tun", "fine_tune_embedding"], "priority": "P2", "source": "SentenceTransformers / LoRA contrastive learning", "target": "tools/kg_rag/fine_tune_embedding.py"},
    {"group": "rag_production", "domain": "meta_navigation", "topic": "reranker / hybrid search", "keywords": ["reranker", "hybrid search"], "priority": "P2", "source": "BM25 + vector reranking literature", "target": "tools/kg_rag/hybrid_search.py"},

    # core baseline (used to keep coverage metric meaningful for well-populated domains)
    {"group": "core", "domain": "ownership_borrow_lifetime", "topic": "Ownership", "keywords": ["ownership"], "priority": "P0", "source": "TRPL / Reference", "target": "concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md"},
    {"group": "core", "domain": "ownership_borrow_lifetime", "topic": "Borrowing", "keywords": ["borrowing"], "priority": "P0", "source": "TRPL / Reference", "target": "concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md"},
    {"group": "core", "domain": "ownership_borrow_lifetime", "topic": "Lifetimes", "keywords": ["lifetimes"], "priority": "P0", "source": "TRPL / Reference", "target": "concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md"},
    {"group": "core", "domain": "type_system", "topic": "Type system basics", "keywords": ["type system"], "priority": "P0", "source": "TRPL / Reference", "target": "concept/01_foundation/02_type_system/01_type_system.md"},
    {"group": "core", "domain": "traits", "topic": "Traits", "keywords": ["traits"], "priority": "P0", "source": "TRPL / Reference", "target": "concept/02_intermediate/00_traits/01_traits.md"},
    {"group": "core", "domain": "generics", "topic": "Generics", "keywords": ["generics"], "priority": "P0", "source": "TRPL / Reference", "target": "concept/02_intermediate/01_generics/01_generics.md"},
    {"group": "core", "domain": "macros", "topic": "Macros", "keywords": ["macros"], "priority": "P0", "source": "Reference / Rustonomicon", "target": "concept/03_advanced/03_proc_macros/01_macros.md"},
    {"group": "core", "domain": "concurrency_async", "topic": "Concurrency", "keywords": ["concurrency"], "priority": "P0", "source": "TRPL / Rust Atomics and Locks", "target": "concept/03_advanced/00_concurrency/01_concurrency.md"},
    {"group": "core", "domain": "concurrency_async", "topic": "Async/Await", "keywords": ["async"], "priority": "P0", "source": "Async Book / Tokio", "target": "concept/03_advanced/01_async/01_async.md"},
    {"group": "core", "domain": "unsafe_ffi", "topic": "Unsafe Rust", "keywords": ["unsafe rust"], "priority": "P0", "source": "Rustonomicon / Reference", "target": "concept/03_advanced/02_unsafe/01_unsafe.md"},
    {"group": "core", "domain": "unsafe_ffi", "topic": "FFI", "keywords": ["ffi"], "priority": "P0", "source": "Rustonomicon / Reference", "target": "concept/03_advanced/04_ffi/01_rust_ffi.md"},
    {"group": "core", "domain": "error_handling", "topic": "Error handling", "keywords": ["error handling"], "priority": "P0", "source": "TRPL", "target": "concept/01_foundation/08_error_handling/01_error_handling_basics.md"},
    {"group": "core", "domain": "performance_zero_cost", "topic": "Performance optimization", "keywords": ["performance optimization"], "priority": "P1", "source": "Rust Performance Book", "target": "concept/06_ecosystem/10_performance/01_performance_optimization.md"},
    {"group": "core", "domain": "formal_methods", "topic": "Type theory", "keywords": ["type theory"], "priority": "P1", "source": "TAPL / Reference", "target": "concept/04_formal/00_type_theory/01_type_theory.md"},
    {"group": "core", "domain": "ecosystem_toolchain", "topic": "Cargo dependency resolution", "keywords": ["cargo dependency"], "priority": "P1", "source": "Cargo Book", "target": "concept/06_ecosystem/01_cargo/06_cargo_dependency_resolution.md"},
    {"group": "core", "domain": "enterprise_architecture", "topic": "Enterprise architecture frameworks", "keywords": ["enterprise architecture framework"], "priority": "P2", "source": "TOGAF / ISO 42010", "target": "concept/06_ecosystem/14_enterprise_architecture/01_enterprise_architecture_frameworks.md"},
]


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def extract_first(pattern: str, text: str, flags: int = re.M) -> str | None:
    m = re.search(pattern, text, flags)
    return m.group(1).strip() if m else None


def classify_domain(rel_path: Path, title: str, en_title: str) -> str:
    """基于路径和标题关键词返回语义领域键。"""
    p = str(rel_path).lower().replace("\\", "/")
    parts = p.split("/")
    t = (title or "").lower()
    e = (en_title or "").lower()
    combined = f"{t} {e}"

    # 路径规则（按优先级）
    if "00_meta" in parts or "sources" in parts or "summary.md" in parts or any("quiz" in part for part in parts):
        return "meta_navigation"
    if "04_formal" in parts:
        return "formal_methods"
    if "14_enterprise_architecture" in parts:
        return "enterprise_architecture"
    if (
        "05_systems_and_embedded" in parts
        or "safety_critical" in p
        or "misra" in p
        or "embedded_hardware" in p
        or "probe_rs" in p
    ):
        return "embedded_no_std"
    if (
        "10_performance" in parts
        or "algorithms" in p
        or "custom_allocators" in p
        or "zero_copy_parsing" in p
    ):
        return "performance_zero_cost"
    if "03_design_patterns" in parts or "domain_applications" in parts or "web_and_networking" in parts:
        return "ecosystem_toolchain"
    if "01_foundation/01_ownership_borrow_lifetime" in p:
        return "ownership_borrow_lifetime"
    if (
        "01_foundation/02_type_system" in p
        or "01_foundation/03_values_and_references" in p
        or "01_foundation/04_control_flow" in p
        or "01_foundation/05_collections" in p
        or "01_foundation/06_strings_and_text" in p
    ):
        return "type_system"
    if "02_intermediate/00_traits" in p:
        return "traits"
    if "02_intermediate/01_generics" in p:
        return "generics"
    if (
        "02_intermediate/06_macros_and_metaprogramming" in p
        or "01_foundation/09_macros_basics" in p
        or "03_advanced/03_proc_macros" in p
    ):
        return "macros"
    if "02_intermediate/03_error_handling" in p or "01_foundation/08_error_handling" in p:
        return "error_handling"
    if "03_advanced/01_async" in p or "03_advanced/00_concurrency" in p or "02_intermediate/07_iterators_and_closures" in p:
        return "concurrency_async"
    if (
        "03_advanced/02_unsafe" in p
        or "03_advanced/04_ffi" in p
        or "03_advanced/05_inline_assembly" in p
        or "03_advanced/06_low_level_patterns" in p
    ):
        return "unsafe_ffi"
    if "02_intermediate/04_types_and_conversions" in p or "02_intermediate/02_memory_management" in p:
        return "type_system"
    if (
        "01_foundation/07_modules_and_items" in p
        or "01_foundation/10_testing_basics" in p
        or "02_intermediate/05_modules_and_visibility" in p
        or "06_ecosystem/01_cargo" in p
        or "06_ecosystem/00_toolchain" in p
        or "06_ecosystem/04_web_and_networking" in p
        or "06_ecosystem/11_domain_applications" in p
    ):
        return "ecosystem_toolchain"
    if "05_idioms_patterns_architecture" in p:
        return "ecosystem_toolchain"
    if "05_comparative/04_verification_and_contracts" in p:
        return "formal_methods"
    if "05_comparative" in parts or "07_future" in parts:
        return "meta_navigation"

    # 标题回退
    if any(k in combined for k in ("ownership", "borrowing", "lifetime", "move semantics")):
        return "ownership_borrow_lifetime"
    if any(k in combined for k in ("trait", "dyn compatibility")):
        return "traits"
    if "generic" in combined:
        return "generics"
    if "macro" in combined:
        return "macros"
    if any(k in combined for k in ("async", "concurrency", "parallel", "atomic", "lock-free", "future", "thread", "iterator")):
        return "concurrency_async"
    if any(k in combined for k in ("unsafe", "ffi", "linkage", "inline assembly", "memory model")):
        return "unsafe_ffi"
    if any(k in combined for k in ("embedded", "no_std", "bare metal", "linker", "critical", "rtic", "embassy", "kernel module")):
        return "embedded_no_std"
    if any(k in combined for k in ("error", "panic", "exception safety")):
        return "error_handling"
    if any(k in combined for k in ("performance", "optimization", "zero cost", "allocator")):
        return "performance_zero_cost"
    if any(k in combined for k in ("formal", "logic", "semantics", "model", "rustbelt", "aeneas")):
        return "formal_methods"
    if any(k in combined for k in ("enterprise", "architecture framework", "togaf", "cmmi")):
        return "enterprise_architecture"
    if any(k in combined for k in ("cargo", "toolchain", "compiler", "module", "crate", "testing", "design pattern", "idiom")):
        return "ecosystem_toolchain"
    if any(k in combined for k in ("knowledge", "rag", "bloom", "roadmap", "methodology", "navigation", "index", "glossary")):
        return "meta_navigation"
    if any(k in combined for k in ("type system", "types", "coercion", "casting", "enum", "struct", "pattern", "string", "collection")):
        return "type_system"

    return "ecosystem_toolchain"


def detect_sources(content: str) -> list[str]:
    """返回命中的来源类别键列表。"""
    text_lower = content.lower()
    urls = []
    # Markdown 链接
    urls += [url.lower() for _, url in re.findall(r"\[([^\]]*)\]\(([^)]+)\)", content)]
    # 尖括号 URL
    urls += [u.lower() for u in re.findall(r"<https?://[^>]+>", content)]
    # 裸 URL
    urls += [u.lower() for u in re.findall(r"https?://\S+", content)]

    matched: set[str] = set()
    for cat, spec in SOURCE_CATEGORIES.items():
        for pat in spec["urls"]:
            if any(re.search(pat, url) for url in urls):
                matched.add(cat)
                break
        else:
            for tok in spec["tokens"]:
                if re.search(rf"\b{re.escape(tok)}\b", text_lower):
                    matched.add(cat)
                    break
    return sorted(matched)


def has_mindmap(content: str) -> bool:
    # 查找包含 mindmap 的 mermaid 块
    for block in re.findall(r"```mermaid\s(.*?)```", content, re.S):
        if re.search(r"\bmindmap\b", block, re.I):
            return True
    return False


def parse_file(path: Path) -> dict[str, Any] | None:
    try:
        content = path.read_text(encoding="utf-8", errors="ignore")
    except Exception:
        return None

    title = extract_first(r"^#\s+(.+)$", content) or ""
    # concept/ 文件常在 `>` 引用块中放置 frontmatter，允许可选前缀
    en_title = extract_first(r"^\s*(?:>\s*)?\*\*EN\*\*:\s*(.+)$", content) or ""
    summary = extract_first(r"^\s*(?:>\s*)?\*\*Summary\*\*:\s*(.+)$", content) or ""
    bloom = (
        extract_first(r"^\s*(?:>\s*)?(?:\*\*)?(?:Bloom\s*层级|Bloom level|层级)(?:\*\*)?[^\d]*(L\d)", content)
        or None
    )
    rust_version = extract_first(r"^\s*(?:>\s*)?(?:\*\*)?(?:Rust\s*版本|Rust Version)(?:\*\*)?[^\d]*(1\.\d{2}(?:\.\d+)?)", content) or None
    authority_statement = bool(re.search(r"^\s*(?:>\s*)?.*权威来源.*concept/.*权威页", content, re.M | re.I))
    is_stub = bool(re.search(r"(stub|重定向|redirect|学习入口|专题入口)", content, re.I)) and authority_statement

    domain = classify_domain(path.relative_to(CONCEPT_ROOT), title, en_title)
    sources = detect_sources(content)

    rust_blocks = len(re.findall(r"```rust", content))
    counterexample = bool(re.search(r"^#{2,4}\s*.*?(?:反例|counter[-\s]?example)", content, re.M | re.I))
    decision_tree = bool(re.search(r"decision[-\s]?tree|决策树", content, re.I))

    return {
        "path": str(path.as_posix()),
        "rel_path": str(path.relative_to(CONCEPT_ROOT).as_posix()),
        "domain": domain,
        "title": title,
        "en_title": en_title,
        "summary": summary,
        "bloom": bloom,
        "rust_version": rust_version,
        "authority_statement": authority_statement,
        "is_stub": is_stub,
        "has_mindmap": has_mindmap(content),
        "rust_blocks": rust_blocks,
        "has_counterexample": counterexample,
        "has_decision_tree": decision_tree,
        "sources": sources,
    }


def evaluate_expected(inventory: list[dict[str, Any]]) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    """对比预期清单，返回缺口列表与按域统计。"""
    by_domain: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for item in inventory:
        by_domain[item["domain"]].append(item)

    gaps: list[dict[str, Any]] = []
    domain_expected: dict[str, dict[str, int]] = {}

    for exp in EXPECTED_TOPICS:
        domain = exp["domain"]
        domain_expected.setdefault(domain, {"total": 0, "matched": 0})
        domain_expected[domain]["total"] += 1

        haystack_texts: list[str] = []
        for item in by_domain.get(domain, []):
            haystack_texts.append(
                " ".join(
                    [
                        item["title"],
                        item["en_title"],
                        item["summary"],
                        item["rel_path"],
                    ]
                ).lower()
            )

        matched = False
        matched_path = None
        for kw in exp["keywords"]:
            kwl = kw.lower()
            for idx, text in enumerate(haystack_texts):
                if kwl in text:
                    matched = True
                    matched_path = by_domain[domain][idx]["path"]
                    break
            if matched:
                break

        if matched:
            domain_expected[domain]["matched"] += 1
        else:
            gaps.append({**exp, "matched_path": matched_path})

    return gaps, domain_expected


def build_matrix(inventory: list[dict[str, Any]], domain_expected: dict[str, dict[str, int]]) -> dict[str, Any]:
    by_domain: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for item in inventory:
        by_domain[item["domain"]].append(item)

    rows: list[dict[str, Any]] = []
    for domain, label in DOMAIN_LABELS.items():
        pages = by_domain.get(domain, [])
        n = len(pages)
        if n == 0:
            rows.append({
                "domain": domain,
                "label": label,
                "pages": 0,
                "mindmap_pct": 0,
                "code_pct": 0,
                "counter_pct": 0,
                "decision_tree_pct": 0,
                "source_categories": 0,
                "source_category_list": [],
                "source_hits": {},
                "expected_total": 0,
                "expected_matched": 0,
                "expected_coverage": 0.0,
            })
            continue

        cat_counter: Counter = Counter()
        for p in pages:
            cat_counter.update(p["sources"])

        mindmap_count = sum(1 for p in pages if p["has_mindmap"])
        code_count = sum(1 for p in pages if p["rust_blocks"] > 0)
        counter_count = sum(1 for p in pages if p["has_counterexample"])
        decision_count = sum(1 for p in pages if p["has_decision_tree"])

        expected_total = domain_expected.get(domain, {}).get("total", 0)
        expected_matched = domain_expected.get(domain, {}).get("matched", 0)
        coverage = (expected_matched / expected_total * 100) if expected_total else 0.0

        rows.append({
            "domain": domain,
            "label": label,
            "pages": n,
            "mindmap_pct": round(mindmap_count / n * 100),
            "code_pct": round(code_count / n * 100),
            "counter_pct": round(counter_count / n * 100),
            "decision_tree_pct": round(decision_count / n * 100),
            "source_categories": len(cat_counter),
            "source_category_list": [SOURCE_CATEGORIES[k]["label"] for k in cat_counter.keys()],
            "source_hits": dict(cat_counter),
            "expected_total": expected_total,
            "expected_matched": expected_matched,
            "expected_coverage": round(coverage, 1),
        })

    return {"rows": rows, "total_pages": len(inventory)}


def write_json(inventory: list[dict[str, Any]], matrix: dict[str, Any], gaps: list[dict[str, Any]], path: Path) -> None:
    payload = {
        "meta": {
            "script": "scripts/semantic_domain_inventory.py",
            "concept_root": str(CONCEPT_ROOT),
            "total_pages": len(inventory),
        },
        "matrix": matrix,
        "gaps": gaps,
        "inventory": inventory,
    }
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8")


def write_matrix_md(matrix: dict[str, Any], path: Path) -> None:
    lines: list[str] = [
        "# 语义领域 - 国际权威来源矩阵",
        "",
        f"生成工具：`scripts/semantic_domain_inventory.py` | 总页数：{matrix['total_pages']}",
        "",
        "| 语义领域 | 页数 | mindmap% | 代码块% | 反例% | 决策树% | 对齐来源类别数 | 预期覆盖% | 主要来源类别 |",
        "|---|---:|---:|---:|---:|---:|---:|---:|---|",
    ]
    for r in matrix["rows"]:
        cats = ", ".join(r["source_category_list"]) or "—"
        lines.append(
            f"| {r['label']} | {r['pages']} | {r['mindmap_pct']}% | {r['code_pct']}% | {r['counter_pct']}% | {r['decision_tree_pct']}% | {r['source_categories']} | {r['expected_coverage']}% | {cats} |"
        )
    lines.append("")
    lines.append("## 按域来源命中数")
    lines.append("")
    for r in matrix["rows"]:
        if not r["source_hits"]:
            continue
        lines.append(f"### {r['label']}")
        for cat, cnt in sorted(r["source_hits"].items(), key=lambda x: -x[1]):
            lines.append(f"- {SOURCE_CATEGORIES[cat]['label']}: {cnt}")
        lines.append("")
    path.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="P10 semantic domain inventory")
    parser.add_argument("--root", default=".", help="repository root")
    args = parser.parse_args()

    root = Path(args.root)
    concept_root = root / CONCEPT_ROOT
    tmp_dir = root / TMP_DIR
    tmp_dir.mkdir(parents=True, exist_ok=True)

    inventory: list[dict[str, Any]] = []
    for path in sorted(concept_root.rglob("*.md")):
        rec = parse_file(path)
        if rec is not None:
            inventory.append(rec)

    gaps, domain_expected = evaluate_expected(inventory)
    matrix = build_matrix(inventory, domain_expected)

    write_json(inventory, matrix, gaps, tmp_dir / OUT_JSON.name)
    write_matrix_md(matrix, tmp_dir / OUT_MATRIX.name)

    # stdout 摘要
    print(f"P10 Semantic Domain Inventory")
    print(f"  Total concept pages scanned: {len(inventory)}")
    domain_counts = Counter(item["domain"] for item in inventory)
    print("  Domain distribution:")
    for domain, label in DOMAIN_LABELS.items():
        n = domain_counts.get(domain, 0)
        if n:
            print(f"    - {label}: {n}")
    total_expected = sum(v["total"] for v in domain_expected.values())
    total_matched = sum(v["matched"] for v in domain_expected.values())
    print(f"  Expected topic coverage: {total_matched}/{total_expected} = {total_matched/total_expected*100:.1f}%" if total_expected else "  Expected topic coverage: N/A")
    print(f"  Gaps found: {len(gaps)}")
    print(f"  Outputs:")
    print(f"    - {tmp_dir / OUT_JSON.name}")
    print(f"    - {tmp_dir / OUT_MATRIX.name}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
