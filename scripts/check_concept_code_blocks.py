#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""concept/ 代码块批量编译实测门（P3-x，2026-07-12 建立）。

背景：
    concept/ 权威概念层有约 4600+ 个 ```rust 代码块（kb_auditor 统计），
    此前仅零星验证。本脚本提取全部分类并批量编译实测：

    1. 标注跳过：ignore / compile_fail / should_panic / no_run / edition* 等
       fence flag → 跳过编译但统计；
    2. 伪代码跳过：含 todo!()/unimplemented!()/占位省略行/伪代码标记 → 跳过；
    3. nightly / no_std / no_main → 跳过（非 stable-2024 可直接验证范围）；
    4. 无外部依赖候选 → rustc --edition 2024 逐块编译（自动包装 fn main）；
       候选超过 --sample（默认 300）时按文件分层随机抽样（固定 seed，可复现）；
    5. 引用外部 crate 的块：默认归为"需外部依赖未测"；--with-deps 模式下
       生成 target/code_check/ 临时 crate 借用 workspace 已有依赖编译。

用法：
    python scripts/check_concept_code_blocks.py                 # 观察模式：失败告警 exit 0（输出通过率）
    python scripts/check_concept_code_blocks.py --strict        # 阻断模式：通过率 <95% exit 1
    python scripts/check_concept_code_blocks.py --sample 0      # 不抽样，全量编译（慢）
    python scripts/check_concept_code_blocks.py --with-deps     # 附加依赖块实测（慢，一次性审计用）
    python scripts/check_concept_code_blocks.py --stats-only    # 只提取分类，不编译
    python scripts/check_concept_code_blocks.py --limit 200 --offset 0   # 分批（不走抽样）
    python scripts/check_concept_code_blocks.py --report reports/xxx.md  # 输出报告
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import random
import re
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CONCEPT_DIR = ROOT / "concept"
SCRATCH_CRATE = ROOT / "target" / "code_check"

# --- fence flags: 跳过编译但统计 ---
SKIP_FLAGS = {"ignore", "compile_fail", "should_panic", "no_run", "allow_fail", "norun", "test_harness"}

# --- 已知外部 crate（出现在 use/extern crate 中即视为依赖块） ---
KNOWN_CRATES = {
    "tokio", "tokio_stream", "tokio_util", "futures", "futures_util", "async_std",
    "serde", "serde_json", "serde_derive", "serde_yaml", "toml", "ron",
    "anyhow", "thiserror", "eyre", "snafu",
    "rayon", "crossbeam", "crossbeam_channel", "crossbeam_utils", "dashmap",
    "parking_lot", "flume", "tokio_util",
    "reqwest", "hyper", "hyper_util", "hyper_tls", "h2", "http", "axum", "axum_core",
    "actix_web", "actix", "actix_rt", "tower", "tower_http", "warp", "rocket", "tide",
    "salvo", "ntex", "poem",
    "clap", "structopt", "argh",
    "rand", "rand_chacha", "rand_core", "regex", "lazy_static", "once_cell",
    "chrono", "time", "uuid", "itertools", "num", "num_traits", "num_bigint",
    "log", "env_logger", "tracing", "tracing_subscriber", "slog",
    "async_trait", "pin_project", "pin_project_lite", "futures_core", "futures_executor",
    "proptest", "quickcheck", "criterion", "arbitrary", "rstest", "mockall",
    "wasm_bindgen", "js_sys", "web_sys", "pyo3", "napi", "napi_derive", "uniffi",
    "libc", "winapi", "windows", "nix", "mio", "socket2",
    "libloading", "dlopen", "cxx", "bindgen", "cc",
    "bevy", "bevy_ecs", "amethyst", "ggez", "macroquad", "winit", "wgpu", "glow",
    "egui", "iced", "slint", "tauri", "dioxus", "yew", "leptos", "seed",
    "sqlx", "diesel", "sea_orm", "sea_query", "rusqlite", "tokio_postgres", "redis",
    "mongodb", "surrealdb",
    "tonic", "prost", "tarpc", "grpc", "capnp",
    "libp2p", "multibase", "multiaddr",
    "cortex_m", "cortex_m_rt", "embedded_hal", "embassy", "rtic", "riscv", "avr_device",
    "heapless", "defmt", "defmt_rtt", "panic_halt", "panic_semihosting",
    "nom", "pest", "lalrpop", "logos", "chumsky", "combine", "winnow",
    "syn", "quote", "proc_macro2", "proc_macro_error", "darling",
    "inkwell", "llvm_sys", "cranelift", "walrus", "wasmer", "wasmtime", "wat",
    "openssl", "rustls", "native_tls", "ring", "sha2", "sha3", "blake3", "aes",
    "ed25519_dalek", "x25519_dalek", "curve25519_dalek", "subtle", "zeroize",
    "bytes", "byteorder", "bincode", "rmp_serde", "postcard", "flatbuffers", "protobuf",
    "indexmap", "hashbrown", "smallvec", "tinyvec", "arrayvec", "im", "rpds",
    "slab", "bumpalo", "typed_arena", "slotmap", "generational_arena", "petgraph",
    "either", "enum_dispatch", "enumset", "bitflags", "bitvec", "bytemuck", "zerocopy",
    "scopeguard", "defer", "guard", "owning_ref", "rental", "self_cell", "ouroboros",
    "static_assertions", "const_fn", "paste", "seq_macro", "maplit", "matches",
    "derive_more", "derive_builder", "auto_impl", "delegate", "shrinkwraprs",
    "strum", "strum_macros", "num_enum", "enum_primitive",
    "colored", "termcolor", "crossterm", "ratatui", "tui", "indicatif", "console",
    "dialoguer", "inquire", "comfy_table", "prettytable_rs", "tabled",
    "image", "imageproc", "nalgebra", "glam", "cgmath", "euclid", "mint",
    "ndarray", "tch", "candle_core", "ort", "tract", "linfa",
    "rodio", "cpal", "symphonia", "hound", "dasp",
    "csv", "polars", "arrow", "parquet", "datafusion",
    "sled", "rocksdb", "redb", "heed", "lmdb", "fjall",
    "tempfile", "tempdir", "walkdir", "glob", "fs_extra", "camino",
    "dirs", "directories", "home", "which", "is_terminal", "atty",
    "signal_hook", "ctrlc", "daemonize", "nix",
    "url", "urlencoding", "percent_encoding", "idna", "publicsuffix",
    "jsonschema", "schemars", "validator", "garde",
    "html5ever", "scraper", "select", "kuchiki", "markup5ever",
    "pulldown_cmark", "comrak", "markdown",
    "askama", "tera", "handlebars", "liquid", "maud", "horrorshow",
    "sentry", "opentelemetry", "prometheus", "metrics", "statsd",
    "backtrace", "color_eyre", "human_panic", "better_panic",
    "serde_with", "serde_repr", "serde_bytes", "serde_path_to_error",
    "smol", "async_executor", "async_task", "async_lock", "async_channel",
    "event_listener", "polling", "async_io", "async_net",
    "kanal", "thingbuf", "bus", "broadcast",
    "loom", "shuttle", "proptest_derive",
    "approx", "float_cmp", "ordered_float", "noisy_float",
    "fixed", "rust_decimal", "bigdecimal", "fraction",
    "unicode_segmentation", "unicode_normalization", "unicode_width", "unicase",
    "encoding_rs", "charset", "iconv",
    "memchr", "aho_corasick", "bstr", "simd_json", "sonic_rs",
    "lz4", "zstd", "flate2", "brotli", "snap", "xz2", "bzip2", "zip", "tar",
    "object", "goblin", "elf", "mach", "pe", "xmas_elf",
    "capstone", "iced_x86", "yaxpeax_x86",
    "notify", "hotwatch", "watchexec",
    "config", "figment", "dotenv", "dotenvy",
    "jwt", "jsonwebtoken", "oauth2", "openidconnect", "paseto",
    "argon2", "bcrypt", "scrypt", "pbkdf2", "hkdf", "hmac",
    "rustls_pemfile", "pem", "x509_parser", "rcgen",
    "socketcan", "pnet", "tun", "smoltcp",
    "gstreamer", "ffmpeg", "av_device",
    "vulkano", "ash", "gfx", "gfx_hal", "rend3", "three_d",
    "rusttype", "fontdue", "ab_glyph", "cosmic_text", "swash",
    "usvg", "resvg", "tiny_skia", "raqote", "plotters", "svg",
    "include_dir", "rust_embed", "include_flate",
    "mlua", "rlua", "rhai", "gluon", "deno_core", "rune", "starlark",
    "tree_sitter", "tree_sitter_rust",
    "insta", "expect_test", "goldenfile", "assert_cmd", "predicates", "wiremock",
    "httpmock", "mockito", "httptest", "test_context",
    "ctor", "inventory", "linkme", "typetag", "erased_serde",
    "ghost", "static_assertions", "const_panic",
    "measure_time", "coarsetime", "quanta", "tikv_jemallocator", "mimalloc",
    "miri", "kani", "verus", "prusti", "creusot", "autoverus",
    "ratatui", "cursive", "termion", "termwiz", "vt100",
    "threadpool", "scheduled_thread_pool", "cron", "tokio_cron_scheduler",
    "dynosaur", "miniextendr_api", "extendr_api", "r_vector",
    "orthrus", "numcodecs",
}

# workspace 已有（可离线编译）的依赖子集 → --with-deps 模式用
# name in code -> cargo package name (None = same)
WORKSPACE_DEPS = {
    "tokio": None, "futures": None, "serde": None, "serde_json": None,
    "anyhow": None, "thiserror": None, "rayon": None, "crossbeam": None,
    "dashmap": None, "parking_lot": None, "reqwest": None, "hyper": None,
    "hyper_util": "hyper-util", "axum": None, "tower": None, "tower_http": "tower-http",
    "clap": None, "rand": None, "regex": None, "lazy_static": "lazy_static",
    "once_cell": "once_cell", "chrono": None, "uuid": None, "itertools": None,
    "log": None, "tracing": None, "async_trait": "async-trait",
    "pin_project": "pin-project", "bytes": None, "libc": None,
    "proptest": None, "criterion": None, "tempfile": None, "url": None,
    "bitflags": None, "indexmap": None, "smallvec": None, "slab": None,
    "either": None, "paste": None, "derive_more": "derive_more",
    "strum": None, "nom": None, "syn": None, "quote": None, "proc_macro2": "proc-macro2",
    "sha2": None, "base64": None, "hex": None, "md5": "md-5", "flate2": None,
    "csv": None, "toml": None, "serde_yaml": "serde_yaml", "jsonwebtoken": None,
    "num": None, "num_traits": "num-traits", "num_bigint": "num-bigint",
    "ordered_float": "ordered-float", "rust_decimal": "rust_decimal",
    "unicode_segmentation": "unicode-segmentation", "encoding_rs": "encoding_rs",
    "memchr": None, "aho_corasick": "aho-corasick",
    "walkdir": None, "glob": None, "dirs": None, "which": None,
    "colored": None, "indicatif": None, "console": None,
    "sqlx": None, "tokio_postgres": "tokio-postgres", "rusqlite": None, "redis": None,
    "sea_orm": "sea-orm", "diesel": None,
    "libp2p": None, "h2": None, "http": None,
    "salvo": None, "ntex": None, "askama": None,
    "actix_web": "actix-web", "actix": None,
    "mockall": None, "rstest": None, "insta": None, "assert_cmd": "assert_cmd",
    "predicates": None, "wiremock": None,
    "loom": None, "arbitrary": None,
    "nalgebra": None, "ndarray": None,
    "notify": None, "config": None, "dotenvy": None,
    "sled": None, "polars": None,
    "opentelemetry": None, "prometheus": None, "metrics": None,
    "backtrace": None, "color_eyre": "color-eyre",
    "jsonschema": None, "schemars": None, "validator": None,
    "pulldown_cmark": "pulldown-cmark", "comrak": None,
    "tera": None, "handlebars": None,
    "criterion": None, "quickcheck": None,
    "socket2": None, "mio": None, "nix": None,
    "wasm_bindgen": "wasm-bindgen",
    "serde_with": "serde_with", "serde_repr": "serde_repr",
    "smol": None, "async_lock": "async-lock", "async_channel": "async-channel",
    "event_listener": "event-listener",
    "bytemuck": None, "zerocopy": None, "scopeguard": None, "self_cell": "self_cell",
    "static_assertions": "static_assertions", "enum_dispatch": "enum_dispatch",
    "bumpalo": None, "typed_arena": "typed-arena", "slotmap": None, "petgraph": None,
    "hashbrown": None, "tinyvec": None, "arrayvec": None,
    "bincode": None, "postcard": None, "rmp_serde": "rmp-serde",
    "crossterm": None, "ratatui": None, "termcolor": None,
    "dialoguer": None, "inquire": None, "comfy_table": "comfy-table",
    "image": None, "plotters": None, "resvg": None, "usvg": None, "tiny_skia": "tiny-skia",
    "rodio": None, "cpal": None, "hound": None, "symphonia": None,
    "glam": None, "cgmath": None,
    "rustls": None, "native_tls": "native-tls", "ring": None, "blake3": None,
    "zeroize": None, "subtle": None, "hkdf": None, "hmac": None, "pbkdf2": None,
    "x509_parser": "x509-parser", "rcgen": None, "pem": None, "rustls_pemfile": "rustls-pemfile",
    "openssl": None,
    "goblin": None, "object": None, "xmas_elf": "xmas-elf",
    "capstone": None, "iced_x86": "iced-x86",
    "include_dir": "include_dir", "rust_embed": "rust-embed",
    "mlua": None, "rhai": None,
    "ctor": None, "inventory": None, "linkme": None, "typetag": None, "erased_serde": "erased-serde",
    "expect_test": "expect-test",
    "threadpool": None, "cron": None,
    "approx": None, "float_cmp": "float-cmp", "noisy_float": "noisy_float",
    "fixed": None, "bigdecimal": None,
    "unicode_normalization": "unicode-normalization", "unicode_width": "unicode-width",
    "bstr": None, "simd_json": "simd-json", "sonic_rs": "sonic-rs",
    "zstd": None, "brotli": None, "snap": None, "lz4": None, "xz2": None, "bzip2": None,
    "zip": None, "tar": None,
    "nom": None, "pest": None, "logos": None, "chumsky": None, "winnow": None,
    "pnet": None, "smoltcp": None,
    "rusttype": None, "fontdue": None, "ab_glyph": "ab_glyph",
    "async_executor": "async-executor", "async_task": "async-task", "async_io": "async-io",
    "async_net": "async-net", "polling": None,
    "kanal": None,
    "coarsetime": None, "quanta": None,
    "auto_impl": "auto_impl", "derive_builder": "derive_builder", "delegate": None,
    "strum_macros": "strum_macros", "num_enum": "num_enum",
    "percent_encoding": "percent-encoding", "idna": None,
    "html5ever": None, "scraper": None,
    "sentry": None,
    "serde_path_to_error": "serde_path_to_error",
    "futures_util": "futures-util", "futures_executor": "futures-executor",
    "darling": None, "proc_macro_error": "proc-macro-error",
    "multibase": None, "multiaddr": None,
    "prost": None, "tonic": None, "tarpc": None,
    "hyper_rustls": "hyper-rustls", "hyper_tls": "hyper-tls", "hyper_timeout": "hyper-timeout",
    "serde_derive": "serde_derive",
    "env_logger": "env_logger", "tracing_subscriber": "tracing-subscriber",
    "crossbeam_channel": "crossbeam-channel", "crossbeam_utils": "crossbeam-utils",
    "flume": None,
    "tokio_stream": "tokio-stream", "tokio_util": "tokio-util",
    "rand_chacha": "rand_chacha",
    "dynosaur": None,
    "extendr_api": "extendr-api", "miniextendr_api": "miniextendr-api",
}

WORKSPACE_MEMBER_CRATES = {
    "c01_ownership_borrow_scope", "c02_type_system", "c03_control_fn", "c04_generic",
    "c05_threads", "c06_async", "c07_process", "c08_algorithms", "c09_design_pattern",
    "c10_networks", "c11_macro_system_proc", "c12_wasm", "c13_embedded",
    "c14_semantic_web", "c15_verification_tools", "c16_gui",
    "c17_resolver_v3_public_demo", "common",
}

# 抽样：候选超过该数量时按文件分层随机抽样（默认 300，固定 seed 可复现）
SAMPLE_CAP = 300
SAMPLE_SEED = 20260712
STRICT_PASS_RATE = 0.95

# 已知不可能编译的环境（嵌入式/nightly-only crate）→ 直接跳过
SKIP_CRATES = {
    "cortex_m", "cortex_m_rt", "embedded_hal", "embassy", "rtic", "riscv",
    "avr_device", "heapless", "defmt", "defmt_rtt", "panic_halt",
    "panic_semihosting", "wasm_bindgen", "js_sys", "web_sys",
    "miri", "kani", "verus", "prusti", "creusot", "autoverus",
}

PSEUDO_MARKERS = [
    "todo!()", "unimplemented!()", "unreachable!(\"TODO",
]
PSEUDO_LINE_RE = re.compile(
    r"^\s*(//\s*)?(…|\.\.\.)\s*(//.*)?$"  # 整行只有 ... 或 …
)
PSEUDO_COMMENT_RE = re.compile(
    r"(伪代码|示意代码|示意：|简化示意|此处省略|代码省略|省略实现|省略细节|pseudocode|pseudo-code|placeholder)",
    re.IGNORECASE,
)

TOP_LEVEL_ITEM_RE = re.compile(
    r"^(?:pub(?:\([^)]*\))?\s+)?(?:async\s+)?(?:unsafe\s+)?(?:extern\s+\"[^\"]+\"\s+)?"
    r"(?:fn|struct|enum|trait|impl|mod|use|const|static|type|macro_rules!|extern crate)\b"
)
ATTR_RE = re.compile(r"^\s*#\s*!?\[")
FEATURE_RE = re.compile(r"#\s*!\s*\[\s*feature\s*\(")

FENCE_RE = re.compile(r"^([ \t]*(?:>[ \t]*)?)```(rust[^\n]*)\n(.*?)^\1```", re.DOTALL | re.IGNORECASE | re.MULTILINE)
CRATE_USE_RE = re.compile(
    r"(?:^|\n)\s*(?:use\s+([a-zA-Z_][a-zA-Z0-9_]*)|extern\s+crate\s+([a-zA-Z_][a-zA-Z0-9_]*))"
)
CRATE_PATH_RE = re.compile(r"\b([a-z][a-z0-9_]*)::")


def extract_blocks(path: Path) -> list[dict]:
    """提取一个 md 文件中的全部 rust 代码块。"""
    text = path.read_text(encoding="utf-8", errors="replace")
    blocks = []
    for i, m in enumerate(FENCE_RE.finditer(text)):
        prefix = m.group(1)
        header = m.group(2).strip()
        code = m.group(3)
        if prefix.strip().startswith(">"):
            # blockquote 内的代码块：剥离引用前缀
            q = prefix
            code = "\n".join(
                ln[len(q):] if ln.startswith(q) else (ln[1:] if ln.startswith(">") else ln)
                for ln in code.splitlines()
            )
        flags = [f.strip() for f in re.split(r"[, ]+", header.replace("rust", "", 1)) if f.strip()]
        line_no = text[: m.start()].count("\n") + 1
        blocks.append({
            "file": str(path.relative_to(ROOT)).replace("\\", "/"),
            "index": i,
            "line": line_no,
            "flags": flags,
            "code": code,
        })
    return blocks


def classify(block: dict) -> tuple[str, str]:
    """返回 (category, reason)。category:
    flag_skip / pseudo / nightly / nostd / dep_skip / dep / candidate
    """
    flags = set(block["flags"])
    code = block["code"]

    if flags & SKIP_FLAGS:
        return "flag_skip", "fence: " + ",".join(sorted(flags & SKIP_FLAGS))

    stripped = code.strip()
    if not stripped or stripped in {"// ...", "...", "…"}:
        return "pseudo", "空块/纯省略"

    for marker in PSEUDO_MARKERS:
        if marker in code:
            return "pseudo", f"含 {marker}"

    pseudo_lines = sum(1 for ln in code.splitlines() if PSEUDO_LINE_RE.match(ln))
    if pseudo_lines >= 2:
        return "pseudo", f"含 {pseudo_lines} 行占位省略"
    if PSEUDO_COMMENT_RE.search(code) and ("..." in code or "…" in code):
        return "pseudo", "伪代码注释+省略"

    if FEATURE_RE.search(code):
        return "nightly", "含 #![feature(...)]"
    if re.search(r"#\s*!\s*\[\s*no_std\s*\]", code) or re.search(r"#\s*!\s*\[\s*no_main\s*\]", code):
        return "nostd", "no_std/no_main"

    crates = set()
    for m in CRATE_USE_RE.finditer(code):
        name = (m.group(1) or m.group(2))
        if name in {"std", "core", "alloc", "self", "crate", "super"}:
            continue
        crates.add(name)
    for m in CRATE_PATH_RE.finditer(code):
        name = m.group(1)
        if name in {"std", "core", "alloc", "self", "crate", "super"}:
            continue
        if name in KNOWN_CRATES or name in WORKSPACE_MEMBER_CRATES:
            crates.add(name)
    ext = {c for c in crates if c in KNOWN_CRATES or c in WORKSPACE_MEMBER_CRATES}
    if ext:
        if ext & SKIP_CRATES:
            return "dep_skip", "环境不可用: " + ",".join(sorted(ext & SKIP_CRATES))
        missing = {c for c in ext if c not in WORKSPACE_DEPS and c not in WORKSPACE_MEMBER_CRATES}
        if missing:
            return "dep_untested", "外部依赖(workspace外): " + ",".join(sorted(missing))
        return "dep", "workspace依赖: " + ",".join(sorted(ext))
    return "candidate", ""


def unhide_lines(code: str) -> str:
    """rustdoc/mdbook 约定：以 `# ` 开头的行是隐藏上下文行，编译时去掉 `# ` 前缀。"""
    out = []
    for ln in code.splitlines():
        s = ln.lstrip()
        if s.startswith("# ") and not s.startswith("#!") and not s.startswith("#["):
            indent = ln[: len(ln) - len(s)]
            out.append(indent + s[2:])
        else:
            out.append(ln)
    return "\n".join(out)


def wrap_code(code: str) -> str:
    """无 fn main 时自动包装：整体包入 fn main（Rust 允许 fn 体内定义 items），
    inner attribute (#![...]) 提到文件顶部。"""
    code = unhide_lines(code)
    if re.search(r"fn\s+main\s*\(", code):
        return code
    lines = code.splitlines()
    inner_attrs = [ln for ln in lines if ln.strip().startswith("#![")]
    body = [ln for ln in lines if not ln.strip().startswith("#![")]
    indented = "\n".join("    " + ln for ln in body)
    head = "\n".join(inner_attrs) + ("\n" if inner_attrs else "")
    return f"{head}fn main() {{\n{indented}\n}}\n"


def compile_one(block: dict, tmpdir: Path) -> dict:
    """rustc 直接编译无依赖块。包装为 bin 失败时，回退按 lib（不包装）再试一次：
    部分纯 item 块（含 super::/mod 语义）包入 fn main 会改变模块语义。"""
    src = wrap_code(block["code"])
    h = hashlib.sha1(src.encode()).hexdigest()[:12]
    f = tmpdir / f"b_{h}.rs"
    f.write_text(src, encoding="utf-8")
    out = tmpdir / f"b_{h}.out"

    def _run(source: str, crate_type: str, suffix: str) -> subprocess.CompletedProcess:
        ff = tmpdir / f"b_{h}{suffix}.rs"
        ff.write_text(source, encoding="utf-8")
        return subprocess.run(
            ["rustc", "--edition", "2024", "--emit=metadata", "--crate-type", crate_type,
             "-o", str(tmpdir / f"b_{h}{suffix}.out"), str(ff)],
            capture_output=True, text=True, timeout=60,
        )

    try:
        r = _run(src, "bin", "")
        if r.returncode != 0 and not re.search(r"fn\s+main\s*\(", block["code"]):
            r2 = _run(unhide_lines(block["code"]), "lib", "_lib")
            if r2.returncode == 0:
                return {**block, "status": "pass", "stderr": "", "mode": "lib"}
    except subprocess.TimeoutExpired:
        return {**block, "status": "timeout", "stderr": "rustc timeout 60s"}
    ok = r.returncode == 0
    stderr = "" if ok else r.stderr
    return {**block, "status": "pass" if ok else "fail", "stderr": stderr}


def summarize_stderr(stderr: str, limit: int = 600) -> str:
    lines = [ln for ln in stderr.splitlines() if ln.strip().startswith(("error", "warning: unused"))]
    errs = [ln for ln in stderr.splitlines() if ln.startswith("error")]
    return "\n".join(errs)[:limit] if errs else stderr[:limit]


def stratified_sample(candidates: list[dict], cap: int, seed: int) -> list[dict]:
    """按文件分层随机抽样：每层（文件）按候选占比分配名额（最大余数法取整），
    层内固定 seed 随机抽取，保证可复现且覆盖不同文件。"""
    rng = random.Random(seed)
    by_file: dict[str, list[dict]] = {}
    for b in candidates:
        by_file.setdefault(b["file"], []).append(b)
    files = sorted(by_file)
    total = len(candidates)
    alloc: dict[str, int] = {}
    remainders: list[tuple[float, str]] = []
    for f in files:
        exact = len(by_file[f]) * cap / total
        alloc[f] = int(exact)
        remainders.append((exact - int(exact), f))
    leftover = cap - sum(alloc.values())
    for _, f in sorted(remainders, key=lambda t: (-t[0], t[1]))[:leftover]:
        alloc[f] += 1
    sampled: list[dict] = []
    for f in files:
        n = min(alloc[f], len(by_file[f]))
        if n > 0:
            sampled.extend(rng.sample(by_file[f], n))
    return sampled


def block_crates(block: dict) -> set[str]:
    """提取块中引用的已知外部/workspace crate。"""
    crates = set()
    for m in CRATE_USE_RE.finditer(block["code"]):
        name = m.group(1) or m.group(2)
        if name in KNOWN_CRATES or name in WORKSPACE_MEMBER_CRATES:
            crates.add(name)
    for m in CRATE_PATH_RE.finditer(block["code"]):
        name = m.group(1)
        if name in KNOWN_CRATES or name in WORKSPACE_MEMBER_CRATES:
            crates.add(name)
    return crates


def load_lock_versions() -> dict[str, str]:
    """从根 Cargo.lock 读取 name -> version（离线精确钉版）。"""
    lock = ROOT / "Cargo.lock"
    versions: dict[str, str] = {}
    if not lock.exists():
        return versions
    name = None
    for line in lock.read_text(encoding="utf-8").splitlines():
        m = re.match(r'^name = "(.+)"$', line)
        if m:
            name = m.group(1)
            continue
        m = re.match(r'^version = "(.+)"$', line)
        if m and name:
            versions.setdefault(name, m.group(1))
            name = None
    return versions


def run_dep_mode(dep_blocks: list[dict]) -> list[dict]:
    """借用 workspace 依赖，在 target/code_check/ 临时 crate 中编译依赖块。"""
    if not dep_blocks:
        return []
    needed_ext: set[str] = set()
    needed_members: set[str] = set()
    for b in dep_blocks:
        for c in block_crates(b):
            if c in WORKSPACE_MEMBER_CRATES:
                needed_members.add(c)
            elif c in WORKSPACE_DEPS:
                pkg = WORKSPACE_DEPS[c] or c
                needed_ext.add(pkg)

    lock_versions = load_lock_versions()
    unresolvable = {p for p in needed_ext if p not in lock_versions}
    if unresolvable:
        print(f"[deps] 不在 Cargo.lock，无法离线解析（跳过）: {sorted(unresolvable)}")

    SCRATCH_CRATE.mkdir(parents=True, exist_ok=True)
    (SCRATCH_CRATE / "src" / "bin").mkdir(parents=True, exist_ok=True)
    # 清理旧 bin
    for old in (SCRATCH_CRATE / "src" / "bin").glob("b_*.rs"):
        old.unlink()

    dep_lines = []
    for pkg in sorted(needed_ext - unresolvable):
        dep_lines.append(f'{pkg} = "={lock_versions[pkg]}"')
    for mem in sorted(needed_members):
        dep_lines.append(f'{mem} = {{ path = "../../crates/{mem}" }}')
    cargo_toml = (
        "[package]\nname = \"code_check\"\nversion = \"0.0.0\"\n"
        "edition = \"2024\"\n\n[workspace]\n\n[dependencies]\n" + "\n".join(dep_lines) + "\n"
    )
    (SCRATCH_CRATE / "Cargo.toml").write_text(cargo_toml, encoding="utf-8")

    name_of = {}
    skipped_unresolvable: list[dict] = []
    for b in dep_blocks:
        b_crates = {WORKSPACE_DEPS.get(c) or c for c in block_crates(b) if c in WORKSPACE_DEPS}
        if b_crates & unresolvable:
            skipped_unresolvable.append(
                {**b, "status": "dep_env_fail",
                 "stderr": "依赖不在 Cargo.lock: " + ",".join(sorted(b_crates & unresolvable))})
            continue
        src = wrap_code(b["code"])
        h = hashlib.sha1((b["file"] + str(b["line"]) + src).encode()).hexdigest()[:12]
        name = f"b_{h}"
        name_of[name] = b
        (SCRATCH_CRATE / "src" / "bin" / f"{name}.rs").write_text(src, encoding="utf-8")

    print(f"[deps] scratch crate: {len(needed_ext)} ext pkgs + {len(needed_members)} workspace members, "
          f"{len(dep_blocks)} bins -> cargo check --offline")
    env = dict(os.environ, CARGO_TARGET_DIR=str(ROOT / "target"))
    try:
        r = subprocess.run(
            ["cargo", "check", "--offline", "--bins", "--message-format=json"],
            cwd=SCRATCH_CRATE, capture_output=True, text=True, timeout=280, env=env,
        )
    except subprocess.TimeoutExpired:
        print("[deps] cargo check timeout 280s")
        return [{**b, "status": "timeout", "stderr": "cargo check timeout"} for b in dep_blocks]

    # 解析 json 诊断
    errors_by_bin: dict[str, list[str]] = {}
    saw_compiler_message = False
    for line in r.stdout.splitlines():
        try:
            msg = json.loads(line)
        except json.JSONDecodeError:
            continue
        if msg.get("reason") != "compiler-message":
            continue
        saw_compiler_message = True
        m = msg.get("message", {})
        if m.get("level") not in ("error", "error: internal compiler error"):
            continue
        # 找到对应 bin 文件
        target_bin = None
        for sp in m.get("spans", []):
            fn = sp.get("file_name", "")
            mm = re.search(r"(b_[0-9a-f]{12})\.rs", fn)
            if mm:
                target_bin = mm.group(1)
                break
        if target_bin:
            rendered = (m.get("rendered") or m.get("message") or "").splitlines()[0]
            errors_by_bin.setdefault(target_bin, []).append(rendered)

    # crate 级失败（依赖本身编译不了）→ 所有块标 dep_env_fail
    # 判定：错误来自非 code_check 包（依赖包编译失败）
    crate_level = []
    unattributed = 0
    for line in r.stdout.splitlines():
        try:
            msg = json.loads(line)
        except json.JSONDecodeError:
            continue
        if msg.get("reason") == "compiler-message":
            m = msg.get("message", {})
            if m.get("level", "").startswith("error"):
                if not any("b_" in (sp.get("file_name") or "") for sp in m.get("spans", [])):
                    if "code_check" not in msg.get("package_id", ""):
                        crate_level.append((m.get("rendered") or m.get("message") or "").splitlines()[0])
                    else:
                        unattributed += 1
    if unattributed:
        print(f"[deps] {unattributed} 个无法归因到具体 bin 的 code_check 错误（见 cargo 输出）")
    if crate_level:
        print("[deps] crate-level errors (dep build failures):")
        for e in crate_level[:10]:
            print("   ", e[:160])
    resolution_failed = r.returncode != 0 and not saw_compiler_message
    if resolution_failed:
        print("[deps] cargo 解析/构建失败（非编译诊断），全部按 dep_env_fail 处理:")
        print("   ", (r.stderr or "").splitlines()[-1][:200] if r.stderr else "")

    results = list(skipped_unresolvable)
    for name, b in name_of.items():
        if name in errors_by_bin:
            results.append({**b, "status": "fail", "stderr": "\n".join(errors_by_bin[name])})
        elif crate_level or resolution_failed:
            reason = (crate_level[0] if crate_level else "cargo 解析失败")
            results.append({**b, "status": "dep_env_fail", "stderr": "依赖编译失败: " + reason})
        else:
            results.append({**b, "status": "pass", "stderr": ""})
    npass = sum(1 for x in results if x["status"] == "pass")
    print(f"[deps] pass={npass} fail={sum(1 for x in results if x['status'] == 'fail')} "
          f"dep_env_fail={sum(1 for x in results if x['status'] == 'dep_env_fail')}")
    return results


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--strict", action="store_true")
    ap.add_argument("--with-deps", action="store_true")
    ap.add_argument("--stats-only", action="store_true")
    ap.add_argument("--limit", type=int, default=0)
    ap.add_argument("--offset", type=int, default=0)
    ap.add_argument("--sample", type=int, default=SAMPLE_CAP,
                    help="候选超过该数量时按文件分层抽样的样本上限；0=不抽样")
    ap.add_argument("--seed", type=int, default=SAMPLE_SEED)
    ap.add_argument("--jobs", type=int, default=8)
    ap.add_argument("--report", type=str, default="")
    ap.add_argument("--json", type=str, default="")
    args = ap.parse_args()

    files = sorted(CONCEPT_DIR.rglob("*.md"))
    files = [f for f in files if "sources" not in f.parts]
    all_blocks: list[dict] = []
    for f in files:
        all_blocks.extend(extract_blocks(f))

    # 分类
    buckets: dict[str, list[dict]] = {}
    for b in all_blocks:
        cat, reason = classify(b)
        b["category"] = cat
        b["reason"] = reason
        buckets.setdefault(cat, []).append(b)

    total = len(all_blocks)
    print(f"[extract] files={len(files)} blocks={total}")
    for cat in ["flag_skip", "pseudo", "nightly", "nostd", "dep_skip", "dep_untested", "dep", "candidate"]:
        n = len(buckets.get(cat, []))
        if n:
            print(f"  {cat:14s} {n}")

    candidates = buckets.get("candidate", [])
    sampled_note = ""
    if args.limit:
        candidates = candidates[args.offset: args.offset + args.limit]
        sampled_note = f"（--limit 分批 {args.offset}:{args.offset + args.limit}）"
    elif args.sample and len(candidates) > args.sample:
        before = len(candidates)
        candidates = stratified_sample(candidates, args.sample, args.seed)
        sampled_note = f"（分层抽样 {len(candidates)}/{before}，seed={args.seed}）"
    if sampled_note:
        print(f"[sample] {sampled_note}")

    results: list[dict] = []
    if not args.stats_only and candidates:
        print(f"[compile] candidates={len(candidates)} jobs={args.jobs}")
        with tempfile.TemporaryDirectory(prefix="concept_cb_") as td:
            tmpdir = Path(td)
            with ThreadPoolExecutor(max_workers=args.jobs) as ex:
                results = list(ex.map(lambda b: compile_one(b, tmpdir), candidates))
        passed = sum(1 for r in results if r["status"] == "pass")
        failed = [r for r in results if r["status"] == "fail"]
        timeouts = [r for r in results if r["status"] == "timeout"]
        rate = passed / len(results) if results else 1.0
        print(f"[result] pass={passed} fail={len(failed)} timeout={len(timeouts)} "
              f"pass_rate={rate:.1%}")
        for r in failed[:40]:
            print(f"  FAIL {r['file']}:{r['line']} :: {summarize_stderr(r['stderr'], 200).splitlines()[0] if r['stderr'] else ''}")
        if len(failed) > 40:
            print(f"  ... and {len(failed) - 40} more (see --json/--report)")

    dep_results: list[dict] = []
    if args.with_deps and not args.stats_only:
        dep_blocks = buckets.get("dep", [])
        dep_results = run_dep_mode(dep_blocks)

    summary = {
        "total": total,
        "buckets": {k: len(v) for k, v in buckets.items()},
        "compiled": len(results),
        "pass": sum(1 for r in results if r["status"] == "pass"),
        "fail": sum(1 for r in results if r["status"] == "fail"),
        "timeout": sum(1 for r in results if r["status"] == "timeout"),
        "dep_compiled": len(dep_results),
        "dep_pass": sum(1 for r in dep_results if r["status"] == "pass"),
        "dep_fail": sum(1 for r in dep_results if r["status"] == "fail"),
        "dep_env_fail": sum(1 for r in dep_results if r["status"] == "dep_env_fail"),
    }

    if args.json:
        payload = {
            "summary": summary,
            "failures": [
                {"file": r["file"], "line": r["line"], "index": r["index"],
                 "error": summarize_stderr(r.get("stderr", "")), "dep": False}
                for r in results if r["status"] != "pass"
            ] + [
                {"file": r["file"], "line": r["line"], "index": r["index"],
                 "error": summarize_stderr(r.get("stderr", "")), "dep": True,
                 "status": r["status"]}
                for r in dep_results if r["status"] != "pass"
            ],
        }
        Path(args.json).write_text(json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8")
        print(f"[json] -> {args.json}")

    if args.report:
        write_report(Path(args.report), summary, results, dep_results, buckets)

    failed_real = [r for r in results if r["status"] in ("fail", "timeout")]
    if failed_real:
        print(f"[gate] {len(failed_real)} 个无依赖块编译失败/超时（详见 --json/--report）")
    if results:
        rate = summary["pass"] / len(results)
        if args.strict and rate < STRICT_PASS_RATE:
            print(f"[gate] STRICT: pass_rate={rate:.1%} < {STRICT_PASS_RATE:.0%} → exit 1")
            return 1
    if not args.strict:
        print("[gate] 观察模式：exit 0")
    return 0


def write_report(path: Path, summary: dict, results: list[dict], dep_results: list[dict], buckets: dict):
    lines = ["# concept/ 代码块编译实测报告", "", "## 分类统计", ""]
    lines.append("| 分类 | 数量 |")
    lines.append("|---|---:|")
    labels = {
        "flag_skip": "标注跳过(ignore/compile_fail/no_run/should_panic)",
        "pseudo": "伪代码/占位跳过",
        "nightly": "nightly-only(#![feature])",
        "nostd": "no_std/no_main",
        "dep_skip": "依赖环境不可用(嵌入式/wasm/验证工具)",
        "dep_untested": "需外部依赖未测(workspace外)",
        "dep": "需外部依赖(workspace内,可测)",
        "candidate": "无依赖编译候选",
    }
    for k, label in labels.items():
        if summary["buckets"].get(k):
            lines.append(f"| {label} | {summary['buckets'][k]} |")
    lines.append(f"| **合计** | **{summary['total']}** |")
    lines += ["", "## 无依赖块实测", "",
              f"- 编译候选: {summary['compiled']}",
              f"- 通过: {summary['pass']}",
              f"- 失败（真实腐烂）: {summary['fail']}",
              f"- 超时: {summary['timeout']}", ""]
    fails = [r for r in results if r["status"] != "pass"]
    if fails:
        lines += ["## 失败清单（无依赖块）", "", "| 文件 | 行 | 错误摘要 |", "|---|---:|---|"]
        for r in fails:
            err = summarize_stderr(r.get("stderr", ""), 300).replace("|", "\\|").replace("\n", "<br>")
            lines.append(f"| `{r['file']}` | {r['line']} | {err} |")
    if dep_results:
        lines += ["", "## 依赖块实测（--with-deps）", "",
                  f"- 依赖块: {summary['dep_compiled']}",
                  f"- 通过: {summary['dep_pass']}",
                  f"- 失败: {summary['dep_fail']}",
                  f"- 依赖环境失败（未测）: {summary['dep_env_fail']}", ""]
        dfails = [r for r in dep_results if r["status"] != "pass"]
        if dfails:
            lines += ["| 文件 | 行 | 状态 | 错误摘要 |", "|---|---:|---|---|"]
            for r in dfails:
                err = summarize_stderr(r.get("stderr", ""), 300).replace("|", "\\|").replace("\n", "<br>")
                lines.append(f"| `{r['file']}` | {r['line']} | {r['status']} | {err} |")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"[report] -> {path}")


if __name__ == "__main__":
    sys.exit(main())
