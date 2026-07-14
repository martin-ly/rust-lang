#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""concept/ 代码块批量编译实测工具（P2，2026-07-13 重构；初版 2026-07-12）。

背景：
    concept/ 权威概念层有 4700+ 个 ```rust 代码块，此前仅零星验证（约 60 页）。
    本工具提取全部分类并批量实测，建立全库可机器复核的编译基线。

分类（category）：
    标注类（fence flag）：
      - anno_ignore   : ignore / no_run / allow_fail → 仅统计，不编译
      - compile_fail  : 实测「确实编译失败」；fence 标注 E0xxx 时校验错误码一致
      - should_panic  : 实测编译通过（运行期 panic 语义不执行验证）
    跳过类：
      - pseudo        : 含 todo!()/unimplemented!()/整行省略号(.../…)/伪代码注释
      - nightly       : 含 #![feature(...)]
      - nostd         : no_std / no_main
    依赖类：
      - dep_skip      : 嵌入式/wasm/验证工具等环境不可用 crate
      - dep_untested  : 引用的 crate 在 target/debug/deps 中找不到 rmeta/rlib（需依赖未测）
      - dep           : 依赖可解析 → 用 target/debug/deps 的 rmeta 做 --extern 实测
    可编译候选：
      - candidate     : std-only，rustc --edition 2024 直编（无 fn main 自动包装）

依赖解析（--with-deps）：
    先 `cargo build --workspace`（或 --ensure-deps 自动执行）确保 target/debug/deps
    存在 rmeta；块中引用的 crate 逐一映射 lib<name>-*.rmeta/.rlib（proc-macro 用
    动态库），全部可解析才编译，找不到的归入 dep_untested。

执行：
    分批（每批 --batch 300 块）ThreadPoolExecutor 并行 rustc，防单次运行超时。
    候选超过 --sample（默认 300）时按文件分层随机抽样（固定 seed，可复现）；
    --sample 0 全量。compile_fail/should_panic/dep 块不抽样，全部实测。

用法：
    python scripts/check_concept_code_blocks.py                 # 观察模式：抽样 300 候选，exit 0
    python scripts/check_concept_code_blocks.py --strict        # 阻断：应过但失败 > 0 → exit 1
    python scripts/check_concept_code_blocks.py --sample 0 --with-deps --json tmp/cb.json --report reports/x.md
    python scripts/check_concept_code_blocks.py --stats-only    # 只提取分类，不编译
    python scripts/check_concept_code_blocks.py --ensure-deps   # 先 cargo build --workspace
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
DEPS_DIR = ROOT / "target" / "debug" / "deps"

# --- fence flags ---
IGNORE_FLAGS = {"ignore", "no_run", "norun", "allow_fail", "test_harness", "notest"}
COMPILE_FAIL_FLAGS = {"compile_fail"}
SHOULD_PANIC_FLAGS = {"should_panic"}
EDITION_FLAG_RE = re.compile(r"^edition(2015|2018|2021|2024)$")
ERRCODE_RE = re.compile(r"^E\d{4}$")

# --- 已知外部 crate（出现在 use/extern crate/路径中即视为依赖块） ---
KNOWN_CRATES = {
    "tokio", "tokio_stream", "tokio_util", "futures", "futures_util", "async_std",
    "serde", "serde_json", "serde_derive", "serde_yaml", "toml", "ron",
    "anyhow", "thiserror", "eyre", "snafu",
    "rayon", "crossbeam", "crossbeam_channel", "crossbeam_utils", "dashmap",
    "parking_lot", "flume",
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
    "bevy", "bevy_ec2", "bevy_ecs", "amethyst", "ggez", "macroquad", "winit", "wgpu", "glow",
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
    "signal_hook", "ctrlc", "daemonize",
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
    "include_dir", "rust_embed",
    "mlua", "rlua", "rhai", "gluon", "deno_core", "rune", "starlark",
    "tree_sitter", "tree_sitter_rust",
    "insta", "expect_test", "goldenfile", "assert_cmd", "predicates", "wiremock",
    "httpmock", "mockito", "httptest", "test_context",
    "ctor", "inventory", "linkme", "typetag", "erased_serde",
    "ghost", "const_panic",
    "measure_time", "coarsetime", "quanta", "tikv_jemallocator", "mimalloc",
    "miri", "kani", "verus", "prusti", "creusot", "autoverus",
    "cursive", "termion", "termwiz", "vt100",
    "threadpool", "scheduled_thread_pool", "cron", "tokio_cron_scheduler",
    "dynosaur", "miniextendr_api", "extendr_api", "r_vector",
    "orthrus", "numcodecs",
}

WORKSPACE_MEMBER_CRATES = {
    "c01_ownership_borrow_scope", "c02_type_system", "c03_control_fn", "c04_generic",
    "c05_threads", "c06_async", "c07_process", "c08_algorithms", "c09_design_pattern",
    "c10_networks", "c11_macro_system_proc", "c12_wasm", "c13_embedded",
    "c14_semantic_web", "c15_verification_tools", "c16_gui",
    "c17_resolver_v3_public_demo", "common",
}

# 已知不可能编译的环境（嵌入式/nightly-only crate）→ 直接跳过
SKIP_CRATES = {
    "cortex_m", "cortex_m_rt", "embedded_hal", "embassy", "rtic", "riscv",
    "avr_device", "heapless", "defmt", "defmt_rtt", "panic_halt",
    "panic_semihosting", "wasm_bindgen", "js_sys", "web_sys",
    "miri", "kani", "verus", "prusti", "creusot", "autoverus",
}

PSEUDO_MARKERS = ["todo!()", "unimplemented!()"]
PSEUDO_LINE_RE = re.compile(r"^\s*(//\s*)?(…|\.\.\.)\s*(//.*)?$")  # 整行只有 ... 或 …
PSEUDO_COMMENT_RE = re.compile(
    r"(伪代码|示意代码|示意：|简化示意|此处省略|代码省略|省略实现|省略细节|pseudocode|pseudo-code|placeholder)",
    re.IGNORECASE,
)

FEATURE_RE = re.compile(r"#\s*!\s*\[\s*feature\s*\(")
FENCE_RE = re.compile(
    r"^([ \t]*(?:>[ \t]*)?)```(rust[^\n]*)\n(.*?)^\1```",
    re.DOTALL | re.IGNORECASE | re.MULTILINE,
)
CRATE_USE_RE = re.compile(
    r"(?:^|\n)\s*(?:use\s+([a-zA-Z_][a-zA-Z0-9_]*)|extern\s+crate\s+([a-zA-Z_][a-zA-Z0-9_]*))"
)
CRATE_PATH_RE = re.compile(r"\b([a-z][a-z0-9_]*)::")
PRELUDE_PATHS = {
    "std", "core", "alloc", "self", "crate", "super",
    "fmt", "io", "fs", "env", "mem", "ptr", "str", "string", "vec", "option", "result",
    "iter", "ops", "cmp", "hash", "borrow", "cell", "rc", "sync", "thread", "time",
    "collections", "convert", "default", "clone", "marker", "num", "char", "error",
    "future", "task", "pin", "any", "ascii", "ffi", "path", "process", "net", "panic",
    "range", "slice", "array", "prelude", "hint", "intrinsics", "raw", "f32", "f64",
}

SAMPLE_CAP = 300
SAMPLE_SEED = 20260713
BATCH_SIZE = 300
RUSTC_TIMEOUT = 60


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


def referenced_crates(code: str) -> set[str]:
    """块中引用的疑似外部 crate（use/extern crate + 已知 crate 路径前缀）。"""
    crates: set[str] = set()
    for m in CRATE_USE_RE.finditer(code):
        name = m.group(1) or m.group(2)
        if name not in PRELUDE_PATHS:
            crates.add(name)
    for m in CRATE_PATH_RE.finditer(code):
        name = m.group(1)
        if name in PRELUDE_PATHS:
            continue
        if name in KNOWN_CRATES or name in WORKSPACE_MEMBER_CRATES:
            crates.add(name)
    return crates


def classify(block: dict) -> tuple[str, str]:
    """返回 (category, reason)。"""
    flags = set(block["flags"])
    code = block["code"]

    if flags & COMPILE_FAIL_FLAGS:
        codes = sorted(f for f in flags if ERRCODE_RE.match(f))
        return "compile_fail", "标注错误码: " + ",".join(codes) if codes else "未标注错误码"
    if flags & SHOULD_PANIC_FLAGS:
        return "should_panic", ""
    if flags & IGNORE_FLAGS:
        return "anno_ignore", "fence: " + ",".join(sorted(flags & IGNORE_FLAGS))

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

    crates = referenced_crates(code)
    if crates:
        if crates & SKIP_CRATES:
            return "dep_skip", "环境不可用: " + ",".join(sorted(crates & SKIP_CRATES))
        known = {c for c in crates if c in KNOWN_CRATES or c in WORKSPACE_MEMBER_CRATES}
        unknown = crates - known
        if unknown:
            return "dep_untested", "未知外部 crate: " + ",".join(sorted(unknown))
        return "dep", "引用 crate: " + ",".join(sorted(known))
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


def find_extern_artifacts(deps_dir: Path, crate: str) -> list[Path]:
    """在 target/debug/deps 中定位 crate 的全部候选 rmeta/rlib（proc-macro 为动态库）。
    同一 crate 可能因 feature 差异存在多个构建产物（如 tokio full vs 子集），
    返回全部候选，编译失败时轮换重试。"""
    hits: list[Path] = []
    for pat in (
        f"lib{crate}-*.rmeta", f"lib{crate}-*.rlib",
        f"{crate}-*.dll", f"lib{crate}-*.so", f"{crate}-*.so", f"lib{crate}-*.dylib",
    ):
        hits.extend(sorted(deps_dir.glob(pat)))
    return hits


def block_edition(block: dict) -> str:
    """fence 上的 editionNNNN 标注 → 对应 edition；否则默认 2024。"""
    for f in block["flags"]:
        m = EDITION_FLAG_RE.match(f)
        if m:
            return m.group(1)
    return "2024"


def rustc_compile(src: str, tmpdir: Path, tag: str, externs: list[tuple[str, Path]],
                  crate_type: str = "bin", edition: str = "2024",
                  emit: str = "metadata") -> subprocess.CompletedProcess:
    f = tmpdir / f"{tag}.rs"
    f.write_text(src, encoding="utf-8")
    cmd = ["rustc", "--edition", edition, f"--emit={emit}", "--crate-type", crate_type,
           "-o", str(tmpdir / f"{tag}.out"), str(f)]
    for name, art in externs:
        cmd += ["--extern", f"{name}={art}"]
    if externs:
        cmd += ["-L", f"dependency={DEPS_DIR}"]
    return subprocess.run(cmd, capture_output=True, text=True, timeout=RUSTC_TIMEOUT)


def compile_one(block: dict, tmpdir: Path) -> dict:
    """rustc 直接编译无依赖块。包装为 bin 失败时，回退按 lib（不包装）再试一次：
    部分纯 item 块（含 super::/mod 语义）包入 fn main 会改变模块语义。"""
    src = wrap_code(block["code"])
    h = hashlib.sha1((block["file"] + str(block["line"]) + src).encode()).hexdigest()[:12]
    ed = block_edition(block)
    try:
        r = rustc_compile(src, tmpdir, f"b_{h}", [], edition=ed)
        if r.returncode != 0 and not re.search(r"fn\s+main\s*\(", block["code"]):
            r2 = rustc_compile(unhide_lines(block["code"]), tmpdir, f"b_{h}_lib", [], "lib", ed)
            if r2.returncode == 0:
                return {**block, "status": "pass", "stderr": "", "mode": "lib"}
    except subprocess.TimeoutExpired:
        return {**block, "status": "timeout", "stderr": f"rustc timeout {RUSTC_TIMEOUT}s"}
    ok = r.returncode == 0
    return {**block, "status": "pass" if ok else "fail", "stderr": "" if ok else r.stderr}


def compile_dep_one(block: dict, tmpdir: Path) -> dict:
    """依赖块：rmeta --extern 解析后编译；找不到依赖 → dep_untested。
    多构建产物（feature 差异）时轮换候选重试，最多 4 轮；全部失败且错误为
    feature 缺失 → dep_untested（环境限制，不计入腐烂）。"""
    crates = referenced_crates(block["code"])
    cands: dict[str, list[Path]] = {}
    missing = []
    for c in sorted(crates):
        arts = find_extern_artifacts(DEPS_DIR, c)
        if not arts:
            missing.append(c)
        else:
            cands[c] = arts
    if missing:
        return {**block, "status": "dep_untested",
                "stderr": "deps 目录无 rmeta/rlib: " + ",".join(missing)}
    src = wrap_code(block["code"])
    has_main = bool(re.search(r"fn\s+main\s*\(", block["code"]))
    lib_src = unhide_lines(block["code"])
    ed = block_edition(block)
    h = hashlib.sha1((block["file"] + str(block["line"]) + src).encode()).hexdigest()[:12]
    rounds = min(max(len(v) for v in cands.values()), 8)
    last: subprocess.CompletedProcess | None = None
    try:
        for k in range(rounds):
            externs = [(c, arts[min(k, len(arts) - 1)]) for c, arts in cands.items()]
            r = rustc_compile(src, tmpdir, f"d_{h}_r{k}", externs, edition=ed)
            if r.returncode == 0:
                return {**block, "status": "pass", "stderr": ""}
            last = r
            if not has_main:
                r2 = rustc_compile(lib_src, tmpdir, f"d_{h}_r{k}_lib", externs, "lib", ed)
                if r2.returncode == 0:
                    return {**block, "status": "pass", "stderr": "", "mode": "lib"}
    except subprocess.TimeoutExpired:
        return {**block, "status": "timeout", "stderr": f"rustc timeout {RUSTC_TIMEOUT}s"}
    stderr = last.stderr if last else ""
    if "feature is disabled" in stderr or "feature may not be used" in stderr:
        return {**block, "status": "dep_untested",
                "stderr": "workspace 构建未启用所需 feature: " + summarize_stderr(stderr, 200)}
    return {**block, "status": "fail", "stderr": stderr}


def verify_compile_fail(block: dict, tmpdir: Path) -> dict:
    """compile_fail 块：期望编译失败；标注 E0xxx 时校验错误码。意外通过 → 标注腐烂。"""
    src = wrap_code(block["code"])
    h = hashlib.sha1((block["file"] + str(block["line"]) + src).encode()).hexdigest()[:12]
    want_codes = sorted(f for f in block["flags"] if ERRCODE_RE.match(f))
    ed = block_edition(block)
    try:
        r = rustc_compile(src, tmpdir, f"c_{h}", [], edition=ed)
        if r.returncode == 0 and not re.search(r"fn\s+main\s*\(", block["code"]):
            r2 = rustc_compile(unhide_lines(block["code"]), tmpdir, f"c_{h}_lib", [], "lib", ed)
            if r2.returncode != 0:
                r = r2  # lib 模式下确实失败，以 lib 诊断为准
        if r.returncode == 0:
            # --emit=metadata 会跳过常量求值阶段的 deny lint（如 unconditional_panic：
            # 常量溢出/越界索引在全量编译下确实失败）。追加 lib 全编译回退，消除误报。
            r3 = rustc_compile(src, tmpdir, f"c_{h}_full", [], "lib", ed, emit="link")
            if r3.returncode != 0:
                r = r3
    except subprocess.TimeoutExpired:
        return {**block, "status": "timeout", "stderr": f"rustc timeout {RUSTC_TIMEOUT}s"}
    if r.returncode == 0:
        return {**block, "status": "cf_unexpected_pass",
                "stderr": "compile_fail 块编译通过（标注腐烂或编译器已修复该诊断）"}
    if want_codes:
        got = set(re.findall(r"error\[(E\d{4})\]", r.stderr))
        missing = [c for c in want_codes if c not in got]
        if missing:
            return {**block, "status": "cf_wrong_code",
                    "stderr": f"标注 {','.join(want_codes)} 但实得 {','.join(sorted(got)) or '(无错误码)'}: "
                              + summarize_stderr(r.stderr, 200)}
    return {**block, "status": "cf_ok", "stderr": ""}


def verify_should_panic(block: dict, tmpdir: Path) -> dict:
    """should_panic 块：仅验证编译通过（运行期 panic 语义不执行验证）。"""
    src = wrap_code(block["code"])
    h = hashlib.sha1((block["file"] + str(block["line"]) + src).encode()).hexdigest()[:12]
    ed = block_edition(block)
    try:
        r = rustc_compile(src, tmpdir, f"s_{h}", [], edition=ed)
        if r.returncode != 0 and not re.search(r"fn\s+main\s*\(", block["code"]):
            r2 = rustc_compile(unhide_lines(block["code"]), tmpdir, f"s_{h}_lib", [], "lib", ed)
            if r2.returncode == 0:
                return {**block, "status": "pass", "stderr": "", "mode": "lib"}
    except subprocess.TimeoutExpired:
        return {**block, "status": "timeout", "stderr": f"rustc timeout {RUSTC_TIMEOUT}s"}
    ok = r.returncode == 0
    return {**block, "status": "pass" if ok else "fail", "stderr": "" if ok else r.stderr}


def summarize_stderr(stderr: str, limit: int = 600) -> str:
    errs = [ln for ln in stderr.splitlines() if ln.startswith("error")]
    return "\n".join(errs)[:limit] if errs else stderr[:limit]


def stratified_sample(candidates: list[dict], cap: int, seed: int) -> list[dict]:
    """按文件分层随机抽样（最大余数法 + 固定 seed），可复现且覆盖不同文件。"""
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


def run_batches(jobs: list[tuple[dict, str]], batch: int, n_jobs: int, with_deps: bool) -> list[dict]:
    """分批执行（每批 batch 块），批内线程池并行。jobs: (block, kind)
    kind ∈ candidate / dep / compile_fail / should_panic"""
    results: list[dict] = []
    n_batches = (len(jobs) + batch - 1) // batch
    with tempfile.TemporaryDirectory(prefix="concept_cb_") as td:
        tmpdir = Path(td)
        for bi in range(n_batches):
            chunk = jobs[bi * batch: (bi + 1) * batch]
            with ThreadPoolExecutor(max_workers=n_jobs) as ex:
                futs = []
                for b, kind in chunk:
                    if kind == "candidate":
                        futs.append(ex.submit(compile_one, b, tmpdir))
                    elif kind == "dep":
                        futs.append(ex.submit(compile_dep_one, b, tmpdir))
                    elif kind == "compile_fail":
                        futs.append(ex.submit(verify_compile_fail, b, tmpdir))
                    else:
                        futs.append(ex.submit(verify_should_panic, b, tmpdir))
                for f in futs:
                    results.append(f.result())
            if n_batches > 1:
                print(f"[batch {bi + 1}/{n_batches}] done ({len(results)}/{len(jobs)})", flush=True)
    return results


def ensure_workspace_build() -> bool:
    """cargo build --workspace 确保 target/debug/deps 存在 rmeta。"""
    print("[deps] cargo build --workspace ...", flush=True)
    try:
        r = subprocess.run(["cargo", "build", "--workspace"], cwd=ROOT,
                           capture_output=True, text=True, timeout=3600)
    except subprocess.TimeoutExpired:
        print("[deps] cargo build timeout")
        return False
    if r.returncode != 0:
        print("[deps] cargo build 失败:", (r.stderr or "").splitlines()[-1][:200])
        return False
    return True


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--strict", action="store_true",
                    help="阻断模式：应过但失败（candidate/dep/should_panic 失败 + compile_fail 标注腐烂）> 0 → exit 1")
    ap.add_argument("--with-deps", action="store_true", help="附加依赖块 rmeta --extern 实测")
    ap.add_argument("--ensure-deps", action="store_true", help="先 cargo build --workspace 确保 rmeta 存在")
    ap.add_argument("--stats-only", action="store_true")
    ap.add_argument("--sample", type=int, default=SAMPLE_CAP,
                    help="候选超过该数量时按文件分层抽样的样本上限；0=不抽样")
    ap.add_argument("--seed", type=int, default=SAMPLE_SEED)
    ap.add_argument("--batch", type=int, default=BATCH_SIZE, help="每批块数（防超时）")
    ap.add_argument("--jobs", type=int, default=8)
    ap.add_argument("--report", type=str, default="")
    ap.add_argument("--json", type=str, default="")
    args = ap.parse_args()

    if args.ensure_deps and not ensure_workspace_build():
        return 1

    files = sorted(CONCEPT_DIR.rglob("*.md"))
    files = [f for f in files if "sources" not in f.parts]
    all_blocks: list[dict] = []
    for f in files:
        all_blocks.extend(extract_blocks(f))

    buckets: dict[str, list[dict]] = {}
    for b in all_blocks:
        cat, reason = classify(b)
        b["category"] = cat
        b["reason"] = reason
        buckets.setdefault(cat, []).append(b)

    total = len(all_blocks)
    print(f"[extract] files={len(files)} blocks={total}")
    for cat in ["anno_ignore", "compile_fail", "should_panic", "pseudo", "nightly",
                "nostd", "dep_skip", "dep_untested", "dep", "candidate"]:
        n = len(buckets.get(cat, []))
        if n:
            print(f"  {cat:14s} {n}")

    if args.stats_only:
        return 0

    candidates = buckets.get("candidate", [])
    sampled_note = ""
    if args.sample and len(candidates) > args.sample:
        before = len(candidates)
        candidates = stratified_sample(candidates, args.sample, args.seed)
        sampled_note = f"（分层抽样 {len(candidates)}/{before}，seed={args.seed}）"
    if sampled_note:
        print(f"[sample] {sampled_note}")

    jobs: list[tuple[dict, str]] = [(b, "candidate") for b in candidates]
    jobs += [(b, "compile_fail") for b in buckets.get("compile_fail", [])]
    jobs += [(b, "should_panic") for b in buckets.get("should_panic", [])]
    if args.with_deps:
        jobs += [(b, "dep") for b in buckets.get("dep", [])]

    print(f"[compile] total={len(jobs)} batch={args.batch} jobs={args.jobs} with_deps={args.with_deps}")
    results = run_batches(jobs, args.batch, args.jobs, args.with_deps)

    def cnt(status: str, kind: str | None = None) -> int:
        return sum(1 for r in results if r["status"] == status
                   and (kind is None or r["category"] == kind))

    summary = {
        "total": total,
        "buckets": {k: len(v) for k, v in buckets.items()},
        "tested": len(results),
        "candidate_pass": cnt("pass", "candidate"),
        "candidate_fail": cnt("fail", "candidate"),
        "compile_fail_ok": cnt("cf_ok"),
        "compile_fail_unexpected_pass": cnt("cf_unexpected_pass"),
        "compile_fail_wrong_code": cnt("cf_wrong_code"),
        "should_panic_pass": cnt("pass", "should_panic"),
        "should_panic_fail": cnt("fail", "should_panic"),
        "dep_pass": cnt("pass", "dep"),
        "dep_fail": cnt("fail", "dep"),
        "dep_untested_runtime": cnt("dep_untested"),
        "timeout": cnt("timeout"),
    }
    rot = summary["candidate_fail"] + summary["compile_fail_unexpected_pass"] \
        + summary["compile_fail_wrong_code"] + summary["should_panic_fail"] \
        + summary["dep_fail"] + summary["timeout"]
    summary["rot_total"] = rot
    print(f"[result] candidate pass={summary['candidate_pass']} fail={summary['candidate_fail']} | "
          f"compile_fail ok={summary['compile_fail_ok']} unexpected_pass={summary['compile_fail_unexpected_pass']} "
          f"wrong_code={summary['compile_fail_wrong_code']} | "
          f"should_panic pass={summary['should_panic_pass']} fail={summary['should_panic_fail']} | "
          f"dep pass={summary['dep_pass']} fail={summary['dep_fail']} untested={summary['dep_untested_runtime']} | "
          f"timeout={summary['timeout']}")

    bad_statuses = {"fail", "cf_unexpected_pass", "cf_wrong_code", "timeout"}
    failures = [r for r in results if r["status"] in bad_statuses]
    for r in failures[:40]:
        first = summarize_stderr(r.get("stderr", ""), 200).splitlines()[0] if r.get("stderr") else ""
        print(f"  {r['status'].upper()} {r['file']}:{r['line']} [{r['category']}] :: {first}")
    if len(failures) > 40:
        print(f"  ... and {len(failures) - 40} more (see --json/--report)")

    if args.json:
        payload = {
            "summary": summary,
            "results": [
                {"file": r["file"], "line": r["line"], "index": r["index"],
                 "category": r["category"], "status": r["status"],
                 "reason": r.get("reason", ""),
                 "error": summarize_stderr(r.get("stderr", "")) if r["status"] in bad_statuses else ""}
                for r in results
            ],
        }
        Path(args.json).write_text(json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8")
        print(f"[json] -> {args.json}")

    if args.report:
        write_report(Path(args.report), summary, results, failures)

    if rot:
        print(f"[gate] 应过但失败/标注腐烂: {rot} 块（详见 --json/--report）")
    if args.strict and rot > 0:
        print(f"[gate] STRICT: rot={rot} > 0 → exit 1")
        return 1
    if not args.strict:
        print("[gate] 观察模式：exit 0")
    return 0


def write_report(path: Path, summary: dict, results: list[dict], failures: list[dict]):
    lines = ["# concept/ 代码块编译实测报告", "", "## 分类统计", ""]
    lines.append("| 分类 | 数量 |")
    lines.append("|---|---:|")
    labels = {
        "anno_ignore": "标注跳过(ignore/no_run)",
        "compile_fail": "compile_fail（验证确实失败）",
        "should_panic": "should_panic（验证编译通过）",
        "pseudo": "伪代码/占位跳过",
        "nightly": "nightly-only(#![feature])",
        "nostd": "no_std/no_main",
        "dep_skip": "依赖环境不可用(嵌入式/wasm/验证工具)",
        "dep_untested": "需依赖未测(未知 crate)",
        "dep": "依赖块(workspace 依赖,可测)",
        "candidate": "无依赖编译候选",
    }
    for k, label in labels.items():
        if summary["buckets"].get(k):
            lines.append(f"| {label} | {summary['buckets'][k]} |")
    lines.append(f"| **合计** | **{summary['total']}** |")
    lines += ["", "## 实测统计", "",
              f"- 实测块: {summary['tested']}",
              f"- candidate: pass={summary['candidate_pass']} fail={summary['candidate_fail']}",
              f"- compile_fail: ok={summary['compile_fail_ok']} "
              f"unexpected_pass={summary['compile_fail_unexpected_pass']} "
              f"wrong_code={summary['compile_fail_wrong_code']}",
              f"- should_panic: pass={summary['should_panic_pass']} fail={summary['should_panic_fail']}",
              f"- dep: pass={summary['dep_pass']} fail={summary['dep_fail']} "
              f"untested(无 rmeta)={summary['dep_untested_runtime']}",
              f"- timeout: {summary['timeout']}",
              f"- **应过但失败/标注腐烂合计: {summary['rot_total']}**", ""]
    if failures:
        lines += ["## 失败/腐烂清单", "", "| 文件 | 行 | 分类 | 状态 | 错误摘要 |", "|---|---:|---|---|---|"]
        for r in failures:
            err = summarize_stderr(r.get("stderr", ""), 300).replace("|", "\\|").replace("\n", "<br>")
            lines.append(f"| `{r['file']}` | {r['line']} | {r['category']} | {r['status']} | {err} |")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"[report] -> {path}")


if __name__ == "__main__":
    sys.exit(main())
