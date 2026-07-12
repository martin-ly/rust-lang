#!/usr/bin/env python3
"""
主题-权威来源对齐器 (Topic Authority Aligner)

功能：
1. 扫描项目当前 Markdown 资产，抽取主题树。
2. 抓取/解析权威来源（Rust 官方文档、形式化验证生态、工业应用生态、路线图）。
3. 计算对称差，识别未覆盖空间。
4. 生成项目索引资产与行动计划报告。

用法：
    python scripts/topic_authority_aligner.py [--phase {1,2,3,4,5,all}]
"""
from pathlib import Path
import re
import json
import argparse
import sys
from datetime import datetime

ROOT = Path(__file__).resolve().parent.parent
TMP_DIR = ROOT / "tmp"
REPORTS_DIR = ROOT / "reports"
META_DIR = ROOT / "concept" / "00_meta"


def read_text(path, fallback=""):
    try:
        return path.read_text(encoding="utf-8", errors="ignore")
    except Exception:
        return fallback


def parse_frontmatter(text):
    """提取 YAML frontmatter 为 dict（仅简单键值）。"""
    fm = {}
    if text.startswith("---"):
        parts = text.split("---", 2)
        if len(parts) >= 3:
            content = parts[1]
            for line in content.splitlines():
                if ":" in line and not line.strip().startswith("-"):
                    k, v = line.split(":", 1)
                    fm[k.strip().lower()] = v.strip().strip('"').strip("'")
    return fm


def extract_headings(text, max_level=3):
    """提取 Markdown 标题。"""
    headings = []
    for line in text.splitlines():
        m = re.match(r"^(#{1,%d})\s+(.+)$" % max_level, line.strip())
        if m:
            level = len(m.group(1))
            title = m.group(2).strip()
            title = re.sub(r"\s*\{#.*?\}\s*$", "", title)
            headings.append((level, title))
    return headings


def extract_concept_topics():
    """扫描 concept/ 目录，提取主题。"""
    topics = []
    concept_dir = ROOT / "concept"
    for f in concept_dir.rglob("*.md"):
        if "archive" in f.parts or f.name in ("README.md", "SUMMARY.md"):
            continue
        text = read_text(f)
        fm = parse_frontmatter(text)
        headings = extract_headings(text, max_level=3)
        layer = "L0_meta"
        for part in f.parts:
            if part.startswith("0") and part[1:2].isdigit() and "_" in part:
                layer = "L" + part[:2]
                break
        title = fm.get("title") or (headings[0][1] if headings else f.stem)
        topics.append({
            "source": "concept",
            "layer": layer,
            "path": str(f.relative_to(ROOT)).replace("\\", "/"),
            "filename": f.name,
            "title": title,
            "headings": headings[:10],
            "frontmatter": fm,
        })
    return topics


def extract_index_topics():
    """从索引文件抽取额外主题映射。"""
    indexes = [
        ROOT / "knowledge" / "INDEX.md",
        ROOT / "docs" / "research_notes" / "INDEX.md",
        ROOT / "content" / "README.md",
        ROOT / "crates" / "README.md",
    ]
    topics = []
    for idx_file in indexes:
        if not idx_file.exists():
            continue
        text = read_text(idx_file)
        for line in text.splitlines():
            m = re.search(r"\[([^\]]+)\]\(([^)]+\.md)\)", line)
            if m:
                topics.append({
                    "source": "index",
                    "index_file": str(idx_file.relative_to(ROOT)).replace("\\", "/"),
                    "title": m.group(1).strip(),
                    "path": m.group(2).strip(),
                })
    return topics


def parse_summary(text, book_key, book_name, base_url):
    """解析 mdBook SUMMARY.md，返回主题树。"""
    topics = []
    stack = []
    for line in text.splitlines():
        stripped = line.rstrip()
        if not stripped:
            continue
        indent = len(stripped) - len(stripped.lstrip())
        level = indent // 4 + 1
        m = re.match(r"^\s*[-*]\s+\[([^\]]+)\]\(([^)]+)\)", stripped)
        if not m:
            continue
        title = m.group(1).strip()
        file_path = m.group(2).strip()
        while len(stack) >= level:
            stack.pop()
        parent = stack[-1]["title"] if stack else book_name
        stack.append({"title": title, "level": level})
        topics.append({
            "source": "official_doc",
            "book": book_name,
            "book_key": book_key,
            "level": level,
            "parent": parent,
            "title": title,
            "path": file_path,
            "url": f"{base_url}/{file_path.replace('.md', '.html')}",
        })
    return topics


STOPWORDS = {
    "the", "a", "an", "and", "or", "of", "in", "on", "at", "to", "for", "with",
    "by", "from", "as", "is", "are", "was", "were", "be", "been", "being", "have",
    "has", "had", "do", "does", "did", "will", "would", "could", "should", "may",
    "might", "can", "shall", "this", "that", "these", "those", "it", "its", "using",
    "how", "what", "when", "where", "why", "who", "which", "your", "you", "we", "our",
}

RUST_KEYWORDS = {
    "ownership", "borrow", "borrowing", "lifetime", "lifetimes", "trait", "traits",
    "generic", "generics", "type", "types", "async", "await", "unsafe", "macro",
    "macros", "concurrency", "concurrent", "parallel", "memory", "error", "errors",
    "panic", "result", "option", "module", "modules", "cargo", "crate", "crates",
    "ffi", "wasm", "webassembly", "embedded", "pattern", "patterns", "closure",
    "closures", "iterator", "iterators", "testing", "test", "tests", "pin", "future",
    "futures", "struct", "structs", "enum", "enums", "match", "move", "copy", "clone",
    "send", "sync", "reference", "references", "pointer", "pointers", "variance",
    "subtype", "coercion", "cast", "attribute", "attributes", "derive", "proc",
    "workspace", "dependency", "dependencies", "feature", "features", "profile",
    "profiles", "lint", "lints", "build", "script", "registry", "semver", "publish",
    "installation", "hello", "world", "guessing", "game", "collections", "vector",
    "vectors", "string", "strings", "hash", "map", "io", "file", "command", "line",
    "project", "package", "packages", "path", "paths", "use", "pub", "private",
    "scope", "privacy", "function", "functions", "method", "methods", "loop",
    "while", "for", "if", "else", "let", "const", "static", "mut", "ref",
}


def tokenize(text):
    """分词并返回小写非停用词集合。"""
    if not text:
        return set()
    text = text.lower()
    text = re.sub(r"[^\w\s]", " ", text)
    tokens = set()
    for w in text.split():
        w = w.strip()
        if len(w) > 1 and w not in STOPWORDS:
            tokens.add(w)
    return tokens


def match_score(authority_tokens, project_tokens):
    """返回 0-1 的匹配分数。"""
    if not authority_tokens:
        return 0.0
    intersection = authority_tokens & project_tokens
    if not intersection:
        return 0.0
    keyword_hits = intersection & RUST_KEYWORDS
    base_score = len(intersection) / len(authority_tokens)
    if keyword_hits:
        base_score += 0.15 * min(1.0, len(keyword_hits) / 2)
    return min(1.0, base_score)


def find_best_match(auth_topic, project_topics, threshold=0.45):
    """在项目中找到与权威主题最匹配的条目。先检查人工别名映射，再进行模糊匹配。"""
    title = auth_topic.get("title", "")
    alias_target = AUTHORITY_TOPIC_ALIASES.get(title)
    if alias_target:
        for pt in project_topics:
            if pt.get("path") == alias_target or alias_target in pt.get("path", ""):
                return pt, 1.0

    auth_tokens = tokenize(title)
    auth_tokens |= tokenize(auth_topic.get("domain", ""))
    auth_tokens |= tokenize(auth_topic.get("book", ""))
    if not auth_tokens:
        return None, 0.0

    best = None
    best_score = 0.0
    for pt in project_topics:
        project_tokens = set()
        project_tokens |= tokenize(pt.get("title", ""))
        project_tokens |= tokenize(pt.get("path", ""))
        project_tokens |= tokenize(pt.get("filename", ""))
        for h in pt.get("headings", []):
            project_tokens |= tokenize(h[1] if isinstance(h, (list, tuple)) else str(h))

        score = match_score(auth_tokens, project_tokens)
        if score > best_score:
            best_score = score
            best = pt

    if best_score >= threshold:
        return best, best_score
    return None, best_score


def save_json(data, path):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8", newline="\n")


OFFICIAL_BOOKS = {
    "book": ("The Rust Programming Language", "https://doc.rust-lang.org/book"),
    "reference": ("The Rust Reference", "https://doc.rust-lang.org/reference"),
    "nomicon": ("The Rustonomicon", "https://doc.rust-lang.org/nomicon"),
    "rust-by-example": ("Rust By Example", "https://doc.rust-lang.org/rust-by-example"),
    "cargo": ("The Cargo Book", "https://doc.rust-lang.org/cargo"),
    "rustc": ("The rustc Book", "https://doc.rust-lang.org/rustc"),
    "embedded": ("The Embedded Rust Book", "https://doc.rust-lang.org/embedded-book"),
    "edition-guide": ("The Rust Edition Guide", "https://doc.rust-lang.org/edition-guide"),
    "async-book": ("Asynchronous Programming in Rust", "https://rust-lang.github.io/async-book"),
    "wasm-book": ("Rust and WebAssembly", "https://rustwasm.github.io/docs/book"),
}


FORMAL_VERIFICATION_TOPICS = [
    {"source": "formal", "domain": "Separation Logic / Ownership", "title": "RustBelt: Logical Relations for Rust", "url": "https://plv.mpi-sws.org/rustbelt/"},
    {"source": "formal", "domain": "Separation Logic / Ownership", "title": "Iris: Higher-Order Concurrent Separation Logic Framework", "url": "https://iris-project.org/"},
    {"source": "formal", "domain": "Type System", "title": "Aeneas: Symbolic Semantics for Rust", "url": "https://github.com/AeneasVerif/aeneas"},
    {"source": "formal", "domain": "Type System", "title": "Prusti: Deductive Verification for Rust", "url": "https://www.pm.inf.ethz.ch/research/prusti.html"},
    {"source": "formal", "domain": "Model Checking", "title": "Kani: Rust Model Checker", "url": "https://model-checking.github.io/kani/"},
    {"source": "formal", "domain": "Theorem Proving", "title": "Verus: Verified Rust for Low-Level Systems", "url": "https://verus-lang.github.io/verus/"},
    {"source": "formal", "domain": "Undefined Behavior Detection", "title": "Miri: Rust Interpreter for Undefined Behavior", "url": "https://github.com/rust-lang/miri"},
    {"source": "formal", "domain": "Alias Model", "title": "Tree Borrows / Stacked Borrows", "url": "https://github.com/rust-lang/unsafe-code-guidelines/blob/master/wip/stacked-borrows.md"},
    {"source": "formal", "domain": "Safety Certification", "title": "Ferrocene: Rust for Safety-Critical Systems", "url": "https://ferrocene.dev/"},
    {"source": "formal", "domain": "Type System", "title": "Safety Tags / Type Safety Tags", "url": "https://rust-lang.github.io/rfcs/0000-safety-tags.html"},
    {"source": "formal", "domain": "Memory Safety", "title": "Borrow Sanitizer", "url": "https://github.com/rust-lang/miri/blob/master/BORROW_SANITIZER.md"},
    {"source": "formal", "domain": "Specification", "title": "Rust Specification (lang-spec-rust-lang-org)", "url": "https://github.com/rust-lang/spec"},
]


INDUSTRIAL_ECOSYSTEM_TOPICS = [
    {"source": "industrial", "domain": "Async Runtime", "title": "Tokio", "url": "https://tokio.rs/"},
    {"source": "industrial", "domain": "Web Framework", "title": "Axum", "url": "https://docs.rs/axum/latest/axum/"},
    {"source": "industrial", "domain": "Web Framework", "title": "Actix-web", "url": "https://actix.rs/"},
    {"source": "industrial", "domain": "ORM", "title": "Sea-ORM", "url": "https://www.sea-ql.org/SeaORM/"},
    {"source": "industrial", "domain": "Database Driver", "title": "sqlx", "url": "https://github.com/launchbadge/sqlx"},
    {"source": "industrial", "domain": "Game Engine", "title": "Bevy", "url": "https://bevyengine.org/"},
    {"source": "industrial", "domain": "GUI / Cross-platform", "title": "Tauri", "url": "https://tauri.app/"},
    {"source": "industrial", "domain": "GUI / Cross-platform", "title": "Dioxus", "url": "https://dioxuslabs.com/"},
    {"source": "industrial", "domain": "GUI / Web", "title": "Leptos", "url": "https://leptos.dev/"},
    {"source": "industrial", "domain": "GUI / Immediate Mode", "title": "egui", "url": "https://www.egui.rs/"},
    {"source": "industrial", "domain": "Python Interop", "title": "PyO3", "url": "https://pyo3.rs/"},
    {"source": "industrial", "domain": "FFI / C Interop", "title": "bindgen / cbindgen", "url": "https://rust-lang.github.io/rust-bindgen/"},
    {"source": "industrial", "domain": "WASM", "title": "wasm-bindgen / web-sys", "url": "https://rustwasm.github.io/wasm-bindgen/"},
    {"source": "industrial", "domain": "Concurrency", "title": "crossbeam", "url": "https://docs.rs/crossbeam/latest/crossbeam/"},
    {"source": "industrial", "domain": "Data Parallelism", "title": "rayon", "url": "https://docs.rs/rayon/latest/rayon/"},
    {"source": "industrial", "domain": "Synchronization", "title": "parking_lot", "url": "https://docs.rs/parking_lot/latest/parking_lot/"},
    {"source": "industrial", "domain": "Serialization", "title": "serde", "url": "https://serde.rs/"},
    {"source": "industrial", "domain": "CLI", "title": "clap", "url": "https://docs.rs/clap/latest/clap/"},
    {"source": "industrial", "domain": "Error Handling", "title": "anyhow / thiserror", "url": "https://docs.rs/anyhow/latest/anyhow/"},
    {"source": "industrial", "domain": "Async HTTP Client", "title": "reqwest", "url": "https://docs.rs/reqwest/latest/reqwest/"},
    {"source": "industrial", "domain": "gRPC", "title": "tonic", "url": "https://github.com/hyperium/tonic"},
    {"source": "industrial", "domain": "Metrics / Observability", "title": "tracing / opentelemetry", "url": "https://docs.rs/tracing/latest/tracing/"},
    {"source": "industrial", "domain": "Embedded HAL", "title": "embedded-hal", "url": "https://docs.rs/embedded-hal/latest/embedded_hal/"},
    {"source": "industrial", "domain": "No-std / Bare Metal", "title": "cortex-m / riscv-rt", "url": "https://docs.rs/cortex-m/latest/cortex_m/"},
    {"source": "industrial", "domain": "Crypto", "title": "ring / rustls", "url": "https://github.com/briansmith/ring"},
]


ROADMAP_TOPICS = [
    {"source": "roadmap", "domain": "Project Goals 2025 H1", "title": "Rust Project Goals 2025 H1", "url": "https://rust-lang.github.io/rust-project-goals/2025h1/index.html"},
    {"source": "roadmap", "domain": "Edition", "title": "Rust 2024 Edition", "url": "https://doc.rust-lang.org/edition-guide/rust-2024/index.html"},
    {"source": "roadmap", "domain": "Async", "title": "Async Closures / Async Fn in Traits", "url": "https://rust-lang.github.io/rfcs/3185-static-async-fn-in-trait.html"},
    {"source": "roadmap", "domain": "Type System", "title": "Specialization / Min Specialization", "url": "https://rust-lang.github.io/rfcs/1210-impl-specialization.html"},
    {"source": "roadmap", "domain": "Type System", "title": "Generic Associated Types (GATs)", "url": "https://rust-lang.github.io/rfcs/1598-generic_associated_types.html"},
    {"source": "roadmap", "domain": "Type System", "title": "Type Alias Impl Trait (TAIT)", "url": "https://rust-lang.github.io/rfcs/2515-type-alias-impl-trait.html"},
    {"source": "roadmap", "domain": "Type System", "title": "Return Type Notation (RTN)", "url": "https://rust-lang.github.io/rfcs/3654-new-return-type-notation.html"},
    {"source": "roadmap", "domain": "Type System", "title": "Precise Capturing / Lifetime Capture", "url": "https://rust-lang.github.io/rfcs/0000-lifetime-capture.html"},
    {"source": "roadmap", "domain": "Unsafe", "title": "Unsafe Fields / Unsafe extern blocks", "url": "https://rust-lang.github.io/rfcs/0000-unsafe-extern-blocks.html"},
    {"source": "roadmap", "domain": "Unsafe", "title": "Arbitrary Self Types v2", "url": "https://rust-lang.github.io/rfcs/3519-arbitrary-self-types-v2.html"},
    {"source": "roadmap", "domain": "Macros", "title": "Derive CoercePointee", "url": "https://rust-lang.github.io/rfcs/3693-derive-coerce-pointee.html"},
    {"source": "roadmap", "domain": "Compiler", "title": "Parallel Frontend", "url": "https://blog.rust-lang.org/inside-rust/2024/04/24/parallel-front-end.html"},
    {"source": "roadmap", "domain": "Compiler", "title": "Cranelift Backend", "url": "https://github.com/bjorn3/rustc_codegen_cranelift"},
    {"source": "roadmap", "domain": "Tooling", "title": "Cargo SemVer Checks", "url": "https://github.com/obi1kenobi/cargo-semver-checks"},
    {"source": "roadmap", "domain": "Tooling", "title": "MCDC Coverage", "url": "https://github.com/rust-lang/rust/pull/124658"},
    {"source": "roadmap", "domain": "Tooling", "title": "Rustdoc Search / Scraped Examples", "url": "https://doc.rust-lang.org/rustdoc/scraped-examples.html"},
]

# 人工校准映射：权威主题标题 -> 项目文件路径（或路径子串）
# 用于修正标题差异导致的假缺口；命中时直接视为完全对齐。
AUTHORITY_TOPIC_ALIASES = {
    # 形式化/验证生态
    "Iris: Higher-Order Concurrent Separation Logic Framework": "concept/04_formal/02_separation_logic/02_separation_logic.md",
    "Borrow Sanitizer": "concept/07_future/03_preview_features/24_borrow_sanitizer.md",
    "Miri: Rust Interpreter for Undefined Behavior": "concept/04_formal/04_model_checking/08_miri.md",
    "Ferrocene: Rust for Safety-Critical Systems": "concept/07_future/03_preview_features/12_ferrocene_preview.md",
    "Verus: Verified Rust for Low-Level Systems": "concept/04_formal/04_model_checking/04_modern_verification_tools.md",
    # 工业/应用生态
    "bindgen / cbindgen": "concept/03_advanced/04_ffi/01_rust_ffi.md",
    "reqwest": "concept/06_ecosystem/04_web_and_networking/03_web_frameworks.md",
    "sqlx": "concept/06_ecosystem/06_data_and_distributed/02_database_access.md",
    "Tauri": "concept/06_ecosystem/04_web_and_networking/03_web_frameworks.md",
    "Dioxus": "concept/06_ecosystem/04_web_and_networking/03_web_frameworks.md",
    "Leptos": "concept/06_ecosystem/04_web_and_networking/03_web_frameworks.md",
    "egui": "concept/06_ecosystem/11_domain_applications/02_game_ecs.md",
    "PyO3": "concept/06_ecosystem/11_domain_applications/14_industrial_case_studies.md",
    "rayon": "concept/03_advanced/00_concurrency/03_concurrency_patterns.md",
    # 项目路线图
    "Cranelift Backend": "concept/07_future/03_preview_features/16_cranelift_backend_preview.md",
    "MCDC Coverage": "concept/07_future/03_preview_features/02_mcdc_coverage_preview.md",
    "Rustdoc Search / Scraped Examples": "concept/06_ecosystem/09_testing_and_quality/02_documentation.md",
    "cortex-m / riscv-rt": "concept/06_ecosystem/05_systems_and_embedded/03_embedded_systems.md",
    "ring / rustls": "concept/06_ecosystem/07_security_and_cryptography/02_security_cryptography.md",
}


def phase1():
    print("=== Phase 1: 抽取当前项目主题 ===")
    concept_topics = extract_concept_topics()
    index_topics = extract_index_topics()
    inventory = {
        "generated_at": datetime.now().isoformat(),
        "concept_topics": concept_topics,
        "index_topics": index_topics,
        "stats": {
            "concept_files": len(concept_topics),
            "index_entries": len(index_topics),
        },
    }
    save_json(inventory, TMP_DIR / "topic_inventory_current.json")
    print(f"  concept 主题数: {len(concept_topics)}")
    print(f"  索引条目数: {len(index_topics)}")
    print(f"  已保存: {TMP_DIR / 'topic_inventory_current.json'}")


def phase2():
    print("=== Phase 2: 抽取权威来源主题 ===")
    summary_dir = TMP_DIR / "authority_summaries"
    summary_dir.mkdir(parents=True, exist_ok=True)
    official_topics = []
    for key, (name, base_url) in OFFICIAL_BOOKS.items():
        summary_file = summary_dir / f"{key}.md"
        text = read_text(summary_file)
        if not text:
            print(f"  [跳过] 无本地 SUMMARY: {name}")
            continue
        topics = parse_summary(text, key, name, base_url)
        official_topics.extend(topics)
        print(f"  {name}: {len(topics)} 个主题")

    all_authority = {
        "generated_at": datetime.now().isoformat(),
        "official_docs": official_topics,
        "formal_verification": FORMAL_VERIFICATION_TOPICS,
        "industrial_ecosystem": INDUSTRIAL_ECOSYSTEM_TOPICS,
        "roadmap": ROADMAP_TOPICS,
        "stats": {
            "official_doc_topics": len(official_topics),
            "formal_verification_topics": len(FORMAL_VERIFICATION_TOPICS),
            "industrial_ecosystem_topics": len(INDUSTRIAL_ECOSYSTEM_TOPICS),
            "roadmap_topics": len(ROADMAP_TOPICS),
        },
    }
    save_json(all_authority, TMP_DIR / "topic_inventory_authoritative.json")
    print(f"\n权威来源主题总数: {sum(all_authority['stats'].values())}")
    print(f"  已保存: {TMP_DIR / 'topic_inventory_authoritative.json'}")


def phase3():
    print("=== Phase 3: 主题对齐与对称差计算 ===")
    current = json.loads(read_text(TMP_DIR / "topic_inventory_current.json", "{}"))
    authority = json.loads(read_text(TMP_DIR / "topic_inventory_authoritative.json", "{}"))

    project_topics = current.get("concept_topics", [])
    auth_topics = []
    for key in ["official_docs", "formal_verification", "industrial_ecosystem", "roadmap"]:
        for t in authority.get(key, []):
            t["category"] = key
            auth_topics.append(t)

    aligned = []
    only_in_authority = []
    project_matched = set()

    for at in auth_topics:
        best, score = find_best_match(at, project_topics)
        if best:
            project_matched.add(best["path"])
            aligned.append({
                "authority": at,
                "project_match": {
                    "path": best["path"],
                    "title": best["title"],
                    "layer": best.get("layer"),
                },
                "score": round(score, 3),
            })
        else:
            only_in_authority.append({
                "authority": at,
                "best_score": round(score, 3),
            })

    only_in_project = [pt for pt in project_topics if pt["path"] not in project_matched]

    gap_by_category = {}
    for item in only_in_authority:
        cat = item["authority"].get("category", "unknown")
        gap_by_category.setdefault(cat, []).append(item)
    gap_counts = {k: len(v) for k, v in gap_by_category.items()}

    diff = {
        "generated_at": datetime.now().isoformat(),
        "stats": {
            "project_topics": len(project_topics),
            "authority_topics": len(auth_topics),
            "aligned": len(aligned),
            "only_in_authority": len(only_in_authority),
            "only_in_project": len(only_in_project),
        },
        "gap_by_category": gap_counts,
        "aligned": aligned,
        "only_in_authority": only_in_authority,
        "only_in_project": only_in_project,
    }
    save_json(diff, TMP_DIR / "topic_symmetric_diff.json")

    matrix_path = TMP_DIR / "topic_alignment_matrix.tsv"
    with open(matrix_path, "w", encoding="utf-8", newline="\n") as f:
        f.write("category\tauthority_title\tauthority_domain\tproject_path\tproject_title\tscore\tstatus\n")
        for item in aligned:
            a = item["authority"]
            p = item["project_match"]
            f.write(f"{a.get('category','')}\t{a.get('title','')}\t{a.get('domain','') or a.get('book','')}\t{p['path']}\t{p['title']}\t{item['score']}\taligned\n")
        for item in only_in_authority:
            a = item["authority"]
            f.write(f"{a.get('category','')}\t{a.get('title','')}\t{a.get('domain','') or a.get('book','')}\t\t\t{item['best_score']}\tgap\n")

    print(f"  项目主题数: {len(project_topics)}")
    print(f"  权威主题数: {len(auth_topics)}")
    print(f"  已对齐: {len(aligned)}")
    print(f"  权威独有 (缺口): {len(only_in_authority)}")
    print(f"  项目独有: {len(only_in_project)}")
    print("  缺口按类别:")
    for k, v in sorted(gap_counts.items(), key=lambda x: -x[1]):
        print(f"    {k}: {v}")
    print(f"  已保存: {TMP_DIR / 'topic_symmetric_diff.json'}")
    print(f"  已保存: {matrix_path}")


def phase4():
    print("=== Phase 4: 生成项目索引资产 ===")
    current = json.loads(read_text(TMP_DIR / "topic_inventory_current.json", "{}"))
    diff = json.loads(read_text(TMP_DIR / "topic_symmetric_diff.json", "{}"))

    project_topics = current.get("concept_topics", [])
    aligned = diff.get("aligned", [])
    only_in_authority = diff.get("only_in_authority", [])
    only_in_project = diff.get("only_in_project", [])

    # Build current topic tree by layer
    layers = {}
    for pt in project_topics:
        layers.setdefault(pt["layer"], []).append(pt)
    for k in layers:
        layers[k].sort(key=lambda x: x["path"])

    # Categorize gaps by priority
    p0_keywords = ["ownership", "borrow", "lifetime", "trait", "generic", "type system",
                   "async", "unsafe", "concurrency", "error handling", "module", "cargo",
                   "macro", "ffi", "testing", "match", "struct", "enum"]
    p1_keywords = ["rustbelt", "iris", "aeneas", "kani", "verus", "miri", "ferrocene",
                   "tree borrows", "separation logic", "formal", "verification"]
    p2_keywords = ["tokio", "axum", "sea-orm", "sqlx", "bevy", "tauri", "dioxus",
                   "leptos", "egui", "pyo3", "bindgen", "rayon", "crossbeam",
                   "tracing", "embedded-hal", "serde", "clap"]
    p3_keywords = ["edition", "specialization", "tait", "rtn", "cranelift", "parallel frontend",
                   "semver", "mcdc", "unsafe fields", "arbitrary self types", "coerce pointee"]

    def priority_of(item):
        title = (item["authority"].get("title", "") + " " +
                 item["authority"].get("domain", "")).lower()
        if any(k in title for k in p0_keywords):
            return "P0 官方核心"
        if any(k in title for k in p1_keywords):
            return "P1 形式化/验证"
        if any(k in title for k in p2_keywords):
            return "P2 工业生态"
        if any(k in title for k in p3_keywords):
            return "P3 前沿探索"
        return "P3 前沿探索"

    gaps_by_priority = {}
    for item in only_in_authority:
        p = priority_of(item)
        gaps_by_priority.setdefault(p, []).append(item)

    # Detect duplicate/overlap candidates in project
    duplicates = []
    titles_seen = {}
    for pt in project_topics:
        title_norm = pt["title"].lower().replace(" ", "_").replace("-", "_")
        if title_norm in titles_seen:
            duplicates.append((titles_seen[title_norm], pt))
        else:
            titles_seen[title_norm] = pt

    # Build aligned summary by layer
    aligned_by_layer = {}
    for item in aligned:
        layer = item["project_match"].get("layer") or "unknown"
        aligned_by_layer.setdefault(layer, []).append(item)

    # Write index asset (canonical location under 00_meta/02_sources)
    meta_file = META_DIR / "02_sources" / "topic_authority_alignment_map.md"
    lines = []
    lines.append("# 主题-权威来源对齐图谱 (Topic-Authority Alignment Map)\n")
    lines.append(f"> 生成时间：{datetime.now().strftime('%Y-%m-%d %H:%M')}\n")
    lines.append("> 工具：`scripts/topic_authority_aligner.py` | 数据来源：Rust 官方文档、形式化/验证生态、工业生态、项目路线图\n\n")

    lines.append("## 1. 当前项目概念层级（L0-L7）\n\n")
    for layer in sorted(layers.keys()):
        topics = layers[layer]
        lines.append(f"### {layer}（{len(topics)} 篇）\n\n")
        for pt in topics[:30]:
            lines.append(f"- `{pt['path']}` — {pt['title']}\n")
        if len(topics) > 30:
            lines.append(f"- … 共 {len(topics)} 篇\n")
        lines.append("\n")

    lines.append("## 2. 权威来源覆盖统计\n\n")
    lines.append("| 来源类别 | 权威主题数 | 已对齐 | 缺口 | 覆盖率 |\n")
    lines.append("|----------|-----------|--------|------|--------|\n")
    cat_stats = {}
    for item in aligned:
        cat = item["authority"].get("category", "unknown")
        cat_stats.setdefault(cat, {"aligned": 0, "gap": 0})
        cat_stats[cat]["aligned"] += 1
    for item in only_in_authority:
        cat = item["authority"].get("category", "unknown")
        cat_stats.setdefault(cat, {"aligned": 0, "gap": 0})
        cat_stats[cat]["gap"] += 1
    for cat in ["official_docs", "formal_verification", "industrial_ecosystem", "roadmap"]:
        if cat in cat_stats:
            s = cat_stats[cat]
            total = s["aligned"] + s["gap"]
            coverage = s["aligned"] / total * 100 if total else 0
            lines.append(f"| {cat} | {total} | {s['aligned']} | {s['gap']} | {coverage:.1f}% |\n")
    lines.append("\n")

    lines.append("## 3. 未覆盖空间（按优先级分组）\n\n")
    lines.append("> 注：以下缺口基于标题/路径关键词匹配，部分可能已被项目文件间接覆盖但标题未体现，需人工复核。\n\n")
    for priority in ["P0 官方核心", "P1 形式化/验证", "P2 工业生态", "P3 前沿探索"]:
        gaps = gaps_by_priority.get(priority, [])
        lines.append(f"### {priority}（{len(gaps)} 项）\n\n")
        for item in gaps[:40]:
            a = item["authority"]
            domain = a.get("domain") or a.get("book") or ""
            url = a.get("url", "")
            lines.append(f"- **{a['title']}**")
            if domain:
                lines.append(f" — {domain}")
            if url:
                lines.append(f" [{url}]({url})")
            lines.append("\n")
        if len(gaps) > 40:
            lines.append(f"- … 共 {len(gaps)} 项，详见 `tmp/topic_symmetric_diff.json`\n")
        lines.append("\n")

    lines.append("## 4. 项目独有主题（权威来源未直接强调）\n\n")
    lines.append(f"> 共 {len(only_in_project)} 个 concept 文件未被权威来源主题直接命中。这些多为项目特色的中文学习路径、对比分析、决策树或生态 deep-dive。\n\n")
    for pt in only_in_project[:40]:
        lines.append(f"- `{pt['path']}` — {pt['title']}\n")
    if len(only_in_project) > 40:
        lines.append(f"- … 共 {len(only_in_project)} 项\n")
    lines.append("\n")

    lines.append("## 5. 重复/需合并主题提示\n\n")
    if duplicates:
        lines.append(f"> 检测到 {len(duplicates)} 对标题高度相似的主题，建议人工复核是否重复。\n\n")
        for a, b in duplicates[:20]:
            lines.append(f"- `{a['path']}` vs `{b['path']}` — {a['title']}\n")
    else:
        lines.append("> 未检测到明显标题重复。\n\n")

    lines.append("## 6. 维护机制\n\n")
    lines.append("1. 每季度运行 `python scripts/topic_authority_aligner.py --phase all` 更新本文件。\n")
    lines.append("2. 新缺口优先进入 `reports/TOPIC_ALIGNMENT_AND_GAP_PLAN_*.md` 任务池。\n")
    lines.append("3. 已确认覆盖的缺口从本文件移除或标记为 `verified-covered`。\n\n")

    meta_file.write_text("".join(lines), encoding="utf-8", newline="\n")
    print(f"  已生成: {meta_file}")


def phase5():
    print("=== Phase 5: 生成行动计划报告 ===")
    current = json.loads(read_text(TMP_DIR / "topic_inventory_current.json", "{}"))
    diff = json.loads(read_text(TMP_DIR / "topic_symmetric_diff.json", "{}"))

    project_topics = current.get("concept_topics", [])
    aligned = diff.get("aligned", [])
    only_in_authority = diff.get("only_in_authority", [])
    only_in_project = diff.get("only_in_project", [])
    stats = diff.get("stats", {})

    p0_keywords = ["ownership", "borrow", "lifetime", "trait", "generic", "type system",
                   "async", "unsafe", "concurrency", "error handling", "module", "cargo",
                   "macro", "ffi", "testing", "match", "struct", "enum"]
    p1_keywords = ["rustbelt", "iris", "aeneas", "kani", "verus", "miri", "ferrocene",
                   "tree borrows", "separation logic", "formal", "verification"]
    p2_keywords = ["tokio", "axum", "sea-orm", "sqlx", "bevy", "tauri", "dioxus",
                   "leptos", "egui", "pyo3", "bindgen", "rayon", "crossbeam",
                   "tracing", "embedded-hal", "serde", "clap"]
    p3_keywords = ["edition", "specialization", "tait", "rtn", "cranelift", "parallel frontend",
                   "semver", "mcdc", "unsafe fields", "arbitrary self types", "coerce pointee"]

    def priority_of(item):
        title = (item["authority"].get("title", "") + " " +
                 item["authority"].get("domain", "")).lower()
        if any(k in title for k in p0_keywords):
            return "P0 官方核心"
        if any(k in title for k in p1_keywords):
            return "P1 形式化/验证"
        if any(k in title for k in p2_keywords):
            return "P2 工业生态"
        if any(k in title for k in p3_keywords):
            return "P3 前沿探索"
        return "P3 前沿探索"

    gaps_by_priority = {}
    for item in only_in_authority:
        p = priority_of(item)
        gaps_by_priority.setdefault(p, []).append(item)

    today = datetime.now().strftime("%Y_%m_%d")
    report_file = REPORTS_DIR / f"TOPIC_ALIGNMENT_AND_GAP_PLAN_{today}.md"

    lines = []
    lines.append("# 主题-权威来源对齐与缺口行动计划\n\n")
    lines.append(f"**生成日期**：{datetime.now().strftime('%Y-%m-%d %H:%M')}\n\n")
    lines.append("## 执行摘要\n\n")
    lines.append("本报告基于 `scripts/topic_authority_aligner.py` 对项目当前 `concept/` 资产与四类权威来源的自动对齐结果：\n\n")
    lines.append(f"- 当前项目 `concept/` 主题数：**{stats.get('project_topics', 0)}**\n")
    lines.append(f"- 权威来源主题数：**{stats.get('authority_topics', 0)}**\n")
    lines.append(f"- 已对齐主题：**{stats.get('aligned', 0)}**（覆盖率 {stats.get('aligned', 0) / stats.get('authority_topics', 1) * 100:.1f}%）\n")
    lines.append(f"- 权威独有缺口：**{stats.get('only_in_authority', 0)}**\n")
    lines.append(f"- 项目独有主题：**{stats.get('only_in_project', 0)}**\n\n")

    lines.append("## 1. 对称差矩阵\n\n")
    lines.append("| 来源类别 | 权威主题数 | 已对齐 | 缺口 | 覆盖率 |\n")
    lines.append("|----------|-----------|--------|------|--------|\n")
    cat_stats = {}
    for item in aligned:
        cat = item["authority"].get("category", "unknown")
        cat_stats.setdefault(cat, {"aligned": 0, "gap": 0})
        cat_stats[cat]["aligned"] += 1
    for item in only_in_authority:
        cat = item["authority"].get("category", "unknown")
        cat_stats.setdefault(cat, {"aligned": 0, "gap": 0})
        cat_stats[cat]["gap"] += 1
    cat_labels = {
        "official_docs": "Rust 官方文档",
        "formal_verification": "形式化/验证生态",
        "industrial_ecosystem": "工业/应用生态",
        "roadmap": "项目路线图",
    }
    for cat in ["official_docs", "formal_verification", "industrial_ecosystem", "roadmap"]:
        if cat in cat_stats:
            s = cat_stats[cat]
            total = s["aligned"] + s["gap"]
            coverage = s["aligned"] / total * 100 if total else 0
            lines.append(f"| {cat_labels.get(cat, cat)} | {total} | {s['aligned']} | {s['gap']} | {coverage:.1f}% |\n")
    lines.append("\n")

    lines.append("## 2. Top-30 缺口任务清单\n\n")
    lines.append("> 每项任务包含：缺口标题、建议目录、依赖、验收标准。\n\n")
    lines.append("| 优先级 | 缺口主题 | 建议目录 | 依赖 | 验收标准 |\n")
    lines.append("|--------|----------|----------|------|----------|\n")

    task_id = 0
    for priority in ["P0 官方核心", "P1 形式化/验证", "P2 工业生态", "P3 前沿探索"]:
        gaps = gaps_by_priority.get(priority, [])
        for item in gaps[:30]:
            task_id += 1
            a = item["authority"]
            title = a["title"]
            domain = a.get("domain") or a.get("book") or ""
            # suggest target dir
            if "P0" in priority:
                target = "concept/01_foundation/ 或 concept/03_advanced/"
            elif "P1" in priority:
                target = "concept/04_formal/ 或 docs/12_research_notes/02_formal_methods/"
            elif "P2" in priority:
                target = "concept/06_ecosystem/ 或 crates/cXX_*/docs/"
            else:
                target = "concept/07_future/ 或 content/emerging/"
            deps = "权威来源链接"
            acceptance = f"完成 1 篇概念文档 + 1 个 crates/ 可运行示例（如适用）"
            lines.append(f"| {priority.split()[0]} | {title} | {target} | {deps} | {acceptance} |\n")
            if task_id >= 30:
                break
        if task_id >= 30:
            break
    lines.append("\n")

    lines.append("## 3. 重复/合并建议\n\n")
    duplicates = []
    titles_seen = {}
    for pt in project_topics:
        title_norm = pt["title"].lower().replace(" ", "_").replace("-", "_")
        if title_norm in titles_seen:
            duplicates.append((titles_seen[title_norm], pt))
        else:
            titles_seen[title_norm] = pt
    if duplicates:
        lines.append(f"检测到 {len(duplicates)} 对标题相似或重复的候选：\n\n")
        for a, b in duplicates[:10]:
            lines.append(f"- `{a['path']}` ↔ `{b['path']}` — {a['title']}\n")
        lines.append("\n建议：人工复核后合并或归档其中一篇，保留 canonical 路径。\n\n")
    else:
        lines.append("未检测到明显标题重复。\n\n")

    lines.append("## 4. 后续维护机制\n\n")
    lines.append("1. **月度更新**：运行 `python scripts/topic_authority_aligner.py --phase all`，刷新 `concept/00_meta/02_sources/04_topic_authority_alignment_map.md` 与本报告。\n")
    lines.append("2. **季度评审**：由内容负责人审核 P0/P1 缺口，决定是否纳入下一个 sprint。\n")
    lines.append("3. **新增文档规范**：每个新 `concept/` 文件需在 frontmatter 中标注 `authority_source` 与 `coverage_level`，便于自动对齐。\n")
    lines.append("4. **验证门禁**：合并前必须运行 `kb_auditor.py`、`detect_content_overlap.py`、`cargo check --workspace`。\n\n")

    lines.append("## 附录 A：权威来源列表\n\n")
    lines.append("### 官方文档\n")
    for key, (name, url) in OFFICIAL_BOOKS.items():
        lines.append(f"- [{name}]({url})\n")
    lines.append("\n### 形式化/验证生态\n")
    for t in FORMAL_VERIFICATION_TOPICS:
        lines.append(f"- [{t['title']}]({t['url']})\n")
    lines.append("\n### 工业/应用生态\n")
    for t in INDUSTRIAL_ECOSYSTEM_TOPICS:
        lines.append(f"- [{t['title']}]({t['url']}) — {t['domain']}\n")
    lines.append("\n### 项目路线图\n")
    for t in ROADMAP_TOPICS:
        lines.append(f"- [{t['title']}]({t['url']}) — {t['domain']}\n")
    lines.append("\n")

    lines.append("## 附录 B：项目索引资产\n\n")
    lines.append("- `concept/00_meta/02_sources/04_topic_authority_alignment_map.md`：当前项目主题树与权威来源对齐图谱。\n")
    lines.append("- `tmp/topic_inventory_current.json`：当前项目主题结构化数据。\n")
    lines.append("- `tmp/topic_inventory_authoritative.json`：权威来源主题结构化数据。\n")
    lines.append("- `tmp/topic_symmetric_diff.json`：完整对称差数据。\n")
    lines.append("- `tmp/topic_alignment_matrix.tsv`：对齐矩阵（可用于电子表格透视）。\n\n")

    report_file.write_text("".join(lines), encoding="utf-8", newline="\n")
    print(f"  已生成: {report_file}")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--phase", choices=["1", "2", "3", "4", "5", "all"], default="all")
    args = parser.parse_args()

    if args.phase == "1":
        phase1()
    elif args.phase == "2":
        phase2()
    elif args.phase == "3":
        phase3()
    elif args.phase == "4":
        phase4()
    elif args.phase == "5":
        phase5()
    elif args.phase == "all":
        phase1()
        phase2()
        phase3()
        phase4()
        phase5()
    else:
        print(f"Phase {args.phase} not implemented yet")
        sys.exit(1)


if __name__ == "__main__":
    main()
