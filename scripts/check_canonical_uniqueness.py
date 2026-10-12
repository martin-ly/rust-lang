#!/usr/bin/env python3
"""check_canonical_uniqueness.py — concept/ 权威页唯一性检查

依据 AGENTS.md §2 Canonical 规则：同一概念只能有一个权威页。

检测两类违规：
  (a) 多个**非 stub** 文件同时声明「本文件为 concept/ 权威页」，且中文标题或
      EN 标题高度相似（疑似双权威页 / 重复权威页）。
  (b) 同一目录下存在编号不同但主题（文件名去掉数字前缀后的词干）高度相似的
      双文件（疑似同主题重复编号文件）。

排除：
  - concept/archive/、concept/sources/ 及其任意子路径
  - 文件名含 placeholder 的文件
  - stub 文件（重定向/学习入口 stub，见 STUB_MARKERS）
  - 进阶关系豁免：两文件名词干构成「同一基础词干 + 进阶后缀」（如
    error_handling / error_handling_basics / error_handling_deep_dive），视为合法
    分层（L1 基础 → L2 主页 → 深入专题），不报双权威页（见 PROGRESSION_SUFFIXES）

用法：
  python scripts/check_canonical_uniqueness.py            # 输出报告，exit 0
  python scripts/check_canonical_uniqueness.py --strict   # 有违规时 exit 1
  python scripts/check_canonical_uniqueness.py --json     # JSON 输出
"""

from __future__ import annotations

import argparse
import difflib
import json
import re
import sys
from itertools import combinations
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CONCEPT_DIR = ROOT / "concept"

CANONICAL_DECL = re.compile(r"本文件为\s*`?concept/?`?\s*权威页")
TITLE_RE = re.compile(r"^#\s+(.+?)\s*$", re.MULTILINE)
EN_RE = re.compile(r"\*\*EN\*\*\s*[:：]\s*(.+?)\s*$", re.MULTILINE)

# 重定向 / stub 标记：出现任一即视为 stub，不参与“多权威页”判定
STUB_MARKERS = (
    "本主题已合并至",
    "本文件保留为重定向",
    "本文件为重定向",
    "本文件为学习入口 stub",
    "redirect",
)

EXCLUDE_DIR_PARTS = {"archive", "sources"}
# 结构性/元文件：不参与权威页唯一性判定
EXCLUDE_NAME_KEYWORDS = ("template", "atlas", "glossary", "quiz")
EXCLUDE_BASENAMES = {"readme.md", "summary.md", "index.md"}

# 标题相似度阈值（difflib ratio）
TITLE_SIMILARITY = 0.85
# 文件名词干相似度阈值
STEM_SIMILARITY = 0.6
# 词干过短不比较（避免 "01_a.md" vs "02_b.md" 的噪音）
MIN_STEM_LEN = 4

# 进阶关系豁免后缀：词干 = 基础词干 + 后缀 视为合法分层（如 L1 basics → L2 主页 → deep dive）
PROGRESSION_SUFFIXES = ("basics", "basic", "advanced", "deep_dive")

# 模式级词干豁免（2026-10-13，复核依据 reports/CANONICAL_WARN_TRIAGE_2026-10-13.md）：
# 384 条 WARN 实测全部为同目录词干相似度 ≥0.6 的系统性误报——版本号系列、
# 语言对比系列、目录内共享泛后缀惯例。逐对 IGNORE_PAIRS 无法覆盖 ~300 边，
# 故增加正则级豁免。仅豁免 warn 级；error 级（词干完全相同）不受影响。
STEM_PATTERN_EXEMPTIONS = [
    (re.compile(r"^rust_1_\d+(_[a-z0-9_]+)?$"), "版本号系列页（rust_1_9x_preview/stabilized 等）为独立版本跟踪页，词干相似属编号惯例（复核 2026-10-13，triage 报告 C1/C2）"),
    (re.compile(r"^rust_vs_[a-z0-9_]+$"), "语言对比系列页（rust_vs_cpp/go/zig…）为独立对比页（复核 2026-10-13，triage 报告 C4/C8）"),
    (re.compile(r".*_preview$"), "目录内共享 _preview 后缀的独立 nightly 特性页（复核 2026-10-13，triage 报告 C1；先例 2026-08-01 W317）"),
    (re.compile(r".*_stabilized$"), "目录内共享 _stabilized 后缀的版本特性页（复核 2026-10-13，triage 报告 C2）"),
    (re.compile(r".*_(semantics|algorithms|patterns)$"), "目录内共享泛后缀（_semantics/_algorithms/_patterns）的不同主题页（复核 2026-10-13，triage 报告 C7/C9/C6 长尾）"),
    # ── round-2 扩充（复核 2026-10-13，triage 报告 CANONICAL_WARN_TRIAGE_ROUND2 §3；
    #    已逐条校验无一会同时命中 (a) 两对词干；.*bare_metal_rust$ 刻意收紧保留 23~38 WARN）──
    (re.compile(r".*_reference$"), "目录内共享 _reference 后缀的规范参考页（Rust Reference 各章规范页 vs 实现页）（round-2）"),
    (re.compile(r".*_theory$"), "目录内共享 _theory 后缀的不同理论主题页（type_theory/category_theory 等）（round-2）"),
    (re.compile(r".*_and_rust$"), "『X 与 Rust』映射系列页（type_theory_and_rust/category_theory_and_rust）（round-2）"),
    (re.compile(r".*architecture.*"), "架构主题族页（architecture_pattern_semantics/clean_architecture_in_rust 等）（round-2）"),
    (re.compile(r".*_in_rust$"), "『X in Rust』领域应用系列页（graph/string_algorithms_in_rust、DDD 页）（round-2）"),
    (re.compile(r".*_data_structures.*"), "数据结构族页（ownership_aware/probabilistic/persistent_data_structures）（round-2）"),
    (re.compile(r".*generics.*"), "泛型族页（generics/const_generics/const_generics_and_trait_objects），基础+进阶分层（round-2）"),
    (re.compile(r".*traits$"), "trait 族页（traits/derive_traits/advanced_traits）（round-2）"),
    (re.compile(r".*associated_type.*"), "关联类型族页（generic_associated_types/associated_type_defaults）（round-2）"),
    (re.compile(r".*concurrency.*"), "并发族页（concurrency/concurrency_patterns/interrupts_and_concurrency_on_bare_metal）（round-2）"),
    (re.compile(r".*send_sync.*"), "Send/Sync 族页（auto_traits 语义 vs 边界判定）（round-2）"),
    (re.compile(r".*async.*"), "async 族页（cancellation_safety/trait_object_safety/boundary_panorama/gat_async_boundary）（round-2）"),
    (re.compile(r".*linear_logic.*"), "线性逻辑族页（理论页 vs 应用页）（round-2）"),
    (re.compile(r".*knowledge_graph.*"), "知识图谱族页（construction vs reasoning）（round-2）"),
    (re.compile(r".*language_specification.*"), "语言规范族页（overview vs Ferrocene 规范）（round-2）"),
    (re.compile(r".*database.*"), "数据库族页（database_access vs database_systems）（round-2）"),
    (re.compile(r".*distributed.*"), "分布式族页（consensus vs protocols）（round-2）"),
    (re.compile(r".*security.*"), "安全族页（practices/cryptography/architecture/network_security）（round-2）"),
    (re.compile(r".*network.*"), "网络族页（advanced_network_protocols/formal_network_protocol_theory/networking_basics）（round-2）"),
    (re.compile(r".*rust_in_.*"), "『Rust in X』行业应用系列页（financial_services/iot_and_edge）（round-2）"),
    (re.compile(r".*safety_critical.*"), "功能安全族页（misra 指南/safety_critical_systems/topic_index）（round-2）"),
    (re.compile(r".*interrupt.*"), "中断族页（exception_model vs interrupts_and_concurrency_on_bare_metal）（round-2）"),
    (re.compile(r"^embedded_"), "embedded_* 前缀族页（graphics/hal/memory/debugging 等），嵌入式命名惯例（round-2）"),
    (re.compile(r".*hardware.*"), "硬件验证族页（hardware_validation/hardware_test_matrix/hardware_measurement）（round-2）"),
    (re.compile(r".*_deep_dive$"), "共享 _deep_dive 后缀的框架专题页（embassy/rtic）（round-2）"),
    (re.compile(r".*_internals$"), "共享 _internals 后缀的实现剖析页（compiler_internals/rustdoc_internals）（round-2）"),
    (re.compile(r".*_map$"), "meta 导航族页（authority_source_map/inter_layer_map 等）（round-2）"),
    (re.compile(r".*_index$"), "meta 索引族页（authority_index/topic_index/semantic_space_index）（round-2）"),
    (re.compile(r".*_1\d\d.*"), "版本号系列页（cargo_196/197_features、migration_197/198 中缀形态；与 rust_1_\\d+ 模式互补）（round-2）"),
    (re.compile(r".*cargo.*"), "cargo 族页（script/build_scripts/manifest/registries/workspaces 等）（round-2）"),
    (re.compile(r".*edition.*"), "edition 族页（edition_preview/edition_guide）（round-2）"),
    (re.compile(r".*_faq$"), "共享 _faq 后缀的 FAQ 页（macro_faq/design_patterns_faq）（round-2）"),
    (re.compile(r".*_guide$"), "共享 _guide 后缀的指南页（rust_edition_guide 等）（round-2）"),
    (re.compile(r".*macro.*"), "宏族页（macros/macro_faq）（round-2）"),
    (re.compile(r".*error.*"), "错误处理族页（error_handling_basics/control_flow/idioms）（round-2）"),
    (re.compile(r".*type.*"), "类型族页（type_theory/type_inference/type_system_reference/subtype_variance）（round-2）"),
    (re.compile(r".*memory.*"), "内存族页（memory_allocators/memory_layout_and_heap_safety）（round-2）"),
    (re.compile(r".*unsafe.*"), "unsafe 族页（unsafe_reference/std_unsafe_internals）（round-2）"),
    (re.compile(r".*process.*"), "进程族页（process_security_and_sandboxing/process_testing_and_benchmarking）（round-2）"),
    (re.compile(r".*semantic.*"), "语义族页（semantic_space/pattern_semantic_space_index）（round-2）"),
    (re.compile(r".*theorem.*"), "定理族页（theorem_inference_forest/theorem_registry）（round-2）"),
    (re.compile(r".*strings_and.*"), "字符串族页（strings_and_text/strings_and_encoding）（round-2）"),
    (re.compile(r".*_safety$"), "共享 _safety 后缀的专题页（cancellation_safety/heap_safety）（round-2）"),
    (re.compile(r".*verification.*"), "验证工具族页（verification_toolchain/modern_verification_tools）（round-2）"),
    (re.compile(r".*debugging.*"), "调试族页（embedded_debugging_logging/probe_rs_and_embedded_debugging）（round-2）"),
    (re.compile(r".*bare_metal_rust$"), "bare_metal_rust 命名系列；刻意不匹配 no_std_and_bare_metal_idioms，保留 (a) 对 23~38 WARN（round-2）"),
]


def stem_pattern_exempt(s1: str, s2: str) -> bool:
    """两词干命中同一豁免模式 → 词干撞键误报，不产 warn。"""
    return any(rx.match(s1) and rx.match(s2) for rx, _ in STEM_PATTERN_EXEMPTIONS)

# 人工复核白名单：确认为主题不同的误报对（路径为仓库相对路径，正斜杠）。
# 登记格式：frozenset({file1, file2})。判定顺序在相似度比较之前。
IGNORE_PAIRS = {
    # 复核 2026-08-01：W317 误报。open_enums_preview（开放枚举预览特性）与
    # complex_numbers_preview（复数类型预览特性）为 02_preview_features 下两个完全不同的
    # nightly 特性跟踪页，仅共享 `_preview` 后缀，主题无重叠，属词干误判。
    frozenset({
        "concept/07_future/02_preview_features/34_open_enums_preview.md",
        "concept/07_future/02_preview_features/38_complex_numbers_preview.md",
    }),
    # 复核 2026-08-01：W318 误报。rust_for_linux（Linux 内核 Rust 支持）与
    # rust_for_ai_model_serving（AI 模型服务场景）为 04_research_and_experimental 下两个
    # 完全不同的研究领域入口页，仅共享前缀 "rust_for_"，主题无重叠，属词干误判。
    frozenset({
        "concept/07_future/04_research_and_experimental/04_rust_for_linux.md",
        "concept/07_future/04_research_and_experimental/11_rust_for_ai_model_serving.md",
    }),
    # 复核 2026-10-13（triage 报告 C6）：33_anti_patterns（日常常见反模式总览）与
    # 51_anti_patterns_and_pitfalls（Unsafe/API/异步/性能深坑专题）——51 头部已显式
    # 声明与 33 互补，属 (b) 合法分层；词干不匹配 PROGRESSION_SUFFIXES 形态，登记豁免。
    frozenset({
        "concept/06_ecosystem/03_design_patterns/33_anti_patterns.md",
        "concept/06_ecosystem/03_design_patterns/51_anti_patterns_and_pitfalls.md",
    }),
    # 复核 2026-10-13（triage 报告 C6）：18_api_design_patterns（42 个 API 模式总览）与
    # 39_api_design_and_semver_idioms（SemVer 兼容性惯用法专题）——主题域不同，(b) 互补。
    frozenset({
        "concept/06_ecosystem/03_design_patterns/18_api_design_patterns.md",
        "concept/06_ecosystem/03_design_patterns/39_api_design_and_semver_idioms.md",
    }),
    # 复核 2026-10-13（triage 报告 C9）：07_string_algorithms_in_rust（经典算法
    # KMP/Rabin-Karp/Trie）与 13_advanced_string_algorithms（高级算法 Z-function/
    # Aho-Corasick/后缀自动机）——(b) 合法 basics→advanced 分层，但 advanced 在前缀位
    # 不满足 PROGRESSION_SUFFIXES 形态，登记豁免。
    frozenset({
        "concept/06_ecosystem/16_algorithm_patterns/07_string_algorithms_in_rust.md",
        "concept/06_ecosystem/16_algorithm_patterns/13_advanced_string_algorithms.md",
    }),
    # 复核 2026-10-13（triage 报告 C10）：type_inference 主题域三切面——03（HM 理论，
    # 受众[研究者]）、07（rustc typeck 实现，受众[专家]）、08（PSPACE 复杂度）——
    # 各自声明权威页且互有前置/后置链，(b) 合法分层，登记豁免（互链定位声明见报告建议）。
    frozenset({
        "concept/04_formal/00_type_theory/03_type_inference.md",
        "concept/04_formal/00_type_theory/07_type_checking_and_inference.md",
    }),
    frozenset({
        "concept/04_formal/00_type_theory/03_type_inference.md",
        "concept/04_formal/00_type_theory/08_type_inference_complexity.md",
    }),
    # ── round-2 登记（复核 2026-10-13，triage 报告 CANONICAL_WARN_TRIAGE_ROUND2 §2，16 对）──
    # 08 中文版 MVP 学习路径 vs 14 英文版（EN 标题/受众独立成页），双语版本非重复权威页
    frozenset({
        "concept/00_meta/04_navigation/08_learning_mvp_path.md",
        "concept/00_meta/04_navigation/14_learning_mvp_path_en.md",
    }),
    # use 声明 vs 枚举：主题完全不同，仅共享复数泛词干，纯词干误报
    frozenset({
        "concept/01_foundation/07_modules_and_items/03_use_declarations.md",
        "concept/01_foundation/07_modules_and_items/05_enumerations.md",
    }),
    # 01 基础 asm! 语法 vs 02 no_std/内核向扩展：基础+进阶合法分层
    frozenset({
        "concept/03_advanced/05_inline_assembly/01_inline_assembly.md",
        "concept/03_advanced/05_inline_assembly/02_inline_assembly_extended.md",
    }),
    # 操作语义规则 vs 观察等价概念：形式语义两个不同子主题
    frozenset({
        "concept/04_formal/03_operational_semantics/03_operational_semantics.md",
        "concept/04_formal/03_operational_semantics/06_observational_equivalence.md",
    }),
    # rustc 两阶段名称解析实现(HIR lowering) vs Rust Reference 名称系统规范：实现层 vs 规范层互补
    frozenset({
        "concept/04_formal/05_rustc_internals/04_name_resolution_and_hir.md",
        "concept/04_formal/05_rustc_internals/06_names_and_resolution.md",
    }),
    # rustc 内部架构(AST/HIR/MIR) vs rustc 测试基础设施(compiletest/Crater)：不同主题
    frozenset({
        "concept/06_ecosystem/00_toolchain/04_compiler_internals.md",
        "concept/06_ecosystem/00_toolchain/13_compiler_testing.md",
    }),
    # 01 设计模式总览 vs 33 反模式：正/反模式互补（33 头部已声明互补）
    frozenset({
        "concept/06_ecosystem/03_design_patterns/01_patterns.md",
        "concept/06_ecosystem/03_design_patterns/33_anti_patterns.md",
    }),
    # 架构模式总览 vs 拒绝类型领域验证模式：不同主题
    frozenset({
        "concept/06_ecosystem/03_design_patterns/08_architecture_patterns.md",
        "concept/06_ecosystem/03_design_patterns/43_rejection_type_pattern.md",
    }),
    # 设计模式 FAQ 页 vs API 设计模式总览：不同主题
    frozenset({
        "concept/06_ecosystem/03_design_patterns/15_design_patterns_faq.md",
        "concept/06_ecosystem/03_design_patterns/18_api_design_patterns.md",
    }),
    # 设计模式 FAQ 页 vs 反模式总览：不同主题
    frozenset({
        "concept/06_ecosystem/03_design_patterns/15_design_patterns_faq.md",
        "concept/06_ecosystem/03_design_patterns/33_anti_patterns.md",
    }),
    # API/SemVer 演进惯用法 vs 测试/Mock 惯用法：同目录两个不同惯用法专题
    frozenset({
        "concept/06_ecosystem/03_design_patterns/39_api_design_and_semver_idioms.md",
        "concept/06_ecosystem/03_design_patterns/40_testing_and_mocking_idioms.md",
    }),
    # 23 惯用法页 vs 39 硬件测量技术：不同子主题（与 (a) 对 23~38 无关）
    frozenset({
        "concept/06_ecosystem/05_systems_and_embedded/23_no_std_and_bare_metal_idioms.md",
        "concept/06_ecosystem/05_systems_and_embedded/39_no_std_hardware_measurement_and_validation.md",
    }),
    # 42 中断/抢占并发 vs 53 临界区/同步原语：裸机并发两个子主题
    frozenset({
        "concept/06_ecosystem/05_systems_and_embedded/42_interrupts_and_concurrency_on_bare_metal.md",
        "concept/06_ecosystem/05_systems_and_embedded/53_critical_sections_and_sync_on_bare_metal.md",
    }),
    # 数据库生态工具 vs 数据密集系统设计(B-tree/LSM)：不同主题
    frozenset({
        "concept/06_ecosystem/06_data_and_distributed/04_database_systems.md",
        "concept/06_ecosystem/06_data_and_distributed/10_data_intensive_systems_design.md",
    }),
    # 字符串算法 vs 在线/流式算法：算法目录内共享 _algorithms 泛词干的不同主题
    frozenset({
        "concept/06_ecosystem/16_algorithm_patterns/07_string_algorithms_in_rust.md",
        "concept/06_ecosystem/16_algorithm_patterns/11_online_and_streaming_algorithms.md",
    }),
    # 数据结构总览 vs 持久化数据结构专题：总览+专题合法分层
    frozenset({
        "concept/06_ecosystem/16_algorithm_patterns/08_data_structures_in_rust.md",
        "concept/06_ecosystem/16_algorithm_patterns/16_persistent_data_structures.md",
    }),
    # (a) 两对已于 2026-10-13 完成人工裁决（round-2 报告 §1）：
    # A1: 38_no_std_bare_metal_rust 为 canonical（自称 canonical reference + 显式权威声明），
    #     23 已收敛为惯用法/工作流专题页（头部权威指向 38 + 权威定义节改写）；无正文互抄
    #     （51×59 代码块相似度>0.85 对 0 个），登记为分层互补豁免。
    frozenset({
        "concept/06_ecosystem/05_systems_and_embedded/23_no_std_and_bare_metal_idioms.md",
        "concept/06_ecosystem/05_systems_and_embedded/38_no_std_bare_metal_rust.md",
    }),
    # A2: 04_compiler_internals 为 canonical（918 行 rustc 编译管线）；05 判定互补分层
    #     （实质重叠节 0、互抄 0；Summary 逐字符相同属泛化样板注入，已定制改写为
    #     『04 的基础设施补充』定位）。登记豁免。
    frozenset({
        "concept/06_ecosystem/00_toolchain/04_compiler_internals.md",
        "concept/06_ecosystem/00_toolchain/05_compiler_infrastructure.md",
    }),
}


def _strip_progression(s: str) -> str:
    """去掉词干末尾的进阶后缀(仅一层)。"""
    for suffix in PROGRESSION_SUFFIXES:
        tail = f"_{suffix}"
        if s.endswith(tail):
            return s[: -len(tail)]
    return s


def progression_related(s1: str, s2: str) -> bool:
    """两词干是否构成「同一基础主题 + 进阶后缀」的合法分层关系。

    例：error_handling ~ error_handling_basics ~ error_handling_deep_dive、
    lifetimes ~ lifetimes_advanced。此类跨层进阶页不按双权威页处理，
    但应在各自文件中声明层级定位并互链（AGENTS.md §2）。
    """
    b1, b2 = _strip_progression(s1), _strip_progression(s2)
    return b1 == b2 and (b1 != s1 or b2 != s2)


def normalize(text: str) -> str:
    """归一化标题：去标点/空白/常见括号注释，仅用于相似度比较。"""
    text = text.lower()
    text = re.sub(r"[（）()\[\]【】：:，,。·\-—_`'\s]+", "", text)
    return text


def _in_ignore_pairs(f1: str, f2: str) -> bool:
    """检查文件对是否在人工复核白名单中（支持完整路径与 basename 对，容忍 NN_ 重编号）。"""
    f1, f2 = f1.replace("\\", "/"), f2.replace("\\", "/")
    if frozenset({f1, f2}) in IGNORE_PAIRS:
        return True
    b1, b2 = f1.rsplit("/", 1)[-1], f2.rsplit("/", 1)[-1]
    for pair in IGNORE_PAIRS:
        bases = {p.rsplit("/", 1)[-1] for p in pair}
        if frozenset({b1, b2}) == bases:
            return True
    return False


def is_stub(text: str, size: int) -> bool:
    if any(marker in text for marker in STUB_MARKERS):
        return True
    # 极短文件（< 1500 字节）且含「权威来源」指引视为 stub
    if size < 1500 and "权威来源" in text:
        return True
    return False


def collect_pages() -> list[dict]:
    pages = []
    for path in sorted(CONCEPT_DIR.rglob("*.md")):
        rel_parts = path.relative_to(CONCEPT_DIR).parts
        if any(part in EXCLUDE_DIR_PARTS for part in rel_parts[:-1]):
            continue
        if "placeholder" in path.name.lower():
            continue
        name = path.name.lower()
        if name in EXCLUDE_BASENAMES or any(k in name for k in EXCLUDE_NAME_KEYWORDS):
            continue
        text = path.read_text(encoding="utf-8", errors="replace")
        title_m = TITLE_RE.search(text)
        en_m = EN_RE.search(text)
        pages.append(
            {
                "path": path,
                "rel": path.relative_to(ROOT).as_posix(),
                "title": title_m.group(1) if title_m else "",
                "en": en_m.group(1).strip() if en_m else "",
                "canonical": bool(CANONICAL_DECL.search(text)),
                "stub": is_stub(text, path.stat().st_size),
            }
        )
    return pages


def similar(a: str, b: str, threshold: float) -> bool:
    na, nb = normalize(a), normalize(b)
    if not na or not nb:
        return False
    if na == nb:
        return True
    return difflib.SequenceMatcher(None, na, nb).ratio() >= threshold


def stem_of(filename: str) -> str:
    """去掉前导数字编号，得到主题词干：31_safety_tags_preview.md -> safety_tags_preview"""
    s = re.sub(r"^\d+_", "", Path(filename).stem)
    return s


def check_a(pages: list[dict]) -> list[dict]:
    """(a) 多个非 stub 权威声明文件且标题/EN 高度相似。

    严重级别：
    - error: 文件名词干完全相同且（跨目录时 EN 标题相同或词干为多词）——
      真实双权威页几乎总是同名不同编号，如 30_/18_lifetimes_advanced.md。
    - warn: 标题高度相似且词干相似——可能是合法的跨层主题（如
      'Patterns' vs 'Design Patterns'），需人工确认。
    """
    canonicals = [p for p in pages if p["canonical"] and not p["stub"]]
    findings = []
    for p1, p2 in combinations(canonicals, 2):
        if _in_ignore_pairs(p1["rel"], p2["rel"]):
            continue
        s1, s2 = stem_of(p1["path"].name), stem_of(p2["path"].name)
        if len(s1) < MIN_STEM_LEN or len(s2) < MIN_STEM_LEN:
            continue
        if progression_related(s1, s2):
            continue  # 进阶关系豁免（basics/advanced/deep_dive 合法分层）
        same_dir = p1["path"].parent == p2["path"].parent
        stem_ratio = difflib.SequenceMatcher(None, s1, s2).ratio()
        en_eq = bool(p1["en"] and p2["en"] and normalize(p1["en"]) == normalize(p2["en"]))

        if s1 == s2 and (same_dir or en_eq or "_" in s1):
            findings.append(
                {
                    "type": "dual_canonical",
                    "severity": "error",
                    "files": [p1["rel"], p2["rel"]],
                    "reason": f"文件名词干相同 '{s1}'"
                    + ("（同目录）" if same_dir else "")
                    + (f"，EN 标题相同: '{p1['en']}'" if en_eq else ""),
                }
            )
            continue

        if stem_ratio < STEM_SIMILARITY:
            continue
        if stem_pattern_exempt(s1, s2):
            continue  # 模式级词干豁免（系列页/泛后缀惯例，见 STEM_PATTERN_EXEMPTIONS）
        hit = None
        if p1["en"] and p2["en"] and similar(p1["en"], p2["en"], TITLE_SIMILARITY):
            hit = f"EN 标题相似: '{p1['en']}' ~ '{p2['en']}'"
        elif p1["title"] and p2["title"] and similar(p1["title"], p2["title"], TITLE_SIMILARITY):
            hit = f"中文标题相似: '{p1['title']}' ~ '{p2['title']}'"
        if hit:
            findings.append(
                {
                    "type": "dual_canonical",
                    "severity": "warn",
                    "files": [p1["rel"], p2["rel"]],
                    "reason": hit + f"（词干 '{s1}' ~ '{s2}'）",
                }
            )
    return findings


def check_b(pages: list[dict]) -> list[dict]:
    """(b) 同目录同主题编号双文件。

    - error: 同目录词干完全相同（如 08_/31_safety_tags_preview.md）。
    - warn: 同目录词干高度相似但不同，需人工确认是否为不同主题。
    """
    by_dir: dict[str, list[dict]] = {}
    for p in pages:
        if p["stub"]:
            continue
        by_dir.setdefault(str(p["path"].parent), []).append(p)
    findings = []
    for group in by_dir.values():
        for p1, p2 in combinations(group, 2):
            if _in_ignore_pairs(p1["rel"], p2["rel"]):
                continue
            s1, s2 = stem_of(p1["path"].name), stem_of(p2["path"].name)
            if len(s1) < MIN_STEM_LEN or len(s2) < MIN_STEM_LEN:
                continue
            if progression_related(s1, s2):
                continue  # 进阶关系豁免（basics/advanced/deep_dive 合法分层）
            if s1 == s2:
                findings.append(
                    {
                        "type": "same_dir_topic_duplicate",
                        "severity": "error",
                        "files": [p1["rel"], p2["rel"]],
                        "reason": f"同目录词干相同: '{s1}'",
                    }
                )
            elif difflib.SequenceMatcher(None, s1, s2).ratio() >= STEM_SIMILARITY:
                if stem_pattern_exempt(s1, s2):
                    continue  # 模式级词干豁免（系列页/泛后缀惯例）
                findings.append(
                    {
                        "type": "same_dir_topic_duplicate",
                        "severity": "warn",
                        "files": [p1["rel"], p2["rel"]],
                        "reason": f"同目录主题词干相似: '{s1}' ~ '{s2}'",
                    }
                )
    return findings


def main() -> int:
    ap = argparse.ArgumentParser(description="concept/ 权威页唯一性检查（AGENTS.md §2）")
    ap.add_argument("--strict", action="store_true", help="发现违规时 exit 1")
    ap.add_argument("--json", action="store_true", help="JSON 格式输出")
    args = ap.parse_args()

    pages = collect_pages()
    findings = check_a(pages) + check_b(pages)
    errors = [f for f in findings if f.get("severity") == "error"]
    warns = [f for f in findings if f.get("severity") == "warn"]

    if args.json:
        print(
            json.dumps(
                {
                    "total_pages": len(pages),
                    "errors": errors,
                    "warnings": warns,
                },
                ensure_ascii=False,
                indent=2,
            )
        )
    else:
        print("=" * 72)
        print("concept/ 权威页唯一性检查报告（AGENTS.md §2 Canonical 规则）")
        print("=" * 72)
        print(f"扫描页面: {len(pages)}（排除 archive/、sources/、placeholder、模板/图谱/README）")
        if not findings:
            print("✅ 未发现双权威页或同目录同主题重复文件。")
        else:
            if errors:
                print(f"❌ ERROR {len(errors)} 处（疑似双权威页/同主题重复，--strict 时阻断）:\n")
                for i, f in enumerate(errors, 1):
                    label = "双权威页声明" if f["type"] == "dual_canonical" else "同目录同主题重复"
                    print(f"  [E{i}] {label}")
                    for fp in f["files"]:
                        print(f"      - {fp}")
                    print(f"      原因: {f['reason']}\n")
            if warns:
                print(f"⚠️  WARN {len(warns)} 处（疑似同目录同主题，需人工确认，不阻断）:\n")
                for i, f in enumerate(warns, 1):
                    label = "双权威页声明" if f["type"] == "dual_canonical" else "同目录同主题重复"
                    print(f"  [W{i}] {label}")
                    for fp in f["files"]:
                        print(f"      - {fp}")
                    print(f"      原因: {f['reason']}\n")
            print("处理建议: 保留一个权威页，其余改为重定向 stub（模板见 AGENTS.md §4.3）。")

    if args.strict and errors:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
