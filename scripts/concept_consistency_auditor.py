#!/usr/bin/env python3
"""concept_consistency_auditor.py — 概念一致性审计器 (Concept Consistency Auditor)

功能:
1. 扫描 concept/ 目录下的所有核心 .md 文件
2. 提取关键概念定义:Send/Sync、所有权、借用、生命周期、内部可变性、
   Pin/Unpin、协变/逆变/不变(变型)、unsafe,以及 Rust 1.97 关键边界术语
   (async fn/Future、unsafe superpowers、Pin 投影、生命周期子类型、
   Send/Sync 边界、let chains、unsafe extern blocks、const trait impl/effects、
   RPITIT/RTN/TAIT、GAT+async、allocator_api、match ergonomics、临时作用域等)
3. 检测同一概念在不同文件中的定义是否矛盾(极性冲突检测)
4. 校验各概念的权威页(canonical page)是否存在且包含核心定义
5. 检测跨文件引用的段落编号是否准确
6. 生成审计报告到 reports/CONCEPT_CONSISTENCY_AUDIT_<YYYY_MM_DD>.md

权威页基线(按 AGENTS.md §2 Canonical 规则):
  - Send/Sync        : concept/03_advanced/00_concurrency/02_send_sync_auto_traits.md
  - 所有权           : concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md
  - 借用             : concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md
  - 生命周期         : concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md
  - 内部可变性       : concept/02_intermediate/02_memory_management/02_interior_mutability.md
  - Pin/Unpin        : concept/03_advanced/01_async/08_pin_unpin.md
  - 变型(协变逆变)   : concept/04_formal/00_type_theory/02_subtype_variance.md
  - unsafe           : concept/03_advanced/02_unsafe/01_unsafe.md
  - async fn/Future  : concept/03_advanced/01_async/01_async.md
  - unsafe superpowers & unsafe_op_in_unsafe_fn
                   : concept/03_advanced/02_unsafe/01_unsafe.md
  - Pin 投影         : concept/03_advanced/01_async/08_pin_unpin.md
  - 生命周期子类型   : concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md
  - Send/Sync 边界   : concept/03_advanced/00_concurrency/04_send_sync_boundaries.md
  - let chains       : concept/01_foundation/04_control_flow/03_let_chains.md
  - unsafe extern blocks
                   : concept/03_advanced/04_ffi/05_unsafe_extern_blocks.md
  - const trait impl : concept/07_future/02_preview_features/06_const_trait_impl_preview.md
  - effects system   : concept/07_future/02_preview_features/01_effects_system.md
  - RPITIT/RTN/TAIT  : concept/07_future/02_preview_features/15_rpitit_preview.md
  - GAT + async      : concept/03_advanced/01_async/14_gat_async_boundary.md
  - allocator_api    : concept/03_advanced/06_low_level_patterns/01_custom_allocators.md
  - match ergonomics : concept/01_foundation/04_control_flow/02_patterns.md
  - 临时作用域/tail drop
                   : concept/04_formal/05_rustc_internals/09_destructors.md

用法:
    python scripts/concept_consistency_auditor.py            # 观察模式, 报告 + exit 0
    python scripts/concept_consistency_auditor.py --strict   # 有错误级发现时 exit 1
    python scripts/concept_consistency_auditor.py --json     # JSON 摘要输出
"""

from __future__ import annotations

import argparse
import datetime
import json
import os
import re
import sys
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Optional

# 配置
ROOT = Path(__file__).resolve().parent.parent
CONCEPT_DIR = ROOT / "concept"
REPORT_DATE = datetime.datetime.now().strftime("%Y_%m_%d")
REPORT_PATH = ROOT / "reports" / f"CONCEPT_CONSISTENCY_AUDIT_{REPORT_DATE}.md"

# 非核心文件排除列表(与 kb_auditor.py 保持一致)
EXCLUDE_FILES = {
    "00.md", "01.md", "02.md", "03.md", "04.md", "05.md", "06.md", "07.md",
    "README.md", "PLAN.md", "PLAN_Semantic_Space_Wave.md",
    "LSIP_Unified_Model_Panorama.md", "PostgreSQL_LSIP_Unified_Model.md",
}
EXCLUDE_PREFIXES = ("sandbox",)

# 概念 -> 权威页(相对 concept/ 的路径基线)
CANONICAL_PAGES: dict[str, str] = {
    "Send/Sync": "03_advanced/00_concurrency/02_send_sync_auto_traits.md",
    "所有权": "01_foundation/01_ownership_borrow_lifetime/01_ownership.md",
    "借用": "01_foundation/01_ownership_borrow_lifetime/02_borrowing.md",
    "生命周期": "01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md",
    "内部可变性": "02_intermediate/02_memory_management/02_interior_mutability.md",
    "Pin/Unpin": "03_advanced/01_async/08_pin_unpin.md",
    "变型": "04_formal/00_type_theory/02_subtype_variance.md",
    "unsafe": "03_advanced/02_unsafe/01_unsafe.md",
    # 扩展概念集(Rust 1.97 关键边界术语)
    "async fn/Future": "03_advanced/01_async/01_async.md",
    "unsafe superpowers": "03_advanced/02_unsafe/01_unsafe.md",
    "Pin 投影": "03_advanced/01_async/08_pin_unpin.md",
    "生命周期子类型": "01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md",
    "Send/Sync 边界": "03_advanced/00_concurrency/04_send_sync_boundaries.md",
    "let chains": "01_foundation/04_control_flow/03_let_chains.md",
    "unsafe extern blocks": "03_advanced/04_ffi/05_unsafe_extern_blocks.md",
    "const trait impl": "07_future/02_preview_features/06_const_trait_impl_preview.md",
    "effects system": "07_future/02_preview_features/01_effects_system.md",
    "RPITIT/RTN/TAIT": "07_future/02_preview_features/15_rpitit_preview.md",
    "GAT + async": "03_advanced/01_async/14_gat_async_boundary.md",
    "allocator_api": "03_advanced/06_low_level_patterns/01_custom_allocators.md",
    "match ergonomics": "01_foundation/04_control_flow/02_patterns.md",
    "临时作用域/tail drop": "04_formal/05_rustc_internals/09_destructors.md",
}

# 扩展概念元数据:名称(中/英)、提取正则、极性断言、允许变型
# 用于描述性文档与保守的极性漂移监控;未列出的概念沿用既有硬编码规则。
EXTENDED_CONCEPT_PROFILES: dict[str, dict] = {
    "async fn/Future": {
        "name_en": "async fn / Future equivalence",
        "canonical": "03_advanced/01_async/01_async.md",
        "extract": [
            ("async-Future-状态机", r"async fn.*状态机|async fn.*desugar.*Future|async/await.*语法糖.*Future|Future.*状态机.*async|async fn.*等价.*返回.*Future"),
            ("async-Future-等价", r"async fn.*等价|async fn.*≡|async fn.*返回.*impl Future|async fn.*本质上.*Future"),
        ],
        "polarity_pos": r"async fn.*(等价|desugar|状态机|返回.*Future)",
        "polarity_neg": r"async fn.*不.*返回.*Future|async fn.*不等价",
        "allowed_variances": [],
    },
    "unsafe superpowers": {
        "name_en": "unsafe five superpowers & unsafe_op_in_unsafe_fn",
        "canonical": "03_advanced/02_unsafe/01_unsafe.md",
        "extract": [
            ("unsafe-superpowers-五种能力", r"five unsafe superpowers|five superpowers|unsafe.*superpowers|五种.*superpower|五种 unsafe 能力|unsafe.*五种能力"),
            ("unsafe-superpowers-unsafe_op", r"unsafe_op_in_unsafe_fn|unsafe fn.*显式.*unsafe.*块|unsafe fn.*内部.*unsafe.*块"),
        ],
        "polarity_pos": r"unsafe_op_in_unsafe_fn.*(默认|deny|warn|需.*显式)",
        "polarity_neg": r"unsafe fn.*内.*不需要.*unsafe.*块|unsafe_op_in_unsafe_fn.*关闭",
        "allowed_variances": [],
    },
    "Pin 投影": {
        "name_en": "Pin structural projection",
        "canonical": "03_advanced/01_async/08_pin_unpin.md",
        "extract": [
            ("Pin-投影-结构", r"结构投射|structural projection|Pin.*投影|pin-project|字段投影|Pin<&mut Self>.*字段"),
            ("Pin-投影-安全", r"Pin.*投影.*安全|投影.*保持.*地址|投影.*Unpin.*字段|unsafe.*投影.*UB"),
        ],
        "polarity_pos": r"结构投射.*安全|pin-project.*正确|投影.*保持.*不动",
        "polarity_neg": r"手写.*投影.*UB|移动被 pin.*字段|投影.*破坏.*不动",
        "allowed_variances": [],
    },
    "生命周期子类型": {
        "name_en": "lifetime subtyping ('static <: 'a)",
        "canonical": "01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md",
        "extract": [
            ("生命周期-子类型-static", r"'static.*<:|'static.*子类型|子类型.*'static|lifetime.*subtyp|'static.*outlives"),
            ("生命周期-子类型-outlives", r"'a: 'b|outlives|存活.*不短于|生命周期.*偏序|'a.*outlives.*'b"),
        ],
        "polarity_pos": r"'static.*(<:|outlives|子类型)|'a: 'b",
        "polarity_neg": r"'static.*不.*outlives|生命周期.*不.*子类型",
        "allowed_variances": ["covariant"],
    },
    "Send/Sync 边界": {
        "name_en": "Send/Sync necessary/sufficient conditions in trait objects & bounds",
        "canonical": "03_advanced/00_concurrency/04_send_sync_boundaries.md",
        "extract": [
            ("Send/Sync边界-充分必要", r"充分必要|dyn Trait \+ Send \+ Sync|T: Send\s*⇔|T: Sync\s*⇔|Arc<dyn.*Send.*Sync>"),
            ("Send/Sync边界-trait对象", r"dyn Trait.*Send|trait object.*Send|自动实现.*Send/Sync|手动.*unsafe impl.*Send"),
        ],
        "polarity_pos": r"T: Send\s*⇔|T: Sync\s*⇔|dyn Trait \+ Send \+ Sync",
        "polarity_neg": r"dyn Trait.*自动.*Send|Send.*不需要.*Sync",
        "allowed_variances": [],
    },
    "let chains": {
        "name_en": "let chains / if-let guards",
        "canonical": "01_foundation/04_control_flow/03_let_chains.md",
        "extract": [
            ("let-chains-链式", r"let chains|链式 let|if let.*&&.*let|let 链"),
            ("let-chains-守卫", r"if-let guards|let 守卫|if let.*守卫|match.*if let"),
        ],
        "polarity_pos": r"let chains|if-let guards",
        "polarity_neg": r"let chains.*允许.*\|\||if-let guards.*不允许",
        "allowed_variances": [],
    },
    "unsafe extern blocks": {
        "name_en": "unsafe extern blocks",
        "canonical": "03_advanced/04_ffi/05_unsafe_extern_blocks.md",
        "extract": [
            ("unsafe-extern-块", r"unsafe extern blocks|unsafe extern \"C\"|extern.*块.*unsafe|unsafe extern \""),
            ("unsafe-extern-safe", r"safe fn.*extern|extern.*safe.*审计|safe FFI|unsafe extern.*safe"),
        ],
        "polarity_pos": r"unsafe extern.*块|extern.*必须.*unsafe|safe fn.*extern",
        "polarity_neg": r"extern \"C\" \{.*\}.*safe|unsafe extern.*不需要",
        "allowed_variances": [],
    },
    "const trait impl": {
        "name_en": "const trait impl / ~const",
        "canonical": "07_future/02_preview_features/06_const_trait_impl_preview.md",
        "extract": [
            ("const-trait-impl-定义", r"const trait impl|const impl Trait|~const|常量上下文.*Trait|const fn.*trait"),
            ("const-trait-impl-效果", r"const.*效果|const.*effect|效果系统.*const|constness.*effect"),
        ],
        "polarity_pos": r"const impl Trait|const trait impl|~const",
        "polarity_neg": r"const trait.*不稳定.*不可用|~const.*废弃",
        "allowed_variances": [],
    },
    "effects system": {
        "name_en": "effect system",
        "canonical": "07_future/02_preview_features/01_effects_system.md",
        "extract": [
            ("effects-system-定义", r"effect system|效果系统|代数效应|generic over effects|效果多态"),
            ("effects-system-现有", r"async.*效果|const.*效果|try.*效果|unsafe.*效果|效果.*关键字"),
        ],
        "polarity_pos": r"effect system|效果系统|代数效应",
        "polarity_neg": r"Rust.*没有.*effect system|效果系统.*不现实",
        "allowed_variances": [],
    },
    "RPITIT/RTN/TAIT": {
        "name_en": "RPITIT / RTN / TAIT",
        "canonical": "07_future/02_preview_features/15_rpitit_preview.md",
        "extract": [
            ("RPITIT-RTN-TAIT-定义", r"RPITIT|Return Position Impl Trait|RTN|Return Type Notation|TAIT|Type Alias Impl Trait|impl Trait.*trait.*返回"),
            ("RPITIT-RTN-TAIT-捕获", r"use<'?[a-zA-Z0-9_, ]*'>|精确捕获|lifetime capture|hidden type"),
        ],
        "polarity_pos": r"RPITIT|RTN|TAIT|impl Trait.*trait",
        "polarity_neg": r"RPITIT.*不稳定|TAIT.*未稳定",
        "allowed_variances": [],
    },
    "GAT + async": {
        "name_en": "GAT + async",
        "canonical": "03_advanced/01_async/14_gat_async_boundary.md",
        "extract": [
            ("GAT-async-边界", r"GAT.*async|async trait.*GAT|type Future<'a>|where Self: 'a.*Future|GAT.*Future"),
            ("GAT-async-生命周期", r"关联类型.*生命周期|type constructor.*lifetime|where Self: 'a"),
        ],
        "polarity_pos": r"type Future<'a>|where Self: 'a|GAT.*async",
        "polarity_neg": r"GAT.*不需要.*where Self: 'a|async trait.*不需要.*GAT",
        "allowed_variances": [],
    },
    "allocator_api": {
        "name_en": "allocator_api / custom allocators",
        "canonical": "03_advanced/06_low_level_patterns/01_custom_allocators.md",
        "extract": [
            ("allocator-api-GlobalAlloc", r"GlobalAlloc|allocator_api|#\[global_allocator\]|自定义分配器"),
            ("allocator-api-Allocator", r"Allocator trait|Allocator API|alloc::alloc::Allocator|分配器属性"),
        ],
        "polarity_pos": r"GlobalAlloc|Allocator trait|allocator_api",
        "polarity_neg": r"Allocator API.*已废弃|自定义分配器.*不安全.*避免",
        "allowed_variances": [],
    },
    "match ergonomics": {
        "name_en": "match ergonomics / default binding mode",
        "canonical": "01_foundation/04_control_flow/02_patterns.md",
        "extract": [
            ("match-ergonomics-默认绑定", r"default binding mode|默认绑定模式|match ergonomics|绑定模式.*自动|ref.*绑定"),
            ("match-ergonomics-引用", r"match.*引用.*自动|match &opt.*x.*&T|if let.*引用.*自动"),
        ],
        "polarity_pos": r"default binding mode|match ergonomics|自动.*ref",
        "polarity_neg": r"match ergonomics.*不存在|默认绑定.*不自动",
        "allowed_variances": [],
    },
    "临时作用域/tail drop": {
        "name_en": "temporary scope / tail expression drop",
        "canonical": "04_formal/05_rustc_internals/09_destructors.md",
        "extract": [
            ("temporary-scope-临时作用域", r"临时作用域|Temporary Scopes|temporary scope|临时生命周期"),
            ("temporary-scope-tail", r"tail expression.*drop|块 tail expression.*临时.*drop|尾表达式.*drop|2024 Edition.*if let.*临时值.*drop"),
        ],
        "polarity_pos": r"临时作用域|tail expression.*drop|尾表达式.*drop",
        "polarity_neg": r"临时作用域.*不.*drop|tail expression.*不.*drop",
        "allowed_variances": [],
    },
}


def find_md_files() -> list[Path]:
    """查找核心 markdown 文件,排除非知识体系文件"""
    files = []
    for root, _, names in os.walk(CONCEPT_DIR):
        for name in names:
            if not name.endswith(".md"):
                continue
            if name in EXCLUDE_FILES:
                continue
            if any(name.startswith(p) for p in EXCLUDE_PREFIXES):
                continue
            rel = Path(root).relative_to(CONCEPT_DIR)
            rel_str = str(rel)
            if not (rel_str.startswith("00_meta") or (rel_str.startswith("0") and len(rel_str) >= 2 and rel_str[1].isdigit())):
                continue
            files.append(Path(root) / name)
    files.sort()
    return files


def resolve_canonical(name: str, md_files: list[Path]) -> Optional[Path]:
    """按基线路径解析权威页;若基线路径不存在,按文件名在 concept/ 中动态回退查找。"""
    baseline = CONCEPT_DIR / CANONICAL_PAGES[name]
    if baseline.exists():
        return baseline
    basename = Path(CANONICAL_PAGES[name]).name
    matches = [f for f in md_files if f.name == basename]
    return matches[0] if matches else None


@dataclass
class ConceptDef:
    """概念定义片段"""
    concept: str
    file: Path
    line_no: int
    text: str
    context: str  # 前后几行上下文


@dataclass
class CrossRef:
    """跨文件引用"""
    source_file: Path
    line_no: int
    target_file: Path
    section_ref: str  # e.g., "§2.2"
    raw_text: str


# ==================== 提取器 ====================

def _is_in_code_block(lines: list[str], idx: int) -> bool:
    """判断指定行是否在代码块内(排除 text / mermaid / 无语言标记的块)"""
    in_block = False
    block_lang = ""
    for i, line in enumerate(lines):
        if i > idx:
            break
        stripped = line.strip()
        if stripped.startswith("```"):
            if not in_block:
                in_block = True
                block_lang = stripped[3:].strip().split(",")[0].lower()
            else:
                in_block = False
                block_lang = ""
    if not in_block:
        return False
    # text / mermaid / 空语言标记的块不视为代码块(允许提取概念定义)
    if block_lang in ("", "text", "mermaid"):
        return False
    return True


def _get_context(lines: list[str], idx: int, radius: int = 2) -> str:
    """获取指定行前后 radius 行的上下文"""
    start = max(0, idx - radius)
    end = min(len(lines), idx + radius + 1)
    return "\n".join(lines[start:end])


def _iter_lines(content: str):
    """逐行迭代,跳过代码块。yield (line_no_1based, line, lines)"""
    lines = content.split("\n")
    for i, line in enumerate(lines, 1):
        if _is_in_code_block(lines, i - 1):
            continue
        yield i, line, lines


# 提取规则表: (concept 标签, 行匹配模式, 可选排除模式)
_EXTRACT_RULES: list[tuple[str, str, Optional[str]]] = [
    # ---- Send / Sync ----
    ("Send", r'T:\s*Send\s*⇔|Send\s*trait.*(?:move|转移|线程)|T:\s*Send\s*⇔.*线程.*安全|Send.*表示.*可跨线程转移|Send.*marker trait.*安全|所有权.*跨线程.*转移', None),
    ("Sync", r'T:\s*Sync\s*⇔|Sync\s*trait.*(?:共享|引用|线程)|T:\s*Sync\s*⇔.*&T.*Send|Sync.*表示.*可跨线程共享引用|Sync.*marker trait.*安全|&T:\s*Send', None),
    ("Send+Sync", r'Send.*Sync.*(?:auto trait|marker trait|线程安全)|并发安全.*Send.*Sync', None),
    # ---- 所有权 ----
    ("所有权-唯一所有权", r'唯一所有权|每个值有且仅有一个所有者|每个值有唯一所有者|ownership.*唯一', r'表格|矩阵|mind map|mermaid'),
    ("所有权-作用域绑定", r'作用域绑定|所有者离开作用域|owner.*离开.*作用域|RAII.*drop|scope.*drop', r'表格|矩阵|mind map|mermaid'),
    ("所有权-Move语义", r'Move 语义|赋值/传参默认转移所有权|move.*所有权|默认转移所有权', r'表格|矩阵|mind map|mermaid'),
    ("所有权-Copy例外", r'Copy 例外|标量类型实现.*Copy|Copy trait.*复制|按位复制.*原变量仍可用', r'表格|矩阵|mind map|mermaid'),
    # ---- 借用 ----
    ("借用-共享引用", r'任意.*(?:多个|数量).*(?:不可变|共享)引用|(?:不可变|共享)引用.*(?:任意|多个).*(?:同时|共存)|多个.*&T.*同时', None),
    ("借用-可变独占", r'(?:同一时刻|同一时间|同时).*(?:只能|至多).*(?:一个|唯一).*可变引用|可变引用.*独占|exclusive.*(?:mutable|&mut)|&mut T.*独占', None),
    ("借用-读写互斥", r'不可变引用.*可变引用.*不能同时|存在.*可变引用.*时.*不能.*不可变引用|读写.*互斥|别名.*互斥', None),
    ("借用-引用有效", r'引用.*必须.*有效|引用.*不得.*悬垂|dangling.*reference|引用.*生命周期.*内.*有效', None),
    # ---- 生命周期 ----
    ("生命周期-Rule1", r'Rule 1.*(?:输入|参数|独立).*生命周期|函数参数.*每个引用.*独立生命周期|Rule 1.*输入参数|每个引用参数.*(?:获得|独立).*生命周期', None),
    ("生命周期-Rule2", r'Rule 2.*(?:单输入|输出|唯一).*生命周期|只有一个输入生命周期.*输出|Rule 2.*单输入', None),
    ("生命周期-Rule3", r'Rule 3.*(?:&self|self|方法).*生命周期|&self.*输出生命周期|Rule 3.*self', None),
    ("生命周期-定义", r'生命周期.*引用有效|引用存活.*至少|lifetimes?.*确保.*引用.*valid', r'表格|矩阵|mind map|mermaid'),
    # ---- 内部可变性 ----
    ("内部可变性-定义", r'内部可变性.*(?:允许|通过|模式)|interior mutabilit.*(?:allow|pattern)|通过.*UnsafeCell.*(?:修改|可变)', None),
    ("内部可变性-运行时检查", r'RefCell.*运行时.*(?:借用|检查)|运行时.*借用检查.*RefCell|borrow\(\).*panic|运行时.*panic.*借用', None),
    ("内部可变性-UnsafeCell", r'UnsafeCell.*(?:唯一|仅|only).*(?:允许|内部可变)|UnsafeCell.*基础.*(?:Cell|RefCell)|所有内部可变性.*UnsafeCell', None),
    # ---- Pin / Unpin ----
    ("Pin-定义", r'Pin<.*>.*(?:保证|确保|固定).*(?:不|无法).*(?:移动|move)|Pin.*固定.*(?:内存|位置)|pinned.*(?:cannot|not).*(?:move|moved)', None),
    ("Unpin-定义", r'Unpin.*(?:auto trait|自动实现|marker)|Unpin.*(?:允许|可以).*(?:安全)?.*移动|Unpin.*表示.*(?:移动|move).*安全', None),
    ("Pin-自引用", r'自引用.*(?:需要|使用).*Pin|Pin.*自引用|self-referential.*pin', None),
    # ---- 变型(协变/逆变/不变) ----
    ("变型-定义", r'(?:协变|逆变|不变|covariant|contravariant|invariant).*(?:子类型|subtyp)|子类型.*(?:协变|逆变|变型|variance)', None),
    ("变型-规则", r'&\s*mut\s*T.*(?:不变|invariant|协变|covariant)|&T.*(?:协变|covariant)|fn.*(?:逆变|contravariant)|Box<.*>.*(?:协变|covariant)|Cell<.*>.*(?:不变|invariant)', None),
    # ---- unsafe ----
    ("unsafe-语义", r'unsafe.*不是.*关闭|unsafe.*不关闭|unsafe.*不是.*关闭检查器|unsafe.*声明.*程序员', None),
    ("unsafe-契约", r'Safety Contract.*unsafe|unsafe.*Safety Contract|安全契约.*unsafe|unsafe.*安全契约', None),
    ("unsafe-不变式", r'Validity Invariant|Safety Invariant|有效性不变式|安全性不变式', None),
    ("unsafe-UB", r'UB.*未定义行为|undefined behavior|unsafe.*UB|触发.*UB', r'表格|矩阵|mind map|mermaid'),
    # ---- 扩展概念集:Rust 1.97 关键边界术语 ----
    # async fn / Future 等价表述
    ("async-Future-状态机", r'async fn.*状态机|async fn.*desugar.*Future|async/await.*语法糖.*Future|Future.*状态机.*async|async fn.*等价.*返回.*Future', None),
    ("async-Future-等价", r'async fn.*等价|async fn.*≡|async fn.*返回.*impl Future|async fn.*本质上.*Future', None),
    # unsafe five superpowers & unsafe_op_in_unsafe_fn
    ("unsafe-superpowers-五种能力", r'five unsafe superpowers|five superpowers|unsafe.*superpowers|五种.*superpower|五种 unsafe 能力|unsafe.*五种能力', None),
    ("unsafe-superpowers-unsafe_op", r'unsafe_op_in_unsafe_fn|unsafe fn.*显式.*unsafe.*块|unsafe fn.*内部.*unsafe.*块', None),
    # Pin 投影规则(structural projection)
    ("Pin-投影-结构", r'结构投射|structural projection|Pin.*投影|pin-project|字段投影|Pin<&mut Self>.*字段', None),
    ("Pin-投影-安全", r'Pin.*投影.*安全|投影.*保持.*地址|投影.*Unpin.*字段|unsafe.*投影.*UB', None),
    # 生命周期子类型化
    ("生命周期-子类型-static", r'\'static.*<:|\'static.*子类型|子类型.*\'static|lifetime.*subtyp|\'static.*outlives', None),
    ("生命周期-子类型-outlives", r"'a: 'b|outlives|存活.*不短于|生命周期.*偏序|'a.*outlives.*'b", None),
    # Send/Sync 充分必要条件在 trait 对象、泛型边界
    ("Send/Sync边界-充分必要", r'充分必要|dyn Trait \+ Send \+ Sync|T:\s*Send\s*⇔|T:\s*Sync\s*⇔|Arc<dyn.*Send.*Sync>', None),
    ("Send/Sync边界-trait对象", r'dyn Trait.*Send|trait object.*Send|自动实现.*Send/Sync|手动.*unsafe impl.*Send', None),
    # let chains / if-let guards
    ("let-chains-链式", r'let chains|链式 let|if let.*&&.*let|let 链', None),
    ("let-chains-守卫", r'if-let guards|let 守卫|if let.*守卫|match.*if let', None),
    # unsafe extern blocks
    ("unsafe-extern-块", r'unsafe extern blocks|unsafe extern "C"|extern.*块.*unsafe|unsafe extern "', None),
    ("unsafe-extern-safe", r'safe fn.*extern|extern.*safe.*审计|safe FFI|unsafe extern.*safe', None),
    # const trait impl / effects system
    ("const-trait-impl-定义", r'const trait impl|const impl Trait|~const|常量上下文.*Trait|const fn.*trait', None),
    ("const-trait-impl-效果", r'const.*效果|const.*effect|效果系统.*const|constness.*effect', None),
    # effects system
    ("effects-system-定义", r'effect system|效果系统|代数效应|generic over effects|效果多态', None),
    ("effects-system-现有", r'async.*效果|const.*效果|try.*效果|unsafe.*效果|效果.*关键字', None),
    # RPITIT / RTN / TAIT
    ("RPITIT-RTN-TAIT-定义", r'RPITIT|Return Position Impl Trait|RTN|Return Type Notation|TAIT|Type Alias Impl Trait|impl Trait.*trait.*返回', None),
    ("RPITIT-RTN-TAIT-捕获", r"use<'?[a-zA-Z0-9_, ]*'>|精确捕获|lifetime capture|hidden type", None),
    # GAT + async
    ("GAT-async-边界", r"GAT.*async|async trait.*GAT|type Future<'a>|where Self: 'a.*Future|GAT.*Future", None),
    ("GAT-async-生命周期", r'关联类型.*生命周期|type constructor.*lifetime|where Self: \'a', None),
    # allocator_api
    ("allocator-api-GlobalAlloc", r'GlobalAlloc|allocator_api|#\[global_allocator\]|自定义分配器', None),
    ("allocator-api-Allocator", r'Allocator trait|Allocator API|alloc::alloc::Allocator|分配器属性', None),
    # match ergonomics / default binding mode
    ("match-ergonomics-默认绑定", r'default binding mode|默认绑定模式|match ergonomics|绑定模式.*自动|ref.*绑定', None),
    ("match-ergonomics-引用", r'match.*引用.*自动|match &opt.*x.*&T|if let.*引用.*自动', None),
    # temporary scope / tail expression drop
    ("temporary-scope-临时作用域", r'临时作用域|Temporary Scopes|temporary scope|临时生命周期', None),
    ("temporary-scope-tail", r'tail expression.*drop|块 tail expression.*临时.*drop|尾表达式.*drop|2024 Edition.*if let.*临时值.*drop', None),
]

# 编译提取规则
_COMPILED_RULES = [
    (label, re.compile(pat, re.IGNORECASE), re.compile(neg, re.IGNORECASE) if neg else None)
    for label, pat, neg in _EXTRACT_RULES
]


def extract_concept_defs(content: str, filepath: Path) -> list[ConceptDef]:
    """按统一规则表提取概念定义"""
    defs = []
    for i, line, lines in _iter_lines(content):
        for label, pat, neg in _COMPILED_RULES:
            if neg and neg.search(line):
                continue
            if pat.search(line):
                defs.append(ConceptDef(label, filepath, i, line.strip(), _get_context(lines, i - 1)))
    return defs


# ==================== 跨文件引用验证 ====================

# 段落引用中的章节编号:阿拉伯数字(§2.2)或中文数字(§二)
_SEC_REF = r'§([0-9][0-9.]*|[一二三四五六七八九十]{1,3})'
_CJK_DIGITS = {'一': 1, '二': 2, '三': 3, '四': 4, '五': 5, '六': 6, '七': 7, '八': 8, '九': 9}


def _cjk_to_int(s: str) -> Optional[int]:
    """中文数字 -> int(支持 一..十、十一..十九、二十..九十九)"""
    if s in _CJK_DIGITS:
        return _CJK_DIGITS[s]
    if s == '十':
        return 10
    if s.startswith('十') and len(s) == 2:
        return 10 + _CJK_DIGITS.get(s[1], 0)
    if '十' in s:
        a, _, b = s.partition('十')
        tens = _CJK_DIGITS.get(a, 1) if a else 1
        return tens * 10 + (_CJK_DIGITS.get(b, 0) if b else 0)
    return None


def extract_sections(content: str) -> list[tuple[str, int]]:
    """提取文件中的章节编号:## 2.1 xxx(阿拉伯)与 ## 二、xxx(中文数字,映射为阿拉伯值)"""
    sections = []
    for i, line in enumerate(content.split("\n"), 1):
        m = re.match(r'#{2,4}\s+(\d+(?:\.\d+)*)(?:\s+|$)', line)
        if m:
            sections.append((m.group(1), i))
            continue
        m = re.match(r'#{1,6}\s+([一二三四五六七八九十]{1,3})[、.．\s]', line)
        if m:
            v = _cjk_to_int(m.group(1))
            if v is not None:
                sections.append((str(v), i))
    return sections


def extract_cross_file_refs(content: str, source_file: Path, all_files: list[Path]) -> list[CrossRef]:
    """提取跨文件段落引用,如 file.md §2.2 或 [主题 §1.2](file.md)"""
    refs = []
    lines = content.split("\n")
    file_set = {str(f.resolve()) for f in all_files}

    def _add(target: Optional[Path], section: str, line_no: int, raw: str):
        if target and str(target) in file_set:
            sec = _cjk_to_int(section)
            sec_str = f"§{sec}" if sec is not None and not section[0].isdigit() else f"§{section}"
            if not any(r.raw_text == raw and r.section_ref == sec_str and r.target_file == target for r in refs):
                refs.append(CrossRef(source_file, line_no, target, sec_str, raw))

    for i, line in enumerate(lines, 1):
        # 模式0: [链接文本 §X.X](path/to/file.md) —— § 在链接文本内,归属本链接
        for m in re.finditer(r'\[([^\]]*' + _SEC_REF + r'[^\]]*)\]\(([^)]+\.md)\)', line):
            target = _resolve_ref(source_file, m.group(2))
            for sm in re.finditer(_SEC_REF, m.group(1)):
                _add(target, sm.group(1), i, line.strip())

        # 模式1: [text](path/to/file.md) §X.X
        for m in re.finditer(r'\]\(([^)]+\.md)\)\s*' + _SEC_REF, line):
            _add(_resolve_ref(source_file, m.group(1)), m.group(2), i, line.strip())

        # 模式2: `path/to/file.md §X.X` 或 file.md §X.X
        for m in re.finditer(r'`?([^`\s\]]+\.md)`?\s*' + _SEC_REF, line):
            target_rel = m.group(1)
            if target_rel.startswith("http"):
                continue
            _add(_resolve_ref(source_file, target_rel), m.group(2), i, line.strip())

        # 模式3: 文件链接后带 "§X.X"(限制在 30 字符内,且间隔只允许标点/空白——
        # 排除「迁移树 §7」这类属于其他主体的 § 引用,以及下一个链接的链接文本)
        for m in re.finditer(r'\]\(([^)]+\.md)\)', line):
            target = _resolve_ref(source_file, m.group(1))
            if not (target and str(target) in file_set):
                continue
            rest = line[m.end():m.end() + 30]
            m2 = re.search(_SEC_REF, rest)
            if m2 and re.fullmatch(r'[\s·•|,:：—–\-]*', rest[:m2.start()]):
                _add(target, m2.group(1), i, line.strip())

    return refs


def _resolve_ref(source: Path, ref: str) -> Optional[Path]:
    """解析相对引用为绝对路径"""
    try:
        if ref.startswith("/"):
            return Path(ref).resolve()
        target = (source.parent / ref).resolve()
        if target.exists():
            return target
        target2 = (CONCEPT_DIR / ref).resolve()
        if target2.exists():
            return target2
    except Exception:
        pass
    return None


def validate_section_ref(section_ref: str, sections: list[tuple[str, int]]) -> bool:
    """验证段落引用是否存在(中文数字已在提取/归集时映射为阿拉伯值)"""
    ref_num = section_ref.lstrip("§")
    cjk = _cjk_to_int(ref_num)
    if cjk is not None:
        ref_num = str(cjk)
    for sec, _ in sections:
        if sec == ref_num:
            return True
    # 前缀匹配:§2 可以匹配 2.1, 2.2 等
    if "." not in ref_num:
        for sec, _ in sections:
            if sec.startswith(ref_num + "."):
                return True
    return False


# ==================== 一致性检测 ====================

def _norm_path(p: Path) -> str:
    """返回相对项目根的路径字符串,用于报告"""
    try:
        return p.resolve().relative_to(ROOT).as_posix()
    except ValueError:
        return str(p)


def _issue(type_: str, file: str, detail: str, severity: str) -> dict:
    return {"type": type_, "file": file, "detail": detail, "severity": severity}


def check_canonical_presence(defs: list[ConceptDef], md_files: list[Path]) -> list[dict]:
    """校验每个概念的权威页存在且包含至少一条核心定义"""
    issues = []
    for concept in CANONICAL_PAGES:
        canonical = resolve_canonical(concept, md_files)
        if canonical is None:
            issues.append(_issue(
                f"{concept} 权威页缺失",
                CANONICAL_PAGES[concept],
                "基线权威页文件不存在,且按文件名回退查找失败",
                "❌ 错误",
            ))
            continue
        # 权威页应包含至少一条该概念的定义(变型/unsafe 等概念标签前缀匹配)
        prefixes = {
            "Send/Sync": ("Send", "Sync", "Send+Sync"),
            "所有权": ("所有权-",),
            "借用": ("借用-",),
            "生命周期": ("生命周期-",),
            "内部可变性": ("内部可变性-",),
            "Pin/Unpin": ("Pin-", "Unpin-"),
            "变型": ("变型-",),
            "unsafe": ("unsafe-",),
            "async fn/Future": ("async-Future-",),
            "unsafe superpowers": ("unsafe-superpowers-",),
            "Pin 投影": ("Pin-投影-",),
            "生命周期子类型": ("生命周期-子类型-",),
            "Send/Sync 边界": ("Send/Sync边界-",),
            "let chains": ("let-chains-",),
            "unsafe extern blocks": ("unsafe-extern-",),
            "const trait impl": ("const-trait-impl-",),
            "effects system": ("effects-system-",),
            "RPITIT/RTN/TAIT": ("RPITIT-RTN-TAIT-",),
            "GAT + async": ("GAT-async-",),
            "allocator_api": ("allocator-api-",),
            "match ergonomics": ("match-ergonomics-",),
            "临时作用域/tail drop": ("temporary-scope-",),
        }[concept]
        n = sum(1 for d in defs if d.file == canonical and d.concept.startswith(prefixes))
        if n == 0:
            issues.append(_issue(
                f"{concept} 权威页核心定义缺失",
                _norm_path(canonical),
                "权威页中未提取到该概念的任何核心定义(可能抽取规则需更新,或定义表述偏离基线)",
                "⚠️ 警告",
            ))
    return issues


def check_send_sync_consistency(defs: list[ConceptDef]) -> list[dict]:
    """检测具体类型的 Send/Sync 属性跨文件矛盾(以 17_send_sync_auto_traits.md 为基线)"""
    issues = []
    send_defs = [d for d in defs if d.concept in ("Send", "Send+Sync")]
    sync_defs = [d for d in defs if d.concept in ("Sync", "Send+Sync")]

    # 矛盾检测:具体类型的 Send/Sync 属性是否矛盾
    type_props: dict[str, dict[Path, str]] = defaultdict(dict)
    prop_pattern = re.compile(
        r'(Rc|Arc|RefCell|Mutex|Cell|AtomicUsize|Vec|String|i32|bool|f64|dyn Trait|PhantomData)'
        r'[^.。!！\n]{0,40}?'
        r'([!❌]?\s*Send\s*[+]?\s*[!❌]?\s*Sync|[!❌]?\s*Sync\s*[+]?\s*[!❌]?\s*Send)',
        re.IGNORECASE
    )
    for d in send_defs + sync_defs:
        m = prop_pattern.search(d.text)
        if m:
            type_name = m.group(1)
            prop = m.group(2).replace(" ", "").replace("❌", "!")
            type_props[type_name][d.file] = prop

    for type_name, files_props in type_props.items():
        if len(files_props) <= 1:
            continue
        props = list(files_props.values())
        has_send = any("!Send" not in p and "Send" in p for p in props)
        has_not_send = any("!Send" in p for p in props)
        has_sync = any("!Sync" not in p and "Sync" in p for p in props)
        has_not_sync = any("!Sync" in p for p in props)
        if (has_send and has_not_send) or (has_sync and has_not_sync):
            detail = "; ".join(f"{_norm_path(f)}: {p}" for f, p in files_props.items())
            issues.append(_issue(
                f"{type_name} Send/Sync 属性矛盾",
                ", ".join(_norm_path(f) for f in files_props),
                detail + f"(基线: {CANONICAL_PAGES['Send/Sync']})",
                "❌ 错误",
            ))
    return issues


# 假设/反例/设问语境标记:这些行中的变型表述是“假设性/错误示例”,不作为事实断言
HYPOTHESIS_MARKERS = re.compile(
    r'假设|如果|若 |假如|为什么|是否|误用|错误|陷阱|反例|并非|不是|不能|suppose', re.IGNORECASE)


def check_variance_consistency(defs: list[ConceptDef]) -> list[dict]:
    """检测类型构造器对类型参数 T 的变型(协变/逆变/不变)跨文件矛盾

    真值基线(见 concept/04_formal/00_type_theory/02_subtype_variance.md):
      &T 协变 / &mut T 对 T 不变 / Box<T> 协变 / Cell<T> 不变 / fn 参数逆变、返回值协变

    为避免误报,仅接受显式断言形式:
      - 「对 T 协变/逆变/不变」「对 `T` 是不变」
      - 「→ 协变」「: 不变」「是协变」等紧邻连接词
      - 表格形式「| `T` | 不变 |」
    并跳过含假设/设问/反例标记的行(如“假设 &mut T 是协变”的反证法)。
    """
    issues = []
    claims: dict[str, dict[Path, str]] = defaultdict(dict)
    ctor_pat = re.compile(
        r"(&'?\w*\s*mut\s*T|&'?\w*\s*T|Box\s*<\s*T\s*>|Cell\s*<\s*T\s*>|RefCell\s*<\s*T\s*>"
        r"|Vec\s*<\s*T\s*>|Mutex\s*<\s*T\s*>|UnsafeCell\s*<\s*T\s*>|fn\s*\(\s*T\s*\))")
    # 连接词 + 变型关键词:关键词必须由显式连接词引出(排除“子类型方向不变”等描述性用法)
    claim_pat = re.compile(
        r"(对\s*`?T`?\s*(?:是|为|:|：)?|是|为|:|：|→|\|\s*`?T`?\s*\||over\s+T\s*(?:is\s*)?)\s*`?(协变|逆变|不变)`?")
    kind_norm = {"协变": "covariant", "逆变": "contravariant", "不变": "invariant"}

    def norm_ctor(raw: str) -> str:
        s = re.sub(r"'\w+\s*", "", raw)          # 去生命周期标注 &'a T -> &T
        s = re.sub(r"\s+", "", s)
        return s

    for d in defs:
        if not d.concept.startswith("变型"):
            continue
        line = d.text
        if HYPOTHESIS_MARKERS.search(line):
            continue
        ctors = [(m.start(), norm_ctor(m.group(1))) for m in ctor_pat.finditer(line)]
        if not ctors:
            continue
        for m in claim_pat.finditer(line):
            # 归属给断言前 40 字符内最近的构造器
            before = [c for pos, c in ctors if pos <= m.start() and m.start() - pos <= 40]
            if not before:
                continue
            ctor = before[-1]
            claims[ctor][d.file] = kind_norm[m.group(2)]

    for ctor, files_kinds in claims.items():
        kinds = set(files_kinds.values())
        if len(kinds) <= 1:
            continue
        detail = "; ".join(f"{_norm_path(f)}: {k}" for f, k in files_kinds.items())
        issues.append(_issue(
            f"{ctor} 变型矛盾",
            ", ".join(_norm_path(f) for f in files_kinds),
            detail + f"(基线: {CANONICAL_PAGES['变型']})",
            "❌ 错误",
        ))
    return issues


def check_polarity_consistency(defs: list[ConceptDef]) -> list[dict]:
    """通用极性冲突检测:同一概念的关键断言出现相反极性"""
    issues = []
    # (概念, 断言标签, 正向模式, 反向模式, 反向排除模式)
    # 反向模式仅匹配显式相反断言;反向排除模式剔除“推迟/而非/替代”等一致性表述
    polarity_rules = [
        ("借用-可变独占", "可变引用独占",
         r'同一(?:时刻|时间).*(?:只能|至多).*(?:一个|唯一).*可变引用|可变引用.*独占',
         r'(?:可以|允许).*(?:多个|两个).*(?:同时)?.*可变引用|多个可变引用.*(?:同时|共存)',
         None),
        ("内部可变性-运行时检查", "RefCell 运行时检查",
         r'RefCell.*运行时.*(?:检查|借用)',
         r'RefCell[^。\n]*借用检查[^。\n]*(?:发生|进行|完成|位于|是)在?编译期',
         r'而非|而不是|推迟|替代|移|等价|绕过|不同'),
        ("Unpin-定义", "Unpin 为 auto trait",
         r'Unpin.*auto trait|Unpin.*自动(?:实现|推导)',
         r'Unpin.*(?:需要|必须).*(?:手动|手工).*实现|Unpin.*不是.*auto',
         None),
    ]
    for concept, label, pos_pat, neg_pat, neg_exclude in polarity_rules:
        pos, neg = re.compile(pos_pat, re.IGNORECASE), re.compile(neg_pat, re.IGNORECASE)
        neg_ex = re.compile(neg_exclude) if neg_exclude else None
        pos_files, neg_files = set(), set()
        for d in defs:
            if d.concept != concept:
                continue
            if pos.search(d.text):
                pos_files.add(d.file)
            if neg.search(d.text) and not (neg_ex and neg_ex.search(d.text)):
                neg_files.add(d.file)
        conflicts = pos_files & neg_files
        both = pos_files and neg_files and not conflicts
        if conflicts or both:
            involved = (pos_files | neg_files)
            detail = f"正向断言({label})出现于: {', '.join(_norm_path(f) for f in sorted(pos_files)) or '无'}; " \
                     f"反向断言出现于: {', '.join(_norm_path(f) for f in sorted(neg_files)) or '无'}"
            issues.append(_issue(
                f"{label} 极性矛盾",
                ", ".join(_norm_path(f) for f in sorted(involved)),
                detail,
                "❌ 错误",
            ))
    return issues


def check_extended_concept_polarity(defs: list[ConceptDef]) -> list[dict]:
    """扩展概念集的保守极性漂移检测(仅警告,不阻断 strict)"""
    issues = []
    for name, profile in EXTENDED_CONCEPT_PROFILES.items():
        pos_pat = re.compile(profile["polarity_pos"], re.IGNORECASE)
        neg_pat = re.compile(profile["polarity_neg"], re.IGNORECASE)
        labels = [label for label, _ in profile["extract"]]
        if not labels:
            continue
        parts = labels[0].split("-")
        prefix = "-".join(parts[:2]) + "-" if len(parts) >= 2 else labels[0]
        pos_files: set[Path] = set()
        neg_files: set[Path] = set()
        for d in defs:
            if not d.concept.startswith(prefix):
                continue
            if pos_pat.search(d.text):
                pos_files.add(d.file)
            if neg_pat.search(d.text):
                neg_files.add(d.file)
        conflicts = pos_files & neg_files
        both = bool(pos_files) and bool(neg_files) and not conflicts
        if conflicts or both:
            involved = pos_files | neg_files
            detail = (
                f"正向断言出现于: {', '.join(_norm_path(f) for f in sorted(pos_files)) or '无'}; "
                f"反向断言出现于: {', '.join(_norm_path(f) for f in sorted(neg_files)) or '无'}"
            )
            issues.append(_issue(
                f"{name} 极性漂移(扩展概念)",
                ", ".join(_norm_path(f) for f in sorted(involved)),
                detail,
                "⚠️ 警告",
            ))
    return issues


def check_key_term_coverage(defs: list[ConceptDef]) -> list[dict]:
    """各概念权威页的关键术语覆盖检查(提示级,非阻断)"""
    issues = []
    # (概念前缀, 权威页概念名, 关键术语, 最低匹配数)
    coverage_rules = [
        ("所有权-", "所有权", ["唯一", "作用域", "move", "Copy"], 3),
        ("借用-", "借用", ["引用", "可变", "不可变"], 2),
        ("生命周期-", "生命周期", ["引用", "生命周期"], 2),
        ("内部可变性-", "内部可变性", ["Cell", "RefCell"], 2),
        ("Pin-", "Pin/Unpin", ["Pin", "移动"], 2),
        ("Unpin-", "Pin/Unpin", ["Unpin"], 1),
        ("变型-", "变型", ["协变", "逆变", "不变"], 2),
        ("unsafe-", "unsafe", ["unsafe"], 1),
        # 扩展概念关键术语覆盖(提示级)
        ("async-Future-", "async fn/Future", ["async fn", "Future", "状态机"], 2),
        ("unsafe-superpowers-", "unsafe superpowers", ["superpowers", "unsafe_op_in_unsafe_fn"], 1),
        ("Pin-投影-", "Pin 投影", ["投影", "结构投射"], 1),
        ("生命周期-子类型-", "生命周期子类型", ["'static", "outlives", "子类型"], 2),
        ("Send/Sync边界-", "Send/Sync 边界", ["Send", "Sync", "dyn Trait"], 2),
        ("let-chains-", "let chains", ["let chains", "if-let guards"], 1),
        ("unsafe-extern-", "unsafe extern blocks", ["unsafe extern", "safe fn"], 1),
        ("const-trait-impl-", "const trait impl", ["const trait", "~const"], 1),
        ("effects-system-", "effects system", ["effect system", "效果系统"], 1),
        ("RPITIT-RTN-TAIT-", "RPITIT/RTN/TAIT", ["RPITIT", "RTN", "TAIT"], 1),
        ("GAT-async-", "GAT + async", ["GAT", "Future", "where Self"], 2),
        ("allocator-api-", "allocator_api", ["GlobalAlloc", "Allocator"], 1),
        ("match-ergonomics-", "match ergonomics", ["binding mode", "ref"], 1),
        ("temporary-scope-", "临时作用域/tail drop", ["临时作用域", "tail expression"], 1),
    ]
    by_file: dict[Path, str] = defaultdict(str)
    for d in defs:
        by_file[d.file] += " " + d.text

    md_files = sorted({d.file for d in defs})
    for prefix, concept, terms, min_match in coverage_rules:
        canonical = resolve_canonical(concept, md_files)
        if canonical is None:
            continue
        combined = by_file.get(canonical, "")
        matched = sum(1 for t in terms if re.search(t, combined, re.IGNORECASE))
        if matched < min_match:
            issues.append(_issue(
                f"{concept} 权威页关键术语覆盖不足",
                _norm_path(canonical),
                f"期望术语: {', '.join(terms)},实际匹配 {matched}/{len(terms)}(要求 ≥{min_match})",
                "ℹ️ 提示",
            ))
    return issues


# ==================== 报告生成 ====================

def generate_report(
    all_defs: list[ConceptDef],
    cross_refs: list[CrossRef],
    invalid_refs: list[CrossRef],
    consistency_issues: list[dict],
    section_map: dict[Path, list[tuple[str, int]]],
    md_files: list[Path],
    canonical_map: dict[str, Optional[Path]],
) -> str:
    """生成 Markdown 审计报告"""
    lines = [
        "# 概念一致性审计报告 (Concept Consistency Audit)",
        "",
        f"> 生成时间: {datetime.datetime.now().isoformat()}",
        f"> 生成脚本: `scripts/concept_consistency_auditor.py`(扩展后监控 {len(CANONICAL_PAGES)} 个核心概念)",
        f"> 扫描文件数: {len(md_files)}",
        f"> 提取概念定义数: {len(all_defs)}",
        f"> 跨文件引用数: {len(cross_refs)}",
        "",
        "## 目录",
        "",
        "1. [执行摘要](#一执行摘要)",
        "2. [权威页基线](#二权威页基线)",
        "3. [概念一致性检查](#三概念一致性检查)",
        "4. [跨文件段落引用有效性检查](#四跨文件段落引用有效性检查)",
        "5. [附录:概念定义统计](#五附录概念定义统计)",
        "",
        "---",
        "",
        "## 一、执行摘要",
        "",
    ]

    severity_counts = defaultdict(int)
    for issue in consistency_issues:
        severity_counts[issue.get("severity", "")] += 1
    severity_counts["❌ 错误"] += len(invalid_refs)

    total_errors = severity_counts.get("❌ 错误", 0)
    total_warnings = severity_counts.get("⚠️ 警告", 0)
    total_info = severity_counts.get("ℹ️ 提示", 0)

    lines.append("| 检查项 | 状态 | 详情 |")
    lines.append("|:---|:---|:---|")
    check_groups = [
        ("权威页存在性", lambda i: "权威页" in i.get("type", "")),
        ("Send/Sync 属性矛盾", lambda i: "Send/Sync" in i.get("type", "")),
        ("变型矛盾", lambda i: "变型" in i.get("type", "")),
        ("极性矛盾", lambda i: "极性" in i.get("type", "")),
        ("术语覆盖", lambda i: "术语" in i.get("type", "")),
    ]
    for label, pred in check_groups:
        group = [i for i in consistency_issues if pred(i)]
        has_err = any("❌" in i.get("severity", "") for i in group)
        lines.append(f"| {label} | {'⚠️ 需关注' if has_err else '✅ 通过'} | 检测到 {len(group)} 项 |")
    lines.append(f"| 跨文件段落引用有效性 | {'✅ 全部有效' if not invalid_refs else f'❌ {len(invalid_refs)} 个无效引用'} | 共 {len(cross_refs)} 个引用 |")
    lines.append(f"| **总计** | **{total_errors} 错误 / {total_warnings} 警告 / {total_info} 提示** | — |")
    lines.append("")

    # 权威页基线
    lines.append("## 二、权威页基线")
    lines.append("")
    lines.append("| 概念 | 权威页 | 状态 |")
    lines.append("|:---|:---|:---|")
    for concept, path in canonical_map.items():
        status = f"✅ `{_norm_path(path)}`" if path else f"❌ 缺失(基线 `{CANONICAL_PAGES[concept]}`)"
        lines.append(f"| {concept} | `{CANONICAL_PAGES[concept]}` | {status} |")
    lines.append("")

    # 一致性问题明细
    lines.append("## 三、概念一致性检查")
    lines.append("")
    if not consistency_issues:
        lines.append("> ✅ 未检测到一致性问题。")
        lines.append("")
    else:
        lines.append("| 严重程度 | 类型 | 文件 | 详情 |")
        lines.append("|:---|:---|:---|:---|")
        for issue in consistency_issues:
            detail = str(issue.get("detail", "")).replace("|", "\\|")
            lines.append(f"| {issue.get('severity', '')} | {issue.get('type', '')} | {issue.get('file', '')} | {detail} |")
        lines.append("")

    # 跨文件引用检查
    lines.append("## 四、跨文件段落引用有效性检查")
    lines.append("")
    if invalid_refs:
        lines.append(f"> ❌ 发现 {len(invalid_refs)} 个无效段落引用:")
        lines.append("")
        lines.append("| 来源文件 | 行号 | 目标文件 | 引用段落 | 原始文本 |")
        lines.append("|:---|:---|:---|:---|:---|")
        for ref in invalid_refs:
            raw = ref.raw_text[:60].replace("|", "\\|")
            lines.append(f"| {_norm_path(ref.source_file)} | {ref.line_no} | {_norm_path(ref.target_file)} | {ref.section_ref} | {raw}... |")
        lines.append("")
        lines.append("**可用段落编号列表(目标文件前15个):**")
        lines.append("")
        shown = set()
        for ref in invalid_refs:
            if ref.target_file in shown:
                continue
            shown.add(ref.target_file)
            secs = section_map.get(ref.target_file, [])
            lines.append(f"- `{_norm_path(ref.target_file)}`: {', '.join(s[0] for s in secs[:15])}" + (" ..." if len(secs) > 15 else ""))
        lines.append("")
    else:
        lines.append("> ✅ 所有跨文件段落引用均有效。")
        lines.append("")

    # 附录:概念定义统计
    lines.append("## 五、附录:概念定义统计")
    lines.append("")
    concept_counts = defaultdict(int)
    for d in all_defs:
        concept_counts[d.concept] += 1

    lines.append("### 5.1 按概念分类统计")
    lines.append("")
    lines.append("| 概念 | 提取次数 | 涉及文件数 |")
    lines.append("|:---|:---|:---|")
    for concept, count in sorted(concept_counts.items(), key=lambda x: -x[1]):
        files_count = len({d.file for d in all_defs if d.concept == concept})
        lines.append(f"| {concept} | {count} | {files_count} |")
    lines.append("")

    lines.append("---")
    lines.append("")
    lines.append("> 本报告由 `scripts/concept_consistency_auditor.py` 自动生成。")
    lines.append("")

    return "\n".join(lines)


# ==================== 主流程 ====================

def main() -> int:
    ap = argparse.ArgumentParser(description="概念一致性审计器(质量门 17,语义观察门)")
    ap.add_argument("--strict", action="store_true", help="有错误级发现时 exit 1(默认观察模式 exit 0)")
    ap.add_argument("--json", action="store_true", help="JSON 摘要输出(仍生成报告)")
    args = ap.parse_args()

    print("=" * 60)
    print("概念一致性审计器 (Concept Consistency Auditor)")
    print("=" * 60)

    md_files = find_md_files()
    print(f"\n发现 {len(md_files)} 个核心 markdown 文件")

    canonical_map = {concept: resolve_canonical(concept, md_files) for concept in CANONICAL_PAGES}
    missing = [c for c, p in canonical_map.items() if p is None]
    if missing:
        print(f"  ❌ 权威页缺失: {', '.join(missing)}")

    all_defs: list[ConceptDef] = []
    section_map: dict[Path, list[tuple[str, int]]] = {}
    file_contents: dict[Path, str] = {}

    for filepath in md_files:
        content = filepath.read_text(encoding="utf-8")
        file_contents[filepath.resolve()] = content
        section_map[filepath.resolve()] = extract_sections(content)
        all_defs.extend(extract_concept_defs(content, filepath))

    print(f"提取 {len(all_defs)} 条概念定义")

    # 提取跨文件引用
    all_cross_refs: list[CrossRef] = []
    for filepath in md_files:
        all_cross_refs.extend(extract_cross_file_refs(file_contents[filepath.resolve()], filepath, md_files))

    print(f"发现 {len(all_cross_refs)} 个跨文件段落引用")

    # 验证引用有效性
    invalid_refs: list[CrossRef] = []
    for ref in all_cross_refs:
        sections = section_map.get(ref.target_file, [])
        if not validate_section_ref(ref.section_ref, sections):
            invalid_refs.append(ref)

    print(f"  {'❌ 发现 ' + str(len(invalid_refs)) + ' 个无效引用' if invalid_refs else '✅ 所有引用有效'}")

    # 一致性检查
    print("\n执行一致性检查...")
    consistency_issues: list[dict] = []
    consistency_issues.extend(check_canonical_presence(all_defs, md_files))
    consistency_issues.extend(check_send_sync_consistency(all_defs))
    consistency_issues.extend(check_variance_consistency(all_defs))
    consistency_issues.extend(check_polarity_consistency(all_defs))
    # 扩展概念的极性断言已注册在 EXTENDED_CONCEPT_PROFILES 中；
    # 当前采用保守策略:不自动触发阻断/警告,避免跨上下文(如历史说明、反例页)误报。
    consistency_issues.extend(check_key_term_coverage(all_defs))

    errors = sum(1 for i in consistency_issues if "❌" in i.get("severity", "")) + len(invalid_refs)
    warnings = sum(1 for i in consistency_issues if "⚠️" in i.get("severity", ""))
    infos = sum(1 for i in consistency_issues if "ℹ️" in i.get("severity", ""))
    print(f"  错误: {errors} / 警告: {warnings} / 提示: {infos}")

    # 生成报告
    print("\n生成审计报告...")
    report = generate_report(
        all_defs, all_cross_refs, invalid_refs,
        consistency_issues, section_map, md_files, canonical_map,
    )
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    REPORT_PATH.write_text(report, encoding="utf-8")
    print(f"  ✅ 已保存: {REPORT_PATH.relative_to(ROOT)}")

    if args.json:
        print(json.dumps({
            "files": len(md_files),
            "definitions": len(all_defs),
            "cross_refs": len(all_cross_refs),
            "invalid_refs": len(invalid_refs),
            "errors": errors,
            "warnings": warnings,
            "infos": infos,
            "issues": consistency_issues,
        }, ensure_ascii=False, indent=2))

    print(f"\n{'=' * 60}")
    print(f"审计完成({'strict 阻断' if args.strict else 'observe 观察'})")
    print(f"  文件数: {len(md_files)} / 概念定义: {len(all_defs)} / 跨文件引用: {len(all_cross_refs)}")
    print(f"  无效引用: {len(invalid_refs)} / 错误: {errors} / 警告: {warnings} / 提示: {infos}")
    print(f"{'=' * 60}")

    if args.strict and errors > 0:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
