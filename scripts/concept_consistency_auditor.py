#!/usr/bin/env python3
"""
概念一致性审计器 (Concept Consistency Auditor)

功能:
1. 扫描 concept/ 目录下的所有 .md 文件
2. 提取关键概念定义（Send、Sync、所有权、生命周期、unsafe 等）
3. 检测同一概念在不同文件中的定义是否矛盾
4. 检测跨文件引用的段落编号是否准确
5. 生成审计报告到 reports/concept_consistency_report.md

用法:
    python3 scripts/concept_consistency_auditor.py
"""

import datetime
import json
import os
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional
from collections import defaultdict

# 配置
CONCEPT_DIR = Path("concept")
REPORT_PATH = Path("reports/concept_consistency_report.md")
JSON_PATH = Path("concept_kb.json")

# 非核心文件排除列表（与 kb_auditor.py 保持一致）
EXCLUDE_FILES = {
    "00.md", "01.md", "02.md", "03.md", "04.md", "05.md", "06.md", "07.md",
    "README.md", "PLAN.md", "PLAN_Semantic_Space_Wave.md",
    "LSIP_Unified_Model_Panorama.md", "PostgreSQL_LSIP_Unified_Model.md",
}
EXCLUDE_PREFIXES = ("sandbox",)


def find_md_files() -> list[Path]:
    """查找核心 markdown 文件，排除非知识体系文件"""
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


@dataclass
class FileSections:
    """文件中的章节信息"""
    path: Path
    sections: list[tuple[str, int]]  # (section_number, line_no)


# ==================== 提取器 ====================

def _is_in_code_block(lines: list[str], idx: int) -> bool:
    """判断指定行是否在代码块内（排除 text / mermaid / 无语言标记的块）"""
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
    # text / mermaid / 空语言标记的块不视为代码块（允许提取概念定义）
    if block_lang in ("", "text", "mermaid"):
        return False
    return True


def extract_send_sync_defs(content: str, filepath: Path) -> list[ConceptDef]:
    """提取 Send/Sync 定义"""
    defs = []
    lines = content.split("\n")
    for i, line in enumerate(lines, 1):
        if _is_in_code_block(lines, i - 1):
            continue
        # Send 定义模式
        if re.search(r'T:\s*Send\s*⇔|Send\s*trait.*(?:move|转移|线程)|T:\s*Send\s*⇔.*线程.*安全|Send.*表示.*可跨线程转移|Send.*marker trait.*安全', line, re.IGNORECASE):
            context = _get_context(lines, i - 1)
            defs.append(ConceptDef("Send", filepath, i, line.strip(), context))
        # Sync 定义模式
        if re.search(r'T:\s*Sync\s*⇔|Sync\s*trait.*(?:共享|引用|线程)|T:\s*Sync\s*⇔.*&T.*Send|Sync.*表示.*可跨线程共享引用|Sync.*marker trait.*安全', line, re.IGNORECASE):
            context = _get_context(lines, i - 1)
            defs.append(ConceptDef("Sync", filepath, i, line.strip(), context))
        # Send/Sync 组合定义
        if re.search(r'Send.*Sync.*(?:auto trait|marker trait|线程安全)|并发安全.*Send.*Sync', line, re.IGNORECASE):
            context = _get_context(lines, i - 1)
            defs.append(ConceptDef("Send+Sync", filepath, i, line.strip(), context))
    return defs


def extract_ownership_defs(content: str, filepath: Path) -> list[ConceptDef]:
    """提取所有权三规则定义"""
    defs = []
    lines = content.split("\n")
    for i, line in enumerate(lines, 1):
        if _is_in_code_block(lines, i - 1):
            continue
        # 唯一所有权
        if re.search(r'唯一所有权|每个值有且仅有一个所有者|每个值有唯一所有者|ownership.*唯一', line, re.IGNORECASE):
            if not re.search(r'表格|矩阵|mind map|mermaid', line, re.IGNORECASE):
                context = _get_context(lines, i - 1)
                defs.append(ConceptDef("所有权-唯一所有权", filepath, i, line.strip(), context))
        # 作用域绑定 / RAII
        if re.search(r'作用域绑定|所有者离开作用域|owner.*离开.*作用域|RAII.*drop|scope.*drop', line, re.IGNORECASE):
            if not re.search(r'表格|矩阵|mind map|mermaid', line, re.IGNORECASE):
                context = _get_context(lines, i - 1)
                defs.append(ConceptDef("所有权-作用域绑定", filepath, i, line.strip(), context))
        # Move 语义
        if re.search(r'Move 语义|赋值/传参默认转移所有权|move.*所有权|默认转移所有权', line, re.IGNORECASE):
            if not re.search(r'表格|矩阵|mind map|mermaid', line, re.IGNORECASE):
                context = _get_context(lines, i - 1)
                defs.append(ConceptDef("所有权-Move语义", filepath, i, line.strip(), context))
        # Copy 例外
        if re.search(r'Copy 例外|标量类型实现.*Copy|Copy trait.*复制|按位复制.*原变量仍可用', line, re.IGNORECASE):
            if not re.search(r'表格|矩阵|mind map|mermaid', line, re.IGNORECASE):
                context = _get_context(lines, i - 1)
                defs.append(ConceptDef("所有权-Copy例外", filepath, i, line.strip(), context))
    return defs


def extract_lifetime_defs(content: str, filepath: Path) -> list[ConceptDef]:
    """提取生命周期省略规则定义"""
    defs = []
    lines = content.split("\n")
    for i, line in enumerate(lines, 1):
        if _is_in_code_block(lines, i - 1):
            continue
        # Elision Rule 1
        if re.search(r'Rule 1.*(?:输入|参数|独立).*生命周期|函数参数.*每个引用.*独立生命周期|Rule 1.*输入参数', line, re.IGNORECASE):
            context = _get_context(lines, i - 1)
            defs.append(ConceptDef("生命周期-Rule1", filepath, i, line.strip(), context))
        # Elision Rule 2
        if re.search(r'Rule 2.*(?:单输入|输出|唯一).*生命周期|只有一个输入生命周期.*输出|Rule 2.*单输入', line, re.IGNORECASE):
            context = _get_context(lines, i - 1)
            defs.append(ConceptDef("生命周期-Rule2", filepath, i, line.strip(), context))
        # Elision Rule 3
        if re.search(r'Rule 3.*(?:&self|self|方法).*生命周期|&self.*输出生命周期|Rule 3.*self', line, re.IGNORECASE):
            context = _get_context(lines, i - 1)
            defs.append(ConceptDef("生命周期-Rule3", filepath, i, line.strip(), context))
        # 生命周期总定义
        if re.search(r'生命周期.*引用有效|引用存活.*至少|lifetimes?.*确保.*引用.*valid', line, re.IGNORECASE):
            if not re.search(r'表格|矩阵|mind map|mermaid', line, re.IGNORECASE):
                context = _get_context(lines, i - 1)
                defs.append(ConceptDef("生命周期-定义", filepath, i, line.strip(), context))
    return defs


def extract_unsafe_defs(content: str, filepath: Path) -> list[ConceptDef]:
    """提取 unsafe 语义定义"""
    defs = []
    lines = content.split("\n")
    for i, line in enumerate(lines, 1):
        if _is_in_code_block(lines, i - 1):
            continue
        # unsafe 不是关闭检查器
        if re.search(r'unsafe.*不是.*关闭|unsafe.*不关闭|unsafe.*不是.*关闭检查器|unsafe.*声明.*程序员', line, re.IGNORECASE):
            context = _get_context(lines, i - 1)
            defs.append(ConceptDef("unsafe-语义", filepath, i, line.strip(), context))
        # Safety Contract / 契约（限定在 unsafe 上下文）
        if re.search(r'Safety Contract.*unsafe|unsafe.*Safety Contract|安全契约.*unsafe|unsafe.*安全契约', line, re.IGNORECASE):
            context = _get_context(lines, i - 1)
            defs.append(ConceptDef("unsafe-契约", filepath, i, line.strip(), context))
        # Validity / Safety Invariant
        if re.search(r'Validity Invariant|Safety Invariant|有效性不变式|安全性不变式', line, re.IGNORECASE):
            context = _get_context(lines, i - 1)
            defs.append(ConceptDef("unsafe-不变式", filepath, i, line.strip(), context))
        # UB 定义
        if re.search(r'UB.*未定义行为|undefined behavior|unsafe.*UB|触发.*UB', line, re.IGNORECASE):
            if not re.search(r'表格|矩阵|mind map|mermaid', line, re.IGNORECASE):
                context = _get_context(lines, i - 1)
                defs.append(ConceptDef("unsafe-UB", filepath, i, line.strip(), context))
    return defs


def _get_context(lines: list[str], idx: int, radius: int = 2) -> str:
    """获取指定行前后 radius 行的上下文"""
    start = max(0, idx - radius)
    end = min(len(lines), idx + radius + 1)
    return "\n".join(lines[start:end])


# ==================== 跨文件引用验证 ====================

def extract_sections(content: str) -> list[tuple[str, int]]:
    """提取文件中的章节编号，如 ## 2.1 xxx 或 ### 5.2 xxx"""
    sections = []
    for i, line in enumerate(content.split("\n"), 1):
        # 匹配 ## 或 ### 开头的数字章节
        m = re.match(r'#{2,4}\s+(\d+(?:\.\d+)*)(?:\s+|$)', line)
        if m:
            sections.append((m.group(1), i))
        # 也匹配 "## 十三、`impl Trait`" 这种非数字章节（不用于 §X.X 验证）
    return sections


def extract_cross_file_refs(content: str, source_file: Path, all_files: list[Path]) -> list[CrossRef]:
    """提取跨文件段落引用，如 file.md §2.2"""
    refs = []
    lines = content.split("\n")
    file_set = {str(f.resolve()) for f in all_files}

    for i, line in enumerate(lines, 1):
        # 模式1: [text](path/to/file.md) §X.X
        for m in re.finditer(r'\]\(([^)]+\.md)\)\s*§([0-9][0-9\.]*)', line):
            target_rel = m.group(1)
            section = m.group(2)
            target = _resolve_ref(source_file, target_rel)
            if target and str(target) in file_set:
                refs.append(CrossRef(source_file, i, target, f"§{section}", line.strip()))

        # 模式2: `path/to/file.md §X.X` 或 file.md §X.X
        for m in re.finditer(r'`?([^`\s]+\.md)`?\s*§([0-9][0-9\.]*)', line):
            target_rel = m.group(1)
            section = m.group(2)
            # 排除 URL 中的 .md
            if target_rel.startswith("http"):
                continue
            target = _resolve_ref(source_file, target_rel)
            if target and str(target) in file_set:
                # 避免重复
                raw = line.strip()
                if not any(r.raw_text == raw and r.section_ref == f"§{section}" for r in refs):
                    refs.append(CrossRef(source_file, i, target, f"§{section}", raw))

        # 模式3: 文件链接后带 "§X.X" 在下一行或同一段（限制在同一句/30字符内，避免跨表格单元格）
        for m in re.finditer(r'\]\(([^)]+\.md)\)', line):
            target_rel = m.group(1)
            target = _resolve_ref(source_file, target_rel)
            if target and str(target) in file_set:
                rest = line[m.end():m.end()+25]
                m2 = re.search(r'§([0-9][0-9\.]*)', rest)
                if m2:
                    section = m2.group(1)
                    raw = line.strip()
                    if not any(r.raw_text == raw and r.section_ref == f"§{section}" and r.target_file == target for r in refs):
                        refs.append(CrossRef(source_file, i, target, f"§{section}", raw))

    return refs


def _resolve_ref(source: Path, ref: str) -> Optional[Path]:
    """解析相对引用为绝对路径"""
    try:
        if ref.startswith("/"):
            return Path(ref).resolve()
        target = (source.parent / ref).resolve()
        if target.exists():
            return target
        # 尝试从 concept/ 根目录解析
        target2 = (CONCEPT_DIR / ref).resolve()
        if target2.exists():
            return target2
    except Exception:
        pass
    return None


def validate_section_ref(target_file: Path, section_ref: str, sections: list[tuple[str, int]]) -> bool:
    """验证段落引用是否存在"""
    ref_num = section_ref.lstrip("§")
    # 精确匹配
    for sec, _ in sections:
        if sec == ref_num:
            return True
    # 前缀匹配：§2 可以匹配 2.1, 2.2 等
    if "." not in ref_num:
        for sec, _ in sections:
            if sec.startswith(ref_num + "."):
                return True
    return False


# ==================== 一致性检测 ====================

def is_core_concept_file(f: Path) -> bool:
    """判断是否为核心概念文件（非 meta 文件）"""
    return "00_meta" not in str(f)


def _norm_path(p: Path) -> str:
    """返回相对路径字符串，用于报告"""
    try:
        return str(p.relative_to(Path.cwd()))
    except ValueError:
        return str(p)


def check_send_sync_consistency(defs: list[ConceptDef]) -> list[dict]:
    """检测 Send/Sync 定义是否一致（含矛盾检测）"""
    issues = []
    send_defs = [d for d in defs if d.concept in ("Send", "Send+Sync")]
    sync_defs = [d for d in defs if d.concept in ("Sync", "Send+Sync")]

    # 只检查核心概念文件和 concurrency/traits/ownership 文件
    target_files = {
        CONCEPT_DIR / "01_foundation" / "01_ownership.md",
        CONCEPT_DIR / "02_intermediate" / "01_traits.md",
        CONCEPT_DIR / "03_advanced" / "01_concurrency.md",
        CONCEPT_DIR / "03_advanced" / "03_unsafe.md",
        CONCEPT_DIR / "04_formal" / "04_rustbelt.md",
        CONCEPT_DIR / "05_comparative" / "01_rust_vs_cpp.md",
    }

    # Send 核心语义检查
    for f in target_files:
        f_send_defs = [d for d in send_defs if d.file == f]
        if not f_send_defs:
            continue
        has_core = any(
            re.search(r'线程.*转移|跨线程.*move|move.*线程|跨线程.*转移|值.*move.*安全', d.text, re.IGNORECASE)
            for d in f_send_defs
        )
        if not has_core:
            issues.append({
                "type": "Send 定义可能不完整",
                "file": _norm_path(f),
                "detail": "该文件中的 Send 定义未明确提及'跨线程转移/值move'核心语义",
                "severity": "⚠️ 警告",
            })

    # Sync 核心语义检查
    for f in target_files:
        f_sync_defs = [d for d in sync_defs if d.file == f]
        if not f_sync_defs:
            continue
        has_core = any(
            re.search(r'&T.*Send|共享引用.*线程|跨线程.*共享|引用.*线程.*安全', d.text, re.IGNORECASE)
            for d in f_sync_defs
        )
        if not has_core:
            issues.append({
                "type": "Sync 定义可能不完整",
                "file": _norm_path(f),
                "detail": "该文件中的 Sync 定义未明确提及'共享引用跨线程安全/&T: Send'核心语义",
                "severity": "⚠️ 警告",
            })

    # 矛盾检测：具体类型的 Send/Sync 属性是否矛盾
    type_props = defaultdict(dict)  # {type_name: {file: property_str}}
    prop_pattern = re.compile(
        r'(Rc|Arc|RefCell|Mutex|Cell|AtomicUsize|Vec|String|i32|bool|f64|dyn Trait|PhantomData)'
        r'.*?'
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
        # 检查是否存在矛盾（如一个文件说 !Send，另一个说 Send）
        has_send = any("!Send" not in p and "Send" in p for p in props)
        has_not_send = any("!Send" in p for p in props)
        has_sync = any("!Sync" not in p and "Sync" in p for p in props)
        has_not_sync = any("!Sync" in p for p in props)
        if (has_send and has_not_send) or (has_sync and has_not_sync):
            detail = "; ".join(f"{_norm_path(f)}: {p}" for f, p in files_props.items())
            issues.append({
                "type": f"{type_name} Send/Sync 属性矛盾",
                "file": ", ".join(_norm_path(f) for f in files_props),
                "detail": detail,
                "severity": "❌ 错误",
            })

    return issues


def check_ownership_consistency(defs: list[ConceptDef]) -> list[dict]:
    """检测所有权三规则描述是否一致"""
    issues = []
    rules = {
        "所有权-唯一所有权": [],
        "所有权-作用域绑定": [],
        "所有权-Move语义": [],
        "所有权-Copy例外": [],
    }
    for d in defs:
        if d.concept in rules:
            rules[d.concept].append(d)

    # 只检查核心概念文件
    target_files = {
        CONCEPT_DIR / "01_foundation" / "01_ownership.md",
        CONCEPT_DIR / "01_foundation" / "02_borrowing.md",
        CONCEPT_DIR / "01_foundation" / "03_lifetimes.md",
        CONCEPT_DIR / "03_advanced" / "01_concurrency.md",
        CONCEPT_DIR / "04_formal" / "03_ownership_formal.md",
        CONCEPT_DIR / "05_comparative" / "01_rust_vs_cpp.md",
    }

    # 检查每条规则在不同文件中的表述差异
    key_terms = {
        "所有权-唯一所有权": ["唯一", "一个所有者", "单一", "资源唯一性"],
        "所有权-作用域绑定": ["作用域", "离开", "drop", "释放", "RAII"],
        "所有权-Move语义": ["move", "转移", "赋值", "传参", "uninitialized"],
        "所有权-Copy例外": ["Copy", "按位复制", "标量", "复制而非移动"],
    }

    for rule_name, rule_defs in rules.items():
        if len(rule_defs) <= 1:
            continue

        files = defaultdict(list)
        for d in rule_defs:
            if d.file in target_files:
                files[d.file].append(d)

        terms = key_terms.get(rule_name, [])
        for f, fdefs in files.items():
            combined = " ".join(d.text for d in fdefs)
            matched = sum(1 for t in terms if re.search(t, combined, re.IGNORECASE))
            if terms and matched < len(terms) // 2 + 1:
                issues.append({
                    "type": f"{rule_name} 关键术语覆盖不足",
                    "file": _norm_path(f),
                    "detail": f"期望包含术语: {', '.join(terms)}，实际匹配 {matched}/{len(terms)} 个",
                    "severity": "⚠️ 警告",
                })

    return issues


def check_lifetime_consistency(defs: list[ConceptDef]) -> list[dict]:
    """检测生命周期省略规则描述是否一致"""
    issues = []
    rules = {
        "生命周期-Rule1": [],
        "生命周期-Rule2": [],
        "生命周期-Rule3": [],
    }
    for d in defs:
        if d.concept in rules:
            rules[d.concept].append(d)

    # Rule 1: 函数参数中每个引用获得独立生命周期
    rule1_keywords = ["独立", "参数", "引用", "获得"]
    # Rule 2: 单输入 → 输出等于输入
    rule2_keywords = ["单输入", "输出", "等于", "唯一"]
    # Rule 3: &self → 输出等于 self
    rule3_keywords = ["self", "方法", "输出"]

    keywords = {
        "生命周期-Rule1": rule1_keywords,
        "生命周期-Rule2": rule2_keywords,
        "生命周期-Rule3": rule3_keywords,
    }

    for rule_name, rule_defs in rules.items():
        if not rule_defs:
            continue
        kws = keywords.get(rule_name, [])
        for d in rule_defs:
            matched = sum(1 for kw in kws if kw in d.text)
            if kws and matched < 2:
                issues.append({
                    "type": f"{rule_name} 描述可能不完整",
                    "file": _norm_path(d.file),
                    "detail": f"行 {d.line_no}: '{d.text[:80]}...' 缺少关键描述要素",
                    "severity": "ℹ️ 提示",
                })

    # 检查 lifetimes.md 是否包含全部三条规则
    lifetimes_file = CONCEPT_DIR / "01_foundation" / "03_lifetimes.md"
    for rule_name in rules:
        rule_files = {d.file for d in rules[rule_name]}
        if lifetimes_file not in rule_files:
            issues.append({
                "type": f"{rule_name} 在 lifetimes.md 中未找到",
                "file": _norm_path(lifetimes_file),
                "detail": f"生命周期省略规则 {rule_name} 应在 lifetimes.md 中有明确定义",
                "severity": "❌ 错误",
            })

    return issues


def check_unsafe_consistency(defs: list[ConceptDef]) -> list[dict]:
    """检测 unsafe 语义是否一致"""
    issues = []
    unsafe_main = CONCEPT_DIR / "03_advanced" / "03_unsafe.md"
    unsafe_files = {d.file for d in defs if d.concept.startswith("unsafe-")}

    # 检查 unsafe.md 中是否有核心定义
    unsafe_md_defs = [d for d in defs if d.file == unsafe_main and d.concept.startswith("unsafe-")]
    if not any(d.concept == "unsafe-语义" for d in unsafe_md_defs):
        issues.append({
            "type": "unsafe 核心语义缺失",
            "file": _norm_path(unsafe_main),
            "detail": "03_unsafe.md 中未找到 'unsafe 不是关闭检查器' 类核心语义定义",
            "severity": "❌ 错误",
        })

    # 只检查核心概念文件
    target_files = {
        CONCEPT_DIR / "01_foundation" / "01_ownership.md",
        CONCEPT_DIR / "01_foundation" / "02_borrowing.md",
        CONCEPT_DIR / "02_intermediate" / "01_traits.md",
        CONCEPT_DIR / "03_advanced" / "01_concurrency.md",
        CONCEPT_DIR / "03_advanced" / "02_async.md",
        CONCEPT_DIR / "04_formal" / "04_rustbelt.md",
        CONCEPT_DIR / "05_comparative" / "01_rust_vs_cpp.md",
    }

    core_messages = [
        r'unsafe.*不是.*关闭|unsafe.*不关闭',
        r'unsafe.*程序员.*证明|unsafe.*人工.*验证',
        r'unsafe.*契约|Safety Contract',
    ]

    for f in target_files & unsafe_files:
        fdefs = [d for d in defs if d.file == f and d.concept.startswith("unsafe-")]
        combined = " ".join(d.text for d in fdefs)
        matched = sum(1 for p in core_messages if re.search(p, combined, re.IGNORECASE))
        if matched == 0 and f != unsafe_main:
            issues.append({
                "type": "unsafe 语义表述不一致",
                "file": _norm_path(f),
                "detail": "该文件提及 unsafe 但未使用与核心文件一致的语义表述（如'不是关闭检查器'、'程序员承担证明'）",
                "severity": "⚠️ 警告",
            })

    return issues


# ==================== 报告生成 ====================

def generate_report(
    all_defs: list[ConceptDef],
    cross_refs: list[CrossRef],
    invalid_refs: list[CrossRef],
    consistency_issues: list[dict],
    section_map: dict[Path, list[tuple[str, int]]],
    md_files: list[Path],
) -> str:
    """生成 Markdown 审计报告"""
    lines = [
        "# 概念一致性审计报告 (Concept Consistency Report)",
        "",
        f"> 生成时间: {datetime.datetime.now().isoformat()}",
        f"> 扫描文件数: {len(md_files)}",
        f"> 提取概念定义数: {len(all_defs)}",
        f"> 跨文件引用数: {len(cross_refs)}",
        "",
        "## 目录",
        "",
        "1. [执行摘要](#一执行摘要)",
        "2. [Send / Sync 一致性检查](#二send--sync-一致性检查)",
        "3. [所有权三规则一致性检查](#三所有权三规则一致性检查)",
        "4. [生命周期省略规则一致性检查](#四生命周期省略规则一致性检查)",
        "5. [unsafe 语义一致性检查](#五unsafe-语义一致性检查)",
        "6. [跨文件段落引用有效性检查](#六跨文件段落引用有效性检查)",
        "7. [附录：概念定义统计](#七附录概念定义统计)",
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

    lines.append(f"| 检查项 | 状态 | 详情 |")
    lines.append(f"|:---|:---|:---|")
    lines.append(f"| Send / Sync 一致性 | {'✅ 通过' if not any('Send' in i.get('type','') and '❌' in i.get('severity','') for i in consistency_issues) else '⚠️ 需关注'} | 检测到 {sum(1 for i in consistency_issues if 'Send' in i.get('type',''))} 项 |")
    lines.append(f"| 所有权三规则一致性 | {'✅ 通过' if not any('所有权' in i.get('type','') and '❌' in i.get('severity','') for i in consistency_issues) else '⚠️ 需关注'} | 检测到 {sum(1 for i in consistency_issues if '所有权' in i.get('type',''))} 项 |")
    lines.append(f"| 生命周期省略规则一致性 | {'✅ 通过' if not any('生命周期' in i.get('type','') and '❌' in i.get('severity','') for i in consistency_issues) else '⚠️ 需关注'} | 检测到 {sum(1 for i in consistency_issues if '生命周期' in i.get('type',''))} 项 |")
    lines.append(f"| unsafe 语义一致性 | {'✅ 通过' if not any('unsafe' in i.get('type','') and '❌' in i.get('severity','') for i in consistency_issues) else '⚠️ 需关注'} | 检测到 {sum(1 for i in consistency_issues if 'unsafe' in i.get('type',''))} 项 |")
    lines.append(f"| 跨文件段落引用有效性 | {'✅ 全部有效' if not invalid_refs else f'❌ {len(invalid_refs)} 个无效引用'} | 共 {len(cross_refs)} 个引用 |")
    lines.append(f"| **总计** | **{total_errors} 错误 / {total_warnings} 警告 / {total_info} 提示** | — |")
    lines.append("")

    # 按类别输出详细问题
    categories = [
        ("二、Send / Sync 一致性检查", [i for i in consistency_issues if "Send" in i.get("type", "")]),
        ("三、所有权三规则一致性检查", [i for i in consistency_issues if "所有权" in i.get("type", "")]),
        ("四、生命周期省略规则一致性检查", [i for i in consistency_issues if "生命周期" in i.get("type", "")]),
        ("五、unsafe 语义一致性检查", [i for i in consistency_issues if "unsafe" in i.get("type", "")]),
    ]

    for title, issues in categories:
        lines.append(f"## {title}")
        lines.append("")
        if not issues:
            lines.append("> ✅ 未检测到一致性问题。")
            lines.append("")
            continue
        lines.append("| 严重程度 | 类型 | 文件 | 详情 |")
        lines.append("|:---|:---|:---|:---|")
        for issue in issues:
            lines.append(f"| {issue.get('severity', '')} | {issue.get('type', '')} | {issue.get('file', '')} | {issue.get('detail', '')} |")
        lines.append("")

    # 跨文件引用检查
    lines.append("## 六、跨文件段落引用有效性检查")
    lines.append("")
    if invalid_refs:
        lines.append(f"> ❌ 发现 {len(invalid_refs)} 个无效段落引用：")
        lines.append("")
        lines.append("| 来源文件 | 行号 | 目标文件 | 引用段落 | 原始文本 |")
        lines.append("|:---|:---|:---|:---|:---|")
        for ref in invalid_refs:
            lines.append(f"| {_norm_path(ref.source_file)} | {ref.line_no} | {_norm_path(ref.target_file)} | {ref.section_ref} | {ref.raw_text[:60]}... |")
        lines.append("")
        lines.append("**可用段落编号列表（目标文件前15个）：**")
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

    # 附录：概念定义统计
    lines.append("## 七、附录：概念定义统计")
    lines.append("")
    concept_counts = defaultdict(int)
    for d in all_defs:
        concept_counts[d.concept] += 1

    lines.append("### 7.1 按概念分类统计")
    lines.append("")
    lines.append("| 概念 | 提取次数 | 涉及文件数 |")
    lines.append("|:---|:---|:---|")
    for concept, count in sorted(concept_counts.items(), key=lambda x: -x[1]):
        files_count = len({d.file for d in all_defs if d.concept == concept})
        lines.append(f"| {concept} | {count} | {files_count} |")
    lines.append("")

    lines.append("### 7.2 按文件统计")
    lines.append("")
    lines.append("| 文件 | 概念定义数 | 跨文件引用数 | 章节数 |")
    lines.append("|:---|:---|:---|:---|")
    for f in md_files:
        defs_count = sum(1 for d in all_defs if d.file == f)
        refs_count = sum(1 for r in cross_refs if r.source_file == f)
        secs_count = len(section_map.get(f.resolve(), []))
        lines.append(f"| {f} | {defs_count} | {refs_count} | {secs_count} |")
    lines.append("")

    lines.append("---")
    lines.append("")
    lines.append("> 本报告由 `scripts/concept_consistency_auditor.py` 自动生成。")
    lines.append("")

    return "\n".join(lines)


# ==================== 主流程 ====================

def main():
    print("=" * 60)
    print("概念一致性审计器 (Concept Consistency Auditor)")
    print("=" * 60)

    md_files = find_md_files()
    print(f"\n发现 {len(md_files)} 个核心 markdown 文件")

    all_defs: list[ConceptDef] = []
    section_map: dict[Path, list[tuple[str, int]]] = {}
    file_contents: dict[Path, str] = {}

    for filepath in md_files:
        content = filepath.read_text(encoding="utf-8")
        file_contents[filepath.resolve()] = content
        section_map[filepath.resolve()] = extract_sections(content)

        all_defs.extend(extract_send_sync_defs(content, filepath))
        all_defs.extend(extract_ownership_defs(content, filepath))
        all_defs.extend(extract_lifetime_defs(content, filepath))
        all_defs.extend(extract_unsafe_defs(content, filepath))

    print(f"提取 {len(all_defs)} 条概念定义")

    # 提取跨文件引用
    all_cross_refs: list[CrossRef] = []
    for filepath in md_files:
        refs = extract_cross_file_refs(file_contents[filepath.resolve()], filepath, md_files)
        all_cross_refs.extend(refs)

    print(f"发现 {len(all_cross_refs)} 个跨文件段落引用")

    # 验证引用有效性
    invalid_refs: list[CrossRef] = []
    for ref in all_cross_refs:
        sections = section_map.get(ref.target_file, [])
        if not validate_section_ref(ref.target_file, ref.section_ref, sections):
            invalid_refs.append(ref)

    if invalid_refs:
        print(f"  ❌ 发现 {len(invalid_refs)} 个无效引用")
    else:
        print(f"  ✅ 所有引用有效")

    # 一致性检查
    print("\n执行一致性检查...")
    consistency_issues: list[dict] = []

    consistency_issues.extend(check_send_sync_consistency(all_defs))
    consistency_issues.extend(check_ownership_consistency(all_defs))
    consistency_issues.extend(check_lifetime_consistency(all_defs))
    consistency_issues.extend(check_unsafe_consistency(all_defs))

    errors = sum(1 for i in consistency_issues if "❌" in i.get("severity", ""))
    warnings = sum(1 for i in consistency_issues if "⚠️" in i.get("severity", ""))
    infos = sum(1 for i in consistency_issues if "ℹ️" in i.get("severity", ""))
    print(f"  错误: {errors} / 警告: {warnings} / 提示: {infos}")

    # 生成报告
    print("\n生成审计报告...")
    report = generate_report(
        all_defs, all_cross_refs, invalid_refs,
        consistency_issues, section_map, md_files
    )
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    REPORT_PATH.write_text(report, encoding="utf-8")
    print(f"  ✅ 已保存: {REPORT_PATH}")

    print(f"\n{'=' * 60}")
    print("审计完成")
    print(f"{'=' * 60}")
    print(f"  文件数:      {len(md_files)}")
    print(f"  概念定义:    {len(all_defs)}")
    print(f"  跨文件引用:  {len(all_cross_refs)}")
    print(f"  无效引用:    {len(invalid_refs)}")
    print(f"  一致性问题:  {len(consistency_issues)}")
    print(f"{'=' * 60}")

    return 0 if errors == 0 and len(invalid_refs) == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
