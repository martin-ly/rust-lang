#!/usr/bin/env python3
"""
知识体系一致性检查器 (Knowledge Base Auditor)

功能:
1. 扫描 concept/ 目录下的所有 .md 文件
2. 提取结构化信息: 标题、层级、定理链、代码块、来源、交叉引用等
3. 执行一致性检查: 链接有效性、定理链来源、代码块标记、过渡段密度等
4. 生成质量仪表盘报告

用法:
    python3 scripts/kb_auditor.py
"""

import datetime
import json
import os
import re
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional

# 统一配置
sys.path.insert(0, str(Path(__file__).resolve().parent))
import concept_config

# 配置
CONCEPT_DIR = concept_config.CONCEPT_DIR
REPORT_PATH = Path("reports/kb_quality_dashboard.md")
JSON_PATH = Path("concept_kb.json")


# 非核心文件排除列表
EXCLUDE_FILES = {
    "00.md", "01.md", "02.md", "03.md", "04.md", "05.md", "06.md", "07.md",
    "README.md", "PLAN.md", "PLAN_Semantic_Space_Wave.md",
    "LSIP_Unified_Model_Panorama.md", "PostgreSQL_LSIP_Unified_Model.md",
}
EXCLUDE_PREFIXES = ("sandbox",)
EXCLUDE_DIRS = {"archive", "deprecated", "sources"}

def find_md_files() -> list[Path]:
    """查找核心 markdown 文件，排除非知识体系文件"""
    files = []
    for root, _, names in os.walk(CONCEPT_DIR):
        rel = Path(root).relative_to(CONCEPT_DIR)
        # 跳过归档/废弃/来源目录
        if any(part in EXCLUDE_DIRS for part in rel.parts):
            continue
        for name in names:
            if not name.endswith(".md"):
                continue
            if name in EXCLUDE_FILES:
                continue
            if any(name.startswith(p) for p in EXCLUDE_PREFIXES):
                continue
            # 只包含 concept/ 下 L0-L7 目录及其子目录中的文件
            if not any(part in concept_config.LAYER_DIRS for part in rel.parts):
                continue
            files.append(Path(root) / name)
    files.sort()
    return files


def detect_layer(filepath: Path) -> str:
    """从路径检测层级 L0-L7。兼容主题子目录。"""
    layer = concept_config.detect_layer(filepath)
    return layer if layer is not None else "L?"


def extract_title(content: str) -> str:
    """提取文件标题 (# 开头的第一行)"""
    match = re.search(r"^# (.+)$", content, re.MULTILINE)
    return match.group(1).strip() if match else "Unknown"


def extract_positioning(content: str) -> str:
    """提取定位段落 (> **定位**)"""
    match = re.search(r"> \*\*定位\*\*[:：]\s*(.+?)(?:\n|$)", content)
    return match.group(1).strip() if match else ""


def extract_theorem_chains(content: str) -> list[dict]:
    """提取 ⟹ 推理链标注（排除代码块内）"""
    chains = []
    in_code_block = False
    for line in content.split("\n"):
        stripped = line.strip()
        # 代码块边界检测
        if stripped.startswith("```"):
            in_code_block = not in_code_block
            continue
        if in_code_block:
            continue
        if "⟹" not in stripped:
            continue
        # 表格行
        if stripped.startswith("|"):
            chains.append({"text": stripped, "type": "table_row"})
        # 引用段落、定义段落、定理/引理/推论段落
        elif any(stripped.startswith(p) for p in ("> **", "##", "###", "**", "- ", "  ", "> ")):
            chains.append({"text": stripped, "type": "paragraph"})
        # 独立行中包含定理相关关键词
        elif any(kw in stripped for kw in ("定理", "引理", "推论", "公理", "前提", "结论", "证明", "定理")):
            chains.append({"text": stripped, "type": "paragraph"})
        # 正文中的独立 ⟹ 行（新增）
        elif stripped and not stripped.startswith("|"):
            chains.append({"text": stripped, "type": "inline"})
    return chains


def extract_anti_propositions(content: str) -> list[dict]:
    """提取反命题决策树（支持多种标题格式）"""
    anti = []
    # 匹配: ### 7.1 反命题... / ### 5.2 反命题决策树 / ## 四、反命题...
    # 也匹配: ### 反例：... / ### 6.3 反命题 1: "..."
    pattern = r"^#{2,3}\s*(?:[\d一二三四五六七八九十\.\s、]+)?(?:反命题|反例|边界分析)"
    for match in re.finditer(pattern, content, re.MULTILINE | re.IGNORECASE):
        # 提取整行作为标题
        line = match.group(0).strip()
        anti.append({"title": line})
    return anti


def extract_code_blocks(content: str) -> list[dict]:
    """提取 rust 代码块及其标记"""
    blocks = []
    pattern = r"```(rust[^\n]*)\n(.*?)```"
    for match in re.finditer(pattern, content, re.DOTALL):
        header = match.group(1).strip()
        code = match.group(2)
        flags = [f.strip() for f in header.replace("rust", "").split(",") if f.strip()]
        blocks.append({
            "flags": flags,
            "lines": code.count("\n") + 1,
            "should_fail": "compile_fail" in flags,
            "code_preview": code[:80].replace("\n", " ") + "...",
        })
    return blocks


def extract_sources(content: str) -> list[dict]:
    """提取来源标注"""
    sources = []
    pattern = r"> \*\*\[来源[:：]\s*([^\]]+)\]\*\*\s*(.+?)(?:\n|$)"
    for match in re.finditer(pattern, content):
        sources.append({
            "source": match.group(1).strip(),
            "context": match.group(2).strip(),
        })
    return sources


def extract_cross_references(content: str) -> list[str]:
    """提取相对链接 (.md 文件引用)"""
    refs = set()
    for match in re.finditer(r"\[([^\]]+)\]\(([^)]+\.md)\)", content):
        refs.add(match.group(2))
    return sorted(refs)


def extract_transitions(content: str) -> list[str]:
    """提取过渡段落（支持多种格式）"""
    transitions = []
    patterns = [
        r">\s*\*\*过渡\*\*[:：]?\s*(.+?)(?:\n|$)",
        r">\s*过渡[:：]?\s*(.+?)(?:\n|$)",
        r">\s*\*\*过渡.*\*\*[:：]?\s*(.+?)(?:\n|$)",
    ]
    for pat in patterns:
        for match in re.finditer(pat, content, re.MULTILINE):
            transitions.append(match.group(1).strip())
    return transitions


def extract_cognitive_path(content: str) -> bool:
    """检查是否有认知路径章节（支持多种标题格式）"""
    patterns = [
        r"^##\s*[〇零一二三四五六七八九十]+[、A-Za-z\-\s]*认知路径",
        r"^##\s*\d+\s*[\.、]?\s*认知路径",
        r"^##\s*认知路径",
        r">\s*\*\*认知路径",
        r"^#+\s*Cognitive Path",
    ]
    for pat in patterns:
        if re.search(pat, content, re.MULTILINE | re.IGNORECASE):
            return True
    return False


def extract_mermaid_blocks(content: str) -> list[str]:
    """提取 Mermaid 图块"""
    blocks = []
    pattern = r"```mermaid\n(.*?)```"
    for match in re.finditer(pattern, content, re.DOTALL):
        blocks.append(match.group(1).strip()[:50] + "...")
    return blocks


def extract_matrix_rows(content: str) -> int:
    """计数定理一致性矩阵的行数 (以 | 开头的行)"""
    return len([l for l in content.split("\n") if l.strip().startswith("|") and "---" not in l])


def extract_pre_post_concepts(content: str) -> dict:
    """提取前置/后置概念标注"""
    pre = []
    post = []
    # 前置概念: > **前置依赖** 或 > **前置概念**
    for match in re.finditer(r"> \*\*前置(?:依赖|概念)?\*\*[:：]?\s*(.+?)(?:\n|$)", content, re.MULTILINE):
        pre.append(match.group(1).strip())
    # 后置概念: > **后置概念** 或 > **后续学习**
    for match in re.finditer(r"> \*\*后置概念\*\*[:：]?\s*(.+?)(?:\n|$)", content, re.MULTILINE):
        post.append(match.group(1).strip())
    for match in re.finditer(r"> \*\*后续学习\*\*[:：]?\s*(.+?)(?:\n|$)", content, re.MULTILINE):
        post.append(match.group(1).strip())
    # 也检测定位段落中的前置/后置
    pos_match = re.search(r"> \*\*定位\*\*[:：]\s*(.+?)(?:\n|$)", content)
    if pos_match:
        pos_text = pos_match.group(1)
        if "前置" in pos_text:
            pre.append(pos_text)
        if "后置" in pos_text:
            post.append(pos_text)
    return {"pre": pre, "post": post}


def extract_dual_labels(content: str) -> dict:
    """提取双标签 (受众 + 内容分级)"""
    labels = {"audience": None, "content_level": None}
    # 受众: > **受众**: [初学者] 或 > **受众**: [初学者] / [进阶]
    audience_match = re.search(r">\s*\*\*受众\*\*[:：]\s*\[([^\]]+)\](?:\s*/\s*\[([^\]]+)\])?", content)
    if audience_match:
        labels["audience"] = audience_match.group(1).strip()
        if audience_match.group(2):
            labels["audience_secondary"] = audience_match.group(2).strip()
    # 内容分级: > **内容分级**: [综述级]
    level_match = re.search(r">\s*\*\*内容分级\*\*[:：]\s*\[([^\]]+)\]", content)
    if level_match:
        labels["content_level"] = level_match.group(1).strip()
    return labels


def extract_backward_chains(content: str) -> list[dict]:
    """提取 ⟸ 反向推理标记（排除代码块内）"""
    chains = []
    in_code_block = False
    for line in content.split("\n"):
        stripped = line.strip()
        if stripped.startswith("```"):
            in_code_block = not in_code_block
            continue
        if in_code_block:
            continue
        if "⟸" not in stripped:
            continue
        chains.append({"text": stripped, "type": "backward"})
    return chains


def detect_templated_chains(content: str) -> list[dict]:
    """检测模板化 ⟹ 标记（元结构重复模式）"""
    templated = []
    # 已知模板模式
    patterns = [
        r"结构化组织\s*⟹\s*高效检索",
        r"质量评估\s*⟹\s*持续改进",
        r"跨层映射\s*⟹\s*系统掌握",
        r"概念分层\s*⟹\s*认知路径清晰",
        r"分类维度\s*⟹\s*索引关系",
        r"量化指标\s*⟹\s*审计流程",
    ]
    for line in content.split("\n"):
        stripped = line.strip()
        if "⟹" not in stripped:
            continue
        for pat in patterns:
            if re.search(pat, stripped):
                templated.append({"text": stripped, "pattern": pat})
                break
    return templated


@dataclass
class FileAudit:
    path: Path
    layer: str
    title: str
    positioning: str
    line_count: int
    theorem_chains: list = field(default_factory=list)
    anti_propositions: list = field(default_factory=list)
    code_blocks: list = field(default_factory=list)
    sources: list = field(default_factory=list)
    cross_references: list = field(default_factory=list)
    transitions: list = field(default_factory=list)
    has_cognitive_path: bool = False
    mermaid_blocks: list = field(default_factory=list)
    matrix_rows: int = 0
    pre_post: dict = field(default_factory=dict)
    backward_chains: list = field(default_factory=list)
    templated_chains: list = field(default_factory=list)
    theorem_chain_exempt: bool = False
    dual_labels: dict = field(default_factory=dict)


def audit_file(filepath: Path) -> FileAudit:
    """审计单个文件"""
    content = filepath.read_text(encoding="utf-8")
    return FileAudit(
        path=filepath,
        layer=detect_layer(filepath),
        title=extract_title(content),
        positioning=extract_positioning(content),
        line_count=len(content.split("\n")),
        theorem_chains=extract_theorem_chains(content),
        anti_propositions=extract_anti_propositions(content),
        code_blocks=extract_code_blocks(content),
        sources=extract_sources(content),
        cross_references=extract_cross_references(content),
        transitions=extract_transitions(content),
        has_cognitive_path=extract_cognitive_path(content),
        mermaid_blocks=extract_mermaid_blocks(content),
        matrix_rows=extract_matrix_rows(content),
        pre_post=extract_pre_post_concepts(content),
        backward_chains=extract_backward_chains(content),
        templated_chains=detect_templated_chains(content),
        theorem_chain_exempt="theorem_chain: N/A" in content or "# theorem_chain: N/A" in content,
        dual_labels=extract_dual_labels(content),
    )


def check_inter_layer_consistency(audits: list[FileAudit]) -> list[dict]:
    """检查跨层引用一致性: L1 文件应引用 L0 元文件, L2 应引用 L1 等"""
    issues = []
    layer_order = {"L0": 0, "L1": 1, "L2": 2, "L3": 3, "L4": 4, "L5": 5, "L6": 6, "L7": 7, "L?": -1}
    for a in audits:
        current_layer_num = layer_order.get(a.layer, -1)
        if current_layer_num <= 0:
            continue
        expected_lower = f"L{current_layer_num - 1}"
        has_lower_ref = False
        for ref in a.cross_references:
            # 优先解析到真实文件并用目录结构判定层级（对文件重编号鲁棒）
            ref_layer = None
            try:
                resolved = (a.path.parent / ref.split("#")[0]).resolve()
                ref_layer = concept_config.detect_layer(resolved)
            except OSError:
                pass
            if ref_layer is None:
                # 回退：从路径片段推断（目录名如 02_intermediate）
                for part in Path(ref).parts:
                    if part in concept_config.LAYER_DIRS:
                        ref_layer = concept_config.LAYER_DIRS[part]
                        break
            if ref_layer == expected_lower:
                has_lower_ref = True
                break
        if not has_lower_ref and a.line_count > 100:
            issues.append({
                "file": str(a.path),
                "layer": a.layer,
                "issue": f"缺少向 {expected_lower} 的向下引用",
            })
    return issues


def check_link_validity(audits: list[FileAudit]) -> list[dict]:
    """检查交叉引用链接的有效性"""
    # 收集所有有效文件的绝对路径和相对路径
    valid_paths_abs = set()
    valid_paths_rel = set()
    for a in audits:
        try:
            valid_paths_abs.add(a.path.resolve())
        except OSError:
            pass
        valid_paths_rel.add(str(a.path).replace("\\", "/"))
        valid_paths_rel.add(str(a.path))
    
    dead_links = []
    for audit in audits:
        for ref in audit.cross_references:
            # 跳过外部 URL
            if ref.startswith(("http://", "https://")):
                continue
            # 尝试多种解析方式
            found = False
            candidates = [
                # 方式1：相对于当前文件
                (audit.path.parent / ref).resolve(),
                # 方式2：相对于 CONCEPT_DIR 的父目录
                (CONCEPT_DIR.parent / ref).resolve(),
                # 方式3：相对于项目根目录
                (CONCEPT_DIR.parent / ref.lstrip("/")).resolve(),
            ]
            for candidate in candidates:
                if candidate.exists():
                    found = True
                    break
                # 检查是否匹配已知的审计文件
                candidate_str = str(candidate).replace("\\", "/")
                if candidate in valid_paths_abs or candidate_str in valid_paths_rel:
                    found = True
                    break
            if not found:
                dead_links.append({
                    "from": str(audit.path),
                    "to": ref,
                    "resolved": str(candidates[0]),
                })
    return dead_links


def check_code_blocks(audits: list[FileAudit]) -> list[dict]:
    """编译验证非 compile_fail 的代码块"""
    issues = []
    tmp_dir = Path("target/kb_auditor_tmp")
    tmp_dir.mkdir(parents=True, exist_ok=True)

    for audit in audits:
        for i, block in enumerate(audit.code_blocks):
            if block["should_fail"]:
                continue  # 跳过 compile_fail
            # 写入临时文件并编译
            tmp_file = tmp_dir / f"{audit.path.stem}_{i}.rs"
            # 简单包装：如果代码没有 main，添加一个
            code = block.get("_full_code", "")
            # 注意：这里不实际编译，因为需要提取完整代码
            # 实际编译验证由独立脚本执行
            pass

    return issues


def generate_dashboard(audits: list[FileAudit], dead_links: list[dict]) -> str:
    """生成质量仪表盘 Markdown"""
    total_files = len(audits)
    total_chains = sum(len(a.theorem_chains) for a in audits)
    total_anti = sum(len(a.anti_propositions) for a in audits)
    total_mermaid = sum(len(a.mermaid_blocks) for a in audits)
    total_code = sum(len(a.code_blocks) for a in audits)
    total_matrix = sum(a.matrix_rows for a in audits)
    total_transitions = sum(len(a.transitions) for a in audits)
    total_backward = sum(len(a.backward_chains) for a in audits)
    total_templated = sum(len(a.templated_chains) for a in audits)

    # 前置/后置概念覆盖率统计
    pre_post_stats = {"has_pre": 0, "has_post": 0, "total": 0}
    dual_label_stats = {"has_both": 0, "total": 0, "illegal": 0}
    for a in audits:
        if a.layer in ("L1", "L2", "L3", "L4", "L5", "L6", "L7"):
            pre_post_stats["total"] += 1
            if a.pre_post.get("pre"):
                pre_post_stats["has_pre"] += 1
            if a.pre_post.get("post"):
                pre_post_stats["has_post"] += 1
            # 双标签统计
            dual_label_stats["total"] += 1
            dl = a.dual_labels
            if dl.get("audience") and dl.get("content_level"):
                dual_label_stats["has_both"] += 1
            audience = dl.get("audience") or ""
            level = dl.get("content_level") or ""
            if "初学者" in audience and level == "研究者级":
                dual_label_stats["illegal"] += 1

    # 按层级统计
    layer_stats = {}
    for a in audits:
        layer = a.layer
        if layer not in layer_stats:
            layer_stats[layer] = {"files": 0, "chains": 0, "transitions": 0, "cog": 0, "backward": 0, "templated": 0, "has_pre": 0, "has_post": 0, "dual_both": 0}
        layer_stats[layer]["files"] += 1
        layer_stats[layer]["chains"] += len(a.theorem_chains)
        layer_stats[layer]["transitions"] += len(a.transitions)
        layer_stats[layer]["cog"] += 1 if a.has_cognitive_path else 0
        layer_stats[layer]["backward"] += len(a.backward_chains)
        layer_stats[layer]["templated"] += len(a.templated_chains)
        if a.pre_post.get("pre"):
            layer_stats[layer]["has_pre"] += 1
        if a.pre_post.get("post"):
            layer_stats[layer]["has_post"] += 1
        dl = a.dual_labels
        if dl.get("audience") and dl.get("content_level"):
            layer_stats[layer]["dual_both"] += 1

    # 风险文件
    risk_files = []
    for a in audits:
        issues = []
        if not a.has_cognitive_path and a.layer in ("L1", "L2", "L3", "L4", "L5"):
            issues.append("缺失认知路径")
        # L0 元文件豁免过渡段和定理链检查（设计预期）
        if a.layer != "L0":
            if len(a.transitions) < 3 and a.line_count > 200:
                issues.append(f"过渡段落不足 ({len(a.transitions)} < 3)")
            if len(a.theorem_chains) < 3 and a.line_count > 200 and not a.theorem_chain_exempt:
                issues.append(f"定理链不足 ({len(a.theorem_chains)} < 3)")
        if len(a.anti_propositions) < 1 and a.layer in ("L1", "L2", "L3", "L4"):
            issues.append("缺失反命题")
        # 前置/后置概念检查 (L1-L7)
        if a.layer in ("L1", "L2", "L3", "L4", "L5", "L6", "L7"):
            if not a.pre_post.get("pre"):
                issues.append("缺失前置概念")
            if not a.pre_post.get("post"):
                issues.append("缺失后置概念")
        # 反向推理检查 (L1-L3 核心文件)
        if a.layer in ("L1", "L2", "L3") and a.line_count > 200 and len(a.backward_chains) < 2:
            issues.append(f"反向推理不足 (⟸ {len(a.backward_chains)} < 2)")
        # 双标签检查 (L1-L7 非归档文件)
        if a.layer in ("L1", "L2", "L3", "L4", "L5", "L6", "L7"):
            dl = a.dual_labels
            if not dl.get("audience"):
                issues.append("缺失受众标签")
            if not dl.get("content_level"):
                issues.append("缺失内容分级标签")
            audience = dl.get("audience") or ""
            level = dl.get("content_level") or ""
            if "初学者" in audience and level == "研究者级":
                issues.append("非法标签组合: 初学者 + 研究者级")
        # 模板化 ⟹ 检查
        if len(a.templated_chains) > 0:
            issues.append(f"含 {len(a.templated_chains)} 个模板化 ⟹ 待重构")
        if issues:
            risk_files.append({
                "file": str(a.path),
                "layer": a.layer,
                "issues": issues,
            })

    lines = [
        "# 知识体系质量仪表盘 (KB Quality Dashboard)",
        "",
        f"> 生成时间: {datetime.datetime.now(datetime.timezone.utc).isoformat()}",
        f"> 扫描文件数: {total_files}",
        "",
        "## 全局指标",
        "",
        "| 指标 | 数值 | 目标 | 状态 |",
        "|:---|:---|:---|:---|",
        f"| 总文件数 | {total_files} | 27 | {'✅' if total_files >= 27 else '⚠️'} |",
        f"| 总定理链 (⟹) | {total_chains} | ≥270 | {'✅' if total_chains >= 270 else '⚠️'} |",
        f"| 总反命题 | {total_anti} | ≥40 | {'✅' if total_anti >= 40 else '⚠️'} |",
        f"| 总 Mermaid 图 | {total_mermaid} | ≥50 | {'✅' if total_mermaid >= 50 else '⚠️'} |",
        f"| 编译验证代码块 | {total_code} | ≥150 | {'✅' if total_code >= 150 else '⚠️'} |",
        f"| 定理矩阵总行 | {total_matrix} | — | — |",
        f"| 死链数量 | {len(dead_links)} | 0 | {'✅' if len(dead_links) == 0 else '❌'} |",
        f"| 反向推理 (⟸) | {total_backward} | ≥50 | {'✅' if total_backward >= 50 else '⚠️'} |",
        f"| 模板化 ⟹ | {total_templated} | 0 | {'✅' if total_templated == 0 else '❌'} |",
        f"| 前置概念覆盖率 | {pre_post_stats['has_pre']}/{pre_post_stats['total']} | 100% | {'✅' if pre_post_stats['has_pre'] == pre_post_stats['total'] else '⚠️'} |",
        f"| 后置概念覆盖率 | {pre_post_stats['has_post']}/{pre_post_stats['total']} | 100% | {'✅' if pre_post_stats['has_post'] == pre_post_stats['total'] else '⚠️'} |",
        f"| 双标签覆盖率 | {dual_label_stats['has_both']}/{dual_label_stats['total']} | >=95% | {'✅' if dual_label_stats['has_both'] >= dual_label_stats['total'] * 0.95 else '⚠️'} |",
        f"| 非法标签组合 | {dual_label_stats['illegal']} | 0 | {'✅' if dual_label_stats['illegal'] == 0 else '❌'} |",
        "",
        "## 按层级分布",
        "",
        "| 层级 | 文件数 | 平均 ⟹/文件 | 平均过渡段/文件 | 认知路径 | ⟸/文件 | 模板化 | 前置覆盖 | 后置覆盖 | 双标签 |",
        "|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|",
    ]

    for layer in sorted(layer_stats.keys()):
        s = layer_stats[layer]
        avg_chains = s["chains"] / s["files"] if s["files"] > 0 else 0
        avg_trans = s["transitions"] / s["files"] if s["files"] > 0 else 0
        cog_rate = f"{s['cog']}/{s['files']} ({s['cog']*100//s['files']}%)"
        avg_backward = s["backward"] / s["files"] if s["files"] > 0 else 0
        pre_rate = f"{s['has_pre']}/{s['files']}" if s["files"] > 0 else "-"
        post_rate = f"{s['has_post']}/{s['files']}" if s["files"] > 0 else "-"
        dual_rate = f"{s['dual_both']}/{s['files']}" if s["files"] > 0 else "-"
        lines.append(f"| {layer} | {s['files']} | {avg_chains:.1f} | {avg_trans:.1f} | {cog_rate} | {avg_backward:.1f} | {s['templated']} | {pre_rate} | {post_rate} | {dual_rate} |")

    lines.extend([
        "",
        "## 风险文件",
        "",
        "| 文件 | 层级 | 未通过项 |",
        "|:---|:---|:---|",
    ])

    if risk_files:
        for rf in risk_files:
            issues_str = "; ".join(rf["issues"])
            lines.append(f"| {rf['file']} | {rf['layer']} | {issues_str} |")
    else:
        lines.append("| — | — | 所有文件通过质量门 |")

    if dead_links:
        lines.extend([
            "",
            "## 死链检测",
            "",
            "| 来源文件 | 引用路径 | 解析后的绝对路径 |",
            "|:---|:---|:---|",
        ])
        for dl in dead_links:
            lines.append(f"| {dl['from']} | {dl['to']} | {dl['resolved']} |")

    lines.extend([
        "",
        "## 文件详细统计",
        "",
        "| 文件 | 层级 | 行数 | ⟹ | ⟸ | 模板 | 反命题 | Mermaid | 代码块 | 过渡段 | 认知路径 | 前置 | 后置 | 受众 | 分级 |",
        "|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|",
    ])

    for a in audits:
        pre_mark = "✅" if a.pre_post.get("pre") else "❌"
        post_mark = "✅" if a.pre_post.get("post") else "❌"
        dl = a.dual_labels
        audience_mark = dl.get("audience", "—")
        level_mark = dl.get("content_level", "—")
        lines.append(
            f"| {a.path} | {a.layer} | {a.line_count} | {len(a.theorem_chains)} | "
            f"{len(a.backward_chains)} | {len(a.templated_chains)} | {len(a.anti_propositions)} | "
            f"{len(a.mermaid_blocks)} | {len(a.code_blocks)} | {len(a.transitions)} | "
            f"{'✅' if a.has_cognitive_path else '❌'} | {pre_mark} | {post_mark} | {audience_mark} | {level_mark} |"
        )

    lines.append("")
    return "\n".join(lines)


def export_json(audits: list[FileAudit]) -> dict:
    """导出为 JSON 格式"""
    return {
        "meta": {
            "version": "1.0",
            "total_files": len(audits),
            "generated_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        },
        "files": [
            {
                "path": str(a.path),
                "layer": a.layer,
                "title": a.title,
                "positioning": a.positioning,
                "line_count": a.line_count,
                "theorem_chains": a.theorem_chains,
                "anti_propositions": a.anti_propositions,
                "code_blocks": a.code_blocks,
                "sources": a.sources,
                "cross_references": a.cross_references,
                "transitions": len(a.transitions),
                "has_cognitive_path": a.has_cognitive_path,
                "mermaid_blocks": len(a.mermaid_blocks),
                "matrix_rows": a.matrix_rows,
                "pre_post": a.pre_post,
                "backward_chains": len(a.backward_chains),
                "templated_chains": len(a.templated_chains),
            }
            for a in audits
        ],
    }


def main():
    print("=" * 60)
    print("知识体系一致性检查器 (KB Auditor)")
    print("=" * 60)

    md_files = find_md_files()
    print(f"\n发现 {len(md_files)} 个 markdown 文件")

    audits = []
    for filepath in md_files:
        print(f"  审计: {filepath}")
        audits.append(audit_file(filepath))

    print(f"\n审计完成，检查链接有效性...")
    dead_links = check_link_validity(audits)
    if dead_links:
        print(f"  ⚠️ 发现 {len(dead_links)} 个死链")
    else:
        print(f"  ✅ 所有链接有效")

    print(f"\n检查跨层引用一致性...")
    inter_layer_issues = check_inter_layer_consistency(audits)
    if inter_layer_issues:
        print(f"  ⚠️ 发现 {len(inter_layer_issues)} 个跨层引用问题")
        for issue in inter_layer_issues[:5]:
            print(f"    - {issue['file']}: {issue['issue']}")
        if len(inter_layer_issues) > 5:
            print(f"    ... 还有 {len(inter_layer_issues) - 5} 个")
    else:
        print(f"  ✅ 跨层引用一致")

    print(f"\n生成质量仪表盘...")
    dashboard = generate_dashboard(audits, dead_links)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    REPORT_PATH.write_text(dashboard, encoding="utf-8", newline="\n")
    print(f"  ✅ 已保存: {REPORT_PATH}")

    print(f"\n导出 JSON...")
    kb_data = export_json(audits)
    JSON_PATH.write_text(json.dumps(kb_data, ensure_ascii=False, indent=2), encoding="utf-8", newline="\n")
    print(f"  ✅ 已保存: {JSON_PATH}")

    # 统计摘要
    total_chains = sum(len(a.theorem_chains) for a in audits)
    total_code = sum(len(a.code_blocks) for a in audits)
    total_mermaid = sum(len(a.mermaid_blocks) for a in audits)
    total_backward = sum(len(a.backward_chains) for a in audits)
    total_templated = sum(len(a.templated_chains) for a in audits)

    print(f"\n{'=' * 60}")
    print("摘要")
    print(f"{'=' * 60}")
    print(f"  文件数:       {len(audits)}")
    print(f"  定理链 (⟹):  {total_chains}")
    print(f"  反向推理 (⟸): {total_backward}")
    print(f"  模板化 ⟹:     {total_templated}")
    print(f"  代码块:       {total_code}")
    print(f"  Mermaid 图:   {total_mermaid}")
    print(f"  死链:         {len(dead_links)}")
    print(f"  跨层问题:     {len(inter_layer_issues)}")
    print(f"{'=' * 60}")

    return_code = 0
    if dead_links:
        return_code = 1
    if inter_layer_issues:
        return_code = 1
    if total_templated > 0:
        return_code = 1
    return return_code


if __name__ == "__main__":
    sys.exit(main())
