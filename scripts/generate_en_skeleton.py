#!/usr/bin/env python3
"""批量生成/补全 concept/ 文件的英文骨架元数据。

功能:
- 为缺少 EN 标题的文件生成英文标题（基于 # 标题 + 术语表）。
- 为缺少 Summary 的文件生成英文摘要（基于标题、层级、定义）。
- 为缺少 Prerequisites/Follow-ups 的文件基于 kg_data_v2.json 的 dependsOn 关系补全。

用法:
    python scripts/generate_en_skeleton.py --dry-run
    python scripts/generate_en_skeleton.py --apply
    python scripts/generate_en_skeleton.py --apply --dir concept/01_foundation

注意:
- 本脚本仅生成"骨架"元数据，不翻译正文。
- 生成后需人工审校关键章节。
"""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
from typing import Iterable

ROOT = Path(__file__).resolve().parent.parent
KG_PATH = ROOT / "concept/00_meta/kg_data_v2.json"
TERM_GLOSSARY_PATH = ROOT / "concept/00_meta/terminology_glossary.md"


def load_kg(path: Path) -> dict:
    with path.open("r", encoding="utf-8") as f:
        return json.load(f)


def build_dependency_maps(kg: dict) -> tuple[dict[str, set[str]], dict[str, set[str]]]:
    """构建前置/后置概念映射。"""
    prereqs: dict[str, set[str]] = {}
    followups: dict[str, set[str]] = {}

    for rel in kg.get("relations", []):
        if rel.get("ex:predicate") != "ex:dependsOn":
            continue
        subj = rel["ex:subject"]
        obj = rel["ex:object"]
        prereqs.setdefault(subj, set()).add(obj)
        followups.setdefault(obj, set()).add(subj)

    # 传递闭包
    def transitive(closure: dict[str, set[str]]) -> dict[str, set[str]]:
        changed = True
        while changed:
            changed = False
            for node, deps in list(closure.items()):
                for dep in list(deps):
                    for dd in closure.get(dep, set()):
                        if dd not in deps:
                            deps.add(dd)
                            changed = True
        return closure

    return transitive(prereqs), followups


def label_for(kg: dict, entity_id: str, lang: str = "en") -> str:
    """从 KG 获取实体的指定语言标签。"""
    for items in kg.get("entities", {}).values():
        for item in items:
            if item.get("@id") == entity_id:
                for lbl in item.get("skos:prefLabel", []):
                    if lbl.get("@language") == lang:
                        return lbl["@value"]
    # 去掉 ex: 前缀作为回退
    return entity_id.replace("ex:", "")


def load_glossary(path: Path) -> dict[str, str]:
    """从术语表加载中英对照（简化解析）。"""
    glossary: dict[str, str] = {}
    if not path.exists():
        return glossary
    with path.open("r", encoding="utf-8") as f:
        for line in f:
            # 匹配 "| 中文 | English | ... |"
            m = re.match(r"\|\s*([^|]+?)\s*\|\s*([^|]+?)\s*\|", line)
            if m:
                zh = m.group(1).strip()
                en = m.group(2).strip()
                if zh and en and not zh.startswith("-") and zh != "中文":
                    glossary[zh] = en
    return glossary


def extract_chinese_title(content: str) -> str | None:
    """提取 Markdown 一级标题的中文标题。"""
    for line in content.splitlines():
        if line.startswith("# "):
            title = line[2:].strip()
            # 去掉尾部的英文括号注释
            title = re.sub(r"\s*[（(][^）)]+[）)]\s*$", "", title)
            return title
    return None


def translate_title(title: str, glossary: dict[str, str]) -> str:
    """基于术语表翻译标题。"""
    # 优先匹配整个标题
    if title in glossary:
        return glossary[title]
    # 尝试部分替换（最长匹配）
    result = title
    for zh, en in sorted(glossary.items(), key=lambda x: len(x[0]), reverse=True):
        result = result.replace(zh, en)
    # 如果仍全是中文，返回拼音化占位（需人工审校）
    if re.search(r"[\u4e00-\u9fff]", result):
        return f"{result} (EN TODO)"
    return result


def generate_summary(title_zh: str, title_en: str, layer: str | None) -> str:
    """生成英文摘要占位。"""
    layer_text = {
        "L1": "foundational Rust concept",
        "L2": "intermediate Rust concept",
        "L3": "advanced Rust concept",
        "L4": "formal methods foundation",
        "L5": "comparative analysis",
        "L6": "ecosystem and patterns",
        "L7": "future directions",
    }.get(layer or "", "Rust concept")
    return f"{title_en}: a {layer_text} covering {title_zh}. (Summary TODO)"


def extract_existing_header_value(content: str, key: str) -> str | None:
    """从文件头提取已有字段值。"""
    pattern = rf"\*\*{re.escape(key)}\*\*:\s*(.+?)(?:\n>\s*\*\*|\n---)"
    m = re.search(pattern, content, re.DOTALL)
    if m:
        return m.group(1).strip()
    return None


def has_header_field(content: str, key: str) -> bool:
    return f"**{key}**" in content


def find_rust_version(content: str) -> str | None:
    """从文件头提取 Rust 版本。"""
    m = re.search(r"\*\*Rust 版本\*\*:\s*(\S+)", content)
    return m.group(1) if m else None


def find_layer(content: str) -> str | None:
    """从文件头提取层级。"""
    m = re.search(r"\*\*层级\*\*:\s*(L\d)", content)
    return m.group(1) if m else None


def generate_prerequisites_block(kg: dict, prereqs: dict[str, set[str]], entity_id: str) -> str:
    """生成前置概念链接块。"""
    deps = prereqs.get(entity_id, set())
    if not deps:
        return "N/A"
    parts = []
    for dep in sorted(deps):
        label = label_for(kg, dep, "en")
        parts.append(f"[{label}](./{path_for_entity(dep)})")
    return " · ".join(parts)


def generate_followups_block(kg: dict, followups: dict[str, set[str]], entity_id: str) -> str:
    """生成后置概念链接块。"""
    deps = followups.get(entity_id, set())
    if not deps:
        return "N/A"
    parts = []
    for dep in sorted(deps):
        label = label_for(kg, dep, "en")
        parts.append(f"[{label}](./{path_for_entity(dep)})")
    return " · ".join(parts)


def path_for_entity(entity_id: str) -> str:
    """从实体 ID 推断文件路径（简化版，实际需映射表）。"""
    name = entity_id.replace("ex:", "")
    return f"{name}.md"


def entity_id_from_path(path: Path) -> str | None:
    """从 concept 文件路径推断实体 ID（简化版）。"""
    # 读取文件头 EN 字段作为实体名
    try:
        content = path.read_text(encoding="utf-8")
        m = re.search(r"\*\*EN\*\*:\s*(.+?)(?:\n|\n>)", content)
        if m:
            en = m.group(1).strip()
            return f"ex:{en.replace(' ', '')}"
    except Exception:
        pass
    return None


def process_file(
    path: Path,
    kg: dict,
    prereqs: dict[str, set[str]],
    followups: dict[str, set[str]],
    glossary: dict[str, str],
    dry_run: bool,
) -> dict[str, str | bool]:
    """处理单个文件，返回变更报告。"""
    content = path.read_text(encoding="utf-8")
    changes: dict[str, str | bool] = {"path": str(path), "modified": False}

    title_zh = extract_chinese_title(content)
    if not title_zh:
        return changes

    entity_id = entity_id_from_path(path)

    # 生成 EN
    if not has_header_field(content, "EN"):
        title_en = translate_title(title_zh, glossary)
        changes["en_generated"] = title_en
    else:
        changes["en_existing"] = extract_existing_header_value(content, "EN")

    # 生成 Summary
    if not has_header_field(content, "Summary"):
        layer = find_layer(content)
        title_en = changes.get("en_generated") or changes.get("en_existing", translate_title(title_zh, glossary))
        summary = generate_summary(title_zh, str(title_en), layer)
        changes["summary_generated"] = summary

    # 生成 Prerequisites/Follow-ups
    if entity_id:
        if not has_header_field(content, "Prerequisites"):
            changes["prerequisites_generated"] = generate_prerequisites_block(kg, prereqs, entity_id)
        if not has_header_field(content, "Follow-ups"):
            changes["followups_generated"] = generate_followups_block(kg, followups, entity_id)

    if not dry_run and any(k.endswith("_generated") for k in changes):
        # 在文件头区域插入缺失字段
        new_content = inject_header_fields(content, changes)
        if new_content != content:
            path.write_text(new_content, encoding="utf-8")
            changes["modified"] = True

    return changes


def inject_header_fields(content: str, changes: dict[str, str | bool]) -> str:
    """在文件头中注入生成的字段。"""
    lines = content.splitlines(keepends=True)
    # 找到头部结束位置（第一个 --- 分隔线）
    header_end = -1
    for i, line in enumerate(lines):
        if line.strip() == "---" and i > 2:
            header_end = i
            break

    if header_end == -1:
        return content

    insertions = []
    if "en_generated" in changes:
        insertions.append(f"> **EN**: {changes['en_generated']}\n")
    if "summary_generated" in changes:
        insertions.append(f"> **Summary**: {changes['summary_generated']}\n")
    if "prerequisites_generated" in changes:
        insertions.append(f"> **Prerequisites**: {changes['prerequisites_generated']}\n")
    if "followups_generated" in changes:
        insertions.append(f"> **Follow-ups**: {changes['followups_generated']}\n")

    if not insertions:
        return content

    # 插入到 --- 之前
    new_lines = lines[:header_end] + insertions + lines[header_end:]
    return "".join(new_lines)


def iter_md_files(dirs: Iterable[Path]) -> Iterable[Path]:
    for directory in dirs:
        if directory.is_file() and directory.suffix == ".md":
            yield directory
            continue
        yield from sorted(directory.rglob("*.md"))


def main() -> int:
    parser = argparse.ArgumentParser(description="批量生成英文骨架元数据")
    parser.add_argument("--dir", nargs="+", type=Path, default=[Path("concept")], help="目标目录")
    parser.add_argument("--dry-run", action="store_true", help="只预览不修改")
    parser.add_argument("--output-report", type=Path, help="输出 JSON 报告")
    args = parser.parse_args()

    kg = load_kg(KG_PATH)
    prereqs, followups = build_dependency_maps(kg)
    glossary = load_glossary(TERM_GLOSSARY_PATH)

    reports = []
    for path in iter_md_files(args.dir):
        if "00_meta" in path.parts:
            continue
        report = process_file(path, kg, prereqs, followups, glossary, args.dry_run)
        reports.append(report)

    generated_count = sum(1 for r in reports if r.get("modified"))
    print(f"扫描文件数: {len(reports)}")
    print(f"生成/修改文件数: {generated_count}")

    if args.output_report:
        args.output_report.write_text(
            json.dumps(reports, ensure_ascii=False, indent=2),
            encoding="utf-8",
        )
        print(f"报告已保存: {args.output_report}")

    if args.dry_run:
        print("\n预览（前 5 个变更）:")
        for r in reports[:5]:
            if any(k.endswith("_generated") for k in r):
                print(f"  {r['path']}")
                for k, v in r.items():
                    if k.endswith("_generated"):
                        print(f"    {k}: {v}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
