#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""apply_version_semantic_injection.py — 批量注入 Rust 版本特性 ↔ concept/ 权威页双向链接。

读取 `concept/07_future/00_version_tracking/rust_1_9[0-7]_stabilized.md`
中的特性矩阵，为未映射特性补全前向链接，并在对应 concept/ 权威页追加
"版本兼容性 / Version Compatibility" 小节。

本脚本为一次性/可重复执行工具；映射表硬编码在 FEATURE_MAP 中。
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
VERSION_DIR = ROOT / "concept" / "07_future" / "00_version_tracking"
CONCEPT_DIR = ROOT / "concept"


def normalize_feature(text: str) -> str:
    text = re.sub(r"`+", "", text)
    text = re.sub(r"\[([^\]]+)\]\([^)]+\)", r"\1", text)
    text = re.sub(r"\*+", "", text)
    text = re.sub(r"\s*[（(]§[^）)]+[）)]\s*$", "", text)
    text = re.sub(r"[§0-9.\-/_]", "", text)
    text = re.sub(r"\s+", "", text)
    return text.strip().lower()


# Mapping: (version, normalized_feature) -> list of concept/ relative paths
FEATURE_MAP: dict[tuple[str, str], list[str]] = {
    # 1.90
    ("1.90", normalize_feature("x86_64-unknown-linux-gnu 默认使用 lld 链接器")): ["03_advanced/04_ffi/03_linkage.md"],
    ("1.90", normalize_feature("CStr / CString / Cow<CStr> 互比")): ["03_advanced/04_ffi/01_rust_ffi.md"],
    ("1.90", normalize_feature("f32/f64 floor/ceil/trunc/fract/round/round_ties_even 进入 const")): ["01_foundation/02_type_system/03_numerics.md"],
    ("1.90", normalize_feature("Cargo 多包发布稳定（multi-package publishing）")): ["06_ecosystem/01_cargo/19_cargo_commands_reference.md"],
    ("1.90", normalize_feature("x86_64-apple-darwin 降为 Tier 2（含 host tools）")): ["06_ecosystem/05_systems_and_embedded/10_target_tier_platform_support.md"],
    # 1.91
    ("1.91", normalize_feature("C 风格可变参数函数稳定（sysv64/win64/efiapi/aapcs ABI）")): ["03_advanced/04_ffi/01_rust_ffi.md"],
    ("1.91", normalize_feature("dangling_pointers_from_locals lint")): ["03_advanced/02_unsafe/01_unsafe.md"],
    ("1.91", normalize_feature("{integer}::strict_* 系列方法")): ["01_foundation/02_type_system/03_numerics.md"],
    ("1.91", normalize_feature("AtomicPtr::fetch_ptr_add/sub、fetch_or/and/xor")): ["03_advanced/00_concurrency/06_atomics_and_memory_ordering.md"],
    ("1.91", normalize_feature("Cargo build.build-dir 稳定")): ["06_ecosystem/01_cargo/18_cargo_configuration.md"],
    ("1.91", normalize_feature("内部升级 LLVM 21")): ["06_ecosystem/00_toolchain/09_llvm_backend_and_codegen.md"],
    # 1.92
    ("1.92", normalize_feature("MaybeUninit 表示与有效性正式文档化")): ["03_advanced/02_unsafe/01_unsafe.md"],
    ("1.92", normalize_feature("安全代码允许对联合体字段取 &raw const/mut")): ["03_advanced/02_unsafe/01_unsafe.md"],
    ("1.92", normalize_feature("同一关联项允许多个边界（trait 对象除外）")): ["02_intermediate/00_traits/01_traits.md"],
    ("1.92", normalize_feature("iter::Repeat::last/count 改为 panic（兼容性变更）")): ["02_intermediate/07_iterators_and_closures/01_iterator_patterns.md"],
    ("1.92", normalize_feature("Location::file_as_c_str")): ["02_intermediate/03_error_handling/03_panic.md"],
    # 1.93
    ("1.93", normalize_feature("asm_cfg 稳定")): ["03_advanced/05_inline_assembly/01_inline_assembly.md"],
    ("1.93", normalize_feature("system ABI C 风格可变参数函数稳定")): ["03_advanced/04_ffi/01_rust_ffi.md"],
    ("1.93", normalize_feature("MaybeUninit 切片 API（assume_init_ref/mut、write_copy/clone_of_slice、assume_init_drop）")): ["03_advanced/02_unsafe/01_unsafe.md"],
    ("1.93", normalize_feature("<[T]>::as_array / as_mut_array")): ["01_foundation/05_collections/01_collections.md"],
    ("1.93", normalize_feature("fmt::from_fn / fmt::FromFn")): ["01_foundation/06_strings_and_text/03_formatting_and_display.md"],
    ("1.93", normalize_feature("-Cjump-tables 稳定（原 -Zno-jump-tables）")): ["06_ecosystem/00_toolchain/01_toolchain.md"],
    ("1.93", normalize_feature("cargo clean --workspace")): ["06_ecosystem/01_cargo/19_cargo_commands_reference.md"],
    # 1.94
    ("1.94", normalize_feature("29 个 RISC-V target feature 稳定（含 RVA22U64 / RVA23U64 profile 大部）")): ["06_ecosystem/05_systems_and_embedded/10_target_tier_platform_support.md"],
    ("1.94", normalize_feature("LazyCell / LazyLock::get / get_mut / force_mut")): ["02_intermediate/02_memory_management/02_interior_mutability.md"],
    ("1.94", normalize_feature("f32 / f64::mul_add")): ["01_foundation/02_type_system/03_numerics.md"],
    ("1.94", normalize_feature("EULER_GAMMA / GOLDEN_RATIO 浮点常量")): ["01_foundation/02_type_system/03_numerics.md"],
    ("1.94", normalize_feature("Cargo include 配置键稳定 + TOML v1.1 解析")): ["06_ecosystem/01_cargo/18_cargo_configuration.md"],
    ("1.94", normalize_feature("std 宏改为经 prelude 导入（兼容性变更）")): ["01_foundation/07_modules_and_items/10_preludes.md", "01_foundation/09_macros_basics/01_attributes_and_macros.md"],
    # 1.95
    ("1.95", normalize_feature("if let guards on match arms")): ["01_foundation/04_control_flow/01_control_flow.md"],
    ("1.95", normalize_feature("Vec::push_mut 等可变引用插入")): ["01_foundation/05_collections/01_collections.md"],
    ("1.95", normalize_feature("--remap-path-scope 稳定")): ["03_advanced/04_ffi/03_linkage.md"],
    # 1.96
    ("1.96", normalize_feature("expr metavariable 传入 cfg")): ["03_advanced/03_proc_macros/01_macros.md"],
    ("1.96", normalize_feature("core::range Copy 类型")): ["02_intermediate/07_iterators_and_closures/01_iterator_patterns.md"],
    ("1.96", normalize_feature("From<T> for AssertUnwindSafe / LazyCell / LazyLock")): ["02_intermediate/02_memory_management/02_interior_mutability.md"],
    ("1.96", normalize_feature("Cargo git + alternate registry 共存；CVE-2026-5222/5223 修复")): ["06_ecosystem/01_cargo/06_cargo_dependency_resolution.md"],
    # 1.97
    ("1.97", normalize_feature("must_use lint 扩展至 Result<T, Uninhabited> 与 ControlFlow<Uninhabited, T>")): ["01_foundation/04_control_flow/01_control_flow.md"],
    ("1.97", normalize_feature("dead_code_pub_in_binary lint")): ["06_ecosystem/00_toolchain/01_toolchain.md"],
    ("1.97", normalize_feature("新稳定 target features")): ["03_advanced/00_concurrency/06_atomics_and_memory_ordering.md"],
    ("1.97", normalize_feature("cfg(target_has_atomic_primitive_alignment)")): ["03_advanced/00_concurrency/06_atomics_and_memory_ordering.md"],
    ("1.97", normalize_feature("import 中 self 的放宽")): ["01_foundation/07_modules_and_items/11_crates_and_source_files.md"],
    ("1.97", normalize_feature("{float} 在未约束时回退到 f32")): ["01_foundation/02_type_system/03_numerics.md"],
    ("1.97", normalize_feature("nvptx64-nvidia-cuda 基线提升")): ["06_ecosystem/05_systems_and_embedded/10_target_tier_platform_support.md"],
    ("1.97", normalize_feature("Default for RepeatN")): ["02_intermediate/07_iterators_and_closures/01_iterator_patterns.md"],
    ("1.97", normalize_feature("Copy for ffi::FromBytesUntilNulError")): ["03_advanced/04_ffi/01_rust_ffi.md"],
    ("1.97", normalize_feature("Send for std::fs::File on UEFI")): ["06_ecosystem/05_systems_and_embedded/03_embedded_systems.md"],
    ("1.97", normalize_feature("整数位查询方法")): ["01_foundation/02_type_system/03_numerics.md"],
    ("1.97", normalize_feature("NonZero 位查询方法")): ["01_foundation/02_type_system/03_numerics.md"],
    ("1.97", normalize_feature("char::is_control 在 const 上下文稳定")): ["01_foundation/06_strings_and_text/01_strings_and_text.md"],
    ("1.97", normalize_feature("-m 简写")): ["06_ecosystem/01_cargo/19_cargo_commands_reference.md"],
    ("1.97", normalize_feature("--emit 标志")): ["06_ecosystem/00_toolchain/07_rustdoc_196_changes.md"],
}


def extract_matrix_rows(version: str, filename: str) -> tuple[list[dict], str]:
    path = VERSION_DIR / filename
    text = path.read_text(encoding="utf-8")
    lines = text.splitlines()
    rows: list[dict] = []
    in_matrix = False

    for i, line in enumerate(lines):
        stripped = line.strip()
        if "| 特性 " in stripped and "影响面" in stripped:
            in_matrix = True
            continue
        if in_matrix:
            if not stripped.startswith("|"):
                break
            if stripped.replace("|", "").strip().startswith("-"):
                continue
            cells = [c.strip() for c in stripped.strip("|").split("|")]
            if len(cells) < 4:
                continue
            feature = cells[0]
            if not feature or feature == "特性" or set(feature) <= {"-", "|", ":"}:
                continue
            rows.append({
                "line_no": i,
                "line": line,
                "cells": cells,
                "feature": feature,
                "norm": normalize_feature(feature),
            })

    return rows, text


def extract_section_features(version: str, filename: str, text: str) -> list[dict]:
    """Extract numbered section headings as features (used for e.g. 1.97)."""
    heading_re = re.compile(r"^(#{1,4})\s+(\d+(?:\.\d+)+)\s+(.+?)$", re.MULTILINE)
    features: list[dict] = []
    for m in heading_re.finditer(text):
        section = m.group(2)
        title = m.group(3).strip()
        if not title:
            continue
        if any(k in title for k in ["权威来源", "国际权威参考", "迁移指南", "兼容性注意", "练习与验证"]):
            continue
        features.append({
            "line_no": m.start(),
            "section": section,
            "feature": title,
            "norm": normalize_feature(title),
            "level": len(m.group(1)),
        })
    return features


def update_version_page(version: str, filename: str, dry_run: bool = False) -> int:
    path = VERSION_DIR / filename
    text = path.read_text(encoding="utf-8")
    lines = text.splitlines()
    updated = 0

    rows, _ = extract_matrix_rows(version, filename)
    if rows:
        for row in rows:
            key = (version, row["norm"])
            if key not in FEATURE_MAP:
                continue
            # Already has concept links?
            if re.search(r"\[.*?\]\((?:\.\.?/)*concept/", row["line"]):
                continue
            targets = FEATURE_MAP[key]
            links = " · ".join(
                f"[{path_to_label(p)}](../../{path_to_relative(p, version)})" for p in targets
            )
            # Append to the authority column (4th cell)
            cells = row["cells"]
            authority = cells[3]
            if authority and not authority.endswith(" "):
                authority += " "
            authority += "· " + links
            cells[3] = authority
            new_line = "| " + " | ".join(cells) + " |"
            lines[row["line_no"]] = new_line
            updated += 1
    else:
        # Section-based page (e.g. 1.97): insert concept links after headings
        sections = extract_section_features(version, filename, text)
        for sec in sections:
            key = (version, sec["norm"])
            if key not in FEATURE_MAP:
                continue
            targets = FEATURE_MAP[key]
            links = " · ".join(
                f"[{path_to_label(p)}](../../{path_to_relative(p, version)})" for p in targets
            )
            # Find heading line
            heading_line = f"{'#' * (sec.get('level', 3))} {sec['section']} {sec['feature']}"
            # Insert a link line after the heading
            for i, line in enumerate(lines):
                if line.strip().startswith(f"{'#' * (sec.get('level', 3))} {sec['section']} "):
                    insert_text = f"> **相关概念**: {links}"
                    if i + 1 < len(lines) and lines[i + 1].strip() == "":
                        lines[i + 1] = insert_text
                    else:
                        lines.insert(i + 1, insert_text)
                        # adjust subsequent line numbers not needed for full rewrite
                    updated += 1
                    break

    if updated and not dry_run:
        path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return updated


def path_to_label(rel_path: str) -> str:
    """Generate a short label from concept path."""
    name = Path(rel_path).stem
    name = name.replace("_", " ")
    # Title-case-ish
    return name[:40] + "…" if len(name) > 40 else name


def path_to_relative(rel_path: str, version: str) -> str:
    """Return the concept-relative path; callers prepend ../../ from version tracking page."""
    return rel_path.replace("\\", "/")


def apply_concept_sections(dry_run: bool = False) -> int:
    """Append Version Compatibility sections to concept pages that receive new mappings."""
    # Invert mapping: concept path -> list of (version, feature)
    concept_features: dict[str, list[tuple[str, str]]] = {}
    for (version, _), targets in FEATURE_MAP.items():
        for t in targets:
            concept_features.setdefault(t, [])

    # Re-run extraction to get actual feature names
    for version, filename in [
        ("1.90", "rust_1_90_stabilized.md"),
        ("1.91", "rust_1_91_stabilized.md"),
        ("1.92", "rust_1_92_stabilized.md"),
        ("1.93", "rust_1_93_stabilized.md"),
        ("1.94", "rust_1_94_stabilized.md"),
        ("1.95", "rust_1_95_stabilized.md"),
        ("1.96", "rust_1_96_stabilized.md"),
        ("1.97", "rust_1_97_stabilized.md"),
    ]:
        path = VERSION_DIR / filename
        text = path.read_text(encoding="utf-8")
        rows, _ = extract_matrix_rows(version, filename)
        source_rows = rows if rows else extract_section_features(version, filename, text)
        for row in source_rows:
            key = (version, row["norm"])
            if key in FEATURE_MAP:
                for t in FEATURE_MAP[key]:
                    concept_features[t].append((version, row["feature"]))

    updated = 0
    for rel_path, feats in concept_features.items():
        path = CONCEPT_DIR / rel_path
        if not path.exists():
            print(f"⚠️ concept page missing: {rel_path}", file=sys.stderr)
            continue
        text = path.read_text(encoding="utf-8")
        if "版本兼容性" in text or "Version Compatibility" in text:
            # Already has a section; skip to avoid duplication
            continue
        section = build_version_compatibility_section(feats, rel_path)
        new_text = insert_section(text, section)
        if new_text != text and not dry_run:
            path.write_text(new_text, encoding="utf-8")
            updated += 1
        elif new_text != text:
            updated += 1

    return updated


def build_version_compatibility_section(feats: list[tuple[str, str]], rel_path: str) -> str:
    version_link = "../../07_future/00_version_tracking/rust_{}_{}_stabilized.md"
    lines = [
        "",
        "## 版本兼容性 / Version Compatibility",
        "",
        "> 本节汇总与本概念相关的 Rust 稳定版本变更。完整列表见对应版本跟踪页。",
        "",
    ]
    grouped: dict[str, list[str]] = {}
    for version, feature in feats:
        grouped.setdefault(version, []).append(feature)
    for version in sorted(grouped):
        major, minor = version.split(".")
        link = version_link.format(major, minor.zfill(2))
        lines.append(f"- **[Rust {version}]({link})**")
        for feature in grouped[version]:
            lines.append(f"  - {feature}")
    lines.append("")
    lines.append("")
    return "\n".join(lines)


def insert_section(text: str, section: str) -> str:
    """Insert the section before a suitable end marker, or append at the end."""
    # Try to insert before common end markers
    markers = [
        "## 来源与延伸阅读",
        "## 国际权威参考",
        "## 相关概念",
        "## 判定表",
        "## 认知路径",
        "## 实践",
        "## 权威来源索引",
    ]
    for marker in markers:
        idx = text.find(marker)
        if idx != -1:
            return text[:idx] + section + text[idx:]
    return text.rstrip() + "\n" + section


def main() -> int:
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true", help="只打印，不写文件")
    args = ap.parse_args()

    total_updated_rows = 0
    for version, filename in [
        ("1.90", "rust_1_90_stabilized.md"),
        ("1.91", "rust_1_91_stabilized.md"),
        ("1.92", "rust_1_92_stabilized.md"),
        ("1.93", "rust_1_93_stabilized.md"),
        ("1.94", "rust_1_94_stabilized.md"),
        ("1.95", "rust_1_95_stabilized.md"),
        ("1.96", "rust_1_96_stabilized.md"),
        ("1.97", "rust_1_97_stabilized.md"),
    ]:
        n = update_version_page(version, filename, dry_run=args.dry_run)
        print(f"{version}: updated {n} feature rows")
        total_updated_rows += n

    concept_updated = apply_concept_sections(dry_run=args.dry_run)
    print(f"concept pages updated: {concept_updated}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
