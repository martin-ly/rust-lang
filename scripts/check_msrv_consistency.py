#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""check_msrv_consistency.py — MSRV 单一事实源一致性检查。

根 `Cargo.toml` 的 `[workspace.package] rust-version` 是项目 MSRV 的唯一事实源
（当前 1.97.0）。本脚本检查：

1. **Cargo.toml**：所有 workspace 成员 crate 的 `rust-version` 必须为
   `rust-version.workspace = true`（继承）或与根 MSRV 一致。
   豁免：根 `exclude` 列表中的路径（如嵌入式硬件 demo，独立工具链需求）、
   自带 `[workspace]` 的独立工作区（如 `examples/resolver_v3_practice`，
   其混合 MSRV 是 resolver v3 演示的有意设计）。
2. **Markdown**：活跃文档中“声明本项目/crate MSRV”的版本号必须与根一致。
   豁免：archive/ .kimi/ book/ tmp/ target/ vendor/ reports/ 目录、
   CHANGELOG.md（只增不改的历史记录）、文件名含 rust_1XX 或日期的历史快照、
   描述第三方 crate/上游项目 MSRV 的行（tokio/sqlx/Embassy/Rust for Linux 等）、
   以及带比较语义（MSRV < 1.96、>= 等）的通用建议。
   注意：“特性自某版本可用”属于特性版本而非 MSRV 声明，不匹配本脚本模式。
3. **.clippy.toml**：`msrv` 键必须与根一致。

用法：
    python scripts/check_msrv_consistency.py            # 默认 exit 0，打印报告
    python scripts/check_msrv_consistency.py --strict   # 存在不一致时 exit 1
"""

from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ROOT_CARGO = ROOT / "Cargo.toml"

EXCLUDE_DIRS = {".git", "archive", ".kimi", "book", "tmp", "target", "vendor", "node_modules"}
MD_EXCLUDE_DIRS = EXCLUDE_DIRS | {"reports"}
# 描述第三方/上游项目 MSRV 的行（非本项目 MSRV 声明）
THIRD_PARTY_HINTS = (
    "tokio", "sqlx", "seaorm", "sea orm", "embassy", "rust for linux", "debian",
    "ferrocene", "开源库", "库作者", "第三方", "third-party", "third party",
    "上游", "内核", "kernel", "dynosaur", "resolver", "embedded-hal", "embedded_hal",
    "示例值",
)

VER = r"(1\.\d+(?:\.\d+)?)"
# rust-version = "x" 仅在同行带 MSRV/最低 注释时视为声明（否则为教学示例）
RV_DECL = re.compile(rf"rust-version\s*=\s*\"{VER}\"[^\n]*(MSRV|最低)")
MD_PATTERNS = [
    RV_DECL,
    re.compile(rf"MSRV[^\d\n|<>]{{0,12}}{VER}"),
    re.compile(rf"{VER}\+?\s*MSRV"),
    re.compile(rf"最低[^\n]{{0,8}}Rust[^\n]{{0,6}}版本[^\d\n]{{0,8}}{VER}"),
    re.compile(rf"^\s*>?\s*(?:\*\*)?Rust\s*版本[：:][^\d\n]{{0,4}}{VER}"),
]
# 假设性的版本发布历史示例（v1.0.0 (MSRV 1.65) ✅ 不变）
RELEASE_HIST = re.compile(r"^\s*v?\d+\.\d+\.\d+\s*\(MSRV")


@dataclass
class Finding:
    level: str  # ERROR | WARN | INFO
    path: Path
    line: int
    detail: str


def parse_root() -> tuple[str, list[str]]:
    text = ROOT_CARGO.read_text(encoding="utf-8")
    m = re.search(r"\[workspace\.package\](.*?)(?=\n\[|\Z)", text, re.S)
    if not m:
        raise SystemExit("ERROR: 根 Cargo.toml 缺少 [workspace.package]")
    rv = re.search(r'rust-version\s*=\s*"([^"]+)"', m.group(1))
    if not rv:
        raise SystemExit("ERROR: 根 Cargo.toml 缺少 workspace.package.rust-version")
    ex = re.search(r"exclude\s*=\s*\[(.*?)\]", text, re.S)
    excludes = re.findall(r'"([^"]+)"', ex.group(1)) if ex else []
    return rv.group(1), excludes


def under(path: Path, prefix: str) -> bool:
    try:
        path.relative_to(ROOT / prefix)
        return True
    except ValueError:
        return False


def check_cargo_toml(msrv: str, excludes: list[str]) -> list[Finding]:
    findings: list[Finding] = []
    separate_workspaces: list[Path] = []
    for p in sorted(ROOT.rglob("Cargo.toml")):
        rel = p.relative_to(ROOT)
        if any(part in EXCLUDE_DIRS for part in rel.parts):
            continue
        if p == ROOT_CARGO:
            continue
        if any(under(p, ex) for ex in excludes):
            findings.append(Finding("INFO", p, 0, "workspace exclude 路径，独立工具链，豁免"))
            continue
        if any(p != ws and under(p, str(ws.parent.relative_to(ROOT))) for ws in separate_workspaces):
            continue
        text = p.read_text(encoding="utf-8")
        if re.search(r"^\[workspace\]", text, re.M):
            separate_workspaces.append(p)
            findings.append(Finding("INFO", p, 0, "独立 workspace（非根成员），其 MSRV 自行管理，豁免"))
            continue
        m = re.search(r"^\[package\](.*?)(?=^\[|\Z)", text, re.S | re.M)
        if not m:
            continue
        section = m.group(1)
        if re.search(r"rust-version\.workspace\s*=\s*true", section):
            continue  # 继承 workspace，OK
        rv = re.search(r'rust-version\s*=\s*"([^"]+)"', section)
        if rv:
            if rv.group(1) != msrv:
                line_no = text[: m.start() + section[: rv.start()].count("\n")].count("\n") + 1
                findings.append(Finding(
                    "ERROR", p, line_no,
                    f'rust-version = "{rv.group(1)}" 与根 MSRV {msrv} 不一致；'
                    f"应改为 rust-version.workspace = true 或 \"{msrv}\""))
        else:
            findings.append(Finding(
                "WARN", p, 0, "未声明 rust-version；建议 rust-version.workspace = true 继承"))
    return findings


def md_excluded(path: Path) -> bool:
    rel = path.relative_to(ROOT)
    if any(part in MD_EXCLUDE_DIRS for part in rel.parts):
        return True
    # resolver v3 演示工作区：混合 MSRV 是有意设计
    if under(path, "examples/resolver_v3_practice"):
        return True
    name = path.name.lower()
    if name == "changelog.md" or "link_check_report" in name:
        return True
    if re.search(r"rust_1\d\d", name) or re.search(r"\d{4}[-_]\d{2}", name) or re.search(r"_20\d{2}", name):
        return True
    return False


def check_markdown(msrv: str) -> list[Finding]:
    findings: list[Finding] = []
    for p in sorted(ROOT.rglob("*.md")):
        if md_excluded(p):
            continue
        for i, line in enumerate(p.read_text(encoding="utf-8", errors="replace").splitlines(), 1):
            stripped = line.strip()
            # 跳过标题/目录锚点行与假设性发布历史示例
            if stripped.startswith(("#", "- [", "* [")) or "](#" in line or RELEASE_HIST.match(stripped):
                continue
            low = line.lower()
            if any(h in low for h in THIRD_PARTY_HINTS):
                continue
            for pat in MD_PATTERNS:
                for m in pat.finditer(line):
                    ver = m.group(1)
                    # 带比较语义（MSRV < 1.96 / >= 1.96）属通用建议而非声明
                    span = line[max(0, m.start() - 6): m.end() + 2]
                    if any(op in span for op in ("<", ">", "≥", "≤")):
                        continue
                    if ver != msrv:
                        findings.append(Finding(
                            "ERROR", p, i,
                            f"MSRV 声明版本 {ver} 与根 MSRV {msrv} 不一致: {line.strip()[:100]}"))
                    break  # 同一行同一模式只报一次
    return findings


def check_clippy(msrv: str) -> list[Finding]:
    p = ROOT / ".clippy.toml"
    if not p.exists():
        return []
    for i, line in enumerate(p.read_text(encoding="utf-8").splitlines(), 1):
        m = re.match(r'\s*msrv\s*=\s*"([^"]+)"', line)
        if m and m.group(1) != msrv:
            return [Finding("ERROR", p, i, f'.clippy.toml msrv = "{m.group(1)}" ≠ 根 MSRV {msrv}')]
    return []


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--strict", action="store_true", help="存在 ERROR 级不一致时 exit 1")
    args = ap.parse_args()

    msrv, excludes = parse_root()
    findings = check_cargo_toml(msrv, excludes) + check_markdown(msrv) + check_clippy(msrv)

    errors = [f for f in findings if f.level == "ERROR"]
    warns = [f for f in findings if f.level == "WARN"]
    infos = [f for f in findings if f.level == "INFO"]

    print("=" * 72)
    print("MSRV 一致性检查报告 (check_msrv_consistency.py)")
    print("=" * 72)
    print(f"唯一事实源: Cargo.toml [workspace.package] rust-version = \"{msrv}\"")
    print()
    for f in findings:
        loc = f"{f.path.relative_to(ROOT)}:{f.line}" if f.line else str(f.path.relative_to(ROOT))
        print(f"[{f.level}] {loc}")
        if f.detail:
            print(f"    {f.detail}")
    print()
    print(f"合计: ERROR={len(errors)}  WARN={len(warns)}  INFO(豁免)={len(infos)}")

    if args.strict and errors:
        print("--strict: 存在 MSRV 不一致，exit 1")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
