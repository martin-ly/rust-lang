#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""check_authority_freshness.py — 权威源新鲜度周期巡检（手动巡检工具，非 CI 质量门）。

> 定位：P5 治理机制收尾。一条命令可跑的轻量周期巡检，**不挂质量门**
> （网络依赖门不适合 CI 阻断）。登记于 AGENTS.md §7 治理机制表（每周）。

检查项：

1. **权威源类别扫描（离线，纯统计）**：扫描 `concept/` 各页引用的已知权威源域名
   （releases.rs、blog.rust-lang.org、RFC repo/book、Reference/Nomicon、Ferrocene 等），
   输出各类别引用计数，供人工判断引用面是否健康。
2. **上游 stable 版本比对（在线，优雅降级）**：拉取
   `blog.rust-lang.org/releases.json`（失败回退 releases.rs），解析上游最高 stable
   版本，与库内最高稳定版（根 `Cargo.toml` `rust-version`，当前 1.97.0）比较；
   上游更新 → WARN（提示应启动新版本页）。**网络不可达时优雅降级：打印 WARN，
   exit 0（`--strict` 下网络降级同样 exit 0，不因离线失败）。**
3. **beta→stable 迁移到期检查（离线）**：解析
   `concept/07_future/00_version_tracking/rust_1_98_preview.md` 跟踪清单中标记
   `stabilized in 1.98 beta`（亦兼容 `stabilized-in-beta` 写法）的条目，与对应稳定日
   （1.98.0 = 2026-08-20，优先取页内「预计稳定时间」元数据，回退内置表）比较；
   当前日期 ≥ 稳定日且条目仍滞留 preview 页（未迁移到 `rust_1_98_stabilized.md`）
   → WARN。

用法：
    python scripts/check_authority_freshness.py            # 默认观察，exit 0
    python scripts/check_authority_freshness.py --strict   # 存在可处置 WARN 时 exit 1
    python scripts/check_authority_freshness.py --offline  # 跳过全部网络检查
"""

from __future__ import annotations

import argparse
import json
import re
import sys
import urllib.error
import urllib.request
from dataclasses import dataclass, field
from datetime import date, datetime
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CONCEPT = ROOT / "concept"
ROOT_CARGO = ROOT / "Cargo.toml"
PREVIEW_198 = CONCEPT / "07_future" / "00_version_tracking" / "rust_1_98_preview.md"

# 已知权威源域名清单（类别 → 域名/关键字）
AUTHORITY_DOMAINS: dict[str, tuple[str, ...]] = {
    "release notes (releases.rs)": ("releases.rs",),
    "rust-lang blog": ("blog.rust-lang.org",),
    "RFC repo / RFC book": ("github.com/rust-lang/rfcs", "rust-lang.github.io/rfcs"),
    "Reference / Nomicon": ("doc.rust-lang.org/reference", "doc.rust-lang.org/nomicon"),
    "TRPL / std docs": ("doc.rust-lang.org/book", "doc.rust-lang.org/std"),
    "Ferrocene": ("ferrocene.dev", "spec.ferrocene.dev"),
    "Project Goals": ("rust-lang.github.io/rust-project-goals",),
    "Inside Rust / internals": ("blog.rust-lang.org/inside-rust", "internals.rust-lang.org"),
}

# 上游 stable 版本来源（按优先级尝试）
RELEASES_JSON_URL = "https://blog.rust-lang.org/releases.json"
RELEASES_RS_URL = "https://releases.rs/"
HTTP_TIMEOUT = 8

# beta→stable 稳定日回退表（页内元数据解析失败时使用）
KNOWN_STABLE_DATES = {"1.98": date(2026, 8, 20)}


@dataclass
class Report:
    warnings: list[str] = field(default_factory=list)
    infos: list[str] = field(default_factory=list)
    # 网络降级 WARN 不计入 --strict 判定（离线不能成为失败理由）
    network_degraded: bool = False

    def warn(self, msg: str) -> None:
        self.warnings.append(msg)
        print(f"[WARN] {msg}")

    def info(self, msg: str) -> None:
        self.infos.append(msg)
        print(f"[INFO] {msg}")


def scan_authority_domains(rep: Report) -> dict[str, int]:
    """离线扫描 concept/ 中各权威源类别的引用计数。"""
    counts = {cat: 0 for cat in AUTHORITY_DOMAINS}
    if not CONCEPT.is_dir():
        rep.warn(f"concept/ 目录不存在: {CONCEPT}")
        return counts
    for md in sorted(CONCEPT.rglob("*.md")):
        try:
            text = md.read_text(encoding="utf-8", errors="replace").lower()
        except OSError:
            continue
        for cat, domains in AUTHORITY_DOMAINS.items():
            if any(d in text for d in domains):
                counts[cat] += 1
    print("\n== 检查 1：concept/ 权威源类别引用扫描（离线统计） ==")
    for cat, n in counts.items():
        rep.info(f"{cat}: {n} 页引用")
    zero = [c for c, n in counts.items() if n == 0]
    if zero:
        rep.warn(f"以下权威源类别在 concept/ 中零引用（请人工确认是否预期）: {', '.join(zero)}")
    return counts


def repo_max_stable() -> str | None:
    """库内最高稳定版 = 根 Cargo.toml workspace rust-version（单一事实源）。"""
    try:
        text = ROOT_CARGO.read_text(encoding="utf-8")
    except OSError:
        return None
    m = re.search(r'rust-version\s*=\s*"(\d+\.\d+(?:\.\d+)?)"', text)
    return m.group(1) if m else None


def fetch_url(url: str) -> str | None:
    req = urllib.request.Request(url, headers={"User-Agent": "rust-lang-kb-freshness-check/1.0"})
    try:
        with urllib.request.urlopen(req, timeout=HTTP_TIMEOUT) as resp:
            return resp.read().decode("utf-8", errors="replace")
    except (urllib.error.URLError, OSError, ValueError):
        pass
    # 回退：curl（部分 Windows 环境下 urllib 无代理配置而 curl 可用）
    try:
        import subprocess

        out = subprocess.run(
            ["curl", "-sS", "-m", str(HTTP_TIMEOUT), url],
            capture_output=True, text=True, timeout=HTTP_TIMEOUT + 5,
        )
        if out.returncode == 0 and out.stdout:
            return out.stdout
    except (OSError, subprocess.SubprocessError):
        pass
    return None


def upstream_max_stable(rep: Report) -> str | None:
    """解析上游最高 stable 版本；网络不可达返回 None（优雅降级）。"""
    body = fetch_url(RELEASES_JSON_URL)
    if body:
        try:
            data = json.loads(body)
            items = data if isinstance(data, list) else data.get("releases", [])
            vers = []
            for item in items:
                # releases.json 形如 {"title": "Announcing Rust 1.97.0", "url": ...}
                text = " ".join(str(item.get(k, "")) for k in ("version", "title", "url"))
                m = re.search(r"(\d+\.\d+\.\d+)", text)
                if m:
                    vers.append(m.group(1))
            if vers:
                return max(vers, key=lambda v: tuple(int(x) for x in v.split(".")))
        except (json.JSONDecodeError, AttributeError, TypeError):
            pass
    body = fetch_url(RELEASES_RS_URL)
    if body:
        vers = re.findall(r"1\.(\d+)\.0", body)
        if vers:
            minor = max(int(x) for x in vers)
            return f"1.{minor}.0"
    return None


def check_upstream_version(rep: Report, offline: bool) -> None:
    print("\n== 检查 2：上游 stable 版本比对 ==")
    local = repo_max_stable()
    rep.info(f"库内最高稳定版（根 Cargo.toml rust-version）: {local or '未解析'}")
    if offline:
        rep.info("--offline：跳过网络检查")
        return
    upstream = upstream_max_stable(rep)
    if upstream is None:
        rep.network_degraded = True
        rep.warn("网络不可达或上游页面解析失败（releases.json / releases.rs 均不可用）；"
                 "优雅降级：本次跳过版本比对，exit 0")
        return
    rep.info(f"上游最高 stable 版本: {upstream}")

    def key(v: str) -> tuple[int, ...]:
        return tuple(int(x) for x in v.split(".")[:3])

    if local and key(upstream) > key(local):
        rep.warn(f"上游 stable {upstream} 已高于库内基线 {local}："
                 f"应启动 rust_1_{upstream.split('.')[1]} 版本页与 MSRV 评估（check_msrv_consistency.py）")
    else:
        rep.info("上游 stable 未超过库内基线，无需动作")


def check_beta_migration(rep: Report) -> None:
    """检查 preview 页中 stabilized-in-beta 条目是否已过稳定日仍未迁移。"""
    print("\n== 检查 3：beta→stable 迁移到期检查 ==")
    if not PREVIEW_198.is_file():
        rep.info(f"preview 页不存在（{PREVIEW_198.relative_to(ROOT)}），跳过")
        return
    text = PREVIEW_198.read_text(encoding="utf-8", errors="replace")
    # 标记兼容：stabilized in 1.98 beta / stabilized-in-beta
    stabilized_rows = re.findall(r"stabilized[\s-]+in[\s-]+1\.98[\s-]+beta|stabilized-in-beta",
                                 text, re.I)
    if not stabilized_rows:
        rep.info("跟踪清单中无 stabilized-in-beta 条目，无需迁移检查")
        return
    rep.info(f"跟踪清单中 stabilized-in-beta 条目: {len(stabilized_rows)} 处")

    # 稳定日：优先页内「预计稳定时间」元数据，回退内置表
    m = re.search(r"1\.98\.0\s*=\s*(\d{4})-(\d{2})-(\d{2})", text)
    if m:
        stable_date = date(int(m.group(1)), int(m.group(2)), int(m.group(3)))
        rep.info(f"1.98.0 稳定日（页内元数据）: {stable_date.isoformat()}")
    else:
        stable_date = KNOWN_STABLE_DATES["1.98"]
        rep.info(f"1.98.0 稳定日（内置回退表）: {stable_date.isoformat()}")

    today = date.today()
    stabilized_page = PREVIEW_198.parent / "rust_1_98_stabilized.md"
    if today >= stable_date:
        if stabilized_page.is_file():
            rep.warn(f"已过 1.98.0 稳定日（{stable_date}）且 rust_1_98_stabilized.md 已建立，"
                     f"但 preview 页仍滞留 {len(stabilized_rows)} 处 stabilized-in-beta 条目："
                     f"请将 beta 行迁移至 stabilized 页，preview 页滚动为 1.99+ 跟踪")
        else:
            rep.warn(f"已过 1.98.0 稳定日（{stable_date}），preview 页仍滞留 "
                     f"{len(stabilized_rows)} 处 stabilized-in-beta 条目且 "
                     f"rust_1_98_stabilized.md 尚未建立：请新建 stabilized 页并完成迁移")
    else:
        days = (stable_date - today).days
        rep.info(f"距 1.98.0 稳定日还有 {days} 天，暂无迁移到期项")


def main() -> int:
    ap = argparse.ArgumentParser(description="权威源新鲜度周期巡检（手动巡检工具，非 CI 门）")
    ap.add_argument("--strict", action="store_true", help="存在可处置 WARN 时 exit 1（网络降级除外）")
    ap.add_argument("--offline", action="store_true", help="跳过全部网络检查")
    args = ap.parse_args()

    rep = Report()
    print(f"# 权威源新鲜度巡检 — {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    scan_authority_domains(rep)
    check_upstream_version(rep, args.offline)
    check_beta_migration(rep)

    print("\n== 汇总 ==")
    actionable = len(rep.warnings) - (1 if rep.network_degraded else 0)
    print(f"WARN {len(rep.warnings)}（其中网络降级 {1 if rep.network_degraded else 0}）/ INFO {len(rep.infos)}")
    if args.strict and actionable > 0:
        print("STRICT: 存在可处置 WARN → exit 1")
        return 1
    print("OBSERVE: exit 0")
    return 0


if __name__ == "__main__":
    sys.exit(main())
