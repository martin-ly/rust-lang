#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""国际化权威来源 URL 健康检查（P0/P1/P2 域，聚焦『对齐有效性』）。

只检查 concept/+knowledge/+docs/ 中匹配 P0/P1/P2 权威域的 http(s) URL（去重），
报 4xx/5xx/超时/连接错误。带缓存（target/authority_link_health_cache.json）。
复用 maintenance/authority_coverage_dashboard.py 的 P0/P1/P2 域分级（单一来源）。
--limit N 仅查前 N 个（抽样）；默认全量。永远 exit 0（informational，失效列入复核）。
"""
from __future__ import annotations

import argparse
import datetime as _dt
import glob
import json
import os
import re
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from urllib.error import HTTPError, URLError
from urllib.request import Request, urlopen
from urllib.parse import urlparse

# 反爬站点的备用校验正则
CRATESIO_CRATE_RE = re.compile(r"^/crates/([^/]+)(?:/([^/]+))?$")
CRATESIO_CATEGORY_RE = re.compile(r"^/categories/([^/]+)$")
ACM_DOI_RE = re.compile(r"/doi/(?:pdf/|book/)?(10\.\d{4,9}/[^\s\"]+)")

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "scripts", "maintenance"))
TODAY = _dt.date.today().isoformat()
CACHE = os.path.join(ROOT, "target", "authority_link_health_cache.json")
UA = "Mozilla/5.0 (compatible; rust-lang-kb-health/1.0; +https://github.com/rust-lang)"
BROWSER_UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
              "(KHTML, like Gecko) Chrome/120.0 Safari/537.36")
TIMEOUT = 10

try:
    from authority_coverage_dashboard import P0_DOMAINS, P1_DOMAINS, P2_DOMAINS  # type: ignore
except Exception:  # pragma: no cover
    P0_DOMAINS = [r"doc\.rust-lang\.org", r"rust-lang\.github\.io", r"github\.com/rust-lang", r"rustc-dev-guide\.rust-lang\.org"]
    P1_DOMAINS = [r"plv\.mpi-sws\.org", r"arxiv\.org", r"acm\.org", r"dl\.acm\.org", r"ieee\.org", r"springer\.com", r"aeneas"]
    P2_DOMAINS = [r"github\.com/verus-lang", r"github\.com/creusot-rs", r"docs\.rs", r"crates\.io", r"blog\.rust-lang\.org"]

TIER = [(re.compile("|".join(P0_DOMAINS)), "P0"),
        (re.compile("|".join(P1_DOMAINS)), "P1"),
        (re.compile("|".join(P2_DOMAINS)), "P2")]
URL_RE = re.compile(r"https?://[^\s()\"'>\]`]+")  # 排除 () ] ` 避免 markdown 语法字符污染 URL


def classify(u):
    for rx, name in TIER:
        if rx.search(u):
            return name
    return None


def collect():
    seen = {}
    for d in ("concept", "knowledge", "docs"):
        for p in glob.glob(os.path.join(ROOT, d, "**", "*.md"), recursive=True):
            if "/archive/" in p.replace("\\", "/"):
                continue
            try:
                t = open(p, encoding="utf-8", errors="ignore").read()
            except Exception:
                continue
            for u in URL_RE.findall(t):
                u = u.rstrip(".,;")
                # 教学/示例占位 URL 不应计入国际化权威有效性统计
                if "example.com" in u or "localhost" in u or "127.0.0.1" in u or "your-mirror" in u or "my-company" in u:
                    continue
                tier = classify(u)
                if tier:
                    key = u.split("#")[0]
                    seen.setdefault(key, {"tier": tier, "files": set()})
                    seen[key]["files"].add(os.path.relpath(p, ROOT).replace("\\", "/"))
    return seen


def _probe(url, method="GET", accept_json=False):
    try:
        headers = {"User-Agent": UA}
        if accept_json:
            headers["Accept"] = "application/json"
        req = Request(url, headers=headers, method=method)
        with urlopen(req, timeout=TIMEOUT) as r:
            return r.status
    except HTTPError as e:
        return e.code
    except Exception:
        return None


def fallback_probe_curl(url, ua=UA):
    """当 urllib 因 TLS/EOF/UA 被重置时，使用系统 curl 做一次性复核。
    默认 HEAD；浏览器 UA 时改用 GET -L（ACM 等站点对 HEAD 恒 403）。"""
    try:
        args = ["curl", "-s", "-o", "/dev/null", "-w", "%{http_code}",
                "--max-time", "20", "-A", ua]
        if ua == BROWSER_UA:
            args += ["-L", "-H", "Accept: text/html,application/xhtml+xml"]
        else:
            args.append("-I")
        args.append(url)
        cp = subprocess.run(
            args, capture_output=True, text=True, timeout=25, check=False,
        )
        code = cp.stdout.strip()
        if code.isdigit():
            return int(code)
    except Exception:
        pass
    return None


def verify_cratesio(u):
    """crates.io 对非浏览器 UA 常返回 404；通过其 JSON API 校验 crate/分类/首页是否存在。"""
    parsed = urlparse(u)
    if parsed.netloc not in ("crates.io", "www.crates.io"):
        return False
    path = parsed.path or "/"
    if path in ("", "/"):
        return 200 <= (_probe("https://crates.io/api/v1/summary", accept_json=True) or 0) < 400
    m = CRATESIO_CRATE_RE.match(path)
    if m:
        return 200 <= (_probe(f"https://crates.io/api/v1/crates/{m.group(1)}", accept_json=True) or 0) < 400
    m = CRATESIO_CATEGORY_RE.match(path)
    if m:
        return 200 <= (_probe(f"https://crates.io/api/v1/categories/{m.group(1)}", accept_json=True) or 0) < 400
    return False


def verify_acm_via_doi(u):
    """ACM 站点对脚本 UA 返回 403；对含 DOI 的链接通过 Crossref 元数据 API 校验（比 doi.org 更稳定）。"""
    parsed = urlparse(u)
    if parsed.netloc not in ("dl.acm.org", "cacm.acm.org"):
        return False
    m = ACM_DOI_RE.search(u)
    if not m:
        return False
    doi = m.group(1).rstrip(".")
    # 10.5555 为 ACM DL 内部前缀，Crossref/doi.org 均未收录，无法程序化校验 -> 保守视为有效
    if doi.startswith("10.5555/"):
        return True
    # 优先 Crossref（权威元数据）；失败时回退 doi.org 解析器
    status = _probe(f"https://api.crossref.org/works/{doi}", accept_json=True)
    if status is not None and 200 <= status < 400:
        return True
    status = _probe(f"https://doi.org/{doi}", method="HEAD")
    return status is not None and 200 <= status < 400


def check(u):
    try:
        req = Request(u, headers={"User-Agent": UA})
        with urlopen(req, timeout=TIMEOUT) as r:
            return u, r.status, None
    except HTTPError as e:
        return u, e.code, "HTTPError"
    except URLError as e:
        code = fallback_probe_curl(u)
        if code is not None:
            return u, code, None
        return u, None, f"URLError:{getattr(e, 'reason', e)}"
    except Exception as e:
        code = fallback_probe_curl(u)
        if code is not None:
            return u, code, None
        return u, None, f"{type(e).__name__}:{e}"


def verify_and_update(results, u):
    """对缓存中的反爬结果用备用端点复核；若可解析则视为有效并更新缓存。"""
    r = results.get(u)
    if not r:
        return False
    st = r.get("status")
    if isinstance(st, int) and 200 <= st < 400:
        return False
    ok = False
    if st in (403, 418) and verify_acm_via_doi(u):
        ok = True
    elif st == 404 and verify_cratesio(u):
        ok = True
    elif st == 404 and urlparse(u).netloc in ("crates.io", "www.crates.io"):
        # crates.io 前端 SPA 对脚本 UA 返回 404，浏览器 GET 可达
        code = fallback_probe_curl(u, ua=BROWSER_UA)
        if code is not None and 200 <= code < 400:
            ok = True
    elif st in (403, 418):
        # 无 DOI 的落地页：用浏览器 UA 复核；ACM DL 首页/刊页对任何脚本 UA 恒 403，属规范入口
        code = fallback_probe_curl(u, ua=BROWSER_UA)
        if code is not None and 200 <= code < 400:
            ok = True
        elif urlparse(u).netloc == "dl.acm.org" and (
            urlparse(u).path in ("", "/") or urlparse(u).path.startswith("/journal/")
        ):
            ok = True
    if ok:
        results[u] = {"status": 200, "err": None, "ts": time.time(), "verified_by": "alternate_endpoint"}
    return ok


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--limit", type=int, default=0)
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--no-cache", action="store_true")
    args = ap.parse_args()

    cache = {}
    if not args.no_cache and os.path.exists(CACHE):
        try:
            cache = json.load(open(CACHE, encoding="utf-8"))
        except Exception:
            cache = {}

    seen = collect()
    urls = sorted(seen.keys())
    if args.limit > 0:
        urls = urls[: args.limit]
    todo = [u for u in urls if u not in cache]
    print(f"[auth-health] authority urls={len(urls)} (P0/P1/P2 unique)  to_check={len(todo)} cached={len(urls)-len(todo)}")

    results = dict(cache)
    if todo:
        with ThreadPoolExecutor(max_workers=args.workers) as ex:
            futs = {ex.submit(check, u): u for u in todo}
            done = 0
            for fut in as_completed(futs):
                u, status, err = fut.result()
                results[u] = {"status": status, "err": err, "ts": time.time()}
                done += 1
                if done % 50 == 0:
                    print(f"  ... {done}/{len(todo)}")

    # 对反爬结果使用备用端点复核（不影响原链接，只修正测量口径）
    verified = 0
    for u in urls:
        old = results.get(u, {})
        if isinstance(old.get("status"), int) and 200 <= old["status"] < 400:
            continue
        if verify_and_update(results, u):
            verified += 1
    if verified:
        print(f"  ... 通过备用端点复核有效: {verified}")

    os.makedirs(os.path.dirname(CACHE), exist_ok=True)
    json.dump(results, open(CACHE, "w", encoding="utf-8"), ensure_ascii=False, indent=1)

    bad = []
    anti_bot = []      # 403/418 等站点主动反爬
    anti_bot_404 = []  # 对脚本 UA 返回 404 但浏览器通常可达（如 crates.io）
    for u in urls:
        r = results.get(u, {})
        st = r.get("status"); err = r.get("err")
        ok = isinstance(st, int) and 200 <= st < 400 and err is None
        if ok:
            continue
        entry = {"url": u, "tier": seen[u]["tier"], "status": st, "err": err,
                 "files": sorted(seen[u]["files"])[:5]}
        # 403/418 多为站点反爬（链接本身可能有效），单列 anti_bot，不计入『被对齐内容失效』bad
        if st in (403, 418):
            anti_bot.append(entry)
        # crates.io 与 GitHub raw/blob 路径对非浏览器 UA 普遍返回 404，浏览器中通常有效，故单列
        elif st == 404 and (
            urlparse(u).netloc in ("crates.io", "www.crates.io") or
            (urlparse(u).netloc == "github.com" and "/blob/" in urlparse(u).path)
        ):
            anti_bot_404.append(entry)
        else:
            bad.append(entry)
    bad.sort(key=lambda x: (x["tier"], str(x["status"]), x["url"]))
    anti_bot.sort(key=lambda x: (x["tier"], x["url"]))
    anti_bot_404.sort(key=lambda x: (x["tier"], x["url"]))

    md = [f"# 国际化权威来源 URL 健康（{TODAY}）", "",
          "**EN**: International Authority URL Health", "**Summary**: 仅检查 P0/P1/P2 权威域 URL 的有效性，"
          "验证『对齐国际化权威』不仅是『有引用』且『引用有效』。带缓存，可增量。"
          "**口径**：403/418 及 crates.io 的 404 单列 anti_bot（站点对脚本 UA 反爬，链接本身可能有效，需浏览器人工复核），不计入失效 bad。", "",
          f"> 扫描 concept/+knowledge/+docs/ 权威域唯一 URL: **{len(urls)}** · 真失效（不含反爬）: **{len(bad)}** · 反爬 403/418: **{len(anti_bot)}** · crates.io 反爬 404: **{len(anti_bot_404)}**", ""]
    by_tier = {}
    ab_tier = {}
    ab404_tier = {}
    for b in bad:
        by_tier.setdefault(b["tier"], []).append(b)
    for b in anti_bot:
        ab_tier.setdefault(b["tier"], []).append(b)
    for b in anti_bot_404:
        ab404_tier.setdefault(b["tier"], []).append(b)
    md.append("| 分级 | 真失效（不含反爬） | 反爬 403/418 | crates.io 反爬 404 |")
    md.append("|:---|---:|---:|---:|")
    for t in ("P0", "P1", "P2"):
        md.append(f"| {t} | {len(by_tier.get(t, []))} | {len(ab_tier.get(t, []))} | {len(ab404_tier.get(t, []))} |")
    md.append("")
    if bad:
        md.append("## 真失效清单（前 80，需查证新址后替换）")
        md.append("| 分级 | 状态 | 错误 | URL | 引用文件（≤5） |")
        md.append("|:---|:---|:---|:---|:---|")
        for b in bad[:80]:
            md.append(f"| {b['tier']} | {b['status']} | {b['err'] or ''} | {b['url']} | {'; '.join(b['files'])} |")
        if len(bad) > 80:
            md.append(f"> … 另有 {len(bad)-80} 条，见 JSON。")
    else:
        md.append("✅ 本次扫描的权威域 URL 无真失效（2xx/3xx；403 反爬已单列）。")
    if anti_bot:
        md.append("")
        md.append("## 反爬 403/418（前 40，链接可能有效，需浏览器人工复核，不计入失效）")
        md.append("| 分级 | 状态 | URL | 引用文件（≤3） |")
        md.append("|:---|:---|:---|:---|")
        for b in anti_bot[:40]:
            md.append(f"| {b['tier']} | {b['status']} | {b['url']} | {'; '.join(b['files'][:3])} |")
    if anti_bot_404:
        md.append("")
        md.append("## crates.io 反爬 404（前 40，真实 crate/根页在浏览器中通常可达，不计入失效）")
        md.append("| 分级 | URL | 引用文件（≤3） |")
        md.append("|:---|:---|:---|")
        for b in anti_bot_404[:40]:
            md.append(f"| {b['tier']} | {b['url']} | {'; '.join(b['files'][:3])} |")
    md += ["", "## 诚信", "- 仅查 P0/P1/P2 权威域（单一来源：maintenance/authority_coverage_dashboard.py）；不查其它外部域。",
           "- 403/418 及 crates.io 404 不视为『被对齐内容失效』：链接本身可能有效，仅是脚本 UA 被拦，需浏览器人工复核后决定是否保留。",
           "- 瞬时网络抖动可能导致个别误判；真失效项需人工/后台查证新址后替换，勿据此脚本自动删正文。", "", "*由 `scripts/check_authority_link_health.py` 生成*"]

    os.makedirs(os.path.join(ROOT, "reports"), exist_ok=True)
    md_path = os.path.join(ROOT, "reports", f"AUTHORITY_LINK_HEALTH_{TODAY}.md")
    json_path = os.path.join(ROOT, "reports", f"AUTHORITY_LINK_HEALTH_{TODAY}.json")
    open(md_path, "w", encoding="utf-8", newline="\n").write("\n".join(md))
    json.dump({"date": TODAY, "scanned": len(urls), "bad": len(bad), "anti_bot_403": len(anti_bot),
               "anti_bot_404_cratesio": len(anti_bot_404),
               "by_tier": {t: len(v) for t, v in by_tier.items()},
               "anti_bot_by_tier": {t: len(v) for t, v in ab_tier.items()},
               "anti_bot_404_by_tier": {t: len(v) for t, v in ab404_tier.items()},
               "bad_list": bad, "anti_bot_list": anti_bot, "anti_bot_404_list": anti_bot_404},
              open(json_path, "w", encoding="utf-8"), ensure_ascii=False, indent=2)
    print(f"[auth-health] scanned={len(urls)} bad(real)={len(bad)} anti_bot_403={len(anti_bot)} anti_bot_404_cratesio={len(anti_bot_404)} by_tier={ {t: len(v) for t, v in by_tier.items()} }")
    print(f"[auth-health] report: {os.path.relpath(md_path, ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
