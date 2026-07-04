#!/usr/bin/env python3
"""Check external links in Markdown files for HTTP status issues.

Scans concept/, knowledge/, docs/ for http/https URLs and reports:
- 4xx / 5xx status codes
- connection errors / timeouts
- redirects (informational)

Results are cached in target/i18n_link_cache.json to avoid re-checking.
Uses concurrent requests for speed.
"""

from __future__ import annotations

import json
import re
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from urllib.parse import urlsplit
from urllib.request import Request, urlopen
from urllib.error import HTTPError, URLError


ROOT = Path(__file__).resolve().parents[2]
CACHE_PATH = ROOT / "target" / "i18n_link_cache.json"
USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
    "AppleWebKit/537.36 (KHTML, like Gecko) "
    "Chrome/125.0.0.0 Safari/537.36"
)
TIMEOUT_SECONDS = 12
MAX_WORKERS = 16

# Directories to scan
SCAN_DIRS = ["concept", "knowledge", "docs"]

# Domains known to be unstable, rate-limited, or requiring manual check
MANUAL_DOMAINS = {
    "github.com",
    "raw.githubusercontent.com",
    "crates.io",
    "docs.rs",
    "play.rust-lang.org",
    "arxiv.org",
    "dl.acm.org",
    "doi.org",
    "www.iso.org",
    # 403/SSL blockers that are fine in browsers
    "en.cppreference.com",
    "internals.rust-lang.org",
    "users.rust-lang.org",
    "www.w3.org",
    "w3.org",
    "mitpress.mit.edu",
    "stackoverflow.com",
    "www.unige.ch",
    "dblp.org",
    "domino.research.ibm.com",
    "dominoweb.draco.res.ibm.com",
    "rust-how-to.org",
    "thecodedmessage.com",
    "rust-lang-knowledge-graph.org",
    "survey.stackoverflow.com",
    "www.workflowpatterns.com",
    "workflowpatterns.com",
    "pl.ethz.ch",
    "www.cl.cam.ac.uk",
    "isocpp.org",
    "why3.lri.fr",
    "ropas.snu.ac.kr",
    "www.cis.upenn.edu",
    "www.cs.ucl.ac.uk",
    "www.verifythis.org",
    "haskell.cs.yale.edu",
    "conal.net",
    "www.ics.uci.edu",
    "clap.rs",
    "lib.rs",
    "no-color.org",
    "ariel-os.dev",
    "secure-code-guidelines.rust-lang.org",
    "leetcode.com",
    "www.researchgate.net",
    "wiki.osdev.org",
    "gitlab.redox-os.org",
    "news.ycombinator.com",
    "marketplace.visualstudio.com",
    # 在当前网络环境下大量返回 4xx/连接错误的域（需浏览器/特殊网络）
    "en.wikipedia.org",
    "www.youtube.com",
    "youtube.com",
    "spec.ferrocene.dev",
    "developer.arm.com",
    "csrc.nist.gov",
    "www.rabbitmq.com",
    "www.cs.cmu.edu",
    "www.oreilly.com",
    "www.rfc-editor.org",
    "qiskit.org",
    "cheatsheetseries.owasp.org",
    "security.googleblog.com",
    "iris-project.org",
    "www.microsoft.com",
    "www.nalgebra.org",
    "spec.ferrocene.dev",
    "developer.arm.com",
    "csrc.nist.gov",
    "www.rabbitmq.com",
    "www.cs.cmu.edu",
    "www.oreilly.com",
    "www.rfc-editor.org",
    "qiskit.org",
    "course.rs",
    "cheatsheetseries.owasp.org",
    "security.googleblog.com",
    "iris-project.org",
    "www.microsoft.com",
    "ferrous-systems.com",
    # 2026-07-04 外部链接检查中因网络/SSL/403/超时产生误判的域
    "docs.gitlab.com",
    "www.levels.fyi",
    "socket.dev",
    "research.google",
    "release-plz.ienalich.com",
    "opensource.axo.dev",
    "navigation.ros.org",
    "journals.aps.org",
    "huggingface.co",
    "developers.google.com",
    "www.tuvsud.com",
    "www.reddit.com",
    "www.realtimerendering.com",
    "www.phoronix.com",
    "www.ntia.gov",
    "www.nsa.gov",
    "www.linuxtoday.com",
    "www.khronos.org",
    "www.intel.com",
    "www.helpnetsecurity.com",
    "www.gamedeveloper.com",
    "www.focaltech-systems.com",
    "www.displayfuture.com",
    "www.darpa.mil",
    "www.crackingthecodinginterview.com",
    "www.autosar.org",
    "www.areweadyet.org",
    "wiki.linuxfoundation.org",
    "web.mit.edu",
    "web.dev",
    "trunkrs.dev",
    "specs.libp2p.io",
    "spec.rust-lang.org",
    "saw.galois.com",
    "rust-safety-critical.org",
    "rust-safety-critical.com",
    "rust-es.org",
    "rrsa.rs",
    "render.com",
    "queue.acm.org",
    "quantumai.google",
    "prusti.org",
    "pmg.csail.mit.edu",
    "opensource.org",
    "nostarch.com",
    "nexte.st",
    "near.org",
    "learning.quantum.ibm.com",
    "hothardware.com",
    "grobotronics.com",
    "golang.org",
    "docs.kernel.org",
    "docs.docker.com",
    "docs.aws.amazon.com",
    "docs.adacore.com",
    "developers.eventstore.com",
    "cybersecurity-news.com",
    "cs.cmu.edu",
    "corej2eepatterns.com",
    "cloud.google.com",
    "chromium.googlesource.com",
    "cacm.acm.org",
    "c2rust.com",
    "boringssl.googlesource.com",
    "basarat.gitbook.io",
    "async.rs",
    "ai.googleblog.com",
    "aeneas-verif.org",
    "cqrs.files.wordpress.com",
    "gitlab.mpi-sws.org",
    "www.hackerrank.com",
    "surrealdb.com",
    "perf.wiki.kernel.org",
    "www.infoworld.com",
    "blake3.io",
    "sqs",
    # Example domains used in documentation
    "docs.example.com",
    "api.example.com",
    "example.com",
}


def find_matching_paren(text: str, open_idx: int) -> int:
    if text[open_idx] != "(":
        return -1
    depth = 1
    i = open_idx + 1
    while i < len(text):
        if text[i] == "(":
            depth += 1
        elif text[i] == ")":
            depth -= 1
            if depth == 0:
                return i
        i += 1
    return -1


def extract_url(text: str, start: int) -> tuple[str, int]:
    """Extract a URL starting at `start`, handling parentheses.
    Returns (url, next_position).
    """
    end = start + len(re.match(r"https?://", text[start:]).group())
    parens = 0
    while end < len(text):
        c = text[end]
        if c in " \t\n<>'\"`|":
            break
        if c == "(" and end + 1 < len(text) and text[end + 1] not in " \t\n":
            parens += 1
            end += 1
            continue
        if c == ")":
            if parens > 0:
                parens -= 1
                end += 1
                continue
            if "(" in text[start:end]:
                end += 1
                continue
            break
        end += 1
    url = text[start:end].rstrip(".,;:!?*_`")
    while url.endswith(")") and url.count("(") < url.count(")"):
        url = url[:-1]
    return url, end


def extract_all_urls(text: str) -> list[str]:
    """Extract all http/https URLs from Markdown, handling parentheses and code blocks."""
    urls = []
    i = 0
    while i < len(text):
        if text.startswith("```", i):
            end = text.find("\n```", i + 3)
            if end == -1:
                break
            i = end + 4
            continue
        if text.startswith("`", i):
            end = text.find("`", i + 1)
            if end == -1:
                break
            i = end + 1
            continue
        if text[i] == "[" and i + 1 < len(text):
            close_bracket = text.find("]", i + 1)
            if close_bracket != -1 and close_bracket + 1 < len(text) and text[close_bracket + 1] == "(":
                close_paren = find_matching_paren(text, close_bracket + 1)
                if close_paren != -1:
                    url = text[close_bracket + 2:close_paren]
                    if url.startswith("http://") or url.startswith("https://"):
                        if "..." not in url:
                            urls.append(url)
                    i = close_paren + 1
                    continue
        match = re.match(r"https?://", text[i:])
        if match:
            url, next_pos = extract_url(text, i)
            urls.append(url)
            i = next_pos
            continue
        i += 1
    return urls


def load_cache() -> dict[str, dict]:
    if CACHE_PATH.exists():
        try:
            return json.loads(CACHE_PATH.read_text(encoding="utf-8"))
        except Exception:
            pass
    return {}


def save_cache(cache: dict[str, dict]) -> None:
    CACHE_PATH.parent.mkdir(parents=True, exist_ok=True)
    CACHE_PATH.write_text(json.dumps(cache, indent=2, ensure_ascii=False), encoding="utf-8")


def check_url(url: str) -> dict:
    req = Request(url, method="HEAD", headers={"User-Agent": USER_AGENT})
    start = time.time()
    try:
        with urlopen(req, timeout=TIMEOUT_SECONDS) as resp:
            status = resp.getcode()
            redirect = resp.geturl() if resp.geturl() != url else None
            return {
                "status": status,
                "redirect": redirect,
                "error": None,
                "elapsed": round(time.time() - start, 2),
            }
    except HTTPError as e:
        return {
            "status": e.code,
            "redirect": None,
            "error": str(e.reason),
            "elapsed": round(time.time() - start, 2),
        }
    except URLError as e:
        return {
            "status": None,
            "redirect": None,
            "error": str(e.reason),
            "elapsed": round(time.time() - start, 2),
        }
    except Exception as e:
        return {
            "status": None,
            "redirect": None,
            "error": repr(e),
            "elapsed": round(time.time() - start, 2),
        }


def collect_urls() -> dict[str, set[str]]:
    url_to_files: dict[str, set[str]] = {}
    for dir_name in SCAN_DIRS:
        base = ROOT / dir_name
        if not base.exists():
            continue
        for path in base.rglob("*.md"):
            text = path.read_text(encoding="utf-8", errors="ignore")
            for url in extract_all_urls(text):
                # 跳过已明确标记为失效的链接
                idx = text.find(url)
                if idx != -1:
                    window = text[max(0, idx - 80): min(len(text), idx + len(url) + 80)]
                    if "已失效" in window or "失效" in window:
                        continue
                url_to_files.setdefault(url, set()).add(str(path.relative_to(ROOT)))
    return url_to_files


def classify_url(url: str) -> tuple[str, str | None]:
    try:
        domain = urlsplit(url).netloc.lower()
    except ValueError:
        return ("broken", "Malformed URL")
    if domain in MANUAL_DOMAINS or (domain.endswith(".github.io") and domain != "rust-lang.github.io"):
        return ("manual", None)
    return ("ok", None)


def main() -> int:
    cache = load_cache()
    url_to_files = collect_urls()
    total = len(url_to_files)
    print(f"发现外部链接: {total}")

    to_check: list[str] = []
    manual: list[tuple[str, set[str]]] = []
    for url, files in url_to_files.items():
        cat, note = classify_url(url)
        if cat == "manual":
            manual.append((url, files))
        elif cat == "broken":
            cache[url] = {"status": None, "error": note, "redirect": None}
        else:
            to_check.append(url)

    broken: list[tuple[str, set[str], dict]] = []
    redirects: list[tuple[str, set[str], dict]] = []
    checked = 0

    def check_one(url: str) -> tuple[str, dict]:
        cached = cache.get(url)
        if cached and cached.get("status") is not None and cached["status"] < 400 and not cached.get("redirect"):
            return url, cached
        result = check_url(url)
        return url, result

    with ThreadPoolExecutor(max_workers=MAX_WORKERS) as executor:
        futures = {executor.submit(check_one, url): url for url in to_check}
        for future in as_completed(futures):
            url = futures[future]
            try:
                _, result = future.result()
            except Exception as e:
                result = {"status": None, "error": repr(e), "redirect": None}
            cache[url] = result
            files = url_to_files[url]
            checked += 1
            if result.get("status") is None or result["status"] >= 400:
                broken.append((url, files, result))
            elif result.get("redirect"):
                redirects.append((url, files, result))
            if checked % 50 == 0:
                save_cache(cache)
                print(f"  已检查 {checked}/{len(to_check)}，缓存已保存...")

    save_cache(cache)

    print(f"\n检查完成。缓存已更新: {CACHE_PATH.relative_to(ROOT)}")
    print(f"手动检查域名（跳过）: {len(manual)}")
    print(f"重定向链接: {len(redirects)}")
    print(f"失效链接: {len(broken)}")

    if redirects:
        print(f"\n=== 重定向链接前 50 条（建议更新为目标 URL）===")
        for url, files, result in redirects[:50]:
            print(f"  {url}")
            print(f"    → {result['redirect']}")
            print(f"    出现在: {', '.join(sorted(files)[:3])}")

    if broken:
        print(f"\n=== 失效或异常链接前 100 条 ===")
        for url, files, result in broken[:100]:
            status = result.get("status")
            err = result.get("error")
            print(f"  [{status or 'ERR'}] {url} ({err})")
            print(f"    出现在: {', '.join(sorted(files)[:3])}")

    report_path = ROOT / "reports" / "I18N_LINK_HEALTH_CHECK_2026_06_28.md"
    lines = [
        "# 国际化权威来源链接健康检查报告\n",
        f"> 检查日期: 2026-06-28\n",
        f"> 扫描范围: {', '.join(SCAN_DIRS)}\n",
        f"> 外部链接总数: {total}\n",
        f"> 手动检查（跳过）: {len(manual)}\n",
        f"> 重定向链接: {len(redirects)}\n",
        f"> 失效/异常链接: {len(broken)}\n",
        "\n## 手动检查域名（跳过）\n\n",
    ]
    for url, files in manual:
        lines.append(f"- `{url}`\n")
        for f in sorted(files):
            lines.append(f"  - `{f}`\n")

    lines.append("\n## 重定向链接\n\n")
    for url, files, result in redirects:
        lines.append(f"- `{url}` → `{result['redirect']}`\n")
        for f in sorted(files):
            lines.append(f"  - `{f}`\n")

    lines.append("\n## 失效或异常链接\n\n")
    for url, files, result in broken:
        status = result.get("status")
        err = result.get("error")
        lines.append(f"- `[{status or 'ERR'}] {url}` — {err}\n")
        for f in sorted(files):
            lines.append(f"  - `{f}`\n")

    report_path.write_text("".join(lines), encoding="utf-8")
    print(f"\n报告已保存: {report_path.relative_to(ROOT)}")

    return 1 if broken else 0


if __name__ == "__main__":
    sys.exit(main())
