#!/usr/bin/env python3
"""检查 concept/ 下所有非 GitHub 外部 Markdown 链接的可访问性."""
import argparse
import json
import re
import urllib.request
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from urllib.parse import urlparse
from collections import defaultdict
from datetime import datetime

ROOT = Path(__file__).resolve().parent.parent
CONCEPT = ROOT / "concept"
REPORT = ROOT / "reports" / "non_github_links_health_report.md"
CACHE = ROOT / ".non_github_links_cache.json"
WHITELIST = ROOT / "scripts" / "non_github_link_whitelist.json"
TIMEOUT = 15
MAX_WORKERS = 10
CACHE_TTL_SECONDS = 24 * 3600  # 仅缓存 200 OK 结果 24 小时

HEADERS = {
    'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/115.0.0.0 Safari/537.36',
    'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,*/*;q=0.8',
}


START_RE = re.compile(r'\[([^\]]+)\]\(')


def extract_links(text: str):
    """提取 Markdown 链接，支持 URL 中成对的括号."""
    for m in START_RE.finditer(text):
        start = m.end() - 1  # position of '('
        depth = 0
        i = start
        while i < len(text):
            ch = text[i]
            if ch == '(':
                depth += 1
            elif ch == ')':
                depth -= 1
                if depth == 0:
                    break
            i += 1
        if depth == 0:
            url = text[start + 1:i].strip()
            # ignore whitespace-only or empty URLs
            if url:
                yield m.group(1), url


def clean(url: str) -> str:
    # strip trailing punctuation that may have snuck in, but keep trailing )
    while url and url[-1] in '.,;>\'"':
        url = url[:-1]
    return url


def collect():
    urls = defaultdict(list)
    for p in CONCEPT.rglob('*.md'):
        text = p.read_text(encoding='utf-8', errors='ignore')
        for label, url in extract_links(text):
            url = clean(url)
            if not url.startswith(('http://', 'https://')):
                continue
            if urlparse(url).netloc == 'github.com':
                continue
            urls[url].append(p.relative_to(CONCEPT).as_posix())
    return urls


def load_cache():
    if CACHE.exists():
        try:
            return json.loads(CACHE.read_text(encoding='utf-8'))
        except Exception:
            pass
    return {}


def save_cache(cache):
    CACHE.write_text(json.dumps(cache, indent=2, ensure_ascii=False), encoding='utf-8')


def load_whitelist():
    if WHITELIST.exists():
        try:
            return json.loads(WHITELIST.read_text(encoding='utf-8'))
        except Exception:
            pass
    return []


def is_whitelisted(url, prefixes):
    return any(url.startswith(p) for p in prefixes)


def check(url: str, retries: int = 1):
    last_status, last_err = None, None
    for attempt in range(retries + 1):
        # HEAD 优先，失败再回退 GET，减少带宽
        for method in ('HEAD', 'GET'):
            req = urllib.request.Request(url, method=method, headers=HEADERS)
            try:
                with urllib.request.urlopen(req, timeout=TIMEOUT) as resp:
                    return resp.status, None
            except urllib.error.HTTPError as e:
                last_status, last_err = e.code, None
                # HEAD 返回 4xx 时不直接判定，回退 GET；GET 失败才返回
                if method == 'GET' and 400 <= e.code < 600:
                    return e.code, None
            except Exception as e:
                last_err = str(e)
                last_status = None
    return last_status, last_err or 'unknown'


def classify(status, err):
    if status == 200:
        return 'ok'
    if status in (403, 401):
        return 'protected'
    if status in (301, 302, 303, 307, 308, 202):
        return 'redirect'
    if err and 'SSL' in err:
        return 'ssl_warning'
    if status in (404, 410):
        return 'broken'
    if status is None:
        return 'broken'
    return 'broken'


def main():
    parser = argparse.ArgumentParser(description='检查 concept/ 非 GitHub 外部链接健康')
    parser.add_argument('--no-cache', action='store_true', help='忽略本地缓存，全量重新检查')
    args = parser.parse_args()

    url_map = collect()
    urls = sorted(url_map.keys())
    total = len(urls)

    cache = {} if args.no_cache else load_cache()
    whitelist_prefixes = load_whitelist()
    now = datetime.now().timestamp()

    ok = []
    whitelisted = []
    protected = []
    broken = []

    def process(url):
        if is_whitelisted(url, whitelist_prefixes):
            return url, None, None, False, 'whitelisted'
        cached = cache.get(url)
        if cached and cached.get('ok') and (now - cached.get('ts', 0)) < CACHE_TTL_SECONDS:
            return url, cached['status'], cached.get('err'), True, 'cached'
        status, err = check(url)
        cat = classify(status, err)
        cache[url] = {'status': status, 'err': err, 'ok': cat == 'ok', 'ts': now}
        return url, status, err, False, cat

    print(f"检查 {total} 个 concept/ 非 GitHub 外部链接...")
    with ThreadPoolExecutor(max_workers=MAX_WORKERS) as ex:
        futures = {ex.submit(process, u): u for u in urls}
        for i, fut in enumerate(as_completed(futures), 1):
            result = fut.result()
            url, status, err, from_cache, cat = result
            if cat == 'cached':
                cat = classify(status, err)
            marker = " (cached)" if from_cache else ""
            if cat == 'whitelisted':
                print(f"[{i}/{total}] WHITELISTED {url}")
                whitelisted.append(url)
            elif cat == 'ok':
                print(f"[{i}/{total}] OK{marker} {url}")
                ok.append(url)
            elif cat in ('protected', 'redirect', 'ssl_warning'):
                code = status if status is not None else err
                print(f"[{i}/{total}] WARN{marker} {code} {url}")
                protected.append((url, status, err))
            else:
                code = status if status is not None else err
                print(f"[{i}/{total}] FAIL{marker} {code} {url}")
                broken.append((url, status, err))

    save_cache(cache)

    report_lines = [
        "# 非 GitHub 外部链接健康检查报告",
        "",
        f"> 生成时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}",
        f"> 扫描范围: `concept/` 下所有非 `github.com` 的 Markdown 外部链接",
        f"> 去重链接数: {total}",
        f"> HTTP 200: {len(ok)}",
        f"> 已白名单（脚本/SSL/403 误报）: {len(whitelisted)}",
        f"> 受保护/重定向/SSL 警告（需人工复核）: {len(protected)}",
        f"> 疑似失效（404/超时/5xx）: {len(broken)}",
        "",
    ]
    if protected:
        report_lines.append("## 受保护/重定向/SSL 警告链接清单\n")
        report_lines.append("| URL | 状态 | 涉及文件 |")
        report_lines.append("|:---|:---|:---|")
        for url, status, err in sorted(protected):
            code = status if status is not None else err
            files = ', '.join(sorted(set(url_map[url]))[:5])
            report_lines.append(f"| `{url}` | {code} | {files} |")
        report_lines.append("")
    if broken:
        report_lines.append("## 疑似失效链接清单\n")
        report_lines.append("| URL | 状态 | 涉及文件 |")
        report_lines.append("|:---|:---|:---|")
        for url, status, err in sorted(broken):
            code = status if status is not None else err
            files = ', '.join(sorted(set(url_map[url]))[:5])
            report_lines.append(f"| `{url}` | {code} | {files} |")
        report_lines.append("")
    if whitelisted:
        report_lines.append("## 已白名单链接清单\n")
        report_lines.append("| URL | 涉及文件 |")
        report_lines.append("|:---|:---|")
        for url in sorted(whitelisted):
            files = ', '.join(sorted(set(url_map[url]))[:5])
            report_lines.append(f"| `{url}` | {files} |")
        report_lines.append("")
    if not protected and not broken:
        report_lines.append("所有非 GitHub 外部链接均可访问或已白名单。")
        report_lines.append("")
    REPORT.write_text('\n'.join(report_lines), encoding='utf-8')
    print(f"\n检查完成。异常链接: {len(broken)}")
    print(f"报告已写入: {REPORT}")


if __name__ == '__main__':
    main()
