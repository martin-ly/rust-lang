#!/usr/bin/env python3
"""检查 concept/ 下所有非 GitHub 外部 Markdown 链接的可访问性."""
import re
import urllib.request
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from urllib.parse import urlparse
from collections import defaultdict
from datetime import datetime

ROOT = Path(__file__).resolve().parent.parent / "concept"
REPORT = Path(__file__).resolve().parent.parent / "reports" / "non_github_links_health_report.md"
TIMEOUT = 15
MAX_WORKERS = 10

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
    for p in ROOT.rglob('*.md'):
        text = p.read_text(encoding='utf-8', errors='ignore')
        for label, url in extract_links(text):
            url = clean(url)
            if not url.startswith(('http://', 'https://')):
                continue
            if urlparse(url).netloc == 'github.com':
                continue
            urls[url].append(p.relative_to(ROOT).as_posix())
    return urls


def check(url: str, retries: int = 1):
    last_status, last_err = None, None
    for attempt in range(retries + 1):
        for method in ('GET', 'HEAD'):
            req = urllib.request.Request(url, method=method, headers=HEADERS)
            try:
                with urllib.request.urlopen(req, timeout=TIMEOUT) as resp:
                    return resp.status, None
            except urllib.error.HTTPError as e:
                last_status, last_err = e.code, None
                # Do not retry on 4xx client errors
                if 400 <= e.code < 500:
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
    url_map = collect()
    urls = sorted(url_map.keys())
    total = len(urls)
    ok = []
    protected = []
    broken = []
    print(f"检查 {total} 个 concept/ 非 GitHub 外部链接...")
    with ThreadPoolExecutor(max_workers=MAX_WORKERS) as ex:
        futures = {ex.submit(check, u): u for u in urls}
        for i, fut in enumerate(as_completed(futures), 1):
            url = futures[fut]
            status, err = fut.result()
            cat = classify(status, err)
            if cat == 'ok':
                print(f"[{i}/{total}] OK {url}")
                ok.append(url)
            elif cat in ('protected', 'redirect', 'ssl_warning'):
                code = status if status is not None else err
                print(f"[{i}/{total}] WARN {code} {url}")
                protected.append((url, status, err))
            else:
                code = status if status is not None else err
                print(f"[{i}/{total}] FAIL {code} {url}")
                broken.append((url, status, err))

    report_lines = [
        "# 非 GitHub 外部链接健康检查报告",
        "",
        f"> 生成时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}",
        f"> 扫描范围: `concept/` 下所有非 `github.com` 的 Markdown 外部链接",
        f"> 去重链接数: {total}",
        f"> HTTP 200: {len(ok)}",
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
    if not protected and not broken:
        report_lines.append("所有非 GitHub 外部链接均可访问。")
        report_lines.append("")
    REPORT.write_text('\n'.join(report_lines), encoding='utf-8')
    print(f"\n检查完成。异常链接: {len(broken)}")
    print(f"报告已写入: {REPORT}")


if __name__ == '__main__':
    main()
