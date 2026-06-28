#!/usr/bin/env python3
"""Check health of all github.com links in concept/ Markdown files.

Uses a small concurrent pool with adaptive rate limiting. For file/tree URLs,
validates via raw.githubusercontent.com; for other GitHub pages, validates the
HTML page directly.
"""
import json
import re
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from urllib.parse import urlparse

import urllib.request

ROOT = Path(__file__).resolve().parent.parent / "concept"
LINK_RE = re.compile(r'\[([^\]]+)\]\((https?://github\.com/[^\)]+)\)')
TIMEOUT = 15
CACHE_PATH = Path(__file__).resolve().parent.parent / "target" / "github_link_cache.json"
CACHE_TTL_DAYS = 7
MAX_WORKERS = 5
BASE_DELAY = 0.6

HEADERS = {
    'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36',
    'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8',
}


def normalize(url: str) -> str:
    while url.endswith(('.', ',', ';', ')')):
        url = url[:-1]
    return url


def collect_links():
    links = {}
    for f in ROOT.rglob('*.md'):
        text = f.read_text(encoding='utf-8')
        for label, url in LINK_RE.findall(text):
            url = normalize(url)
            links.setdefault(url, []).append(str(f))
    return links


def load_cache():
    if not CACHE_PATH.exists():
        return {}
    try:
        data = json.loads(CACHE_PATH.read_text(encoding='utf-8'))
        cutoff = time.time() - CACHE_TTL_DAYS * 86400
        return {k: v for k, v in data.items() if v.get('ts', 0) > cutoff}
    except Exception:
        return {}


def save_cache(cache):
    CACHE_PATH.parent.mkdir(parents=True, exist_ok=True)
    CACHE_PATH.write_text(json.dumps(cache, ensure_ascii=False, indent=2), encoding='utf-8')


def resolve_url(url: str) -> tuple:
    parsed = urlparse(url)
    path = parsed.path.strip('/')
    parts = path.split('/')
    if len(parts) >= 5 and parts[2] == 'blob':
        owner, repo = parts[0], parts[1]
        branch = parts[3]
        file_path = '/'.join(parts[4:])
        if file_path.endswith('/'):
            return url, False
        return f'https://raw.githubusercontent.com/{owner}/{repo}/{branch}/{file_path}', True
    return url, False


def check_one(url: str, retries: int = 2) -> tuple:
    req_url, _ = resolve_url(url)
    last_err = None
    for attempt in range(retries + 1):
        req = urllib.request.Request(req_url, method='HEAD', headers=HEADERS)
        try:
            with urllib.request.urlopen(req, timeout=TIMEOUT) as resp:
                return url, resp.status, None
        except urllib.error.HTTPError as e:
            if e.code == 429:
                time.sleep(2 ** attempt)
                continue
            return url, e.code, None
        except Exception as e:
            last_err = str(e)
            time.sleep(0.5)
    return url, None, last_err


def main():
    links = collect_links()
    total = len(links)
    cache = load_cache()
    to_check = [u for u in sorted(links) if u not in cache]
    print(f'Scanning {total} unique github.com links from {ROOT}...')
    print(f'Using cache ({len(cache)} entries); {len(to_check)} to check live.')

    bad = []
    # Add cached bad links (only if still present in current scan)
    for url, entry in cache.items():
        if entry.get('status') != 200 and url in links:
            bad.append((url, entry.get('status'), entry.get('err'), links[url]))

    completed = 0
    with ThreadPoolExecutor(max_workers=MAX_WORKERS) as ex:
        futures = {ex.submit(check_one, u): u for u in to_check}
        for fut in as_completed(futures):
            url = futures[fut]
            _, status, err = fut.result()
            completed += 1
            cache[url] = {'status': status, 'err': err, 'ts': time.time()}
            if status != 200:
                bad.append((url, status, err, links[url]))
            print(f'[{completed}/{len(to_check)}] {status or "ERR"} {url[:90]}')
            time.sleep(BASE_DELAY)

    save_cache(cache)

    report_path = Path(__file__).resolve().parent.parent / 'reports' / 'github_links_health_report.md'
    with open(report_path, 'w', encoding='utf-8') as out:
        out.write('# GitHub 链接健康检查报告\n\n')
        out.write(f'> 生成时间: {time.strftime("%Y-%m-%d %H:%M:%S")}\n')
        out.write(f'> 扫描范围: `concept/` 下所有 `github.com` Markdown 链接\n')
        out.write(f'> 去重链接数: {total}\n')
        out.write(f'> HTTP 200: {total - len(bad)}\n')
        out.write(f'> 异常数: {len(bad)}\n\n')
        if bad:
            out.write('## 异常链接清单\n\n')
            out.write('| URL | 状态码 | 错误 | 涉及文件 |\n|:---|:---|:---|:---|')
            for url, status, err, files in bad:
                status_str = str(status) if status is not None else f'ERR ({err})'
                files_str = ', '.join(sorted(set(files)))
                out.write(f'\n| `{url}` | {status_str} | {err or ""} | {files_str} |')
        else:
            out.write('所有 GitHub 链接均可访问。\n')
    print(f'Report written to {report_path}')
    print(f'Bad links: {len(bad)}')


if __name__ == '__main__':
    main()
