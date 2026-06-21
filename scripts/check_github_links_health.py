#!/usr/bin/env python3
"""Check health of all github.com links in concept/ Markdown files.

Uses slow sequential requests to avoid GitHub rate limits. For file/tree URLs,
validates via raw.githubusercontent.com; for other GitHub pages, validates the
HTML page directly.
"""
import re
import time
import urllib.request
from pathlib import Path
from urllib.parse import urlparse

ROOT = Path(__file__).resolve().parent.parent / "concept"
LINK_RE = re.compile(r'\[([^\]]+)\]\((https?://github\.com/[^\)]+)\)')
TIMEOUT = 15

def normalize(url: str) -> str:
    # Strip markdown trailing punctuation that might be captured
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

def check(url: str) -> tuple:
    parsed = urlparse(url)
    path = parsed.path.strip('/')
    parts = path.split('/')
    # File URLs (/blob/) -> validate via raw.githubusercontent.com
    if len(parts) >= 5 and parts[2] == 'blob':
        owner, repo = parts[0], parts[1]
        branch = parts[3]
        file_path = '/'.join(parts[4:])
        # Directory listings disguised as blob URLs (trailing slash) need HTML
        if file_path.endswith('/'):
            return _request(url, url)
        raw = f'https://raw.githubusercontent.com/{owner}/{repo}/{branch}/{file_path}'
        return _request(raw, url)
    # Directory URLs (/tree/) and all other GitHub pages -> validate HTML page
    return _request(url, url)

def _request(req_url: str, original_url: str) -> tuple:
    req = urllib.request.Request(req_url, method='HEAD', headers={
        'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36',
        'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8',
    })
    try:
        with urllib.request.urlopen(req, timeout=TIMEOUT) as resp:
            return original_url, resp.status, None
    except urllib.error.HTTPError as e:
        return original_url, e.code, None
    except Exception as e:
        return original_url, None, str(e)

def main():
    links = collect_links()
    total = len(links)
    print(f'Scanning {total} unique github.com links from {ROOT}...')
    bad = []
    for i, url in enumerate(sorted(links), 1):
        status, err = check(url)[1:]
        if status != 200:
            bad.append((url, status, err, links[url]))
        print(f'[{i}/{total}] {status or "ERR"} {url[:90]}')
        time.sleep(0.8)
    # Report
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
            out.write('| URL | 状态码 | 错误 | 涉及文件 |\n|:---|:---|:---|:---|\n')
            for url, status, err, files in bad:
                status_str = str(status) if status is not None else f'ERR ({err})'
                files_str = ', '.join(sorted(set(files)))
                out.write(f'| `{url}` | {status_str} | {err or ""} | {files_str} |\n')
        else:
            out.write('所有 GitHub 链接均可访问。\n')
    print(f'Report written to {report_path}')
    print(f'Bad links: {len(bad)}')

if __name__ == '__main__':
    main()
