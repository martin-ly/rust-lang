#!/usr/bin/env python3
"""检查 concept/ 下所有 Markdown 链接（不仅是来源块）的可访问性."""
import re
import urllib.request
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from urllib.parse import urlparse

ROOT = Path(__file__).resolve().parent.parent / "concept"
LINK_RE = re.compile(r'\[([^\]]+)\]\((https?://[^\)]+)\)')

CHECK_DOMAINS = {
    'doc.rust-lang.org',
    'rust-lang.github.io',
    'www.rust-lang.org',
    'blog.rust-lang.org',
    'docs.rs',
    'crates.io',
    # 'github.com',  # GitHub 对频繁 HEAD/GET 敏感，单独维护
    'rust-book.cs.brown.edu',
    'serde.rs',
    'rust-unofficial.github.io',
    'veykril.github.io',
    'plv.mpi-sws.org',
    'docs.rust-embedded.org',
    'rust-cli.github.io',
    'rustwasm.github.io',
    'docs.wasmtime.dev',
    'aya-rs.dev',
    'borrowsanitizer.com',
    'docs.kernel.org',
    'tikv.org',
    'bevyengine.org',
    'rocket.rs',
    'choosealicense.com',
    'docs.github.com',
    'foundation.rust-lang.org',
    'www.redox-os.org',
    'rust-for-linux.com',
    'source.android.com',
    'www.chromium.org',
    'rustc-dev-guide.rust-lang.org',
    'rustup.rs',
}
TIMEOUT = 10


def collect_urls():
    urls = {}
    for p in ROOT.rglob('*.md'):
        text = p.read_text(encoding='utf-8', errors='ignore')
        for label, url in LINK_RE.findall(text):
            if urlparse(url).netloc in CHECK_DOMAINS:
                urls.setdefault(url, []).append(p.relative_to(ROOT).as_posix())
    return urls


def check(url: str):
    headers = {
        'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/115.0.0.0 Safari/537.36',
        'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,*/*;q=0.8',
    }
    for method in ('HEAD', 'GET'):
        req = urllib.request.Request(url, method=method, headers=headers)
        try:
            with urllib.request.urlopen(req, timeout=TIMEOUT) as resp:
                return url, resp.status, None
        except urllib.error.HTTPError as e:
            if method == 'GET':
                return url, e.code, None
        except Exception as e:
            if method == 'GET':
                return url, None, str(e)
    return url, None, 'unknown'


def main():
    url_map = collect_urls()
    urls = sorted(url_map.keys())
    print(f"检查 {len(urls)} 个 concept/ 扩展权威链接...\n")
    broken = []
    with ThreadPoolExecutor(max_workers=16) as ex:
        futures = {ex.submit(check, u): u for u in urls}
        for fut in as_completed(futures):
            url, status, err = fut.result()
            if status == 200:
                print(f"OK {status} {url}")
            else:
                print(f"FAIL {status or err} {url}")
                broken.append((url, status, err))
    print(f"\n检查完成。异常链接: {len(broken)}")
    if broken:
        print("\n### 异常链接（按出现文件分组）\n")
        for url, status, err in sorted(broken):
            files = sorted(set(url_map[url]))
            print(f"- `{url}`: {status or err}")
            for f in files[:5]:
                print(f"  - `{f}`")


if __name__ == '__main__':
    main()
