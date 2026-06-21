#!/usr/bin/env python3
"""扩展来源链接可访问性检查：覆盖 Rust 官方、生态 crate、权威社区文档."""
import re
import urllib.request
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from urllib.parse import urlparse

ROOT = Path(__file__).resolve().parent.parent / "concept"
LINK_RE = re.compile(r'\[([^\]]+)\]\((https?://[^\)]+)\)')

# 扩展权威域名白名单
CHECK_DOMAINS = {
    'doc.rust-lang.org',
    'rust-lang.github.io',
    'www.rust-lang.org',
    'blog.rust-lang.org',
    'docs.rs',
    'crates.io',
    'github.com',
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
}
TIMEOUT = 10


def collect_urls():
    urls = set()
    for p in ROOT.rglob('*.md'):
        text = p.read_text(encoding='utf-8')
        m = re.search(r'^>\s*\*\*来源\*\*:\s*(.*?)$', text, re.MULTILINE)
        if not m:
            continue
        for label, url in LINK_RE.findall(m.group(1)):
            if urlparse(url).netloc in CHECK_DOMAINS:
                urls.add(url)
    return sorted(urls)


def check(url: str):
    req = urllib.request.Request(
        url,
        method='HEAD',
        headers={
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/115.0.0.0 Safari/537.36',
            'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,*/*;q=0.8',
        },
    )
    try:
        with urllib.request.urlopen(req, timeout=TIMEOUT) as resp:
            return url, resp.status, None
    except urllib.error.HTTPError as e:
        return url, e.code, None
    except Exception as e:
        return url, None, str(e)


def main():
    urls = collect_urls()
    print(f"检查 {len(urls)} 个扩展权威来源链接...\n")
    broken = []
    with ThreadPoolExecutor(max_workers=12) as ex:
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
        print("\n### 异常链接\n")
        for url, status, err in broken:
            print(f"- `{url}`: {status or err}")


if __name__ == '__main__':
    main()
