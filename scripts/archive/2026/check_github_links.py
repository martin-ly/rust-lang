#!/usr/bin/env python3
"""检查 concept/ 中 github.com 链接的仓库是否存在（通过 raw.githubusercontent.com）."""
import re
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from urllib.parse import urlparse
import requests

ROOT = Path(__file__).resolve().parent.parent / "concept"
LINK_RE = re.compile(r'\[([^\]]+)\]\((https?://[^\)]+)\)')
TIMEOUT = 12
HEADERS = {
    'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36',
    'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8',
}


def collect():
    urls = {}
    for p in ROOT.rglob('*.md'):
        for label, url in LINK_RE.findall(p.read_text(encoding='utf-8', errors='ignore')):
            if urlparse(url).netloc != 'github.com':
                continue
            urls.setdefault(url, []).append(p.relative_to(ROOT).as_posix())
    return urls


def owner_repo(url: str):
    parsed = urlparse(url)
    parts = parsed.path.strip('/').split('/')
    if len(parts) < 2:
        return None
    return parts[0], parts[1]


def check_repo(owner: str, repo: str):
    # 尝试 raw README，404 表示仓库大概率不存在或为空
    raw_url = f'https://raw.githubusercontent.com/{owner}/{repo}/HEAD/README.md'
    try:
        r = requests.get(raw_url, headers=HEADERS, timeout=TIMEOUT)
        return r.status_code == 200
    except Exception:
        return False


def main():
    url_map = collect()
    # 按 owner/repo 去重
    repo_map = {}
    for url in url_map:
        or_ = owner_repo(url)
        if or_ is None:
            continue
        repo_map.setdefault(or_, []).append(url)

    print(f"检查 {len(repo_map)} 个 GitHub 仓库...\n")
    broken_repos = []
    with ThreadPoolExecutor(max_workers=6) as ex:
        futures = {ex.submit(check_repo, owner, repo): (owner, repo) for owner, repo in repo_map}
        for fut in as_completed(futures):
            owner, repo = futures[fut]
            ok = fut.result()
            if ok:
                print(f"OK {owner}/{repo}")
            else:
                print(f"FAIL {owner}/{repo}")
                broken_repos.append((owner, repo))

    print(f"\n不存在/异常的仓库: {len(broken_repos)}")
    if broken_repos:
        print("\n### 失效链接及涉及文件\n")
        for owner, repo in sorted(broken_repos):
            for url in sorted(repo_map[(owner, repo)]):
                files = sorted(set(url_map[url]))
                print(f"- `{url}`")
                for f in files[:5]:
                    print(f"  - `{f}`")


if __name__ == '__main__':
    main()
