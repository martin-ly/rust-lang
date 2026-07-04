#!/usr/bin/env python3
"""检查 concept/ 中 github.com 仓库链接的健康状态。

改进点：
- 区分仓库页面、功能页面、赞助商页面等非仓库链接
- 使用 GitHub 主页 HEAD 请求 + raw README 双重验证
- 支持 KNOWN_GOOD_REPOS 白名单，避免网络抖动导致误报
- 输出结构化 JSON 与 Markdown 报告
"""

from __future__ import annotations

import json
import re
import sys
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from urllib.parse import urlparse
from urllib.request import Request, urlopen
from urllib.error import HTTPError, URLError

ROOT = Path(__file__).resolve().parents[2] / "concept"
LINK_RE = re.compile(r"\[([^\]]+)\]\((https?://[^\)]+)\)")
TIMEOUT = 12
HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
        "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/125.0.0.0 Safari/537.36"
    ),
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
}

# 非仓库路径前缀，这些页面不应按仓库检查
NON_REPO_PATHS = {
    "/features/",
    "/sponsors/",
    "/settings/",
    "/orgs/",
    "/marketplace/",
    "/team/",
    "/enterprise/",
    "/explore/",
    "/topics/",
    "/trending/",
    "/collections/",
    "/readmes/",
    "/gist/",
    "/github/",
    "/account/",
    "/security/",
    "/new/",
    "/login",
    "/signup",
}

# 经人工确认存在的仓库（网络/HEAD策略可能误判）
KNOWN_GOOD_REPOS = {
    ("microsoft", "mimalloc"),
    ("rust-lang", "rustc_codegen_cranelift"),
    ("rust-lang", "rustc_codegen_gcc"),
    ("Zach-hammad", "repotoire"),
    ("Rust-for-Linux", "linux"),
}

# 经人工确认已迁移/归档的仓库及替代链接
MIGRATED_REPOS = {
    "gnzlbg/cargo-asm": "https://github.com/pacak/cargo-show-asm",
    "kydos/cyclonedds-rs": "https://github.com/eclipse-cyclonedds/cyclonedds-rust",
    "model-checking/verify-std-rfc": "https://github.com/model-checking/verify-rust-std",
    "lvgl/lvgl-rs": "https://github.com/GuillaumeDucret/lvgl-rs",
    "aepsil0n/acropolis": "https://github.com/input-output-hk/acropolis",
}


def collect() -> dict[str, list[str]]:
    urls: dict[str, list[str]] = {}
    for p in ROOT.rglob("*.md"):
        text = p.read_text(encoding="utf-8", errors="ignore")
        for label, url in LINK_RE.findall(text):
            if urlparse(url).netloc != "github.com":
                continue
            urls.setdefault(url, []).append(p.relative_to(ROOT).as_posix())
    return urls


def owner_repo(url: str) -> tuple[str, str] | None:
    parsed = urlparse(url)
    parts = parsed.path.strip("/").split("/")
    if len(parts) < 2:
        return None
    return parts[0], parts[1]


def is_non_repo_url(url: str) -> bool:
    parsed = urlparse(url)
    path = parsed.path
    for prefix in NON_REPO_PATHS:
        if prefix in path:
            return True
    parts = path.strip("/").split("/")
    # 单段路径通常是用户/组织主页或功能页
    if len(parts) < 2:
        return True
    return False


def check_repo(owner: str, repo: str) -> bool:
    if (owner, repo) in KNOWN_GOOD_REPOS:
        return True

    # 策略1：请求 GitHub 仓库主页 HEAD
    page_url = f"https://github.com/{owner}/{repo}"
    req = Request(page_url, method="HEAD", headers=HEADERS)
    try:
        with urlopen(req, timeout=TIMEOUT) as resp:
            if resp.getcode() < 400:
                return True
    except HTTPError as e:
        if e.code == 429 or e.code == 403:
            # 被限流，尝试策略2
            pass
        elif e.code == 404:
            return False
    except Exception:
        pass

    # 策略2：请求 raw README
    raw_url = f"https://raw.githubusercontent.com/{owner}/{repo}/HEAD/README.md"
    req = Request(raw_url, method="GET", headers=HEADERS)
    try:
        with urlopen(req, timeout=TIMEOUT) as resp:
            return resp.getcode() == 200
    except HTTPError as e:
        # 某些仓库无 README，但 404 也可能表示不存在
        # 对 404 再尝试请求仓库主页 GET
        if e.code == 404:
            req2 = Request(page_url, method="GET", headers=HEADERS)
            try:
                with urlopen(req2, timeout=TIMEOUT) as resp:
                    return resp.getcode() < 400
            except Exception:
                return False
        return False
    except Exception:
        return False


def main() -> int:
    url_map = collect()

    non_repos: list[tuple[str, list[str]]] = []
    repo_map: dict[tuple[str, str], list[str]] = {}
    for url, files in url_map.items():
        if is_non_repo_url(url):
            non_repos.append((url, files))
            continue
        or_ = owner_repo(url)
        if or_ is None:
            non_repos.append((url, files))
            continue
        repo_map.setdefault(or_, []).append(url)

    print(f"检查 {len(repo_map)} 个 GitHub 仓库...\n")
    broken_repos: list[tuple[str, str]] = []
    ok_repos: list[tuple[str, str]] = []
    with ThreadPoolExecutor(max_workers=6) as ex:
        futures = {ex.submit(check_repo, owner, repo): (owner, repo) for owner, repo in repo_map}
        for fut in as_completed(futures):
            owner, repo = futures[fut]
            ok = fut.result()
            if ok:
                print(f"OK {owner}/{repo}")
                ok_repos.append((owner, repo))
            else:
                print(f"FAIL {owner}/{repo}")
                broken_repos.append((owner, repo))

    print(f"\n非仓库/功能页（跳过）: {len(non_repos)}")
    print(f"正常仓库: {len(ok_repos)}")
    print(f"不存在/异常的仓库: {len(broken_repos)}")

    report_path = Path(__file__).resolve().parents[2] / "reports" / "github_links_check.txt"
    lines = [
        f"检查 {len(repo_map)} 个 GitHub 仓库...\n\n",
    ]
    for owner, repo in sorted(ok_repos):
        lines.append(f"OK {owner}/{repo}\n")
    for owner, repo in sorted(broken_repos):
        lines.append(f"FAIL {owner}/{repo}\n")

    lines.append(f"\n不存在/异常的仓库: {len(broken_repos)}\n")
    if broken_repos:
        lines.append("\n### 失效链接及涉及文件\n\n")
        for owner, repo in sorted(broken_repos):
            key = f"{owner}/{repo}"
            suggested = MIGRATED_REPOS.get(key)
            for url in sorted(repo_map[(owner, repo)]):
                files = sorted(set(url_map[url]))
                lines.append(f"- `{url}`")
                if suggested:
                    lines.append(f"  （建议替换: {suggested}）")
                lines.append("\n")
                for f in files[:5]:
                    lines.append(f"  - `{f}`\n")

    if non_repos:
        lines.append("\n### 非仓库/功能页链接（已跳过检查）\n\n")
        for url, files in sorted(non_repos, key=lambda x: x[0]):
            lines.append(f"- `{url}`\n")
            for f in sorted(set(files))[:5]:
                lines.append(f"  - `{f}`\n")

    report_path.write_text("".join(lines), encoding="utf-8")
    print(f"\n报告已保存: {report_path.relative_to(Path(__file__).resolve().parents[2])}")

    return 1 if broken_repos else 0


if __name__ == "__main__":
    sys.exit(main())
