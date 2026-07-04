#!/usr/bin/env python3
"""审计 concept/ 下来源链接的权威性与具体性."""
import re
from pathlib import Path
from urllib.parse import urlparse

ROOT = Path(__file__).resolve().parent.parent / "concept"
LINK_RE = re.compile(r'\[([^\]]+)\]\((https?://[^\)]+)\)')

# 权威域名白名单（国际化权威来源）
AUTHORITY_DOMAINS = {
    'doc.rust-lang.org',
    'rust-lang.github.io',
    'blog.rust-lang.org',
    'www.rust-lang.org',
    'inside-rust-blog.org',
    'github.com',
    'crates.io',
    'docs.rs',
    'docs.kernel.org',
    'aya-rs.dev',
    'borrowsanitizer.com',
    # 国际学术与教材来源
    'arxiv.org',
    'doi.org',
    'plv.mpi-sws.org',
    'cel.cs.brown.edu',
    'rust-book.cs.brown.edu',
    'www.cis.upenn.edu',
    'en.wikipedia.org',
    'itanium-cxx-abi.github.io',
    'google.github.io',
    # 工业/生态库文档与官方博客
    'serde.rs',
    'without.boats',
    'rustc-dev-guide.rust-lang.org',
    # 标准组织与会议
    'www.unicode.org',
    'tools.ietf.org',
    'dl.acm.org',
    'pdos.csail.mit.edu',
    'pldi23.sigplan.org',
    'www.microsoft.com',
    # 领域权威教材/讲义
    'bartoszmilewski.com',
    'veykril.github.io',
    'os-checker.github.io',
    # 跨语言/工业/生态权威文档
    'llvm.org',
    'rust-for-linux.com',
    'model-checking.github.io',
    'ziglang.org',
    'docs.oracle.com',
    'docs.python.org',
    'kotlinlang.org',
    'docs.scala-lang.org',
    'docs.microsoft.com',
    'devblogs.microsoft.com',
    'elixir-lang.org',
    'www.erlang.org',
    'www.typescriptlang.org',
    'webassembly.github.io',
    'rustwasm.github.io',
    'oxc.rs',
    'swc.rs',
    'nodejs.org',
    'docs.github.com',
    'tc39.es',
    'www.rtca.org',
    # Rust 生态/工具链/社区权威站点
    'rust-analyzer.github.io',
    'rust-unofficial.github.io',
    'rocket.rs',
    'wasi.dev',
    'docs.rust-embedded.org',
    'rust-cli.github.io',
    'www.redox-os.org',
    'tikv.org',
    'creusot.rs',
    'choosealicense.com',
    'bevyengine.org',
    'docs.wasmtime.dev',
    'foundation.rust-lang.org',
    'releases.rs',
    'ferrocene.dev',
    'spec.ferrocene.dev',
    # 形式化验证项目官方站点
    'iris-project.org',
    'verus-lang.github.io',
    # 工业生态 GUI / 互操作官方站点
    'tauri.app',
    'dioxuslabs.com',
    'leptos.dev',
    'pyo3.rs',
    # 国际标准组织
    'www.iso.org',
    # 社区教材/参考（酌情放行）
    'basarat.gitbook.io',
}

# 根 URL 模式（不够具体）
ROOT_PATHS = {
    '/book/': 'TRPL root',
    '/reference/': 'Reference root',
    '/cargo/': 'Cargo Book root',
    '/edition-guide/': 'Edition Guide root',
    '/nomicon/': 'Nomicon root',
    '/rust-by-example/': 'RBE root',
    '/std/': 'std docs root',
    '/async-book/': 'Async Book root',
    '/rfcs/': 'RFCs root',
}


def main():
    rows = []
    for p in sorted(ROOT.rglob('*.md')):
        text = p.read_text(encoding='utf-8')
        m = re.search(r'^>\s*\*\*来源\*\*:\s*(.*?)$', text, re.MULTILINE)
        if not m:
            continue
        links = LINK_RE.findall(m.group(1))
        for label, url in links:
            parsed = urlparse(url)
            domain = parsed.netloc
            path = parsed.path
            is_authority = domain in AUTHORITY_DOMAINS
            generic = None
            for root_path, name in ROOT_PATHS.items():
                if path.rstrip('/') + '/' == root_path or path == root_path.rstrip('/'):
                    generic = name
                    break
            rows.append((p.relative_to(ROOT).as_posix(), label, url, domain, is_authority, generic))

    # 输出报告
    print("## 来源链接审计\n")
    print(f"总计链接数: {len(rows)}\n")

    non_auth = [r for r in rows if not r[4]]
    if non_auth:
        print(f"### 非权威域名（{len(non_auth)} 个）\n")
        for rel, label, url, domain, _, _ in non_auth[:30]:
            print(f"- `{rel}` → [{label}]({url}) (`{domain}`)")
        print()

    generic_links = [r for r in rows if r[5]]
    if generic_links:
        print(f"### 指向根 URL 不够具体的链接（{len(generic_links)} 个）\n")
        for rel, label, url, _, _, generic in generic_links[:50]:
            print(f"- `{rel}` → [{label}]({url}) (`{generic}`)")
        print()

    # 写详细 TSV（使用项目本地 tmp，兼容 Windows）
    out = Path(__file__).resolve().parent.parent / 'tmp' / 'source_audit.tsv'
    out.parent.mkdir(parents=True, exist_ok=True)
    with out.open('w', encoding='utf-8') as f:
        f.write('file\tlabel\turl\tdomain\tis_authority\tgeneric_root\n')
        for r in rows:
            f.write('\t'.join(map(str, r)) + '\n')
    print(f"详细清单: {out}")


if __name__ == '__main__':
    main()
