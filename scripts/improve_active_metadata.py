#!/usr/bin/env python3
"""为活跃概念文件生成更准确的 EN 标题（修正缩写）和更具描述性的 Summary."""
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent / "concept"

ACRONYMS = {
    'Ai': 'AI',
    'Cli': 'CLI',
    'Api': 'API',
    'Ecs': 'ECS',
    'Ebpf': 'eBPF',
    'Wasi': 'WASI',
    'Wasm': 'WebAssembly',
    'Rpitit': 'RPITIT',
    'Cpp': 'C++',
    'Csharp': 'C#',
    'Typescript': 'TypeScript',
    'Javascript': 'JavaScript',
    'Vs': 'vs',
    'And': 'and',
}

LAYER_TEMPLATES = {
    '01_foundation': '{en}: core Rust concepts, syntax, and examples.',
    '02_intermediate': '{en}: intermediate Rust mechanisms, patterns, and practical examples.',
    '03_advanced': '{en}: advanced Rust topics, performance/runtime considerations, and ecosystem patterns.',
    '04_formal': '{en}: formal methods foundations, semantics, and verification techniques relevant to Rust.',
    '05_comparative': '{en}: comparative analysis with Rust across type systems, memory safety, and concurrency.',
    '06_ecosystem': '{en}: Rust ecosystem tools, crates, and engineering practices.',
    '07_future': '{en}: emerging Rust language feature or ecosystem trend.',
}


def normalize_en(en: str) -> str:
    # 按词边界替换缩写；保留其他词首字母大写
    for old, new in ACRONYMS.items():
        en = re.sub(rf'\b{re.escape(old)}\b', new, en)
    # 清理多余空格
    return en.strip()


def is_generic_summary(s: str) -> bool:
    s = s.strip()
    return s.endswith('Core Rust concept.') or s.startswith('Guide to')


def main():
    for p in sorted(ROOT.rglob('*.md')):
        rel = p.relative_to(ROOT).as_posix()
        if 'archive/' in rel or 'sources/' in rel or rel.startswith('00_meta/') or 'quiz_' in rel or rel.endswith('README.md') or rel.endswith('SUMMARY.md'):
            continue
        layer = rel.split('/')[0]
        template = LAYER_TEMPLATES.get(layer)
        if not template:
            continue

        text = p.read_text(encoding='utf-8')
        en_m = re.search(r'^>\s*\*\*EN\*\*:\s*(.*?)$', text, re.MULTILINE)
        sum_m = re.search(r'^>\s*\*\*Summary\*\*:\s*(.*?)$', text, re.MULTILINE)
        if not en_m or not sum_m:
            continue

        en = en_m.group(1).strip()
        summary = sum_m.group(1).strip()
        new_en = normalize_en(en)
        changed = False

        if new_en != en:
            text = re.sub(
                r'^(>\s*\*\*EN\*\*:\s*).*?$',
                rf'\g<1>{new_en}',
                text,
                count=1,
                flags=re.MULTILINE,
            )
            changed = True

        if is_generic_summary(summary):
            new_summary = template.format(en=new_en)
            text = re.sub(
                r'^(>\s*\*\*Summary\*\*:\s*).*?$',
                rf'\g<1>{new_summary}',
                text,
                count=1,
                flags=re.MULTILINE,
            )
            changed = True

        if changed:
            p.write_text(text, encoding='utf-8')
            print(f"updated: {rel}")


if __name__ == '__main__':
    main()
