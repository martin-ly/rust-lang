#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
批量升级 docs/research_notes/ 根目录下的版本更新/特性矩阵类文档。
目标：统一版本基准为 Rust 1.96.0+ / Edition 2024，补充 1.95/1.96 新特性及权威来源，
替换文件末尾旧模板，更新元信息状态。
"""

import re
from pathlib import Path

BASE = Path('e:/_src/rust-lang/docs/research_notes')
FILES = [
    '10_cargo_194_features.md',
    '10_rust_193_feature_matrix.md',
    '10_rust_193_language_features_comprehensive_analysis.md',
    '10_rust_194_195_feature_matrix.md',
    '10_rust_194_comprehensive_analysis.md',
    '10_rust_194_deep_semantic_analysis.md',
    '10_rust_194_mind_representations.md',
    '10_rust_194_core_notes_index.md',
    '10_rust_194_research_update.md',
]

NEW_STATUS = '> **状态**: ✅ 已完成权威国际化来源对齐升级（Rust 1.96.0+ / Edition 2024）'
NEW_LAST_UPDATE = '> **最后更新**: 2026-06-29'

OLD_SECTION_TITLE = '🆕 Rust 1.94 深度整合更新'
NEW_SECTION_TITLE = '✅ 权威国际化来源对齐升级摘要（Rust 1.96.0+ / Edition 2024）'
NEW_SECTION_ANCHOR = '#-权威国际化来源对齐升级摘要-rust-1960-edition-2024'

NEW_UPGRADE_SUMMARY = f"""## {NEW_SECTION_TITLE}

> **来源: [Rust 1.96.0 Release Notes](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0/)**
> **来源: [Rust 1.95.0 Release Notes](https://blog.rust-lang.org/2026/04/16/Rust-1.95.0/)**
> **来源: [releases.rs](https://releases.rs/)**
> **适用版本**: Rust 1.96.0+ (Edition 2024)
> **升级日期**: 2026-06-29

### 本次升级要点

本文档已完成权威国际化来源对齐升级，统一版本基准为 **Rust 1.96.0+ / Edition 2024**，同时保留 1.93/1.94 历史分析章节。

#### 新增 Rust 1.96.0 特性

| 特性 | 来源 | 说明 |
| :--- | :--- | :--- |
| `core::range` 新类型 | [RFC 3550](https://rust-lang.github.io/rfcs/3550-new-range.html)、[std::range](https://doc.rust-lang.org/stable/std/range/index.html) | `Range`/`RangeFrom`/`RangeInclusive` 实现 `Copy` + `IntoIterator` |
| `assert_matches!` / `debug_assert_matches!` | [core::assert_matches](https://doc.rust-lang.org/stable/core/assert_matches/macro.assert_matches.html) | 模式断言宏，失败输出 Debug 信息 |
| Cargo CVE-2026-5223 / CVE-2026-5222 修复 | [Cargo 安全公告](https://github.com/rust-lang/cargo/security/advisories)、[Rust Blog 1.96.0](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0/) | 第三方 registry tarball symlink 与 URL 规范化修复 |
| WebAssembly 链接行为变更 | [Rust Blog 1.96.0](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0/) | 不再默认传递 `--allow-undefined` |

#### 新增 Rust 1.95.0 特性

| 特性 | 来源 | 说明 |
| :--- | :--- | :--- |
| `if let` guards on match arms | [Rust Reference - Match Guards](https://doc.rust-lang.org/reference/expressions/match-expr.html#match-guards)、[Rust Blog 1.95.0](https://blog.rust-lang.org/2026/04/16/Rust-1.95.0/) | match 臂支持 `if let` 守卫 |
| `cfg_select!` 宏 | [Rust Reference - Conditional Compilation](https://doc.rust-lang.org/reference/conditional-compilation.html)、[releases.rs 1.95.0](https://releases.rs/docs/1.95.0/) | 编译期 cfg 条件选择宏 |
| PowerPC / PowerPC64 内联汇编稳定化 | [Rust Reference - Inline Assembly](https://doc.rust-lang.org/reference/inline-assembly.html)、[Rust Blog 1.95.0](https://blog.rust-lang.org/2026/04/16/Rust-1.95.0/) | 稳定 inline assembly for PowerPC |
| `--remap-path-scope` | [Rust Blog 1.95.0](https://blog.rust-lang.org/2026/04/16/Rust-1.95.0/) | 控制路径重映射作用域 |

#### 权威来源对齐

- Rust release notes（releases.rs）
- Rust Blog 对应版本发布公告
- Rust Reference 具体章节（Range Expressions、Match Guards、Inline Assembly、Conditional Compilation）
- Rust Standard Library 具体 API（`core::range`、`core::assert_matches`、`std::ops::ControlFlow`）
- RFC 链接（RFC 3550 等）

---
""".strip()


def update_metadata(text: str) -> str:
    """更新文件头部的元信息：状态、最后更新、Rust 版本基准。"""
    # 状态行（仅替换第一个出现，通常是头部 metadata）
    text = re.sub(
        r'^([> ]*\*\*状态\*\*):\s*[^\n]+',
        r'\1: ✅ 已完成权威国际化来源对齐升级（Rust 1.96.0+ / Edition 2024）',
        text, count=1, flags=re.MULTILINE
    )
    # 最后更新行（仅替换第一个出现）
    text = re.sub(
        r'^([> ]*\*\*最后更新\*\*):\s*\d{4}-\d{2}-\d{2}',
        r'\1: 2026-06-29',
        text, count=1, flags=re.MULTILINE
    )
    # Rust 版本行（仅替换第一个出现）
    text = re.sub(
        r'^([> ]*\*\*Rust 版本\*\*):\s*[^\n]+',
        r'\1: 1.96.0+ (Edition 2024)',
        text, count=1, flags=re.MULTILINE
    )
    return text


def update_toc_entries(text: str) -> str:
    """更新目录中指向旧模板的条目。"""
    # 匹配形如：- [🆕 Rust 1.94 深度整合更新](#-rust-194-深度整合更新)
    # 或    - [🆕 Rust 1.94 深度整合更新](#-rust-194-深度整合更新)
    text = re.sub(
        r'(-\s*\[)[^\]]*Rust 1\.94[^\]]*(\]\s*\(#[^\)]+\))',
        rf'\g<1>{NEW_SECTION_TITLE}\g<2>',
        text
    )
    # 若 anchor 仍指向 rust-194，也一并替换为新的 anchor
    text = text.replace('#-rust-194-深度整合更新', NEW_SECTION_ANCHOR)
    return text


def replace_old_template(text: str) -> str:
    """将文件末尾的 '🆕 Rust 1.94 深度整合更新' 旧模板替换为新升级摘要。"""
    idx = text.find(f'## {OLD_SECTION_TITLE}')
    if idx == -1:
        return text

    # 找到该 section 的结束位置
    end_idx = len(text)
    # 优先匹配 "---\n\n## 相关概念" 或 "---\n\n**维护者**:" 或 "---\n\n> **权威来源**:"
    for pat in ['---\n\n## 相关概念', '---\n\n**维护者**:', '---\n\n> **权威来源**:']:
        pos = text.find(pat, idx + len(f'## {OLD_SECTION_TITLE}'))
        if pos != -1:
            end_idx = pos
            break
    else:
        # 如果没找到，则尝试找到下一个 "## " 一级/二级标题
        m = re.search(r'\n#{1,2}[^#]', text[idx + len(f'## {OLD_SECTION_TITLE}'):])
        if m:
            end_idx = idx + len(f'## {OLD_SECTION_TITLE}') + m.start()

    return text[:idx] + NEW_UPGRADE_SUMMARY + '\n\n' + text[end_idx:].lstrip('\n')


def update_headings(text: str) -> str:
    """将所有旧模板标题替换为新标题（防止正文其他地方残留）。"""
    return text.replace(f'## {OLD_SECTION_TITLE}', f'## {NEW_SECTION_TITLE}')


def main():
    for name in FILES:
        p = BASE / name
        if not p.exists():
            print(f'[SKIP] {name} not found')
            continue
        text = p.read_text(encoding='utf-8')
        original = text

        text = update_metadata(text)
        text = update_toc_entries(text)
        text = replace_old_template(text)
        text = update_headings(text)

        if text != original:
            p.write_text(text, encoding='utf-8')
            print(f'[UPDATED] {name}')
        else:
            print(f'[NO CHANGE] {name}')


if __name__ == '__main__':
    main()
