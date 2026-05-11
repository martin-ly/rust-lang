#!/usr/bin/env python3
"""
执行实际修复的脚本
"""
import json
import re
from pathlib import Path

BASE_DIR = Path('e:/_src/rust-lang')
DOCS_DIR = BASE_DIR / 'docs'

# 读取 JSON 文件
with open('scripts/real_broken_links.json', 'r', encoding='utf-8') as f:
    data = json.load(f)

real_broken = data.get('real_broken', [])

fixed_count = 0
fixed_files = set()

def fix_in_file(file_rel, old_text, new_text, description=""):
    """在文件中替换文本"""
    global fixed_count, fixed_files
    
    file_path = DOCS_DIR / file_rel
    if not file_path.exists():
        return False
    
    try:
        content = file_path.read_text(encoding='utf-8')
        if old_text not in content:
            return False
        
        content = content.replace(old_text, new_text)
        file_path.write_text(content, encoding='utf-8')
        fixed_count += 1
        fixed_files.add(file_rel)
        if description:
            print(f"  ✓ {description}: {file_rel}")
        return True
    except Exception as e:
        print(f"  ✗ 错误 {file_rel}: {e}")
        return False

print("=" * 80)
print("执行链接修复")
print("=" * 80)

# 1. 修复 TERMINOLOGY_STANDARD.md 中的外部URL格式
print("\n1. 修复外部URL格式问题...")

# 修复类似 <https://...> text 的格式
terminology_fixes = [
    ('[§15.4](<https://spec.ferrocene.dev/ownership-and-destruction.html#> borrowing)',
     '[§15.4](https://spec.ferrocene.dev/ownership-and-destruction.html#borrowing)'),
    ('[§3.6](<https://spec.ferrocene.dev/items.html#derive-macro-> invocations)',
     '[§3.6](https://spec.ferrocene.dev/items.html#derive-macro-invocations)'),
    ('[§9.1](<https://spec.ferrocene.dev/functions.html#extern-function-> qualifier)',
     '[§9.1](https://spec.ferrocene.dev/functions.html#extern-function-qualifier)'),
]

for old, new in terminology_fixes:
    fix_in_file('TERMINOLOGY_STANDARD.md', old, new, "URL格式")

# 2. 修复 Rust所有权与可判定性/guides/drop-check-analysis.md
print("\n2. 修复 drop-check-analysis.md...")
fix_in_file(
    'Rust所有权与可判定性/guides/drop-check-analysis.md',
    '[RFC 1238 - Non-lexical lifetimes](<https://rust-lang.github.io/rfcs/1238-non> Lexical-lifetimes.html)',
    '[RFC 1238 - Non-lexical lifetimes](https://rust-lang.github.io/rfcs/1238-non-lexical-lifetimes.html)',
    "URL格式"
)

# 3. 修复占位符链接
print("\n3. 修复占位符链接...")

# research_notes/BEST_PRACTICES.md
fix_in_file(
    'research_notes/BEST_PRACTICES.md',
    '[文档名](path)',
    '`文档名` ⚠️ (链接待补充)',
    "占位符"
)

fix_in_file(
    'research_notes/BEST_PRACTICES.md',
    '[研究路线图](wrong/absolute/path/RESEARCH_ROADMAP.md)',
    '[研究路线图](./RESEARCH_ROADMAP.md)',
    "错误路径"
)

# research_notes/CONTENT_ENHANCEMENT.md
fix_in_file(
    'research_notes/CONTENT_ENHANCEMENT.md',
    '[xx](path/to/doc.md)',
    '`xx` ⚠️ (链接待补充)',
    "占位符"
)

fix_in_file(
    'research_notes/CONTENT_ENHANCEMENT.md',
    '[矩阵文档 §节名](path)',
    '`矩阵文档 §节名` ⚠️ (链接待补充)',
    "占位符"
)

# 4. 修复 archive/process_reports/2026_02/FORMAT_AND_CONTENT_ALIGNMENT_PLAN.md
print("\n4. 修复 archive/process_reports 中的占位符...")
for i in range(1, 5):  # 可能有多个
    fix_in_file(
        'archive/process_reports/2026_02/FORMAT_AND_CONTENT_ALIGNMENT_PLAN.md',
        '[文本](path)',
        '`文本` ⚠️ (链接待补充)',
        "占位符"
    )

# 5. 修复 archive/spell_check 中的占位符
print("\n5. 修复 spell_check 中的占位符...")
fix_in_file(
    'archive/spell_check/SPELL_CHECK_FINAL_COMPLETION.md',
    '[text](url)',
    '`text` ⚠️ (链接待补充)',
    "占位符"
)

fix_in_file(
    'archive/spell_check/SPELL_CHECK_SETUP_SUMMARY.md',
    '[text](url)',
    '`text` ⚠️ (链接待补充)',
    "占位符"
)

# 6. 修复 rust-ownership-decidability/CONTENT_TEMPLATE_L2.md 中的占位符
print("\n6. 修复 CONTENT_TEMPLATE_L2.md 中的占位符...")
template_fixes = [
    ('[The Rust Book - XXX](link)', '`The Rust Book - XXX` ⚠️ (链接待补充)'),
    ('[The Rust Reference - XXX](link)', '`The Rust Reference - XXX` ⚠️ (链接待补充)'),
    ('[论文标题](link)', '`论文标题` ⚠️ (链接待补充)'),
    ('[相关文档 A](../path/to/doc.md)', '`相关文档 A` ⚠️ (链接待补充)'),
    ('[相关文档 B](../path/to/doc.md)', '`相关文档 B` ⚠️ (链接待补充)'),
]

for old, new in template_fixes:
    fix_in_file('rust-ownership-decidability/CONTENT_TEMPLATE_L2.md', old, new, "占位符")

print("\n" + "=" * 80)
print(f"修复完成!")
print(f"  - 修复问题数: {fixed_count}")
print(f"  - 涉及文件数: {len(fixed_files)}")
print("=" * 80)

if fixed_files:
    print("\n已修复的文件:")
    for f in sorted(fixed_files):
        print(f"  - {f}")
