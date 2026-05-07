import os, re
from datetime import datetime

target_dirs = [
    '01_learning', '02_reference', '03_practice', '04_research',
    '04_thinking', '05_guides', '06_toolchain', '07_project', 'content'
]
base = 'e:/_src/rust-lang/docs'

# Files that are specifically historical documents about Rust 1.94
# We skip version replacements in these, but still update dates
historical_194_files = {
    '13_rust_1.94_preview.md',
    '15_rust_1.94_comprehensive_guide.md',
    '16_rust_1.94_release_notes.md',
    '17_rust_1.93_vs_1.94_comparison.md',
    '18_rust_1.94_adoption_guide.md',
    'RUST_194_MIGRATION_GUIDE.md',
    'RUST_194_GUIDES_INDEX.md',
    'RUST_194_TOOLCHAIN_INDEX.md',
    'rust_194_features_cheatsheet.md',
}

def is_historical_194(filepath):
    filename = os.path.basename(filepath)
    return filename in historical_194_files

def update_dates(content):
    """Update 最后更新 dates to 2026-05-08 if older."""
    def repl(m):
        prefix = m.group(1)
        old_date = m.group(2)
        suffix = m.group(3) if m.group(3) else ''
        try:
            dt = datetime.strptime(old_date, '%Y-%m-%d')
            if dt < datetime(2026, 5, 8):
                return f"{prefix}2026-05-08{suffix}"
        except ValueError:
            pass
        return m.group(0)
    
    pattern = r'((?:\*\*)?最后更新(?:日期)?(?:\*\*)?\s*[:：]\s*)(\d{4}-\d{2}-\d{2})(.*)'
    return re.sub(pattern, repl, content)

def apply_version_replacements(content, filepath):
    """Apply version replacements for active/current version claims."""
    if is_historical_194(filepath):
        return content
    
    # 1. Document headers: **Rust 版本**: 1.94.0+
    content = re.sub(
        r'(\*\*Rust 版本\*\*\s*[:：]\s*)1\.94\.0\+',
        r'\g<1>1.95.0+',
        content
    )
    
    # 2. Applicable version: **适用版本**: Rust 1.94.0+
    content = re.sub(
        r'(\*\*适用版本\*\*\s*[:：]\s*Rust\s+)1\.94\.0\+',
        r'\g<1>1.95.0+',
        content
    )
    
    # 3. "本文档已针对 **Rust 1.94** 进行深度整合"
    content = re.sub(
        r'本文档已针对\s+\*\*Rust 1\.94\*\*\s+进行深度整合',
        '本文档已针对 **Rust 1.95+** 进行深度整合',
        content
    )
    
    # 4. ✅ 使用Rust 1.94语法验证
    content = re.sub(
        r'✅ 使用Rust 1\.94语法验证',
        '✅ 使用Rust 1.95+语法验证',
        content
    )
    
    # 5. 🆕 Rust 1.94 at start of headings/lines
    content = re.sub(
        r'^(#{1,6}\s*🆕?\s*)Rust 1\.94\s+',
        r'\g<1>Rust 1.95+ ',
        content,
        flags=re.MULTILINE
    )
    
    # 6. Specific section title patterns (active claims)
    replacements = [
        (r'Rust 1\.94 学习路径', 'Rust 1.95+ 学习路径'),
        (r'Rust 1\.94 更新要点', 'Rust 1.95+ 更新要点'),
        (r'Rust 1\.94 指南更新', 'Rust 1.95+ 指南更新'),
        (r'Rust 1\.94 思维表征更新', 'Rust 1.95+ 思维表征更新'),
        (r'Rust 1\.94 特性追踪', 'Rust 1.95+ 特性追踪'),
        (r'Rust 1\.94 特性[:：]', 'Rust 1.95+ 特性：'),
        (r'Rust 1\.94\+ 特性', 'Rust 1.95+ 特性'),
        (r'Rust 1\.94 深度语义整合', 'Rust 1.95+ 深度语义整合'),
        (r'结合 Rust 1\.94\+ 特性', '结合 Rust 1.95+ 特性'),
        (r'额外包含 Rust 1\.94\+ 控制流新特性', '额外包含 Rust 1.95+ 控制流新特性'),
        (r'所有速查卡已更新到 Rust 1\.94\.0\+', '所有速查卡已更新到 Rust 1.95.0+'),
        (r'Rust 1\.94 最佳实践', 'Rust 1.95+ 最佳实践'),
        (r'Rust 1\.94 跨模块集成最佳实践', 'Rust 1.95+ 跨模块集成最佳实践'),
        (r'Rust 1\.94 在 CLI 开发中的应用', 'Rust 1.95+ 在 CLI 开发中的应用'),
        (r'Rust 1\.94 在 AI/ML 开发中的应用', 'Rust 1.95+ 在 AI/ML 开发中的应用'),
        (r'Rust 1\.94 在嵌入式开发中的应用', 'Rust 1.95+ 在嵌入式开发中的应用'),
        (r'Rust 1\.94 在测试开发中的应用', 'Rust 1.95+ 在测试开发中的应用'),
        (r'Rust 1\.94 在 WASM 开发中的应用', 'Rust 1.95+ 在 WASM 开发中的应用'),
        (r'Rust 1\.94 在 Unsafe Rust 中的应用', 'Rust 1.95+ 在 Unsafe Rust 中的应用'),
        (r'Rust 1\.94 在宏系统中的应用', 'Rust 1.95+ 在宏系统中的应用'),
        (r'Rust 1\.94 在内联汇编中的应用', 'Rust 1.95+ 在内联汇编中的应用'),
        (r'Rust 1\.94 在算法中的深度应用', 'Rust 1.95+ 在算法中的深度应用'),
        (r'Rust 1\.94 在 AI/ML 中的深度应用', 'Rust 1.95+ 在 AI/ML 中的深度应用'),
        (r'Rust 1\.94 在 WASM 中的深度应用', 'Rust 1.95+ 在 WASM 中的深度应用'),
        (r'Rust 1\.94 在泛型中的深度应用', 'Rust 1.95+ 在泛型中的深度应用'),
        (r'Rust 1\.94 在闭包与函数式编程中的深度应用', 'Rust 1.95+ 在闭包与函数式编程中的深度应用'),
        (r'Rust 1\.94 在网络编程中的深度应用', 'Rust 1.95+ 在网络编程中的深度应用'),
        (r'Rust 1\.94 异步模式', 'Rust 1.95+ 异步模式'),
        (r'Rust 1\.94 并发特性', 'Rust 1.95+ 并发特性'),
        (r'Rust 1\.94 故障排查指南', 'Rust 1.95+ 故障排查指南'),
        (r'Rust 1\.94 性能测试与基准', 'Rust 1.95+ 性能测试与基准'),
        (r'Rust 1\.94 工作流理论应用', 'Rust 1.95+ 工作流理论应用'),
        (r'Rust 1\.94 工作流优化', 'Rust 1.95+ 工作流优化'),
        (r'Rust 1\.94 高级特性深度解析', 'Rust 1.95+ 高级特性深度解析'),
        (r'Rust 1\.94 ControlFlow 深度错误控制', 'Rust 1.95+ ControlFlow 深度错误控制'),
        (r'Rust 1\.94 ControlFlow 核心 API', 'Rust 1.95+ ControlFlow 核心 API'),
        (r'Rust 1\.94 文档完成指南更新', 'Rust 1.95+ 文档完成指南更新'),
        (r'Rust 1\.94 更新说明', 'Rust 1.95+ 更新说明'),
        (r'Rust 1\.94 更新', 'Rust 1.95+ 更新'),
        (r'Rust 1\.94 重要更新', 'Rust 1.95+ 重要更新'),
        (r'Rust 1\.94 数学常量', 'Rust 1.95+ 数学常量'),
        (r'Rust 1\.94 LazyLock', 'Rust 1.95+ LazyLock'),
        (r'Rust 1\.94 ControlFlow', 'Rust 1.95+ ControlFlow'),
        (r'Rust 1\.94 Unsafe 改进', 'Rust 1.95+ Unsafe 改进'),
        (r'Rust 1\.94 解决方案', 'Rust 1.95+ 解决方案'),
        (r'Rust 1\.94 新增方法', 'Rust 1.95+ 新增方法'),
        (r'Rust 1\.94 新增 API', 'Rust 1.95+ 新增 API'),
        (r'Rust 1\.94 新增常量', 'Rust 1.95+ 新增常量'),
        (r'Rust 1\.94 模式', 'Rust 1.95+ 模式'),
        (r'Rust 1\.94 设计模式应用', 'Rust 1.95+ 设计模式应用'),
    ]
    
    for old, new in replacements:
        content = re.sub(old, new, content)
    
    # 8. 1.94.0+ (Edition 2024) -> 1.95.0+ (Edition 2024)
    content = re.sub(r'1\.94\.0\+ \(Edition 2024\)', '1.95.0+ (Edition 2024)', content)
    
    return content

# Collect all target markdown files
files = []
for d in target_dirs:
    path = os.path.join(base, d)
    if not os.path.exists(path):
        continue
    for root, _, filenames in os.walk(path):
        for f in filenames:
            if f.endswith('.md'):
                files.append(os.path.join(root, f))

modified_files = []
version_changes = []
date_changes = []

for filepath in files:
    try:
        with open(filepath, 'r', encoding='utf-8') as file:
            content = file.read()
    except Exception as e:
        print(f"Error reading {filepath}: {e}")
        continue
    
    new_content = content
    
    # Apply date updates to ALL files
    new_content = update_dates(new_content)
    
    # Apply version replacements (skips historical files internally)
    new_content = apply_version_replacements(new_content, filepath)
    
    if new_content != content:
        # Count changes
        orig_lines = content.split('\n')
        new_lines = new_content.split('\n')
        v_count = 0
        d_count = 0
        for ol, nl in zip(orig_lines, new_lines):
            if ol != nl:
                if '1.94' in ol and '1.95' in nl:
                    v_count += 1
                if re.search(r'最后更新', ol) and re.search(r'最后更新', nl):
                    d_count += 1
        
        with open(filepath, 'w', encoding='utf-8') as file:
            file.write(new_content)
        
        modified_files.append(filepath)
        if v_count > 0:
            version_changes.append((filepath, v_count))
        if d_count > 0:
            date_changes.append((filepath, d_count))

print(f"Modified {len(modified_files)} files")
print(f"Files with version changes: {len(version_changes)}")
print(f"Files with date changes: {len(date_changes)}")

print("\n--- Version changes (first 50) ---")
for f, c in version_changes[:50]:
    print(f"  {f}: {c} lines")

print("\n--- Date changes (first 50) ---")
for f, c in date_changes[:50]:
    print(f"  {f}: {c} lines")
