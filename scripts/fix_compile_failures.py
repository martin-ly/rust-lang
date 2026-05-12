#!/usr/bin/env python3
"""批量修复编译失败的代码块标记"""

import re, sys
from pathlib import Path

TMP_DIR = Path('target/tmp/code_block_tests')
EXTERNAL_CRATES = {
    'tokio', 'futures', 'anyhow', 'thiserror', 'libc', 'rayon',
    'parking_lot', 'dashmap', 'clap', 'cortex_m_rt', 'libloading',
    'tokio_stream', 'bevy', 'serde', 'reqwest', 'actix', 'axum',
    'criterion', 'proptest', 'quickcheck', 'wasm_bindgen', 'pyo3',
    'napi', 'tonic', 'tarpc', 'tide', 'rocket', 'warp',
}

def find_md_file(base_name):
    """根据测试文件名找到原始 markdown 文件"""
    for root in Path('concept').rglob('*.md'):
        if root.stem == base_name:
            return root
    # 尝试前缀匹配
    for root in Path('concept').rglob('*.md'):
        if base_name.startswith(root.stem) or root.stem.startswith(base_name):
            return root
    return None

def extract_block_at_line(content, line_num):
    """提取指定行号的代码块围栏"""
    lines = content.split('\n')
    idx = line_num - 1
    if idx < 0 or idx >= len(lines):
        return None
    if not lines[idx].startswith('```'):
        return None
    return lines[idx].strip()

def categorize(stderr, code, fence):
    """返回 (action, reason, new_fence)"""
    # 外部 crate
    for crate in EXTERNAL_CRATES:
        if f"cannot find module or crate `{crate}`" in stderr:
            return 'ignore', f'外部 crate: {crate}', 'rust,ignore'
        if f"unresolved import `{crate}" in stderr:
            return 'ignore', f'外部 crate: {crate}', 'rust,ignore'
    
    # 故意错误 (反例)
    has_anti = '❌ 反例' in code or '反例:' in code or ('编译错误' in code and 'error[' in stderr)
    if has_anti and 'error[' in stderr:
        return 'compile_fail', '故意编译错误', 'rust,compile_fail'
    
    # 过程宏
    if 'proc_macro_derive' in stderr:
        return 'ignore', '过程宏需要 proc-macro crate', 'rust,ignore'
    
    # const generics 限制
    if 'generic parameters may not be used in const operations' in stderr:
        return 'ignore', 'const generics 当前限制', 'rust,ignore'
    
    # Effects 语法
    if 'effect ' in code.lower() and 'expected one of' in stderr:
        return 'ignore', 'Effects 概念语法', 'rust,ignore'
    
    # Verus
    if 'proof fn' in code:
        return 'ignore', 'Verus 形式化代码', 'rust,ignore'
    
    # GAT 缺失 bounds
    if 'missing required bound' in stderr:
        return 'ignore', 'GAT 概念代码', 'rust,ignore'
    
    # 片段：注释在 impl 内
    if 'non-item in item list' in stderr:
        if any(l.strip().startswith('// ') for l in code.split('\n')[:3]):
            return 'ignore', '片段（注释混入 impl）', 'rust,ignore'
    
    # 全角标点
    if 'unknown start of token' in stderr:
        if '\uff0c' in code or '\u3002' in code or '\u3001' in code:
            return 'ignore', '含全角标点', 'rust,ignore'
    
    # trait 方法片段
    if '`self` parameter is only allowed in associated functions' in stderr:
        return 'ignore', 'trait 方法片段', 'rust,ignore'
    
    # 不完整签名
    if 'expected one of' in stderr and ('found `}`' in stderr or 'found `)`' in stderr):
        return 'ignore', '不完整函数签名', 'rust,ignore'
    
    # 缺少生命周期（片段）
    if 'missing lifetime specifier' in stderr and len(code.strip().split('\n')) <= 4:
        return 'ignore', '缺少生命周期的片段', 'rust,ignore'
    
    # 递归类型（故意）
    if 'recursive type' in stderr and 'has infinite size' in stderr:
        if '❌' in code or '反例' in code:
            return 'compile_fail', '故意展示递归类型错误', 'rust,compile_fail'
        return 'ignore', '递归类型片段', 'rust,ignore'
    
    # 孤儿规则（故意）
    if 'only traits defined in the current crate' in stderr:
        return 'compile_fail', '故意展示孤儿规则', 'rust,compile_fail'
    
    # 冲突实现（故意）
    if 'conflicting implementations' in stderr:
        return 'compile_fail', '故意展示冲突实现', 'rust,compile_fail'
    
    # 移动后借用（故意）
    if ('borrow of moved value' in stderr or 'cannot borrow' in stderr):
        if '❌' in code or '反例' in code or 'cannot' in code:
            return 'compile_fail', '故意展示借用错误', 'rust,compile_fail'
    
    # 非穷尽匹配（故意）
    if 'non-exhaustive patterns' in stderr:
        if '❌' in code or '反例' in code:
            return 'compile_fail', '故意展示非穷尽匹配', 'rust,compile_fail'
        return 'ignore', '非穷尽匹配片段', 'rust,ignore'
    
    # 缺少定义（短片段）
    if ('cannot find type' in stderr or 'cannot find function' in stderr or 'cannot find value' in stderr):
        lines = code.strip().split('\n')
        if len(lines) <= 3:
            return 'ignore', '缺少定义的短片段', 'rust,ignore'
    
    # 默认
    return 'manual', '需要人工审查', None

def main():
    if not TMP_DIR.exists():
        print("请先运行 code_block_compiler.py")
        sys.exit(1)
    
    fixes_by_file = {}
    manual = []
    
    for stderr_file in sorted(TMP_DIR.glob('*.stderr')):
        rs_file = stderr_file.with_suffix('.rs')
        if not rs_file.exists():
            continue
        
        # 解析文件名: {name}_L{line}.rs
        m = re.match(r'(.+)_L(\d+)$', rs_file.stem)
        if not m:
            continue
        
        base_name = m.group(1)
        line_num = int(m.group(2))
        stderr = stderr_file.read_text(encoding='utf-8')
        
        # 跳过只有 warning 的成功编译
        if 'error[' not in stderr and 'error:' not in stderr:
            continue
        
        wrapped = rs_file.read_text(encoding='utf-8')
        
        md_file = find_md_file(base_name)
        if not md_file:
            manual.append(f"找不到文件: {base_name} L{line_num}")
            continue
        
        content = md_file.read_text(encoding='utf-8')
        old_fence = extract_block_at_line(content, line_num)
        if not old_fence:
            manual.append(f"找不到代码块: {md_file}:{line_num}")
            continue
        
        # 获取原始代码（未包裹的）
        # 从 markdown 提取
        lines = content.split('\n')
        code_lines = []
        j = line_num  # 0-indexed: line_num - 1 + 1
        while j < len(lines) and not lines[j].startswith('```'):
            code_lines.append(lines[j])
            j += 1
        original_code = '\n'.join(code_lines)
        
        action, reason, new_fence = categorize(stderr, original_code, old_fence)
        
        if action == 'manual':
            # 输出前 100 字节的 stderr 用于判断
            preview = stderr[:200].replace('\n', ' ')
            manual.append(f"{md_file.name}:{line_num} {old_fence} → ? ({reason}) | {preview}")
            continue
        
        key = str(md_file)
        if key not in fixes_by_file:
            fixes_by_file[key] = []
        fixes_by_file[key].append((line_num, old_fence, new_fence, reason))
    
    # 应用修复
    total = 0
    for md_path, changes in fixes_by_file.items():
        content = Path(md_path).read_text(encoding='utf-8')
        lines = content.split('\n')
        
        for line_num, old_fence, new_fence, reason in sorted(changes, key=lambda x: x[0], reverse=True):
            idx = line_num - 1
            if idx < len(lines):
                current = lines[idx].strip()
                if current == old_fence or current.startswith('```rust'):
                    lines[idx] = new_fence
                    total += 1
                    print(f"  {Path(md_path).name}:{line_num} → {new_fence} ({reason})")
        
        Path(md_path).write_text('\n'.join(lines), encoding='utf-8')
    
    print(f"\n自动修复 {total} 个代码块")
    
    if manual:
        print(f"\n需要人工审查 {len(manual)} 个:")
        for m in manual[:30]:
            print(f"  {m}")
        if len(manual) > 30:
            print(f"  ... 还有 {len(manual)-30} 个")

if __name__ == '__main__':
    main()
