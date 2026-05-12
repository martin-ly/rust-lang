#!/usr/bin/env python3
"""自动分类编译失败的代码块并建议标记修正"""

import re, json, sys
from pathlib import Path

# 外部 crate 列表（需要标记 ignore）
EXTERNAL_CRATES = {
    'tokio', 'futures', 'anyhow', 'thiserror', 'libc', 'rayon', 
    'parking_lot', 'dashmap', 'clap', 'cortex_m_rt', 'libloading',
    'tokio_stream', 'bevy', 'serde', 'reqwest', 'actix', 'axum',
    'criterion', 'proptest', 'quickcheck', 'wasm_bindgen', 'pyo3',
    'napi', 'tonic', 'tarpc', 'tide', 'rocket', 'warp',
}

# 编译错误模式 → 建议标记
def categorize_error(stderr, code, fence):
    stderr_lower = stderr.lower()
    code_lower = code.lower()
    
    # 外部 crate
    for crate in EXTERNAL_CRATES:
        if f"cannot find module or crate `{crate}`" in stderr:
            return 'ignore', f'外部 crate: {crate}'
        if f"unresolved import `{crate}" in stderr:
            return 'ignore', f'外部 crate: {crate}'
    
    # 故意编译错误 (反例)
    if '❌ 反例' in code or '反例:' in code or '编译错误' in code:
        if 'error[' in stderr:
            return 'compile_fail', '故意编译错误（反例）'
    
    # 伪代码 / 省略号
    if '...' in code and 'fn ' not in code:
        return 'ignore', '伪代码/省略号'
    if code.count('...') >= 2:
        return 'ignore', '含多处省略号'
    
    # 过程宏 crate 类型
    if 'proc_macro_derive' in stderr:
        return 'ignore', '过程宏需要 proc-macro crate 类型'
    
    # Rust 2024 unsafe extern 语法
    if 'extern blocks must be unsafe' in stderr:
        return 'fix_rust2024', 'Rust 2024: extern 需要 unsafe'
    if 'unsafe attribute used without unsafe' in stderr:
        return 'fix_rust2024', 'Rust 2024: unsafe attribute 需要 unsafe 前缀'
    
    # 重复定义
    if 'defined multiple times' in stderr:
        return 'fix_duplicate', '重复定义'
    
    # 全角标点
    if 'unknown start of token' in stderr and ('\uff0c' in code or '\u3002' in code):
        return 'fix_punctuation', '全角标点'
    
    # 缺少 unsafe 块
    if 'call to unsafe function' in stderr and 'requires unsafe block' in stderr:
        return 'fix_unsafe', '需要 unsafe 块'
    if 'dereference of raw pointer is unsafe' in stderr:
        return 'fix_unsafe', '需要 unsafe 块'
    
    # 缺少 lifetime
    if 'missing lifetime specifier' in stderr and 'fn ' in code:
        return 'ignore', '缺少生命周期（片段）'
    
    # 递归类型
    if 'recursive type' in stderr and 'has infinite size' in stderr:
        return 'compile_fail', '故意展示递归类型错误'
    
    # 孤儿规则
    if 'only traits defined in the current crate' in stderr:
        return 'compile_fail', '故意展示孤儿规则'
    
    # 冲突实现
    if 'conflicting implementations' in stderr:
        return 'compile_fail', '故意展示冲突实现'
    
    # 移动后借用
    if 'borrow of moved value' in stderr or 'cannot borrow' in stderr:
        if '❌' in code or '反例' in code:
            return 'compile_fail', '故意展示借用错误'
    
    # 非穷尽匹配
    if 'non-exhaustive patterns' in stderr:
        return 'compile_fail', '故意展示非穷尽匹配'
    
    # GAT 缺失 bounds
    if 'missing required bound' in stderr:
        return 'ignore', 'GAT 概念代码（不完整）'
    
    # const generics 限制
    if 'generic parameters may not be used in const operations' in stderr:
        return 'ignore', 'const generics 当前限制'
    
    # effects 语法（未来特性）
    if 'effect' in code_lower and 'expected one of' in stderr:
        return 'ignore', 'Effects 概念语法（未来特性）'
    
    # Verus 语法
    if 'proof fn' in code:
        return 'ignore', 'Verus 形式化代码'
    
    # 片段：没有 fn main 且无法作为顶层项
    if 'non-item in item list' in stderr:
        if '// ' in code.split('\n')[0] or '...' in code:
            return 'ignore', '片段/注释混入 impl'
        return 'fix_comment', '注释位置错误'
    
    # 缺少类型/函数定义
    if 'cannot find type' in stderr or 'cannot find function' in stderr:
        lines = code.strip().split('\n')
        if len(lines) <= 3:
            return 'ignore', '缺少定义的短片段'
        # 检查是否是函数签名缺少 body
        if 'expected one of' in stderr and ('found `}`' in stderr or 'found `}`' in stderr):
            return 'ignore', '不完整函数签名'
    
    # self 参数在自由函数中
    if '`self` parameter is only allowed in associated functions' in stderr:
        return 'ignore', 'trait 方法片段'
    
    # 默认分类
    return 'manual_review', '需要人工审查'


def main():
    # 读取编译报告 JSON（需要修改 compiler 脚本输出 JSON）
    # 这里我们直接从报告 markdown 解析
    report_path = Path('reports/code_block_compile_report.md')
    if not report_path.exists():
        print("报告不存在，请先运行 code_block_compiler.py")
        sys.exit(1)
    
    # 统计各分类
    categories = {}
    manual_reviews = []
    
    # 重新运行 compiler 获取结构化数据
    import subprocess
    result = subprocess.run(
        [sys.executable, 'scripts/code_block_compiler.py'],
        capture_output=True, text=True
    )
    
    # 从临时目录读取测试文件和错误信息
    tmp_dir = Path('target/tmp/code_block_tests')
    for rs_file in sorted(tmp_dir.glob('*.rs')):
        content = rs_file.read_text(encoding='utf-8')
        # 提取原始代码（在 main 包裹之前）
        stderr_file = rs_file.with_suffix('.stderr')
        stderr = stderr_file.read_text(encoding='utf-8') if stderr_file.exists() else ''
        
        # 尝试找到原始 markdown 中的代码块
        # 这需要更复杂的解析...
        pass
    
    print("请使用 code_block_compiler.py 的 JSON 输出模式")

if __name__ == '__main__':
    main()
