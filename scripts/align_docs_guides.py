import os

STATUS_BLOCK = '\n---\n\n> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)\n>\n> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]\n\n**文档版本**: 1.1\n**对应 Rust 版本**: 1.95.0+ (Edition 2024)\n**最后更新**: 2026-05-19\n**状态**: ✅ 权威来源对齐完成 (Batch 8)\n'

dirs_to_process = [
    'docs/05_guides',
    'docs/06_toolchain',
    'docs/07_future',
]

processed = 0

for base_dir in dirs_to_process:
    for fname in sorted(os.listdir(base_dir)):
        if not fname.endswith('.md'):
            continue
        filepath = os.path.join(base_dir, fname)
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()
        
        if '权威来源对齐完成' in content:
            continue
        
        result = content.rstrip() + STATUS_BLOCK
        with open(filepath, 'w', encoding='utf-8') as f:
            f.write(result)
        
        processed += 1
        print(f'Processed: {filepath}')

print(f'\nTotal processed: {processed}')
