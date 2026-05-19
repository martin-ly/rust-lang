import os

STATUS_BLOCK = '\n---\n\n> **权威来源**: [Rust Standard Library](https://doc.rust-lang.org/std/), [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/)\n>\n> **权威来源对齐变更日志**: 2026-05-19 新增 Rust 标准库、Rust Reference、TRPL 官方来源标注 [来源: Authority Source Sprint Batch 8]\n\n**文档版本**: 1.1\n**对应 Rust 版本**: 1.95.0+ (Edition 2024)\n**最后更新**: 2026-05-19\n**状态**: ✅ 权威来源对齐完成 (Batch 8)\n'

base_dir = 'docs/02_reference/quick_reference'
processed = 0

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
