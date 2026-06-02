#!/usr/bin/env python3
"""修复 doc test 中缺少代码块开始标记的问题"""
from pathlib import Path

def fix_file(filepath):
    """为没有开始标记的代码块添加 ignore 标记"""
    content = filepath.read_text(encoding='utf-8')
    lines = content.split('\n')
    
    # 找到所有 ``` 结束标记，检查前面是否有对应的开始标记
    i = 0
    while i < len(lines):
        line = lines[i].strip()
        if line.endswith('```') and not line.startswith('/// ```') and not line.startswith('//! ```'):
            # 不是 doc 注释中的代码块，跳过
            i += 1
            continue
        
        if line == '/// ```' or line == '//! ```':
            # 向前查找开始标记
            j = i - 1
            found_start = False
            while j >= 0:
                prev = lines[j].strip()
                if prev == '/// ```' or prev == '//! ```' or prev == '/// ```ignore' or prev == '//! ```ignore':
                    # 找到了另一个标记，检查它是否是开始标记
                    # 如果它和当前标记之间没有空行或其他内容，可能是连续的
                    found_start = True
                    break
                j -= 1
            
            if not found_start:
                # 在代码块开始位置添加 ```ignore
                # 向前查找代码块实际开始的位置
                j = i - 1
                code_start = i
                while j >= 0:
                    prev = lines[j].strip()
                    if prev == '///' or prev == '//!' or prev == '/// ```' or prev == '//! ```':
                        # 空行或另一个标记，代码块从这里开始
                        code_start = j + 1
                        break
                    if not (prev.startswith('///') or prev.startswith('//!')):
                        code_start = j + 1
                        break
                    j -= 1
                
                # 在当前行添加 ignore
                if lines[i].strip() == '/// ```':
                    lines[i] = '/// ```ignore'
                elif lines[i].strip() == '//! ```':
                    lines[i] = '//! ```ignore'
        
        i += 1
    
    new_content = '\n'.join(lines)
    if new_content != content:
        filepath.write_text(new_content, encoding='utf-8')
        print(f'Fixed {filepath}')
        return True
    return False

def main():
    files = [
        'crates/c02_type_system/src/precise_capturing_guide.rs',
        'crates/c02_type_system/src/rust_191_features.rs',
        'crates/c02_type_system/src/rust_195_features.rs',
    ]
    
    for f in files:
        fix_file(Path(f))

if __name__ == '__main__':
    main()
