#!/usr/bin/env python3
"""
基于 **定位** 字段关键词，批量生成更有针对性的英文摘要。
只处理当前仍为模板化摘要的文件。
"""

import glob
import re
import os

TEMPLATE = "Core Rust concept with theoretical foundations and practical applications."

def extract_field(content, field_name):
    pattern = rf'\*\*{re.escape(field_name)}\*\*:\s*(.*?)(?=\n>|\n#|\n\n|\Z)'
    m = re.search(pattern, content, re.DOTALL)
    if m:
        return ' '.join(m.group(1).strip().split())
    return None

def generate_desc(zh_position, en_title, filename):
    """基于定位关键词生成针对性英文描述"""
    if not zh_position:
        return TEMPLATE
    
    p = zh_position.lower()
    parts = []
    
    # 关键词映射
    if '形式化' in p or 'formal' in p or '逻辑' in p or '定理' in p:
        parts.append("formal methods foundations")
    if '示例' in p or '代码' in p or '实践' in p or '用例' in p:
        parts.append("practical examples")
    if '对比' in p or '比较' in p or 'vs' in p or 'versus' in p:
        parts.append("cross-language comparison")
    if '心智模型' in p or '模型' in p or '直觉' in p:
        parts.append("mental model building")
    if '机制' in p or '分析' in p or '深入' in p:
        parts.append("mechanism analysis")
    if '模式' in p or 'pattern' in p or 'idiom' in p:
        parts.append("design patterns")
    if '并发' in p or '并行' in p or '线程' in p or '同步' in p:
        parts.append("concurrent programming patterns")
    if '异步' in p or 'async' in p or 'future' in p:
        parts.append("async/await patterns")
    if 'unsafe' in p or '内存安全' in p or 'ub' in p:
        parts.append("memory safety and UB prevention")
    if '性能' in p or '优化' in p or 'zero-cost' in p:
        parts.append("performance optimization")
    if '编译器' in p or '前端' in p or '后端' in p or 'cranelift' in p:
        parts.append("compiler internals")
    if '类型系统' in p or '泛型' in p or 'trait' in p:
        parts.append("type system mechanics")
    if '生命周期' in p or 'lifetime' in p:
        parts.append("lifetime semantics")
    if '所有权' in p or '借用' in p:
        parts.append("ownership and borrowing")
    if '错误处理' in p or 'panic' in p or 'result' in p:
        parts.append("error handling strategies")
    if '宏' in p or 'macro' in p or '元编程' in p:
        parts.append("metaprogramming techniques")
    if 'ffi' in p or '互操作' in p or 'c ' in p:
        parts.append("FFI interoperability")
    if '嵌入式' in p or 'embedded' in p or 'no_std' in p:
        parts.append("embedded systems programming")
    if '测试' in p or '验证' in p or 'miri' in p or 'kani' in p:
        parts.append("testing and verification")
    if '生态' in p or '工具链' in p or 'cargo' in p:
        parts.append("ecosystem and tooling")
    if 'web' in p or '网络' in p or 'http' in p:
        parts.append("web and network programming")
    if '数据结构' in p or '算法' in p or 'collections' in p:
        parts.append("data structures and algorithms")
    if 'ai' in p or '机器学习' in p or 'llm' in p:
        parts.append("AI/ML integration patterns")
    
    if not parts:
        # 尝试从定位中提取动词短语
        if p.startswith('建立') or p.startswith('构建'):
            return "Builds conceptual foundations for Rust developers."
        if p.startswith('理解') or p.startswith('澄清'):
            return "Clarifies core mechanisms and common misconceptions."
        if p.startswith('覆盖') or p.startswith('涵盖'):
            return "Comprehensive coverage of Rust language features and patterns."
        return TEMPLATE
    
    return "Core Rust concept covering " + ", ".join(parts) + "."

def enhance_file(path):
    with open(path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # 检查当前摘要是否是模板
    summary_match = re.search(r'(\*\*Summary\*\*:\s*)(.+?)(?=\n>|\n#|\Z)', content, re.DOTALL)
    if not summary_match:
        return False, "no summary"
    
    summary_val = summary_match.group(2).strip()
    if TEMPLATE not in summary_val:
        return False, "already enhanced"
    
    en_title = extract_field(content, 'EN')
    zh_position = extract_field(content, '定位')
    
    topic = en_title or os.path.basename(path).replace('.md', '')
    topic = topic.split('（')[0].strip()
    
    desc = generate_desc(zh_position, topic, path)
    
    # 替换模板部分
    new_summary_val = summary_val.replace(TEMPLATE, desc)
    
    old_block = summary_match.group(0)
    new_block = summary_match.group(1) + new_summary_val
    
    new_content = content.replace(old_block, new_block, 1)
    if new_content == content:
        return False, "replace failed"
    
    with open(path, 'w', encoding='utf-8') as f:
        f.write(new_content)
    return True, desc

def main():
    files = glob.glob('concept/**/*.md', recursive=True)
    files = [f for f in files if 'archive' not in f]
    
    fixed = 0
    skipped = 0
    
    for path in files:
        try:
            changed, msg = enhance_file(path)
            if changed:
                fixed += 1
            else:
                skipped += 1
        except Exception as e:
            print(f"ERROR {path}: {e}")
    
    print(f"Enhanced: {fixed}")
    print(f"Skipped:  {skipped}")

if __name__ == '__main__':
    main()
