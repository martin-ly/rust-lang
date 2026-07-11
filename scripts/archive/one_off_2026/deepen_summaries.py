#!/usr/bin/env python3
"""
强力批量深化仍有模板化英文摘要的文件。
基于 **定位** / **EN** / 标题 生成针对性描述。
"""

import glob
import re
import os

TEMPLATE_PATTERNS = [
    'Core Rust concept with theoretical foundations and practical applications.',
    'Core Rust concept covering mechanism analysis.',
    'Core Rust concept covering practical examples.',
    'Core Rust concept covering formal methods foundations.',
    'Core Rust concept covering practical examples, mechanism analysis.',
    'Core Rust concept covering practical examples, type system mechanics.',
    'Core Rust concept covering mechanism analysis, type system mechanics.',
    'Core Rust concept covering formal methods foundations, mechanism analysis.',
    'Core Rust concept covering ownership and borrowing, testing and verification.',
    'Core Rust concept covering mental model building, mechanism analysis.',
]

def extract_field(content, field_name):
    pattern = rf'\*\*{re.escape(field_name)}\*\*:\s*(.*?)(?=\n>|\n#|\n\n|\Z)'
    m = re.search(pattern, content, re.DOTALL)
    if m:
        return ' '.join(m.group(1).strip().split())
    return None

def has_template(summary):
    s = summary.strip()
    for tp in TEMPLATE_PATTERNS:
        if tp in s:
            return True
    return False

def keywords_to_desc(p):
    """基于定位文本生成英文描述"""
    p = p.lower()
    parts = []
    
    # 按优先级排序的关键词
    checks = [
        ('形式化', "formal methods foundations"),
        ('formal', "formal methods foundations"),
        ('逻辑', "formal logic foundations"),
        ('定理', "theorem proving foundations"),
        ('验证', "verification techniques"),
        ('测试', "testing strategies"),
        ('miri', "dynamic verification with Miri"),
        ('kani', "model checking with Kani"),
        ('示例', "practical examples"),
        ('代码', "practical examples"),
        ('实践', "practical applications"),
        ('用例', "use-case driven examples"),
        ('对比', "cross-language comparison"),
        ('比较', "comparative analysis"),
        ('心智模型', "mental model building"),
        ('模型', "mental model building"),
        ('直觉', "intuitive understanding"),
        ('机制', "mechanism analysis"),
        ('分析', "mechanism analysis"),
        ('深入', "in-depth analysis"),
        ('模式', "design patterns"),
        ('idiom', "idiomatic patterns"),
        ('并发', "concurrent programming patterns"),
        ('并行', "parallel programming"),
        ('线程', "threading and synchronization"),
        ('同步', "synchronization primitives"),
        ('异步', "async/await patterns"),
        ('future', "async/await patterns"),
        ('unsafe', "unsafe Rust and memory safety"),
        ('内存安全', "memory safety guarantees"),
        ('性能', "performance optimization"),
        ('优化', "performance optimization"),
        ('zero-cost', "zero-cost abstractions"),
        ('编译器', "compiler internals"),
        ('前端', "compiler frontend"),
        ('后端', "compiler backend"),
        ('cranelift', "Cranelift backend"),
        ('类型系统', "type system mechanics"),
        ('泛型', "generic programming"),
        ('trait', "trait system mechanics"),
        ('生命周期', "lifetime semantics"),
        ('lifetime', "lifetime semantics"),
        ('所有权', "ownership and borrowing"),
        ('借用', "ownership and borrowing"),
        ('错误处理', "error handling strategies"),
        ('panic', "error handling strategies"),
        ('result', "error handling strategies"),
        ('宏', "metaprogramming techniques"),
        ('macro', "metaprogramming techniques"),
        ('元编程', "metaprogramming techniques"),
        ('ffi', "FFI interoperability"),
        ('互操作', "FFI interoperability"),
        ('嵌入式', "embedded systems programming"),
        ('embedded', "embedded systems programming"),
        ('no_std', "no_std development"),
        ('生态', "ecosystem and tooling"),
        ('工具链', "ecosystem and tooling"),
        ('cargo', "Cargo and build tooling"),
        ('web', "web and network programming"),
        ('网络', "network programming"),
        ('http', "HTTP and web services"),
        ('数据结构', "data structures"),
        ('算法', "algorithms"),
        ('collections', "collections and data structures"),
        ('ai', "AI/ML integration patterns"),
        ('机器学习', "machine learning integration"),
        ('llm', "LLM and AI tooling"),
        ('安全', "security practices"),
        ('security', "security practices"),
        ('密码学', "cryptography"),
        ('crypto', "cryptography"),
        ('wasm', "WebAssembly development"),
        ('webassembly', "WebAssembly development"),
        ('操作系统', "operating systems"),
        ('内核', "kernel development"),
        ('linux', "Linux kernel integration"),
        ('游戏', "game development"),
        ('game', "game development"),
        ('区块链', "blockchain development"),
        ('blockchain', "blockchain development"),
        ('数据库', "database programming"),
        ('database', "database programming"),
        ('信号处理', "signal processing"),
        ('gpu', "GPU and GPGPU programming"),
        ('simd', "SIMD and vectorization"),
        ('向量化', "SIMD and vectorization"),
        ('ebpf', "eBPF kernel programming"),
        ('空间', "aerospace and fault-tolerant systems"),
        ('太空', "aerospace and fault-tolerant systems"),
        ('辐射', "radiation-hardened computing"),
        ('自动微分', "automatic differentiation"),
        ('autodiff', "automatic differentiation"),
        ('spec', "language specification"),
        ('规范', "language specification"),
        ('roadmap', "language roadmap and evolution"),
        ('路线图', "language roadmap and evolution"),
        ('edition', "Rust edition mechanism"),
        ('迁移', "migration strategies"),
        ('quiz', "knowledge assessment quizzes"),
        ('测验', "knowledge assessment quizzes"),
        ('习题', "practice exercises"),
        ('练习', "practice exercises"),
    ]
    
    for kw, desc in checks:
        if kw in p and desc not in parts:
            parts.append(desc)
    
    if not parts:
        if '建立' in p or '构建' in p:
            return "Builds conceptual foundations for Rust developers."
        if '理解' in p or '澄清' in p:
            return "Clarifies core mechanisms and common misconceptions."
        if '覆盖' in p or '涵盖' in p:
            return "Comprehensive coverage of Rust language features and patterns."
        return None
    
    if len(parts) == 1:
        return f"Core Rust concept covering {parts[0]}."
    return "Core Rust concept covering " + ", ".join(parts[:3]) + "."

def generate_summary(en_title, zh_position, filename):
    topic = en_title or os.path.basename(filename).replace('.md', '')
    topic = topic.split('（')[0].strip()
    
    desc = None
    if zh_position:
        desc = keywords_to_desc(zh_position)
    
    if not desc:
        # 基于文件名生成简单描述
        base = re.sub(r'^\d+_', '', os.path.basename(filename).replace('.md', ''))
        base = re.sub(r'_preview$', '', base)
        base = base.replace('_', ' ')
        desc = f"Core Rust concept: {base}."
    
    return f"{topic}. {desc}"

def fix_file(path):
    with open(path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    summary_match = re.search(r'(\*\*Summary\*\*:\s*)(.+?)(?=\n>|\n#|\Z)', content, re.DOTALL)
    if not summary_match:
        return False, "no summary"
    
    summary_val = summary_match.group(2).strip()
    if not has_template(summary_val):
        return False, "not template"
    
    en_title = extract_field(content, 'EN')
    zh_position = extract_field(content, '定位')
    
    new_summary_text = generate_summary(en_title, zh_position, path)
    
    # 保留 Summary 行之前的格式（通常是 "> **Summary**: "）
    prefix = summary_match.group(1)  # "**Summary**: "
    old_block = summary_match.group(0)
    new_block = prefix + new_summary_text
    
    new_content = content.replace(old_block, new_block, 1)
    if new_content == content:
        return False, "replace failed"
    
    with open(path, 'w', encoding='utf-8') as f:
        f.write(new_content)
    return True, new_summary_text

def main():
    files = glob.glob('concept/**/*.md', recursive=True)
    files = [f for f in files if 'archive' not in f]
    
    fixed = 0
    skipped = 0
    errors = []
    
    for path in files:
        try:
            changed, msg = fix_file(path)
            if changed:
                fixed += 1
                if fixed <= 3:
                    print(f"[FIXED] {path}")
                    print(f"        → {msg}")
            else:
                skipped += 1
        except Exception as e:
            errors.append((path, str(e)))
    
    print(f"\n=== Results ===")
    print(f"Fixed:   {fixed}")
    print(f"Skipped: {skipped}")
    print(f"Errors:  {len(errors)}")

if __name__ == '__main__':
    main()
