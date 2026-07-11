#!/usr/bin/env python3
"""修复 concept/07_future/ 下被错误填充的 Summary 字段。"""

import glob
import re
import os

def extract_field(content, field_name):
    pattern = rf'\*\*{re.escape(field_name)}\*\*:\s*(.*?)(?=\n>|\n#|\n\n|\Z)'
    m = re.search(pattern, content, re.DOTALL)
    if m:
        return ' '.join(m.group(1).strip().split())
    return None

def is_bad_summary(summary):
    s = summary.strip()
    if s.startswith('```') or s.startswith('|'):
        return True
    if len(s) > 200:
        return True
    return False

def get_topic_from_filename(filename):
    base = os.path.basename(filename).replace('.md', '')
    # 去掉数字前缀和 _preview 后缀
    base = re.sub(r'^\d+_', '', base)
    base = re.sub(r'_preview$', '', base)
    base = base.replace('_', ' ').title()
    return base

def generate_summary(en_title, filename):
    topic = en_title or get_topic_from_filename(filename)
    topic = topic.split('（')[0].strip()
    # 去掉常见的后缀
    topic = re.sub(r'\s*Preview$', '', topic, flags=re.I)
    topic = re.sub(r'\s*预研$', '', topic)
    topic = re.sub(r'\s*预览$', '', topic)
    topic = re.sub(r'^Rust\s+', '', topic)
    
    mapping = {
        'Ai Integration': 'AI integration patterns with Rust, covering generative verification loops and deterministic containers.',
        'Formal Methods': 'Formal verification ecosystem for Rust: tools, techniques, and industrial adoption.',
        'Evolution': 'Rust language evolution roadmap, edition mechanisms, and RFC process.',
        'Effects System': 'Type-and-effect systems for tracking computational effects in Rust.',
        'Rust Version Tracking': 'Tracking Rust language and standard library evolution across versions.',
        'Mcdc Coverage': 'Modified Condition/Decision Coverage for safety-critical Rust code.',
        'Safety Tags': 'Machine-readable safety annotations as an evolution of `# Safety` comments.',
        'Parallel Frontend': 'Compiler parallel frontend development for faster compile times.',
        'Derive Coerce Pointee': 'Smart pointer ergonomics via derive macros for coercion.',
        'Const Trait Impl': 'Const trait implementations and compile-time evaluation.',
        'Stable Abi': 'Stable ABI guarantees for cross-language interoperability.',
        'Inline Const Pattern': 'Inline const blocks in pattern matching for expressive control flow.',
        'Must Not Suspend': 'Preventing accidental suspension across await points in async Rust.',
        'Lifetime Capture': 'Precise lifetime capture control in impl trait return types.',
        'Pin Ergonomics': 'Improving Pin projection and self-referential struct ergonomics.',
        'Rpitit': 'Return Position Impl Trait In Traits (RPITIT) and implementation strategies.',
        'Cranelift Backend': 'Cranelift codegen backend as a fast development-time alternative.',
        'Type Alias Impl Trait': 'Type alias impl trait (TAIT) for naming opaque return types.',
        'Arbitrary Self Types': 'Custom method receiver types beyond &self and &mut self.',
        'Const Trait': 'Const traits enabling generic computations in const contexts.',
        'Ergonomic Ref Counting': 'Ergonomic reference counting proposals for smoother shared ownership.',
        'Rust Specification': 'Formal specification efforts for the Rust language.',
        'Async Drop': 'Asynchronous destructors for proper async resource cleanup.',
        'Field Projections': 'Safe field projection mechanisms for pinned and unsafe contexts.',
        'Rust Edition': 'Rust edition mechanism, migration strategies, and future directions.',
        'Rust For Linux': 'Rust adoption in the Linux kernel and driver development.',
        'Borrowsanitizer': 'BorrowSanitizer (BSan) for dynamic detection of aliasing rule violations.',
        'Rust In Ai': 'Rust in AI/ML: performance, safety, and ecosystem integration.',
        'Edition Guide': 'Comprehensive guide to Rust Edition 2024 features and migrations.',
        'Gen Blocks': 'Generator blocks (gen {}) for lazy iterator construction.',
        'Std Autodiff': 'Automatic differentiation in Rust standard library discussions.',
        'Cargo Semver Checks': 'Semantic versioning compatibility checking for Rust crates.',
        'Roadmap': 'Rust 2027 Edition and long-term language roadmap.',
        'Wasm Target Evolution': 'WebAssembly target evolution and WASI preview specifications.',
        'Aarch64 Sve Sme': 'ARM Scalable Vector Extension (SVE) and SME support in Rust.',
        'Open Enums': 'Open enums and unnamed variants for C FFI compatibility.',
        'Rust In Space': 'Rust for space applications: radiation tolerance and fault tolerance.',
        'Specialization': 'Trait specialization for overlapping impls with priority rules.',
        'Compile Time Execution': 'Compile-time execution and const evaluation limits.',
        'Rust For Webassembly': 'Rust as a primary language for WebAssembly development.',
        'Ebpf Rust': 'eBPF development with Rust for kernel observability and networking.',
        'Return Type Notation': 'Return Type Notation (RTN) for constraining opaque return types.',
        'Unsafe Fields': 'Unsafe field annotations for partial struct initialization.',
    }
    
    key = topic.strip()
    desc = mapping.get(key, f"Emerging Rust feature or ecosystem trend: {key}.")
    return f"> **Summary**: {topic}. {desc}"

def fix_file(path):
    with open(path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    summary_match = re.search(r'(\*\*Summary\*\*:\s*)(.+?)(?=\n>|\n#|\Z)', content, re.DOTALL)
    if not summary_match:
        return False, "no summary"
    
    summary_val = summary_match.group(2)
    if not is_bad_summary(summary_val):
        return False, "summary ok"
    
    en_title = extract_field(content, 'EN')
    new_summary = generate_summary(en_title, path)
    
    old_block = summary_match.group(0)
    # 构造新的完整行，保留前面的 > 和字段名
    prefix = summary_match.group(1)  # "**Summary**: "
    # 由于 generate_summary 已经包含 "> **Summary**: "，我们需要替换整个块
    # 但旧块可能前面有 > 和空格
    # 让我们用更精确的方式：找到包含 Summary 的整行/块
    
    # 实际上，old_block 是 "**Summary**: <bad_content>"
    # 我们需要把它替换成 new_summary（不包含前面的 >）
    new_block = prefix + new_summary.split(':', 1)[1].strip()
    
    new_content = content.replace(old_block, new_block, 1)
    if new_content == content:
        return False, "replace failed"
    
    with open(path, 'w', encoding='utf-8') as f:
        f.write(new_content)
    return True, new_summary

def main():
    files = glob.glob('concept/07_future/*.md')
    fixed = 0
    skipped = 0
    
    for path in files:
        try:
            changed, msg = fix_file(path)
            if changed:
                fixed += 1
                print(f"[FIXED] {os.path.basename(path)}")
            else:
                skipped += 1
        except Exception as e:
            print(f"ERROR {path}: {e}")
    
    print(f"\nFixed: {fixed}, Skipped: {skipped}")

if __name__ == '__main__':
    main()
