#!/usr/bin/env python3
"""验证 compile_fail 代码块 v3: 使用唯一文件名避免竞争条件"""

import os, re, subprocess, sys, concurrent.futures, threading
from pathlib import Path
from datetime import datetime

RUSTC = "rustc"
TMP_DIR = Path("target/tmp/verify_compile_fail_v3")
REPORT_PATH = "reports/verify_compile_fail_v3_report.md"
MAX_WORKERS = 4
TIMEOUT = 15

counter = 0
counter_lock = threading.Lock()

def get_next_id():
    global counter
    with counter_lock:
        counter += 1
        return counter

EXTERNAL_CRATES = {
    'tokio', 'axum', 'sqlx', 'serde', 'tracing', 'clap', 'reqwest',
    'crossbeam', 'rayon', 'parking_lot', 'loom',
    'futures', 'tokio_stream',
    'prusti_contracts', 'kani', 'vstd', 'creusot_contracts',
    'eyre', 'color_eyre', 'anyhow', 'thiserror',
    'jemallocator', 'mimalloc',
    'leptos', 'dioxus', 'yew',
    'embassy_executor', 'embassy_stm32', 'embassy_time',
    'bevy', 'wgpu', 'rapier', 'rodio', 'egui',
    'candle_core', 'burn', 'tract', 'ort', 'tch',
    'cxx', 'bindgen', 'cbindgen',
    'libfuzzer_sys', 'proptest',
    'sccache', 'cargo_vet',
    'mio', 'hyper', 'tower',
    'rocket', 'warp', 'tide', 'actix', 'tonic',
    'napi', 'pyo3', 'wasm_bindgen',
    'criterion', 'quickcheck',
    'libc', 'winapi',
    'dashmap', 'sled', 'rusqlite',
    'zeroize', 'secrecy', 'anstream',
    'owo_colors', 'termcolor', 'ansi_term',
    'lazy_static', 'once_cell',
    'openraft', 'raft',
    'candle', 'burn', 'tract',
}

def find_md_files():
    files = []
    for base in ["concept", "knowledge"]:
        for root, _, fs in os.walk(base):
            for f in fs:
                if f.endswith(".md"):
                    files.append(os.path.join(root, f))
    return sorted(files)

def extract_compile_fail_blocks(content, file_path):
    blocks = []
    lines = content.split('\n')
    i = 0
    while i < len(lines):
        line = lines[i]
        if line.startswith('```'):
            fence = line[3:].strip()
            if 'rust' in fence and 'compile_fail' in fence:
                start_line = i + 1
                code_lines = []
                i += 1
                while i < len(lines) and not lines[i].startswith('```'):
                    code_lines.append(lines[i])
                    i += 1
                code = '\n'.join(code_lines)
                blocks.append((code, start_line, fence))
            else:
                i += 1
                while i < len(lines) and not lines[i].startswith('```'):
                    i += 1
        i += 1
    return blocks

def needs_skip(code):
    for crate in EXTERNAL_CRATES:
        patterns = [
            f'use {crate}',
            f'extern crate {crate}',
            f'{crate}::',
            f'#[derive({crate.title()}',
        ]
        for pat in patterns:
            if pat in code:
                return True, f'external_crate:{crate}'
    if 'include_str!' in code or 'include_bytes!' in code:
        return True, 'compile_time_resource'
    return False, None

def compile_code(source, test_path, crate_type):
    test_path.parent.mkdir(parents=True, exist_ok=True)
    test_path.write_text(source, encoding='utf-8')
    try:
        result = subprocess.run(
            [RUSTC, "--edition", "2024", "--crate-type", crate_type, str(test_path)],
            capture_output=True, text=True, timeout=TIMEOUT
        )
        success = result.returncode == 0
        stderr = result.stderr or ''
        for suffix in ['.exe', '.rlib', '.lib', '.pdb']:
            p = test_path.with_suffix(suffix)
            if p.exists():
                p.unlink()
        return success, stderr
    except subprocess.TimeoutExpired:
        return False, "编译超时"
    except Exception as e:
        return False, str(e)

def try_compile(code):
    uid = get_next_id()
    
    # 方式1: 如果有 fn main，直接作为 bin
    if 'fn main' in code:
        test_path = TMP_DIR / f"test_{uid}_bin.rs"
        success, stderr = compile_code(code, test_path, "bin")
        if not success:
            return False, stderr, 'bin_direct'
        return True, stderr, 'bin_direct'
    
    # 方式2: 无 fn main，提取指令后包裹为 bin
    lines = code.split('\n')
    directives = [l for l in lines if l.strip().startswith('#![') or l.strip().startswith('#![feature')]
    body = [l for l in lines if not (l.strip().startswith('#![') or l.strip().startswith('#![feature'))]
    body_text = '\n'.join(body)
    source = '\n'.join(directives) + '\n' if directives else ''
    source += 'fn main() {\n'
    source += body_text + '\n'
    source += '}\n'
    
    test_path = TMP_DIR / f"test_{uid}_wrapped.rs"
    success, stderr = compile_code(source, test_path, "bin")
    if not success:
        return False, stderr, 'bin_wrapped'
    
    # 方式3: bin_wrapped 通过了，尝试作为 lib（不包裹）
    lib_source = '\n'.join(directives) + '\n' if directives else ''
    lib_source += body_text + '\n'
    test_path = TMP_DIR / f"test_{uid}_lib.rs"
    success2, stderr2 = compile_code(lib_source, test_path, "lib")
    if not success2:
        return False, stderr2, 'lib_direct'
    
    return True, stderr + "\n" + stderr2, 'all_pass'

def classify(stderr, success):
    if success:
        return 'unexpected_pass'
    # 编译失败，检查是否是真正的语义错误
    if 'error[' in stderr:
        return 'expected_fail'
    if 'error: aborting due to' in stderr and 'error:' in stderr:
        # 有错误但无 error[EXXXX]，可能是语法错误
        if 'expected' in stderr.lower() or 'unexpected' in stderr.lower() or 'found' in stderr.lower():
            return 'syntax_error'
        return 'expected_fail'
    return 'syntax_error'

def compile_one(args):
    file_path, code, line_num, fence = args
    skip, reason = needs_skip(code)
    if skip:
        return {
            'file': file_path, 'line': line_num, 'status': 'skipped',
            'reason': reason, 'stderr': '', 'mode': 'skipped'
        }
    
    success, stderr, compile_mode = try_compile(code)
    status = classify(stderr, success)
    
    return {
        'file': file_path, 'line': line_num, 'status': status,
        'stderr': stderr[:300], 'mode': compile_mode,
        'code_preview': code[:60].replace('\n', ' ')
    }

def main():
    TMP_DIR.mkdir(parents=True, exist_ok=True)
    md_files = find_md_files()
    
    tasks = []
    for file_path in md_files:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
        blocks = extract_compile_fail_blocks(content, file_path)
        for code, line_num, fence in blocks:
            tasks.append((file_path, code, line_num, fence))
    
    print(f"发现 {len(tasks)} 个 compile_fail 代码块，开始验证...")
    
    results = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=MAX_WORKERS) as executor:
        futures = {executor.submit(compile_one, task): task for task in tasks}
        for future in concurrent.futures.as_completed(futures):
            result = future.result()
            results.append(result)
            icon = {'expected_fail': '✅', 'unexpected_pass': '⚠️', 
                    'syntax_error': '❌', 'skipped': '⏭️'}.get(result['status'], '?')
            print(f"  {icon} {Path(result['file']).name}:{result['line']} [{result['status']}] ({result['mode']})")
    
    generate_report(results)
    
    expected = sum(1 for r in results if r['status'] == 'expected_fail')
    unexpected = sum(1 for r in results if r['status'] == 'unexpected_pass')
    syntax = sum(1 for r in results if r['status'] == 'syntax_error')
    skipped = sum(1 for r in results if r['status'] == 'skipped')
    
    print(f"\n{'='*60}")
    print(f"验证完成")
    print(f"  预期失败: {expected}")
    print(f"  意外通过: {unexpected}")
    print(f"  语法错误: {syntax}")
    print(f"  跳过: {skipped}")
    print(f"  报告: {REPORT_PATH}")

def generate_report(results):
    lines = [
        "# Compile Fail 验证报告 v3 (唯一文件名)",
        "",
        f"> 生成时间: {datetime.now().strftime('%Y-%m-%d %H:%M')}",
        "",
        "## 摘要",
        "",
    ]
    
    counts = {}
    for r in results:
        counts[r['status']] = counts.get(r['status'], 0) + 1
    
    lines.append(f"| 状态 | 数量 |")
    lines.append(f"|:---|:---|")
    for status, count in sorted(counts.items(), key=lambda x: -x[1]):
        lines.append(f"| {status} | {count} |")
    lines.append("")
    
    problems = [r for r in results if r['status'] in ('unexpected_pass', 'syntax_error')]
    if problems:
        lines.extend([
            "## 问题代码块",
            "",
            "| 文件 | 行号 | 状态 | 编译模式 | 预览 | 错误信息 |",
            "|:---|:---|:---|:---|:---|:---|",
        ])
        for r in problems:
            preview = r['code_preview'][:35].replace('|', '\\|')
            stderr = r['stderr'][:70].replace('|', '\\|').replace('\n', ' ')
            lines.append(f"| {r['file']} | {r['line']} | {r['status']} | {r['mode']} | `{preview}` | {stderr} |")
        lines.append("")
    
    report_dir = Path(REPORT_PATH).parent
    report_dir.mkdir(parents=True, exist_ok=True)
    with open(REPORT_PATH, 'w', encoding='utf-8') as f:
        f.write('\n'.join(lines))

if __name__ == '__main__':
    main()
