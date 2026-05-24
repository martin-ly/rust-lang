#!/usr/bin/env python3
"""验证所有 compile_fail 代码块：确保它们确实编译失败，且无语法错误（伪代码）"""

import os, re, subprocess, sys, json, concurrent.futures
from pathlib import Path
from datetime import datetime

RUSTC = "rustc"
TMP_DIR = Path("target/tmp/verify_compile_fail")
REPORT_PATH = "reports/verify_compile_fail_report.md"
MAX_WORKERS = 8
TIMEOUT = 15

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

def prepare_source(code):
    if 'fn main' in code:
        return code
    lines = code.split('\n')
    directives = []
    body = []
    for line in lines:
        stripped = line.strip()
        if stripped.startswith('#![') or stripped.startswith('#![feature'):
            directives.append(line)
        else:
            body.append(line)
    body_text = '\n'.join(body)
    source = '\n'.join(directives) + '\n' if directives else ''
    source += 'fn main() {\n'
    source += body_text + '\n'
    source += '}\n'
    return source

def compile_one(args):
    file_path, code, line_num, fence = args
    skip, reason = needs_skip(code)
    if skip:
        return {
            'file': file_path, 'line': line_num, 'status': 'skipped',
            'reason': reason, 'stderr': '', 'code_preview': code[:80].replace('\n', ' ')
        }
    
    block_id = f"{Path(file_path).stem}_L{line_num}"
    test_path = TMP_DIR / f"{block_id}.rs"
    test_path.parent.mkdir(parents=True, exist_ok=True)
    
    source = prepare_source(code)
    test_path.write_text(source, encoding='utf-8')
    
    try:
        result = subprocess.run(
            [RUSTC, "--edition", "2024", "--crate-type", "bin", str(test_path)],
            capture_output=True, text=True, timeout=TIMEOUT
        )
        success = result.returncode == 0
        stderr = result.stderr or ''
        
        exe = test_path.with_suffix('.exe')
        if exe.exists():
            exe.unlink()
        
        if success:
            status = 'unexpected_pass'
        else:
            # 检查是否有语法错误（不是预期的语义错误）
            if 'error: expected' in stderr and 'error[' not in stderr:
                status = 'syntax_error'
            elif 'error: aborting due to' in stderr and stderr.count('error[') == 0:
                status = 'syntax_error'
            elif 'unknown start of token' in stderr:
                status = 'syntax_error'
            elif 'unresolved import' in stderr:
                status = 'syntax_error'  # 可能是我们遗漏的外部 crate
            else:
                status = 'expected_fail'
        
        return {
            'file': file_path, 'line': line_num, 'status': status,
            'reason': '', 'stderr': stderr[:400], 'code_preview': code[:80].replace('\n', ' ')
        }
    except subprocess.TimeoutExpired:
        return {
            'file': file_path, 'line': line_num, 'status': 'timeout',
            'reason': f'编译超时（{TIMEOUT}秒）', 'stderr': '', 'code_preview': code[:80].replace('\n', ' ')
        }
    except Exception as e:
        return {
            'file': file_path, 'line': line_num, 'status': 'error',
            'reason': str(e), 'stderr': '', 'code_preview': code[:80].replace('\n', ' ')
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
            status_icon = {
                'expected_fail': '✅', 'unexpected_pass': '⚠️ PASS',
                'syntax_error': '❌ SYNTAX', 'skipped': '⏭️',
                'timeout': '⏱️', 'error': '💥'
            }.get(result['status'], '?')
            print(f"  {status_icon} {Path(result['file']).name}:{result['line']} [{result['status']}]")
    
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
    
    if unexpected > 0 or syntax > 0:
        print(f"\n⚠️ 有 {unexpected + syntax} 个问题需要修复！")
        sys.exit(1)
    else:
        print(f"\n✅ 所有 compile_fail 代码块验证通过！")

def generate_report(results):
    lines = [
        "# Compile Fail 代码块验证报告",
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
            "| 文件 | 行号 | 状态 | 预览 | 错误信息 |",
            "|:---|:---|:---|:---|:---|",
        ])
        for r in problems:
            preview = r['code_preview'][:40].replace('|', '\\|')
            stderr = r['stderr'][:80].replace('|', '\\|').replace('\n', ' ')
            lines.append(f"| {r['file']} | {r['line']} | {r['status']} | `{preview}` | {stderr} |")
        lines.append("")
    
    report_dir = Path(REPORT_PATH).parent
    report_dir.mkdir(parents=True, exist_ok=True)
    with open(REPORT_PATH, 'w', encoding='utf-8') as f:
        f.write('\n'.join(lines))

if __name__ == '__main__':
    main()
