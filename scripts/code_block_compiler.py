#!/usr/bin/env python3
"""代码块编译验证：提取 markdown 中的 rust 代码块并编译测试"""

import os, re, subprocess, tempfile, json, sys
from pathlib import Path

RUSTC = "rustc"
TMP_DIR = Path("target/tmp/code_block_tests")
REPORT_PATH = "reports/code_block_compile_report.md"

def find_md_files():
    files = []
    for base in ["concept", "knowledge"]:
        for root, _, fs in os.walk(base):
            for f in fs:
                if f.endswith(".md"):
                    files.append(os.path.join(root, f))
    return sorted(files)

def extract_rust_blocks(content, file_path):
    """提取 rust 代码块，返回 (language_modifiers, code_text, line_number) 列表"""
    blocks = []
    lines = content.split('\n')
    i = 0
    while i < len(lines):
        line = lines[i]
        if line.startswith('```'):
            fence = line[3:].strip()
            parts = [p.strip() for p in fence.split(',')]
            lang = parts[0] if parts else ''
            modifiers = set(p.lower() for p in parts[1:])
            
            if lang == 'rust':
                start_line = i + 1
                code_lines = []
                i += 1
                while i < len(lines) and not lines[i].startswith('```'):
                    code_lines.append(lines[i])
                    i += 1
                code = '\n'.join(code_lines)
                blocks.append((modifiers, code, start_line, fence))
            else:
                i += 1
                while i < len(lines) and not lines[i].startswith('```'):
                    i += 1
        i += 1
    return blocks

# 需要外部 crate 的库（验证环境未安装，自动跳过）
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
}

def should_compile(modifiers, code=''):
    """判断是否应该编译此代码块"""
    if 'ignore' in modifiers:
        return False, 'ignore'
    if 'compile_fail' in modifiers:
        return True, 'compile_fail'
    
    # 检查是否使用了未安装的外部 crate
    for crate in EXTERNAL_CRATES:
        patterns = [
            f'use {crate}',
            f'extern crate {crate}',
            f'{crate}::',
            f'#[derive({crate.title()}',
        ]
        for pat in patterns:
            if pat in code:
                return False, f'external_crate:{crate}'
    
    # 检查编译期资源依赖（文件/环境变量）
    if 'include_str!' in code or 'include_bytes!' in code:
        return False, 'compile_time_resource'
    if 'env!' in code and 'CARGO_' not in code:
        return False, 'compile_time_env'
    
    return True, 'normal'

def prepare_source(code, expected_mode):
    """准备 Rust 源代码"""
    # 如果已有 fn main，直接使用
    if 'fn main' in code:
        return code
    
    # 如果已有 #![feature(...)] 或 extern crate，保留在顶部
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
    # 包裹为 main 函数
    source = '\n'.join(directives) + '\n'
    source += 'fn main() {\n'
    source += body_text + '\n'
    source += '}\n'
    return source

def compile_block(source, test_path):
    """编译单个代码块，返回 (success, stderr)"""
    test_path.parent.mkdir(parents=True, exist_ok=True)
    test_path.write_text(source, encoding='utf-8')
    
    try:
        result = subprocess.run(
            [RUSTC, "--edition", "2024", "--crate-type", "bin", str(test_path)],
            capture_output=True, text=True, timeout=30
        )
        success = result.returncode == 0
        stderr = result.stderr
        # 保存 stderr
        if stderr:
            test_path.with_suffix('.stderr').write_text(stderr, encoding='utf-8')
        # 清理生成的可执行文件
        exe = test_path.with_suffix('.exe')
        if exe.exists():
            exe.unlink()
        return success, stderr
    except subprocess.TimeoutExpired:
        return False, "编译超时（30秒）"
    except Exception as e:
        return False, str(e)

def main():
    TMP_DIR.mkdir(parents=True, exist_ok=True)
    
    md_files = find_md_files()
    results = []
    total = 0
    passed = 0
    failed = 0
    skipped = 0
    
    print(f"扫描 {len(md_files)} 个 markdown 文件...")
    
    for file_path in md_files:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        blocks = extract_rust_blocks(content, file_path)
        for modifiers, code, line_num, fence in blocks:
            should, mode = should_compile(modifiers, code)
            if not should:
                skipped += 1
                continue
            
            total += 1
            block_id = f"{Path(file_path).stem}_L{line_num}"
            test_path = TMP_DIR / f"{block_id}.rs"
            
            source = prepare_source(code, mode)
            success, stderr = compile_block(source, test_path)
            
            result = {
                'file': file_path,
                'line': line_num,
                'mode': mode,
                'success': success,
                'stderr': stderr[:500] if stderr else '',
                'code_preview': code[:100].replace('\n', ' ')
            }
            results.append(result)
            
            if mode == 'compile_fail':
                if not success:
                    passed += 1  # compile_fail 且确实编译失败 → 通过
                else:
                    failed += 1  # compile_fail 但编译通过 → 失败
            else:
                if success:
                    passed += 1
                else:
                    failed += 1
            
            status = "✅" if (mode == 'compile_fail' and not success) or (mode != 'compile_fail' and success) else "❌"
            print(f"  {status} {file_path}:{line_num} ({mode})")
    
    # 生成报告
    generate_report(results, total, passed, failed, skipped)
    
    print(f"\n{'='*60}")
    print(f"编译测试完成")
    print(f"  总计: {total}")
    print(f"  通过: {passed}")
    print(f"  失败: {failed}")
    print(f"  跳过: {skipped}")
    print(f"  报告: {REPORT_PATH}")
    
    if failed > 0:
        print(f"\n⚠️ 有 {failed} 个代码块编译测试失败！")
        sys.exit(1)
    else:
        print(f"\n✅ 所有代码块编译测试通过！")

def generate_report(results, total, passed, failed, skipped):
    from datetime import datetime
    scan_dirs = "concept/ + knowledge/"
    lines = [
        "# 代码块编译验证报告 (Code Block Compile Report)",
        "",
        f"> 生成时间: {datetime.now().strftime('%Y-%m-%d')}",
        f"> 扫描范围: {scan_dirs}",
        "",
        "## 摘要",
        "",
        f"| 指标 | 数值 |",
        f"|:---|:---|",
        f"| 测试代码块 | {total} |",
        f"| 编译通过 | {passed} |",
        f"| 编译失败 | {failed} |",
        f"| 跳过 (ignore/no_run) | {skipped} |",
        f"| 通过率 | {passed/max(total,1)*100:.1f}% |",
        "",
    ]
    
    concept_fails = [r for r in results if not r['success'] and r['mode'] != 'compile_fail' and r['file'].startswith('concept')]
    knowledge_fails = [r for r in results if not r['success'] and r['mode'] != 'compile_fail' and r['file'].startswith('knowledge')]
    compile_fail_passes = [r for r in results if r['success'] and r['mode'] == 'compile_fail']
    
    if concept_fails or compile_fail_passes:
        lines.extend([
            "## 编译失败的代码块（concept/）",
            "",
            "| 文件 | 行号 | 模式 | 预览 | 错误信息 |",
            "|:---|:---|:---|:---|:---|",
        ])
        for r in concept_fails:
            preview = r['code_preview'][:40].replace('|', '\\|')
            stderr = r['stderr'][:80].replace('|', '\\|').replace('\n', ' ')
            lines.append(f"| {r['file']} | {r['line']} | {r['mode']} | `{preview}` | {stderr} |")
        for r in compile_fail_passes:
            preview = r['code_preview'][:40].replace('|', '\\|')
            lines.append(f"| {r['file']} | {r['line']} | compile_fail | `{preview}` | 应编译失败但通过了 |")
        lines.append("")
    
    if knowledge_fails:
        lines.extend([
            f"## 编译失败的代码块（knowledge/）",
            f"",
            f"> knowledge/ 中的 {len(knowledge_fails)} 个失败块多为教学片段（不完整代码、故意展示编译错误），",
            f"> 属于预期行为。以下显示前 5 个示例：",
            f"",
            "| 文件 | 行号 | 预览 | 错误信息 |",
            "|:---|:---|:---|:---|",
        ])
        for r in knowledge_fails[:5]:
            preview = r['code_preview'][:40].replace('|', '\\|')
            stderr = r['stderr'][:60].replace('|', '\\|').replace('\n', ' ')
            lines.append(f"| {r['file']} | {r['line']} | `{preview}` | {stderr} |")
        lines.append("")
    
    lines.extend([
        "## 编译通过的代码块（抽样）",
        "",
        "| 文件 | 行号 | 模式 | 预览 |",
        "|:---|:---|:---|:---|",
    ])
    passed_samples = [r for r in results if r['success'] and r['mode'] != 'compile_fail'][:20]
    for r in passed_samples:
        preview = r['code_preview'][:40].replace('|', '\\|')
        lines.append(f"| {r['file']} | {r['line']} | {r['mode']} | `{preview}` |")
    
    lines.append("")
    
    report_dir = Path(REPORT_PATH).parent
    report_dir.mkdir(parents=True, exist_ok=True)
    with open(REPORT_PATH, 'w', encoding='utf-8') as f:
        f.write('\n'.join(lines))

if __name__ == '__main__':
    main()
