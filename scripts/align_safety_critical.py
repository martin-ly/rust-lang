import os

AUTHORITY_MAP = {
    '10_standards/DO_178C': '> **权威来源**: [DO-178C / ED-12C](https://www.rtca.org/), [Ferrocene](https://ferrous-systems.com/ferrocene/), [Rust Reference](https://doc.rust-lang.org/reference/)\n>\n> **权威来源对齐变更日志**: 2026-05-19 新增 DO-178C 标准来源标注、Ferrocene 认证工具链引用 [来源: Authority Source Sprint Batch 8]',
    '10_standards/IEC_61508': '> **权威来源**: [IEC 61508](https://www.iec.ch/), [Rust Reference](https://doc.rust-lang.org/reference/), [Ferrocene](https://ferrous-systems.com/ferrocene/)\n>\n> **权威来源对齐变更日志**: 2026-05-19 新增 IEC 61508 标准来源标注、Rust 安全关键应用引用 [来源: Authority Source Sprint Batch 8]',
    '10_standards/ISO_26262': '> **权威来源**: [ISO 26262](https://www.iso.org/standard/68383.html), [MISRA C](https://misra.org.uk/), [Rust Reference](https://doc.rust-lang.org/reference/)\n>\n> **权威来源对齐变更日志**: 2026-05-19 新增 ISO 26262 标准来源标注、MISRA C 对标引用 [来源: Authority Source Sprint Batch 8]',
    '10_standards/MISRA_C': '> **权威来源**: [MISRA C](https://misra.org.uk/), [ISO 26262](https://www.iso.org/standard/68383.html), [Rust Reference](https://doc.rust-lang.org/reference/)\n>\n> **权威来源对齐变更日志**: 2026-05-19 新增 MISRA C 标准来源标注、Rust 安全编码规范引用 [来源: Authority Source Sprint Batch 8]',
    '10_standards/REGULATORY': '> **权威来源**: [FAA](https://www.faa.gov/), [EASA](https://www.easa.europa.eu/), [FDA](https://www.fda.gov/), [Rust Reference](https://doc.rust-lang.org/reference/)\n>\n> **权威来源对齐变更日志**: 2026-05-19 新增监管机构标准来源标注 [来源: Authority Source Sprint Batch 8]',
    '07_case_studies/CASE_STUDY_01': '> **权威来源**: [Ferrocene](https://ferrous-systems.com/ferrocene/), [TUV SUD](https://www.tuvsud.com/), [Rust Reference](https://doc.rust-lang.org/reference/)\n>\n> **权威来源对齐变更日志**: 2026-05-19 新增 Ferrocene 认证案例来源标注 [来源: Authority Source Sprint Batch 8]',
    '07_case_studies/CASE_STUDY_02': '> **权威来源**: [NASA](https://www.nasa.gov/), [cFS](https://cfs.gsfc.nasa.gov/), [Rust Reference](https://doc.rust-lang.org/reference/)\n>\n> **权威来源对齐变更日志**: 2026-05-19 新增 NASA cFS Rust 案例来源标注 [来源: Authority Source Sprint Batch 8]',
    '07_case_studies/CASE_STUDY_03': '> **权威来源**: [ISO 26262](https://www.iso.org/standard/68383.html), [AUTOSAR](https://www.autosar.org/), [Rust Reference](https://doc.rust-lang.org/reference/)\n>\n> **权威来源对齐变更日志**: 2026-05-19 新增汽车 ECU Rust 应用案例来源标注 [来源: Authority Source Sprint Batch 8]',
    '07_case_studies/CASE_STUDY_04': '> **权威来源**: [FDA](https://www.fda.gov/), [IEC 62304](https://www.iec.ch/), [Rust Reference](https://doc.rust-lang.org/reference/)\n>\n> **权威来源对齐变更日志**: 2026-05-19 新增医疗器械 Rust 应用案例来源标注 [来源: Authority Source Sprint Batch 8]',
    '07_case_studies/CASE_STUDY_05': '> **权威来源**: [CENELEC](https://www.cenelec.eu/), [EN 50128](https://www.cenelec.eu/), [Rust Reference](https://doc.rust-lang.org/reference/)\n>\n> **权威来源对齐变更日志**: 2026-05-19 新增铁路信号 Rust 应用案例来源标注 [来源: Authority Source Sprint Batch 8]',
    '07_case_studies/CASE_STUDY_06': '> **权威来源**: [ISO 26262](https://www.iso.org/standard/68383.html), [SAE J3016](https://www.sae.org/standards/content/j3016_202104/), [Rust Reference](https://doc.rust-lang.org/reference/)\n>\n> **权威来源对齐变更日志**: 2026-05-19 新增自动驾驶 Rust 应用案例来源标注 [来源: Authority Source Sprint Batch 8]',
    '09_reference/GLOSSARY': '> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [ISO 26262](https://www.iso.org/standard/68383.html), [IEC 61508](https://www.iec.ch/), [DO-178C](https://www.rtca.org/)\n>\n> **权威来源对齐变更日志**: 2026-05-19 新增安全关键术语标准来源标注 [来源: Authority Source Sprint Batch 8]',
    'default': '> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [Rustonomicon](https://doc.rust-lang.org/nomicon/), [Ferrocene](https://ferrous-systems.com/ferrocene/), [Rust Safety Critical WG](https://github.com/rust-safety-critical/wg)\n>\n> **权威来源对齐变更日志**: 2026-05-19 新增 Rust 安全关键生态系统来源标注 [来源: Authority Source Sprint Batch 8]'
}

STATUS_BLOCK = '\n---\n\n**最后更新**: 2026-05-19\n**状态**: ✅ 权威来源对齐完成 (Batch 8)\n'

def get_authority_block(filepath):
    norm = filepath.replace(chr(92), '/')
    for key, value in AUTHORITY_MAP.items():
        if key in norm:
            return value
    return AUTHORITY_MAP['default']

def process_file(filepath):
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()
    
    if '权威来源对齐完成' in content:
        return False
    
    authority = get_authority_block(filepath)
    lines = content.split('\n')
    new_lines = []
    inserted = False
    
    for i, line in enumerate(lines):
        new_lines.append(line)
        if not inserted and line.startswith('# ') and i > 0:
            new_lines.append('')
            new_lines.append(authority)
            inserted = True
    
    if not inserted:
        new_lines.insert(0, authority)
    
    result = '\n'.join(new_lines)
    if not result.rstrip().endswith('---'):
        result = result.rstrip() + STATUS_BLOCK
    else:
        result = result.rstrip() + '\n' + STATUS_BLOCK.lstrip()
    
    with open(filepath, 'w', encoding='utf-8') as f:
        f.write(result)
    
    return True

def main():
    base_dir = 'knowledge/04_expert/safety_critical'
    processed = 0
    
    for root, dirs, files in os.walk(base_dir):
        for fname in files:
            if fname.endswith('.md'):
                filepath = os.path.join(root, fname)
                if process_file(filepath):
                    processed += 1
                    print(f'Processed: {filepath}')
    
    print(f'\nTotal processed: {processed}')

if __name__ == '__main__':
    main()
