import re, subprocess, tempfile, os, sys

files = [
    'concept/06_ecosystem/11_domain_applications/26_zero_copy_parsing_in_rust.md',
    'concept/06_ecosystem/11_domain_applications/27_ownership_aware_algorithms.md',
    'concept/06_ecosystem/11_domain_applications/28_unsafe_algorithm_invariants.md',
]

def extract_blocks(text):
    # Match ```lang,opts\ncode\n```
    pattern = r'```([a-zA-Z0-9_,]+)\n(.*?)```'
    return re.findall(pattern, text, re.DOTALL)

errors = []
for f in files:
    with open(f,'r',encoding='utf-8') as fh:
        text=fh.read()
    blocks = extract_blocks(text)
    print(f'\n{f}: {len(blocks)} blocks')
    for i, (header, code) in enumerate(blocks):
        header = header.strip()
        # Skip non-rust and special annotations
        if not header.startswith('rust'):
            continue
        if 'ignore' in header or 'pseudo' in header or 'nightly' in header or 'nostd' in header or 'compile_fail' in header:
            continue
        code = code.strip()
        if not code:
            continue
        with tempfile.NamedTemporaryFile('w', suffix='.rs', delete=False) as tf:
            tf.write(code)
            path=tf.name
        try:
            r = subprocess.run(['rustc','--edition','2024',path], capture_output=True, text=True, timeout=30)
            if r.returncode != 0:
                err = r.stderr.split('\n')[0]
                print(f'  block {i} ({header}) FAIL: {err}')
                errors.append((f, i, header, err))
            else:
                print(f'  block {i} ({header}) OK')
        finally:
            os.unlink(path)

if errors:
    print(f'\nTotal errors: {len(errors)}')
    sys.exit(1)
else:
    print('\nAll compilable blocks OK')
