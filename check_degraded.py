import re
import pathlib
import subprocess

HAN_RE = re.compile(r'[\u4e00-\u9fff]')
DOC_RE = re.compile(r'^(\s*//[!/]\s)(.*)$')

def get_git_content(path):
    try:
        result = subprocess.run(['git', 'show', f'HEAD:{path}'], capture_output=True, text=True)
        if result.returncode == 0:
            return result.stdout.splitlines()
    except:
        pass
    return None

paths = list(pathlib.Path('crates').rglob('*.rs')) + list(pathlib.Path('examples').rglob('*.rs'))

bad = []
for p in paths:
    if 'target' in str(p):
        continue
    rel = str(p).replace(chr(92), '/')
    git_lines = get_git_content(rel)
    if not git_lines:
        continue
    try:
        cur_lines = p.read_text(encoding='utf-8').splitlines()
    except:
        continue
    
    git_doc_lines = set()
    for line in git_lines:
        m = DOC_RE.match(line)
        if m:
            git_doc_lines.add(m.group(2).strip())
    
    for i, line in enumerate(cur_lines):
        m = DOC_RE.match(line)
        if m:
            text = m.group(2).strip()
            if text not in git_doc_lines and not HAN_RE.search(text):
                if i > 0:
                    pm = DOC_RE.match(cur_lines[i-1])
                    if pm and HAN_RE.search(pm.group(2)) and not re.search(r'[a-zA-Z]{2,}', pm.group(2)):
                        orig = pm.group(2).strip()
                        if '（）' in text or '()' in text or len(text) < len(orig) * 0.3:
                            if text not in ['', '-', '*', '|', '#', '##', '###']:
                                bad.append((rel, orig, text))

print(f'Found {len(bad)} actual degraded translations added by script')
for rel, orig, text in bad[:30]:
    print(f'  {rel}')
    print(f'    {orig}')
    print(f'    → {text}')
