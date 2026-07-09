from pathlib import Path
import re, sys
sys.path.insert(0, 'scripts')
import concept_config as cc

def title_for(path):
    txt = path.read_text(encoding='utf-8')
    m = re.search(r'^#\s+(.+)$', txt, re.MULTILINE)
    title = m.group(1).strip() if m else path.stem
    return title

summary_text = Path('concept/SUMMARY.md').read_text(encoding='utf-8')
# robust link parser from validate_summary
def parse_links(text):
    links=[]; i=0; n=len(text)
    while i<n:
        if text[i]=='[' and (i==0 or text[i-1]!='\\'):
            depth=1; i+=1; in_code=False; code_delim=''
            while i<n and depth>0:
                if not in_code:
                    if text[i]=='\\' and i+1<n: i+=2; continue
                    if text[i]=='`':
                        j=i
                        while j<n and text[j]=='`': j+=1
                        code_delim=text[i:j]; in_code=True; i=j; continue
                    if text[i]=='[': depth+=1
                    elif text[i]==']': depth-=1
                else:
                    if text[i:i+len(code_delim)]==code_delim: in_code=False; i+=len(code_delim); continue
                i+=1
            if depth==0 and i<n and text[i]=='(':
                j=i+1; pdepth=1
                while j<n and pdepth>0:
                    if text[j]=='\\' and j+1<n: j+=2; continue
                    if text[j]=='(': pdepth+=1
                    elif text[j]==')': pdepth-=1
                    j+=1
                links.append(text[i+1:j-1].strip())
                i=j; continue
        i+=1
    return links

linked = set(Path(p) for p in parse_links(summary_text) if p.endswith('.md'))
files = []
for p in cc.iter_concept_files():
    rel = p.relative_to(cc.CONCEPT_DIR)
    if rel.name == 'SUMMARY.md': continue
    if any(part in {'placeholders'} for part in rel.parts): continue
    if rel.name in {'bilingual_template.md', 'template_deduplication_guide.md', 'audit_checklist.md'}: continue
    if rel.name == 'README.md' and len(rel.parts)==1: continue
    if rel not in linked:
        files.append(rel)

for rel in sorted(files):
    title = title_for(cc.CONCEPT_DIR/rel)
    print(f'{rel.as_posix()}\t{title}')
