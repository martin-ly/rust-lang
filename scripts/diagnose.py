import re, os

SOURCE_PATTERNS = [
    r"\[来源[：:]\s*[^\]]+\]",
    r"\[学术来源[：:][^\]]*\]",
    r"\[工业来源[：:][^\]]*\]",
    r"> \*\*来源[：:][^\*]*\*\*",
    r"> \*\*权威来源[：:][^\*]*\*\*",
    r">\s*\*\*\[[^\]]+\]\*\*",
    r"> \*\*来源\*\*[：:]",
    r"\[RFC\s+\d+[^\]]*\]",
    r"\[POPL\s+\d{4}[^\]]*\]",
    r"\[PLDI\s+\d{4}[^\]]*\]",
    r"\[ECOOP\s+\d{4}[^\]]*\]",
    r"\[SOSP\s+\d{4}[^\]]*\]",
    r"\[OOPSLA\s+\d{4}[^\]]*\]",
    r"\[JFP\s+\d{4}[^\]]*\]",
    r"\[ICFP\s+\d{4}[^\]]*\]",
    r"\[FM\s+\d{4}[^\]]*\]",
    r"\[VSTTE\s+\d{4}[^\]]*\]",
    r"\[RustBelt[^\]]*\]",
    r"\[Iris[^\]]*\]",
    r"\[Kani[^\]]*\]",
    r"\[Verus[^\]]*\]",
    r"\[Creusot[^\]]*\]",
    r"\[Prusti[^\]]*\]",
    r"\[Aeneas[^\]]*\]",
    r"\[RefinedRust[^\]]*\]",
    r"\[Miri[^\]]*\]",
    r"Jung et al\.,\s*\*[^\*]+\*\s*,\s*(?:POPL|PLDI|ECOOP|OOPSLA|JFP|ICFP)\s+\d{4}",
    r"O'Hearn\s+\d{4}",
    r"Girard\s+\d{4}",
    r"Tofte-Talpin\s+\d{4}",
    r"\[Wikipedia[：:]?\s*[^\]]+\]",
    r"\[Rust Reference[^\]]*\]",
    r"\[Rust Book[^\]]*\]",
    r"\[Rustonomicon[^\]]*\]",
    r"\[The Rust Programming Language[^\]]*\]",
    r"\[Rust\s+\d+\.\d+\s+Release Notes\]",
    r"\[Rust\s+\d{4}\s+Edition\s+Guide\]",
    r"\[RFC\s+\d{4}[^\]]*\]",
    r"来源[：:]\s*\[[^\]]+\]\s*·\s*[^\n]*✅",
    r"来源[：:]\s*\[[^\]]+\]\s*·\s*[^\n]*🔍",
]

def check(content):
    total = 0
    for p in SOURCE_PATTERNS:
        total += len(re.findall(p, content, re.IGNORECASE))
    paragraphs = [p for p in re.split(r'\n\s*\n', content) if len(p.strip()) > 20]
    claims = len(re.findall(r'^(?:>|#+\s*\S|\*\*定理|\*\*定义|\*\*公理)', content, re.MULTILINE))
    return total, len(paragraphs), claims

results = []
for root, dirs, fs in os.walk("concept"):
    for fname in fs:
        if not fname.endswith(".md"):
            continue
        if not re.match(r"^\d{2}_[a-z_]+\.md$", fname):
            continue
        filepath = os.path.join(root, fname)
        with open(filepath, "r", encoding="utf-8") as f:
            content = f.read()
        ann, para, claims = check(content)
        denom = para + claims * 2
        rate = ann / denom if denom > 0 else 0
        results.append((filepath, rate, ann, denom))

results.sort(key=lambda x: x[1])
print("Bottom 30 files (lowest source rate):")
for path, rate, ann, denom in results[:30]:
    need = int(0.30 * denom) + 1 - ann
    print(f"  {os.path.basename(path)}: {rate*100:.1f}% ({ann}/{denom}) -> +{max(0,need)} to 30%")

# Calculate total
total_ann = sum(r[2] for r in results)
total_denom = sum(r[3] for r in results)
print(f"\nTotal: {total_ann}/{total_denom} = {total_ann/total_denom*100:.2f}%")
print(f"Sources needed for 30%: {int(0.30 * total_denom) - total_ann}")
