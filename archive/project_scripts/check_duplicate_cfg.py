with open('crates/c07_process/src/error/enhanced.rs', 'r', encoding='utf-8') as f:
    content = f.read()
    lines = content.split('\n')

# Check for any line that starts with ##[ (duplicate #)
for i, line in enumerate(lines):
    if line.strip().startswith('##[cfg'):
        print(f"Line {i+1} has duplicate #: {repr(line)}")

# Check for cfg followed by empty line followed by another cfg
for i in range(len(lines) - 2):
    l1 = lines[i].strip()
    l2 = lines[i+1].strip()
    l3 = lines[i+2].strip()
    
    if 'cfg' in l1 and l1.startswith('#[') and l2 == '' and 'cfg' in l3 and l3.startswith('#['):
        print(f"\nFound cfg-gap-cfg at lines {i+1}, {i+2}, {i+3}:")
        for j in range(max(0, i-2), min(len(lines), i+6)):
            marker = ">>> " if j in [i, i+1, i+2] else "    "
            print(f"{marker}{j+1}: {repr(lines[j])}")
