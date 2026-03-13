with open('crates/c07_process/src/error/enhanced.rs', 'r', encoding='utf-8') as f:
    lines = f.readlines()

# Check for pattern: #[cfg(feature = "async")] followed by empty line followed by another attribute
cfg_line = '#[cfg(feature = "async")]'

for i in range(len(lines) - 2):
    line1 = lines[i].strip()
    line2 = lines[i+1].strip()
    line3 = lines[i+2].strip()
    
    if line1 == cfg_line and line2 == '' and line3.startswith('#['):
        print(f"Found at lines {i+1}, {i+2}, {i+3}:")
        for j in range(max(0, i-2), min(len(lines), i+8)):
            marker = ">>> " if j == i+1 else "    "
            print(f"{marker}{j+1}: {repr(lines[j])}")
        print()
