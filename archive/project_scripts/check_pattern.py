with open('crates/c07_process/src/error/enhanced.rs', 'r', encoding='utf-8') as f:
    lines = f.readlines()

# Check for pattern: #[cfg(feature = "async")] followed by empty line followed by #[cfg(feature = "async")]
cfg_line = '#[cfg(feature = "async")]\n'

for i in range(len(lines) - 2):
    if lines[i] == cfg_line and lines[i+1].strip() == '' and lines[i+2] == cfg_line:
        print(f"Found pattern at lines {i+1}, {i+2}, {i+3}:")
        for j in range(max(0, i-2), min(len(lines), i+6)):
            print(f"{j+1}: {repr(lines[j])}")
        print()

# Also check for empty_line_after_outer_attr pattern
for i in range(len(lines) - 2):
    line1 = lines[i].strip()
    line2 = lines[i+1].strip()
    line3 = lines[i+2].strip()
    if line1.startswith('#[cfg') and line2 == '' and (line3.startswith('impl') or line3.startswith('fn') or line3.startswith('struct') or line3.startswith('enum')):
        print(f"Found empty_line_after_outer_attr at lines {i+1}, {i+2}, {i+3}:")
        for j in range(max(0, i-1), min(len(lines), i+5)):
            print(f"{j+1}: {repr(lines[j])}")
        print()
