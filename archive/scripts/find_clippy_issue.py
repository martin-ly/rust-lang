with open('crates/c07_process/src/error/enhanced.rs', 'r', encoding='utf-8') as f:
    lines = f.readlines()

# Find all lines with #[cfg(feature = "async")]
cfg_indices = []
for i, line in enumerate(lines):
    if line.strip() == '#[cfg(feature = "async")]':
        cfg_indices.append(i)

print(f"Found {len(cfg_indices)} cfg attributes at lines: {[i+1 for i in cfg_indices]}\n")

# Check each cfg for the empty_line_after_outer_attr pattern
# This happens when an outer attribute is followed by an empty line, then code
for idx in cfg_indices:
    if idx + 2 < len(lines):
        next_line = lines[idx + 1].strip()
        code_line = lines[idx + 2].strip()
        
        # Check if next line is empty and the following line is actual code (not another attribute)
        is_empty = next_line == ''
        is_code = (code_line.startswith('impl ') or 
                   code_line.startswith('fn ') or 
                   code_line.startswith('pub fn ') or
                   code_line.startswith('struct ') or 
                   code_line.startswith('pub struct ') or
                   code_line.startswith('enum ') or
                   code_line.startswith('pub enum ') or
                   code_line.startswith('trait ') or
                   code_line.startswith('type ') or
                   code_line.startswith('const ') or
                   code_line.startswith('static '))
        
        # But NOT if the line after empty is another attribute
        is_attr = code_line.startswith('#[')
        
        if is_empty and is_code and not is_attr:
            print(f"Potential issue at line {idx+1} (cfg) -> line {idx+2} (empty) -> line {idx+3} (code):")
            for j in range(max(0, idx-1), min(len(lines), idx+5)):
                marker = ">>> " if j == idx + 1 else "    "
                print(f"{marker}{j+1}: {repr(lines[j])}")
            print()

# Check for duplicate cfg (cfg -> empty -> cfg)
print("\n--- Checking for cfg -> empty -> cfg pattern ---")
for i in range(len(lines) - 2):
    l1 = lines[i].strip()
    l2 = lines[i+1].strip()
    l3 = lines[i+2].strip()
    
    if l1 == '#[cfg(feature = "async")]' and l2 == '' and l3 == '#[cfg(feature = "async")]':
        print(f"\n!!! Found duplicate cfg at lines {i+1}, {i+2}, {i+3}:")
        for j in range(max(0, i-2), min(len(lines), i+6)):
            marker = ">>> " if j in [i, i+1, i+2] else "    "
            print(f"{marker}{j+1}: {repr(lines[j])}")
        print()
