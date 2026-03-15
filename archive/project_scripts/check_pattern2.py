with open('crates/c07_process/src/error/enhanced.rs', 'r', encoding='utf-8') as f:
    lines = f.readlines()

# Check for pattern: outer attribute followed by empty line followed by code
# This triggers empty_line_after_outer_attr
for i in range(len(lines) - 2):
    line1 = lines[i].strip()
    line2 = lines[i+1].strip()
    line3 = lines[i+2].strip()
    
    # Check if line1 is an outer attribute (starts with #[] but not #![])
    is_outer_attr = line1.startswith('#[') and not line1.startswith('#![')
    is_empty = line2 == ''
    is_code = (line3.startswith('impl ') or 
               line3.startswith('fn ') or 
               line3.startswith('pub fn ') or
               line3.startswith('struct ') or 
               line3.startswith('pub struct ') or
               line3.startswith('enum ') or
               line3.startswith('pub enum ') or
               line3.startswith('trait ') or
               line3.startswith('pub trait ') or
               line3.startswith('type ') or
               line3.startswith('pub type ') or
               line3.startswith('use ') or
               line3.startswith('mod ') or
               line3.startswith('const ') or
               line3.startswith('static '))
    
    if is_outer_attr and is_empty and is_code:
        print(f"Found at lines {i+1}, {i+2}, {i+3}:")
        for j in range(max(0, i-2), min(len(lines), i+6)):
            marker = ">>> " if j == i else "    "
            print(f"{marker}{j+1}: {repr(lines[j])}")
        print()
