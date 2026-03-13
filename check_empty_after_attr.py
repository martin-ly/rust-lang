with open('crates/c07_process/src/error/enhanced.rs', 'r', encoding='utf-8') as f:
    lines = f.readlines()

# Check for outer attribute followed by empty line followed by code
# This is what empty_line_after_outer_attr lint checks
for i in range(len(lines) - 2):
    line1 = lines[i].rstrip()  # Keep trailing whitespace for check
    line2 = lines[i+1].rstrip()
    line3 = lines[i+2].strip()
    
    # Check if line1 is an outer attribute (starts with #[])
    is_outer_attr = line1.startswith('#[') and not line1.startswith('#![')
    # Line 2 should be empty (only whitespace or nothing)
    is_empty_line = line2 == ''
    # Line 3 should be code (not another attribute)
    is_code = (line3.startswith('impl ') or 
               line3.startswith('fn ') or 
               line3.startswith('pub fn ') or
               line3.startswith('struct ') or 
               line3.startswith('pub struct ') or
               line3.startswith('enum ') or
               line3.startswith('mod ') or
               line3.startswith('use ') or
               line3.startswith('const ') or
               line3.startswith('static ') or
               line3.startswith('type '))
    
    if is_outer_attr and is_empty_line and is_code:
        print(f"Potential empty_line_after_outer_attr at lines {i+1}-{i+3}:")
        for j in range(max(0, i-1), min(len(lines), i+5)):
            marker = ">>> " if j == i+1 else "    "
            print(f"{marker}{j+1}: {repr(lines[j])}")
        print()
        
        # Suggest fix: delete the empty line
        print(f"Fix: Delete line {i+2} (the empty line)")
        print("-" * 50)
