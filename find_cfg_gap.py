with open('crates/c07_process/src/error/enhanced.rs', 'r', encoding='utf-8') as f:
    lines = f.readlines()

# Find any cfg attribute followed by whitespace-only line followed by another attribute
for i in range(len(lines) - 2):
    l1 = lines[i].strip()
    l2_stripped = lines[i+1].strip()
    l2_raw = lines[i+1]
    l3 = lines[i+2].strip()
    
    # Check if l1 is a cfg attribute, l2 is whitespace-only, l3 is an attribute
    if (l1.startswith('#[cfg') and 
        l2_stripped == '' and 
        l3.startswith('#[')):
        print(f"Found cfg -> empty -> attr at lines {i+1}, {i+2}, {i+3}:")
        for j in range(max(0, i-1), min(len(lines), i+5)):
            marker = ">>> " if j in [i, i+1, i+2] else "    "
            print(f"{marker}{j+1}: {repr(lines[j])}")
        print()
