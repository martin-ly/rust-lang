with open('crates/c07_process/src/error/enhanced.rs', 'r', encoding='utf-8') as f:
    lines = f.readlines()

cfg_attr = '#[cfg(feature = "async")]'

for i in range(len(lines) - 2):
    l1 = lines[i].strip()
    l2 = lines[i+1].strip()
    l3 = lines[i+2].strip()
    
    if l1 == cfg_attr and l2 == '' and l3 == cfg_attr:
        print(f'Found duplicate cfg at lines {i+1}, {i+2}, {i+3}:')
        for j in range(max(0, i-2), min(len(lines), i+6)):
            print(f'{j+1}: {repr(lines[j])}')
        print()
        
        # Fix: remove the empty line and the duplicate cfg
        print(f'Fixing by removing line {i+2} (empty) and line {i+3} (duplicate cfg)...')
        del lines[i+1:i+3]
        
        # Write back
        with open('crates/c07_process/src/error/enhanced.rs', 'w', encoding='utf-8') as f:
            f.writelines(lines)
        print('Fixed!')
        break
else:
    print('No duplicate cfg pattern found in current file.')
    print('Checking if the pattern was already fixed...')
