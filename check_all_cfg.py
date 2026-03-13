with open('crates/c07_process/src/error/enhanced.rs', 'r', encoding='utf-8') as f:
    lines = f.readlines()

cfg_line = '#[cfg(feature = "async")]'

print("All positions of cfg attributes:")
for i, line in enumerate(lines):
    if line.strip() == cfg_line:
        context = []
        for j in range(max(0, i-1), min(len(lines), i+4)):
            marker = ">>>" if j == i else "   "
            context.append(f"{marker}{j+1}: {repr(lines[j])}")
        print(f"\nLine {i+1}:")
        print("\n".join(context))
