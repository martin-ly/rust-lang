import re

t = '- [Ownership（所有权 \\[来源: TRPL Ch. 4\\]）](#ownership所有权-来源-trpl-ch-4)'
print('text:', t)

# Find positions of backslash
for i, c in enumerate(t):
    if c == '\\':
        print(f'Backslash at {i}, next char: {repr(t[i+1])}')

# Build pattern: literal \\[  ...  \\]
prefix = re.escape('\\[')
suffix = re.escape('\\]')
pat = re.compile(prefix + r'来源:\s*[^\]]+' + suffix)
m = pat.search(t)
print()
print('Match:', repr(m.group(0)) if m else None)
print('Start:', m.start() if m else None)
