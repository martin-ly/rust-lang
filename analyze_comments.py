import re

with open('unique_comments.txt', 'r', encoding='utf-8') as f:
    lines = f.readlines()[1:]  # skip first line

# Categorize
categories = {
    'headers': [],
    'short': [],
    'medium': [],
    'long': [],
    'lists': [],
    'links': [],
    'warnings': [],
    'code_markers': [],
}

for line in lines:
    line = line.strip()
    if '|' in line:
        _, text = line.split('|', 1)
        text = text.strip()
        if text.startswith('#'):
            categories['headers'].append(text)
        elif text.startswith('```'):
            categories['code_markers'].append(text)
        elif text.startswith('- ') or re.match(r'^\d+\.', text):
            categories['lists'].append(text)
        elif 'http' in text:
            categories['links'].append(text)
        elif any(e in text for e in ['⚠️', '🔧', '🚀', '✅', '📦', '🎯', '🎉', '📚', '💡', '📝', '🔒', '🌐', '⏱️', '🔍', '📊', '❌', '⚡', '🔴', '🟢', '🟡']):
            categories['warnings'].append(text)
        elif len(text) <= 10:
            categories['short'].append(text)
        elif len(text) <= 30:
            categories['medium'].append(text)
        else:
            categories['long'].append(text)

for cat, items in categories.items():
    print(f'{cat}: {len(items)}')
    for item in items[:15]:
        print(f'  - {item}')
    if len(items) > 15:
        print(f'  ... and {len(items)-15} more')
    print()
