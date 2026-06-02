#!/usr/bin/env python3
import re

# Test the regex pattern
text = r'lazy\_static → LazyLock'
print('Input:', repr(text))

try:
    result = re.sub(r'\\(.)', r'\1', text)
    print('Result:', repr(result))
except Exception as e:
    print('Error:', e)

# Alternative without problematic regex
result2 = text.replace('\\_', '_').replace('\\*', '*').replace('\\`', '`')
print('Result2:', repr(result2))
