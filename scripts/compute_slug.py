import re

def github_slug(text):
    text = text.strip()
    text = re.sub(r'\s*\{#[^}]+\}\s*$', '', text)
    text = re.sub(r'\[([^\]]+)\]\([^)]+\)', r'\1', text)
    text = re.sub(r'\\(.)', r'\1', text)
    text = re.sub(r'\*\*(.+?)\*\*', r'\1', text)
    text = re.sub(r'\*(.+?)\*', r'\1', text)
    text = re.sub(r'`(.+?)`', r'\1', text)
    text = text.lower()
    text = re.sub(r'[^\w\s-]', '', text, flags=re.UNICODE)
    text = re.sub(r' ', '-', text.strip())
    text = text.strip('-')
    return text

headers = [
    '4.1 引理：Box<T> ⟹ 堆分配 + 唯一所有权',
    '7.1 测试 1: Rc<RefCell<T>> 循环引用极限',
    '6.4 反命题 4: "Option<T> 完全替代 null"',
]
for h in headers:
    print(github_slug(h))
