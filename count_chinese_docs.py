import os
import re

def count_docs(filepath):
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()
    doc_comments = re.findall(r'^\s*///.*$', content, re.MULTILINE)
    mod_docs = re.findall(r'^\s*//!.*$', content, re.MULTILINE)
    chinese_docs = [l for l in doc_comments + mod_docs if re.search(r'[\u4e00-\u9fff]', l)]
    return len(chinese_docs), len(doc_comments) + len(mod_docs)

files = [
    'crates/c02_type_system/examples/run_all_examples.rs',
    'crates/c03_control_fn/src/lib.rs',
    'crates/c05_threads/src/demo.rs',
    'crates/c06_async/examples/async_database_example.rs',
    'crates/c07_process/src/concurrency/atomic.rs',
    'crates/c08_algorithms/src/algorithms/backtracking/mod.rs',
]

for f in files:
    if os.path.exists(f):
        c, t = count_docs(f)
        print(f"{f}: {c} chinese / {t} total doc lines")
