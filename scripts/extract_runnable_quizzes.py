#!/usr/bin/env python3
"""Extract runnable rust code blocks from L1-L2 concept files for test generation."""

import re
from pathlib import Path

FILES = [
    "concept/01_foundation/04_type_system.md",
    "concept/01_foundation/07_control_flow.md",
    "concept/01_foundation/08_collections.md",
    "concept/01_foundation/09_strings_and_text.md",
    "concept/01_foundation/10_error_handling_basics.md",
    "concept/01_foundation/10_numerics.md",
    "concept/01_foundation/11_modules_and_paths.md",
    "concept/01_foundation/12_attributes_and_macros.md",
    "concept/01_foundation/15_closure_basics.md",
    "concept/02_intermediate/10_module_system.md",
]

def extract_blocks(filepath: str):
    with open(filepath, "r", encoding="utf-8") as f:
        content = f.read()
    # Match ```rust blocks without compile_fail, ignore, no_run markers
    pattern = r"```rust\n(.*?)```"
    blocks = re.findall(pattern, content, re.DOTALL)
    runnable = []
    for b in blocks:
        first_line = b.split("\n")[0].strip()
        if any(tag in first_line for tag in ["compile_fail", "ignore", "no_run", "edition2024", "edition2021"]):
            continue
        if "fn main()" in b:
            runnable.append(b)
    return blocks, runnable

print("File | Total blocks | Runnable (fn main)")
print("-" * 50)
all_runnable = []
for f in FILES:
    blocks, runnable = extract_blocks(f)
    print(f"{Path(f).name:30} | {len(blocks):4} | {len(runnable):4}")
    for b in runnable:
        all_runnable.append((f, b))

print(f"\nTotal runnable blocks: {len(all_runnable)}")
