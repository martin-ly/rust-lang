#!/usr/bin/env python3
"""
Fast translation using Ollama with keep_alive.
"""

import os
import re
import json
import time
import sys
import urllib.request

OLLAMA_MODEL = "qwen3.5:latest"
OLLAMA_URL = "http://localhost:11434/api/generate"
BATCH_SIZE = 20
CACHE_FILE = "translation_cache.json"

def extract_chinese_blocks(filepath):
    with open(filepath, "r", encoding="utf-8") as f:
        lines = f.readlines()
    blocks = []
    i = 0
    while i < len(lines):
        if lines[i].startswith("///") or lines[i].startswith("//!"):
            block_type = "///" if lines[i].startswith("///") else "//!"
            block_lines = []
            while i < len(lines) and lines[i].startswith(block_type):
                block_lines.append(lines[i])
                i += 1
            block_text = "".join(block_lines)
            if re.search(r"[\u4e00-\u9fff]", block_text):
                blocks.append(block_text)
        else:
            i += 1
    return blocks

def translate_batch(blocks):
    prompt = (
        "Translate these Chinese Rust doc comments to English. "
        "Preserve exact doc comment style (/// or //!) and markdown. "
        "Output ONLY translations, no explanations. "
        "Separate each translated block with ---BLOCK---.\n\n"
    )
    for idx, block in enumerate(blocks, 1):
        prompt += f"Block {idx}:\n{block}\n\n"

    data = json.dumps({
        "model": OLLAMA_MODEL,
        "prompt": prompt,
        "stream": False,
        "keep_alive": "30m",
        "options": {"num_predict": 2048, "temperature": 0.1}
    }).encode("utf-8")

    req = urllib.request.Request(
        OLLAMA_URL,
        data=data,
        headers={"Content-Type": "application/json"},
        method="POST",
    )

    with urllib.request.urlopen(req, timeout=90) as resp:
        result = json.loads(resp.read().decode("utf-8"))
        return result.get("response", "")

def parse_batch_output(output, expected_count):
    parts = re.split(r"\n?---BLOCK---\n?", output)
    cleaned = []
    for p in parts:
        p = p.strip()
        p = re.sub(r"^Block \d+:\s*", "", p, flags=re.MULTILINE)
        p = p.strip()
        if p:
            cleaned.append(p)
    return cleaned

def load_cache():
    if os.path.exists(CACHE_FILE):
        with open(CACHE_FILE, "r", encoding="utf-8") as f:
            return json.load(f)
    return {}

def save_cache(cache):
    with open(CACHE_FILE, "w", encoding="utf-8") as f:
        json.dump(cache, f, ensure_ascii=False, indent=2)

def apply_translation(filepath, mapping):
    with open(filepath, "r", encoding="utf-8") as f:
        content = f.read()
    lines = content.split("\n")
    new_lines = []
    i = 0
    modified = False

    while i < len(lines):
        if lines[i].startswith("///") or lines[i].startswith("//!"):
            block_type = "///" if lines[i].startswith("///") else "//!"
            block_lines = []
            while i < len(lines) and lines[i].startswith(block_type):
                block_lines.append(lines[i])
                i += 1
            block_text = "\n".join(block_lines)

            if re.search(r"[\u4e00-\u9fff]", block_text):
                already_has_english = False
                if i < len(lines) and lines[i].startswith(block_type):
                    next_lines = []
                    next_i = i
                    while next_i < len(lines) and lines[next_i].startswith(block_type):
                        next_lines.append(lines[next_i])
                        next_i += 1
                    next_text = "\n".join(next_lines)
                    if not re.search(r"[\u4e00-\u9fff]", next_text):
                        already_has_english = True

                if not already_has_english:
                    if block_text in mapping:
                        translated = mapping[block_text]
                        new_lines.extend(block_lines)
                        if translated and translated != block_text:
                            new_lines.extend(translated.split("\n"))
                            modified = True
                    else:
                        new_lines.extend(block_lines)
                else:
                    new_lines.extend(block_lines)
            else:
                new_lines.extend(block_lines)
        else:
            new_lines.append(line)
            i += 1

    if modified:
        with open(filepath, "w", encoding="utf-8") as f:
            f.write("\n".join(new_lines))
    return modified

def main(directories):
    all_blocks = set()
    file_blocks = {}

    for d in directories:
        if not os.path.exists(d):
            continue
        for root, _, files in os.walk(d):
            for fname in files:
                if fname.endswith(".rs"):
                    filepath = os.path.join(root, fname)
                    blocks = extract_chinese_blocks(filepath)
                    if blocks:
                        file_blocks[filepath] = blocks
                        for b in blocks:
                            all_blocks.add(b)

    print(f"Files: {len(file_blocks)}, Unique blocks: {len(all_blocks)}")
    cache = load_cache()
    pending = [b for b in all_blocks if b not in cache]
    print(f"Cached: {len(cache)}, Pending: {len(pending)}")

    if pending:
        total = len(pending)
        for batch_start in range(0, total, BATCH_SIZE):
            batch = pending[batch_start : batch_start + BATCH_SIZE]
            batch_num = batch_start // BATCH_SIZE + 1
            total_batches = (total - 1) // BATCH_SIZE + 1
            print(f"Batch {batch_num}/{total_batches} ({len(batch)} blocks)...", flush=True)

            try:
                start = time.time()
                output = translate_batch(batch)
                elapsed = time.time() - start
                print(f"  API took {elapsed:.1f}s")
                translated = parse_batch_output(output, len(batch))

                if len(translated) != len(batch):
                    print(f"  MISMATCH: expected {len(batch)}, got {len(translated)}")
                    for i in range(min(len(batch), len(translated))):
                        cache[batch[i]] = translated[i]
                else:
                    for orig, trans in zip(batch, translated):
                        cache[orig] = trans
                    print(f"  OK")
            except Exception as e:
                print(f"  ERROR: {e}")

            save_cache(cache)

    print("\nApplying translations...")
    modified_files = []
    for filepath, blocks in file_blocks.items():
        if apply_translation(filepath, cache):
            modified_files.append(filepath)

    print(f"Modified {len(modified_files)} files")
    save_cache(cache)
    print("Done!")

if __name__ == "__main__":
    if len(sys.argv) > 1:
        main(sys.argv[1:])
    else:
        main([
            "crates/c10_networks/src",
            "crates/c11_macro_system/src",
            "crates/c11_macro_system_proc/src",
            "crates/c12_wasm/src",
            "crates/c13_embedded/src",
            "exercises/src",
        ])
