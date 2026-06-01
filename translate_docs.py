#!/usr/bin/env python3
"""
Translate Chinese doc comments to English in Rust source files.
Uses local Ollama API for translation.
"""

import os
import re
import json
import time
import sys
import urllib.request
from pathlib import Path

OLLAMA_MODEL = "qwen3.5:latest"
OLLAMA_URL = "http://localhost:11434/api/generate"
BATCH_SIZE = 30  # blocks per batch
CACHE_FILE = "translation_cache.json"


def extract_chinese_blocks(filepath):
    """Extract all Chinese-only doc comment blocks from a file."""
    with open(filepath, "r", encoding="utf-8") as f:
        lines = f.readlines()

    blocks = []
    i = 0
    while i < len(lines):
        line = lines[i]
        if line.startswith("///") or line.startswith("//!"):
            block_type = "///" if line.startswith("///") else "//!"
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
    """Send a batch of blocks to Ollama for translation."""
    prompt = (
        "Translate these Chinese Rust doc comment blocks to English. "
        "Preserve the doc comment style (/// or //!) and markdown formatting. "
        "Output each translated block separated by ---BLOCK--- on its own line. "
        "Do not add explanations, only output the translations.\n\n"
    )
    for idx, block in enumerate(blocks, 1):
        prompt += f"Block {idx}:\n{block}\n\n"

    data = json.dumps(
        {"model": OLLAMA_MODEL, "prompt": prompt, "stream": False}
    ).encode("utf-8")

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
    """Parse Ollama output into individual translated blocks."""
    parts = re.split(r"\n?---BLOCK---\n?", output)
    # Filter out empty strings
    cleaned = []
    for p in parts:
        p = p.strip()
        # Remove "Block N:" prefixes
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


def apply_translation(file_path, mapping):
    """Apply translations to a single file. Returns True if modified."""
    with open(file_path, "r", encoding="utf-8") as f:
        content = f.read()

    original_content = content
    lines = content.split("\n")
    new_lines = []
    i = 0
    modified = False

    while i < len(lines):
        line = lines[i]
        if line.startswith("///") or line.startswith("//!"):
            block_type = "///" if line.startswith("///") else "//!"
            block_lines = []
            start_i = i
            while i < len(lines) and lines[i].startswith(block_type):
                block_lines.append(lines[i])
                i += 1
            block_text = "\n".join(block_lines)

            if re.search(r"[\u4e00-\u9fff]", block_text):
                # Check if next block is already English translation
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
                            print(f"  Warning: empty translation for block in {file_path}")
                    else:
                        print(f"  Warning: missing translation for block in {file_path}")
                        print(f"    Block preview: {block_text[:80]}...")
                        new_lines.extend(block_lines)
                else:
                    new_lines.extend(block_lines)
            else:
                new_lines.extend(block_lines)
        else:
            new_lines.append(line)
            i += 1

    if modified:
        with open(file_path, "w", encoding="utf-8") as f:
            f.write("\n".join(new_lines))

    return modified


def main(directories):
    # Step 1: Collect all unique Chinese blocks
    print(f"Collecting Chinese doc comment blocks from {directories}...")
    all_blocks = set()
    file_blocks = {}

    for d in directories:
        if not os.path.exists(d):
            print(f"Directory not found: {d}")
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

    print(f"Found {len(file_blocks)} files with {len(all_blocks)} unique Chinese blocks")

    # Step 2: Load cache and determine what needs translation
    cache = load_cache()
    pending = [b for b in all_blocks if b not in cache]
    print(f"Already cached: {len(cache)}, Pending: {len(pending)}")

    # Step 3: Translate pending blocks in batches
    if pending:
        print("Translating with Ollama...")
        total = len(pending)
        for batch_start in range(0, total, BATCH_SIZE):
            batch = pending[batch_start : batch_start + BATCH_SIZE]
            batch_num = batch_start // BATCH_SIZE + 1
            total_batches = (total - 1) // BATCH_SIZE + 1
            print(f"  Batch {batch_num}/{total_batches} ({len(batch)} blocks)...")

            max_retries = 2
            for attempt in range(max_retries):
                try:
                    output = translate_batch(batch)
                    translated = parse_batch_output(output, len(batch))

                    if len(translated) != len(batch):
                        print(
                            f"    Mismatch: expected {len(batch)}, got {len(translated)}. Retrying..."
                        )
                        if attempt < max_retries - 1:
                            time.sleep(1)
                            continue
                        else:
                            print(f"    Warning: mapping partial results")
                            for i in range(min(len(batch), len(translated))):
                                cache[batch[i]] = translated[i]
                            break
                    else:
                        for orig, trans in zip(batch, translated):
                            cache[orig] = trans
                        break
                except Exception as e:
                    print(f"    Error: {e}")
                    if attempt < max_retries - 1:
                        time.sleep(1)
                    else:
                        print(f"    Failed after retries")

            save_cache(cache)

    # Step 4: Apply translations to files
    print("\nApplying translations to files...")
    modified_files = []
    for filepath, blocks in file_blocks.items():
        if apply_translation(filepath, cache):
            modified_files.append(filepath)

    print(f"\nModified {len(modified_files)} files")
    for f in modified_files:
        print(f"  {f}")

    save_cache(cache)
    print("\nDone!")


if __name__ == "__main__":
    if len(sys.argv) > 1:
        directories = sys.argv[1:]
    else:
        directories = [
            "crates/c10_networks/src",
            "crates/c11_macro_system/src",
            "crates/c11_macro_system_proc/src",
            "crates/c12_wasm/src",
            "crates/c13_embedded/src",
            "exercises/src",
        ]
    main(directories)
