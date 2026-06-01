#!/usr/bin/env python3
"""
Translate Chinese doc comments using Google Translate via deep-translator.
"""

import os
import re
import json
import time
from deep_translator import GoogleTranslator

CACHE_FILE = "google_translation_cache.json"
BATCH_SAVE_INTERVAL = 20  # Save cache every N translations


def load_cache():
    if os.path.exists(CACHE_FILE):
        with open(CACHE_FILE, "r", encoding="utf-8") as f:
            return json.load(f)
    return {}


def save_cache(cache):
    with open(CACHE_FILE, "w", encoding="utf-8") as f:
        json.dump(cache, f, ensure_ascii=False, indent=2)


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


def translate_block(translator, block_text):
    """Translate a block, preserving prefixes."""
    lines = block_text.split("\n")
    prefix = "///" if lines[0].startswith("///") else "//!"

    # Extract just the text content (remove prefixes)
    content_lines = []
    for line in lines:
        if line.startswith(prefix + " "):
            content_lines.append(line[len(prefix)+1:])
        elif line.startswith(prefix):
            content_lines.append(line[len(prefix):])
        else:
            content_lines.append(line)

    content = "\n".join(content_lines)

    # Skip if no actual Chinese text
    if not re.search(r"[\u4e00-\u9fff]", content):
        return block_text

    try:
        translated = translator.translate(content)
    except Exception as e:
        print(f"    Translation error: {e}")
        return None

    # Re-add prefixes
    translated_lines = []
    for line in translated.split("\n"):
        translated_lines.append(prefix + " " + line)

    return "\n".join(translated_lines)


def apply_translation(filepath, mapping):
    with open(filepath, "r", encoding="utf-8") as f:
        content = f.read()

    lines = content.split("\n")
    new_lines = []
    i = 0
    modified = False

    while i < len(lines):
        line = lines[i]
        if line.startswith("///") or line.startswith("//!"):
            block_type = "///" if line.startswith("///") else "//!"
            block_lines = []
            while i < len(lines) and lines[i].startswith(block_type):
                block_lines.append(lines[i])
                i += 1
            block_text = "\n".join(block_lines)

            if re.search(r"[\u4e00-\u9fff]", block_text):
                # Check if next block is already English
                already_english = False
                if i < len(lines) and lines[i].startswith(block_type):
                    next_lines = []
                    next_i = i
                    while next_i < len(lines) and lines[next_i].startswith(block_type):
                        next_lines.append(lines[next_i])
                        next_i += 1
                    next_text = "\n".join(next_lines)
                    if not re.search(r"[\u4e00-\u9fff]", next_text):
                        already_english = True

                if not already_english:
                    if block_text in mapping:
                        translated = mapping[block_text]
                        if translated and translated != block_text:
                            new_lines.extend(block_lines)
                            new_lines.extend(translated.split("\n"))
                            modified = True
                        else:
                            new_lines.extend(block_lines)
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


def main():
    directories = [
        "crates/c10_networks/src",
        "crates/c11_macro_system/src",
        "crates/c11_macro_system_proc/src",
        "crates/c12_wasm/src",
        "crates/c13_embedded/src",
        "exercises/src",
    ]

    print("Collecting Chinese doc comment blocks...")
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
        translator = GoogleTranslator(source="zh-CN", target="en")
        print("Translating...")

        total = len(pending)
        for idx, block in enumerate(pending, 1):
            print(f"  {idx}/{total}...", end="", flush=True)
            start = time.time()
            translated = translate_block(translator, block)
            elapsed = time.time() - start

            if translated:
                cache[block] = translated
                print(f" OK ({elapsed:.1f}s)")
            else:
                print(f" SKIP")

            if idx % BATCH_SAVE_INTERVAL == 0:
                save_cache(cache)
                print(f"  Cache saved ({len(cache)} entries)")

            # No delay - process as fast as possible

        save_cache(cache)

    print("\nApplying translations to files...")
    modified_files = []
    for filepath, blocks in file_blocks.items():
        if apply_translation(filepath, cache):
            modified_files.append(filepath)

    print(f"\nModified {len(modified_files)} files")
    save_cache(cache)
    print("Done!")


if __name__ == "__main__":
    main()
