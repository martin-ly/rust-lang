#!/usr/bin/env python3
"""修复 concept/ 中剩余的真实 404 权威来源链接."""
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent / "concept"

# 按字符串长度降序排列，避免短 URL 误替换长 URL
REPLACEMENTS = [
    # WASI Preview 2
    (
        "https://github.com/WebAssembly/WASI/blob/main/preview2/README.md",
        "https://github.com/WebAssembly/WASI/blob/main/specifications/wasi-0.2.4/Overview.md",
    ),
    # Chromium Rust
    (
        "https://www.chromium.org/developers/design-documents/rust/",
        "https://www.chromium.org/chromium-os/developer-library/guides/rust/rust-on-cros/",
    ),
    # Android Rust
    (
        "https://source.android.com/docs/core/architecture/rust",
        "https://security.googleblog.com/2021/05/integrating-rust-into-android-open.html",
    ),
    # wasm-bindgen 子路径（先处理具体路径，再处理根路径）
    (
        "https://rustwasm.github.io/wasm-bindgen/contributing/design/js-objects.html",
        "https://rustwasm.github.io/docs/wasm-bindgen/contributing/design/js-objects-in-rust.html",
    ),
    (
        "https://rustwasm.github.io/wasm-bindgen/contributing/design/index.html",
        "https://rustwasm.github.io/docs/wasm-bindgen/contributing/design/index.html",
    ),
    (
        "https://rustwasm.github.io/wasm-bindgen/contributing/design.html",
        "https://rustwasm.github.io/docs/wasm-bindgen/contributing/design/index.html",
    ),
    (
        "https://rustwasm.github.io/wasm-bindgen/reference/js-promises-and-rust-futures.html",
        "https://rustwasm.github.io/docs/wasm-bindgen/reference/js-promises-and-rust-futures.html",
    ),
    (
        "https://rustwasm.github.io/wasm-bindgen/reference/types/exported-rust-types.html",
        "https://rustwasm.github.io/docs/wasm-bindgen/reference/types/exported-rust-types.html",
    ),
    (
        "https://rustwasm.github.io/wasm-bindgen/reference/types.html",
        "https://rustwasm.github.io/docs/wasm-bindgen/reference/types.html",
    ),
    (
        "https://rustwasm.github.io/wasm-bindgen/reference/receiving-js-closures.html",
        "https://rustwasm.github.io/docs/wasm-bindgen/reference/receiving-js-closures-in-rust.html",
    ),
    (
        "https://rustwasm.github.io/wasm-bindgen/reference/",
        "https://rustwasm.github.io/docs/wasm-bindgen/reference/",
    ),
    (
        "https://rustwasm.github.io/wasm-bindgen/api/wasm_bindgen_futures/",
        "https://docs.rs/wasm-bindgen-futures/latest/wasm_bindgen_futures/",
    ),
    (
        "https://rustwasm.github.io/wasm-bindgen/",
        "https://rustwasm.github.io/docs/wasm-bindgen/",
    ),
]


def main():
    changed = 0
    for p in ROOT.rglob("*.md"):
        text = p.read_text(encoding="utf-8")
        new_text = text
        for old, new in REPLACEMENTS:
            new_text = new_text.replace(old, new)
        if new_text != text:
            p.write_text(new_text, encoding="utf-8")
            changed += 1
            print(f"updated: {p.relative_to(ROOT)}")
    print(f"\n共更新 {changed} 个文件")


if __name__ == "__main__":
    main()
