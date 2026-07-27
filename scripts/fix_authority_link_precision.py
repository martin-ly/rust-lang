#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""批量修复 concept/ 中指向权威来源首页的 S1 链接。

读取 `scripts/authority_link_precision.py --json` 的输出，按链接文本精确映射到
具体章节 URL，执行替换。仅处理白名单中的确切链接文本，避免误改。

用法：
  python scripts/authority_link_precision.py --json tmp/authority_link_precision.json
  python scripts/fix_authority_link_precision.py --json tmp/authority_link_precision.json --apply
"""
from __future__ import annotations

import argparse
import json
import os
import re
import sys
from typing import Dict, List, Tuple

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# 链接文本（大小写不敏感，去首尾空格）→ 目标 URL
LINK_TEXT_TO_URL: Dict[str, str] = {
    # Rust Reference
    "rust reference — lifetimes": "https://doc.rust-lang.org/reference/lifetimes.html",
    "rust reference: lifetimes": "https://doc.rust-lang.org/reference/lifetimes.html",
    "rust reference — lifetime elision": "https://doc.rust-lang.org/reference/lifetime-elision.html",
    "rust reference: lifetime elision": "https://doc.rust-lang.org/reference/lifetime-elision.html",
    "rust reference: lifetime resolution": "https://doc.rust-lang.org/reference/lifetime-elision.html",
    "rust reference — variance": "https://doc.rust-lang.org/reference/subtyping.html",
    "rust reference: variance": "https://doc.rust-lang.org/reference/subtyping.html",
    "rust reference — subtyping": "https://doc.rust-lang.org/reference/subtyping.html",
    "rust reference: subtyping": "https://doc.rust-lang.org/reference/subtyping.html",
    "rust reference — type coercions": "https://doc.rust-lang.org/reference/type-coercions.html",
    "rust reference: type coercions": "https://doc.rust-lang.org/reference/type-coercions.html",
    "rust reference — types": "https://doc.rust-lang.org/reference/types.html",
    "rust reference: types": "https://doc.rust-lang.org/reference/types.html",
    "rust reference — ownership": "https://doc.rust-lang.org/reference/ownership.html",
    "rust reference: ownership": "https://doc.rust-lang.org/reference/ownership.html",
    "rust reference — unsafe rust": "https://doc.rust-lang.org/reference/unsafe-blocks.html",
    "rust reference: unsafe rust": "https://doc.rust-lang.org/reference/unsafe-blocks.html",
    "rust reference: unsafety": "https://doc.rust-lang.org/reference/unsafe-blocks.html",
    "rust reference — pointer types": "https://doc.rust-lang.org/reference/types/pointer.html",
    "rust reference: pointer types": "https://doc.rust-lang.org/reference/types/pointer.html",
    "rust reference — external blocks": "https://doc.rust-lang.org/reference/items/external-blocks.html",
    "rust reference: external blocks": "https://doc.rust-lang.org/reference/items/external-blocks.html",
    "rust reference — ffi": "https://doc.rust-lang.org/reference/items/external-blocks.html",
    "rust reference: ffi": "https://doc.rust-lang.org/reference/items/external-blocks.html",
    "rust reference — send and sync": "https://doc.rust-lang.org/reference/special-types-and-traits.html",
    "rust reference: send and sync": "https://doc.rust-lang.org/reference/special-types-and-traits.html",
    "rust reference — auto traits": "https://doc.rust-lang.org/reference/special-types-and-traits.html",
    "rust reference: auto traits": "https://doc.rust-lang.org/reference/special-types-and-traits.html",
    "rust reference — traits": "https://doc.rust-lang.org/reference/items/traits.html",
    "rust reference: traits": "https://doc.rust-lang.org/reference/items/traits.html",
    "rust reference — macros": "https://doc.rust-lang.org/reference/macros.html",
    "rust reference: macros": "https://doc.rust-lang.org/reference/macros.html",
    "rust reference — const fn": "https://doc.rust-lang.org/reference/items/functions.html#const-functions",
    "rust reference: const fn": "https://doc.rust-lang.org/reference/items/functions.html#const-functions",
    "rust reference — const_eval": "https://doc.rust-lang.org/reference/const_evaluation.html",
    "rust reference: const_eval": "https://doc.rust-lang.org/reference/const_evaluation.html",
    "rust reference — built-in macros": "https://doc.rust-lang.org/reference/macros-by-example.html",
    "rust reference: built-in macros": "https://doc.rust-lang.org/reference/macros-by-example.html",
    "rust reference — async await": "https://doc.rust-lang.org/reference/expressions/await-expr.html",
    "rust reference: async await": "https://doc.rust-lang.org/reference/expressions/await-expr.html",
    "rust reference — await expressions": "https://doc.rust-lang.org/reference/expressions/await-expr.html",
    "rust reference: await expressions": "https://doc.rust-lang.org/reference/expressions/await-expr.html",
    "rust reference — async blocks": "https://doc.rust-lang.org/reference/expressions/block-expr.html#async-blocks",
    "rust reference: async blocks": "https://doc.rust-lang.org/reference/expressions/block-expr.html#async-blocks",
    "rust reference — pin methods": "https://doc.rust-lang.org/reference/types/pin.html",
    "rust reference: pin methods": "https://doc.rust-lang.org/reference/types/pin.html",
    "rust reference — async closures": "https://doc.rust-lang.org/reference/types/closure.html#async-closures",
    "rust reference: async closures": "https://doc.rust-lang.org/reference/types/closure.html#async-closures",
    "rust reference — async fn desugaring": "https://doc.rust-lang.org/reference/items/functions.html#async-functions",
    "rust reference: async fn desugaring": "https://doc.rust-lang.org/reference/items/functions.html#async-functions",
    "rust reference: async fn desugaring — 局部变量提升规则": "https://doc.rust-lang.org/reference/items/functions.html#async-functions",
    "rust reference — recursive async fn": "https://doc.rust-lang.org/reference/items/functions.html#recursive-async-functions",
    "rust reference: recursive async fn": "https://doc.rust-lang.org/reference/items/functions.html#recursive-async-functions",
    "rust reference — waker": "https://doc.rust-lang.org/reference/special-types-and-traits.html",
    "rust reference: waker": "https://doc.rust-lang.org/reference/special-types-and-traits.html",
    "rust reference — waker safety": "https://doc.rust-lang.org/reference/special-types-and-traits.html",
    "rust reference: waker safety": "https://doc.rust-lang.org/reference/special-types-and-traits.html",
    "rust reference — future::poll contract": "https://doc.rust-lang.org/reference/items/traits.html",
    "rust reference: future::poll contract": "https://doc.rust-lang.org/reference/items/traits.html",
    "rust reference — pin_macro": "https://doc.rust-lang.org/reference/types/pin.html",
    "rust reference: pin_macro": "https://doc.rust-lang.org/reference/types/pin.html",
    "rust reference — auto trait derivation for !unpin": "https://doc.rust-lang.org/reference/special-types-and-traits.html",
    "rust reference: auto trait derivation for !unpin": "https://doc.rust-lang.org/reference/special-types-and-traits.html",
    "rust reference — sync": "https://doc.rust-lang.org/reference/special-types-and-traits.html",
    "rust reference: sync": "https://doc.rust-lang.org/reference/special-types-and-traits.html",
    "rust reference — memory model": "https://doc.rust-lang.org/reference/behavior-considered-undefined.html",
    "rust reference: memory model": "https://doc.rust-lang.org/reference/behavior-considered-undefined.html",
    "rust reference — constant evaluation": "https://doc.rust-lang.org/reference/const_evaluation.html",
    "rust reference: constant evaluation": "https://doc.rust-lang.org/reference/const_evaluation.html",
    "rust reference — panic": "https://doc.rust-lang.org/reference/macros.html#panic",
    "rust reference: panic": "https://doc.rust-lang.org/reference/macros.html#panic",
    "rust reference — errors": "https://doc.rust-lang.org/reference/items/functions.html",
    "rust reference: errors": "https://doc.rust-lang.org/reference/items/functions.html",
    "rust reference — interior mutability": "https://doc.rust-lang.org/reference/interior-mutability.html",
    "rust reference: interior mutability": "https://doc.rust-lang.org/reference/interior-mutability.html",
    "rust reference — zero-sized types": "https://doc.rust-lang.org/reference/types.html",
    "rust reference: zero-sized types": "https://doc.rust-lang.org/reference/types.html",
    "rust reference — pointer operators": "https://doc.rust-lang.org/reference/expressions/operator-expr.html",
    "rust reference: pointer operators": "https://doc.rust-lang.org/reference/expressions/operator-expr.html",
    "rust reference — concurrency": "https://doc.rust-lang.org/reference/special-types-and-traits.html",
    "rust reference - concurrency": "https://doc.rust-lang.org/reference/special-types-and-traits.html",
    "rust reference: panic; rustonomicon": "https://doc.rust-lang.org/reference/unsafe-blocks.html",
    "rust reference: unsafe rust; rustonomicon": "https://doc.rust-lang.org/reference/unsafe-blocks.html",

    # Rustonomicon
    "rustonomicon — send and sync": "https://doc.rust-lang.org/nomicon/send-and-sync.html",
    "rustonomicon: send and sync": "https://doc.rust-lang.org/nomicon/send-and-sync.html",
    "rustonomicon — meet safe and unsafe": "https://doc.rust-lang.org/nomicon/safe-unsafe-meaning.html",
    "rustonomicon: the safe/unsafe boundary": "https://doc.rust-lang.org/nomicon/safe-unsafe-meaning.html",
    "rustonomicon — interior mutability": "https://doc.rust-lang.org/nomicon/interior-mutability.html",
    "rustonomicon: interior mutability": "https://doc.rust-lang.org/nomicon/interior-mutability.html",
    "rustonomicon: special memory": "https://doc.rust-lang.org/nomicon/exotic-sizes.html",
    "rustonomicon — subtyping and variance": "https://doc.rust-lang.org/nomicon/subtyping.html",
    "rustonomicon: subtyping and variance": "https://doc.rust-lang.org/nomicon/subtyping.html",
    "rustonomicon: variance": "https://doc.rust-lang.org/nomicon/subtyping.html",
    "rustonomicon — variance": "https://doc.rust-lang.org/nomicon/subtyping.html",
    "rustonomicon: transmute": "https://doc.rust-lang.org/nomicon/transmutes.html",
    "the rustonomicon: transmute": "https://doc.rust-lang.org/nomicon/transmutes.html",
    "the rustonomicon: exotic sizes": "https://doc.rust-lang.org/nomicon/exotic-sizes.html",
    "rustonomicon: exotic sizes": "https://doc.rust-lang.org/nomicon/exotic-sizes.html",
    "rustonomicon: working with memory": "https://doc.rust-lang.org/nomicon/working-with-memory.html",
    "rustonomicon: ownership and move semantics": "https://doc.rust-lang.org/nomicon/ownership.html",
    "rustonomicon: ownership": "https://doc.rust-lang.org/nomicon/ownership.html",
    "rustonomicon — ownership": "https://doc.rust-lang.org/nomicon/ownership.html",
    "rustonomicon: pin projection and structural pinning": "https://doc.rust-lang.org/nomicon/pin.html",
    "rustonomicon — memory layout": "https://doc.rust-lang.org/nomicon/repr-rust.html",
    "rustonomicon — allocators": "https://doc.rust-lang.org/nomicon/vec/vec-alloc.html",
    "rustonomicon, *what unsafe rust can do*": "https://doc.rust-lang.org/nomicon/what-unsafe-does.html",
    "rustonomicon: what unsafe can do": "https://doc.rust-lang.org/nomicon/what-unsafe-does.html",
    "rustonomicon — life before main": "https://doc.rust-lang.org/nomicon/lifetime-mismatch.html",
    "the rustonomicon: ownership and move semantics": "https://doc.rust-lang.org/nomicon/ownership.html",
    "the rustonomicon: working with memory": "https://doc.rust-lang.org/nomicon/working-with-memory.html",

    # TRPL
    "trpl — references": "https://doc.rust-lang.org/book/ch04-02-references-and-borrowing.html",
    "trpl — types": "https://doc.rust-lang.org/book/ch03-02-data-types.html",

    # Async Book
    "async book": "https://rust-lang.github.io/async-book/01_getting_started/01_chapter.html",
    "the rust async book": "https://rust-lang.github.io/async-book/01_getting_started/01_chapter.html",
    "async book — execution model": "https://rust-lang.github.io/async-book/02_execution/01_chapter.html",
    "async book: execution model": "https://rust-lang.github.io/async-book/02_execution/01_chapter.html",
    "async book: under the hood": "https://rust-lang.github.io/async-book/02_execution/02_future.html",
    "async book: cancellation": "https://rust-lang.github.io/async-book/06_multiple_futures/01_chapter.html",
    "async book — cancellation": "https://rust-lang.github.io/async-book/06_multiple_futures/01_chapter.html",
    "async book: waker": "https://rust-lang.github.io/async-book/02_execution/03_wakeups.html",
    "async book — waker": "https://rust-lang.github.io/async-book/02_execution/03_wakeups.html",
    "async book: executors": "https://rust-lang.github.io/async-book/02_execution/04_executor.html",
    "async book: common mistakes": "https://rust-lang.github.io/async-book/07_workarounds/03_common_mistakes.html",
    "async book: common mi": "https://rust-lang.github.io/async-book/07_workarounds/03_common_mistakes.html",
    "async book: waker registration": "https://rust-lang.github.io/async-book/02_execution/03_wakeups.html",
    "async book — streams 章": "https://rust-lang.github.io/async-book/05_streams/01_chapter.html",
    "async book — execution 章": "https://rust-lang.github.io/async-book/02_execution/01_chapter.html",
    "asynchronous programming in rust": "https://rust-lang.github.io/async-book/01_getting_started/01_chapter.html",
    "rust async book — cancellation": "https://rust-lang.github.io/async-book/06_multiple_futures/01_chapter.html",
    "rust async book — pin": "https://rust-lang.github.io/async-book/04_pinning/01_chapter.html",
    "rust async book — async/await": "https://rust-lang.github.io/async-book/01_getting_started/04_async_await_primer.html",
    "rust async book: streams": "https://rust-lang.github.io/async-book/05_streams/01_chapter.html",
    "rust async book": "https://rust-lang.github.io/async-book/01_getting_started/01_chapter.html",
    "async rust book": "https://rust-lang.github.io/async-book/01_getting_started/01_chapter.html",
    "async rust book — future": "https://rust-lang.github.io/async-book/02_execution/02_future.html",
    "async cancellation": "https://rust-lang.github.io/async-book/06_multiple_futures/01_chapter.html",
    "async patterns": "https://rust-lang.github.io/async-book/07_workarounds/01_chapter.html",
    "async rust book — cpu bound": "https://rust-lang.github.io/async-book/07_workarounds/02_cancellation.html",
    "async rust book — workarounds": "https://rust-lang.github.io/async-book/07_workarounds/01_chapter.html",
    "common async mistakes": "https://rust-lang.github.io/async-book/07_workarounds/03_common_mistakes.html",
    "rust async book — executing futures": "https://rust-lang.github.io/async-book/02_execution/02_future.html",
    "async book (wip)": "https://rust-lang.github.io/async-book/01_getting_started/01_chapter.html",
    "async book - pinning": "https://rust-lang.github.io/async-book/04_pinning/01_chapter.html",
    "rust async book — cancellation / `futuresunordered`": "https://rust-lang.github.io/async-book/06_multiple_futures/01_chapter.html",

    # rustc-dev-guide
    "rust compiler development guide — proc macros": "https://rustc-dev-guide.rust-lang.org/proc-macros.html",
    "rustc-dev-guide — track_caller in traits": "https://rustc-dev-guide.rust-lang.org/traits/track-caller.html",

    # Additional precise mappings for remaining S1
    "rust reference: atomic types — memory orderings": "https://doc.rust-lang.org/reference/behavior-considered-undefined.html",
    "rust reference: memory model — release-acquire ordering": "https://doc.rust-lang.org/reference/behavior-considered-undefined.html",
    "rust reference: memory model — sequential consistency": "https://doc.rust-lang.org/reference/behavior-considered-undefined.html",
    "rust reference: thread spawning and memory ordering": "https://doc.rust-lang.org/reference/special-types-and-traits.html",
    "rust reference: send and sync — unsafe impl guidelines": "https://doc.rust-lang.org/reference/special-types-and-traits.html",
    "rust reference: async fn desugaring — 局部变量提升规则": "https://doc.rust-lang.org/reference/items/functions.html#async-functions",
    "rust reference: async fn": "https://doc.rust-lang.org/reference/items/functions.html#async-functions",
    "rust reference — §6.10.1 const contexts": "https://doc.rust-lang.org/reference/const_evaluation.html",
    "nom — what is unsafe?": "https://doc.rust-lang.org/nomicon/what-unsafe-does.html",
    "the rustonomicon: transmute": "https://doc.rust-lang.org/nomicon/transmutes.html",
    "the rustonomicon: variance": "https://doc.rust-lang.org/nomicon/subtyping.html",
    "rust reference — generic associated types": "https://doc.rust-lang.org/reference/items/associated-items.html",
    "rust reference: generic associated types": "https://doc.rust-lang.org/reference/items/associated-items.html",
    "rust reference — memory model": "https://doc.rust-lang.org/reference/behavior-considered-undefined.html",
    "rust reference — memory model / 2025": "https://doc.rust-lang.org/reference/behavior-considered-undefined.html",
    "rust reference — constant evaluation — query cycles": "https://doc.rust-lang.org/reference/const_evaluation.html",
    "rust reference: constant evaluation — query cycles": "https://doc.rust-lang.org/reference/const_evaluation.html",
    "the rustonomicon, *what unsafe rust can do*": "https://doc.rust-lang.org/nomicon/what-unsafe-does.html",
}


def normalize(text: str) -> str:
    return text.strip().lower().rstrip(".").rstrip(",")


def load_findings(path: str) -> List[dict]:
    with open(path, encoding="utf-8") as f:
        return json.load(f)


def group_by_file(findings: List[dict]) -> Dict[str, List[dict]]:
    grouped: Dict[str, List[dict]] = {}
    for f in findings:
        if f.get("severity") != "S1":
            continue
        grouped.setdefault(f["path"], []).append(f)
    return grouped


def try_fix(text: str) -> str | None:
    key = normalize(text)
    return LINK_TEXT_TO_URL.get(key)


def apply_fixes(json_path: str, apply: bool) -> Tuple[int, int, List[dict]]:
    findings = load_findings(json_path)
    grouped = group_by_file(findings)
    fixed_total = 0
    skipped: List[dict] = []

    for rel, items in grouped.items():
        path = os.path.join(ROOT, rel)
        if not os.path.exists(path):
            skipped.extend(items)
            continue
        with open(path, encoding="utf-8") as f:
            content = f.read()
        original = content
        for item in items:
            target = try_fix(item["text"])
            if not target:
                skipped.append(item)
                continue
            # 构造精确的旧链接文本并替换
            old_link = f"[{item['text']}]({item['url']})"
            new_link = f"[{item['text']}]({target})"
            if old_link not in content:
                # 可能 URL 被截断或包含额外字符，按文本+URL 前缀匹配
                escaped_url = re.escape(item["url"])
                pattern = re.compile(rf"\[{re.escape(item['text'])}\]\({escaped_url}[^\)]*\)")
                if not pattern.search(content):
                    skipped.append(item)
                    continue
                content = pattern.sub(new_link, content)
            else:
                content = content.replace(old_link, new_link)
            fixed_total += 1
            print(f"  修复: {rel}:{item['line']} [{item['text']}] -> {target}")

        if apply and content != original:
            with open(path, "w", encoding="utf-8") as f:
                f.write(content)

    return fixed_total, len(skipped), skipped


def main() -> int:
    parser = argparse.ArgumentParser(description="Batch-fix imprecise authority links")
    parser.add_argument("--json", required=True, help="Path to authority_link_precision JSON output")
    parser.add_argument("--apply", action="store_true", help="Actually write changes")
    args = parser.parse_args()

    fixed, skipped_count, skipped = apply_fixes(args.json, args.apply)
    print(f"\n[fix_authority_link_precision] fixed={fixed} skipped={skipped_count}")
    if skipped:
        print("\n未自动修复（缺少映射或链接模式不匹配）：")
        for s in skipped[:50]:
            print(f"  {s['path']}:{s['line']} [{s['text']}] -> {s['url']}")
        if len(skipped) > 50:
            print(f"  ... 还有 {len(skipped) - 50} 条")
    return 0


if __name__ == "__main__":
    sys.exit(main())
