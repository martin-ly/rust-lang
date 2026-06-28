#!/usr/bin/env python3
"""Replace generic TRPL links under concept/ with 3rd Ed chapter links."""
import os
import re
import sys
from collections import defaultdict

ROOT = "concept"
EXCLUDE = {
    "01_ownership.md",
    "02_borrowing.md",
    "LEARNING_MVP_PATH.md",
}
BROWN_ELIGIBLE_TARGETS = {
    "ch04-00-understanding-ownership.html",
    "ch04-02-references-and-borrowing.html",
    "ch10-03-lifetime-syntax.html",
    "ch16-00-concurrency.html",
    "ch17-00-async-await.html",
}


def _lc(parts, filename):
    """lowercase helpers."""
    return parts, filename.lower()


def default_target(rel):
    rel_u = rel.replace("\\", "/")
    parts = rel_u.split("/")
    filename = parts[-1].lower()
    if filename in {p.lower() for p in EXCLUDE}:
        return None

    # archive / deprecated
    if "archive" in parts:
        if "lifetimes" in filename:
            return "ch10-03-lifetime-syntax.html"
        if "async" in filename:
            return "ch17-00-async-await.html"
        if "unsafe" in filename:
            return "ch20-01-unsafe-rust.html"
        if "macros" in filename:
            return "ch20-05-macros.html"
        if "numeric" in filename:
            return "ch03-02-data-types.html"
        return "title-page.html"

    # meta and indexes
    if parts[0] in ("00_meta", "sources") or filename == "readme.md":
        return "title-page.html"

    # 01 foundation
    if "01_foundation" in parts:
        if "lifetimes" in filename:
            return "ch10-03-lifetime-syntax.html"
        if "reference_semantics" in filename:
            return "ch04-02-references-and-borrowing.html"
        if "control_flow" in filename:
            return "ch03-05-control-flow.html"
        if "collections" in filename:
            return "ch08-00-common-collections.html"
        if "strings" in filename:
            return "ch08-02-storing-utf-8-encoded-text-with-strings.html"
        if "error_handling" in filename:
            return "ch09-00-error-handling.html"
        if "numerics" in filename or "numeric_types" in filename:
            return "ch03-02-data-types.html"
        if "modules_and_paths" in filename:
            return "ch07-00-packages-crates-and-modules.html"
        if "attributes_and_macros" in filename:
            return "ch20-05-macros.html"
        if "panic_and_abort" in filename:
            return "ch09-01-unrecoverable-errors-with-panic.html"
        if "closure" in filename:
            return "ch13-01-closures.html"
        if "testing_basics" in filename:
            return "ch11-00-testing.html"
        if "variable_model" in filename:
            return "ch03-01-variables-and-mutability.html"
        return "title-page.html"

    # 02 intermediate
    if "02_intermediate" in parts:
        if "traits" in filename and "advanced" not in filename:
            return "ch10-02-traits.html"
        if "generics" in filename:
            return "ch10-00-generics.html"
        if "memory_management" in filename:
            return "ch15-00-smart-pointers.html"
        if "error_handling" in filename:
            return "ch09-00-error-handling.html"
        if "assert_matches" in filename:
            return "ch19-00-patterns-and-matching.html"
        if "closure" in filename:
            return "ch13-01-closures.html"
        if "interior_mutability" in filename:
            return "ch15-05-refcell-and-interior-mutability.html"
        if "module_system" in filename:
            return "ch07-00-packages-crates-and-modules.html"
        if "cow_and_borrowed" in filename:
            return "ch04-02-references-and-borrowing.html"
        if "smart_pointers" in filename:
            return "ch15-00-smart-pointers.html"
        if "iterator" in filename:
            return "ch13-00-functional-features.html"
        if "macro" in filename:
            return "ch20-05-macros.html"
        if "lifetimes" in filename:
            return "ch10-03-lifetime-syntax.html"
        if "advanced_traits" in filename:
            return "ch20-02-advanced-traits.html"
        if "type_system_advanced" in filename:
            return "ch20-03-advanced-types.html"
        return "title-page.html"

    # 03 advanced
    if "03_advanced" in parts:
        if "concurrency" in filename or "atomics" in filename or "lock_free" in filename:
            return "ch16-00-concurrency.html"
        if "async" in filename or "pin_unpin" in filename or "stream" in filename:
            return "ch17-00-async-await.html"
        if "unsafe" in filename or "ffi" in filename:
            return "ch20-01-unsafe-rust.html"
        if "macro" in filename or "proc_macro" in filename:
            return "ch20-05-macros.html"
        if "nll" in filename or "polonius" in filename:
            return "ch10-03-lifetime-syntax.html"
        return "title-page.html"

    # 04 formal
    if "04_formal" in parts:
        if "ownership_formal" in filename or "borrow_checking" in filename:
            return "ch04-00-understanding-ownership.html"
        if "subtype_variance" in filename or "type_system_advanced" in filename:
            return "ch20-03-advanced-types.html"
        return "title-page.html"

    # comparative / ecosystem / future
    if "05_comparative" in parts:
        return "title-page.html"
    if "06_ecosystem" in parts:
        if "testing" in filename:
            return "ch11-00-testing.html"
        return "title-page.html"
    if "07_future" in parts:
        return "title-page.html"

    return "title-page.html"


def brown_url(target):
    return f"https://rust-book.cs.brown.edu/{target}"


def trpl_url(target):
    return f"https://doc.rust-lang.org/book/{target}"


def add_brown_to_source_line(line, target, prev_line=None):
    """Append a Brown book link to a source line if it looks safe."""
    brown = brown_url(target)
    # avoid double-adding
    if brown in line:
        return line
    # only append to lines that look like source/authority lines
    # (allow the marker to be on the previous line for multi-line quote blocks)
    has_source_marker = bool(
        re.search(r"(主要来源|权威来源|\\*\\*来源\\*\\*|>\\s*来源)", line)
    )
    if not has_source_marker and prev_line is not None:
        has_source_marker = bool(
            re.search(r"(主要来源|权威来源|\\*\\*来源\\*\\*|>\\s*来源)", prev_line)
        )
    if not has_source_marker:
        return line
    # only if this line already points to the matching TRPL chapter
    if trpl_url(target) not in line:
        return line
    # Append Brown. If the line already ends with a separator such as " ·",
    # insert Brown before that separator to avoid " · · [Brown]".
    stripped = line.rstrip("\n").rstrip()
    if stripped.endswith("·"):
        stripped = stripped[:-1].rstrip()
        suffix = " ·"
    else:
        suffix = ""
    return stripped + f" · [Brown University Interactive Book]({brown})" + suffix + "\n"


def process(dry_run=True):
    md_link_re = re.compile(r"\[([^\]]*)\]\(https://doc\.rust-lang\.org/book/\)")
    angle_re = re.compile(r"<https://doc\.rust-lang\.org/book/>")

    records = []
    modified_files = 0
    skipped_files = []

    for root, _, files in os.walk(ROOT):
        for f in files:
            if not f.endswith(".md"):
                continue
            path = os.path.join(root, f)
            rel = os.path.relpath(path, ROOT)
            target = default_target(rel)
            if target is None:
                skipped_files.append(rel)
                continue

            with open(path, "r", encoding="utf-8") as fh:
                text = fh.read()

            md_count = len(md_link_re.findall(text))
            angle_count = len(angle_re.findall(text))
            if md_count == 0 and angle_count == 0:
                continue

            new_text = md_link_re.sub(
                lambda m: f"[{m.group(1)}](https://doc.rust-lang.org/book/{target})",
                text,
            )
            new_text = angle_re.sub(
                lambda m: f"<https://doc.rust-lang.org/book/{target}>",
                new_text,
            )

            brown_added = False
            parts = rel.replace("\\", "/").split("/")
            is_brown_eligible_file = (
                target in BROWN_ELIGIBLE_TARGETS
                and parts[0] in ("01_foundation", "02_intermediate", "03_advanced")
            )

            if is_brown_eligible_file:
                # First, upgrade any generic Brown root links to the specific chapter
                brown_root_md = re.compile(r"\[([^\]]*)\]\(https://rust-book\.cs\.brown\.edu/\)")
                brown_root_angle = re.compile(r"<https://rust-book\.cs\.brown\.edu/>")
                if brown_root_md.search(new_text) or brown_root_angle.search(new_text):
                    new_text = brown_root_md.sub(
                        lambda m: f"[{m.group(1)}]({brown_url(target)})",
                        new_text,
                    )
                    new_text = brown_root_angle.sub(
                        lambda m: f"<{brown_url(target)}>",
                        new_text,
                    )
                    brown_added = True

                # Then, append Brown to the first matching source/authority line if not already present
                if brown_url(target) not in new_text:
                    lines = new_text.splitlines(keepends=True)
                    for i, line in enumerate(lines):
                        prev = lines[i - 1] if i > 0 else None
                        new_line = add_brown_to_source_line(line, target, prev)
                        if new_line is not line:
                            lines[i] = new_line
                            brown_added = True
                            break
                    new_text = "".join(lines)

            changed = new_text != text
            if changed:
                modified_files += 1
                if not dry_run:
                    with open(path, "w", encoding="utf-8") as fh:
                        fh.write(new_text)

            records.append({
                "file": rel,
                "target": target,
                "md_replaced": md_count,
                "angle_replaced": angle_count,
                "brown_added": brown_added,
                "changed": changed,
            })

    return records, modified_files, skipped_files


if __name__ == "__main__":
    dry = "--apply" not in sys.argv
    report_path = None
    if "--report" in sys.argv:
        idx = sys.argv.index("--report")
        report_path = sys.argv[idx + 1]
    records, modified, skipped = process(dry_run=dry)
    print(f"{'DRY RUN' if dry else 'APPLIED'}: {modified} files modified")
    print(f"Skipped excluded files: {len(skipped)}")
    if report_path:
        with open(report_path, "w", encoding="utf-8") as fh:
            fh.write("# TRPL Generic Link Fix Report\n\n")
            fh.write(f"- **Total modified files**: {modified}\n")
            fh.write(f"- **Skipped excluded files**: {', '.join(skipped)}\n")
            fh.write("- **Legend**: `md` = markdown generic links replaced; "
                     "`angle` = angle-bracket generic links replaced; "
                     "`+Brown` = Brown University Interactive Book link added/updated.\n\n")
            fh.write("| File | Target URL | md | angle | Brown |\n")
            fh.write("|------|------------|----:|----:|-------|\n")
            for r in records:
                if not r["changed"]:
                    continue
                brown = "✅" if r["brown_added"] else ""
                fh.write(
                    f"| `{r['file']}` | `{r['target']}` | {r['md_replaced']} | "
                    f"{r['angle_replaced']} | {brown} |\n"
                )
        print(f"Report written to: {report_path}")
    else:
        for r in records:
            if not r["changed"]:
                continue
            brown = " +Brown" if r["brown_added"] else ""
            print(
                f"{r['file']} -> {r['target']} "
                f"(md={r['md_replaced']} angle={r['angle_replaced']}{brown})"
            )
