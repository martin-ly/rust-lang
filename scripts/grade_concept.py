import os
import re

BASE = "concept"

DIR_DEFAULTS = {
    "00_meta": ("[初学者]", "[综述级]"),
    "01_foundation": ("[初学者]", "[综述级]"),
    "02_intermediate": ("[进阶]", "[专家级]"),
    "03_advanced": ("[进阶]", "[专家级]"),
    "04_formal": ("[研究者]", "[研究者级]"),
    "05_comparative": ("[进阶]", "[综述级]"),
    "06_ecosystem": ("[进阶]", "[综述级]"),
    "07_future": ("[专家]", "[实验级]"),
}

FILENAME_OVERRIDES = {
    "preview": ("[专家]", "[实验级]"),
    "tracking": ("[专家]", "[实验级]"),
    "evolution": ("[专家]", "[综述级]"),
    "roadmap": ("[专家]", "[综述级]"),
    "guide": ("[进阶]", "[综述级]"),
    "cheatsheet": ("[进阶]", "[综述级]"),
    "deep_dive": ("[专家]", "[专家级]"),
    "formal": ("[研究者]", "[研究者级]"),
    "semantics": ("[研究者]", "[研究者级]"),
    "linear_logic": ("[研究者]", "[研究者级]"),
    "rustbelt": ("[研究者]", "[研究者级]"),
    "ownership_formal": ("[研究者]", "[研究者级]"),
    "borrow_checker": ("[专家]", "[专家级]"),
    "nll": ("[专家]", "[专家级]"),
    "polonius": ("[专家]", "[专家级]"),
    "unsafe": ("[进阶]", "[专家级]"),
    "pin": ("[进阶]", "[专家级]"),
    "macro": ("[进阶]", "[专家级]"),
    "async": ("[进阶]", "[专家级]"),
    "concurrency": ("[进阶]", "[专家级]"),
    "thread": ("[进阶]", "[专家级]"),
    "lifetime": ("[初学者]", "[综述级]"),
    "borrowing": ("[初学者]", "[综述级]"),
    "ownership": ("[初学者]", "[综述级]"),
    "type_system": ("[初学者]", "[综述级]"),
    "generics": ("[进阶]", "[专家级]"),
    "trait": ("[进阶]", "[专家级]"),
    "error_handling": ("[进阶]", "[专家级]"),
    "memory_management": ("[进阶]", "[专家级]"),
    "smart_pointer": ("[进阶]", "[专家级]"),
    "closure": ("[初学者]", "[综述级]"),
    "iterator": ("[初学者]", "[综述级]"),
    "pattern_matching": ("[初学者]", "[综述级]"),
    "control_flow": ("[初学者]", "[综述级]"),
    "function": ("[初学者]", "[综述级]"),
    "collection": ("[初学者]", "[综述级]"),
    "string": ("[初学者]", "[综述级]"),
    "module": ("[初学者]", "[综述级]"),
    "package": ("[初学者]", "[综述级]"),
    "cargo": ("[初学者]", "[综述级]"),
    "testing": ("[初学者]", "[综述级]"),
    "documentation": ("[初学者]", "[综述级]"),
    "benchmark": ("[进阶]", "[专家级]"),
    "ffi": ("[专家]", "[专家级]"),
    "wasm": ("[进阶]", "[专家级]"),
    "embedded": ("[专家]", "[专家级]"),
    "blockchain": ("[专家]", "[综述级]"),
    "game": ("[专家]", "[综述级]"),
    "aerospace": ("[专家]", "[综述级]"),
    "design_pattern": ("[进阶]", "[综述级]"),
    "idiom": ("[进阶]", "[综述级]"),
    "api_guidelines": ("[进阶]", "[综述级]"),
    "performance": ("[进阶]", "[专家级]"),
    "security": ("[专家]", "[专家级]"),
    "cryptography": ("[专家]", "[专家级]"),
    "serialization": ("[进阶]", "[综述级]"),
    "logging": ("[进阶]", "[综述级]"),
    "network": ("[进阶]", "[专家级]"),
    "database": ("[进阶]", "[综述级]"),
    "web_framework": ("[进阶]", "[综述级]"),
    "grpc": ("[进阶]", "[专家级]"),
    "distributed": ("[专家]", "[专家级]"),
    "cross_compile": ("[进阶]", "[综述级]"),
    "toolchain": ("[进阶]", "[综述级]"),
    "compiler": ("[专家]", "[专家级]"),
    "mir": ("[研究者]", "[研究者级]"),
    "hir": ("[研究者]", "[研究者级]"),
    "ast": ("[研究者]", "[研究者级]"),
    "type_theory": ("[研究者]", "[研究者级]"),
    "operational_semantics": ("[研究者]", "[研究者级]"),
    "axiomatic_semantics": ("[研究者]", "[研究者级]"),
    "verification": ("[研究者]", "[研究者级]"),
    "kani": ("[专家]", "[实验级]"),
    "miri": ("[专家]", "[实验级]"),
    "borrowsanitizer": ("[专家]", "[实验级]"),
    "effect": ("[研究者]", "[实验级]"),
    "const_trait": ("[专家]", "[实验级]"),
    "gen_block": ("[专家]", "[实验级]"),
    "async_drop": ("[专家]", "[实验级]"),
    "rtn": ("[专家]", "[实验级]"),
    "cranelift": ("[专家]", "[实验级]"),
    "parallel_frontend": ("[专家]", "[实验级]"),
    "build_std": ("[专家]", "[实验级]"),
    "rust_for_linux": ("[专家]", "[实验级]"),
    "field_projections": ("[专家]", "[实验级]"),
    "pin_ergonomics": ("[专家]", "[实验级]"),
    "reborrow": ("[专家]", "[实验级]"),
    "rust_specification": ("[专家]", "[实验级]"),
    "edition": ("[进阶]", "[综述级]"),
    "release": ("[进阶]", "[综述级]"),
    "version": ("[进阶]", "[综述级]"),
    "changelog": ("[进阶]", "[综述级]"),
    "migration": ("[进阶]", "[综述级]"),
    "comparison": ("[进阶]", "[综述级]"),
    "vs_": ("[进阶]", "[综述级]"),
}

CONTENT_OVERRIDES = [
    (r"#!\[feature\(", "[专家]", "[实验级]"),
    (r"nightly\s+1\.\d+", "[专家]", "[实验级]"),
    (r"nightly.*experimental", "[专家]", "[实验级]"),
    (r"RUSTSEC", "[专家]", "[专家级]"),
    (r"CVE-\d{4}-", "[专家]", "[专家级]"),
    (r" theorem |定理|⟹|⊗|⊸|∀|∃|∈|⊆|⊂", "[研究者]", "[研究者级]"),
    (r"Datalog|分离逻辑|线性逻辑|范畴论|类型论", "[研究者]", "[研究者级]"),
    (r"RustBelt|Iris|Coq|Verus|Kani|Prusti", "[研究者]", "[研究者级]"),
]

SKIP_DIRS = {"archive", "sources"}

def classify_file(filepath):
    rel = os.path.relpath(filepath, BASE)
    parts = rel.split(os.sep)
    if any(p in SKIP_DIRS for p in parts):
        return None, None
    dir_key = parts[0] if parts else ""
    audience, grade = DIR_DEFAULTS.get(dir_key, ("[进阶]", "[综述级]"))
    basename = os.path.basename(filepath).lower()
    for keyword, (a, g) in FILENAME_OVERRIDES.items():
        if keyword in basename:
            audience, grade = a, g
            break
    try:
        with open(filepath, "r", encoding="utf-8") as f:
            content = f.read(3000)
    except Exception:
        return audience, grade
    for pattern, a, g in CONTENT_OVERRIDES:
        if re.search(pattern, content, re.IGNORECASE):
            audience, grade = a, g
            break
    return audience, grade


def add_tags(filepath, audience, grade):
    with open(filepath, "r", encoding="utf-8") as f:
        content = f.read()
    
    has_audience = "**受众**" in content
    has_grade = "**内容分级**" in content
    
    if has_audience and has_grade:
        return False, "both already tagged"
    
    lines = content.splitlines(keepends=True)
    title_idx = -1
    for i, line in enumerate(lines):
        if line.strip().startswith("# ") or line.strip().startswith("> # "):
            title_idx = i
            break
    
    if title_idx < 0:
        return False, "no title found"
    
    if has_audience and not has_grade:
        for i in range(title_idx, min(title_idx + 20, len(lines))):
            if "**受众**" in lines[i]:
                insert_idx = i + 1
                tag_line = f"> **内容分级**: {grade}\n"
                if grade == "[实验级]":
                    tag_line += "> **跟踪版本**: nightly 1.98.0 (2026-06-06)\n"
                new_lines = lines[:insert_idx] + [tag_line] + lines[insert_idx:]
                with open(filepath, "w", encoding="utf-8") as f:
                    f.write("".join(new_lines))
                return True, "grade added"
        return False, "audience line not found"
    
    if has_grade and not has_audience:
        for i in range(title_idx, min(title_idx + 20, len(lines))):
            if "**内容分级**" in lines[i]:
                insert_idx = i
                tag_line = f"> **受众**: {audience}\n"
                new_lines = lines[:insert_idx] + [tag_line] + lines[insert_idx:]
                with open(filepath, "w", encoding="utf-8") as f:
                    f.write("".join(new_lines))
                return True, "audience added"
        return False, "grade line not found"
    
    insert_idx = title_idx + 1
    while insert_idx < len(lines) and lines[insert_idx].strip() in ("", ">"):
        insert_idx += 1
    
    tag_lines = [">\n", f"> **受众**: {audience}\n", f"> **内容分级**: {grade}\n"]
    if grade == "[实验级]":
        tag_lines.append("> **跟踪版本**: nightly 1.98.0 (2026-06-06)\n")
    
    new_lines = lines[:insert_idx] + tag_lines + lines[insert_idx:]
    with open(filepath, "w", encoding="utf-8") as f:
        f.write("".join(new_lines))
    return True, "both added"


def main():
    tagged = skipped = errors = already = 0
    for root, dirs, files in os.walk(BASE):
        dirs[:] = [d for d in dirs if d not in SKIP_DIRS]
        for fname in files:
            if not fname.endswith(".md"):
                continue
            filepath = os.path.join(root, fname)
            audience, grade = classify_file(filepath)
            if audience is None:
                skipped += 1
                continue
            ok, reason = add_tags(filepath, audience, grade)
            if ok:
                tagged += 1
                print(f"[TAGGED] {os.path.relpath(filepath, BASE)} -> {reason} ({audience} {grade})")
            elif reason == "both already tagged":
                already += 1
            else:
                errors += 1
                print(f"[ERROR] {filepath}: {reason}")
    
    print(f"\nTagged: {tagged}, Already both: {already}, Skipped: {skipped}, Errors: {errors}")

if __name__ == "__main__":
    main()
