import os, re

# Files modified by rebuild_core_sources.py
CORE_FILES = [
    "concept/01_foundation/01_ownership.md",
    "concept/01_foundation/02_borrowing.md",
    "concept/01_foundation/03_lifetimes.md",
    "concept/01_foundation/04_type_system.md",
    "concept/01_foundation/05_reference_semantics.md",
    "concept/01_foundation/06_zero_cost_abstractions.md",
    "concept/01_foundation/07_control_flow.md",
    "concept/01_foundation/08_collections.md",
    "concept/01_foundation/20_variable_model.md",
    "concept/01_foundation/21_effects_and_purity.md",
    "concept/02_intermediate/01_traits.md",
    "concept/02_intermediate/02_generics.md",
    "concept/02_intermediate/03_memory_management.md",
    "concept/02_intermediate/08_interior_mutability.md",
    "concept/02_intermediate/12_smart_pointers.md",
    "concept/02_intermediate/14_newtype_and_wrapper.md",
    "concept/03_advanced/01_concurrency.md",
    "concept/03_advanced/02_async.md",
    "concept/03_advanced/02_async_advanced.md",
    "concept/03_advanced/03_unsafe.md",
    "concept/03_advanced/04_macros.md",
    "concept/03_advanced/07_proc_macro.md",
    "concept/03_advanced/10_concurrency_patterns.md",
    "concept/03_advanced/11_atomics_and_memory_ordering.md",
    "concept/03_advanced/16_lock_free.md",
    "concept/03_advanced/19_parallel_distributed_pattern_spectrum.md",
    "concept/03_advanced/20_stream_processing_semantics.md",
]

total_removed = 0
for filepath in CORE_FILES:
    if not os.path.exists(filepath):
        continue
    with open(filepath, 'r', encoding='utf-8') as f:
        lines = f.readlines()
    
    new_lines = []
    removed = 0
    for line in lines:
        stripped = line.strip()
        # Remove standalone inline source lines inserted by the script
        # Pattern: starts with [来源: ...] at beginning of line (not inside blockquote)
        if re.match(r'^\[来源:', stripped):
            removed += 1
            continue
        new_lines.append(line)
    
    if removed > 0:
        with open(filepath, 'w', encoding='utf-8') as f:
            f.writelines(new_lines)
        total_removed += removed
        print(f"FIXED: {os.path.basename(filepath)} (-{removed} inline sources)")

print(f"\nTotal removed: {total_removed} overflow inline sources")
