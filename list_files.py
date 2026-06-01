import os

directories = [
    'crates/c10_networks/src',
    'crates/c11_macro_system/src',
    'crates/c11_macro_system_proc/src',
    'crates/c12_wasm/src',
    'crates/c13_embedded/src',
    'exercises/src',
]

files = []
for d in directories:
    if not os.path.exists(d):
        continue
    for root, _, fnames in os.walk(d):
        for fname in fnames:
            if fname.endswith('.rs'):
                filepath = os.path.join(root, fname)
                size = os.path.getsize(filepath)
                files.append((filepath, size))

files.sort(key=lambda x: x[1])
for f, s in files:
    print(f"{s:6d} {f}")
