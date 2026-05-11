import glob

files = glob.glob('crates/*/src/rust_191_features.rs')
for f in files:
    with open(f, 'r', encoding='utf-8') as fp:
        content = fp.read()
    # Replace the specific doctest that uses unstable c_variadic
    content = content.replace('/// ```rust\n/// unsafe extern "C" fn printf(fmt: *const c_char, ...) { }\n/// ```', 
                              '/// ```ignore\n/// unsafe extern "C" fn printf(fmt: *const c_char, ...) { }\n/// ```')
    with open(f, 'w', encoding='utf-8', newline='') as fp:
        fp.write(content)
    print(f'Fixed doctest in {f}')
