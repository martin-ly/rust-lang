import glob

files = glob.glob('crates/*/src/rust_192_features.rs')
for f in files:
    with open(f, 'r', encoding='utf-8') as fp:
        content = fp.read()
    content = content.replace(
        'let mut arr: [MaybeUninit<i32>; 3] = std::array::from_fn(|i| MaybeUninit::new(i as i32 * 10));',
        'let arr: [MaybeUninit<i32>; 3] = std::array::from_fn(|i| MaybeUninit::new(i as i32 * 10));'
    )
    with open(f, 'w', encoding='utf-8', newline='') as fp:
        fp.write(content)
    print(f'Fixed {f}')
