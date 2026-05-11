import re, glob

files = glob.glob('crates/*/src/rust_187_features.rs')
for f in files:
    with open(f, 'r', encoding='utf-8') as fp:
        content = fp.read()
    # Replace only in trait definitions, not impl blocks
    new_content = re.sub(
        r'fn parse\(&self, input: &\'a str\) -> impl Iterator<Item = &\'a str> \+ use<\'a>;',
        r"fn parse(&self, input: &'a str) -> impl Iterator<Item = &'a str> + use<'a, Self>;",
        content
    )
    if new_content != content:
        with open(f, 'w', encoding='utf-8', newline='') as fp:
            fp.write(new_content)
        print(f'Fixed {f}')
    else:
        print(f'Skipped {f}')
