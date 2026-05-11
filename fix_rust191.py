import re, glob, os

files = glob.glob('crates/*/src/rust_191_features.rs')

pattern = re.compile(
    r'use std::ffi::\{c_char, c_int, VaList\};\n\n'
    r'/// 示例：C 风格变参函数的 Rust 声明（非完整实现）\n'
    r'///\n'
    r'/// 实际实现需要使用 `VaList` 逐个提取参数。\n'
    r'unsafe extern "C" fn rust_printf\(fmt: \*const c_char, mut args: \.\.\.\) -> c_int \{\n'
    r'    let mut ap: VaList = args\.clone\(\);\n'
    r'    // 通过 ap\.arg::<T>\(\) 提取参数（此处为示意）\n'
    r'    let _ = ap\.arg::<c_int>\(\);\n'
    r'    0 // 返回写入的字符数\n'
    r'\}\n\n'
    r'#\[test\]\n'
    r'fn test_c_variadic_signature\(\) \{\n'
    r'    // 验证函数签名存在\n'
    r'    let _ptr: unsafe extern "C" fn\(\*const c_char, \.\.\.\) -> c_int = rust_printf;\n'
    r'\}'
)

replacement = '''/// **注意**：截至 Rust 1.95.0 stable，`c_variadic` 特性尚未完全稳定。
/// 以下代码需要 nightly 工具链才能编译。
///
/// ```ignore
/// use std::ffi::{c_char, c_int, VaList};
///
/// unsafe extern "C" fn rust_printf(fmt: *const c_char, mut args: ...) -> c_int {
///     let mut ap: VaList = args.clone();
///     let _ = ap.arg::<c_int>();
///     0
/// }
/// ```
pub fn c_variadic_doc_placeholder() -> &'static str {
    "c_variadic requires nightly Rust; see documentation above"
}

#[test]
fn test_c_variadic_placeholder() {
    assert_eq!(c_variadic_doc_placeholder(), "c_variadic requires nightly Rust; see documentation above");
}'''

for f in files:
    with open(f, 'r', encoding='utf-8') as fp:
        content = fp.read()
    new_content, count = pattern.subn(replacement, content)
    if count > 0:
        with open(f, 'w', encoding='utf-8', newline='') as fp:
            fp.write(new_content)
        print(f'Fixed {f}')
    else:
        print(f'Skipped {f} (no match)')
