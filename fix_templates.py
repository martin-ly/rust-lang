import re, glob, os

# Fix rust_188_features.rs: #[naked] -> #[unsafe(naked)], asm! -> naked_asm!
rust188_files = glob.glob('crates/*/src/rust_188_features.rs')
old188 = '''#[cfg(target_arch = "x86_64")]
#[naked]
pub extern "C" fn naked_syscall_handler() {
    unsafe {
        core::arch::asm!(
            "push rax",
            "push rcx",
            "push rdx",
            "call {handler}",
            "pop rdx",
            "pop rcx",
            "pop rax",
            "iretq",
            handler = sym syscall_dispatch,
            options(noreturn),
        );
    }
}'''
new188 = '''#[cfg(target_arch = "x86_64")]
#[unsafe(naked)]
pub extern "C" fn naked_syscall_handler() {
    core::arch::naked_asm!(
        "push rax",
        "push rcx",
        "push rdx",
        "call {handler}",
        "pop rdx",
        "pop rcx",
        "pop rax",
        "iretq",
        handler = sym syscall_dispatch,
    );
}'''

for f in rust188_files:
    with open(f, 'r', encoding='utf-8') as fp:
        content = fp.read()
    if old188 in content:
        content = content.replace(old188, new188)
        with open(f, 'w', encoding='utf-8', newline='') as fp:
            fp.write(content)
        print(f'Fixed rust_188: {f}')
    else:
        print(f'Skipped rust_188: {f} (no match)')

# Fix rust_192_features.rs: unsafe fn body needs unsafe blocks
rust192_files = glob.glob('crates/*/src/rust_192_features.rs')
old192 = '''pub unsafe fn assume_init_array<T, const N: usize>(arr: [MaybeUninit<T>; N]) -> [T; N] {
    // SAFETY: [MaybeUninit<T>; N] 与 [T; N] layout 相同（1.92+ 文档保证）
    std::mem::transmute_copy(&arr)
}'''
new192 = '''pub unsafe fn assume_init_array<T, const N: usize>(arr: [MaybeUninit<T>; N]) -> [T; N] {
    // SAFETY: [MaybeUninit<T>; N] 与 [T; N] layout 相同（1.92+ 文档保证）
    unsafe { std::mem::transmute_copy(&arr) }
}'''

for f in rust192_files:
    with open(f, 'r', encoding='utf-8') as fp:
        content = fp.read()
    if old192 in content:
        content = content.replace(old192, new192)
        with open(f, 'w', encoding='utf-8', newline='') as fp:
            fp.write(content)
        print(f'Fixed rust_192: {f}')
    else:
        print(f'Skipped rust_192: {f} (no match)')
