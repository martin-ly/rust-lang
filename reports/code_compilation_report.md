# Rust Code Block Compilation Report

Generated: 2026-05-13T23:21:27.873069

## Summary

- Total markdown files scanned: 52
- Total `rust` code blocks found: 432
- Explicitly ignored (ignore/no_run/compile_fail/etc.): 296
- Plain `rust` blocks considered: 136
- Pseudo-code / incomplete snippets skipped: 2
- Compilation attempted: 134
- **Compilation successful**: 133
- **Compilation failed**: 1

## Skipped Pseudo-Code / Incomplete Snippets

### Skip #1

- **File**: `e:\_src\rust-lang\concept\03_advanced\04_macros.md` (line 773)
- **Reason**: contains ellipsis (...)

**Code preview**:

```rust
// 声明宏: 模式匹配
macro_rules! say_hello {
    () => { println!("Hello!"); };
    ($name:expr) => { println!("Hello, {}!", $name); };
}

// 过程宏: 用函数处理 TokenStream
// #[proc_macro]
// pub fn sql(input: TokenStream) -> TokenStream { ... }
```

### Skip #2

- **File**: `e:\_src\rust-lang\concept\06_ecosystem\02_patterns.md` (line 659)
- **Reason**: contains ellipsis (...)

**Code preview**:

```rust
// ❌ Stringly typed
fn run_command(name: &str) { /* ... */ }

// ✅ 强类型
enum Command { Start, Stop, Restart }
fn run_command(cmd: Command) { match cmd { ... } }
```

## Failed Compilation Details

### Failure #1

- **File**: `e:\_src\rust-lang\concept\01_foundation\04_type_system.md` (line 422)
- **Temp file**: `01_foundation_04_type_system_block2.rs`

**Code preview**:

```rust
// ✅ 修正: 覆盖所有变体或使用通配符
fn print_color(c: Color) {
    match c {
        Color::Red => println!("Red"),
        Color::Green => println!("Green"),
        Color::Blue => println!("Blue"),
    }
}

// 或
fn print_color(c: Color) {
    match c {
        Color::Red => println!("Red"),
        Color::Green => println!("Green"),
        _ => println!("Other"),  // ✅ 通配符覆盖剩余变体
    }
}
```

**Error output**:

```
error[E0428]: the name `print_color` is defined multiple times
  --> e:\_src\rust-lang\target\semantic_test\01_foundation_04_type_system_block2.rs:11:1
   |
 2 | fn print_color(c: Color) {
   | ------------------------ previous definition of the value `print_color` here
...
11 | fn print_color(c: Color) {
   | ^^^^^^^^^^^^^^^^^^^^^^^^ `print_color` redefined here
   |
   = note: `print_color` must be defined only once in the value namespace of this module

error[E0425]: cannot find type `Color` in this scope
 --> e:\_src\rust-lang\target\semantic_test\01_foundation_04_type_system_block2.rs:2:19
  |
2 | fn print_color(c: Color) {
  |                   ^^^^^ not found in this scope

error[E0425]: cannot find type `Color` in this scope
  --> e:\_src\rust-lang\target\semantic_test\01_foundatio
```
