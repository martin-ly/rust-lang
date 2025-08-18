# 符号扩展性——实际代码/工具应用案例

## 1. 所有权符号 O 的代码示例
```rust
fn move_ownership(x: String) -> String {
    let y = x; // O: x -> Moved, y -> Owned
    y
}
```
- 工具链：deep_concept_checker.rs 可自动检测 O 的状态转移

## 2. 生命周期符号 L 的代码示例
```rust
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}
```
- 工具链：生命周期推导与自动化验证

## 3. 新特性符号的代码示例
```rust
trait MyTrait {
    type AssocType<'a>;
}
```
- GAT 的符号扩展与自动化检测

## 4. 交叉引用
- 见 symbol_extension_proof.md、symbol_extension_script.md

## 5. 递归反馈
- 代码案例为 symbol_extension_script.md 自动化测试与验证提供输入 