
### 10.4 边界测试：代码块标记的 `compile_fail` 与 `no_run` 的误用（读者误导）

```rust,ignore
/// ```rust,compile_fail
/// // 这段代码应该编译失败
/// let x: i32 = "hello"; // 类型不匹配
/// ```
fn documented() {}

fn main() {}
```

> **修正**: 代码块标记的**规范**：1) `rust,compile_fail` — 代码编译失败（展示错误模式）；2) `rust,no_run` — 代码编译通过但不运行（无限循环、I/O）；3) `rust,ignore` — 跳过（外部依赖、平台特定）；4) `rust,should_panic` — 编译通过但运行 panic（预期崩溃）；5) `rust`（无属性）— 编译且运行通过。常见误用：1) 运行时 panic 标为 `compile_fail`（应 `should_panic`）；2) 编译通过的代码标为 `compile_fail`（伪标记）；3) 依赖外部 crate 的代码未标 `ignore`（编译失败但非教学目的）。审计脚本 `verify_compile_fail_v3.py` 自动检测：1) 提取所有 `compile_fail` 块；2) 用 `rustc --edition 2024` 编译；3) 标记 `unexpected_pass`（伪标记）和 `syntax_error`（代码本身错误）。维护原则：每个 `compile_fail` 块必须是**真实的编译错误**，且**错误信息应与教学内容匹配**。[来源: [Rustdoc Book](https://doc.rust-lang.org/rustdoc/index.html)] · [来源: [mdBook](https://rust-lang.github.io/mdBook/)]
