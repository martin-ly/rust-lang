# Rust 2024 Edition 迁移完全指南

> **版本**: Rust 1.85.0+ (Edition 2024 于 1.85.0 稳定)
> **最后更新**: 2026-06-01
> **难度**: 初级 → 中级
> **预计阅读**: 25 分钟

---

## 一、什么是 Edition？

Rust 的 **Edition** 是一种**向后兼容的语言演进机制**，允许在不破坏现有代码的前提下引入不兼容的语法变更。

```text
Edition 演进时间线:
Rust 1.0  (2015) ──→ Rust 2015 (初始 Edition)
Rust 1.31 (2018) ──→ Rust 2018 (async/await, NLL, ?)
Rust 1.56 (2021) ──→ Rust 2021 (闭包捕获、panic 一致性、预留)
Rust 1.85 (2025) ──→ Rust 2024 (gen, async 闭包, never type, unsafe 标记)
```

**核心规则**:

- 同一 crate 内的所有代码使用同一 Edition
- 不同 Edition 的 crate 可以无缝互操作（链接兼容）
- Edition 变更仅影响语法解析和语义，不影响 ABI

---

## 二、Rust 2024 Edition 核心变化清单

### 2.1 语言特性

| 特性 | 说明 | 影响范围 | 自动迁移 |
|:---|:---|:---|:---:|
| **`gen` 关键字预留** | 为生成器（generator）预留关键字 | 变量/函数名使用 `gen` 的代码 | ✅ |
| **异步闭包 `async \| \| {}`** | 原生支持 `async` 闭包 | 使用 `async_trait` 模拟闭包的代码 | ⚠️ |
| **临时变量作用域收紧** | `if let` / 尾部表达式中的临时值更早 drop | 依赖特定 drop 顺序的代码 | ⚠️ |
| **`never` 类型回退** | `!` 在更多上下文中作为默认类型 | 泛型代码的类型推断 | ✅ |
| **`unsafe` 操作需显式标记** | `unsafe` 块内的 `unsafe` 调用需写 `unsafe { }` | 所有 unsafe 代码 | ✅ |

### 2.2 标准库变化

| 变化 | 说明 |
|:---|:---|
| `std::env::set_var` 标记为 `unsafe` | 设置环境变量现在需要 `unsafe` 块 |
| `Future` / `IntoFuture` 加入 prelude | 不再需要显式导入 |
| `impl Future for {…}` 异步闭包支持 | 异步闭包可直接 `.await` |

### 2.3 Cargo 改进

| 特性 | 说明 |
|:---|:---|
| 版本感知解析器 | `Cargo.toml` 中的 `rust-version` 影响依赖解析 |
| `cargo fix --edition` | 自动迁移工具支持 2024 Edition |
| Workspace edition 继承 | 子 crate 可继承 workspace 的 edition |

---

## 三、自动迁移流程

### 3.1 一步迁移（推荐）

```bash
# 1. 确保使用 Rust 1.85.0+
rustup update stable

# 2. 自动修复大部分变更
cargo fix --edition

# 3. 手动检查剩余的 unsafe 相关变更
cargo check

# 4. 运行测试确保行为正确
cargo test
```

### 3.2 `cargo fix --edition` 能做什么

```bash
# 自动处理的变化:
# ✅ 在 unsafe 块内的 unsafe 调用添加 unsafe { }
# ✅ 临时变量作用域相关的借用调整
# ✅ gen 关键字冲突的变量重命名
# ✅ never 类型相关的类型标注补充
# ✅ async 闭包语法转换

# 不能自动处理（需人工审查）:
# ⚠️ 依赖特定 drop 顺序的代码逻辑
# ⚠️ 环境变量设置代码的 unsafe 块包裹
# ⚠️ 异步闭包与现有 async_trait 的交互
```

---

## 四、关键变更详解与手动迁移

### 4.1 `unsafe` 块中的 `unsafe` 需显式标记

**变更前 (Edition 2021)**:

```rust
unsafe fn dangerous() { }

fn call_dangerous() {
    unsafe {
        dangerous();      // OK: 外层的 unsafe 足够
        println!("called");
    }
}
```

**变更后 (Edition 2024)**:

```rust
unsafe fn dangerous() { }

fn call_dangerous() {
    unsafe {
        // 需要显式标记内部 unsafe 调用
        unsafe { dangerous(); }
        println!("called");
    }
}
```

**设计理由**: 明确区分"调用 unsafe 函数"和"unsafe 块中的安全操作"，减少误读。

**迁移策略**: `cargo fix --edition` 自动添加。审查时确认每个 `unsafe { }` 都是必要的。

### 4.2 `std::env::set_var` 变为 `unsafe`

**变更前**:

```rust
std::env::set_var("KEY", "value"); // 安全函数
```

**变更后**:

```rust
// 需要 unsafe 块，因为修改环境变量影响全局状态，
// 在多线程环境中可能导致未定义行为
unsafe {
    std::env::set_var("KEY", "value");
}
```

**迁移策略**:

```bash
# 搜索项目中所有 set_var 调用
grep -rn "set_var" src/

# 逐处审查并添加 unsafe 块
# 注意: 在多线程代码中使用 set_var 应格外谨慎
```

### 4.3 临时变量作用域收紧

**变更前（可能编译或行为不同）**:

```rust
let x = &temp_value();
println!("{}", x); // temp_value() 在此处仍存活
```

**变更后（临时值更早 drop）**:

```rust
let x = &temp_value();
// temp_value() 的返回值在此处已 drop
println!("{}", x); // ❌ 编译错误: 悬垂引用
```

**迁移策略**:

```rust
// 方案 1: 绑定到具名变量
let temp = temp_value();
let x = &temp;
println!("{}", x);

// 方案 2: 直接传递值而非引用
println!("{}", temp_value());
```

### 4.4 异步闭包

**变更前（需要 async_trait 或手动 Future）**:

```rust
use async_trait::async_trait;

let f = async || { "hello".to_string() };
// 错误: 异步闭包在 Edition 2021 中不支持
```

**变更后（原生支持）**:

```rust
// Edition 2024 原生异步闭包
let f = async || { "hello".to_string() };
let result = f().await;

// 与 move 结合
let data = vec![1, 2, 3];
let g = async move || { data.len() };
```

**迁移策略**: 逐步将 `async_trait` 模拟的闭包模式替换为原生语法。

---

## 五、迁移检查清单

```markdown
## Edition 2024 迁移检查清单

### 自动步骤
- [ ] `rustup update stable` (确保 >= 1.85.0)
- [ ] `cargo fix --edition`
- [ ] `cargo check` (零错误)
- [ ] `cargo clippy` (零警告)
- [ ] `cargo test` (全部通过)

### 手动审查
- [ ] 搜索所有 `set_var` 调用，确认 unsafe 块包裹
- [ ] 检查 `gen` 作为标识符的使用（变量/函数/模块名）
- [ ] 审查 unsafe 代码块中的嵌套 unsafe 标记
- [ ] 检查依赖特定 drop 顺序的测试
- [ ] 验证异步闭包替换 async_trait 模拟后的行为

### Cargo.toml 更新
- [ ] `edition = "2024"`
- [ ] `rust-version = "1.85.0"` (如需要)
- [ ] 检查 workspace edition 继承
```

---

## 六、版本兼容性矩阵

| 你的代码 Edition | 依赖库 Edition | 兼容性 |
|:---|:---|:---:|
| 2024 | 2021 | ✅ 完全兼容 |
| 2024 | 2018 | ✅ 完全兼容 |
| 2021 | 2024 | ✅ 完全兼容 |
| 2024 | 2024 | ✅ 完全兼容 |

> **关键保证**: Edition 差异仅限于**语法解析层**，生成的 LLVM IR 和 ABI 完全一致。因此跨 Edition 的 crate 可以任意链接。

---

## 七、常见问题 (FAQ)

### Q1: 不迁移到 2024 Edition 会有什么后果？

**A**: 没有立即后果。2021 Edition 继续受支持。但：

- 无法使用 `async` 闭包等 2024 语法特性
- 新 crate 默认使用 2024 Edition
- 长期维护成本增加

### Q2: `cargo fix --edition` 会破坏代码吗？

**A**: 不会。`cargo fix` 只在确认语义等价时才应用变更。但：

- 建议先提交 git 再进行迁移
- 迁移后必须运行完整测试套件

### Q3: 大型 workspace 如何批量迁移？

**A**:

```bash
# 在 workspace 根目录
cargo fix --edition --workspace

# 或在 Cargo.toml 中统一设置:
[workspace.package]
edition = "2024"
rust-version = "1.85.0"
```

---

## 八、来源与参考

| 来源 | 说明 |
|:---|:---|
| [Edition Guide — Rust 2024](https://doc.rust-lang.org/edition-guide/rust-2024/) | 官方 Edition 迁移指南 |
| [TRPL 第三版 — Ch.17 异步](https://doc.rust-lang.org/book/ch17-00-async-await.html) | 异步闭包等内容 |
| [Rust 1.85.0 Release Notes](https://blog.rust-lang.org/2025/02/20/Rust-1.85.0.html) | 2024 Edition 稳定公告 |
| [cargo fix 文档](https://doc.rust-lang.org/cargo/commands/cargo-fix.html) | 自动迁移工具 |

---

**文档版本**: 1.0
**对应 Rust 版本**: 1.85.0+ (Edition 2024)
**最后更新**: 2026-06-01
**状态**: ✅ 概念文档创建完成

> **权威来源**: [Edition Guide](https://doc.rust-lang.org/edition-guide/rust-2024/), [Rust 1.85.0 Release Notes](https://blog.rust-lang.org/2025/02/20/Rust-1.85.0.html)
>
> **权威来源对齐变更日志**: 2026-06-01 创建 [来源: Official Edition Guide]
