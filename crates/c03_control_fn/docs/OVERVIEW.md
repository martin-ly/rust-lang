# 概览：控制流与函数（c03_control_fn）

本模块覆盖 Rust 控制流、函数抽象、错误传播、异步控制流等主题，并与 Rust 1.89 的增强特性进行对齐。

---

## 目录导航

- 版本与特性对齐
  - [RUST_189_FEATURES_SUMMARY.md](./RUST_189_FEATURES_SUMMARY.md)
  - [RUST_189_ENHANCED_FEATURES.md](./RUST_189_ENHANCED_FEATURES.md)
  - [RUST_189_COMPREHENSIVE_FEATURES.md](./RUST_189_COMPREHENSIVE_FEATURES.md)
  - [RUST_189_MIGRATION_GUIDE.md](./RUST_189_MIGRATION_GUIDE.md)
  - [RUST_189_PRACTICAL_GUIDE.md](./RUST_189_PRACTICAL_GUIDE.md)

- 控制流视图
  - [view01.md](./view01.md)
  - [view02.md](./view02.md)
  - 片段示例：`snippets/async_control_flow_example.rs`

- 专题：所有权与访问控制
  - [Rust 所有权模型针对特定类型的访问控制.md](./Rust 所有权模型针对特定类型的访问控制.md)

---

### 快速开始

1. 从 `RUST_189_FEATURES_SUMMARY.md` 了解版本变化
2. 阅读 `view01.md` / `view02.md` 建立控制流全景
3. 跑通 `snippets/` 的异步控制流示例

---

### 待完善

详见 [PENDING_ITEMS.md](./PENDING_ITEMS.md)。主要项：

- 增补错误处理与 `Result`/`?` 的边界案例与最佳实践
- 增补迭代器与闭包在控制流中的协同示例
- 与 `c06_async` 的 async/await 场景互链

#### 错误处理边界案例（补全）

- From/Into 错误映射； anyhow vs thiserror；早返回与资源释放（RAII）
- 样例：

```rust
fn parse(data: &str) -> Result<u32, std::num::ParseIntError> { data.parse() }

fn process(s: &str) -> anyhow::Result<()> {
    let n = parse(s)?; // 边界：错误类型不一致时用 `map_err` 或 `?` + `From`
    println!("{}", n);
    Ok(())
}
```

#### 迭代器与闭包（补全）

```rust
let sum: i64 = (0..1_000).filter(|x| x % 2 == 0).map(|x| x as i64).sum();
```

#### 互链

- 与 `c06_async`：错误传播与 `?` 在 `async fn` 中的使用、`Result<_, anyhow::Error>` 的边界
