# Builder 惯用法

**EN**: Builder Idiom
**Summary**: Separate the construction of a complex object from its representation via a consuming, chainable builder.

```mermaid
mindmap
  root((Builder))
    Chainable API
      method(self) -> Self
    Optional fields
      default values
    Validation
      build returns Result
    Consumption
      consuming vs non-consuming
    Pitfalls
      partial move
      builder reuse after build
```

> **Rust 版本**: 1.97.0+ (Edition 2024)
> **Bloom 层级**: L5
> **权威来源**: 本文件为 `concept/` 权威页。
> **前置概念**: [结构体](../../../01_foundation/07_modules_and_items/04_structs.md) · [错误处理](../../../01_foundation/08_error_handling/01_error_handling_basics.md)
> **后置概念**: [Typestate](./05_typestate.md)

---

## 一、权威定义

Builder 模式将复杂对象的**构造过程**拆分为多个步骤，每一步通过链式方法设置一个字段，最后由 `build` 方法返回构造完成的对象或错误。

Rust 中的 Builder 通常采用**消耗式（consuming）**设计：每个设置方法获取 `self` 并返回 `Self`，这样可以在编译期防止部分 move 问题，并自然支持不可变链式调用。

## 二、核心属性与关系

| 属性 | 说明 |
|:---|:---|
| **可选字段默认值** | Builder 持有 `Option<T>` 或默认值，未设置时使用默认。 |
| **验证集中化** | 必填字段缺失或组合非法在 `build` 中统一返回错误。 |
| **不可变链** | 消耗式 builder 的每个方法获取所有权，调用链不需要可变引用。 |
| **与 Typestate 结合** | 可通过 Typestate 在类型层面保证必填字段已设置。 |

## 三、正向推理决策树

```text
对象包含多个字段，尤其是可选字段？
├── 否 → 直接构造函数或 struct literal。
└── 是
    ├── 字段数量 ≥ 4 或存在多个可选字段？
    │   └── 是 → Builder 显著提升可读性。
    ├── 构造过程需要分阶段验证？
    │   └── 是 → Builder 的 build() 集中校验。
    └── 是否需要不可变链式调用？
        └── 是 → 使用 consuming builder（self -> Self）。
```

## 四、反向推理决策树

```text
Builder 使用体验差？
├── 链式调用中某一步返回 Result，破坏流畅性？
│   └── 将可能失败的操作放在 build 中，或拆分为 let 绑定。
├── 需要复用 builder 构建多个对象？
│   └── 使用非消耗式 builder（&mut self）或实现 Clone。
├── 必填字段缺失导致运行时 panic？
│   └── 让 build 返回 Result，或使用 Typestate 在编译期保证。
└── 默认值太多导致 builder 样板冗长？
    └── 使用 derive_builder 等宏生成。
```

## 五、Rust 表达与示例

```rust
#[derive(Debug, PartialEq, Eq)]
pub struct Request {
    method: String,
    url: String,
    timeout_ms: u64,
}

pub struct RequestBuilder {
    method: Option<String>,
    url: Option<String>,
    timeout_ms: u64,
}

impl RequestBuilder {
    pub fn new() -> Self {
        Self {
            method: None,
            url: None,
            timeout_ms: 5000,
        }
    }

    pub fn method(mut self, value: impl Into<String>) -> Self {
        self.method = Some(value.into());
        self
    }

    pub fn url(mut self, value: impl Into<String>) -> Self {
        self.url = Some(value.into());
        self
    }

    pub fn timeout_ms(mut self, value: u64) -> Self {
        self.timeout_ms = value;
        self
    }

    pub fn build(self) -> Result<Request, &'static str> {
        Ok(Request {
            method: self.method.ok_or("method is required")?,
            url: self.url.ok_or("url is required")?,
            timeout_ms: self.timeout_ms,
        })
    }
}

fn main() {
    let req = RequestBuilder::new()
        .method("GET")
        .url("https://example.com")
        .timeout_ms(3000)
        .build()
        .unwrap();
    assert_eq!(req.method, "GET");
}
```

## 六、反例与常见错误

消耗式 builder 在 `build` 后不能被再次使用：

```rust,compile_fail,E0382
#[derive(Default)]
struct Builder {
    value: Option<i32>,
}

impl Builder {
    fn value(mut self, v: i32) -> Self { self.value = Some(v); self }
    fn build(self) -> i32 { self.value.unwrap_or(0) }
}

fn main() {
    let b = Builder::default();
    let _ = b.build();
    let _ = b.value(10); // ❌ b 已被 move 进 build
}
```

## 七、国际权威来源

- [Rust API Guidelines — Type Construction](https://rust-lang.github.io/api-guidelines/flexibility.html#c-builder)
- [Rust Design Patterns — Builder](https://rust-unofficial.github.io/patterns/creational/builder.html)
- [Refactoring Guru — Builder Pattern](https://refactoring.guru/design-patterns/builder)

## 来源与延伸阅读

- [RustBelt — Logical Foundations for Safe Systems Programming](https://plv.mpi-sws.org/rustbelt/)（P1 形式化基础）
- [Do Code LLMs Understand Design Patterns?](https://arxiv.org/abs/2501.04835)（P1 Builder 模式研究）
- [derive_builder — Derive Builder Pattern](https://docs.rs/derive_builder/latest/derive_builder/)（P2 生态）
- [derive_builder on crates.io](https://crates.io/crates/derive_builder)
- [Stabilizing async fn in traits in 2023](https://blog.rust-lang.org/inside-rust/2023/05/03/stabilizing-async-fn-in-trait.html)（P2 官方博客，builder-provider 案例）

## 形式化基础

本页的工程模式可追溯到以下 L4 形式化/理论权威页：

- [类型论基础](../../../04_formal/00_type_theory/01_type_theory.md)
- [操作语义](../../../04_formal/03_operational_semantics/03_operational_semantics.md)
- [λ 演算与可计算性](../../../04_formal/00_type_theory/05_lambda_calculus.md)
