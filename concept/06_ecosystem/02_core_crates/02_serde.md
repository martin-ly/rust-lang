> **EN**: Serde
> **Summary**: Serde is Rust's canonical serialization framework, using derive macros and the Serialize/Deserialize traits to map Rust ADTs to JSON, TOML, YAML, MessagePack, and other formats with zero-cost abstraction.
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **生态版本**: serde 1.0
> **Bloom 层级**: L6
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **P** — Procedure
> **前置概念**:
> [Ownership](../../01_foundation/01_ownership_borrow_lifetime/01_ownership.md) ·
> [Traits](../../02_intermediate/00_traits/01_traits.md) ·
> [Generics](../../02_intermediate/01_generics/01_generics.md) ·
> [Procedural Macros](../../03_advanced/03_proc_macros/01_macros.md) ·
> [Error Handling](../../02_intermediate/03_error_handling/01_error_handling.md)
> **后置概念**:
> [tokio](./03_tokio.md) ·
> [reqwest](./06_reqwest.md) ·
> [axum](./07_axum.md) ·
> [Application Domains](../06_data_and_distributed/01_application_domains.md)
> **主要来源**:
> [serde.rs](https://serde.rs) ·
> [serde GitHub](https://github.com/serde-rs/serde) ·
> [The Rust Programming Language](https://doc.rust-lang.org/book/) ·
> [Rust API Guidelines — Data structures](https://rust-lang.github.io/api-guidelines/) ·
> [Wikipedia: Serialization](https://en.wikipedia.org/wiki/Serialization)
> **定理链**: N/A — 描述性/工程性文档，不涉及形式化定理链

---

# Serde 序列化框架

## 一、权威定义

- **crate 官方定义**：*Serde is a framework for serializing and deserializing Rust data structures efficiently and generically.*（[serde.rs](https://serde.rs)）
- **Wikipedia 定义**：Serialization is the process of translating a data structure or object state into a format that can be stored or transmitted and reconstructed later.（[Wikipedia: Serialization](https://en.wikipedia.org/wiki/Serialization)）
- **在本知识体系中的定位**：`serde` 是 Rust 生态的**事实标准序列化层**。它通过 `Serialize` / `Deserialize` trait 与 `#[derive(Serialize, Deserialize)]` 过程宏，将代数数据类型（ADT）映射到 JSON、TOML、YAML、MessagePack、Protocol Buffers 等数十种格式，是 Rust **Trait 系统 + 过程宏 + 零成本抽象**的工业级典范。

判定依据：serde 被绝大多数 Rust crate 作为传递依赖；选型序列化方案时默认优先评估 serde + 对应格式 crate。

---

## 二、关键类型与 Traits

| **类型 / Trait** | **作用域** | **说明** |
|:---|:---|:---|
| `serde::Serialize` | Trait | 定义如何将 Rust 类型编码为通用数据模型；由格式 crate 的 `Serializer` 消费。 |
| `serde::Deserialize` | Trait | 定义如何从通用数据模型重建 Rust 类型；由格式 crate 的 `Deserializer` 消费。 |
| `serde::Serializer` | Trait | 格式实现侧接口，负责把数据模型写入具体格式（JSON、TOML 等）。 |
| `serde::Deserializer` | Trait | 格式实现侧接口，负责从具体格式读取数据模型。 |
| `serde_json::to_string` / `to_vec` | 函数 | 将实现了 `Serialize` 的值编码为 JSON 字符串 / 字节。 |
| `serde_json::from_str` / `from_slice` | 函数 | 将 JSON 字符串 / 字节反序列化为实现了 `Deserialize` 的类型。 |
| `#[derive(Serialize, Deserialize)]` | 过程宏 | 为 struct / enum 自动生成 trait 实现；支持字段重命名、跳过、默认值等属性。 |
| `#[serde(rename = "...")]` | 属性 | 控制字段 / variant 在目标格式中的名字（常用于 snake_case ↔ camelCase）。 |
| `#[serde(skip_serializing_if = "...")]` | 属性 | 条件跳过字段，减少输出体积并避免无意义字段。 |

**关键洞察**：serde 本身是格式无关的。`Serialize` / `Deserialize` trait 只定义 Rust 类型与 serde 通用数据模型之间的契约；具体的 JSON/TOML/YAML 编解码由 `serde_json`、`serde_yaml`、`toml` 等 crate 实现。这种分层使新格式可以在不修改用户代码的情况下被加入。

---

## 三、惯用法与示例

### 3.1 最小可用示例：JSON round-trip

```rust
// Cargo.toml
// [dependencies]
// serde = { version = "1", features = ["derive"] }
// serde_json = "1"

use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize, PartialEq)]
struct User {
    id: u64,
    name: String,
    active: bool,
}

fn main() -> Result<(), serde_json::Error> {
    let user = User {
        id: 1,
        name: "Alice".to_string(),
        active: true,
    };

    let json = serde_json::to_string(&user)?;
    println!("{}", json);
    // {"id":1,"name":"Alice","active":true}

    let decoded: User = serde_json::from_str(&json)?;
    assert_eq!(user, decoded);
    Ok(())
}
```

### 3.2 惯用 idiom：字段重命名与默认值

```rust
// Cargo.toml
// [dependencies]
// serde = { version = "1", features = ["derive"] }
// serde_json = "1"

use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize, PartialEq)]
#[serde(rename_all = "camelCase")]
struct Config {
    #[serde(default)]
    max_retries: u32,
    #[serde(default = "default_timeout")]
    timeout_ms: u64,
    #[serde(skip_serializing_if = "Option::is_none")]
    region: Option<String>,
}

fn default_timeout() -> u64 {
    5_000
}

fn main() -> Result<(), serde_json::Error> {
    let cfg: Config = serde_json::from_str(r#"{"timeoutMs": 1000}"#)?;
    assert_eq!(cfg.max_retries, 0);
    assert_eq!(cfg.timeout_ms, 1_000);
    assert_eq!(cfg.region, None);

    let json = serde_json::to_string(&cfg)?;
    println!("{}", json);
    // {"maxRetries":0,"timeoutMs":1000}
    Ok(())
}
```

### 3.3 与网络 / Web 生态的组合用法

```rust,ignore
// Axum + serde_json 返回 JSON 的典型片段
use axum::{Json, Router, routing::get};
use serde::Serialize;

#[derive(Serialize)]
struct Health {
    status: &'static str,
}

async fn health() -> Json<Health> {
    Json(Health { status: "ok" })
}

#[tokio::main]
async fn main() {
    let app = Router::new().route("/health", get(health));
    // axum::serve(...).await ...
}
```

> **关键设计**：`Json<T>` 提取器 / 响应器要求 `T: Serialize` 或 `T: Deserialize`，把 HTTP 请求体与 Rust 类型在编译期绑定，避免运行时字段缺失或类型不匹配。

---

## 四、常见陷阱与边界测试

### 陷阱 1：为外部类型实现外部 trait

`Serialize` / `Deserialize` 属于 serde，若目标类型也来自外部 crate，则违反 Rust **孤儿规则（Orphan Rule）**，无法直接 `impl Serialize for ExternalType`。

❌ 错误做法：

```rust,ignore
use serde::Serialize;
use some_crate::ExternalId;

impl Serialize for ExternalId {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_u64(self.0)
    }
}
```

✅ 修正做法：使用 newtype 模式包装外部类型，并为包装类型实现 serde trait。

```rust
use serde::Serialize;
use std::fmt;

#[derive(Debug)]
struct ExternalId(u64); // 占位外部类型

#[derive(Debug, Serialize)]
#[serde(transparent)]
struct ExternalIdWrapper(ExternalId);

impl fmt::Display for ExternalId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Serialize for ExternalIdWrapper {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_str(&self.0.to_string())
    }
}
```

> **原理**：newtype 在本地 crate 中定义，因此 `impl Serialize for ExternalIdWrapper` 满足孤儿规则。

### 陷阱 2：enum 反序列化时字段名不匹配

JSON 字段名默认与 Rust 字段名一致；目标格式使用 camelCase 或 kebab-case 时未加 `rename_all` 会导致反序列化失败。

❌ 错误做法：

```rust,ignore
use serde::Deserialize;

#[derive(Deserialize, Debug)]
struct Task {
    task_id: u64,
}

fn main() {
    let t: Task = serde_json::from_str(r#"{"taskId": 42}"#).unwrap(); // panic
}
```

✅ 修正做法：

```rust
use serde::Deserialize;

#[derive(Deserialize, Debug)]
#[serde(rename_all = "camelCase")]
struct Task {
    task_id: u64,
}

fn main() {
    let t: Task = serde_json::from_str(r#"{"taskId": 42}"#).unwrap();
    println!("{:?}", t);
}
```

### 陷阱 3：反序列化时缺失字段导致 panic

未对 `from_str` 返回的 `Result` 做错误处理，或默认未声明字段，会在输入缺失字段时失败。

❌ 错误做法：

```rust,ignore
let user: User = serde_json::from_str(r#"{}"#).unwrap();
```

✅ 修正做法：使用 `#[serde(default)]` 或为字段提供默认值，并对 `Result` 做显式处理。

```rust
use serde::Deserialize;

#[derive(Deserialize, Debug)]
struct User {
    #[serde(default)]
    name: String,
    #[serde(default)]
    active: bool,
}

fn main() {
    match serde_json::from_str::<User>(r#"{}"#) {
        Ok(u) => println!("{:?}", u),
        Err(e) => eprintln!("parse failed: {}", e),
    }
}
```

---

## 五、版本说明

- **当前稳定版本**：serde 1.0.x（语义化主版本 1.0 已长期稳定；最新 patch 版本见 [crates.io/serde](https://crates.io/crates/serde)）。
- **MSRV 政策**：serde 1.0 系列支持较宽的 Rust 版本窗口，通常兼容多个 Edition；具体 MSRV 以 crate 主页 / `Cargo.toml` `rust-version` 字段为准。本知识库以 **Rust 1.97.1+ (Edition 2024)** 为基线。
- **Edition 2024 注意点**：serde derive 宏在 Edition 2024 下无需额外配置；`Cargo.toml` 中使用 `edition.workspace = true` 时，依赖仍使用标准 `serde = { version = "1", features = ["derive"] }`。
- **近期特性动向**（稳定后将在版本追踪页更新）：serde 核心 trait 保持高度稳定，新增能力通常体现在格式 crate（`serde_json` 的 `arbitrary_precision`、`toml` 的 `preserve_order` 等）和 `serde_derive` 的更多属性支持上。

---

## 六、思维导图（Mindmap）

```mermaid
mindmap
  root((serde))
    核心抽象
      Serialize trait
      Deserialize trait
      Serializer / Deserializer
    格式生态
      serde_json
      serde_yaml
      toml
      serde_with
    derive 宏
      #[derive(Serialize, Deserialize)]
      #[serde(rename_all)]
      #[serde(default)]
    工程组合
      axum Json
      reqwest json()
      sqlx query_as!
    常见陷阱
      孤儿规则 / newtype
      字段命名不匹配
      缺失字段默认值
    版本与生态
      1.0 长期稳定
      MSRV 兼容
      Edition 2024 可用
```

---

## 七、嵌入式测验

### 测验 1：serde 的核心机制是什么？（理解层）

serde 实现序列化的关键机制是什么？

- A. 运行时反射遍历字段
- B. `#[derive(Serialize, Deserialize)]` 过程宏在编译期生成 trait 实现
- C. 要求每个格式都内置 Rust 类型知识
- D. 使用 `unsafe` 绕过类型系统进行内存拷贝

<details>
<summary>✅ 答案</summary>

**B. `#[derive(Serialize, Deserialize)]` 过程宏在编译期生成 trait 实现**。

serde 基于 `Serialize` / `Deserialize` trait 与格式无关的 `Serializer` / `Deserializer` 接口，通过 derive 宏为每个 ADT 单态化生成编解码代码，零运行时反射。
</details>

---

### 测验 2：以下代码能否编译？（应用层）

```rust,ignore
use serde::Serialize;
use external_crate::Uuid;

impl Serialize for Uuid {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where S: serde::Serializer,
    {
        serializer.serialize_str(&self.to_string())
    }
}
```

- A. 能，因为 `Serialize` 是标准 trait
- B. 不能，因为违反孤儿规则
- C. 能，只要 `external_crate` 启用了 serde feature
- D. 不能，因为 `Serialize` 只能在当前 crate 中定义的类型上实现

<details>
<summary>✅ 答案</summary>

**B. 不能，因为违反孤儿规则**。

`Uuid` 和 `Serialize` 都来自外部 crate，Rust 不允许为外部类型实现外部 trait。应使用 newtype 包装后再实现 `Serialize`。
</details>

---

### 测验 3：需要把 Rust 字段 `user_name` 序列化成 JSON 的 `userName`，应使用哪个属性？（应用层）

- A. `#[serde(rename = "userName")]`
- B. `#[serde(rename_all = "camelCase")]`
- C. `#[serde(skip)]`
- D. A 和 B 都可以，取决于作用范围

<details>
<summary>✅ 答案</summary>

**D. A 和 B 都可以，取决于作用范围**。

- 字段级：`#[serde(rename = "userName")]` 仅改变该字段。
- 结构体级：`#[serde(rename_all = "camelCase")]` 把所有字段统一映射为 camelCase。

</details>

---

### 测验 4：判断正误（分析层）

serde 本身是格式无关的，它只定义 Rust 类型与通用数据模型之间的契约，真正的 JSON / YAML / TOML 编码由 `serde_json`、`serde_yaml`、`toml` 等格式 crate 完成。

- 正确
- 错误

<details>
<summary>✅ 答案</summary>

**正确**。

serde 核心 crate 只提供 trait 与通用 `Serializer` / `Deserializer` 接口。具体格式实现位于独立 crate，这也是 serde 能支持数十种数据格式的原因。
</details>

---

## 八、国际权威来源

- **P0 官方 / Rust Book**
  - [The Rust Programming Language](https://doc.rust-lang.org/book/)：Rust 官方教材，是理解 trait、所有权与宏系统的前提。
  - [The Rust Reference — Macros](https://doc.rust-lang.org/reference/macros.html)：过程宏的语法与展开规则。
  - 状态：链接可访问（截至最近巡检）。

- **P2 crate 文档与源码**
  - [serde.rs](https://serde.rs)：serde 官方文档与 derive 属性参考。
  - [serde on docs.rs](https://docs.rs/serde)：API 文档，包含 trait 与数据模型说明。
  - [serde GitHub 仓库](https://github.com/serde-rs/serde)：源码、Issue、MSRV 与发布说明。
  - [serde_json on docs.rs](https://docs.rs/serde_json)：JSON 格式实现的关键 API。
  - 状态：链接可访问；版本信息以 crates.io 最新发布为准。

- **补充来源**
  - [Wikipedia: Serialization](https://en.wikipedia.org/wiki/Serialization)：序列化通用概念定义。
  - [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/)：与数据结构设计相关的 Rust 生态指南。

---

## 九、相关概念链接

| 概念 | 文件 | 关系 |
|:---|:---|:---|
| 所有权（Ownership） | [`../../01_foundation/01_ownership_borrow_lifetime/01_ownership.md`](../../01_foundation/01_ownership_borrow_lifetime/01_ownership.md) | Rust 资源管理根基，serde 编解码遵守所有权移动 / 借用规则。 |
| Trait 系统 | [`../../02_intermediate/00_traits/01_traits.md`](../../02_intermediate/00_traits/01_traits.md) | `Serialize` / `Deserialize` 是 trait 抽象的核心用例。 |
| 泛型（Generics） | [`../../02_intermediate/01_generics/01_generics.md`](../../02_intermediate/01_generics/01_generics.md) | serde 通过泛型实现格式无关与零成本单态化。 |
| 过程宏 | [`../../03_advanced/03_proc_macros/01_macros.md`](../../03_advanced/03_proc_macros/01_macros.md) | `#[derive(Serialize, Deserialize)]` 的底层机制。 |
| 错误处理 | [`../../02_intermediate/03_error_handling/01_error_handling.md`](../../02_intermediate/03_error_handling/01_error_handling.md) | `serde_json::Error` 与 `?` 的错误传播实践。 |
| tokio | [`./03_tokio.md`](./03_tokio.md) | 与 serde 在网络 / Web 场景中组合使用。 |
| reqwest | [`./06_reqwest.md`](./06_reqwest.md) | 通过 `.json::<T>()` 完成 HTTP JSON 反序列化。 |
| axum | [`./07_axum.md`](./07_axum.md) | `Json<T>` 提取器依赖 serde。 |
| Rust vs Java | [`../../05_comparative/02_managed_languages/01_rust_vs_java.md`](../../05_comparative/02_managed_languages/01_rust_vs_java.md) | 类型系统与序列化生态的跨语言对比视角。 |

---

> **认知功能**: 本页建立 serde 的独立权威画像：从 trait 与 derive 宏的核心抽象出发，覆盖 JSON round-trip、字段映射、Web 组合、孤儿规则与默认值等关键工程陷阱，并以思维导图和测验巩固 L6 应用层记忆。使用建议：在学习网络 / Web crate 之前先掌握 serde 基础；遇到外部类型序列化问题时优先使用 newtype 模式。
