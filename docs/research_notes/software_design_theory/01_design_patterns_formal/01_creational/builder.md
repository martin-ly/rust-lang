# Builder 形式化分析

> **创建日期**: 2026-02-12
> **分类**: 创建型
> **安全边界**: 纯 Safe

---

## 形式化定义

**Def 1.1（Builder 结构）**

设 $B$ 为 Builder 类型，$T$ 为目标类型。Builder 满足：

- $\exists \mathit{build} : B \to \mathrm{Result}(T)$ 或 $B \to T$
- $\mathit{build}$ 消费 $B$（所有权转移：$\Omega(B) \mapsto \emptyset$）
- 可选：$\mathit{set}_i : B \times V_i \to B$ 链式构建，返回 `Self` 实现流式 API

**Axiom B1**：`build` 调用时必填字段已设置；否则返回 `Err` 或 panic。

**Axiom B2**：`build` 消费 `self`；调用后 $B$ 无效，保证单次构建。

**定理 B-T1**：由 [ownership_model](../../../formal_methods/ownership_model.md) T2，`build(self)` 消费 $B$ 后 $B$ 无效，无双重使用。

**定理 B-T2**：类型状态模式可强制编译期必填：`ConfigBuilder<SetHost>` 与 `ConfigBuilder<SetPort>` 等相位类型，仅当所有相位完成时 `build` 可用。

---

## Rust 实现与代码示例

```rust
struct Config {
    host: String,
    port: u16,
    timeout: u64,
}

struct ConfigBuilder {
    host: Option<String>,
    port: Option<u16>,
    timeout: Option<u64>,
}

impl ConfigBuilder {
    fn new() -> Self {
        Self { host: None, port: None, timeout: None }
    }

    fn host(mut self, host: String) -> Self {
        self.host = Some(host);
        self
    }

    fn port(mut self, port: u16) -> Self {
        self.port = Some(port);
        self
    }

    fn build(self) -> Result<Config, String> {
        Ok(Config {
            host: self.host.ok_or("host required")?,
            port: self.port.ok_or("port required")?,
            timeout: self.timeout.unwrap_or(30),
        })
    }
}

// 使用：链式调用，build 消费 self
let config = ConfigBuilder::new()
    .host("localhost".to_string())
    .port(8080)
    .build()?;
```

**形式化对应**：`build(self)` 即 $\mathit{build} : B \to \mathrm{Result}(T)$；`self` 被消费，符合 Axiom B2。

---

## 证明思路

1. **单次构建**：`build` 取 `self` 而非 `&self`，调用后 builder 被移动，无法再次调用。由 ownership T2。
2. **必填校验**：`ok_or` 在缺省时返回 `Err`；或使用类型状态在编译期消除缺失分支。

---

## 典型场景

| 场景 | 说明 |
| :--- | :--- |
| 复杂配置 | 多可选参数、默认值 |
| SQL/查询构建 | 链式添加条件 |
| 请求构建 | HTTP 请求头、体、参数 |
| 类型状态 Builder | 强制顺序：必填 → 可选 → build |

---

## 相关模式

| 模式 | 关系 |
| :--- | :--- |
| [Factory Method](factory_method.md) | Builder 可由 Factory 创建 |
| [Abstract Factory](abstract_factory.md) | 可组合：Factory 返回 Builder |
| [Prototype](prototype.md) | 可组合：Builder 基于 Prototype 克隆 |

---

## 实现变体

| 变体 | 说明 | 适用 |
| :--- | :--- | :--- |
| Option + ok_or | 运行时校验；缺省返回 Err | 简单构建 |
| 类型状态 Builder | 相位类型；编译期强制顺序 | 必填→可选→build |
| derive_builder | 宏生成；减少样板代码 | 结构体多字段 |

---

## 反例

**反例**：`build()` 在必填字段未设置时调用 → 返回 `Err` 或 panic。类型状态模式可强制编译期检查。

---

## 错误处理

`build()` 返回 `Result<Config, String>` 时，缺必填字段用 `ok_or("host required")?` 传播 Err；调用方用 `?` 或 `match` 处理。避免 `unwrap()` 导致不可恢复 panic。

---

## 选型决策树

```
需要多步骤、可选参数构建？
├── 是 → 需编译期必填？ → 类型状态 Builder
│       └── 运行时校验即可？ → Option + ok_or
├── 否 → 单产品、简单？ → Factory Method
└── 需克隆已有对象？ → Prototype
```

---

## 与 GoF 对比

| GoF | Rust 对应 | 差异 |
| :--- | :--- | :--- |
| Director + Builder | 可选；Rust 常直接链式 | 等价 |
| 链式 set | `fn set(self, v) -> Self` | 消费 self 更安全 |
| build 消费 | `fn build(self) -> T` | 单次构建，等价 |

---

## 边界

| 维度 | 分类 |
| :--- | :--- |
| 安全 | 纯 Safe |
| 支持 | 原生 |
| 表达 | 等价 |
