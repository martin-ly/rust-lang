# 基础设施即代码（Infrastructure as Code, IaC）

## 1. 定义与软件工程对标

**基础设施即代码（IaC）**是用代码管理和配置基础设施资源的实践。软件工程wiki认为，IaC是自动化运维和可重复部署的基础。
**Infrastructure as Code (IaC)** is the practice of managing and provisioning infrastructure resources using code. In software engineering, IaC is foundational for automated operations and repeatable deployments.

## 2. Rust 1.88 最新特性

- **异步trait**：高效处理并发资源操作。
- **trait对象向上转型**：便于抽象多云和多平台资源。
- **LazyLock**：全局状态与配置缓存。

## 3. 典型惯用法（Idioms）

- 使用serde/toml/yaml解析配置
- 结合async/await实现自动化流程
- 利用trait抽象资源提供者与操作器

## 4. 代码示例

```rust
trait Resource {
    async fn provision(&self) -> Result<(), Error>;
}
```

## 5. 软件工程概念对照

- **自动化（Automation）**：代码驱动基础设施变更。
- **可重复性（Repeatability）**：配置即代码，易于回滚和审计。
- **可扩展性（Scalability）**：trait支持多平台扩展。

## 6. FAQ

- Q: Rust做IaC工具的优势？
  A: 性能高、类型安全、易于并发扩展，适合大规模自动化场景。

---
