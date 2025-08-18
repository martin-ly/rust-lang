# 持续集成与持续交付（CI/CD, Continuous Integration & Continuous Delivery）

## 1. 定义与软件工程对标

**CI/CD**是指通过自动化测试、构建、部署，实现代码变更的高效集成与快速交付。软件工程wiki认为，CI/CD是现代敏捷开发和DevOps的核心。
**CI/CD** means automating testing, building, and deployment to enable efficient integration and rapid delivery of code changes. In software engineering, CI/CD is central to agile development and DevOps.

## 2. Rust 1.88 最新特性

- **异步trait**：高效实现并发流水线任务。
- **trait对象向上转型**：便于插件化扩展CI/CD步骤。
- **LazyLock**：全局流水线状态缓存。

## 3. 典型惯用法（Idioms）

- 使用GitHub Actions/GitLab CI自动化Rust项目测试与发布
- 结合cargo-make/justfile定义流水线任务
- 利用trait抽象构建、测试、部署等步骤

## 4. 代码示例

```rust
trait Step {
    async fn execute(&self) -> Result<(), Error>;
}
```

## 5. 软件工程概念对照

- **自动化（Automation）**：流水线全流程自动化。
- **可追溯性（Traceability）**：每次变更可审计、可回滚。
- **高可用（High Availability）**：自动化部署减少人为失误。

## 6. FAQ

- Q: Rust项目CI/CD的优势？
  A: 编译快、类型安全、易于自动化，适合高频交付场景。

---
