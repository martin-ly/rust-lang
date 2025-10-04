# 🤝 贡献指南

感谢你对 c13_reliability 项目的关注！我们欢迎所有形式的贡献。

---

## 📋 目录

- [🤝 贡献指南](#-贡献指南)
  - [📋 目录](#-目录)
  - [🌟 行为准则](#-行为准则)
    - [我们的承诺](#我们的承诺)
    - [不可接受的行为](#不可接受的行为)
  - [🚀 如何贡献](#-如何贡献)
    - [报告Bug](#报告bug)
    - [建议新功能](#建议新功能)
    - [改进文档](#改进文档)
  - [🛠️ 开发环境设置](#️-开发环境设置)
    - [前置要求](#前置要求)
    - [克隆仓库](#克隆仓库)
    - [安装依赖](#安装依赖)
    - [运行测试](#运行测试)
    - [检查代码](#检查代码)
  - [📝 代码规范](#-代码规范)
    - [Rust代码风格](#rust代码风格)
    - [命名规范](#命名规范)
    - [注释规范](#注释规范)
    - [错误处理](#错误处理)
    - [异步代码](#异步代码)
  - [📤 提交规范](#-提交规范)
    - [Commit Message格式](#commit-message格式)
    - [类型](#类型)
    - [示例](#示例)
  - [🔄 Pull Request流程](#-pull-request流程)
    - [1. Fork仓库并创建分支](#1-fork仓库并创建分支)
    - [2. 开发和测试](#2-开发和测试)
    - [3. 提交更改](#3-提交更改)
    - [4. 推送并创建PR](#4-推送并创建pr)
    - [PR清单](#pr清单)
    - [PR模板](#pr模板)
  - [✅ 测试要求](#-测试要求)
    - [单元测试](#单元测试)
    - [集成测试](#集成测试)
    - [测试覆盖率](#测试覆盖率)
  - [📚 文档贡献](#-文档贡献)
    - [代码文档](#代码文档)
    - [README和指南](#readme和指南)
    - [文档结构](#文档结构)
  - [🎯 贡献领域](#-贡献领域)
    - [我们特别欢迎](#我们特别欢迎)
  - [🏅 贡献者](#-贡献者)
  - [📞 联系方式](#-联系方式)
  - [📜 许可证](#-许可证)

---

## 🌟 行为准则

### 我们的承诺

为了营造一个开放和友好的环境，我们承诺：

- ✅ 尊重不同的观点和经验
- ✅ 优雅地接受建设性批评
- ✅ 关注对社区最有利的事情
- ✅ 对其他社区成员表现同理心

### 不可接受的行为

- ❌ 使用性化的语言或图像
- ❌ 人身攻击或侮辱性评论
- ❌ 骚扰行为
- ❌ 发布他人的私人信息

---

## 🚀 如何贡献

### 报告Bug

发现Bug？请：

1. **检查现有Issues** - 确保没有重复报告
2. **创建详细的Bug报告**，包括：
   - 清晰的标题和描述
   - 重现步骤
   - 预期行为 vs 实际行为
   - 环境信息（Rust版本、OS等）
   - 相关代码片段或错误日志

### 建议新功能

有好想法？请：

1. **先创建Issue讨论** - 在开始编码前
2. **描述清楚**：
   - 功能的目的和使用场景
   - 预期的API设计
   - 可能的实现方案
   - 是否愿意自己实现

### 改进文档

文档永远可以更好！你可以：

- 修正拼写错误
- 改进示例代码
- 添加更多使用场景
- 翻译文档

---

## 🛠️ 开发环境设置

### 前置要求

```bash
# Rust 1.90+
rustc --version
# rustc 1.90.0 或更高

# Cargo
cargo --version
```

### 克隆仓库

```bash
git clone https://github.com/yourusername/c13_reliability.git
cd c13_reliability
```

### 安装依赖

```bash
cargo build
```

### 运行测试

```bash
# 运行所有测试
cargo test

# 运行特定模块的测试
cargo test --test integration_tests

# 查看测试覆盖率（需要安装 tarpaulin）
cargo install cargo-tarpaulin
cargo tarpaulin --out Html
```

### 检查代码

```bash
# 编译检查
cargo check

# 格式化代码
cargo fmt

# Lint检查
cargo clippy -- -D warnings
```

---

## 📝 代码规范

### Rust代码风格

遵循标准Rust代码风格：

```rust
// ✅ 推荐
pub struct CircuitBreaker {
    state: Arc<RwLock<BreakerState>>,
    config: CircuitBreakerConfig,
}

impl CircuitBreaker {
    /// 创建新的熔断器
    /// 
    /// # 示例
    /// 
    /// ```
    /// let cb = CircuitBreaker::new(config);
    /// ```
    pub fn new(config: CircuitBreakerConfig) -> Self {
        Self {
            state: Arc::new(RwLock::new(BreakerState::Closed)),
            config,
        }
    }
}
```

### 命名规范

- **类型**: `PascalCase` (如 `CircuitBreaker`)
- **函数/变量**: `snake_case` (如 `try_acquire`)
- **常量**: `SCREAMING_SNAKE_CASE` (如 `MAX_RETRIES`)
- **生命周期**: 简短描述性 (如 `'a`, `'tx`)

### 注释规范

```rust
/// 简短的一句话描述
///
/// 更详细的说明（可选）
///
/// # 参数
///
/// * `param1` - 参数1的说明
/// * `param2` - 参数2的说明
///
/// # 返回值
///
/// 返回值的说明
///
/// # 示例
///
/// ```
/// let result = function(param1, param2);
/// ```
///
/// # 错误
///
/// 可能的错误情况
pub fn function(param1: Type1, param2: Type2) -> Result<ReturnType> {
    // 实现
}
```

### 错误处理

```rust
// ✅ 使用 Result 类型
pub async fn operation() -> Result<String> {
    let result = some_operation()
        .await
        .context("操作失败的上下文信息")?;
    Ok(result)
}

// ❌ 避免使用 unwrap/expect（除非在测试中）
let value = some_operation().unwrap(); // 不推荐
```

### 异步代码

```rust
// ✅ 使用 async/await
pub async fn async_operation() -> Result<()> {
    let result = external_call().await?;
    process(result).await?;
    Ok(())
}

// ✅ 正确使用 Arc 和锁
let data = Arc::new(RwLock::new(Data::new()));
let data_clone = Arc::clone(&data);
```

---

## 📤 提交规范

### Commit Message格式

```text
<类型>(<范围>): <简短描述>

<详细描述>（可选）

<关联Issue>（可选）
```

### 类型

- `feat`: 新功能
- `fix`: Bug修复
- `docs`: 文档更新
- `style`: 代码格式（不影响功能）
- `refactor`: 重构（不是新功能也不是修复）
- `test`: 测试相关
- `chore`: 构建/工具链相关

### 示例

```bash
# 好的提交消息
feat(circuit_breaker): 添加五状态熔断器支持

实现了 Closed -> Open -> Half-Open -> Recovering -> Closed 的状态转换，
提供更平滑的恢复机制。

Closes #123

# 简单修改
fix(rate_limiter): 修复令牌桶算法的边界条件

docs(readme): 更新快速开始示例
```

---

## 🔄 Pull Request流程

### 1. Fork仓库并创建分支

```bash
# Fork后克隆你的仓库
git clone https://github.com/yourusername/c13_reliability.git

# 创建功能分支
git checkout -b feature/my-feature
```

### 2. 开发和测试

```bash
# 进行修改
# ...

# 运行测试
cargo test

# 检查格式
cargo fmt
cargo clippy
```

### 3. 提交更改

```bash
git add .
git commit -m "feat: 添加新功能"
```

### 4. 推送并创建PR

```bash
git push origin feature/my-feature
```

然后在GitHub上创建Pull Request。

### PR清单

提交PR前，请确保：

- [ ] 所有测试通过
- [ ] 代码符合风格指南
- [ ] 添加了必要的测试
- [ ] 更新了相关文档
- [ ] Commit message符合规范
- [ ] PR描述清晰

### PR模板

```markdown
## 描述
简要描述这个PR的目的

## 变更类型
- [ ] Bug修复
- [ ] 新功能
- [ ] 破坏性变更
- [ ] 文档更新

## 测试
描述如何测试这些变更

## 关联Issue
Closes #(issue编号)
```

---

## ✅ 测试要求

### 单元测试

每个新功能都应该有单元测试：

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_feature() {
        let result = some_function().await;
        assert!(result.is_ok());
    }

    #[test]
    fn test_sync_feature() {
        let result = sync_function();
        assert_eq!(result, expected_value);
    }
}
```

### 集成测试

复杂功能需要集成测试：

```rust
// tests/integration_test.rs
use c13_reliability::prelude::*;

#[tokio::test]
async fn test_complete_flow() {
    // 测试完整流程
}
```

### 测试覆盖率

- 新代码的测试覆盖率应 ≥ 80%
- 核心模块应 ≥ 90%
- 使用 `cargo tarpaulin` 检查覆盖率

---

## 📚 文档贡献

### 代码文档

所有公共API都必须有文档：

```rust
/// 这是一个公共函数的文档
///
/// # 示例
///
/// ```
/// use c13_reliability::module::function;
/// let result = function();
/// ```
pub fn function() {
    // 实现
}
```

### README和指南

- 保持简洁明了
- 提供实际可运行的示例
- 包含常见问题解答

### 文档结构

```text
docs/
├── ARCHITECTURE_DECISIONS.md  # 架构决策记录
├── BEST_PRACTICES.md          # 最佳实践
├── api_reference.md           # API参考
└── architecture.md            # 架构文档
```

---

## 🎯 贡献领域

### 我们特别欢迎

1. **功能增强**
   - 新的分布式算法
   - 额外的设计模式
   - 性能优化

2. **文档改进**
   - 更多使用示例
   - 教程和指南
   - API文档完善

3. **测试增强**
   - 提高测试覆盖率
   - 性能基准测试
   - 压力测试

4. **Bug修复**
   - 修复已知问题
   - 改进错误处理
   - 优化性能

---

## 🏅 贡献者

感谢所有贡献者！

<!-- 贡献者列表将自动生成 -->

---

## 📞 联系方式

有问题？

- GitHub Issues: (待添加)
- 讨论区: (待添加)
- Email: (待添加)

---

## 📜 许可证

通过贡献代码，你同意你的贡献将按照项目的MIT许可证进行授权。

---

**感谢你的贡献！** 🎉

每一个贡献，无论大小，都让这个项目变得更好！
