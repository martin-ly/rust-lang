# 贡献指南 (Contributing Guide)

> **欢迎贡献！** 本项目欢迎各种形式的贡献，无论大小。

**文档语言**: 中文为主，英文为辅  
**最后更新**: 2025-10-19  
**维护团队**: Rust 学习社区

---

## 📋 目录

- [贡献指南 (Contributing Guide)](#贡献指南-contributing-guide)
  - [📋 目录](#-目录)
  - [🤝 行为准则](#-行为准则)
    - [我们的承诺](#我们的承诺)
    - [我们的标准](#我们的标准)
  - [💡 如何贡献](#-如何贡献)
    - [快速开始](#快速开始)
  - [🎯 贡献类型](#-贡献类型)
    - [1. 代码贡献](#1-代码贡献)
      - [新功能](#新功能)
      - [Bug 修复](#bug-修复)
      - [性能优化](#性能优化)
    - [2. 文档贡献](#2-文档贡献)
      - [改进现有文档](#改进现有文档)
      - [新增文档](#新增文档)
      - [翻译](#翻译)
    - [3. 测试贡献](#3-测试贡献)
      - [单元测试](#单元测试)
      - [集成测试](#集成测试)
      - [基准测试](#基准测试)
    - [4. 其他贡献](#4-其他贡献)
  - [🔧 开发流程](#-开发流程)
    - [环境准备](#环境准备)
    - [开发循环](#开发循环)
  - [📝 代码规范](#-代码规范)
    - [Rust 代码风格](#rust-代码风格)
      - [遵循官方规范](#遵循官方规范)
      - [命名约定](#命名约定)
      - [文档注释](#文档注释)
      - [错误处理](#错误处理)
    - [代码组织](#代码组织)
  - [📖 文档规范](#-文档规范)
    - [文档结构](#文档结构)
    - [文档模板](#文档模板)
      - [主索引 (00\_MASTER\_INDEX.md)](#主索引-00_master_indexmd)
      - [FAQ](#faq)
      - [术语表 (Glossary)](#术语表-glossary)
    - [Markdown 规范](#markdown-规范)
  - [🔍 提交规范](#-提交规范)
    - [Commit Message 格式](#commit-message-格式)
      - [Type 类型](#type-类型)
      - [示例](#示例)
  - [🐛 问题反馈](#-问题反馈)
    - [报告 Bug](#报告-bug)
    - [功能建议](#功能建议)
  - [✅ Pull Request 流程](#-pull-request-流程)
    - [PR 检查清单](#pr-检查清单)
    - [PR 模板](#pr-模板)
    - [审核流程](#审核流程)
  - [🏆 贡献者认可](#-贡献者认可)
    - [Hall of Fame](#hall-of-fame)
    - [贡献统计](#贡献统计)
  - [📞 获取帮助](#-获取帮助)
    - [遇到问题？](#遇到问题)
    - [联系方式](#联系方式)
  - [📄 许可证](#-许可证)
  - [🙏 致谢](#-致谢)

---

## 🤝 行为准则

### 我们的承诺

为了营造一个开放和友好的环境，我们承诺：

- ✅ 尊重不同的观点和经验
- ✅ 接受建设性的批评
- ✅ 关注对社区最有利的事情
- ✅ 对其他社区成员表示同情

### 我们的标准

**鼓励的行为**:

- 使用友好和包容的语言
- 尊重不同的观点和经验
- 优雅地接受建设性批评
- 关注对社区最有利的事情
- 对其他社区成员表示同情

**不可接受的行为**:

- 使用性化的语言或图像
- 发表侮辱性/贬损性评论
- 公开或私下骚扰
- 未经许可发布他人的私人信息
- 其他可能被认为不专业的行为

---

## 💡 如何贡献

### 快速开始

1. **Fork 项目**

   ```bash
   # 在 GitHub 上 Fork 项目
   # 然后克隆你的 Fork
   git clone https://github.com/YOUR_USERNAME/rust-lang.git
   cd rust-lang
   ```

2. **创建分支**

   ```bash
   # 创建并切换到新分支
   git checkout -b feature/your-feature-name
   
   # 或修复 Bug
   git checkout -b fix/your-bug-fix
   ```

3. **进行修改**

   - 编辑文件
   - 添加测试
   - 更新文档

4. **测试修改**

   ```bash
   # 运行测试
   cargo test --workspace
   
   # 运行 Clippy
   cargo clippy --workspace -- -D warnings
   
   # 格式化代码
   cargo fmt --all
   ```

5. **提交改动**

   ```bash
   git add .
   git commit -m "feat: 添加新功能"
   ```

6. **推送分支**

   ```bash
   git push origin feature/your-feature-name
   ```

7. **创建 Pull Request**

   - 访问你的 Fork 页面
   - 点击 "New Pull Request"
   - 填写 PR 描述
   - 等待审核

---

## 🎯 贡献类型

### 1. 代码贡献

#### 新功能

- 在 Issue 中讨论新功能
- 等待维护者反馈
- 实现功能并添加测试
- 更新相关文档

#### Bug 修复

- 搜索是否已有相关 Issue
- 如果没有，创建新 Issue
- 实现修复并添加测试
- 引用 Issue 编号

#### 性能优化

- 提供基准测试数据
- 说明优化方案
- 保持功能一致性
- 添加性能测试

### 2. 文档贡献

#### 改进现有文档

- 修正错别字
- 完善说明
- 添加示例
- 改进格式

#### 新增文档

- 遵循文档标准（见下文）
- 添加到相应模块
- 更新主索引
- 添加交叉引用

#### 翻译

- 保持术语一致
- 遵循原文结构
- 标注翻译版本

### 3. 测试贡献

#### 单元测试

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_feature() {
        // 测试代码
    }
}
```

#### 集成测试

```rust
// tests/integration_test.rs
#[test]
fn test_integration() {
    // 测试代码
}
```

#### 基准测试

```rust
// benches/benchmark.rs
use criterion::{criterion_group, criterion_main, Criterion};

fn benchmark(c: &mut Criterion) {
    c.bench_function("my_function", |b| {
        b.iter(|| {
            // 被测代码
        });
    });
}

criterion_group!(benches, benchmark);
criterion_main!(benches);
```

### 4. 其他贡献

- 报告 Bug
- 提出功能建议
- 参与讨论
- 推广项目
- 分享经验

---

## 🔧 开发流程

### 环境准备

```bash
# 安装 Rust (推荐最新稳定版)
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

# 安装开发工具
rustup component add rustfmt clippy

# 克隆项目
git clone https://github.com/YOUR_USERNAME/rust-lang.git
cd rust-lang

# 构建项目
cargo build --workspace
```

### 开发循环

1. **编写代码**

   ```bash
   # 编辑文件
   code crates/c01_ownership_borrow_scope/src/lib.rs
   ```

2. **运行测试**

   ```bash
   # 运行所有测试
   cargo test --workspace
   
   # 运行特定模块测试
   cargo test --package c01_ownership_borrow_scope
   
   # 运行特定测试
   cargo test test_name
   ```

3. **代码检查**

   ```bash
   # Clippy 检查
   cargo clippy --workspace -- -D warnings
   
   # 格式化检查
   cargo fmt --all -- --check
   ```

4. **格式化代码**

   ```bash
   # 自动格式化
   cargo fmt --all
   ```

5. **构建文档**

   ```bash
   # 构建文档
   cargo doc --workspace --no-deps
   
   # 打开文档
   cargo doc --workspace --no-deps --open
   ```

---

## 📝 代码规范

### Rust 代码风格

#### 遵循官方规范

- 使用 `cargo fmt` 格式化代码
- 遵循 [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/)
- 通过 `cargo clippy` 检查

#### 命名约定

```rust
// 模块：snake_case
mod my_module;

// 类型：PascalCase
struct MyStruct;
enum MyEnum;
trait MyTrait;

// 函数：snake_case
fn my_function() {}

// 常量：SCREAMING_SNAKE_CASE
const MAX_SIZE: usize = 100;

// 静态变量：SCREAMING_SNAKE_CASE
static GLOBAL_VAR: i32 = 42;

// 生命周期：单字母小写
fn foo<'a>(x: &'a str) {}
```

#### 文档注释

```rust
/// 函数简短描述
///
/// 详细说明功能、参数和返回值
///
/// # Examples
///
/// ```
/// let result = my_function(42);
/// assert_eq!(result, 84);
/// ```
///
/// # Panics
///
/// 说明何时会 panic
///
/// # Errors
///
/// 说明可能的错误
pub fn my_function(x: i32) -> i32 {
    x * 2
}
```

#### 错误处理

```rust
// ✅ 推荐：使用 Result
fn parse_config(path: &str) -> Result<Config, Error> {
    // ...
}

// ✅ 推荐：使用 ?运算符
fn process() -> Result<(), Error> {
    let config = parse_config("config.toml")?;
    // ...
    Ok(())
}

// ❌ 避免：过度使用 unwrap
let config = parse_config("config.toml").unwrap(); // 不推荐
```

### 代码组织

```rust
// 1. 外部 crate 导入
use std::collections::HashMap;
use tokio::runtime::Runtime;

// 2. 内部模块导入
use crate::module::Type;

// 3. 类型定义
pub struct MyStruct {
    // 字段
}

// 4. 实现
impl MyStruct {
    // 方法
}

// 5. Trait 实现
impl MyTrait for MyStruct {
    // Trait 方法
}

// 6. 测试
#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_something() {
        // 测试代码
    }
}
```

---

## 📖 文档规范

### 文档结构

每个模块应包含：

```text
crates/module_name/
├── docs/
│   ├── 00_MASTER_INDEX.md  # 主索引（必需）
│   ├── FAQ.md              # 常见问题（必需）
│   ├── Glossary.md         # 术语表（必需）
│   └── ...                 # 其他文档
├── examples/               # 示例代码
├── src/                    # 源代码
├── tests/                  # 测试
└── README.md              # 模块说明
```

### 文档模板

#### 主索引 (00_MASTER_INDEX.md)

```markdown
# 模块名称: 主索引 (Master Index)

> **文档定位**: 简短描述
> **使用方式**: 使用说明
> **相关文档**: [README](../README.md) | [FAQ](./FAQ.md)

**最后更新**: YYYY-MM-DD
**适用版本**: Rust X.Y+
**文档类型**: 📚 导航索引

---

## 📋 快速导航

...

## 🏗️ 核心内容结构

...
```

#### FAQ

```markdown
# 模块名称: 常见问题解答 (FAQ)

> **文档定位**: 常见问题快速解答
> **使用方式**: 遇到问题时快速查找
> **相关文档**: [主索引](./00_MASTER_INDEX.md)

---

## Q1: 问题标题？

**A**: 答案内容

**示例**:

\`\`\`rust
// 代码示例
\`\`\`

**相关**: [链接](./other.md)

---

```

#### 术语表 (Glossary)

```markdown
# 模块名称: 术语表 (Glossary)

> **文档定位**: 核心术语快速参考
> **使用方式**: 通过术语索引快速查找定义

---

## 术语名称 (Term Name)

**定义**: 术语定义

**示例**:

\`\`\`rust
// 代码示例
\`\`\`

**相关**: [链接](./other.md)

---

```

### Markdown 规范

- 使用 ATX 风格标题 (`#`)
- 代码块指定语言
- 列表前后有空行
- 表格对齐
- 链接使用相对路径

---

## 🔍 提交规范

### Commit Message 格式

```text
<type>(<scope>): <subject>

<body>

<footer>
```

#### Type 类型

- `feat`: 新功能
- `fix`: Bug 修复
- `docs`: 文档修改
- `style`: 代码格式（不影响功能）
- `refactor`: 重构（不是新功能也不是修复）
- `test`: 添加测试
- `chore`: 构建过程或辅助工具的变动
- `perf`: 性能优化

#### 示例

```bash
# 新功能
git commit -m "feat(c01): 添加生命周期示例"

# Bug 修复
git commit -m "fix(c06): 修复异步示例的编译错误"

# 文档
git commit -m "docs(readme): 更新快速开始指南"

# 带详细说明
git commit -m "feat(c10): 添加 WebSocket 客户端示例

添加了一个完整的 WebSocket 客户端示例，
展示如何连接服务器并收发消息。

Closes #123"
```

---

## 🐛 问题反馈

### 报告 Bug

创建 Issue 时请包含：

1. **Bug 描述**: 清晰描述问题
2. **复现步骤**: 详细的复现步骤
3. **预期行为**: 应该发生什么
4. **实际行为**: 实际发生了什么
5. **环境信息**:
   - Rust 版本: `rustc --version`
   - 操作系统
   - 相关依赖版本

**Issue 模板**:

```markdown
## Bug 描述
简短描述问题

## 复现步骤
1. 步骤一
2. 步骤二
3. 步骤三

## 预期行为
应该...

## 实际行为
实际...

## 环境信息
- Rust 版本: 
- 操作系统: 
- 其他依赖:

## 附加信息
其他相关信息
```

### 功能建议

创建 Issue 时请包含：

1. **功能描述**: 清晰描述建议的功能
2. **使用场景**: 为什么需要这个功能
3. **建议方案**: 如何实现（可选）
4. **替代方案**: 其他可能的方案（可选）

---

## ✅ Pull Request 流程

### PR 检查清单

提交 PR 前请确认：

- [ ] 代码通过所有测试 (`cargo test --workspace`)
- [ ] 代码通过 Clippy 检查 (`cargo clippy --workspace`)
- [ ] 代码已格式化 (`cargo fmt --all`)
- [ ] 添加了必要的测试
- [ ] 更新了相关文档
- [ ] PR 标题清晰描述改动
- [ ] PR 描述包含详细信息

### PR 模板

```markdown
## 改动描述
简短描述本次改动

## 改动类型
- [ ] 新功能
- [ ] Bug 修复
- [ ] 文档更新
- [ ] 重构
- [ ] 性能优化
- [ ] 其他

## 相关 Issue
Closes #issue_number

## 测试说明
如何测试这些改动

## 截图（如适用）
添加截图说明

## 检查清单
- [ ] 通过所有测试
- [ ] 通过 Clippy 检查
- [ ] 代码已格式化
- [ ] 添加了测试
- [ ] 更新了文档
```

### 审核流程

1. **自动检查**: CI 运行测试和检查
2. **代码审核**: 维护者审核代码
3. **修改请求**: 根据反馈修改
4. **批准合并**: 审核通过后合并

---

## 🏆 贡献者认可

### Hall of Fame

我们会在以下地方认可贡献者：

- 项目 README
- 发布说明
- 贡献者页面

### 贡献统计

- 定期更新贡献者列表
- 标注重要贡献
- 展示贡献历史

---

## 📞 获取帮助

### 遇到问题？

1. **查看文档**: 先查看相关模块文档
2. **搜索 Issues**: 看是否已有类似问题
3. **创建 Issue**: 描述你的问题
4. **讨论区**: 参与技术讨论

### 联系方式

- **GitHub Issues**: 技术问题和 Bug 报告
- **GitHub Discussions**: 一般性讨论
- **Email**: [维护者邮箱]

---

## 📄 许可证

通过贡献代码，你同意你的贡献将在 MIT 许可证下授权。

---

## 🙏 致谢

感谢每一位贡献者！你们的贡献让这个项目变得更好。

**特别感谢**:

- 所有代码贡献者
- 文档改进者
- Bug 报告者
- 功能建议者

---

**准备好开始贡献了吗？** 🚀

查看 [Good First Issues](https://github.com/your-repo/issues?q=is%3Aissue+is%3Aopen+label%3A%22good+first+issue%22) 开始你的第一个贡献！

**最后更新**: 2025-10-19  
**维护团队**: Rust 学习社区  
**版本**: v1.0
