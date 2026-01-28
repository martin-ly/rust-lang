# 贡献指南

感谢您对 C12 WASM 项目的关注！我们欢迎各种形式的贡献。

## 📋 目录

- [贡献指南](#贡献指南)
  - [📋 目录](#-目录)
  - [🚀 开始之前](#-开始之前)
    - [环境准备](#环境准备)
    - [Fork 和克隆](#fork-和克隆)
  - [🤝 如何贡献](#-如何贡献)
    - [贡献类型](#贡献类型)
  - [💻 开发流程](#-开发流程)
    - [1. 创建分支](#1-创建分支)
    - [2. 开发](#2-开发)
    - [3. 提交](#3-提交)
    - [4. 推送](#4-推送)
    - [5. 创建 Pull Request](#5-创建-pull-request)
  - [📝 代码规范](#-代码规范)
    - [Rust 代码规范](#rust-代码规范)
    - [JavaScript 代码规范](#javascript-代码规范)
  - [📬 提交规范](#-提交规范)
    - [提交类型](#提交类型)
    - [提交示例](#提交示例)
    - [提交消息格式](#提交消息格式)
  - [🧪 测试要求](#-测试要求)
    - [1. 单元测试](#1-单元测试)
    - [2. 集成测试](#2-集成测试)
    - [3. 运行测试](#3-运行测试)
    - [4. 基准测试](#4-基准测试)
  - [📖 文档规范](#-文档规范)
    - [1. 代码文档](#1-代码文档)
    - [2. Markdown 文档](#2-markdown-文档)
    - [3. README 更新](#3-readme-更新)
  - [🔍 代码审查](#-代码审查)
    - [审查要点](#审查要点)
  - [🎯 优先级](#-优先级)
    - [高优先级 ⭐⭐⭐](#高优先级-)
    - [中优先级 ⭐⭐](#中优先级-)
    - [低优先级 ⭐](#低优先级-)
  - [📞 获取帮助](#-获取帮助)
  - [📄 许可证](#-许可证)
  - [🙏 感谢](#-感谢)

## 🚀 开始之前

### 环境准备

1. **安装 Rust** (1.90+)

   ```bash
   curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
   ```

2. **安装 WASM 工具链**

   ```bash
   rustup target add wasm32-unknown-unknown
   rustup target add wasm32-wasi
   ```

3. **安装 wasm-pack**

   ```bash
   curl https://rustwasm.github.io/wasm-pack/installer/init.sh -sSf | sh
   ```

4. **安装开发工具**

   ```bash
   # 代码格式化
   rustup component add rustfmt

   # 代码检查
   rustup component add clippy

   # 覆盖率工具（可选）
   cargo install cargo-tarpaulin
   ```

### Fork 和克隆

1. Fork 本项目到您的 GitHub 账户
2. 克隆您的 Fork

   ```bash
   git clone https://github.com/YOUR_USERNAME/rust-lang-learning.git
   cd rust-lang-learning/crates/c12_wasm
   ```

3. 添加上游仓库

```bash
git remote add upstream https://github.com/rust-lang/rust-lang-learning.git
```

## 🤝 如何贡献

### 贡献类型

我们欢迎以下类型的贡献：

1. **Bug 修复** 🐛
   - 修复现有代码中的错误
   - 修复文档中的错误

2. **新功能** ✨
   - 添加新的示例代码
   - 添加新的设计模式实现
   - 添加新的工具函数

3. **文档改进** 📖
   - 改进现有文档
   - 添加新的教程
   - 翻译文档

4. **性能优化** ⚡
   - 优化现有代码性能
   - 减小 WASM 二进制大小
   - 提升编译速度

5. **测试** 🧪
   - 添加单元测试
   - 添加集成测试
   - 添加性能基准测试

## 💻 开发流程

### 1. 创建分支

```bash
# 从 main 分支创建新分支
git checkout -b feature/your-feature-name

# 或者修复 bug
git checkout -b fix/bug-description
```

### 2. 开发

```bash
# 编写代码
vim src/your_file.rs

# 运行测试
cargo test

# 检查代码
cargo clippy

# 格式化代码
cargo fmt
```

### 3. 提交

```bash
# 添加更改
git add .

# 提交（遵循提交规范）
git commit -m "feat: add new feature"
```

### 4. 推送

```bash
# 推送到您的 Fork
git push origin feature/your-feature-name
```

### 5. 创建 Pull Request

1. 访问您的 Fork 在 GitHub 上的页面
2. 点击 "New Pull Request"
3. 填写 PR 描述
4. 等待审核

## 📝 代码规范

### Rust 代码规范

1. **使用 rustfmt 格式化代码**

   ```bash
   cargo fmt
   ```

2. **遵循 Clippy 建议**

   ```bash
   cargo clippy -- -D warnings
   ```

3. **代码注释**

   ````rust
   /// 计算两个数的和
   ///
   /// # 参数
   /// - `a`: 第一个加数
   /// - `b`: 第二个加数
   ///
   /// # 返回值
   /// 返回两个数的和
   ///
   /// # 示例
   /// ```
   /// use c12_wasm::basic_examples::add;
   /// assert_eq!(add(2, 3), 5);
   /// ```
   #[wasm_bindgen]
   pub fn add(a: i32, b: i32) -> i32 {
       a + b
   }
   ````

4. **错误处理**

   ```rust
   // ✅ 好的做法
   #[wasm_bindgen]
   pub fn safe_operation(x: i32) -> Result<i32, JsValue> {
       if x < 0 {
           Err(JsValue::from_str("x must be positive"))
       } else {
           Ok(x * 2)
       }
   }

   // ❌ 不好的做法
   #[wasm_bindgen]
   pub fn unsafe_operation(x: i32) -> i32 {
       assert!(x >= 0); // 可能 panic
       x * 2
   }
   ```

5. **性能考虑**

   ```rust
   // ✅ 好的做法：避免不必要的克隆
   #[wasm_bindgen]
   pub fn process(data: &[i32]) -> Vec<i32> {
       data.iter().filter(|&&x| x > 0).copied().collect()
   }

   // ❌ 不好的做法：不必要的克隆
   #[wasm_bindgen]
   pub fn process_bad(data: Vec<i32>) -> Vec<i32> {
       data.clone().into_iter().filter(|&x| x > 0).collect()
   }
   ```

### JavaScript 代码规范

1. **使用现代 JavaScript**

   ```javascript
   // ✅ 使用 async/await
   async function loadWasm() {
     const module = await init()
     return module
   }

   // ❌ 避免回调地狱
   init().then(module => {
     // ...
   })
   ```

2. **错误处理**

   ```javascript
   // ✅ 处理错误
   try {
     const result = wasmModule.risky_operation()
     console.log(result)
   } catch (err) {
     console.error("Error:", err)
   }
   ```

## 📬 提交规范

使用 [Conventional Commits](https://www.conventionalcommits.org/) 规范：

### 提交类型

- `feat`: 新功能
- `fix`: Bug 修复
- `docs`: 文档更新
- `style`: 代码格式（不影响代码运行）
- `refactor`: 重构
- `test`: 测试相关
- `chore`: 构建过程或辅助工具的变动
- `perf`: 性能优化

### 提交示例

```bash
# 新功能
git commit -m "feat: add bubble sort example"

# Bug 修复
git commit -m "fix: correct palindrome check logic"

# 文档更新
git commit -m "docs: update WASM compilation guide"

# 性能优化
git commit -m "perf: optimize array processing with SIMD"

# 重构
git commit -m "refactor: simplify error handling in file operations"
```

### 提交消息格式

```text
<type>(<scope>): <subject>

<body>

<footer>
```

示例：

```text
feat(examples): add WebSocket communication example

Add a comprehensive WebSocket example demonstrating:
- Connection establishment
- Message sending/receiving
- Error handling
- Connection cleanup

Closes #123
```

## 🧪 测试要求

### 1. 单元测试

每个新功能都应该有相应的单元测试：

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_add() {
        assert_eq!(add(2, 3), 5);
        assert_eq!(add(-1, 1), 0);
        assert_eq!(add(0, 0), 0);
    }
}
```

### 2. 集成测试

复杂功能应该有集成测试：

```rust
// tests/integration_test.rs
use c12_wasm::*;

#[test]
fn test_complex_workflow() {
    // 测试完整的工作流程
}
```

### 3. 运行测试

```bash
# 运行所有测试
cargo test

# 运行特定测试
cargo test test_add

# 显示输出
cargo test -- --nocapture

# WASI 测试
cargo test --target wasm32-wasi
```

### 4. 基准测试

性能相关的改进应该包含基准测试：

```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn bench_my_function(c: &mut Criterion) {
    c.bench_function("my_function", |b| {
        b.iter(|| my_function(black_box(100)));
    });
}

criterion_group!(benches, bench_my_function);
criterion_main!(benches);
```

## 📖 文档规范

### 1. 代码文档

所有公共 API 必须有文档注释：

````rust
/// 计算数组的平均值
///
/// # 参数
/// - `numbers`: 数字数组
///
/// # 返回值
/// 返回平均值，如果数组为空则返回 0.0
///
/// # 性能说明
/// 时间复杂度 O(n)，空间复杂度 O(1)
///
/// # 示例
/// ```
/// use c12_wasm::array_examples::calculate_average;
/// let avg = calculate_average(&[1.0, 2.0, 3.0]);
/// assert_eq!(avg, 2.0);
/// ```
#[wasm_bindgen]
pub fn calculate_average(numbers: &[f64]) -> f64 {
    // 实现...
}
````

### 2. Markdown 文档

文档应该包含：

- 清晰的标题层次
- 代码示例
- 使用说明
- 常见问题

示例：

```markdown
# 功能名称

> 简短描述

## 概述

详细描述...

## 使用方法

\`\`\`rust
// 代码示例
\`\`\`

## 常见问题

### Q: 问题？

**A**: 答案
```

### 3. README 更新

如果添加了新功能，更新相关的 README：

- 主 README.md
- examples/README.md
- tests/README.md
- demo/README.md

## 🔍 代码审查

### 审查要点

1. **功能正确性**
   - 代码是否按预期工作？
   - 边界情况是否处理？

2. **代码质量**
   - 代码是否清晰易读？
   - 是否遵循项目规范？

3. **测试覆盖**
   - 是否有足够的测试？
   - 测试是否有意义？

4. **文档完整性**
   - 文档是否清晰？
   - 示例是否正确？

5. **性能影响**
   - 是否有性能回归？
   - 是否有优化空间？

## 🎯 优先级

我们特别欢迎以下贡献：

### 高优先级 ⭐⭐⭐

- Bug 修复
- 文档改进
- 测试覆盖率提升
- 性能优化

### 中优先级 ⭐⭐

- 新的示例代码
- 新的设计模式
- 工具脚本

### 低优先级 ⭐

- 代码重构
- 美化改进

## 📞 获取帮助

如果您有任何问题：

1. **查看文档**: 先查看项目文档
2. **搜索 Issues**: 看看是否已有人遇到类似问题
3. **提问**: 在 GitHub Discussions 中提问
4. **联系维护者**: 通过 Issue 联系维护者

## 📄 许可证

通过贡献代码，您同意您的贡献将按照项目的 MIT/Apache-2.0 双许可证进行授权。

## 🙏 感谢

感谢您的贡献！每一个贡献都让这个项目变得更好。

---

**最后更新**: 2025-10-30
**维护者**: Documentation Team
