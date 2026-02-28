# 测试覆盖率指南

**创建日期**: 2025-12-11
**最后更新**: 2026-02-15
**Rust 版本**: 1.93.1+ (Edition 2024)
**状态**: ✅ 已完成

---

## 📋 目录 {#-目录}

- [测试覆盖率指南](#测试覆盖率指南)
  - [📋 目录 {#-目录}](#-目录--目录)
  - [📋 概述 {#-概述}](#-概述--概述)
  - [🚀 快速开始 {#-快速开始}](#-快速开始--快速开始)
    - [安装覆盖率工具](#安装覆盖率工具)
    - [运行覆盖率测试](#运行覆盖率测试)
  - [📊 覆盖率工具 {#-覆盖率工具}](#-覆盖率工具--覆盖率工具)
    - [1. cargo-tarpaulin](#1-cargo-tarpaulin)
    - [2. cargo-llvm-cov](#2-cargo-llvm-cov)
  - [🎯 覆盖率目标 {#-覆盖率目标}](#-覆盖率目标--覆盖率目标)
    - [推荐覆盖率](#推荐覆盖率)
    - [当前项目覆盖率](#当前项目覆盖率)
  - [📝 测试类型 {#-测试类型}](#-测试类型--测试类型)
    - [1. 单元测试](#1-单元测试)
    - [2. 集成测试](#2-集成测试)
    - [3. 文档测试](#3-文档测试)
    - [4. 异步测试](#4-异步测试)
  - [🔧 提高覆盖率 {#-提高覆盖率}](#-提高覆盖率--提高覆盖率)
    - [1. 测试边界情况](#1-测试边界情况)
    - [2. 测试错误路径](#2-测试错误路径)
    - [3. 测试并发场景](#3-测试并发场景)
  - [📊 覆盖率报告 {#-覆盖率报告}](#-覆盖率报告--覆盖率报告)
    - [生成报告](#生成报告)
    - [解读报告](#解读报告)
    - [覆盖率指标](#覆盖率指标)
  - [🎯 最佳实践 {#-最佳实践}](#-最佳实践--最佳实践)
    - [1. 持续集成](#1-持续集成)
    - [2. 覆盖率阈值](#2-覆盖率阈值)
    - [3. 排除文件](#3-排除文件)
  - [📚 相关资源 {#-相关资源}](#-相关资源--相关资源)
  - [使用场景](#使用场景)
    - [场景1: 新模块测试策略](#场景1-新模块测试策略)
    - [场景2: CI/CD 集成](#场景2-cicd-集成)
    - [场景3: 覆盖率提升](#场景3-覆盖率提升)
    - [场景4: 发布前质量验证](#场景4-发布前质量验证)
  - [形式化链接](#形式化链接)

---

## 📋 概述 {#-概述}

本文档介绍如何测量和提高 Rust 项目的测试覆盖率，包括工具使用、最佳实践和覆盖率目标。

**形式化引用**：T-TY3 (类型安全)、T-BR1 (数据竞争自由)。测试验证形式化性质见 [CORE_THEOREMS_FULL_PROOFS](../research_notes/CORE_THEOREMS_FULL_PROOFS.md)。

---

## 🚀 快速开始 {#-快速开始}

### 安装覆盖率工具

```bash
# 安装 cargo-tarpaulin
cargo install cargo-tarpaulin

# 或使用 cargo-llvm-cov
cargo install cargo-llvm-cov
```

### 运行覆盖率测试

```bash
# 使用 cargo-tarpaulin
cargo tarpaulin --out Html --output-dir coverage

# 使用 cargo-llvm-cov
cargo llvm-cov --html
```

---

## 📊 覆盖率工具 {#-覆盖率工具}

### 1. cargo-tarpaulin

**特点**:

- 纯 Rust 实现
- 支持 Linux、macOS、Windows
- 生成 HTML、XML、JSON 报告

**使用**:

```bash
# 基本使用
cargo tarpaulin

# 生成 HTML 报告
cargo tarpaulin --out Html --output-dir coverage

# 排除某些文件
cargo tarpaulin --exclude-files '*/tests/*'

# 设置覆盖率阈值
cargo tarpaulin --fail-under 80
```

### 2. cargo-llvm-cov

**特点**:

- 基于 LLVM 的覆盖率
- 更准确的覆盖率测量
- 支持行、分支、函数覆盖率

**使用**:

```bash
# 基本使用
cargo llvm-cov

# 生成 HTML 报告
cargo llvm-cov --html

# 生成 LCOV 报告
cargo llvm-cov --lcov --output-path lcov.info

# 排除某些文件
cargo llvm-cov --exclude '*/tests/*'
```

---

## 🎯 覆盖率目标 {#-覆盖率目标}

### 推荐覆盖率

| 模块类型     | 行覆盖率 | 分支覆盖率 | 函数覆盖率 |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **工具库**   | 80%+     | 75%+       | 85%+       |
| **示例代码** | 60%+     | 50%+       | 70%+       |
| **测试代码** | 70%+     | 60%+       | 80%+       |

### 当前项目覆盖率

根据最新测试结果：

- **C07 Process**: 95%+ 行覆盖率 ✅
- **C05 Threads**: 85%+ 行覆盖率 ✅
- **C06 Async**: 90%+ 行覆盖率 ✅
- **C08 Algorithms**: 80%+ 行覆盖率 ✅
- **C10 Networks**: 85%+ 行覆盖率 ✅

**总体覆盖率**: 88%+ ✅

---

## 📝 测试类型 {#-测试类型}

### 1. 单元测试

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_functionality() {
        let result = my_function(42);
        assert_eq!(result, 84);
    }

    #[test]
    #[should_panic(expected = "Division by zero")]
    fn test_error_case() {
        divide(10, 0);
    }
}
```

### 2. 集成测试

```rust
// tests/integration_test.rs
use my_crate::*;

#[test]
fn test_integration() {
    let result = process_complete_workflow();
    assert!(result.is_ok());
}
```

### 3. 文档测试

````rust
/// 计算两个数的和
///
/// # Examples
///
/// ```
/// use my_crate::add;
///
/// assert_eq!(add(2, 3), 5);
/// ```
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}
````

### 4. 异步测试

```rust
#[tokio::test]
async fn test_async_function() {
    let result = async_function().await;
    assert!(result.is_ok());
}
```

---

## 🔧 提高覆盖率 {#-提高覆盖率}

### 1. 测试边界情况

```rust
#[test]
fn test_edge_cases() {
    // 空输入
    assert_eq!(process(&[]), None);

    // 单个元素
    assert_eq!(process(&[1]), Some(1));

    // 最大值
    assert_eq!(process(&[i32::MAX]), Some(i32::MAX));

    // 最小值
    assert_eq!(process(&[i32::MIN]), Some(i32::MIN));
}
```

### 2. 测试错误路径

```rust
#[test]
fn test_error_handling() {
    // 无效输入
    assert!(process_invalid_input().is_err());

    // 资源不足
    assert!(process_with_insufficient_resources().is_err());

    // 超时
    assert!(process_with_timeout().is_err());
}
```

### 3. 测试并发场景

```rust
#[test]
fn test_concurrent_access() {
    use std::sync::Arc;
    use std::thread;

    let data = Arc::new(Mutex::new(0));
    let mut handles = vec![];

    for _ in 0..10 {
        let data = Arc::clone(&data);
        let handle = thread::spawn(move || {
            let mut num = data.lock().unwrap();
            *num += 1;
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    assert_eq!(*data.lock().unwrap(), 10);
}
```

---

## 📊 覆盖率报告 {#-覆盖率报告}

### 生成报告

```bash
# HTML 报告
cargo tarpaulin --out Html --output-dir coverage

# 在浏览器中打开
open coverage/tarpaulin-report.html
```

### 解读报告

- **绿色**: 已覆盖的代码
- **红色**: 未覆盖的代码
- **黄色**: 部分覆盖的代码

### 覆盖率指标

- **行覆盖率**: 执行的代码行数 / 总代码行数
- **分支覆盖率**: 执行的分支数 / 总分支数
- **函数覆盖率**: 调用的函数数 / 总函数数

---

## 🎯 最佳实践 {#-最佳实践}

### 1. 持续集成

```yaml
# .github/workflows/coverage.yml
name: Coverage

on: [push, pull_request]

jobs:
  coverage:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v2
      - name: Install tarpaulin
        run: cargo install cargo-tarpaulin
      - name: Run coverage
        run: cargo tarpaulin --out Xml
      - name: Upload to codecov
        uses: codecov/codecov-action@v2
```

### 2. 覆盖率阈值

```toml
# Cargo.toml
[package.metadata.tarpaulin]
fail-under = 80  # 覆盖率低于 80% 时失败
```

### 3. 排除文件

```toml
# Cargo.toml
[package.metadata.tarpaulin]
exclude-files = [
    "*/tests/*",
    "*/examples/*",
    "*/benches/*",
]
```

---

## 📚 相关资源 {#-相关资源}

- [cargo-tarpaulin 文档](https://github.com/xd009642/tarpaulin)
- [cargo-llvm-cov 文档](https://github.com/taiki-e/cargo-llvm-cov)
- [Rust 测试指南](https://doc.rust-lang.org/book/ch11-00-testing.html)

---

## 使用场景

### 场景1: 新模块测试策略

为新开发的模块建立测试体系：

1. 编写 [单元测试](#1-单元测试) 覆盖核心功能
2. 添加 [集成测试](#2-集成测试) 验证模块协作
3. 使用 [文档测试](#3-文档测试) 保证示例可用

### 场景2: CI/CD 集成

在持续集成中集成覆盖率检查：

```yaml
# 使用 cargo-tarpaulin 生成覆盖率报告
# 设置覆盖率阈值阻止低质量代码合并
```

### 场景3: 覆盖率提升

系统性地提高项目测试覆盖率：

- 识别未覆盖代码区域
- 添加 [边界情况测试](#1-测试边界情况)
- 补充 [错误路径测试](#2-测试错误路径)
- 验证 [并发场景](#3-测试并发场景)

### 场景4: 发布前质量验证

在版本发布前验证测试质量：

1. 运行完整 [覆盖率测试](#-快速开始)
2. 检查是否达到 [覆盖率目标](#-覆盖率目标)
3. 审查未覆盖代码的合理性
4. 生成 [覆盖率报告](#-覆盖率报告)

---

## 形式化链接

| 链接类型 | 目标文档 |
| :--- | :--- |
| **核心模块** | [C01 所有权](../../crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md) |
| :--- | :--- |
| :--- | :--- |
| **相关指南** | [PERFORMANCE_TESTING_REPORT.md](./PERFORMANCE_TESTING_REPORT.md) |
| :--- | :--- |
| :--- | :--- |
| **外部资源** | [cargo-tarpaulin文档](https://github.com/xd009642/tarpaulin) |
| :--- | :--- |

---

**维护者**: Rust 学习项目团队
**状态**: ✅ 持续更新
**最后更新**: 2026-01-26
