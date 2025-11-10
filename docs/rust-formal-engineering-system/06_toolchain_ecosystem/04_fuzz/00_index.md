# 模糊测试（Fuzzing）索引

> **创建日期**: 2025-10-31
> **最后更新**: 2025-11-10
> **Rust 版本**: 1.91.0 (Edition 2024) ✅
> **状态**: 已完善 ✅

---

## 📊 目录

- [模糊测试（Fuzzing）索引](#模糊测试fuzzing索引)
  - [📊 目录](#-目录)
  - [🎯 目的](#-目的)
    - [核心价值](#核心价值)
  - [📚 核心工具](#-核心工具)
    - [1. cargo-fuzz（LibFuzzer）](#1-cargo-fuzzlibfuzzer)
    - [2. AFL++（American Fuzzy Lop）](#2-aflamerican-fuzzy-lop)
    - [3. 其他工具](#3-其他工具)
  - [💻 常用命令](#-常用命令)
    - [cargo-fuzz](#cargo-fuzz)
    - [AFL++](#afl)
  - [🚀 快速开始](#-快速开始)
    - [cargo-fuzz](#cargo-fuzz-1)
    - [AFL++](#afl-1)
  - [🔄 CI 集成建议](#-ci-集成建议)
    - [GitHub Actions](#github-actions)
    - [建议策略](#建议策略)
  - [✨ 最佳实践](#-最佳实践)
    - [开发流程](#开发流程)
    - [配置策略](#配置策略)
  - [🔗 相关索引](#-相关索引)
  - [🧭 导航](#-导航)

## 🎯 目的

本模块通过 Fuzz 提升健壮性，覆盖边界与异常路径，提供全面的模糊测试工具使用指南。所有内容均基于 Rust 1.91.0 和当前最佳实践。

### 核心价值

- **模糊测试**: 专注于 Rust 模糊测试最佳实践
- **最佳实践**: 基于 Rust 社区最新模糊测试实践
- **完整覆盖**: 涵盖 LibFuzzer、AFL++ 等核心工具
- **易于理解**: 提供详细的模糊测试说明和代码示例

## 📚 核心工具

### 1. cargo-fuzz（LibFuzzer）

**推荐工具**: `cargo-fuzz`, `libfuzzer-sys`

- **LibFuzzer 接入**: LibFuzzer 集成、模糊测试目标
- **代码覆盖**: 代码覆盖分析、覆盖率报告
- **崩溃检测**: 崩溃检测、崩溃复现
- **字典支持**: 字典文件、种子文件

**相关资源**:

- [cargo-fuzz 文档](https://github.com/rust-fuzz/cargo-fuzz)
- [libfuzzer-sys 文档](https://docs.rs/libfuzzer-sys/)
- [LibFuzzer 文档](https://llvm.org/docs/LibFuzzer.html)

### 2. AFL++（American Fuzzy Lop）

**推荐工具**: `afl++`, `afl.rs`

- **进程级模糊**: 进程级模糊测试、文件输入
- **代码覆盖**: 代码覆盖分析、覆盖率报告
- **崩溃检测**: 崩溃检测、崩溃复现
- **字典支持**: 字典文件、种子文件

**相关资源**:

- [AFL++ 文档](https://github.com/AFLplusplus/AFLplusplus)
- [afl.rs 文档](https://docs.rs/afl/)
- [AFL++ 用户指南](https://github.com/AFLplusplus/AFLplusplus/blob/stable/docs/README.md)

### 3. 其他工具

**推荐工具**: `honggfuzz`, `proptest`, `quickcheck`

- **Honggfuzz**: 进程级模糊测试、代码覆盖
- **属性测试**: 属性测试、随机测试生成
- **快速检查**: 快速检查、测试用例生成

**相关资源**:

- [honggfuzz 文档](https://github.com/google/honggfuzz)
- [proptest 文档](https://docs.rs/proptest/)
- [quickcheck 文档](https://docs.rs/quickcheck/)

## 💻 常用命令

### cargo-fuzz

```bash
# 安装 cargo-fuzz
cargo install cargo-fuzz

# 初始化模糊测试
cargo fuzz init

# 添加模糊测试目标
cargo fuzz add fuzz_target_1

# 运行模糊测试
cargo fuzz run fuzz_target_1

# 运行指定时间
cargo fuzz run fuzz_target_1 -- -max_total_time=300
```

### AFL++

```bash
# 安装 AFL++
# Linux
sudo apt install afl++
# macOS
brew install afl-fuzz

# 编译模糊测试目标
afl-clang-fast -o fuzz_target fuzz_target.c

# 运行模糊测试
afl-fuzz -i input_dir -o output_dir ./fuzz_target
```

## 🚀 快速开始

### cargo-fuzz

```bash
# 安装 cargo-fuzz
cargo install cargo-fuzz

# 初始化模糊测试
cargo fuzz init

# 添加模糊测试目标
cargo fuzz add fuzz_target_1

# 运行模糊测试
cargo fuzz run fuzz_target_1
```

### AFL++

```bash
# 安装 AFL++
# Linux
sudo apt install afl++
# macOS
brew install afl-fuzz

# 编译模糊测试目标
afl-clang-fast -o fuzz_target fuzz_target.c

# 运行模糊测试
afl-fuzz -i input_dir -o output_dir ./fuzz_target
```

## 🔄 CI 集成建议

### GitHub Actions

```yaml
name: Fuzz Test
on: [push, pull_request]
jobs:
  fuzz:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - name: Install Rust
        uses: actions-rs/toolchain@v1
        with:
          toolchain: stable
      - name: Install cargo-fuzz
        run: cargo install cargo-fuzz
      - name: Run Fuzz
        run: cargo fuzz run fuzz_target_1 -- -max_total_time=300
```

### 建议策略

- **解析/编解码库**: 对解析/编解码库添加夜间 fuzz job（限定运行时间）
- **崩溃样例**: 将崩溃样例持久化到工件或仓库字典目录
- **优先模块**: 为解析/编解码/状态机等模块优先添加 fuzz 目标
- **字典维护**: 维护字典与最小崩溃样例，纳入 CI 轮转

## ✨ 最佳实践

### 开发流程

- **提交前检查**: 使用 pre-commit hook 自动运行 fuzz 测试
- **代码审查**: 将 fuzz 测试结果纳入代码审查标准
- **持续集成**: 在 CI 中运行 fuzz 测试（限定运行时间）
- **渐进式采用**: 逐步为关键模块添加 fuzz 目标

### 配置策略

- **项目初期**: 为基础模块添加 fuzz 目标
- **项目成熟**: 为关键模块添加 fuzz 目标
- **团队规范**: 统一 fuzz 配置和测试策略
- **定期更新**: 保持 fuzz 工具版本更新

---

## 🔗 相关索引

- **测试框架**: [`../04_testing_frameworks/00_index.md`](../04_testing_frameworks/00_index.md) - 测试工具
- **质量保障**: [`../../10_quality_assurance/00_index.md`](../../10_quality_assurance/00_index.md) - 质量保障标准
- **代码分析**: [`../05_code_analysis/00_index.md`](../05_code_analysis/00_index.md) - 动态分析工具

---

## 🧭 导航

- **返回工具链生态**: [`../00_index.md`](../00_index.md)
- **测试框架**: [`../04_testing_frameworks/00_index.md`](../04_testing_frameworks/00_index.md)
- **质量保障**: [`../../10_quality_assurance/00_index.md`](../../10_quality_assurance/00_index.md)
- **返回项目根**: [`../../README.md`](../../README.md)

---

**别名与规范说明**:

- 本页为 Fuzz 专题页，编号为 `04_fuzz`。与"04_testing_frameworks"编号冲突已通过规范入口化处理：
  - 测试框架规范入口: [`../04_testing_frameworks/00_index.md`](../04_testing_frameworks/00_index.md)
  - Fuzz 作为质量保障的补充手段，相关综述也可在: [`../../10_quality_assurance/00_index.md`](../../10_quality_assurance/00_index.md)

---

**最后更新**: 2025-11-10
**维护者**: 项目维护者
**状态**: 已完善 ✅
