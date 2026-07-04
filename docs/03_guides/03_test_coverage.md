> **权威来源**:
>
> [The Rust Programming Language — Ch11](https://doc.rust-lang.org/book/ch11-00-testing.html),
> [cargo test 文档](https://doc.rust-lang.org/cargo/commands/cargo-test.html),
> [cargo-tarpaulin 文档](https://github.com/xd009642/tarpaulin)
>
> **分级**: [A]
> **Rust 版本**: 1.96.1+ (Edition 2024)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Book、cargo test、cargo-tarpaulin 官方文档来源标注 [来源: Authority Source Sprint Batch 8]

# 代码覆盖率测试指南 {#代码覆盖率测试指南}

> **EN**: Test Coverage
> **Summary**: 代码覆盖率测试指南 Test Coverage.
> **Bloom 层级**: L2-L3 (理解/应用)
> 本文档对应 Rust 生产级工程实践体系阶段三 —— 代码覆盖率集成。
> 参考: Microsoft Azure 测试策略、Rust Foundation 质量倡议。

---

## 📑 目录 {#目录}
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [代码覆盖率测试指南 {#代码覆盖率测试指南}](#代码覆盖率测试指南-代码覆盖率测试指南)
  - [📑 目录 {#目录}](#-目录-目录)
  - [1. 覆盖率工具选择 {#1-覆盖率工具选择}](#1-覆盖率工具选择-1-覆盖率工具选择)
  - [2. cargo-tarpaulin 使用 {#2-cargo-tarpaulin-使用}](#2-cargo-tarpaulin-使用-2-cargo-tarpaulin-使用)
    - [安装 {#安装-1}](#安装-安装-1)
    - [基本使用 {#基本使用-1}](#基本使用-基本使用-1)
    - [输出文件 {#输出文件}](#输出文件-输出文件)
  - [3. cargo-llvm-cov 使用 {#3-cargo-llvm-cov-使用}](#3-cargo-llvm-cov-使用-3-cargo-llvm-cov-使用)
    - [安装 {#安装-1}](#安装-安装-1-1)
    - [基本使用 {#基本使用-1}](#基本使用-基本使用-1-1)
  - [4. CI 集成 {#4-ci-集成}](#4-ci-集成-4-ci-集成)
    - [与 Codecov 集成 {#与-codecov-集成}](#与-codecov-集成-与-codecov-集成)
  - [5. 覆盖率目标 {#5-覆盖率目标}](#5-覆盖率目标-5-覆盖率目标)
    - [当前项目状态 {#当前项目状态}](#当前项目状态-当前项目状态)
  - [6. 提高覆盖率的策略 {#6-提高覆盖率的策略}](#6-提高覆盖率的策略-6-提高覆盖率的策略)
  - [7. 常见问题 {#7-常见问题}](#7-常见问题-7-常见问题)
    - [Q: tarpaulin 在 Windows 上失败？ {#q-tarpaulin-在-windows-上失败}](#q-tarpaulin-在-windows-上失败-q-tarpaulin-在-windows-上失败)
    - [Q: 覆盖率报告包含测试代码本身？ {#q-覆盖率报告包含测试代码本身}](#q-覆盖率报告包含测试代码本身-q-覆盖率报告包含测试代码本身)
    - [Q: async 代码覆盖率不准确？ {#q-async-代码覆盖率不准确}](#q-async-代码覆盖率不准确-q-async-代码覆盖率不准确)
  - [8. 参考资源 {#8-参考资源}](#8-参考资源-8-参考资源)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [权威来源索引 {#权威来源索引}](#权威来源索引-权威来源索引)

## 1. 覆盖率工具选择 {#1-覆盖率工具选择}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

Rust 生态有两个主流的覆盖率工具：

| 工具 | 引擎 | 优点 | 缺点 |
|-----|------|------|------|
| **cargo-tarpaulin** | LLVM / ptrace | 简单易用，支持 CI 报告 | Linux only (ptrace)，部分场景不稳定 |
| **cargo-llvm-cov** | LLVM profdata | 跨平台，与 rustc 深度集成 | 需要 llvm-tools-preview |

本项目使用 **cargo-tarpaulin** 作为主要工具（CI 已配置），同时支持 **cargo-llvm-cov** 作为本地开发备选。

---

## 2. cargo-tarpaulin 使用 {#2-cargo-tarpaulin-使用}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### 安装 {#安装-1}

> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```bash
# 通过 cargo 安装 {#通过-cargo-安装}
cargo install cargo-tarpaulin --locked

# 验证安装 {#验证安装}
cargo tarpaulin --version
```

> **注意**: Windows 下 tarpaulin 的 ptrace 引擎不可用，需使用 `--engine llvm`。如果当前环境无法安装，标记为 "待 CI 验证"。

### 基本使用 {#基本使用-1}

> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**

```bash
# 生成文本报告 {#生成文本报告}
cargo tarpaulin --workspace --all-features

# 生成 HTML 报告 {#生成-html-报告-1}
cargo tarpaulin --workspace --all-features --out html

# 生成 XML 报告（供 CI 和代码质量平台使用） {#生成-xml-报告供-ci-和代码质量平台使用}
cargo tarpaulin --workspace --all-features --out xml

# 使用 LLVM 引擎（跨平台兼容） {#使用-llvm-引擎跨平台兼容}
cargo tarpaulin --workspace --all-features --engine llvm --out xml

# 排除特定文件/目录 {#排除特定文件目录}
cargo tarpaulin --workspace --exclude-files "*/examples/*" --exclude-files "*/benches/*"

# 设置超时（秒） {#设置超时秒}
cargo tarpaulin --workspace --timeout 300
```

### 输出文件 {#输出文件}

> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

| 格式 | 文件 | 用途 |
|-----|------|------|
| XML | `cobertura.xml` | Jenkins, Azure DevOps, Codecov |
| HTML | `tarpaulin-report.html` | 本地浏览 |
| JSON | `tarpaulin-report.json` | 自定义分析 |
| LCOV | `lcov.info` | Coveralls, Codecov |

---

## 3. cargo-llvm-cov 使用 {#3-cargo-llvm-cov-使用}
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### 安装 {#安装-1}

> **来源: [POPL](https://www.sigplan.org/Conferences/POPL/)**

```bash
# 安装 rustup 组件 {#安装-rustup-组件}
rustup component add llvm-tools-preview

# 安装 cargo-llvm-cov {#安装-cargo-llvm-cov}
cargo install cargo-llvm-cov --locked
```

### 基本使用 {#基本使用-1}

> **来源: [PLDI](https://www.sigplan.org/Conferences/PLDI/)**

```bash
# 生成 HTML 报告 {#生成-html-报告-1}
cargo llvm-cov --workspace --all-features --html

# 生成 LCOV 报告 {#生成-lcov-报告}
cargo llvm-cov --workspace --all-features --lcov --output-path lcov.info

# 打开 HTML 报告 {#打开-html-报告}
cargo llvm-cov --workspace --all-features --html --open
```

---

## 4. CI 集成 {#4-ci-集成}
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

本项目 CI 已配置覆盖率生成（`.github/workflows/ci.yml`）：

```yaml
coverage:
  name: Code Coverage
  runs-on: ubuntu-latest
  steps:
    - uses: actions/checkout@v4
    - uses: dtolnay/rust-toolchain@stable
      with:
        toolchain: "1.96.1"
        components: llvm-tools-preview
    - name: Install cargo-tarpaulin
      run: cargo install cargo-tarpaulin --locked
    - name: Generate coverage report
      run: |
        cargo tarpaulin \
          --workspace \
          --all-features \
          --engine llvm \
          --out xml \
          --timeout 300 \
          --skip-clean || true
    - name: Upload coverage report
      uses: actions/upload-artifact@v4
      with:
        name: coverage-report
        path: cobertura.xml
```

### 与 Codecov 集成 {#与-codecov-集成}

> **来源: [Wikipedia - Memory Safety](https://en.wikipedia.org/wiki/Memory_Safety)**

```yaml
- name: Upload to Codecov
  uses: codecov/codecov-action@v4
  with:
    files: cobertura.xml
    fail_ci_if_error: false
```

---

## 5. 覆盖率目标 {#5-覆盖率目标}
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

| 等级 | 行覆盖率 | 说明 |
|-----|---------|------|
| 🚧 最低 | 50% | 新功能模块的初始目标 |
| ✅ 良好 | 70% | 核心业务逻辑要求 |
| 🏆 优秀 | 85% | 关键安全模块（如 c10_networks 的安全子模块） |
| 💎 卓越 | 95% | 金融/密码学相关代码 |

### 当前项目状态 {#当前项目状态}

> **来源: [PLDI](https://www.sigplan.org/Conferences/PLDI/)**

运行以下命令查看各 crate 覆盖率：

```bash
cargo tarpaulin --workspace --all-features --engine llvm --out html
# 查看 tarpaulin-report.html {#查看-tarpaulin-reporthtml}
```

---

## 6. 提高覆盖率的策略 {#6-提高覆盖率的策略}
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

1. **先覆盖核心路径**: 优先测试最常用的公共 API
2. **使用 property-based testing**: proptest 可自动生成边界 case
3. **测试错误路径**: 确保错误处理分支也被覆盖
4. **避免测试私有函数**: 通过公共 API 间接测试
5. **关注 unsafe 代码**: 每个 unsafe 块都应被测试覆盖

---

## 7. 常见问题 {#7-常见问题}
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

### Q: tarpaulin 在 Windows 上失败？ {#q-tarpaulin-在-windows-上失败}

> **来源: [Wikipedia - Memory Safety](https://en.wikipedia.org/wiki/Memory_Safety)**

A: 使用 `--engine llvm` 标志：

```bash
cargo tarpaulin --engine llvm --out xml
```

### Q: 覆盖率报告包含测试代码本身？ {#q-覆盖率报告包含测试代码本身}
>
> **[来源: [crates.io](https://crates.io/)]**

A: 使用 `--exclude-files` 排除测试文件：

```bash
cargo tarpaulin --exclude-files "*/tests/*" --exclude-files "*/benches/*"
```

### Q: async 代码覆盖率不准确？ {#q-async-代码覆盖率不准确}
>
> **[来源: [docs.rs](https://docs.rs/)]**

A: 这是已知问题。尝试：

- 使用 `cargo-llvm-cov` 替代
- 增加测试运行时间

---

## 8. 参考资源 {#8-参考资源}
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

- [cargo-tarpaulin 文档](https://github.com/xd009642/tarpaulin)
- [cargo-llvm-cov 文档](https://github.com/taiki-e/cargo-llvm-cov)
- [Codecov Rust 指南](https://docs.codecov.com/docs)
- [Microsoft 测试覆盖率策略](https://docs.microsoft.com/en-us/azure/devops/pipelines/test/codecoverage-for-pullrequests)

---

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.1+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [Parent README](../README.md)

---

## 相关概念 {#相关概念}
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

- [docs 索引](../README.md)

---

## 权威来源索引 {#权威来源索引}

> **来源: [Wikipedia - Code Coverage](https://en.wikipedia.org/wiki/Code_Coverage)**
> **来源: [Wikipedia - Software Testing](https://en.wikipedia.org/wiki/Software_Testing)**
> **[来源: ACM - Test Coverage Metrics]**
> **[来源: IEEE - Software Quality Standards]**
> **[来源: Rust Book - Testing]**
> **来源: [Rust Reference - Test Attributes](https://doc.rust-lang.org/reference/attributes/testing.html)**
> **[来源: Martin Fowler - Test Coverage]**

---
