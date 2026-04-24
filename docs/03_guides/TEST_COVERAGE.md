# 代码覆盖率测试指南

> 本文档对应 Rust 生产级工程实践体系阶段三 —— 代码覆盖率集成。
> 参考: Microsoft Azure 测试策略、Rust Foundation 质量倡议。

---

## 1. 覆盖率工具选择

Rust 生态有两个主流的覆盖率工具：

| 工具 | 引擎 | 优点 | 缺点 |
|-----|------|------|------|
| **cargo-tarpaulin** | LLVM / ptrace | 简单易用，支持 CI 报告 | Linux only (ptrace)，部分场景不稳定 |
| **cargo-llvm-cov** | LLVM profdata | 跨平台，与 rustc 深度集成 | 需要 llvm-tools-preview |

本项目使用 **cargo-tarpaulin** 作为主要工具（CI 已配置），同时支持 **cargo-llvm-cov** 作为本地开发备选。

---

## 2. cargo-tarpaulin 使用

### 安装

```bash
# 通过 cargo 安装
cargo install cargo-tarpaulin --locked

# 验证安装
cargo tarpaulin --version
```

> **注意**: Windows 下 tarpaulin 的 ptrace 引擎不可用，需使用 `--engine llvm`。如果当前环境无法安装，标记为 "待 CI 验证"。

### 基本使用

```bash
# 生成文本报告
cargo tarpaulin --workspace --all-features

# 生成 HTML 报告
cargo tarpaulin --workspace --all-features --out html

# 生成 XML 报告（供 CI 和代码质量平台使用）
cargo tarpaulin --workspace --all-features --out xml

# 使用 LLVM 引擎（跨平台兼容）
cargo tarpaulin --workspace --all-features --engine llvm --out xml

# 排除特定文件/目录
cargo tarpaulin --workspace --exclude-files "*/examples/*" --exclude-files "*/benches/*"

# 设置超时（秒）
cargo tarpaulin --workspace --timeout 300
```

### 输出文件

| 格式 | 文件 | 用途 |
|-----|------|------|
| XML | `cobertura.xml` | Jenkins, Azure DevOps, Codecov |
| HTML | `tarpaulin-report.html` | 本地浏览 |
| JSON | `tarpaulin-report.json` | 自定义分析 |
| LCOV | `lcov.info` | Coveralls, Codecov |

---

## 3. cargo-llvm-cov 使用

### 安装

```bash
# 安装 rustup 组件
rustup component add llvm-tools-preview

# 安装 cargo-llvm-cov
cargo install cargo-llvm-cov --locked
```

### 基本使用

```bash
# 生成 HTML 报告
cargo llvm-cov --workspace --all-features --html

# 生成 LCOV 报告
cargo llvm-cov --workspace --all-features --lcov --output-path lcov.info

# 打开 HTML 报告
cargo llvm-cov --workspace --all-features --html --open
```

---

## 4. CI 集成

本项目 CI 已配置覆盖率生成（`.github/workflows/ci.yml`）：

```yaml
coverage:
  name: Code Coverage
  runs-on: ubuntu-latest
  steps:
    - uses: actions/checkout@v4
    - uses: dtolnay/rust-toolchain@stable
      with:
        toolchain: "1.96.0"
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

### 与 Codecov 集成

```yaml
- name: Upload to Codecov
  uses: codecov/codecov-action@v4
  with:
    files: cobertura.xml
    fail_ci_if_error: false
```

---

## 5. 覆盖率目标

| 等级 | 行覆盖率 | 说明 |
|-----|---------|------|
| 🚧 最低 | 50% | 新功能模块的初始目标 |
| ✅ 良好 | 70% | 核心业务逻辑要求 |
| 🏆 优秀 | 85% | 关键安全模块（如 c10_networks 的安全子模块） |
| 💎 卓越 | 95% | 金融/密码学相关代码 |

### 当前项目状态

运行以下命令查看各 crate 覆盖率：

```bash
cargo tarpaulin --workspace --all-features --engine llvm --out html
# 查看 tarpaulin-report.html
```

---

## 6. 提高覆盖率的策略

1. **先覆盖核心路径**: 优先测试最常用的公共 API
2. **使用 property-based testing**: proptest 可自动生成边界 case
3. **测试错误路径**: 确保错误处理分支也被覆盖
4. **避免测试私有函数**: 通过公共 API 间接测试
5. **关注 unsafe 代码**: 每个 unsafe 块都应被测试覆盖

---

## 7. 常见问题

### Q: tarpaulin 在 Windows 上失败？

A: 使用 `--engine llvm` 标志：

```bash
cargo tarpaulin --engine llvm --out xml
```

### Q: 覆盖率报告包含测试代码本身？

A: 使用 `--exclude-files` 排除测试文件：

```bash
cargo tarpaulin --exclude-files "*/tests/*" --exclude-files "*/benches/*"
```

### Q: async 代码覆盖率不准确？

A: 这是已知问题。尝试：

- 使用 `cargo-llvm-cov` 替代
- 增加测试运行时间

---

## 8. 参考资源

- [cargo-tarpaulin 文档](https://github.com/xd009642/tarpaulin)
- [cargo-llvm-cov 文档](https://github.com/taiki-e/cargo-llvm-cov)
- [Codecov Rust 指南](https://docs.codecov.com/docs/rust)
- [Microsoft 测试覆盖率策略](https://docs.microsoft.com/en-us/azure/devops/pipelines/test/codecoverage-for-pullrequests)
