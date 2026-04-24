# cargo-semver-checks 集成指南

> 本文档对应 Rust 生产级工程实践体系阶段三 —— API 兼容性保护。
> 参考: Rust Foundation API 兼容性指南、Microsoft 版本管理规范。

---

## 1. 什么是 cargo-semver-checks？

**cargo-semver-checks** 是一个静态分析工具，用于检测 Rust crate 的公共 API 是否违反了语义化版本控制（Semantic Versioning）规则。

### 为什么需要它？

Rust 生态严格遵循 SemVer：

- **MAJOR**: 破坏性变更（breaking changes）
- **MINOR**: 向后兼容的功能新增
- **PATCH**: 向后兼容的问题修复

但在实际开发中，很容易**无意间**引入破坏性变更：

- 给 `pub struct` 添加字段（除非有 `#[non_exhaustive]`）
- 收窄泛型约束
- 修改 trait 的默认实现行为
- 删除或重命名公共项

### 检测范围

cargo-semver-checks 基于 rustdoc JSON 输出进行分析，可检测：

| 变更类型 | 检测能力 | 违反的 SemVer |
|---------|---------|-------------|
| 删除公共函数/类型 | ✅ | MAJOR |
| 给非 exhaustive struct 添加字段 | ✅ | MAJOR |
| 收窄函数返回类型 | ✅ | MAJOR |
| 放宽函数参数类型 | ✅ | MAJOR |
| trait 新增 required method | ✅ | MAJOR |
| 给 enum 添加 variant | ✅ | MINOR（需 `#[non_exhaustive]`） |
| 修改文档 | ❌ | N/A |
| 行为变更 | ❌ | 需人工审查 |

---

## 2. 安装

```bash
# 安装 cargo-semver-checks
cargo install cargo-semver-checks --locked

# 验证安装
cargo semver-checks --version
```

> **注意**: 如果当前环境无法安装，此步骤标记为 "待 CI 验证"。CI 环境已配置自动安装。

---

## 3. 基本使用

### 检查当前工作目录的 crate

```bash
cd crates/c10_networks
cargo semver-checks
```

### 检查 workspace 中的特定 crate

```bash
cargo semver-checks -p c10_networks
```

### 与 baseline 版本比较

```bash
# 与发布的最新版本比较（从 crates.io 获取）
cargo semver-checks -p c10_networks --baseline-version 0.1.0

# 与 git 标签比较
cargo semver-checks -p c10_networks --baseline-rev v0.1.0

# 与另一个分支比较
cargo semver-checks -p c10_networks --baseline-rev main
```

### 本地开发工作流

```bash
# 在发布前检查
# 1. 确保当前版本号已正确更新
# 2. 运行检查
cargo semver-checks

# 3. 如果报告了问题，评估是否真的是 breaking change
# 4. 如果是 breaking change，更新 MAJOR 版本号
# 5. 如果只是误报，记录原因
```

---

## 4. CI 集成

参见 `.github/workflows/pr-checks.yml` 中的 `semver-checks` 任务：

```yaml
semver-checks:
  name: SemVer Checks
  runs-on: ubuntu-latest
  steps:
    - uses: actions/checkout@v4
      with:
        fetch-depth: 0  # 需要完整 git 历史以比较 baseline

    - uses: dtolnay/rust-toolchain@stable
      with:
        toolchain: "1.96.0"

    - name: Install cargo-semver-checks
      run: cargo install cargo-semver-checks --locked

    - name: Run semver checks
      run: cargo semver-checks --workspace
```

### CI 策略

1. **PR 检查**: 与 `main` 分支比较，阻止无意的 breaking change
2. **发布前检查**: 与上一个发布的版本比较
3. **允许失败模式**: 对于实验性 crate，可设置 `continue-on-error: true`

---

## 5. 处理误报和例外

### 场景 1: 新增字段但已使用 `#[non_exhaustive]`

```rust
#[non_exhaustive]
pub struct Config {
    pub name: String,
    pub new_field: u32, // ✅ 这是 MINOR 变更，semver-checks 不会报告
}
```

### 场景 2: 有意进行 breaking change（MAJOR 版本升级）

```bash
# 在 CI 中允许（因为版本号已更新为 MAJOR）
cargo semver-checks --baseline-version 0.1.0
# 如果当前版本是 1.0.0，则 breaking change 是预期的
```

### 场景 3: 内部 API 被误判

```rust
// 使用 #[doc(hidden)] 标记内部 API
#[doc(hidden)]
pub fn __internal_helper() {} // semver-checks 会忽略此项
```

---

## 6. 最佳实践

1. **给所有公共 struct 添加 `#[non_exhaustive]`**（如果计划未来扩展）
2. **给所有公共 enum 添加 `#[non_exhaustive]`**
3. **使用 sealed trait 模式** 防止外部实现
4. **在 PR 描述中标注 SemVer 影响**
5. **将 semver-checks 作为发布清单的必检项**

---

## 7. 参考资源

- [cargo-semver-checks 文档](https://github.com/obi1kenobi/cargo-semver-checks)
- [Rust API 指南](https://rust-lang.github.io/api-guidelines/)
- [SemVer 规范](https://semver.org/lang/zh-CN/)
