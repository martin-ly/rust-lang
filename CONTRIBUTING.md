# 贡献指南

> **最后更新**: 2026-04-10
> **维护者**: Rust 学习项目团队

---

## 感谢你的贡献

感谢你对 Rust 学习项目的关注！

---

## 贡献类型

| 类型 | 描述 | 示例 |
|------|------|------|
| 文档 | 改进文档 | 修正错误、补充说明 |
| 代码 | 功能实现 | 新示例、修复 bug |
| 测试 | 测试覆盖 | 单元测试、集成测试 |
| 设计 | 架构改进 | 重构、模式应用 |

---

## 贡献路径

### 入门贡献

适合刚学完 C01-C03 的贡献者:

- 修正文档错别字
- 更新过时链接
- 补充速查卡反例

### 模块贡献

适合已掌握对应模块的贡献者:

- 为特定模块补充示例
- 完善 FAQ
- 添加练习题

### 形式化贡献

适合有形式化背景的贡献者:

- 补充证明
- 形式化分析
- 类型论推导

### 维护贡献

适合长期使用者:

- 认领模块维护
- 参与版本发布追踪
- 代码审查

---

## 开发环境

参见 [DEVELOPMENT.md](./DEVELOPMENT.md) 设置开发环境。

快速开始:

```bash
# 克隆项目
git clone <repo-url>
cd rust-lang

# 安装工具链
rustup show

# 构建项目
cargo build --workspace

# 运行测试
cargo test --workspace
```

---

## 工作流程

### 1. Fork 项目

在 GitHub 上 fork 仓库到你的账号。

### 2. 克隆你的 fork

```bash
git clone https://github.com/YOUR_USERNAME/rust-lang.git
cd rust-lang
```

### 3. 添加上游仓库

```bash
git remote add upstream https://github.com/original/rust-lang.git
```

### 4. 创建分支

```bash
git checkout -b feature/my-feature
# 或
git checkout -b fix/bug-fix
```

### 5. 开发

- 编写代码
- 添加测试
- 更新文档

### 6. 提交前检查

```bash
# 格式化代码
cargo fmt

# 运行 clippy
cargo clippy --workspace --all-targets

# 运行测试
cargo test --workspace

# 检查文档
cargo doc --workspace
```

### 7. 提交更改

```bash
git add .
git commit -m "feat: 添加新功能描述"
```

### 8. 推送到你的 fork

```bash
git push origin feature/my-feature
```

### 9. 创建 Pull Request

在 GitHub 上创建 PR，描述你的更改。

---

## 代码规范

### 格式化

使用 rustfmt:

```bash
cargo fmt
```

### Lint

使用 clippy:

```bash
cargo clippy --workspace --all-targets -- -D warnings
```

### 命名规范

- 文件: snake_case.rs
- 函数: snake_case
- 结构体: PascalCase
- 常量: SCREAMING_SNAKE_CASE

### 文档要求

- 所有公共 API 必须有文档
- 代码示例必须可运行
- 使用中文或英文（保持一致）

---

## 提交信息规范

使用 Conventional Commits:

```
<type>(<scope>): <description>

[optional body]

[optional footer]
```

### 类型

| 类型 | 说明 |
|------|------|
| feat | 新功能 |
| fix | 修复 |
| docs | 文档 |
| style | 格式 |
| refactor | 重构 |
| test | 测试 |
| chore | 构建/工具 |

### 示例

```
feat(c01): 添加所有权转移示例

fix(c06): 修复异步取消竞争条件
docs: 更新 API 文档
test(c08): 添加排序算法测试
```

---

## Pull Request 流程

### PR 要求

- 所有检查必须通过
- 至少一个审查者批准
- 代码覆盖率不下降
- 文档已更新

### 审查清单

- [ ] 代码正确性
- [ ] 测试覆盖
- [ ] 文档完整
- [ ] 性能影响
- [ ] 向后兼容

---

## 模块特定指南

各模块可能有独立的贡献指南:

- [C01 所有权](./crates/c01_ownership_borrow_scope/CONTRIBUTING.md)
- [C02 类型系统](./crates/c02_type_system/CONTRIBUTING.md)
- [C11 宏系统](./crates/c11_macro_system/CONTRIBUTING.md)

---

## 链接规范

### 文档内链接

- 从 docs/ 引用 crates: 使用 ../crates/
- 目录命名: tier_01_foundations（统一格式）
- 文件名: 与实际文件名一致（大小写敏感）

### 链接检查

提交 PR 前运行:

```bash
cargo deadlinks
# 或
markdown-link-check docs/*.md
```

---

## 社区

- 问题讨论: GitHub Issues
- 实时聊天: Discord
- 邮件列表: <rust-learning@example.com>

---

## 许可证

贡献你的代码即表示你同意将其许可为 MIT 或 Apache-2.0。

---

## 参考

- [ARCHITECTURE.md](./docs/ARCHITECTURE.md)
- [DEVELOPMENT.md](./DEVELOPMENT.md)
- [TESTING.md](./TESTING.md)
