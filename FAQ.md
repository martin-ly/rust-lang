# Rust 学习项目 FAQ

> 常见问题解答

---

## 📚 入门问题

### Q: 我该如何开始学习这个项目？

**A**: 建议按以下顺序：

1. 阅读 `docs/README.md` 了解项目结构
2. 查看 `docs/CROSS_MODULE_NAVIGATION.md` 了解学习路径
3. 从 `crates/c01_ownership/` 开始学习
4. 使用 `LEARNING_CHECKLIST.md` 跟踪进度

---

### Q: 需要什么样的 Rust 基础？

**A**:

- **零基础**: 从 C01 开始，配合官方 Rust Book
- **有基础**: 可从 C04 泛型开始，按需复习前面内容
- **进阶开发者**: 可直接阅读 content/ 目录的前沿内容

---

### Q: 学习顺序是什么？

**A**: 推荐顺序：

```text
C01 → C02 → C03 → C04 → C05 → C06
                      ↓
        C07    C08    C09    C10    C11    C12
```

详见 `docs/CROSS_MODULE_NAVIGATION.md`

---

## 🔧 技术问题

### Q: 编译失败怎么办？

**A**:

1. 确保 Rust 版本 >= 1.94.0: `rustc --version`
2. 更新工具链: `rustup update`
3. 清理构建: `cargo clean`
4. 重新构建: `cargo build`

---

### Q: 如何运行测试？

**A**:

```bash
# 运行所有测试
cargo test --workspace

# 运行特定 crate 的测试
cargo test --package c04_generic

# 运行特定测试
cargo test --package c04_generic -- advanced
```

---

### Q: 如何运行示例？

**A**:

```bash
# 运行特定示例
cargo run --example comprehensive_web_server

# 运行 crate 内的示例
cargo run --package c06_async --example tokio_smoke
```

---

## 📖 内容问题

### Q: crates/ 和 content/ 有什么区别？

**A**:

- **crates/**: 核心学习模块，包含可运行的代码和测试
- **content/**: 扩展内容，包含前沿特性、生产实践、学术研究

详见 `content/CONTENT_CRATES_MAPPING.md`

---

### Q: 如何找到特定主题的内容？

**A**: 使用主题索引：

- 内存安全 → C01, content/academic/
- 并发编程 → C05, C06, content/ecosystem/
- Web 开发 → C10, C12, content/ecosystem/web_frameworks/
- 系统编程 → C07, content/production/

---

### Q: 练习题的答案在哪里？

**A**: 练习题答案通常在文档的 `<details>` 标签内，点击"答案"展开。

---

## 🎯 进阶问题

### Q: 如何贡献代码？

**A**:

1. Fork 仓库
2. 创建特性分支
3. 提交更改（遵循现有代码风格）
4. 确保测试通过
5. 提交 Pull Request

---

### Q: 项目会跟进新 Rust 版本吗？

**A**: 是的，content/emerging/ 目录会跟踪 Rust 1.95+ 的新特性，crates/ 中的 archive/ 目录包含历史版本特性。

---

### Q: 有配套视频教程吗？

**A**: 目前主要是文本和代码形式。推荐使用方式：

1. 阅读文档
2. 运行代码示例
3. 完成练习题
4. 构建个人项目

---

## 🐛 常见问题

### Q: 遇到 "cannot find crate" 错误？

**A**:

```bash
# 更新依赖
cargo update

# 检查 Cargo.toml 配置
# 确保在工作区根目录运行
```

---

### Q: 文档链接失效？

**A**:

- 检查是否在正确目录
- 参考 `docs/00_MASTER_INDEX.md` 获取正确链接
- 提交 issue 报告失效链接

---

### Q: 如何在 VS Code 中获得最佳体验？

**A**: 推荐安装：

- rust-analyzer
- CodeLLDB (调试)
- Better TOML
- Markdown All in One

---

## 📞 获取帮助

### 还有问题？

1. **查看文档**: `docs/` 目录包含详细指南
2. **检查示例**: `examples/` 目录包含可运行代码
3. **运行测试**: 查看测试用例了解用法
4. **提交 Issue**: 报告问题或建议

---

## 📝 快速链接

| 问题类型 | 推荐资源 |
|----------|----------|
| 入门指南 | `GETTING_STARTED.md` |
| 学习路径 | `LEARNING_CHECKLIST.md` |
| 模块导航 | `docs/CROSS_MODULE_NAVIGATION.md` |
| 内容映射 | `content/CONTENT_CRATES_MAPPING.md` |
| 项目状态 | `PROGRESS_SUMMARY_2026_03_15.md` |

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-03-15
**状态**: ✅ 100% 完成
