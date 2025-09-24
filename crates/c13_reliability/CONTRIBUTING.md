# 贡献指南

感谢您对 c13_reliability 项目的关注！我们欢迎各种形式的贡献。

## 如何贡献

### 报告问题

如果您发现了 bug 或有功能请求，请通过以下方式报告：

1. 检查 [Issues](https://github.com/rust-lang/c13_reliability/issues) 是否已有相关问题
2. 如果没有，请创建新的 Issue
3. 提供详细的问题描述和复现步骤

### 提交代码

1. Fork 本仓库
2. 创建您的特性分支 (`git checkout -b feature/AmazingFeature`)
3. 提交您的更改 (`git commit -m 'Add some AmazingFeature'`)
4. 推送到分支 (`git push origin feature/AmazingFeature`)
5. 打开 Pull Request

## 开发环境设置

### 前置要求

- Rust 1.90 或更高版本
- Cargo
- Git

### 克隆仓库

```bash
git clone https://github.com/rust-lang/c13_reliability.git
cd c13_reliability
```

### 运行测试

```bash
# 运行所有测试
cargo test

# 运行特定模块的测试
cargo test error_handling

# 运行集成测试
cargo test --test integration_tests
```

### 运行示例

```bash
# 运行基本使用示例
cargo run --example basic_usage

# 运行高级使用示例
cargo run --example advanced_usage

# 运行集成示例
cargo run --example integration_example
```

### 运行基准测试

```bash
cargo bench
```

## 代码规范

### Rust 代码风格

我们使用 `rustfmt` 和 `clippy` 来保持代码风格一致：

```bash
# 格式化代码
cargo fmt

# 运行 clippy 检查
cargo clippy -- -D warnings
```

### 文档规范

- 所有公共 API 必须有文档注释
- 使用 `///` 为函数、结构体、枚举等添加文档
- 提供使用示例
- 文档应该用中文编写

### 测试规范

- 每个公共函数都应该有对应的测试
- 测试应该覆盖正常情况和异常情况
- 使用描述性的测试名称
- 测试应该独立且可重复运行

### 提交信息规范

使用以下格式编写提交信息：

```text
<类型>(<范围>): <描述>

[可选的正文]

[可选的脚注]
```

类型包括：

- `feat`: 新功能
- `fix`: 修复 bug
- `docs`: 文档更新
- `style`: 代码格式调整
- `refactor`: 代码重构
- `test`: 测试相关
- `chore`: 构建过程或辅助工具的变动

示例：

```text
feat(error_handling): 添加统一错误处理系统

- 实现 UnifiedError 结构体
- 添加错误上下文记录
- 提供错误恢复策略
```

## 项目结构

```text
crates/c13_reliability/
├── src/                    # 源代码
│   ├── error_handling/     # 错误处理模块
│   ├── fault_tolerance/    # 容错机制模块
│   ├── runtime_monitoring/ # 运行时监控模块
│   ├── chaos_engineering/  # 混沌工程模块
│   ├── config/            # 配置管理模块
│   ├── metrics/           # 指标收集模块
│   ├── utils/             # 工具函数模块
│   └── lib.rs             # 库入口
├── examples/              # 示例代码
├── tests/                 # 集成测试
├── benches/               # 基准测试
├── docs/                  # 文档
├── Cargo.toml            # 项目配置
├── README.md             # 项目说明
├── CHANGELOG.md          # 更新日志
├── LICENSE               # 许可证
└── CONTRIBUTING.md       # 贡献指南
```

## 模块开发指南

### 添加新模块

1. 在 `src/` 目录下创建新的模块目录
2. 创建 `mod.rs` 文件定义模块结构
3. 在 `src/lib.rs` 中声明新模块
4. 在 `prelude` 中导出公共 API
5. 添加相应的测试和文档

### 模块结构

每个模块应该包含：

- `mod.rs`: 模块定义和公共 API
- 具体的实现文件
- 相应的测试文件
- 文档说明

## 性能考虑

### 基准测试

- 为新功能添加基准测试
- 确保性能回归测试通过
- 使用 `criterion` 进行性能测试

### 内存使用

- 避免不必要的内存分配
- 使用对象池减少 GC 压力
- 监控内存泄漏

### CPU 使用

- 使用异步处理减少阻塞
- 批量处理提高效率
- 缓存减少重复计算

## 安全考虑

### 输入验证

- 验证所有外部输入
- 防止注入攻击
- 限制资源使用

### 错误处理

- 不泄露敏感信息
- 记录安全相关事件
- 实现适当的错误恢复

## 发布流程

### 版本号

遵循 [语义化版本](https://semver.org/lang/zh-CN/) 规范：

- 主版本号：不兼容的 API 修改
- 次版本号：向下兼容的功能性新增
- 修订号：向下兼容的问题修正

### 发布检查清单

- [ ] 所有测试通过
- [ ] 基准测试通过
- [ ] 文档更新完成
- [ ] CHANGELOG.md 更新
- [ ] 版本号更新
- [ ] 标签创建

## 社区

### 讨论

- 使用 GitHub Issues 进行讨论
- 欢迎提出问题和建议
- 分享使用经验和最佳实践

### 支持

- 查看文档和示例
- 搜索已有的 Issues
- 创建新的 Issue 寻求帮助

## 许可证

通过贡献代码，您同意您的贡献将在 MIT 许可证下发布。

## 感谢

感谢所有为项目做出贡献的开发者！

---

如果您有任何问题或建议，请随时联系我们。
