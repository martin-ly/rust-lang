# 贡献指南

感谢您对 c12_model 项目的关注！本指南将帮助您了解如何为项目做出贡献。

## 贡献方式

### 1. 报告问题

如果您发现了 bug 或有功能请求，请：

1. 检查 [Issues](https://github.com/c12model/c12_model/issues) 是否已存在
2. 创建新的 Issue，包含：
   - 清晰的问题描述
   - 复现步骤
   - 预期行为
   - 实际行为
   - 环境信息（Rust 版本、操作系统等）

### 2. 提交代码

#### 准备工作

1. Fork 项目到您的 GitHub 账户
2. 克隆您的 fork：

   ```bash
   git clone https://github.com/your-username/c12_model.git
   cd c12_model
   ```

3. 添加上游仓库：

   ```bash
   git remote add upstream https://github.com/c12model/c12_model.git
   ```

#### 开发流程

1. **创建分支**：

   ```bash
   git checkout -b feature/your-feature-name
   # 或
   git checkout -b fix/your-bug-fix
   ```

2. **编写代码**：
   - 遵循项目的代码风格
   - 添加适当的文档注释
   - 编写测试用例
   - 确保所有测试通过

3. **运行测试**：

   ```bash
   cargo test
   cargo test --lib
   cargo test --examples
   ```

4. **性能评估（可选）**：当前仓库未内置基准项，如需请自建 criterion 基准或使用外部工具。

5. **检查代码质量**：

   ```bash
   cargo clippy
   cargo fmt
   ```

6. **提交更改**：

   ```bash
   git add .
   git commit -m "feat: add new feature description"
   ```

7. **推送分支**：

   ```bash
   git push origin feature/your-feature-name
   ```

8. **创建 Pull Request**：
   - 在 GitHub 上创建 PR
   - 填写 PR 模板
   - 等待代码审查

## 代码规范

### Rust 代码风格

1. **使用 rustfmt**：

   ```bash
   cargo fmt
   ```

2. **使用 clippy**：

   ```bash
   cargo clippy
   ```

3. **命名规范**：
   - 函数和变量：`snake_case`
   - 类型和结构体：`PascalCase`
   - 常量：`SCREAMING_SNAKE_CASE`
   - 模块：`snake_case`

4. **文档注释**：

   ```rust
   /// 计算系统利用率
   /// 
   /// # 参数
   /// - `arrival_rate`: 到达率 λ
   /// - `service_rate`: 服务率 μ
   /// 
   /// # 返回
   /// 系统利用率，范围 [0, ∞)
   /// 
   /// # 示例
   /// ```
   /// use c12_model::MM1Queue;
   /// let queue = MM1Queue::new(1.0, 2.0);
   /// assert_eq!(queue.utilization(), 0.5);
   /// ```
   pub fn utilization(&self) -> f64 {
       // 实现
   }
   ```

### 测试规范

1. **单元测试**：
   - 每个公共函数都应该有测试
   - 测试应该覆盖正常情况和边界情况
   - 测试应该验证错误处理

2. **集成测试**：
   - 在 `tests/` 目录下创建集成测试
   - 测试模块间的交互

3. **文档测试**：
   - 在文档注释中包含可运行的示例
   - 确保示例代码能够编译和运行

4. **基准测试（可选）**：
   - 如需评估性能，请创建自定义 criterion 基准

### 错误处理

1. **使用统一的错误类型**：

   ```rust
   use c12_model::{ModelError, ErrorHandler, Result as ModelResult};
   
   fn my_function() -> ModelResult<f64> {
       if condition {
           Err(ErrorHandler::validation_error("错误描述"))
       } else {
           Ok(result)
       }
   }
   ```

2. **提供有意义的错误信息**：
   - 错误信息应该清晰易懂
   - 包含足够的上下文信息
   - 提供修复建议

### 性能考虑

1. **避免不必要的分配**：
   - 使用 `&str` 而不是 `String` 当可能时
   - 重用数据结构
   - 使用 `Vec::with_capacity` 预分配

2. **优化算法复杂度**：
   - 选择合适的数据结构
   - 避免不必要的嵌套循环

## 项目结构

```text
c12_model/
├── src/                    # 源代码
│   ├── lib.rs             # 库入口
│   ├── config.rs          # 配置管理
│   ├── error.rs           # 错误处理
│   ├── queueing_models.rs # 排队论模型
│   ├── ml_models.rs       # 机器学习模型
│   ├── formal_models.rs   # 形式化方法模型
│   ├── math_models.rs     # 数学模型
│   ├── performance_models.rs # 性能分析模型
│   ├── utils.rs           # 工具函数
│   └── （可按需扩展）
├── examples/              # 示例代码
├── tests/                 # 集成测试
├── docs/                  # 文档
└── Cargo.toml            # 项目配置
```

## 提交信息规范

使用 [Conventional Commits](https://www.conventionalcommits.org/) 规范：

```text
<type>[optional scope]: <description>

[optional body]

[optional footer(s)]
```

### 类型

- `feat`: 新功能
- `fix`: 修复 bug
- `docs`: 文档更新
- `style`: 代码格式调整
- `refactor`: 代码重构
- `test`: 测试相关
- `chore`: 构建过程或辅助工具的变动

### 示例

```text
feat(queueing): add M/G/1 queue model

Add support for M/G/1 queueing model with general service time distribution.
Includes performance analysis and reliability calculations.

Closes #123
```

## 代码审查

### 审查者指南

1. **检查代码质量**：
   - 代码是否遵循项目规范
   - 是否有适当的测试覆盖
   - 性能是否合理

2. **检查功能正确性**：
   - 功能是否按预期工作
   - 边界情况是否处理
   - 错误处理是否完善

3. **检查文档**：
   - API 文档是否完整
   - 示例代码是否正确
   - 变更日志是否需要更新

### 被审查者指南

1. **响应审查意见**：
   - 及时回复审查意见
   - 解释设计决策
   - 根据意见修改代码

2. **保持 PR 更新**：
   - 解决冲突
   - 保持分支最新
   - 添加必要的测试

## 发布流程

### 版本号规范

使用 [语义化版本](https://semver.org/)：

- `MAJOR`: 不兼容的 API 修改
- `MINOR`: 向下兼容的功能性新增
- `PATCH`: 向下兼容的问题修正

### 发布步骤

1. **更新版本号**：
   - 更新 `Cargo.toml` 中的版本
   - 更新 `CHANGELOG.md`

2. **创建发布标签**：

   ```bash
   git tag -a v0.2.0 -m "Release version 0.2.0"
   git push origin v0.2.0
   ```

3. **发布到 crates.io**：

   ```bash
   cargo publish
   ```

## 社区准则

### 行为准则

1. **友好和包容**：欢迎所有背景的贡献者
2. **尊重他人**：保持专业和礼貌的交流
3. **建设性反馈**：提供有帮助的反馈和建议
4. **协作精神**：共同努力改进项目

### 沟通渠道

- **GitHub Issues**: 问题报告和功能请求
- **GitHub Discussions**: 一般讨论和问答
- **Pull Requests**: 代码贡献和审查

## 获取帮助

如果您在贡献过程中遇到问题：

1. 查看现有文档
2. 搜索 Issues 和 Discussions
3. 创建新的 Issue 寻求帮助
4. 联系维护者

## 致谢

感谢所有为 c12_model 项目做出贡献的开发者！您的贡献使这个项目变得更好。

---

**最后更新**: 2025年1月  
**版本**: 0.2.0
