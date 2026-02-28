# MDBook Quiz 使用指南

本文档介绍如何在项目中使用和维护 mdbook-quiz 交互式测验系统。

## 目录

- [快速开始](#快速开始)
- [添加新测验](#添加新测验)
- [测验编写最佳实践](#测验编写最佳实践)
- [测验格式规范](#测验格式规范)
- [常见问题](#常见问题)

## 快速开始

### 1. 安装依赖

确保已安装 mdbook 和 mdbook-quiz：

```bash
cargo install mdbook
cargo install mdbook-quiz
```

### 2. 构建和预览

```bash
cd book
mdbook build    # 构建
mdbook serve    # 预览（自动刷新）
```

### 3. 访问测验

打开浏览器访问 `http://localhost:3000`，选择对应的测验章节即可开始。

## 添加新测验

### 步骤 1：创建测验目录

如果还没有对应主题的目录，先创建：

```bash
mkdir -p book/src/quizzes
```

### 步骤 2：创建 TOML 测验文件

在 `book/src/quizzes/` 下创建新的 `.toml` 文件：

```bash
touch book/src/quizzes/your_topic.toml
```

### 步骤 3：编写测验内容

参考以下模板：

```toml
[[questions]]
type = "SingleChoice"
id = "your_topic_001"
prompt = "题目描述"
answer = 0
options = [
  "选项 A",
  "选项 B",
  "选项 C",
  "选项 D"
]
explanation = "详细解释为什么正确答案是正确的，以及其他选项为什么错误。"
difficulty = "基础"
```

### 步骤 4：创建 Markdown 入口文件

创建 `book/src/quizzes/your_topic.md`：

```markdown
# 主题测验

本测验涵盖 ... 的核心概念。

{{#quiz ./your_topic.toml}}
```

### 步骤 5：更新 SUMMARY.md

在 `book/src/SUMMARY.md` 中添加新章节：

```markdown
- [主题测验](./quizzes/your_topic.md)
```

### 步骤 6：更新测验索引

在 `book/src/quiz-index.md` 中添加新测验信息。

## 测验编写最佳实践

### 1. 题目质量

- **概念准确**：确保题目和答案技术上正确
- **覆盖全面**：涵盖主题的各个方面和常见误区
- **难度分级**：明确标注基础/进阶/挑战
- **代码可运行**：所有代码示例应该可以编译（除非用于展示错误）

### 2. 答案设计

- **干扰项合理**：错误选项应该反映常见误解
- **解释详尽**：不仅说明为什么对，还要说明为什么错
- **引用文档**：适当引用官方文档或标准库

### 3. 难度分级标准

| 级别 | 描述 | 示例 |
|------|------|------|
| 🟢 基础 | 基本概念，直接考察 | 什么是所有权？ |
| 🟡 进阶 | 需要理解深层原理 | 为什么这段代码不能编译？ |
| 🔴 挑战 | 复杂场景，边界情况 | 结合多个概念的实际问题 |

### 4. 题型选择指南

- **单选题**：只有一个正确答案的概念性问题
- **多选题**：多个正确选项，考察全面理解
- **判断题**：明确的是非概念
- **填空题**：代码补全，考察实践能力

## 测验格式规范

### 单选题 (SingleChoice)

```toml
[[questions]]
type = "SingleChoice"
id = "unique_id_001"
prompt = "题目文本"
answer = 1  # 正确选项的索引（从0开始）
options = [
  "选项 A",
  "选项 B",
  "选项 C",
  "选项 D"
]
explanation = "解释文本"
difficulty = "基础"
```

### 多选题 (MultipleChoice)

```toml
[[questions]]
type = "MultipleChoice"
id = "unique_id_002"
prompt = "题目文本"
answer = [0, 2]  # 正确选项的索引数组
options = [
  "选项 A",
  "选项 B",
  "选项 C",
  "选项 D"
]
explanation = "解释文本"
difficulty = "进阶"
```

### 判断题 (TrueFalse)

```toml
[[questions]]
type = "TrueFalse"
id = "unique_id_003"
prompt = "陈述文本"
answer = false  # true 或 false
explanation = "解释文本"
difficulty = "基础"
```

### 填空题 (FillInBlank)

```toml
[[questions]]
type = "FillInBlank"
id = "unique_id_004"
prompt = "题目描述，用 _____ 表示填空位置"
answer = ["答案1", "答案2"]  # 允许多个正确答案
explanation = "解释文本"
difficulty = "进阶"
```

### 代码块格式

在 prompt 中使用代码块：

```toml
prompt = '''以下代码的输出是什么？

```rust
fn main() {
    println!("Hello");
}
```

选择正确答案：'''
```

注意使用三引号（'''）来支持多行字符串。

## 测验文件结构示例

```toml
# 所有权测验 - ownership.toml

# 基础题（5道）
[[questions]]
# ... 基础题目 ...

# 进阶题（4道）
[[questions]]
# ... 进阶题目 ...

# 挑战题（3道）
[[questions]]
# ... 挑战题目 ...
```

## 常见问题

### Q: mdbook-quiz 和 mdbook 版本不兼容怎么办？

A: 确保两者都使用最新版本：

```bash
cargo install mdbook --force
cargo install mdbook-quiz --force
```

### Q: 测验不显示怎么办？

A: 检查以下几点：
1. TOML 文件语法是否正确（可以用在线 TOML 验证器）
2. 文件路径是否正确（相对于 .md 文件）
3. `book.toml` 中是否正确配置了预处理器

### Q: 如何添加图片到题目中？

A: 当前 mdbook-quiz 不支持直接嵌入图片。可以将图片放在 `book/src/assets/` 目录，在 prompt 中使用 Markdown 图片语法引用。

### Q: 可以限制答题次数吗？

A: mdbook-quiz 本身不限制答题次数。如果需要，可以通过自定义 JavaScript 实现。

### Q: 如何导出测验结果？

A: 目前 mdbook-quiz 不支持直接导出。可以通过浏览器的 Local Storage 查看保存的答案，或扩展插件实现导出功能。

## 贡献指南

### 提交新测验

1. 创建新的分支
2. 按照本指南添加测验
3. 本地测试确保可以正常显示
4. 提交 PR，说明测验覆盖的内容

### 代码审查清单

- [ ] 题目技术准确性
- [ ] 解释清晰完整
- [ ] 难度标注合理
- [ ] ID 全局唯一
- [ ] TOML 语法正确
- [ ] Markdown 格式正确

## 参考资源

- [mdbook 官方文档](https://rust-lang.github.io/mdBook/)
- [mdbook-quiz GitHub](https://github.com/willcrichton/mdbook-quiz)
- [Brown 大学交互式 Rust Book](https://rust-book.cs.brown.edu/)
- [Rust 官方文档](https://doc.rust-lang.org/)

---

如有问题或建议，请在项目 Issue 中提出。
