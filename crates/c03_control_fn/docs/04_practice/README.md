# 04. 实践应用 (Practice)

本部分关注 Rust 控制流与函数在实际工程中的应用，包括性能优化、最佳实践、常见陷阱以及实战案例。

## 📚 文档列表

### 实践指南

1. [**函数与闭包实践**](./01_functions_closures_practice.md)
   - 函数设计原则
   - 闭包使用场景
   - 高阶函数应用
   - API 设计最佳实践

2. [**错误处理实践**](./02_error_handling_practice.md)
   - Result 类型的实际应用
   - 自定义错误类型
   - 错误传播策略
   - anyhow 与 thiserror
   - 错误恢复模式

3. [**控制流性能实践（Rust 1.90）**](./03_control_flow_performance_practices_1_90.md)
   - 分支预测优化
   - 循环展开技巧
   - 迭代器性能
   - 零成本抽象验证
   - 编译器优化理解

4. [**控制流设计模式**](./04_control_flow_design_patterns.md)
   - 状态机模式
   - 策略模式
   - 责任链模式
   - 访问者模式
   - 命令模式

5. [**常见陷阱与解决方案**](./05_common_pitfalls.md)
   - 借用检查器与控制流
   - 闭包捕获问题
   - 模式匹配常见错误
   - 生命周期与控制流
   - 性能陷阱

### 实战案例

1. [**实战案例：命令行工具**](./06_case_study_cli.md)
   - 参数解析
   - 错误处理
   - 子命令设计
   - 配置管理

2. [**实战案例：状态机实现**](./07_case_study_state_machine.md)
   - 类型状态模式
   - 状态转换
   - 编译时验证
   - 性能优化

3. [**实战案例：解析器设计**](./08_case_study_parser.md)
   - 递归下降解析
   - 组合子模式
   - 错误恢复
   - 性能优化

## 🎯 学习目标

通过本部分的学习，你将：

- 掌握控制流在实际项目中的应用
- 学会设计高性能的控制流结构
- 了解常见陷阱并知道如何避免
- 能够应用设计模式解决实际问题
- 通过实战案例提升工程能力

## 📖 阅读顺序

### 推荐学习路径

#### 第一阶段：基础实践

1. [函数与闭包实践](./01_functions_closures_practice.md)
2. [错误处理实践](./02_error_handling_practice.md)
3. [常见陷阱与解决方案](./05_common_pitfalls.md)

#### 第二阶段：性能与设计

1. [控制流性能实践](./03_control_flow_performance_practices_1_90.md)
2. [控制流设计模式](./04_control_flow_design_patterns.md)

#### 第三阶段：实战应用

1. [实战案例：命令行工具](./06_case_study_cli.md)
2. [实战案例：状态机实现](./07_case_study_state_machine.md)
3. [实战案例：解析器设计](./08_case_study_parser.md)

### 按主题学习

- **性能优化** → 文档 3、5
- **设计模式** → 文档 4、7
- **错误处理** → 文档 2、6
- **实战项目** → 文档 6、7、8

## 🔗 相关章节

- **理论基础** → [理论基础](../01_theory/README.md)
- **基础知识** → [基础知识](../02_basics/README.md)
- **高级特性** → [高级主题](../03_advanced/README.md)

## 💻 代码示例

实践部分包含完整的可运行项目：

```bash
# 运行函数闭包示例
cargo run --example functions_closures_practice

# 运行错误处理示例
cargo run --example error_handling_practice

# 运行性能测试
cargo bench --bench control_flow_performance

# 运行实战案例
cargo run --example cli_tool
cargo run --example state_machine
cargo run --example parser
```

## 📊 难度分级

| 文档 | 难度 | 前置知识 | 预计学习时间 |
|------|------|---------|------------|
| 函数与闭包实践 | ⭐⭐⭐ | 基础+高级 | 3-4 小时 |
| 错误处理实践 | ⭐⭐⭐ | 基础错误处理 | 3-4 小时 |
| 控制流性能实践 | ⭐⭐⭐⭐ | 高级主题 | 4-5 小时 |
| 控制流设计模式 | ⭐⭐⭐⭐ | 高级主题 | 5-6 小时 |
| 常见陷阱 | ⭐⭐⭐ | 基础+高级 | 2-3 小时 |
| CLI 案例 | ⭐⭐⭐ | 基础实践 | 4-5 小时 |
| 状态机案例 | ⭐⭐⭐⭐ | 设计模式 | 5-6 小时 |
| 解析器案例 | ⭐⭐⭐⭐⭐ | 高级+设计模式 | 6-8 小时 |

## 💡 学习建议

1. **实践为主**：边学边做，完成每个练习和案例
2. **性能意识**：使用 benchmarks 验证性能优化
3. **代码质量**：关注代码的可读性和维护性
4. **设计思维**：思考为什么这样设计，有什么优缺点
5. **迭代优化**：先实现功能，再逐步优化
6. **测试驱动**：为代码编写充分的测试
7. **文档完善**：养成编写文档的好习惯

## 🎓 检查点

完成本部分学习后，你应该能够：

- [ ] 设计清晰、高效的函数和闭包 API
- [ ] 实现健壮的错误处理策略
- [ ] 编写性能优化的控制流代码
- [ ] 应用设计模式解决实际问题
- [ ] 避免常见的控制流陷阱
- [ ] 独立完成中等复杂度的项目
- [ ] 理解性能优化的权衡
- [ ] 编写可维护的生产级代码

## 🚀 实践建议

### 小型练习（1-2天）

1. 实现一个简单的配置文件解析器
2. 编写一个命令行计算器
3. 实现一个状态机验证器
4. 编写一个日志过滤工具

### 中型项目（1周）

1. 开发一个完整的 CLI 工具（如 grep 的简化版）
2. 实现一个简单的表达式求值器
3. 编写一个 JSON 解析器
4. 开发一个文件处理工具

### 大型项目（2-4周）

1. 实现一个小型编程语言解释器
2. 开发一个复杂的命令行应用
3. 编写一个代码生成器
4. 实现一个领域特定语言（DSL）

## 📖 推荐资源

### 官方资源

- [Rust Book - Error Handling](https://doc.rust-lang.org/book/ch09-00-error-handling.html)
- [Rust by Example - Flow Control](https://doc.rust-lang.org/rust-by-example/flow_control.html)
- [Performance Book](https://nnethercote.github.io/perf-book/)

### 社区资源

- [anyhow](https://docs.rs/anyhow/) - 错误处理库
- [thiserror](https://docs.rs/thiserror/) - 自定义错误类型
- [clap](https://docs.rs/clap/) - 命令行参数解析
- [nom](https://docs.rs/nom/) - 解析器组合子

### 相关模块

- **异步编程** → `c06_async` 模块
- **设计模式** → `c09_design_pattern` 模块
- **算法实现** → `c08_algorithms` 模块

## 🎯 项目成果

完成实践部分后，你将拥有：

- 3-5 个完整的小型项目
- 对 Rust 控制流的深入理解
- 丰富的实战经验
- 可展示的代码作品
- 解决实际问题的能力

---

*最后更新：2025年1月*  
*文档版本：v1.0*  
*Rust 版本：1.90+*
