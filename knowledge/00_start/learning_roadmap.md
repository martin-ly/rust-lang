# Rust 学习路线图

> **从入门到精通的完整路径**
> **总预计时间**: 200-400 小时

## 🎯 学习阶段总览

```
Level 1: 基础 (40-60小时)
    │
    ▼
Level 2: 进阶 (60-80小时)
    │
    ▼
Level 3: 高级 (80-100小时)
    │
    ▼
Level 4: 精通 (60-100小时)
    │
    ▼
Level 5: 专家 (持续学习)
```

---

## Level 1: 基础 - 建立根基 (40-60小时)

### 1.1 起步 (5-8小时)

| 主题 | 文档 | 时间 | 目标 |
|------|------|------|------|
| 安装配置 | [installation.md](installation.md) | 1h | 搭建环境 |
| Hello World | [hello_world.md](hello_world.md) | 2h | 理解项目结构 |
| 设计哲学 | [rust_philosophy.md](rust_philosophy.md) | 2h | 理解核心理念 |
| Cargo 基础 | [../06_ecosystem/cargo_basics.md](../06_ecosystem/cargo_basics.md) | 2h | 包管理 |

### 1.2 核心语法 (15-20小时)

| 主题 | 文档位置 | 时间 | 掌握程度 |
|------|---------|------|----------|
| 变量与可变性 | ../01_fundamentals/variables.md | 2h | ⭐⭐⭐ |
| 基本类型 | ../01_fundamentals/types.md | 3h | ⭐⭐⭐ |
| 函数 | ../01_fundamentals/functions.md | 2h | ⭐⭐⭐ |
| 控制流 | ../01_fundamentals/control_flow.md | 3h | ⭐⭐⭐ |
| 结构体 | ../01_fundamentals/structs.md | 3h | ⭐⭐⭐ |
| 枚举与模式匹配 | ../01_fundamentals/enums.md | 4h | ⭐⭐⭐ |

### 1.3 所有权系统 (20-30小时) ⭐⭐⭐⭐⭐

**这是 Rust 最重要的概念！**

| 主题 | 文档位置 | 时间 | 掌握程度 |
|------|---------|------|----------|
| 所有权基础 | ../01_fundamentals/ownership.md | 5h | ⭐⭐⭐⭐⭐ |
| 借用 | ../01_fundamentals/borrowing.md | 5h | ⭐⭐⭐⭐⭐ |
| 切片 | ../01_fundamentals/slices.md | 3h | ⭐⭐⭐⭐ |
| 生命周期 | ../01_fundamentals/lifetimes.md | 8h | ⭐⭐⭐⭐⭐ |

### Level 1 项目实战

- [ ] 命令行计算器
- [ ] 待办事项 CLI
- [ ] 文件统计工具

---

## Level 2: 进阶 - 掌握抽象 (60-80小时)

### 2.1 类型系统 (15-20小时)

| 主题 | 文档位置 | 时间 | 掌握程度 |
|------|---------|------|----------|
| 泛型 | ../02_intermediate/generics.md | 5h | ⭐⭐⭐⭐ |
| Trait | ../02_intermediate/traits.md | 8h | ⭐⭐⭐⭐⭐ |
| 生命周期进阶 | ../02_intermediate/lifetimes_advanced.md | 5h | ⭐⭐⭐⭐ |

### 2.2 集合与迭代器 (10-15小时)

| 主题 | 文档位置 | 时间 | 掌握程度 |
|------|---------|------|----------|
| 向量、HashMap | ../02_intermediate/collections.md | 4h | ⭐⭐⭐⭐ |
| 迭代器 | ../01_fundamentals/iterators.md | 6h | ⭐⭐⭐⭐⭐ |
| 字符串处理 | ../02_intermediate/strings.md | 3h | ⭐⭐⭐⭐ |

### 2.3 错误处理 (5-8小时)

| 主题 | 文档位置 | 时间 | 掌握程度 |
|------|---------|------|----------|
| Result 和 Option | ../02_intermediate/error_handling.md | 4h | ⭐⭐⭐⭐⭐ |
| 错误传播 | ../02_intermediate/error_handling.md | 2h | ⭐⭐⭐⭐ |
| 自定义错误 | ../02_intermediate/error_handling.md | 2h | ⭐⭐⭐⭐ |

### 2.4 智能指针 (10-12小时)

| 主题 | 文档位置 | 时间 | 掌握程度 |
|------|---------|------|----------|
| Box | ../02_intermediate/smart_pointers.md | 2h | ⭐⭐⭐⭐ |
| Rc 和 Arc | ../02_intermediate/smart_pointers.md | 3h | ⭐⭐⭐⭐ |
| RefCell 和 Mutex | ../02_intermediate/interior_mutability.md | 5h | ⭐⭐⭐⭐⭐ |

### Level 2 项目实战

- [ ] 简单数据库（内存）
- [ ] HTTP 客户端
- [ ] 配置文件解析器

---

## Level 3: 高级 - 系统编程 (80-100小时)

### 3.1 并发编程 (20-25小时)

| 主题 | 文档位置 | 时间 | 掌握程度 |
|------|---------|------|----------|
| 线程基础 | ../03_advanced/concurrency/threads.md | 5h | ⭐⭐⭐⭐ |
| 消息传递 | ../03_advanced/concurrency/message_passing.md | 5h | ⭐⭐⭐⭐ |
| 共享状态 | ../03_advanced/concurrency/shared_state.md | 6h | ⭐⭐⭐⭐ |
| Send 和 Sync | ../03_advanced/concurrency/send_sync.md | 5h | ⭐⭐⭐⭐⭐ |

### 3.2 异步编程 (25-30小时)

| 主题 | 文档位置 | 时间 | 掌握程度 |
|------|---------|------|----------|
| async/await | ../03_advanced/async/async_await.md | 8h | ⭐⭐⭐⭐⭐ |
| Future 和 Pin | ../03_advanced/async/futures.md | 8h | ⭐⭐⭐⭐ |
| Tokio 运行时 | ../03_advanced/async/tokio.md | 8h | ⭐⭐⭐⭐ |
| 异步 trait | ../03_advanced/async/async_traits.md | 3h | ⭐⭐⭐ |

### 3.3 宏系统 (15-20小时)

| 主题 | 文档位置 | 时间 | 掌握程度 |
|------|---------|------|----------|
| 声明宏 | ../03_advanced/macros/declarative.md | 6h | ⭐⭐⭐⭐ |
| 过程宏 | ../03_advanced/macros/procedural.md | 8h | ⭐⭐⭐ |

### 3.4 Unsafe Rust (10-15小时)

| 主题 | 文档位置 | 时间 | 掌握程度 |
|------|---------|------|----------|
| Unsafe 基础 | ../03_advanced/unsafe/basics.md | 4h | ⭐⭐⭐⭐ |
| FFI | ../03_advanced/unsafe/ffi.md | 5h | ⭐⭐⭐ |
| 原始指针 | ../03_advanced/unsafe/raw_pointers.md | 3h | ⭐⭐⭐ |

### Level 3 项目实战

- [ ] 多线程 Web 服务器
- [ ] 异步爬虫
- [ ] 简单的数据库驱动

---

## Level 4: 精通 - 工程实践 (60-100小时)

### 4.1 设计模式 (20-25小时)

| 主题 | 文档位置 | 时间 | 掌握程度 |
|------|---------|------|----------|
| 创建型模式 | ../04_expert/design_patterns/creational.md | 6h | ⭐⭐⭐ |
| 结构型模式 | ../04_expert/design_patterns/structural.md | 8h | ⭐⭐⭐ |
| 行为型模式 | ../04_expert/design_patterns/behavioral.md | 8h | ⭐⭐⭐ |

### 4.2 性能优化 (15-20小时)

| 主题 | 文档位置 | 时间 | 掌握程度 |
|------|---------|------|----------|
| 性能分析 | ../04_expert/performance/profiling.md | 5h | ⭐⭐⭐ |
| 零成本抽象 | ../04_expert/performance/zero_cost.md | 5h | ⭐⭐⭐⭐ |
| SIMD | ../04_expert/performance/simd.md | 5h | ⭐⭐ |

### 4.3 内存模型 (10-15小时)

| 主题 | 文档位置 | 时间 | 掌握程度 |
|------|---------|------|----------|
| Miri | ../04_expert/miri/README.md | 5h | ⭐⭐⭐ |
| Tree Borrows | ../04_expert/miri/tree_borrows.md | 5h | ⭐⭐⭐ |

### Level 4 项目实战

- [ ] 高性能网络框架
- [ ] 数据库引擎模块
- [ ] 游戏引擎组件

---

## Level 5: 专家 - 持续学习

### 5.1 形式化验证

| 主题 | 文档位置 |
|------|---------|
| 形式化语义 | ../05_master/formal_semantics/ |
| 验证工具 | ../05_master/verification/ |

### 5.2 编译器内部

| 主题 | 文档位置 |
|------|---------|
| MIR | ../05_master/compiler/mir.md |
| 优化 | ../05_master/compiler/optimization.md |

### 5.3 贡献 Rust

- 阅读 [Rust RFCs](https://rust-lang.github.io/rfcs/)
- 参与 [Rust 开发](https://rustc-dev-guide.rust-lang.org/)

---

## 📊 个性化路径

### Web 开发者路径

基础 → 泛型/Trait → 错误处理 → 异步/Tokio → Web 框架

### 系统编程路径

基础 → 所有权深度 → 并发 → Unsafe → FFI → 嵌入式

### 数据科学路径

基础 → 迭代器 → 集合 → ndarray → 性能优化

---

## ✅ 学习检查清单

### Level 1 完成标准

- [ ] 理解所有权、借用、生命周期
- [ ] 能编写 500 行以内的程序
- [ ] 能阅读简单 Rust 代码

### Level 2 完成标准

- [ ] 能使用泛型和 Trait 设计接口
- [ ] 能处理各种错误场景
- [ ] 能编写 2000 行以内的项目

### Level 3 完成标准

- [ ] 能编写多线程/异步程序
- [ ] 理解 Unsafe 边界
- [ ] 能参与开源项目

### Level 4 完成标准

- [ ] 能优化程序性能
- [ ] 能设计系统架构
- [ ] 能指导他人学习

---

## 📖 学习资源

### 必读

- [The Rust Programming Language](https://doc.rust-lang.org/book/)
- [Rust by Example](https://doc.rust-lang.org/rust-by-example/)

### 推荐

- [Rustlings](https://github.com/rust-lang/rustlings) - 交互式练习
- [Exercism Rust](https://exercism.org/tracks/rust) - 编程练习
- [Rust 精选](https://github.com/rust-unofficial/awesome-rust)

---

**文档版本**: 1.0
**最后更新**: 2026-03-19
