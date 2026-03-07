# Rust设计模式系列

> **Rust版本**: 1.93.1
> **适用读者**: 有Rust基础，希望深入理解设计模式应用的开发者
> **学习目标**: 掌握Rust特有的设计模式实现方式，编写符合Rust哲学的代码

---

## 目录结构

```text
11-design-patterns/
├── README.md                          # 本文件 - 导航和学习指南
├── 11-01-rust-design-patterns.md     # 设计模式全面指南
├── 11-02-idiomatic-patterns.md       # 惯用Rust模式
├── 11-03-type-state-pattern.md       # 类型状态模式详解
├── creational/                        # 创建型模式
│   ├── README.md
│   ├── singleton.md
│   ├── builder.md
│   └── factory.md
├── structural/                        # 结构型模式
│   ├── README.md
│   ├── adapter.md
│   ├── decorator.md
│   └── proxy.md
├── behavioral/                        # 行为型模式
│   ├── README.md
│   ├── observer.md
│   ├── strategy.md
│   └── command.md
└── rust-specific/                     # Rust特有模式
    ├── README.md
    ├── raii-guard.md
    └── newtype.md
```

---

## 文件导航

### [11-01-rust-design-patterns.md](./11-01-rust-design-patterns.md)

**内容概述**: Rust设计模式的全面指南，涵盖所有经典GoF模式在Rust中的实现。

**包含内容**:

- 创建型模式：构建者、工厂、单例、原型
- 结构型模式：适配器、装饰器、组合、外观、桥接、代理
- 行为型模式：命令、策略、观察者、迭代器、状态、模板方法、责任链、访问者、备忘录、中介者
- Rust特有模式：Newtype、类型状态、RAII守卫

**适合**: 系统性学习设计模式

**阅读时间**: 约45分钟

---

### [11-02-idiomatic-patterns.md](./11-02-idiomatic-patterns.md)

**内容概述**: Rust语言特有的惯用编程模式，编写地道Rust代码的必备指南。

**包含内容**:

- Option组合子（map, and_then, unwrap_or等）
- Result传播与错误处理（?操作符、try_trait）
- 借用模式（AsRef、Borrow、ToOwned）
- 转换模式（From、Into、TryFrom、TryInto）
- 迭代器适配器模式
- 闭包与函数式编程
- 智能指针模式
- 生命周期管理最佳实践

**适合**: 提高Rust代码质量和地道程度

**阅读时间**: 约40分钟

---

### [11-03-type-state-pattern.md](./11-03-type-state-pattern.md)

**内容概述**: 深度剖析类型状态模式，Rust类型系统最强大的应用之一。

**包含内容**:

- 类型状态模式核心概念
- 从零构建类型状态机
- 数据库连接实战案例
- HTTP请求构建器案例
- 编译时状态验证
- 零成本抽象实现
- 与状态模式的对比
- 高级技巧与权衡

**适合**: 深入理解Rust类型系统，编写编译时安全的代码

**阅读时间**: 约35分钟

---

## 学习路径建议

### 路径一：系统设计导向

适合需要设计复杂Rust系统的架构师：

1. **11-01-rust-design-patterns.md** - 全面了解可用模式
2. **11-03-type-state-pattern.md** - 掌握Rust最强大的设计模式
3. **11-02-idiomatic-patterns.md** - 编写地道Rust代码

### 路径二：算法与数据处理导向

适合需要处理大量数据的开发者：

1. **11-02-idiomatic-patterns.md** - 掌握迭代器和错误处理模式
2. **11-01-rust-design-patterns.md** - 了解策略与访问者模式

### 路径三：API设计导向

适合需要设计公开库的开发者：

1. **11-03-type-state-pattern.md** - 类型安全API
2. **11-02-idiomatic-patterns.md** - 惯用接口设计
3. **11-01-rust-design-patterns.md** - 其他模式参考

---

## 前置知识要求

在阅读本系列之前，建议掌握：

- **所有权系统**: 借用、生命周期、所有权转移
- **Trait系统**: 定义、实现、泛型约束
- **基础泛型**: 泛型函数、结构体、生命周期参数
- **错误处理**: Result、Option基本用法
- **模块系统**: 包、crate、模块组织

推荐先修内容：

- [The Rust Book](https://doc.rust-lang.org/book/) 第1-10章
- [Rust by Example](https://doc.rust-lang.org/rust-by-example/) 基础部分

---

## 实践建议

### 练习1：设计一个类型安全的状态机

实现一个文件解析器的状态机：

- 状态：Idle → Reading → Parsing → Complete | Error
- 使用类型状态模式确保非法转换在编译时被阻止
- 参考：11-03-type-state-pattern.md

### 练习2：构建SQL查询器

设计一个类型安全的SQL查询构建器：

- 支持SELECT、WHERE、ORDER BY子句
- 使用构建者模式
- 确保只有完整的查询才能执行
- 参考：11-04-builder-pattern.md

### 练习3：重构代码使用惯用模式

找到一段使用unwrap()过多的代码：

- 使用?操作符重构错误传播
- 使用Option组合子简化逻辑
- 参考：11-02-idiomatic-patterns.md

---

## 相关资源

### 官方资源

- [Rust Design Patterns](https://rust-unofficial.github.io/patterns/) - Rust非官方设计模式书
- [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/) - API设计指南
- [The Rust Reference](https://doc.rust-lang.org/reference/) - 语言参考

### 推荐书籍

- *Programming Rust* by Jim Blandy, et al.
- *Rust for Rustaceans* by Jon Gjengset
- *Effective Rust* by David Drysdale
- *Zero To Production In Rust* by Luca Palmieri

### 在线资源

- [Rust Playground](https://play.rust-lang.org/) - 在线代码测试
- [Rustlings](https://github.com/rust-lang/rustlings) - 交互式练习
- [Exercism Rust Track](https://exercism.org/tracks/rust) - 渐进式练习

---

## 模式速查表

### 创建型模式

| 模式 | 使用场景 | Rust特性 |
|------|---------|---------|
| Builder | 复杂对象创建 | consuming builder, type state |
| Factory | 运行时类型选择 | Trait对象 |
| Singleton | 全局唯一实例 | OnceLock, lazy_static |
| Prototype | 对象克隆 | Clone trait |

### 结构型模式

| 模式 | 使用场景 | Rust特性 |
|------|---------|---------|
| Adapter | 接口兼容 | Trait实现 |
| Decorator | 动态添加功能 | 泛型组合 |
| Composite | 树形结构 | Trait对象集合 |
| Facade | 简化复杂接口 | 模块封装 |

### 行为型模式

| 模式 | 使用场景 | Rust特性 |
|------|---------|---------|
| Command | 请求参数化 | 闭包, Trait对象 |
| Strategy | 算法替换 | Trait对象, 泛型 |
| Observer | 事件通知 | Weak引用避免循环 |
| Iterator | 序列访问 | Iterator trait |

### Rust特有模式

| 模式 | 使用场景 | 优势 |
|------|---------|------|
| Type State | 状态机 | 编译时验证 |
| Newtype | 类型区分 | 零成本抽象 |
| RAII Guard | 资源管理 | 自动清理 |
| Option组合 | 空值处理 | 显式安全 |

---

## 常见问答

### Q: Rust中为什么没有传统继承？

A: Rust使用Trait系统替代继承，通过组合实现代码复用。这避免了继承的菱形问题，并提供更灵活的接口设计。

### Q: 什么时候应该使用类型状态模式？

A: 当你有明确的状态转换规则，且希望在编译时防止非法状态转换时。特别适用于连接管理、解析器状态、工作流引擎等场景。

### Q: `Rc<RefCell<T>>`是反模式吗？

A: 不完全是，但应该谨慎使用。它用于单线程场景下需要共享可变访问的情况。优先考虑使用借用检查器的静态分析，仅在必要时降级到运行时检查。

### Q: 如何选择构建者模式变体？

A:

- **标准构建者**: 通用场景
- **Type State构建者**: 需要编译时验证必须字段
- **消耗式构建者**: 构建后不再需要builder
- **可变引用构建者**: 需要重用builder

### Q: 自定义迭代器的性能如何？

A: Rust的迭代器是零成本抽象，通过单态化和内联优化，自定义迭代器通常与手写循环性能相当。

---

## 贡献与反馈

本系列文档持续更新，欢迎：

- 提出改进建议
- 报告错误或不清晰之处
- 分享实际应用案例
- 贡献更多模式示例

---

## 版本历史

| 版本 | 日期 | 变更内容 |
|------|------|---------|
| 1.0 | 2026-03-04 | 初始版本，包含5个文档 |

---

**Happy Rusting! 🦀**:
