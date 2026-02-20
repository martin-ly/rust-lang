# Rust 学习检查清单

> **最后更新**: 2026-02-11
> **用途**: 追踪学习进度、间隔重复、自测验证

---

## 可量化学习目标

| 阶段   | 模块      | 目标                     | 验证方式              |
| :--- | :--- | :--- | :--- || 入门   | C01-C03   | 能独立编写所有权正确代码 | 通过 C01-C03 测试     |
| 进阶   | C04-C06   | 理解泛型、并发、异步     | 完成 3 个示例项目     |
| 高级   | C07-C10   | 掌握系统与网络编程       | 完成 1 个网络应用     |
| 专家   | C11-C12   | 宏与 WASM 开发           | 完成 1 个 WASM 项目   |

---

## 间隔重复建议 (Spaced Repetition)

根据认知科学，建议在以下时间点复习：

| 学习日 | 复习日 1 | 复习日 2 | 复习日 3 |
| :--- | :--- | :--- | :--- || Day 0  | Day 1    | Day 4    | Day 11   |
| Day 1  | Day 2    | Day 5    | Day 12   |
| ...    | +1 天    | +3 天    | +7 天    |

**实践**:

- 学完每个模块后，在复习日重做该模块的速查卡自测题
- 使用 Anki 或类似工具制作 Rust 概念卡片

---

## 自测题 (按模块)

### C01 所有权与借用

1. 写出所有权三大规则
2. mutable 借用与 immutable 借用的区别？
3. 什么情况下需要使用 `Rc` 或 `Arc`？

### C02 类型系统

1. 泛型与 Trait 的关系？
2. `impl Trait` 与 `dyn Trait` 的区别？
3. 生命周期标注 `'a` 的含义？

### C03 控制流与函数

1. `match` 与 `if let` 的使用场景？
2. 闭包怎样捕获环境变量？
3. `?` 操作符的展开形式？

### C04 泛型编程

1. 泛型单态化与零成本抽象的关系？
2. `where` 子句与内联约束的适用场景？
3. 关联类型与泛型参数的区别？

### C05 线程与并发

1. `Mutex` 与 `RwLock` 的选型场景？
2. 通道 `mpsc` 的典型用法？
3. `Send` 与 `Sync` 的含义？

### C06 异步编程

1. `async` 块返回什么类型？
2. Tokio 运行时的作用？
3. `.await` 在什么情况下会挂起？

### C07 进程管理

1. `Command::new()` 与 `Command::spawn()` 的区别？
2. 子进程如何捕获输出？
3. 跨平台 IPC 常用方案？

### C08 算法与数据结构

1. `Iterator` 的 `map` 与 `for_each` 何时消费？
2. `Vec::sort()` 与 `sort_unstable()` 的取舍？
3. 何时用 `BinaryHeap` 而非 `Vec` 排序？

### C09 设计模式

1. Rust 中实现单例的常见方式？
2. 建造者模式与 `Default` trait 的配合？
3. 策略模式与闭包/函数指针的选型？

### C10 网络编程

1. Tokio 下 `TcpListener::accept()` 返回什么？
2. `reqwest` 异步与同步客户端的区别？
3. WebSocket 常见心跳机制？

### C11 宏系统

1. 声明宏与过程宏的扩展时机？
2. `syn` 与 `quote` 的典型用途？
3. `#[derive]` 宏如何获取结构体字段？

### C12 WASM

1. `wasm-bindgen` 的作用？
2. `#[wasm_bindgen]` 可标注哪些项？
3. WASM 与 JS 互操作的数据拷贝注意点？

---

## 学习进度追踪

- [ ] C01 所有权与借用
- [ ] C02 类型系统
- [ ] C03 控制流与函数
- [ ] C04 泛型编程
- [ ] C05 线程与并发
- [ ] C06 异步编程
- [ ] C07 进程管理
- [ ] C08 算法与数据结构
- [ ] C09 设计模式
- [ ] C10 网络编程
- [ ] C11 宏系统
- [ ] C12 WebAssembly

---

## 相关文档

- [README.md](./README.md) - 项目入口
- [guides/README.md](./guides/README.md) - 学习指南
- [exercises/README.md](./exercises/README.md) - 交互式练习（Rustlings、Playground）
- [docs/quick_reference/](./docs/quick_reference/) - 速查卡
