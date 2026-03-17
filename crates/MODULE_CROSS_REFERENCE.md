# Crate 模块交叉引用指南

> 12 个学习模块之间的关联导航

---

## 🗺️ 模块依赖图

```
                    ┌─────────────────┐
                    │   C01 所有权     │
                    │  Ownership      │
                    └────────┬────────┘
                             │
                             ▼
                    ┌─────────────────┐
                    │   C02 类型系统   │
                    │  Type System    │
                    └────────┬────────┘
                             │
                             ▼
                    ┌─────────────────┐
                    │   C03 控制流     │
                    │  Control Flow   │
                    └────────┬────────┘
                             │
                             ▼
        ┌────────────────────┴────────────────────┐
        │                                         │
        ▼                                         ▼
┌─────────────────┐                     ┌─────────────────┐
│   C04 泛型       │                     │   C05 并发      │
│  Generics       │                     │  Concurrency    │
└────────┬────────┘                     └────────┬────────┘
         │                                        │
         │    ┌─────────────────────────┐         │
         └───▶│      C06 异步           │◀───────┘
              │     Async/Await         │
              └───────────┬─────────────┘
                          │
          ┌───────────────┼───────────────┐
          │               │               │
          ▼               ▼               ▼
┌─────────────────┐ ┌─────────────────┐ ┌─────────────────┐
│   C07 进程      │ │   C08 算法       │ │  C09 设计模式   │
│  Processes      │ │  Algorithms     │ │  Patterns       │
└─────────────────┘ └─────────────────┘ └─────────────────┘
                                                   │
                          ┌────────────────────────┘
                          │
          ┌───────────────┼───────────────┐
          │               │               │
          ▼               ▼               ▼
┌─────────────────┐ ┌─────────────────┐ ┌─────────────────┐
│   C10 网络       │ │   C11 宏系统     │ │   C12 WASM     │
│  Networking     │ │  Macros         │ │  WebAssembly    │
└─────────────────┘ └─────────────────┘ └─────────────────┘
```

---

## 🔗 核心依赖关系

### 基础层 (C01-C03)

| 模块 | 前置知识 | 后续影响 |
|------|----------|----------|
| C01 所有权 | 无 | C02, C05, C06, C07 |
| C02 类型系统 | C01 | C04, C11 |
| C03 控制流 | C02 | C05, C06, C08 |

### 进阶层 (C04-C06)

| 模块 | 前置知识 | 后续影响 | 关联 content/ |
|------|----------|----------|---------------|
| C04 泛型 | C01-C02 | C06, C09, C11 | content/emerging/ |
| C05 并发 | C01, C03 | C06, C07, C10 | content/ecosystem/ |
| C06 异步 | C03-C05 | C07, C10 | content/ecosystem/async_runtimes/ |

### 高级层 (C07-C12)

| 模块 | 前置知识 | 应用场景 | 关联 content/ |
|------|----------|----------|---------------|
| C07 进程 | C01, C05 | 系统编程 | content/production/ |
| C08 算法 | C03, C04 | 算法竞赛 | - |
| C09 设计模式 | C04, C06 | 架构设计 | content/scenarios/ |
| C10 网络 | C05, C06 | Web 开发 | content/ecosystem/web_frameworks/ |
| C11 宏系统 | C02, C04 | DSL 开发 | content/emerging/ |
| C12 WASM | C04, C06 | Web 应用 | content/production/ |

---

## 📚 交叉学习路径

### 路径 1: Web 开发

```
C01 → C02 → C03 → C04 → C06 ─┬─▶ C10 (网络) ───┬─▶ C12 (WASM)
                               │                 │
                               └─▶ content/ecosystem/web_frameworks/
                               └─▶ content/scenarios/web_app/
```

### 路径 2: 系统编程

```
C01 → C02 → C05 ─┬─▶ C07 (进程) ─────┬─▶ content/production/
                 └─▶ C10 (网络) ─────┘
```

### 路径 3: 高性能计算

```
C01 → C02 → C04 → C05 ─┬─▶ C08 (算法) ──┬─▶ C12 (WASM SIMD)
                       └─▶ C06 (异步) ──┘
```

### 路径 4: 元编程与 DSL

```
C01 → C02 → C04 ─▶ C11 (宏系统) ─▶ content/emerging/
```

---

## 🔄 模块间代码示例

### C01 → C05: 所有权与并发

```rust
// C05 中需要 C01 的所有权知识
use std::sync::Arc;
use std::thread;

let data = Arc::new(vec![1, 2, 3]);
let data_clone = Arc::clone(&data);

thread::spawn(move || {
    // 所有权转移到这里
    println!("{:?}", data_clone);
});
```

### C04 → C06: 泛型与异步

```rust
// C06 中大量使用 C04 的泛型
async fn process<T: Send + 'static>(data: T) -> T {
    // 异步处理泛型数据
    data
}
```

### C05 → C10: 并发与网络

```rust
// C10 基于 C05 的并发原语
tokio::spawn(async {
    // 异步网络操作
});
```

---

## 📖 文档交叉引用

### 思维表示 (docs/04_thinking/)

| 文档 | 覆盖模块 | 用途 |
|------|----------|------|
| MIND_MAP_COLLECTION.md | C01-C12 | 概念总览 |
| MULTI_DIMENSIONAL_CONCEPT_MATRIX.md | C04-C06 | 技术对比 |
| DECISION_TREES.md | C05-C10 | 选型决策 |

### 实用指南 (docs/05_guides/)

| 指南 | 主要模块 | 关联模块 |
|------|----------|----------|
| BEST_PRACTICES.md | C01-C06 | 全部 |
| DESIGN_PATTERNS_USAGE_GUIDE.md | C09 | C04, C06 |
| ASYNC_PROGRAMMING_USAGE_GUIDE.md | C06 | C05, C10 |
| FFI_PRACTICAL_GUIDE.md | C07 | C01, C12 |

### 前沿内容 (content/)

| 目录 | 关联 Crate | 内容 |
|------|------------|------|
| content/emerging/ | C04, C11 | Rust 1.95+ 特性 |
| content/ecosystem/ | C05, C06, C10 | 生态库 |
| content/production/ | C07, C12 | 部署实践 |
| content/academic/ | C01, C04 | 形式化方法 |

---

## 🎯 快速导航

### 按主题查找

| 主题 | 起始模块 | 深入模块 | 实践内容 |
|------|----------|----------|----------|
| 内存安全 | C01 | C02, C04 | content/academic/ |
| 并发编程 | C05 | C06, C07 | content/ecosystem/ |
| Web 开发 | C06 | C10, C12 | content/scenarios/ |
| 性能优化 | C08 | C05, C06 | content/production/ |
| 元编程 | C04 | C11 | content/emerging/ |

### 按难度查找

| 难度 | 模块 | 预计时间 |
|------|------|----------|
| 初级 | C01-C03 | 2-3 周 |
| 中级 | C04-C06 | 3-4 周 |
| 高级 | C07-C12 | 4-6 周 |
| 专家 | content/ | 持续 |

---

## 📝 贡献指南

添加新的交叉引用:

1. 在相关模块的 README.md 中添加链接
2. 更新本文档
3. 确保链接有效性

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-03-15
**状态**: ✅ 100% 完成
