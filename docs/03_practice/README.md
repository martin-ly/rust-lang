# 03 实践与练习 (Practice)

> 动手实践 Rust 编程的最佳场所

---

## 📂 目录结构

```
03_practice/
├── README.md                   # 本文件
├── exercises_by_topic/         # 按主题分类的练习
├── mini_projects/              # 迷你项目
└── code_challenges/            # 代码挑战
```

---

## 🎯 练习分类

### 基础练习 (C01-C03)

| 模块 | 练习 | 难度 | 预计时间 |
|------|------|------|----------|
| C01 所有权 | [借用检查器练习](../crates/c01_ownership/exercises/01_borrow_checker.md) | ⭐⭐ | 30分钟 |
| C02 类型系统 | [类型技巧](../crates/c02_type_system/exercises/01_type_tricks.rs) | ⭐⭐ | 45分钟 |
| C03 控制流 | [模式匹配](../crates/c03_control_flow/exercises/01_pattern_matching.rs) | ⭐⭐ | 40分钟 |

### 进阶练习 (C04-C06)

| 模块 | 练习 | 难度 | 预计时间 |
|------|------|------|----------|
| C04 泛型 | GAT 模式实现 | ⭐⭐⭐ | 60分钟 |
| C05 并发 | 线程池实现 | ⭐⭐⭐⭐ | 90分钟 |
| C06 异步 | Future 组合器 | ⭐⭐⭐⭐ | 75分钟 |

### 高级项目 (C07-C12)

| 模块 | 项目 | 难度 | 预计时间 |
|------|------|------|----------|
| C07 进程 | 迷你 Shell | ⭐⭐⭐ | 2小时 |
| C08 算法 | 排序算法可视化 | ⭐⭐⭐⭐ | 3小时 |
| C09 设计模式 | 类型状态机 | ⭐⭐⭐⭐ | 2.5小时 |
| C10 网络 | HTTP 客户端 | ⭐⭐⭐⭐ | 3小时 |
| C11 宏系统 | 派生宏实现 | ⭐⭐⭐⭐⭐ | 4小时 |
| C12 WASM | 浏览器计算器 | ⭐⭐⭐⭐ | 3小时 |

---

## 🚀 快速开始

### 运行练习

```bash
# 运行特定练习
cargo test --package c02_type_system -- exercises::type_tricks

# 运行所有测试
cargo test --workspace
```

### 提交解答

将解答放在 `exercises_by_topic/` 目录下相应位置。

---

## 📚 学习建议

1. **先阅读理论**: 完成 crates 中的文档学习
2. **动手实践**: 独立完成练习，不先看答案
3. **代码审查**: 对比参考答案，理解差异
4. **扩展思考**: 思考如何改进或扩展练习

---

## 🔗 相关资源

- [C01-C12 学习模块](../crates/)
- [最佳实践指南](../05_guides/BEST_PRACTICES.md)
- [设计模式](../05_guides/DESIGN_PATTERNS_USAGE_GUIDE.md)

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-03-15
