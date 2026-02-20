# Rust 与 C++/Go/Python 跨语言对比

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-12
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **用途**: 技术选型、迁移参考、概念对标

---

## 目录

- [Rust 与 C++/Go/Python 跨语言对比](#rust-与-cgopython-跨语言对比)
  - [目录](#目录)
  - [内存管理](#内存管理)
  - [并发模型](#并发模型)
  - [错误处理](#错误处理)
  - [类型系统](#类型系统)
  - [生态与工具链](#生态与工具链)
  - [相关文档](#相关文档)

---

## 内存管理

| 维度 | Rust | C++ | Go | Python |
| :--- | :--- | :--- | :--- | :--- || 模型 | 所有权 + 借用 | 手动/智能指针/RAII | GC | GC |
| 安全 | 编译期保证 | 依赖程序员 | 运行时 GC | 运行时 GC |
| 零成本 | 是 | 可选 | 否 | 否 |
| 学习曲线 | 高 | 高 | 低 | 低 |

---

## 并发模型

| 维度 | Rust | C++ | Go | Python |
| :--- | :--- | :--- | :--- | :--- || 线程 | std::thread | std::thread | goroutine | threading |
| 异步 | async/await | 库（如 asio） | go/chan | asyncio |
| 数据竞争 | 编译期禁止 | 需手动同步 | 通道优先 | GIL 限制 |
| 推荐 | 所有权 + Send/Sync | 各显其能 | CSP/goroutine | 多进程/asyncio |

---

## 错误处理

| 维度 | Rust | C++ | Go | Python |
| :--- | :--- | :--- | :--- | :--- || 机制 | Result/Option | 异常/error_code | error 返回值 | 异常 |
| 必须处理 | 是（编译期） | 否 | 习惯性 | 否 |
| 传播 | ? 操作符 | throw/catch | if err | raise |

---

## 类型系统

| 维度 | Rust | C++ | Go | Python |
| :--- | :--- | :--- | :--- | :--- || 类型 | 静态强类型 | 静态强类型 | 静态（少泛型） | 动态 |
| 泛型 | 单态化 | 模板 | 1.18+ 泛型 | 不适用 |
| 推断 | 强 | 有 | 有 | 无 |

---

## 生态与工具链

| 维度 | Rust | C++ | Go | Python |
| :--- | :--- | :--- | :--- | :--- || 包管理 | Cargo | vcpkg/conan | go mod | pip |
| 构建 | cargo build | CMake/MSBuild | go build | 无统一 |
| 文档 | rustdoc | Doxygen | godoc | Sphinx |

---

## 相关文档

- [多维概念矩阵](./MULTI_DIMENSIONAL_CONCEPT_MATRIX.md)
- [应用分析视图](./APPLICATIONS_ANALYSIS_VIEW.md)
