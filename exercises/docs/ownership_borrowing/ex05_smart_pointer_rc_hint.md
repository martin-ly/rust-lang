# 提示: Rc 智能指针共享所有权

Rc::clone 不会深拷贝数据，只是增加引用计数。使用 Rc::strong_count 查看计数。

## 相关阅读

- 项目内对应模块: `crates/` 下的相关源码
- 速查卡: `docs/02_reference/quick_reference/`
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
