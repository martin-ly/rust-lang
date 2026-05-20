# 所有权系统设计决策树

## 1. 智能指针选择决策树
> **[来源: Rust Official Docs]**

```text
开始
│
├─► 需要共享所有权？
│   ├─ 是 ─► 需要跨线程？
│   │         ├─ 是 ─► Arc<T>
│   │         └─ 否 ─► Rc<T>
│   └─ 否 ─► 需要可变性？
│             ├─ 是 ─► 需要运行时检查？
│             │         ├─ 是 ─► RefCell<T>
│             │         └─ 否 ─► Box<T> + &mut T
│             └─ 否 ─► Box<T> / &T
│
```

## 2. 并发策略决策树
> **[来源: Rust Official Docs]**

```text
数据并发策略
│
├─► 数据所有权是否转移？
│   ├─ 是 ─► 使用 move + spawn
│   └─ 否 ─► 需要可变访问？
│             ├─ 是 ─► 互斥访问？
│             │         ├─ 是 ─► Mutex<T>
│             │         └─ 否 ─► 考虑设计重构
│             └─ 否 ─► 只读共享？
│                       ├─ 是 ─► Arc<T> 或 静态生命周期
│                       └─ 否 ─► 通道 (mpsc/oneshot)
│
```

## 3. 错误处理决策树
> **[来源: Rust Official Docs]**

```text
错误处理策略
│
├─► 错误是否可恢复？
│   ├─ 是 ─► 使用 Result<T, E>
│   │         ├─ 需要传播？ ─► ? 运算符
│   │         └─ 需要转换？ ─► map_err
│   └─ 否 ─► 程序Bug？
│             ├─ 是 ─► panic! + unwrap/expect
│             └─ 否 ─► unreachable! / todo!
│
```

## 4. 生命周期标注决策

```text
是否需要标注生命周期？
│
├─► 函数有引用参数？
│   ├─ 否 ─► 无需标注
│   ├─ 是 ─► 返回引用？
│   │         ├─ 是 ─► 参数有多个？
│   │         │         ├─ 是 ─► 必须标注
│   │         │         └─ 否 ─► 推断即可
│   │         └─ 否 ─► 推断即可
│   └─ 结构体含引用？
│       ├─ 是 ─► 必须标注
│       └─ 否 ─► 推断即可
```
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
