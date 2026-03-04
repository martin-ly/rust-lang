# 设计模式选择决策树

## 交互式决策流程

```text
开始选择设计模式
        │
        ▼
┌─────────────────┐
│ 需要创建复杂对象? │
└────────┬────────┘
         │
    ┌────┴────┐
    ▼         ▼
   是         否
    │         │
    ▼         ▼
┌─────────┐ ┌─────────────────┐
│Builder  │ │需要对象间行为解耦?│
│模式     │ └────────┬────────┘
└─────────┘          │
                ┌────┴────┐
                ▼         ▼
               是         否
                │         │
                ▼         ▼
        ┌───────────┐ ┌─────────────────┐
        │Strategy或  │ │需要共享所有权?    │
        │Command模式 │ └────────┬────────┘
        └───────────┘          │
                            ┌────┴────┐
                            ▼         ▼
                           是         否
                            │         │
                            ▼         ▼
                    ┌───────────┐ ┌─────────────────┐
                    │Rc/Arc     │ │需要跨线程共享?    │
                    │模式       │ └────────┬────────┘
                    └───────────┘          │
                                        ┌────┴────┐
                                        ▼         ▼
                                       是         否
                                        │         │
                                        ▼         ▼
                                ┌───────────┐ ┌───────────┐
                                │Arc<Mutex> │ │Channel或  │
                                │模式       │ │Cell/      │
                                └───────────┘ │RefCell模式│
                                              └───────────┘
```

---

## 模式分类决策树

### 1. 对象创建

```text
对象创建需求
      │
      ├──▶ 需要多个配置选项? ──▶ 是 ──▶ Builder模式
      │                          否
      │                          ▼
      │                     需要运行时多态? ──▶ 是 ──▶ Factory模式
      │                                          否
      │                                          ▼
      │                                     需要类型转换? ──▶ 是 ──▶ Into/From模式
      │                                                      否
      │                                                      ▼
      │                                                 直接构造即可
      │
      └──▶ 需要单例? ──▶ 是 ──▶ OnceCell/LazyLock模式
                        否
                        ▼
                   需要池化? ──▶ 是 ──▶ Pool模式
                                  否
                                  ▼
                             标准new()
```

### 2. 并发模式

```text
并发需求
      │
      ├──▶ 需要共享可变状态? ──▶ 是 ──▶ 需要跨线程? ──▶ 是 ──▶ Arc<Mutex<T>>
      │                          否                    否
      │                          ▼                     ▼
      │                     消息传递优先              RefCell<T>
      │                          │
      │                          ▼
      │                     Channel模式
      │
      └──▶ 需要异步? ──▶ 是 ──▶ 需要组合多个Future? ──▶ 是 ──▶ select!/join!
                        否                          否
                        ▼                           ▼
                   同步并发                      async/await

                        ┌──────────────┬──────────────┐
                        │              │              │
                        ▼              ▼              ▼
                   需要锁?         无锁?         原子操作?
                        │              │              │
                        ▼              ▼              ▼
                   Mutex/RwLock   Crossbeam      AtomicUsize
                   (阻塞)          (Lock-free)     (CAS)
```

### 3. 错误处理模式

```text
错误处理需求
      │
      ├──▶ 可恢复错误? ──▶ 是 ──▶ 需要传递错误上下文? ──▶ 是 ──▶ anyhow/thiserror
      │                          否                    否
      │                          ▼                     ▼
      │                     panic!                  Result<T, E>
      │                          │
      │                          ▼
      │                     自定义Error类型
      │
      └──▶ 需要枚举错误类型? ──▶ 是 ──▶ 使用enum定义错误
                        否
                        ▼
                   使用标准Error类型
```

---

## 快速选择表

| 问题 | 答案 | 推荐模式 |
|:---|:---|:---|
| 需要逐步构造对象? | 是 | Builder |
| 需要类型转换? | 是 | Into/From |
| 需要运行时多态? | 是 | Trait对象 / enum |
| 需要共享不可变? | 是 | `Rc<T> / Arc<T>` |
| 需要可变共享? | 是 | `RefCell<T> / Mutex<T>` |
| 需要跨线程共享? | 是 | Arc<...> |
| 需要消息传递? | 是 | Channel |
| 需要类型状态? | 是 | 类型状态模式 |
| 需要自引用? | 是 | Pin<Box<...>> |
| 需要零成本抽象? | 是 | Newtype + PhantomData |

---

## 模式组合建议

### 常见组合

```rust
// Builder + TypeState
UserBuilder::new()
    .name("Alice")  // returns UserBuilder<HasName>
    .email("a@b.c") // returns UserBuilder<HasName, HasEmail>
    .build();       // only compiles with all required fields

// Arc<Mutex<T>> + Drop
struct SharedState {
    data: Arc<Mutex<Vec<u8>>>,
}

impl Drop for SharedState {
    fn drop(&mut self) {
        // 自动清理
    }
}

// Channel + Select
select! {
    msg = rx1.recv() => handle_msg(msg),
    sig = signal_rx.recv() => handle_signal(sig),
    _ = timeout => handle_timeout(),
}
```

---

**维护者**: Rust Design Patterns Team
**更新日期**: 2026-03-05
