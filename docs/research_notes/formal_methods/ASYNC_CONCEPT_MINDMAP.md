# 异步编程概念思维导图

> **创建日期**: 2026-02-24
> **最后更新**: 2026-02-28
> **状态**: ✅ 已扩展
> **版本**: Rust 1.93.0+ (Edition 2024)

---

## 异步编程全景

```mermaid
mindmap
  root((异步编程<br/>Async Rust))
    核心概念
      Future
        状态机表示
        Poll机制
        Pin固定
      async/await
        语法糖
        状态机转换
        挂起点
      Executor
        任务调度
        事件循环
        Work Stealing
      Waker
        唤醒机制
        通知Executor
        回调注册
    类型系统
      Future Trait
        fn poll()
        Pin<&mut Self>
        Context<'_>
      Send/Sync边界
        async Send
        跨线程约束
      生命周期
        'static Future
        借用限制
    执行模型
      单线程
        LocalSet
        !Send Future
        局部任务
      多线程
        Send Future
        Work Stealing
        线程池
      混合模式
        spawn_local
        spawn
        组合使用
    同步原语
      Mutex
        tokio::sync::Mutex
        跨await保持
        注意事项
      RwLock
        多读单写
        异步兼容
      Channel
        mpsc
        oneshot
        broadcast
      Semaphore
        并发限制
        信号量获取
    组合操作
      join!
        并行执行
        全部完成
      select!
        竞赛模式
        首个完成
      try_join!
        短路错误
      timeout
        超时控制
    运行时
      Tokio
        功能最全
        生态丰富
        生产级
      async-std
        标准库风格
        简洁API
      smol
        轻量级
        嵌入式友好
      embassy
        嵌入式
        no_std支持
    陷阱与模式
      跨越await持有锁
        阻塞executor
        解决方案
      递归async
        编译错误
        间接递归
      自我引用
        Pin需求
        状态机
      取消安全
        优雅关闭
        资源清理
    与同步对比
      性能
        内存效率
        上下文切换
      可扩展性
        高并发
        资源利用
      复杂度
        学习曲线
        调试难度
```

---

## 核心概念详解

### Future 状态机

```rust
// async fn 编译后的状态机
enum MyAsyncFn {
    Start,
    Waiting1 { /* 状态 */ },
    Waiting2 { /* 状态 */ },
    Done,
}

impl Future for MyAsyncFn {
    type Output = T;

    fn poll(self: Pin<&mut Self>, cx: &mut Context) -> Poll<T> {
        loop {
            match self.state {
                Start => { /* 初始化 */ }
                Waiting1 => { /* 检查完成 */ }
                Waiting2 => { /* 检查完成 */ }
                Done => return Poll::Ready(value),
            }
        }
    }
}
```

### 执行流程

```
┌──────────┐     ┌──────────┐     ┌──────────┐
│  创建    │────>│  Poll    │────>│ Pending  │
│  Future  │     │  首次    │     │ 注册Waker│
└──────────┘     └──────────┘     └────┬─────┘
                                       │
                              I/O完成/Waker唤醒
                                       │
                                       ▼
┌──────────┐     ┌──────────┐     ┌──────────┐
│  完成    │<────│ Poll::   │<────│  再次    │
│ 返回值   │     │ Ready    │     │  Poll    │
└──────────┘     └──────────┘     └──────────┘
```

---

## 类型系统关联

### Future Trait 定义

```rust
trait Future {
    type Output;
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output>;
}

enum Poll<T> {
    Ready(T),
    Pending,
}
```

### Send边界规则

| 场景 | Future: Send? | 条件 |
| :--- | :--- | :--- |
| 纯计算 | ✅ | 无跨线程数据 |
| 持有`Rc` | ❌ | `Rc`非Send |
| 持有`Arc` | ✅ | `Arc<T: Send>` |
| 持有`&mut T` | ✅(T: Send) | 独占引用 |
| 使用`tokio::sync::Mutex` | ✅ | MutexGuard跨await |

---

## 同步原语对比

| 原语 | 同步版本 | 异步版本 | 关键区别 |
| :--- | :--- | :--- | :--- |
| Mutex | `std::sync::Mutex` | `tokio::sync::Mutex` | 异步版本可跨await |
| RwLock | `std::sync::RwLock` | `tokio::sync::RwLock` | 异步兼容 |
| Channel | `std::sync::mpsc` | `tokio::sync::mpsc` | 异步send/recv |
| Semaphore | - | `tokio::sync::Semaphore` | 纯异步 |
| Barrier | `std::sync::Barrier` | `tokio::sync::Barrier` | 异步等待 |

### 跨await持有锁的危险

```rust
// ❌ 危险: 锁guard跨越await
async fn bad() {
    let guard = mutex.lock().unwrap();
    some_async_op().await; // 锁在整个await期间持有
    // 其他任务无法获取锁
}

// ✅ 正确: 锁在await前释放
async fn good() {
    {
        let guard = mutex.lock().unwrap();
        // 使用guard
    } // 锁在这里释放
    some_async_op().await;
}

// ✅ 更好: 使用异步Mutex
async fn better() {
    let guard = async_mutex.lock().await;
    some_async_op().await; // OK: 异步Mutex支持
}
```

---

## 组合操作详解

### join! - 并行等待

```rust
use tokio::join;

async fn fetch_data() {
    let (user, order, config) = join!(
        fetch_user(),
        fetch_order(),
        fetch_config(),
    );
    // 全部完成后继续
}
```

### select! - 竞赛等待

```rust
use tokio::select;

async fn race() {
    select! {
        result = task1() => {
            println!("task1完成: {:?}", result);
        }
        result = task2() => {
            println!("task2完成: {:?}", result);
        }
        _ = tokio::time::sleep(Duration::from_secs(5)) => {
            println!("超时!");
        }
    }
}
```

### 取消安全

```rust
// ❌ 非取消安全: 操作可能部分完成
async fn not_cancellation_safe() {
    file.write(b"header").await?;
    // 如果在这里被取消，文件处于不一致状态
    file.write(b"body").await?;
}

// ✅ 取消安全: 使用临时文件+原子重命名
async fn cancellation_safe() {
    let mut temp = File::create("temp").await?;
    temp.write(b"header").await?;
    temp.write(b"body").await?;
    drop(temp);
    tokio::fs::rename("temp", "final").await?;
}
```

---

## 运行时对比

| 特性 | Tokio | async-std | smol | embassy |
| :--- | :--- | :--- | :--- | :--- |
| 成熟度 | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐ |
| 功能丰富度 | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐ |
| 性能 | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ |
| 内存占用 | 中 | 中 | 低 | 极低 |
| 生态支持 | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐ |
| no_std | ❌ | ❌ | ❌ | ✅ |
| 嵌入式 | ❌ | ❌ | 部分 | ✅ |

---

## 与形式化方法关联

| 概念 | 形式化定义 | 相关定理 |
| :--- | :--- | :--- |
| Future | `trait Future { type Output; fn poll(...) -> Poll<Output>; }` | T-ASYNC |
| Pin | `Pin<P>: Deref` 保证位置稳定 | PIN-T1 |
| Waker | 唤醒条件的信号机制 | ASYNC-T2 |
| Executor | 任务调度算法的正确性 | ASYNC-T3 |

---

## 最佳实践清单

```markdown
□ 选择合适的运行时(Tokio用于生产)
□ 使用异步版本的同步原语
□ 避免跨越await持有std锁
□ 确保操作是取消安全的
□ 合理使用spawn进行并行
□ 注意Send边界约束
□ 使用timeout防止永久等待
□ 处理select!中的取消分支
```

---

## 概念层次结构

```text
                            异步编程概念
                                 │
            ┌────────────────────┼────────────────────┐
            │                    │                    │
       【核心概念】          【执行模型】          【关键抽象】
            │                    │                    │
    ┌───────┴───────┐    ┌───────┴───────┐    ┌───────┴───────┐
    │               │    │               │    │               │
  Future        async  轮询驱动         事件循环   Pin           Waker
    │            await   │               │      │               │
  ├─Pending       ├─挂起  ├─Poll          ├─调度  ├─固定内存地址   ├─唤醒机制
  ├─Ready         ├─恢复  ├─Ready         ├─回调  └─自引用结构     └─通知执行器
  └─State Machine └─状态机 └─Waker传递     └─驱动
```

---

## 核心概念详解

### Future trait

```rust
pub trait Future {
    type Output;
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output>;
}
```

| 状态 | 含义 | 图示 |
| :--- | :--- | :--- |
| `Pending` | 未完成，等待中 | ⏳ |
| `Ready(T)` | 已完成，返回值 | ✅ |

---

## 执行器生态

```text
执行器选择
├── tokio
│   ├── 多线程调度
│   ├── 网络/IO集成
│   └── 生产环境首选
│
├── async-std
│   ├── 标准库API风格
│   └── 简洁接口
│
└── smol
    ├── 轻量级
    └── 嵌入式友好
```

---

## Pin与自引用

```text
Pin<P<T>>
├── 保证内存位置不变
├── 支持自引用结构
└── 与Unpin trait配合
```

| 类型 | 是否Unpin | 需要Pin |
| :--- | :--- | :--- |
| 普通类型 | 是 | 否 |
| 自引用结构 | 否 | 是 |

---

## 与其他概念的关系

```text
异步编程
├── 借用检查 → Future lifetime约束
├── 所有权 → async move / async &self
├── Send/Sync → 跨线程任务调度
└── 并发 → 并行执行多个Future
```

---

## 学习路径

1. **L1**: 理解`async/await`语法
2. **L2**: 掌握`Pin<Waker>`机制
3. **L3**: 实现自定义Future

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-28
**状态**: ✅ 已扩展 - 异步编程概念思维导图完整版
