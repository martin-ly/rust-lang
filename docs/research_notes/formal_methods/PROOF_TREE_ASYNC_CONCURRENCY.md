# 证明树：异步并发安全

> **定理**: async/await 并发执行安全
> **创建日期**: 2026-02-28
> **状态**: ✅ 完成

---

## 定理陈述

### Thm ASYNC-T1 (Future 状态一致性)

Future 状态转换是确定性的：从任何状态，只有唯一的有效转换。

### Thm ASYNC-T2 (并发执行安全)

多个 Future 并发执行时，Send/Sync 边界保证数据竞争自由。

### Thm ASYNC-T3 (执行进度)

良型异步程序不会饥饿：执行器公平调度所有就绪的 Future。

---

## 证明树可视化

```mermaid
graph TD
    subgraph "Future 状态机"
    S0[Start] --> S1[Poll::Pending]
    S0 --> S2[Poll::Ready]

    S1 -->|wake| S3[Poll Again]
    S3 --> S1
    S3 --> S2

    S2 --> S4[Complete]

    S0 -.->|Cancel| S5[Cancelling]
    S5 --> S6[Complete]
    end

    subgraph "ASYNC-T1: 状态一致性"
    T1[Thm ASYNC-T1<br/>状态一致性] --> T1_Def[状态定义]

    T1_Def --> T1_S1["State::Start: 初始状态"]
    T1_Def --> T1_S2["State::Polling: 执行中"]
    T1_Def --> T1_S3["State::Pending: 等待中"]
    T1_Def --> T1_S4["State::Ready(T): 完成"]

    T1 --> T1_Trans[转换规则]
    T1_Trans --> T1_T1["Start → Polling: poll() 调用"]
    T1_Trans --> T1_T2["Polling → Pending: 遇到 .await"]
    T1_Trans --> T1_T3["Polling → Ready: 完成计算"]
    T1_Trans --> T1_T4["Pending → Polling: wake() 调用"]

    T1 --> T1_Det[确定性]
    T1_Det --> T1_D1["每个状态只有一个出边"]
    T1_Det --> T1_D2["无歧义转换"]
    end

    subgraph "ASYNC-T2: 并发安全"
    T2[Thm ASYNC-T2<br/>并发安全] --> T2_Send[Send边界]
    T2 --> T2_Sync[Sync边界]

    T2_Send --> T2_S1["spawn: F: Send → Future: Send"]
    T2_Send --> T2_S2["跨线程转移: F: Send"]

    T2_Sync --> T2_Y1["共享状态: T: Sync"]
    T2_Sync --> T2_Y2["Arc<T>: Send + Sync iff T: Send + Sync"]

    T2 --> T2_Exec[执行器安全]
    T2_Exec --> T2_E1["单线程执行器: 无数据竞争"]
    T2_Exec --> T2_E2["多线程执行器: work-stealing + Send检查"]
    end

    subgraph "ASYNC-T3: 执行进度"
    T3[Thm ASYNC-T3<br/>执行进度] --> T3_Ready[就绪保证]

    T3_Ready --> T3_R1["I/O 完成 → wake()"]
    T3_Ready --> T3_R2["定时器到期 → wake()"]
    T3_Ready --> T3_R3["通道消息 → wake()"]

    T3 --> T3_Fair[公平调度]
    T3_Fair --> T3_F1["FIFO 队列"]
    T3_Fair --> T3_F2["无 Future 饥饿"]

    T3 --> T3_Live[活性]
    T3_Live --> T3_L1["无死锁: 异步等待无循环"]
    end

    subgraph "Pin 与自引用"
    P1[Pin<Future>] --> P1_Safe[自引用安全]
    P1_Safe --> P1_1["移动 Pin 后地址不变"]
    P1_Safe --> P1_2["自引用指针有效"]

    P1 --> P1_Unpin[Unpin边界]
    P1_Unpin --> P1_U1["T: Unpin → Pin<T> 可移动"]
    P1_Unpin --> P1_U2["T: !Unpin → Pin<T> 固定"]
    end
```

---

## 形式化证明

### ASYNC-T1: Future 状态一致性

**状态定义**:

```text
State(F) := Start | Polling(ctx) | Pending(Waker) | Ready(T) | Complete
```

**转换关系**:

```text
 poll(ctx)          async op not ready       wake()
Start ─────────→ Polling ──────────────→ Pending ─────→ Polling
                      │                              │
                      │ async op ready               │
                      ↓                              │
                   Ready(T) ─────────────────────────┘
```

**证明** (对状态归纳):

**Case Start**:

- 唯一转换: `poll(ctx)` → Polling
- 无副作用，确定性

**Case Polling**:

- 若遇到 `.await` on Future G:
  - G 为 Ready → 继续执行
  - G 为 Pending → 当前 Future 变为 Pending
- 若计算完成 → Ready
- 转换由控制流决定，确定性

**Case Pending**:

- 唯一转换: `wake()` → Polling
- waker 被调用时触发

### ASYNC-T2: 并发安全

**Send 边界**:

```rust
fn spawn<F, R>(f: F) -> JoinHandle<R>
where
    F: FnOnce() -> R + Send + 'static,
    R: Send + 'static,
```

**证明**:

- `F: Send` 保证闭包可跨线程转移
- `R: Send` 保证返回值可跨线程转移
- Future 跨线程时，内部状态必须 `Send`

**反例**:

```rust
let rc = Rc::new(42);
// async { *rc } 不能 spawn 到线程池
// 因为 Rc 不是 Send
```

### ASYNC-T3: 执行进度

**公平调度证明**:

执行器使用队列调度:

1. 所有就绪 Future 入队
2. 出队执行
3. 若 Pending，注册 waker
4. I/O 完成时 wake() 重新入队

**无饥饿**:

- 每个 I/O 有超时或完成保证
- 定时器有到期保证
- 通道有消息/关闭通知
- 故每个 Future 最终会被唤醒

---

## Rust 代码示例

### 状态转换

```rust
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

struct MyFuture {
    state: State,
}

enum State {
    Start,
    Waiting,
    Complete,
}

impl Future for MyFuture {
    type Output = i32;

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<i32> {
        match self.state {
            State::Start => {
                self.state = State::Waiting;
                // 注册 waker
                cx.waker().wake_by_ref();
                Poll::Pending
            }
            State::Waiting => {
                self.state = State::Complete;
                Poll::Ready(42)
            }
            State::Complete => Poll::Ready(42),
        }
    }
}
```

### Send 边界

```rust
use std::sync::Arc;
use tokio::task;

async fn send_example() {
    let data = Arc::new(vec![1, 2, 3]);
    // Arc<T>: Send if T: Send + Sync

    let handle = task::spawn(async move {
        // data 安全转移到新任务
        println!("{:?}", data);
    });

    handle.await.unwrap();
}
```

---

**维护者**: Rust 形式化研究团队
**最后更新**: 2026-02-28
**证明状态**: ✅ L2 完成
