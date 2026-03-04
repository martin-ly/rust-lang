# Embassy异步嵌入式运行时形式化分析

> **主题**: 嵌入式异步运行时
> **形式化框架**: async/await + 无分配 + 任务调度
> **参考**: Embassy Documentation (<https://embassy.dev>)

---

## 目录

- [Embassy异步嵌入式运行时形式化分析](#embassy异步嵌入式运行时形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 核心概念形式化](#2-核心概念形式化)
    - [定义 EMB-1 ( Embassy Spawner )](#定义-emb-1--embassy-spawner-)
    - [定义 EMB-2 ( Embassy Executor )](#定义-emb-2--embassy-executor-)
  - [3. 任务模型形式化](#3-任务模型形式化)
    - [定义 TASK-1 ( Embassy任务 )](#定义-task-1--embassy任务-)
    - [定义 TASK-2 ( 任务入口宏 )](#定义-task-2--任务入口宏-)
    - [定理 TASK-T1 ( 任务静态分配 )](#定理-task-t1--任务静态分配-)
  - [4. Executor形式化](#4-executor形式化)
    - [定义 EXEC-1 ( 轮询语义 )](#定义-exec-1--轮询语义-)
    - [定义 EXEC-2 ( Waker机制 )](#定义-exec-2--waker机制-)
    - [定理 EXEC-T1 ( 单线程安全 )](#定理-exec-t1--单线程安全-)
  - [5. 时间驱动形式化](#5-时间驱动形式化)
    - [定义 TIMER-1 ( Embassy定时器 )](#定义-timer-1--embassy定时器-)
    - [定义 TIMER-2 ( 低功耗等待 )](#定义-timer-2--低功耗等待-)
    - [定理 TIMER-T1 ( 时间准确性 )](#定理-timer-t1--时间准确性-)
  - [6. 定理与证明](#6-定理与证明)
    - [定理 EMB-T1 ( 无堆安全 )](#定理-emb-t1--无堆安全-)
    - [定理 EMB-T2 ( 中断安全 )](#定理-emb-t2--中断安全-)
    - [定理 EMB-T3 ( 优先级继承 )](#定理-emb-t3--优先级继承-)
  - [7. 代码示例](#7-代码示例)
    - [示例1: 基本任务](#示例1-基本任务)
    - [示例2: 通道通信](#示例2-通道通信)
    - [示例3: 中断集成](#示例3-中断集成)
    - [示例4: 多Executor核心](#示例4-多executor核心)
  - [8. 与标准async对比](#8-与标准async对比)

---

## 1. 引言

Embassy是针对嵌入式系统的异步运行时，特点：

- 无堆分配（no_alloc）
- 零成本任务切换
- 编译时任务声明
- 集成硬件中断

---

## 2. 核心概念形式化

### 定义 EMB-1 ( Embassy Spawner )

Spawner负责任务的生命周期管理。

$$
\text{Spawner} = \{ \text{spawn} : \text{Task} \to \text{Result<(), SpawnError>} \}
$$

**类型规则**:

```rust
#[embassy_executor::task]
async fn task1() { ... }

// spawner.spawn(task1()) 的类型规则
Γ ⊢ task : impl Future<Output = ()>
Γ ⊢ spawner : Spawner
─────────────────────────────── (EMB-1)
Γ ⊢ spawner.spawn(task) : Result<(), SpawnError>
```

### 定义 EMB-2 ( Embassy Executor )

Executor是单线程异步任务调度器。

$$
\text{Executor} = (\text{run_queue} : \text{Queue}<\text{Task}>, \text{timer_queue} : \text{TimerQueue})
$$

**状态转换**:

$$
\text{Executor} \xrightarrow{\text{poll ready task}} \text{Executor}'
$$

---

## 3. 任务模型形式化

### 定义 TASK-1 ( Embassy任务 )

Embassy任务是编译时静态分配的Future。

$$
\text{EmbassyTask} = \{
    \text{future} : \text{impl Future}<\text{Output} = ()>,
    \text{state} : \{ \text{Running}, \text{Sleeping}, \text{Done} \}
\}
$$

### 定义 TASK-2 ( 任务入口宏 )

`#[embassy_executor::main]`宏创建入口点和Executor。

```rust
#[embassy_executor::main]
async fn main(spawner: Spawner) {
    // main是异步的，由embassy executor驱动
}
```

**形式化**:

$$
\text{main} : \text{Spawner} \to \text{impl Future} \equiv \text{Executor}.\text{run}(\text{main})
$$

### 定理 TASK-T1 ( 任务静态分配 )

Embassy任务在编译时分配内存，无运行时分配失败风险。

$$
\forall t : \text{EmbassyTask}.\ \text{size}(t) \in \text{CompileTimeConst}
$$

**证明**:

1. `#[embassy_executor::task]`宏展开时计算任务栈大小
2. 使用`static`存储任务状态
3. 运行时只需初始化，无需分配
4. 因此内存使用在编译时确定 ∎

---

## 4. Executor形式化

### 定义 EXEC-1 ( 轮询语义 )

Executor轮询就绪任务。

$$
\text{poll_cycle}(E) = \begin{cases}
\text{poll}(\text{next\_ready}(E)) & \text{if } \exists t \in E.\ t.\text{state} = \text{Ready} \\
\text{sleep\_until\_interrupt}() & \text{otherwise}
\end{cases}
$$

### 定义 EXEC-2 ( Waker机制 )

任务通过Waker通知就绪。

$$
\text{Waker}_{\text{embassy}} : \text{TaskId} \to \text{enqueue}(\text{run\_queue})
$$

### 定理 EXEC-T1 ( 单线程安全 )

Embassy Executor是单线程的，无需同步原语。

$$
\forall E : \text{Executor}.\ \text{single\_threaded}(E) \rightarrow \neg\exists \text{race\_condition}
$$

**推论**: 无需`Send` bound，闭包可以捕获`!Send`类型。

---

## 5. 时间驱动形式化

### 定义 TIMER-1 ( Embassy定时器 )

```rust
Timer::after(Duration::from_millis(100)).await;
```

**形式化**:

$$
\text{Timer}::\text{after}(d) : \text{Duration} \to \text{Future} \text{ that resolves at } t_0 + d
$$

### 定义 TIMER-2 ( 低功耗等待 )

$$
\text{sleep\_low\_power}(d) = \begin{cases}
\text{set\_alarm}(t_0 + d) \\
\text{enter\_sleep\_mode}() \\
\text{wake\_on\_alarm\_or\_interrupt}()
\end{cases}
$$

### 定理 TIMER-T1 ( 时间准确性 )

定时器在轮询周期内触发。

$$
\forall \tau : \text{Timer}.\ \text{poll}(\tau, t) \rightarrow t \in [\tau.\text{deadline}, \tau.\text{deadline} + \epsilon]
$$

其中$\epsilon$是轮询延迟。

---

## 6. 定理与证明

### 定理 EMB-T1 ( 无堆安全 )

使用`embassy-executor`的no_alloc特性，保证无堆分配。

$$
\text{Embassy}_{\text{no\_alloc}} \vdash \neg\exists \text{heap\_allocation}
$$

**证明**:

- 任务栈静态分配
- 通道使用固定大小的环形缓冲区
- 无动态类型创建
- 所有内存需求在编译时确定 ∎

### 定理 EMB-T2 ( 中断安全 )

Embassy与中断处理程序正确交互。

$$
\forall \text{ISR}.\ \text{ISR} \to \text{signal\_waker} \to \text{executor\_poll} \text{ is safe}
$$

**机制**:

- 中断只设置原子标志或信号Waker
- 实际工作在Executor上下文中执行
- 避免中断中的复杂逻辑

### 定理 EMB-T3 ( 优先级继承 )

Embassy支持任务优先级，高优先级任务优先执行。

$$
\forall t_1, t_2 : \text{Task}.\ p(t_1) > p(t_2) \to \text{poll}(t_1) \prec \text{poll}(t_2)
$$

---

## 7. 代码示例

### 示例1: 基本任务

```rust
use embassy_executor::Spawner;
use embassy_time::{Duration, Timer};

# [embassy_executor::task]
async fn blinky(led: &'static mut Led) {
    loop {
        led.toggle();
        Timer::after(Duration::from_millis(500)).await;
    }
}

# [embassy_executor::main]
async fn main(spawner: Spawner) {
    let led = make_static!(Led::new());
    spawner.spawn(blinky(led)).unwrap();

    // 主任务可以继续执行
    loop {
        Timer::after(Duration::from_secs(1)).await;
        defmt::info!("Main task tick");
    }
}
```

### 示例2: 通道通信

```rust
use embassy_sync::blocking_mutex::raw::ThreadModeRawMutex;
use embassy_sync::channel::Channel;

static CHANNEL: Channel<ThreadModeRawMutex, Data, 3> = Channel::new();

# [embassy_executor::task]
async fn producer() {
    loop {
        let data = sensor.read().await;
        CHANNEL.send(data).await;  // 异步发送
    }
}

# [embassy_executor::task]
async fn consumer() {
    loop {
        let data = CHANNEL.receive().await;  // 异步接收
        process(data).await;
    }
}
```

### 示例3: 中断集成

```rust
use embassy_nrf::gpio::{Input, Pin, Pull};
use embassy_nrf::interrupt;

static BUTTON_PRESS: Signal<CriticalSectionRawMutex, ()> = Signal::new();

# [interrupt]
fn GPIOTE() {
    // 中断处理：只发信号
    BUTTON_PRESS.signal(());
}

# [embassy_executor::task]
async fn button_handler() {
    loop {
        BUTTON_PRESS.wait().await;  // 等待中断信号
        defmt::info!("Button pressed!");
        handle_press().await;
    }
}
```

### 示例4: 多Executor核心

```rust
# [embassy_executor::main]
async fn main(_spawner: Spawner) {
    // 创建两个executor
    let mut executor1 = Executor::new();
    let mut executor2 = Executor::new();

    // 在独立线程/核心上运行
    executor1.run(|spawner| {
        spawner.spawn(task_on_core1()).unwrap();
    });

    executor2.run(|spawner| {
        spawner.spawn(task_on_core2()).unwrap();
    });
}
```

---

## 8. 与标准async对比

| 特性 | Embassy | Tokio/std async |
| :--- | :--- | :--- |
| 运行时大小 | <1KB | ~100KB+ |
| 堆分配 | 无 | 需要 |
| 任务数 | 编译时确定 | 动态 |
| 调度器 | 单线程协作式 | 多线程工作窃取 |
| 中断集成 | 原生支持 | 需适配 |
| 低功耗 | 内置 | 需手动 |

**形式化对比**:

$$
\text{Embassy} \subset \text{Tokio}_{\text{async}} \text{ in expressiveness, but } \text{Embassy} \supset \text{Tokio}_{\text{embedded}}
$$

---

**维护者**: Rust Embedded Formal Methods Team
**创建日期**: 2026-03-05
**Embassy版本**: 0.3+
**状态**: ✅ 已对齐
