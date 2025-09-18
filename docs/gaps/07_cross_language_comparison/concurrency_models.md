# 并发模型比较：Rust vs C/C++/Go/Java/JavaScript

## 概述

对比主流语言并发内核（内存模型、并发原语、错误模型、工具生态），给出选型与迁移建议。

## 对比维度

- 内存模型：顺序一致性、松弛内存、数据竞争定义
- 并发原语：线程/协程、通道、锁/原子、选择/事件
- 安全模型：数据竞争定义、类型层保证、运行时保护
- 错误模型：取消/超时、panic/异常、恢复语义
- 工具生态：模型检查、竞争检测、模糊与属性测试

## 语言要点

- Rust：所有权/借用在编译期消除数据竞争；`Send/Sync` 编码可传递性；Loom/Kani/Proptest
- C/C++：C11 原子与 UB 风险；需人工约束；TSAN/模型检查工具为后盾
- Go：CSP 风格（goroutine+channel）；数据竞争检测依赖工具；`select` 多路复用
- Java：JMM 与并发包；可见性/有序性需谨慎；工具链成熟
- JavaScript：事件循环+任务队列+Workers；共享内存需 Atomics/SharedArrayBuffer

## 选型建议

- 强安全与零开销：Rust
- 快速原型与服务端：Go/Java
- 系统与高性能：C++/Rust
- 前端/事件驱动：JavaScript

## 迁移要点（到 Rust）

- 明确所有权边界与别名策略
- 将共享状态改造为消息传递或受控同步
- 用类型建模协议阶段与不变量

## 细粒度对比（补充）

### 内存模型与可见性

- Rust: 采用与 LLVM 一致的原子内存序，结合借用检查器，默认禁止数据竞争；对 `unsafe` 边界要求不变量文档化。
- C++: C++11 内存模型提供顺序一致/获取释放/松弛等语义，但存在 UB 派生放大问题，需严格审计。
- Go: Go 内存模型强调通过 `happens-before` 保证可见性，常以 channel/锁建立顺序，竞态检测主要依赖工具。
- Java: JMM 提供可见性与有序性规则，`volatile`/`final` 具备特殊语义，错误多源于发布/逃逸与双检锁等细节。
- JavaScript: 事件循环单线程 + 微/宏任务；SharedArrayBuffer + Atomics 提供弱共享内存能力，需谨慎。

### 并发原语与模式

- Rust: 线程、`std::sync` 原语、`crossbeam` 工具箱、`tokio` 任务与 `select!`，偏向类型见证的协议建模（状态机 enum）。
- Go: goroutine + channel + `select`，倡导 CSP；共享内存亦常见，但竞态风险较高。
- Java: `java.util.concurrent` 全家桶（`CompletableFuture`、ForkJoinPool），锁分层丰富；结构化并发正在演进。

### 错误与取消语义

- Rust: `Result` 显式错误；`panic` 默认线程隔离；`tokio::task::JoinHandle::abort` 可取消，需协作式检查。
- Go: `context.Context` 传递取消/超时；`panic/recover` 不建议作控制流。
- Java: `InterruptedException` 协作式取消；异常传播与重试框架普遍。

### 工具链与验证

- Rust: Loom 并发探索、Kani 模型检查、Miri/UBSan（部分场景）、Proptest 属性测试。
- C/C++: TSAN/ASAN/MSAN、CBMC/SMACK、模型检查器（Spin/TLA+ 外部）。
- Go/Java: 自带竞态检测/分析器；JCStress 等并发微基准与验证工具。

## 迁移清单（Checklist）

1. 标注共享可变状态，优先改造为消息传递或不可变快照。
2. 用 `enum` 状态机刻画协议阶段，禁止非法转换；必要时引入 typestate 模式。
3. 把隐式时序依赖显式化：`Arc<Mutex<_>>/RwLock` 或 `mpsc`/`broadcast`，并限定持锁范围。
4. 为关键并发路径编写 Loom 探索与 Proptest 属性；小状态空间用 Kani 检查。
5. 约束 `unsafe`：定义不变量、最小暴露面、单元/属性/模型检查三重护栏。

## 典型错误与修复对照

- 锁粒度过粗 → 细化为 `RwLock` 或基于消息的序列化
- 共享可变迭代器 → 以快照克隆 + 增量补丁（diff）
- 死锁（锁顺序不一致） → 定义全局锁序；以 `parking_lot::ReentrantMutex` 仅在必要处兜底
- 忘记 `JoinHandle` 处理 → 收集并 `join()`，或显式 `abort` 并处理未完成任务

## 微基准与验证脚本模板

```rust
// cargo bench --bench sched_lat
#[bench]
fn sched_lat(b: &mut test::Bencher) {
    use std::sync::mpsc;
    use std::thread;
    b.iter(|| {
        let (tx, rx) = mpsc::channel::<u64>();
        let t = thread::spawn(move || tx.send(1).unwrap());
        let _ = rx.recv().unwrap();
        t.join().unwrap();
    })
}
```

```rust
// loom 验证关键互斥序
#[test]
fn loom_mutex_order() {
    loom::model(|| {
        use loom::sync::Mutex;
        let a = Mutex::new(0);
        let b = Mutex::new(0);
        let t1 = loom::thread::spawn({
            let a = a.clone(); let b = b.clone(); move || {
                *a.lock().unwrap() += 1;
                *b.lock().unwrap() += 1;
            }
        });
        let t2 = loom::thread::spawn({
            let a = a.clone(); let b = b.clone(); move || {
                *a.lock().unwrap() += 1;
                *b.lock().unwrap() += 1;
            }
        });
        t1.join().unwrap(); t2.join().unwrap();
    });
}
```

## 示例：从 Go channel 到 Rust mpsc

```rust
use std::thread;
use std::sync::mpsc;

fn main() {
    let (tx, rx) = mpsc::channel::<u32>();
    let t = thread::spawn(move || {
        for i in 0..3 { tx.send(i).unwrap(); }
    });
    for v in rx { println!("{}", v); }
    t.join().unwrap();
}
```

要点：用所有权移动代替共享写；通道关闭触发迭代结束，避免泄漏与悬挂消费者。

## 延伸阅读

- Rust Reference: Atomics and Memory Ordering
- Go Memory Model（2023 修订）
- JSR-133: Java Memory Model and Thread Specification

## 参考

- The Rustonomicon; Go Memory Model; Java Memory Model; C++ Concurrency TS
