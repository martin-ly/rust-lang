# 内存模型理论

## 1. 抽象内存模型

- 内存操作的数学抽象，$\Sigma$表示内存状态
- $p \mapsto v$：指针p指向值v

## 2. 并发与弱内存模型

- 并发内存一致性：多线程下的可见性与顺序保证
- 弱内存模型：现代CPU的乱序执行与内存屏障

## 3. 分离原理与内存屏障

- $\Sigma_1 \perp \Sigma_2$：内存状态分离，便于并发推理
- 内存屏障保证操作顺序，防止数据竞争

## 4. 工程案例

```rust
use std::sync::atomic::{AtomicUsize, Ordering};
let a = AtomicUsize::new(0);
a.store(1, Ordering::SeqCst);
let v = a.load(Ordering::SeqCst);
```

## 5. 批判性分析与未来展望

- Rust内存模型兼顾安全与性能，但弱内存模型下推理复杂
- 未来可探索自动化并发内存分析与可视化工具
