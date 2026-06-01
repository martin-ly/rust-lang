//! 线程池设计模式与高级并发
//! thread pool design and concurrency
//! 本模块深入讲解线程池设计模式、工作窃取调度、作用域线程与无锁数据结构概念：
//! this module thread pool design 、、role domain thread and lock-free data structure concept ：
//! - 线程池设计模式（固定 vs 动态、共享队列 vs 本地队列、关闭策略）
//! - thread pool design （ vs 、 vs this 、strategy ）
//! - 工作窃取调度概念（Chase-Lev 双端队列、Owner/Thief 操作）
//! - concept （Chase-Lev 、Owner/Thief ）
//! - 工作窃取调度concept（Chase-Lev 双端队列、Owner/Thief 操作）
//! - 作用域线程深度解析（std::thread::scope、生命周期安全、并行模式）
//! - role domain thread （std::thread::scope、lifetime 、parallelism ）
//! - 无锁数据结构概念（lock-free vs wait-free、ABA 问题、Treiber 栈、Michael-Scott 队列）
//! - lock-freedata structureconcept（lock-free vs wait-free、ABA problem、Treiber stack、Michael-Scott 队列）
//! 注意：本模块不包含任何 unsafe 代码；无锁数据结构部分以概念和伪代码形式呈现。
//! ：this module unsafe ；lock-free data structure part concept and 。

use std::sync::{Arc, Mutex};
use std::thread;

// ============================================================================
// 1. ThreadPoolDesign — 线程池设计模式
// ============================================================================

/// 线程池设计模式深度解析
/// thread pool design
pub struct ThreadPoolDesign;

impl ThreadPoolDesign {
    /// 固定大小线程池 vs 动态线程池
    /// thread pool vs thread pool
    /// 固定大小thread pool vs 动态thread pool
    pub fn fixed_vs_dynamic() -> &'static str {
        r#"
=== 固定大小线程池 (Fixed-size Thread Pool) ===
- 创建时预先启动固定数量的工作线程
- 所有线程共享一个任务队列（或每个线程有本地队列）
- 优点：资源可控、无线程创建销毁开销、避免抖动
- 缺点：任务突增时可能排队过长；空闲线程浪费资源
- 典型代表：Java ThreadPoolExecutor (core == max)

=== 动态线程池 (Dynamic/Cached Thread Pool) ===
- 根据任务负载动态创建/销毁线程
- 新任务到来时，若所有线程忙则创建新线程（有上限）
- 空闲线程在超时后自动回收
- 优点：适应负载波动、低延迟处理突发流量
- 缺点：线程创建销毁有开销；无限制增长可能导致 OOM
- 典型代表：Java ThreadPoolExecutor (core < max)、tokio::runtime

=== 决策树 ===
任务量稳定且可预测？     -> 固定线程池
任务量波动大、 latency 敏感？ -> 动态线程池（设上限）
CPU 密集型任务？         -> 线程数 ≈ CPU 核心数
IO 密集型任务？          -> 线程数 > CPU 核心数（等待不占用 CPU）
        "#
    }

    /// 工作队列设计：共享队列 vs 每个线程的队列
    /// design ： vs thread
    pub fn work_queue_design() -> &'static str {
        r#"
=== 共享全局队列 (Shared Global Queue) ===
- 所有生产者将任务推入同一个队列（通常用 Mutex<VecDeque> 或 MPMC channel）
- 所有工作线程竞争从队列取出任务
- 优点：实现简单、负载均衡天然成立
- 缺点：高竞争下锁成为瓶颈（cache-line bouncing）
- 优化：使用无锁 MPMC 队列（如 crossbeam-queue）减少争用

=== 每个线程的本地队列 (Per-thread Local Queue) ===
- 每个工作线程拥有独立的任务队列
- 生产者按某种策略（轮询/哈希）将任务分发到特定线程队列
- 优点：无锁访问本地队列、cache locality 好
- 缺点：可能出现负载不均（某线程队列空，其他线程队列满）
- 优化：引入 Work-Stealing 机制，空闲线程从其他线程"窃取"任务

=== 混合模型 (Hybrid: Global + Local) ===
- 全局注入器（Injector）+ 每个线程的本地 Worker 队列
- 新任务先进入全局注入器；线程优先处理本地队列，空时从全局或他人处窃取
- 代表实现：rayon、crossbeam-deque、Tokio 调度器
        "#
    }

    /// 线程池关闭策略：优雅关闭 vs 立即关闭
    /// thread pool strategy ： vs
    pub fn shutdown_strategies() -> &'static str {
        r#"
=== 优雅关闭 (Graceful Shutdown) ===
- 停止接受新任务
- 等待已提交的任务全部执行完毕
- 然后按序 join 所有工作线程
- 优点：不丢失已提交任务、数据一致性有保障
- 实现要点：
  1. 关闭任务提交端（如 drop sender / 设置 shutdown 标志）
  2. 工作线程检测到关闭信号后，先清空本地队列再退出
  3. 主线程 join 所有 worker，设置超时避免永远阻塞

=== 立即关闭 (Immediate Shutdown) ===
- 立即停止所有工作线程，丢弃未开始执行的任务
- 可能需要向线程发送信号（如 std::thread::Thread::unpark 配合 AtomicBool）
- 优点：快速释放资源、适合紧急停止场景
- 缺点：任务丢失、可能产生不一致状态
- 注意事项：正在执行的任务无法强制中断（Rust 没有 Thread.stop()）

=== 超时关闭 (Timeout Shutdown) ===
- 先尝试优雅关闭，若超过指定时间仍未完成，则强制剩余线程退出
- 折中方案：兼顾数据完整性和响应速度
        "#
    }

    /// 对比：threadpool crate vs rayon vs 自定义实现
    pub fn crate_comparison() -> &'static str {
        r#"
=== threadpool crate ===
- 经典固定大小线程池，基于共享队列 + Mutex/Condvar
- API 简单：ThreadPool::new(n) -> execute(closure)
- 优点：轻量、稳定、易于理解
- 缺点：无工作窃取、无 scope/并行迭代器、性能中规中矩
- 适用：快速集成、教学演示、简单并发任务

=== rayon ===
- 基于工作窃取（work-stealing）的数据并行库
- 核心抽象：ParallelIterator、join、scope
- 优点：
  - 利用 Chase-Lev 双端队列实现高效任务分发
  - 自动负载均衡、对不均匀任务效果极佳
  - 提供高级 API（par_iter、par_sort、par_map）
- 缺点：引入依赖较大；自定义调度策略受限
- 适用：数据并行、递归分治算法、需要极致性能的场景

=== 自定义实现 ===
- 从零构建线程池，完全掌控队列策略、关闭语义、监控统计
- 优点：灵活、可针对业务特化（如优先级队列、NUMA 感知）
- 缺点：开发维护成本高；极易引入并发 Bug
- 建议：优先用成熟 crate，仅在确有特殊需求时自定义
        "#
    }

    /// 打印线程池设计模式概览
    /// thread pool design
    pub fn print_overview() {
        println!("{}", Self::fixed_vs_dynamic());
        println!("{}", Self::work_queue_design());
        println!("{}", Self::shutdown_strategies());
        println!("{}", Self::crate_comparison());
    }
}

// ============================================================================
// 2. WorkStealingConcept — 工作窃取调度概念
// ============================================================================

/// 工作窃取调度概念深度解析
/// concept
/// 讲解工作窃取corethought、Chase-Lev 双端队列、Owner/Thief 操作模式，
/// 以及 Rayon's work-stealing scheduler 概念。
pub struct WorkStealingConcept;

impl WorkStealingConcept {
    /// 什么是工作窃取调度
    pub fn what_is_work_stealing() -> &'static str {
        r#"
=== 工作窃取调度 (Work-Stealing Scheduling) ===

工作窃取是一种负载均衡策略，核心思想：
- 每个工作线程维护自己的本地任务队列
- 线程优先从本地队列取出任务执行（LIFO，后进先出）
- 当本地队列为空时，该线程变为"小偷"(thief)，随机选择其他线程的队列
  从尾部"窃取"任务（FIFO，先进先出）

=== 为什么这样设计？ ===
- Owner 使用 LIFO：利用递归分治的深度优先特性，子任务往往共享缓存数据
- Thief 使用 FIFO：窃取的是最老的任务，通常粒度更大，减少后续窃取次数
- 这种不对称设计兼顾了 cache locality 和负载均衡

=== 工作窃取的适用场景 ===
- 递归分治算法（快速排序、归并排序、矩阵乘法）
- 任务生成不均匀（某些分支产生大量子任务，其他分支很快结束）
- 任务粒度差异大（避免小任务被频繁窃取导致调度开销过高）
        "#
    }

    /// Chase-Lev 双端队列概念
    /// Chase-Lev concept
    /// Chase-Lev 双端队列concept
    pub fn chase_lev_deque_concept() -> &'static str {
        r#"
=== Chase-Lev 双端队列 (Dynamic Work-Stealing Deque) ===

Chase-Lev deque 是工作窃取调度器的经典数据结构，核心特征：
- 支持单生产者（Owner）多消费者（Thief）
- Owner 在队列头部进行 push/pop，无需同步（通常）
- Thief 在队列尾部进行 steal，需要与 Owner 竞争

=== 核心操作 ===
1. push(task) — Owner:
   - 直接在数组头部插入新任务
   - 若数组满则扩容（需要 CAS 保证安全）

2. pop() — Owner:
   - 从头部取出任务
   - 当只剩一个元素时，需要与 thief CAS 竞争

3. steal() — Thief:
   - 读取尾部索引，尝试 CAS 将 tail 加 1
   - 若成功则获取该位置任务；若失败则重试或放弃

=== 关键不变式 ===
- head <= tail（在稳定状态下）
- 当 head == tail 时队列为空
- Owner 和 Thief 只在边界处竞争，日常操作无锁
        "#
    }

    /// Owner vs Thief 线程操作
    pub fn owner_vs_thief_operations() -> &'static str {
        r#"
=== Owner 线程操作（本地线程） ===
- push: 将新任务放入队列头部（顶部）
- pop:  从队列头部取出任务执行
- 特点：通常无锁，使用普通内存操作；只在队列将空时可能需要原子操作
- 工作顺序：LIFO（后进先出）
  原因：递归生成的子任务通常有数据局部性，后生成的任务更可能访问热缓存

=== Thief 线程操作（其他空闲线程） ===
- steal: 从队列尾部（底部）尝试窃取任务
- 特点：必须全程使用原子操作（Acquire/Release 或 SeqCst）
- 竞争处理：使用 CAS（compare-and-swap）尝试移动 tail 指针
  - CAS 成功：窃取成功，执行任务
  - CAS 失败：Owner 可能正在 pop 或扩容，放弃或重试
- 工作顺序：FIFO（先进先出）
  原因：老任务通常粒度更大，窃取大任务能减少总窃取次数

=== 伪代码概念 ===
```text
Owner::push(task):
    buffer[head] = task
    head += 1

Owner::pop() -> Option<Task>:
    head -= 1
    task = buffer[head]
    if head > tail:
        return Some(task)      // 确定有数据，无竞争
    // head 与 tail 交叉，可能只剩一个元素
    // 需要 CAS 与 thief 竞争
    ...

Thief::steal() -> Option<Task>:
    old_tail = load(tail, Acquire)
    old_head = load(head, Acquire)
    if old_tail >= old_head:
        return None            // 队列空
    task = buffer[old_tail]
    if CAS(tail, old_tail, old_tail + 1):
        return Some(task)
    else:
        return None            // 竞争失败
```
        "#
    }

    /// 何时工作窃取有帮助
    pub fn when_work_stealing_helps() -> &'static str {
        r#"
=== 工作窃取显著帮助的场景 ===

1. 不均匀负载分布 (Uneven Workload Distribution)
   - 某些任务分支深度大、计算量大，其他分支很快结束
   - 无工作窃取时，快速结束的线程空闲，慢线程积压

2. 递归分治算法 (Divide-and-Conquer)
   - 快速排序、归并排序、Strassen 矩阵乘法
   - 子任务粒度随递归深度减小，天然适合窃取

3. 动态任务生成 (Dynamic Task Generation)
   - 任务在执行过程中产生新任务（如并行搜索、图遍历）
   - 静态分区无法预测任务分布

=== 工作窃取效果有限的场景 ===

1. 完全均匀的批处理
   - 所有任务计算量相同，静态均分已足够

2. 任务粒度极细
   - 窃取开销 > 任务执行时间，调度成本主导

3. 单生产者顺序执行
   - 没有并发空间，工作窃取无意义
        "#
    }

    pub fn rayons_work_stealing_scheduler() -> &'static str {
        r#"
=== Rayon 的工作窃取调度器 ===

Rayon 是 Rust 生态中最著名的数据并行库，其调度器基于改进的 Chase-Lev deque：

=== 核心组件 ===
- Registry: 全局线程池管理器，维护一组 Worker 线程
- Worker<T>: 每个线程一个，包含本地 deque（LIFO push/pop）
- Stealer<T>: 其他线程用来从该 Worker 窃取任务（FIFO steal）
- Injector<T>: 全局任务注入器，用于外部线程提交任务

=== 调度流程 ===
1. 调用 rayon::join(a, b) 或 par_iter() 时，当前线程将任务推入本地 Worker
2. 线程优先执行本地任务（LIFO），保持深度优先、cache 友好
3. 本地队列为空时，线程开始窃取：
   a. 先尝试从全局 Injector 窃取
   b. 再按随机顺序尝试从其他 Worker 的 Stealer 窃取
4. 若窃取也失败，线程进入休眠（parking），等待新任务唤醒

=== join 语义 ===
- join(closure_a, closure_b) 在当前线程执行其中一个闭包，
  另一个被推入本地队列供后续处理（或被其他线程窃取）
- 若闭包 B 被窃取，当前线程继续执行 A；完成后帮助完成 B
- 这形成了"work-first"调度，极大减少线程同步开销
        "#
    }

    /// 打印工作窃取概念概览
    /// concept
    pub fn print_overview() {
        println!("{}", Self::what_is_work_stealing());
        println!("{}", Self::chase_lev_deque_concept());
        println!("{}", Self::owner_vs_thief_operations());
        println!("{}", Self::when_work_stealing_helps());
        println!("{}", Self::rayons_work_stealing_scheduler());
    }
}

// ============================================================================
// 3. ScopedThreadsDeepDive — 作用域线程深度解析
// ============================================================================

/// 作用域线程深度解析
/// role domain thread
pub struct ScopedThreadsDeepDive;

impl ScopedThreadsDeepDive {
    /// std::thread::scope 深度解析
    /// std::thread::scope 深度Parse
    pub fn std_thread_scope_deep_dive() -> &'static str {
        r#"
=== std::thread::scope (稳定于 Rust 1.63) ===

签名：
```rust
pub fn scope<'env, F, T>(f: F) -> T
where
    F: for<'scope> FnOnce(&'scope Scope<'env, '_>) -> T,
```

=== 核心能力 ===
- 在闭包内部创建的线程（scoped threads）可以借用闭包参数的数据
- 所有 scoped threads 必须在 scope 闭包返回前 join 完毕
- 因此编译器可以确保借用的数据在线程结束前一直有效

=== 为什么不需要 Arc + Mutex？ ===
- 普通 thread::spawn 要求闭包 'static，因为主线程可能先结束，
  导致子线程访问已释放的栈数据
- scope 通过 API 契约保证：子线程一定在 scope 返回前结束
- 编译器利用生命周期系统静态验证这一点
        "#
    }

    /// 为什么作用域线程是安全的：生命周期保证
    /// as role domain thread ：lifetime
    pub fn why_scoped_threads_are_safe() -> &'static str {
        r#"
=== 生命周期保证 (Lifetime Guarantees) ===

Rust 编译器通过以下机制确保 scoped threads 不会访问失效数据：

1. Scope 对象的生命周期 ('scope)
   - scope 闭包接收 &Scope<'env>，'env 是外部数据的生命周期
   - 所有 scoped threads 借用的数据必须满足 'env

2. Thread 句柄的生命周期绑定
   - Scope::spawn 返回 ScopedJoinHandle<'scope>
   - 该句柄必须在 'scope 内被处理（drop 即 join）

3. 自动 join 保证
   - scope 返回时，Scope 对象被 drop
   - Drop 实现会依次 join 所有尚未 join 的子线程
   - 因此 scope 返回 = 所有子线程已结束 = 借用安全释放

=== 编译时检查示例 ===
```rust
let data = vec![1, 2, 3];
thread::scope(|s| {
    s.spawn(|| println!("{:?}", &data)); // OK: data 在 scope 内有效
});
// data 在这里被释放，但所有线程已 join，安全
```

如果尝试将 handle 泄露到 scope 外部：
```rust
let handle;
thread::scope(|s| {
    handle = s.spawn(|| {}); // 编译错误：handle 生命周期不够长
});
```
        "#
    }

    /// 并行分治模式（使用作用域线程的安全演示）
    /// parallelism （role domain thread demonstration ）
    pub fn parallel_divide_and_conquer(data: &mut [i32]) {
        if data.len() <= 1 {
            return;
        }
        if data.len() <= 1024 {
            // 小数组直接串行排序
            data.sort_unstable();
            return;
        }

        let len = data.len();
        let mid = len / 2;
        let (left, right) = data.split_at_mut(mid);

        thread::scope(|s| {
            s.spawn(|| Self::parallel_divide_and_conquer(left));
            Self::parallel_divide_and_conquer(right);
        });

        // 合并两个有序半区（稳定实现：使用临时Vec）
        let mut merged = Vec::with_capacity(len);
        let (mut i, mut j) = (0, 0);
        while i < left.len() && j < right.len() {
            if left[i] <= right[j] {
                merged.push(left[i]);
                i += 1;
            } else {
                merged.push(right[j]);
                j += 1;
            }
        }
        while i < left.len() {
            merged.push(left[i]);
            i += 1;
        }
        while j < right.len() {
            merged.push(right[j]);
            j += 1;
        }
        data.copy_from_slice(&merged);
    }

    pub fn parallel_map_filter(input: &[i32]) -> Vec<i32> {
        if input.is_empty() {
            return Vec::new();
        }
        if input.len() < 512 {
            // 小数据量直接串行处理
            return input
                .iter()
                .filter(|&&x| x % 2 == 0)
                .map(|&x| x * x)
                .collect();
        }

        let num_threads = std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(4)
            .min(input.len());

        let chunk_size = input.len().div_ceil(num_threads);
        let results: Arc<Mutex<Vec<Vec<i32>>>> =
            Arc::new(Mutex::new(vec![Vec::new(); num_threads]));

        thread::scope(|s| {
            for t in 0..num_threads {
                let start = t * chunk_size;
                let end = ((t + 1) * chunk_size).min(input.len());
                if start >= end {
                    continue;
                }
                let chunk = &input[start..end];
                let results = Arc::clone(&results);
                s.spawn(move || {
                    let local: Vec<i32> = chunk
                        .iter()
                        .filter(|&&x| x % 2 == 0)
                        .map(|&x| x * x)
                        .collect();
                    results.lock().expect("获取结果锁不应失败")[t] = local;
                });
            }
        });

        let guard = results.lock().expect("获取结果锁不应失败");
        guard.iter().flatten().copied().collect()
    }

    /// 对比：scoped threads vs rayon vs crossbeam::scope
    /// to比：scoped threads vs rayon vs crossbeam::scope
    pub fn comparison_scoped_vs_rayon_vs_crossbeam() -> &'static str {
        r#"
=== std::thread::scope (标准库) ===
- 稳定、零依赖
- 手动管理任务划分和线程同步
- 适合：学习生命周期机制、细粒度控制、不引入外部依赖
- 不足：没有自动负载均衡、需要自己写分治递归

=== rayon ===
- 基于工作窃取的数据并行库
- 高级 API：par_iter、join、scope
- 自动处理任务划分和线程池管理
- 适合：快速实现数据并行、递归算法、追求性能
- 不足：对任务粒度有要求；过度使用可能增加编译时间

=== crossbeam::scope ===
- crossbeam 提供的 scope 实现（比 std 更早存在）
- 功能与 std::thread::scope 类似，但支持更多底层控制
- 例如：可配置线程栈大小、更灵活的句柄管理
- crossbeam 生态还提供 channel、deque、epoch GC 等配套工具
- 适合：需要 crossbeam 全家桶、或需要 std 不提供的底层控制

=== 选型建议 ===
快速数据并行？                  -> rayon
简单借用安全 + 零依赖？          -> std::thread::scope
需要底层控制 + crossbeam 生态？   -> crossbeam::scope
        "#
    }

    /// 打印作用域线程深度解析概览
    /// role domain thread
    pub fn print_overview() {
        println!("{}", Self::std_thread_scope_deep_dive());
        println!("{}", Self::why_scoped_threads_are_safe());
        println!("{}", Self::comparison_scoped_vs_rayon_vs_crossbeam());
    }
}

// ============================================================================
// 4. LockFreeDataStructures — 无锁数据结构概念
// ============================================================================

/// 无锁数据结构概念深度解析
/// lock-free data structure concept
/// 本模块以概念、算法伪代码和决策指导形式呈现，不使用任何 unsafe 代码。
/// this module concept 、algorithm and ， unsafe 。
pub struct LockFreeDataStructures;

impl LockFreeDataStructures {
    /// Lock-free vs Wait-free vs Obstruction-free
    pub fn progress_guarantees() -> &'static str {
        r#"
=== 非阻塞同步的三种进度保证 ===

1. Obstruction-Free (无障碍)
   - 定义：任意线程在单独执行时（无其他线程竞争）能在有限步内完成操作
   - 特点：最弱的非阻塞保证；多个线程竞争时可能活锁
   - 应用：很少直接使用，通常作为构建更强算法的中间步骤

2. Lock-Free (无锁)
   - 定义：系统作为一个整体持续前进；至少有一个线程在有限步内完成操作
   - 特点：个别线程可能饥饿（starvation），但系统不会死锁
   - 应用：大多数实际无锁数据结构的目标级别
   - 代表：Treiber Stack、Michael-Scott Queue、ConcurrentHashMap

3. Wait-Free (无等待)
   - 定义：每个线程都能在有限步内完成操作，无论其他线程行为如何
   - 特点：最强的保证；无饥饿、延迟可预测
   - 代价：通常实现更复杂、性能开销更高（可能需要更多原子操作或辅助状态）
   - 代表：Wait-Free Ring Buffer（特定实现）、一些高级队列

=== 对比表 ===
| 保证级别       | 个体进度 | 系统进度 | 实现复杂度 | 典型应用            |
|---------------|---------|---------|-----------|-------------------|
| Obstruction-Free | 不一定  | 不一定   | 低         | 理论构建块          |
| Lock-Free        | 可能饥饿 | 保证     | 中         | 高并发栈/队列/哈希表 |
| Wait-Free        | 保证     | 保证     | 高         | 实时系统、内核       |
        "#
    }

    /// ABA 问题及其解决方案
    /// ABA problem and its solution
    pub fn aba_problem_and_solutions() -> &'static str {
        r#"
=== ABA 问题 ===

场景：线程 T1 读取指针 A，准备用 CAS 将其改为 C；
      在此期间线程 T2 将 A 改为 B 又改回 A；
      T1 的 CAS 仍然成功，但 A 指向的内容/状态已发生变化。

后果：T1 误以为 A 未被修改，可能导致数据结构损坏或内存安全问题。

=== 解决方案 ===

1. 标签指针 / 版本号 (Tagged Pointers / Version Counter)
   - 将指针与单调递增的计数器打包为一个 CAS 操作的原子单元
   - 每次修改时计数器加 1，即使指针值回到 A，计数器已不同
   - Rust 实现思路：使用 AtomicUsize/AtomicU64，高几位存计数器，低位存指针
   - 限制：64 位系统可利用地址空间对齐节省的低位；计数器可能回绕（极罕见）

2. 危险指针 (Hazard Pointers)
   - 每个线程声明自己正在访问的节点（放入 hazard pointer 数组）
   - 其他线程删除节点时，先检查是否被任何 hazard pointer 引用
   - 若无引用则可安全释放；若有则延迟释放（retire list）
   - Rust 生态：crossbeam-epoch 提供了基于 Epoch-Based Reclamation 的等价机制

3. Epoch-Based Reclamation (EBR)
   - 全局 epoch 计数器，线程进入/离开临界区时记录当前 epoch
   - 删除的节点放入延迟释放列表，等到所有线程都跨越至少一个 epoch 边界后释放
   - 优点：批量回收、开销低；缺点：延迟释放、内存峰值可能升高
   - Rust 实现：crossbeam-epoch crate
        "#
    }

    /// Treiber 栈概念（无锁栈）
    /// Treiber stack concept （lock-free stack ）
    pub fn treiber_stack_concept() -> &'static str {
        r#"
=== Treiber Stack (无锁栈) ===

由 Treiber 于 1986 年提出，是最简单的无锁数据结构之一。

=== 数据结构 ===
```text
struct Node<T> {
    data: T,
    next: AtomicPtr<Node<T>>,
}

struct TreiberStack<T> {
    head: AtomicPtr<Node<T>>,
}
```

=== 核心操作（概念伪代码） ===

push(value):
    new_node = alloc(Node { data: value, next: null })
    loop:
        old_head = head.load(Acquire)
        new_node.next = old_head
        if head.compare_exchange(old_head, new_node, Release, Relaxed):
            return

pop() -> Option<T>:
    loop:
        old_head = head.load(Acquire)
        if old_head == null:
            return None
        new_head = old_head.next.load(Relaxed)
        if head.compare_exchange(old_head, new_head, Acquire, Relaxed):
            value = read(old_head.data)
            // 注意：不能直接 free(old_head)，可能有其他线程正在读取
            // 需要使用 Hazard Pointers / Epoch-Based Reclamation 延迟释放
            return Some(value)

=== 特性 ===
- Lock-Free：push/pop 都是 CAS 循环，系统整体持续前进
- ABA 风险：若 pop 后 head 被其他线程改回原值，CAS 可能成功但 next 已变
  - 解决：使用 tagged pointer（将 head 指针与版本号打包）
- 内存回收：必须使用安全的延迟释放机制（如 crossbeam-epoch）
        "#
    }

    /// Michael-Scott 队列概念（无锁队列）
    /// Michael-Scott concept （lock-free queue ）
    /// Michael-Scott 队列concept（lock-free queue）
    pub fn michael_scott_queue_concept() -> &'static str {
        r#"
=== Michael-Scott Queue (无锁队列) ===

由 Michael 和 Scott 于 1996 年提出，是工业界最广泛使用的无锁队列算法。
支持多生产者并发入队（MP）和多消费者并发出队（MC）。

=== 数据结构 ===
```text
struct Node<T> {
    data: MaybeUninit<T>,
    next: AtomicPtr<Node<T>>,
}

struct MSQueue<T> {
    head: AtomicPtr<Node<T>>,  // 出队端
    tail: AtomicPtr<Node<T>>,  // 入队端
}
```

初始化时创建一个 dummy node，head 和 tail 都指向它。

=== 核心操作（概念伪代码） ===

enqueue(value):
    new_node = alloc(Node { data: value, next: null })
    loop:
        tail = self.tail.load(Acquire)
        next = tail.next.load(Acquire)
        if tail == self.tail.load(Relaxed):          // 确认 tail 未变
            if next == null:                         // tail 确实是最后一个节点
                if tail.next.compare_exchange(next, new_node, Release, Relaxed):
                    // 尝试更新 tail（允许失败，其他线程会帮忙）
                    let _ = self.tail.compare_exchange(tail, new_node, Release, Relaxed)
                    return
            else:
                // tail 滞后了，帮忙推进
                let _ = self.tail.compare_exchange(tail, next, Release, Relaxed)

dequeue() -> Option<T>:
    loop:
        head = self.head.load(Acquire)
        tail = self.tail.load(Acquire)
        next = head.next.load(Acquire)
        if head == self.head.load(Relaxed):          // 确认 head 未变
            if head == tail:
                if next == null:
                    return None                      // 队列为空
                // tail 滞后，帮忙推进
                let _ = self.tail.compare_exchange(tail, next, Release, Relaxed)
            else:
                value = read(next.data)
                if self.head.compare_exchange(head, next, Release, Relaxed):
                    // 注意：head 是 dummy，真正的节点是 next
                    // 释放 old dummy 需要使用延迟回收机制
                    return Some(value)

=== 关键设计点 ===
- 分离的 head/tail 指针减少入队/出队之间的竞争
- 使用 dummy node 简化边界条件
- 允许"帮忙推进"（helping）：一个线程发现 tail/head 滞后时，主动 CAS 推进
- 内存回收：出队后的旧 dummy 节点不能立即释放，需 EBR/Hazard Pointers
        "#
    }

    /// 何时使用无锁数据结构
    /// lock-free data structure
    /// 何时Uselock-freedata structure
    pub fn when_to_use_lock_free() -> &'static str {
        r#"
=== 无锁数据结构的适用场景 ===

1. 极高并发争用 (High Contention)
   - 当锁成为瓶颈（cache-line bouncing、优先级反转、convoying）时
   - 无锁结构通过 CAS 循环替代锁，减少系统级阻塞

2. 低延迟要求 (Low Latency / Real-time)
   - 锁可能导致不可预测的阻塞（持有锁的线程被调度出去）
   - Lock-free/Wait-free 保证线程不会因其他线程而无限阻塞

3. 中断上下文 / 信号处理程序
   - 不能睡眠的上下文无法使用锁（可能死锁）
   - 无锁操作仅依赖原子指令，不会睡眠

4. 跨 NUMA 节点共享
   - 锁的缓存一致性流量在 NUMA 下代价高昂
   - 无锁结构配合 per-CPU 设计可降低跨节点流量

=== 不适用的情况 ===

1. 低并发场景
   - 无锁的 CAS 重试和内存屏障开销可能高于简单的 Mutex

2. 需要复杂事务语义
   - 无锁结构难以组合（A + B 两个无锁操作难以原子化）
   - 锁可以方便地保护一组操作

3. 快速原型开发
   - 无锁代码极难编写和验证；优先使用标准同步原语

=== Rust 生态推荐 ===
- 通用无锁队列/栈：crossbeam-queue (ArrayQueue, SegQueue)
- 内存回收：crossbeam-epoch
- 无锁哈希表：dashmap（基于 RwLock 分片，非纯无锁但性能优异）
- 计数器/标志：std::sync::atomic 已足够
        "#
    }

    /// 打印无锁数据结构概念概览
    /// lock-free data structure concept
    pub fn print_overview() {
        println!("{}", Self::progress_guarantees());
        println!("{}", Self::aba_problem_and_solutions());
        println!("{}", Self::treiber_stack_concept());
        println!("{}", Self::michael_scott_queue_concept());
        println!("{}", Self::when_to_use_lock_free());
    }
}

// ============================================================================
// 测试模块
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // ---------- ThreadPoolDesign 测试 ----------

    #[test]
    fn test_thread_pool_design_fixed_vs_dynamic() {
        let doc = ThreadPoolDesign::fixed_vs_dynamic();
        assert!(doc.contains("Fixed-size Thread Pool"));
        assert!(doc.contains("Dynamic/Cached Thread Pool"));
        assert!(doc.contains("决策树"));
    }

    #[test]
    fn test_thread_pool_design_work_queue() {
        let doc = ThreadPoolDesign::work_queue_design();
        assert!(doc.contains("Shared Global Queue"));
        assert!(doc.contains("Per-thread Local Queue"));
        assert!(doc.contains("Hybrid"));
    }

    #[test]
    fn test_thread_pool_design_shutdown() {
        let doc = ThreadPoolDesign::shutdown_strategies();
        assert!(doc.contains("Graceful Shutdown"));
        assert!(doc.contains("Immediate Shutdown"));
        assert!(doc.contains("Timeout Shutdown"));
    }

    #[test]
    fn test_thread_pool_design_comparison() {
        let doc = ThreadPoolDesign::crate_comparison();
        assert!(doc.contains("threadpool"));
        assert!(doc.contains("rayon"));
        assert!(doc.contains("自定义实现"));
    }

    #[test]
    fn test_thread_pool_design_print_overview() {
        // 只验证不 panic
        ThreadPoolDesign::print_overview();
    }

    // ---------- WorkStealingConcept 测试 ----------

    #[test]
    fn test_work_stealing_what_is() {
        let doc = WorkStealingConcept::what_is_work_stealing();
        assert!(doc.contains("Work-Stealing Scheduling"));
        assert!(doc.contains("LIFO"));
        assert!(doc.contains("FIFO"));
    }

    #[test]
    fn test_work_stealing_chase_lev() {
        let doc = WorkStealingConcept::chase_lev_deque_concept();
        assert!(doc.contains("Chase-Lev"));
        assert!(doc.contains("push"));
        assert!(doc.contains("pop"));
        assert!(doc.contains("steal"));
    }

    #[test]
    fn test_work_stealing_owner_vs_thief() {
        let doc = WorkStealingConcept::owner_vs_thief_operations();
        assert!(doc.contains("Owner"));
        assert!(doc.contains("Thief"));
        assert!(doc.contains("CAS"));
    }

    #[test]
    fn test_work_stealing_when_helps() {
        let doc = WorkStealingConcept::when_work_stealing_helps();
        assert!(doc.contains("Uneven Workload Distribution"));
        assert!(doc.contains("Divide-and-Conquer"));
    }

    #[test]
    fn test_work_stealing_rayon() {
        let doc = WorkStealingConcept::rayons_work_stealing_scheduler();
        assert!(doc.contains("Rayon"));
        assert!(doc.contains("Registry"));
        assert!(doc.contains("Injector"));
    }

    #[test]
    fn test_work_stealing_print_overview() {
        WorkStealingConcept::print_overview();
    }

    // ---------- ScopedThreadsDeepDive 测试 ----------

    #[test]
    fn test_scoped_threads_deep_dive_doc() {
        let doc = ScopedThreadsDeepDive::std_thread_scope_deep_dive();
        assert!(doc.contains("std::thread::scope"));
        assert!(doc.contains("Rust 1.63"));
    }

    #[test]
    fn test_scoped_threads_safety_doc() {
        let doc = ScopedThreadsDeepDive::why_scoped_threads_are_safe();
        assert!(doc.contains("Lifetime Guarantees"));
        assert!(doc.contains("自动 join"));
    }

    #[test]
    fn test_scoped_threads_divide_and_conquer() {
        let mut data = vec![5, 2, 8, 1, 9, 3, 7, 4, 6, 0];
        ScopedThreadsDeepDive::parallel_divide_and_conquer(&mut data);
        assert_eq!(data, vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
    }

    #[test]
    fn test_scoped_threads_divide_and_conquer_empty() {
        let mut data: Vec<i32> = vec![];
        ScopedThreadsDeepDive::parallel_divide_and_conquer(&mut data);
        assert!(data.is_empty());
    }

    #[test]
    fn test_scoped_threads_divide_and_conquer_single() {
        let mut data = vec![42];
        ScopedThreadsDeepDive::parallel_divide_and_conquer(&mut data);
        assert_eq!(data, vec![42]);
    }

    #[test]
    fn test_scoped_threads_parallel_map_filter() {
        let input = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
        let result = ScopedThreadsDeepDive::parallel_map_filter(&input);
        // 偶数: 2,4,6,8,10 -> 平方: 4,16,36,64,100
        assert_eq!(result, vec![4, 16, 36, 64, 100]);
    }

    #[test]
    fn test_scoped_threads_parallel_map_filter_empty() {
        let input: Vec<i32> = vec![];
        let result = ScopedThreadsDeepDive::parallel_map_filter(&input);
        assert!(result.is_empty());
    }

    #[test]
    fn test_scoped_threads_parallel_map_filter_small() {
        // 小于 512 走串行路径
        let input = vec![1, 2, 3, 4];
        let result = ScopedThreadsDeepDive::parallel_map_filter(&input);
        assert_eq!(result, vec![4, 16]);
    }

    #[test]
    fn test_scoped_threads_comparison_doc() {
        let doc = ScopedThreadsDeepDive::comparison_scoped_vs_rayon_vs_crossbeam();
        assert!(doc.contains("std::thread::scope"));
        assert!(doc.contains("rayon"));
        assert!(doc.contains("crossbeam"));
    }

    #[test]
    fn test_scoped_threads_print_overview() {
        ScopedThreadsDeepDive::print_overview();
    }

    // ---------- LockFreeDataStructures 测试 ----------

    #[test]
    fn test_lock_free_progress_guarantees() {
        let doc = LockFreeDataStructures::progress_guarantees();
        assert!(doc.contains("Obstruction-Free"));
        assert!(doc.contains("Lock-Free"));
        assert!(doc.contains("Wait-Free"));
    }

    #[test]
    fn test_lock_free_aba_problem() {
        let doc = LockFreeDataStructures::aba_problem_and_solutions();
        assert!(doc.contains("ABA"));
        assert!(doc.contains("Tagged Pointers"));
        assert!(doc.contains("Hazard Pointers"));
        assert!(doc.contains("Epoch-Based Reclamation"));
    }

    #[test]
    fn test_lock_free_treiber_stack() {
        let doc = LockFreeDataStructures::treiber_stack_concept();
        assert!(doc.contains("Treiber Stack"));
        assert!(doc.contains("push"));
        assert!(doc.contains("pop"));
        assert!(doc.contains("CAS"));
    }

    #[test]
    fn test_lock_free_michael_scott_queue() {
        let doc = LockFreeDataStructures::michael_scott_queue_concept();
        assert!(doc.contains("Michael-Scott Queue"));
        assert!(doc.contains("enqueue"));
        assert!(doc.contains("dequeue"));
        assert!(doc.contains("dummy node"));
    }

    #[test]
    fn test_lock_free_when_to_use() {
        let doc = LockFreeDataStructures::when_to_use_lock_free();
        assert!(doc.contains("High Contention"));
        assert!(doc.contains("Low Latency"));
        assert!(doc.contains("crossbeam-queue"));
    }

    #[test]
    fn test_lock_free_print_overview() {
        LockFreeDataStructures::print_overview();
    }
}
