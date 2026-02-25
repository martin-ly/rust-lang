# 并发概念族谱

> **创建日期**: 2026-02-24
> **状态**: ✅ 新建 (15/15思维导图)
> **任务ID**: P1-W6-T3

---

## 并发概念全景

```text
                        并发概念族
                               │
        ┌──────────────────────┼──────────────────────┐
        │                      │                      │
   【线程】                【同步原语】            【异步】
        │                      │                      │
    ├─OS线程              ├─互斥锁              ├─Future
    │  ├─spawn            │  ├─Mutex            │  ├─状态机
    │  ├─join             │  └─RwLock           │  ├─轮询
    │  └─park             │                      │  └─唤醒
    │                     ├─信号量              │
    ├─线程池              │  ├─Semaphore        ├─async/await
    │  └─rayon            │  └─Atomic           │  ├─语法糖
    │                     │                      │  └─状态机转换
    └─线程本地            ├─屏障                │
       └─ThreadLocal      │  └─Barrier          ├─Pin
                          │                      │  └─固定位置
                          ├─条件变量            │
                          │  └─Condvar          └─Executor
                          │                      ├─调度器
                          └─原子操作            └─Reactor
                             ├─AtomicUsize
                             ├─AtomicBool
                             └─内存排序
                                      │
   【Send/Sync】           【内存模型】
        │                      │
    ├─Send                ├─Happens-Before
    │  └─跨线程转移       ├─Acquire-Release
    │                      ├─Sequential
    └─Sync                └─Consistency
       └─跨线程共享
```

---

## 一、线程 (Thread)

### 1.1 OS线程

```text
OS线程
├── 创建
│   └── std::thread::spawn
│
├── 等待
│   └── JoinHandle::join
│
├── 暂停
│   └── thread::park / thread::unpark
│
└── 线程本地存储
    └── thread_local!宏
```

### 1.2 线程池

```text
线程池
├── rayon
│   ├── parallel iterators
│   ├── join!
│   └── scope
│
└── threadpool crate
    └── 自定义线程池
```

---

## 二、同步原语

### 2.1 互斥锁 (Mutex)

```text
Mutex<T>
├── 独占访问
│   └── lock() -> MutexGuard
│
├── 自动解锁
│   └── Drop时释放
│
├── 线程安全
│   └── T: Send
│
└─- Send + Sync
```

### 2.2 读写锁 (RwLock)

```text
RwLock<T>
├── 多读
│   └── read() -> RwLockReadGuard
│
├── 单写
│   └── write() -> RwLockWriteGuard
│
└── 适用场景
    └── 读多写少
```

### 2.3 原子操作

```text
原子操作
├── 类型
│   ├── AtomicUsize / AtomicIsize
│   ├── AtomicU32 / AtomicI32
│   ├── AtomicU64 / AtomicI64
│   ├── AtomicBool
│   └── AtomicPtr<T>
│
├── 操作
│   ├── load/store
│   ├── fetch_add/fetch_sub
│   ├── compare_exchange
│   └── swap
│
└── 内存排序
    ├── Relaxed
    ├── Acquire
    ├── Release
    ├── AcqRel
    └── SeqCst
```

### 2.4 其他原语

```text
其他原语
├── Semaphore
│   └── 许可数量控制
│
├── Barrier
│   └── 等待所有线程到达
│
└── Condvar
    └── 条件变量
```

---

## 三、异步 (Async)

### 3.1 Future

```text
Future
├── 状态
│   ├── Pending
│   └── Ready(Output)
│
├── 轮询
│   └── poll() -> Poll
│
├── 唤醒
│   └── Waker::wake()
│
└── 组合
    ├── then
    ├── map
    └── join/select
```

### 3.2 async/await

```text
async/await
├── async fn
│   └── 返回impl Future
│
├── async block
│   └── async { ... }
│
└── .await
    └── 挂起点
```

### 3.3 Pin

```text
Pin<P>
├── 固定位置
│   └── 防止移动
│
├── 自引用结构
│   └── async状态机
│
└─- Unpin trait
    └── 标记可安全移动
```

### 3.4 执行器与反应器

```text
运行时组件
├── Executor (执行器)
│   ├── 调度任务
│   ├── 工作窃取
│   └── 任务队列
│
└── Reactor (反应器)
    ├── IO事件监听
    ├── epoll/kqueue/IOCP
    └── 唤醒任务
```

---

## 四、Send与Sync

### 4.1 Send

```text
Send
├── 定义
│   └── 可安全跨线程转移所有权
│
├── T: Send
│   └── 所有权转移安全
│
└── 示例
    ├── i32, String, Vec<T> ✅
    ├── Rc<T> ❌
    └── *const T ❌
```

### 4.2 Sync

```text
Sync
├── 定义
│   └── 可安全跨线程共享(&T: Send)
│
├── T: Sync
│   └── &T可安全传递给其他线程
│
├── 等价定义
│   └── &T: Send
│
└── 示例
    ├── i32, String ✅
    ├── Cell<T> ❌
    └── RefCell<T> ❌
```

### 4.3 Send/Sync关系

```text
Send/Sync组合
├── T: Send + Sync
│   ├── i32, String
│   ├── Vec<T>, Box<T>
    └── Arc<T> (T: Sync)
│
├── T: Send + !Sync
│   ├── Cell<T>
│   ├── RefCell<T>
│   └── mpsc::Sender<T>
│
├── T: !Send + Sync
│   └── (几乎不存在)
│
└── T: !Send + !Sync
    └── Rc<T>
    └── *const T
```

---

## 五、内存模型

### 5.1 Happens-Before

```text
Happens-Before关系
├── 程序顺序
├── 线程间同步
│   ├── 锁释放 -> 锁获取
│   ├── 线程启动 -> 线程执行
│   └── 线程完成 -> join返回
│
└── 原子操作
    └── Release -> Acquire
```

### 5.2 内存排序

```text
内存排序
├── Relaxed
│   └── 仅原子性，无顺序保证
│
├── Acquire
│   └── 获取操作，防止后续重排序
│
├── Release
│   └── 释放操作，防止先前重排序
│
├── AcqRel
│   └── Acquire + Release
│
└── SeqCst
    └── 顺序一致性，最强保证
```

---

## 六、与所有权的关系

```text
并发安全基于所有权
        │
        ├──→ 所有权唯一性
        │       └── Mutex/RwLock保证互斥
        │
        ├──→ 借用规则
        │       └── Send/Sync基于借用
        │
        └──→ 生命周期
                └── 跨线程引用有效性
```

---

## 七、形式化保证

### 定理

| 定理 | 描述 |
| :--- | :--- |
| T-BR1 | 借用检查通过 ⇒ 无数据竞争 |
| SEND-T1 | Send类型可安全跨线程转移 |
| SYNC-T1 | Sync类型可安全跨线程共享 |

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-24
**状态**: ✅ 已完成 - 并发概念族谱 (15/15)
