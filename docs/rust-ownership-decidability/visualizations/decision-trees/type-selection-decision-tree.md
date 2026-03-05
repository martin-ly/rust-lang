# Rust类型选择决策树

> **根据场景选择最合适的类型和智能指针**

---

## 1. 智能指针选择决策树

```text
需要堆分配?
├── 否 → 使用栈分配或静态分配
│         └── let x = T::new();
│
└── 是 → 需要共享所有权?
          │
          ├── 否 → Box<T>
          │         ├── 唯一所有权
          │         ├── 大小确定类型
          │         └── DST (dyn Trait, [T])
          │
          └── 是 → 需要多线程共享?
                    │
                    ├── 否 → Rc<T>
                    │         ├── 单线程
                    │         ├── 引用计数
                    │         └── 循环引用风险 → Rc<RefCell<T>> + Weak<T>
                    │
                    └── 是 → Arc<T>
                              ├── 多线程 (Send + Sync)
                              ├── 原子引用计数
                              └── 内部可变性 → Arc<Mutex<T>> / Arc<RwLock<T>>
```

---

## 2. 内部可变性选择决策树

```text
需要内部可变性?
├── 否 → 使用普通可变引用 &mut T
│
└── 是 → 单线程还是多线程?
          │
          ├── 单线程
          │         │
          │         ├── 类型实现Copy? → Cell<T>
          │         │                    ├── get()/set()
          │         │                    └── 无借用，直接复制
          │         │
          │         └── 非Copy类型 → RefCell<T>
          │                           ├── borrow() / borrow_mut()
          │                           └── 运行时检查，panic风险
          │
          └── 多线程
                    │
                    ├── 简单计数器/标志 → Atomic*
                    │                       ├── AtomicUsize, AtomicBool
                    │                       └── 无锁，最高性能
                    │
                    ├── 多读一写场景 → RwLock<T>
                    │                   ├── read() 允许多个
                    │                   └── write() 独占
                    │
                    └── 一般互斥 → Mutex<T>
                                   ├── lock() 独占访问
                                   └── Poison错误处理
```

---

## 3. 引用类型选择决策树

```text
需要引用?
├── 否 → 使用所有权转移
│         └── fn take(t: T) { ... }
│
└── 是 → 需要修改数据?
          │
          ├── 否 → 共享引用 &T
          │         ├── 只读访问
          │         ├── 多个共存
          │         └── 编译时检查
          │
          └── 是 → 编译时确定借用模式?
                    │
                    ├── 是 → 可变引用 &mut T
                    │         ├── 读写访问
                    │         ├── 唯一性 (不能与其他借用共存)
                    │         └── 编译时检查
                    │
                    └── 否 → 内部可变性
                               ├── 单线程: RefCell<T>
                               └── 多线程: Mutex<T> / RwLock<T>
```

---

## 4. 集合类型选择决策树

```text
需要集合类型?
│
├── 顺序访问，动态大小
│         │
│         ├── 只在末尾操作 → Vec<T>
│         │                   ├── push/pop O(1)
│         │                   └── 随机访问 O(1)
│         │
│         └── 双端操作 → VecDeque<T>
│                         ├── push_front/pop_front O(1)
│                         └── push_back/pop_back O(1)
│
├── 键值查找
│         │
│         ├── 需要顺序遍历 → BTreeMap<K,V>
│         │                   ├── O(log n) 操作
│         │                   └── 按键排序
│         │
│         └── 只关心查找速度 → HashMap<K,V>
│                               ├── O(1) 平均
│                               └── 哈希要求: K: Eq + Hash
│
├── 集合运算
│         ├── 有序集合 → BTreeSet<T>
│         └── 哈希集合 → HashSet<T>
│
├── 链表场景
│         ├── 频繁中间插入/删除 → LinkedList<T>
│         └── 其他 → Vec<T> (缓存友好)
│
└── 优先队列 → BinaryHeap<T>
               ├── max-heap (默认)
               └── push/pop O(log n)
```

---

## 5. 错误处理选择决策树

```text
函数可能失败?
├── 否 → 返回 T
│         └── fn success() -> T { ... }
│
└── 是 → 失败原因重要?
          │
          ├── 否 (只是可能没有值) → Option<T>
          │                           ├── Some(T) 有值
          │                           └── None 无值
          │
          └── 是 (需要错误信息) → Result<T, E>
                                   ├── Ok(T) 成功
                                   └── Err(E) 失败，带错误信息

错误处理策略?
├── 当前函数能处理? → match 处理
│                     └── match result { Ok(v) => ..., Err(e) => ... }
│
├── 需要传播给调用者? → ? 运算符
│                       └── let x = may_fail()?
│
├── 不可恢复错误? → panic!
│                   └── panic!("critical error: {}", msg)
│
└── 原型/确定不会失败? → unwrap/expect
                         ├── value.unwrap() (危险!)
                         └── value.expect("reason") (稍好)
```

---

## 6. 并发模型选择决策树

```text
需要并发?
│
├── 共享状态并发
│         │
│         ├── 只读数据 → Arc<T>
│         │             └── 多个线程只读
│         │
│         └── 可变共享
│                   ├── 简单计数器 → Atomic*
│                   │                 └── fetch_add, compare_exchange
│                   │
│                   ├── 复杂数据结构 → Arc<Mutex<T>>
│                   │                   ├── 互斥访问
│                   │                   └── 注意死锁
│                   │
│                   └── 多读一写 → Arc<RwLock<T>>
│
├── 消息传递并发
│         ├── 异步通道 → tokio::sync::mpsc
│         ├── 同步通道 → std::sync::mpsc
│         └── 广播 → tokio::sync::broadcast
│
└── 任务并行
          ├── CPU密集型 → rayon::join, par_iter
          │               └── 数据并行，工作窃取
          │
          └── IO密集型 → async/await + Tokio
                         └── 多路复用，非阻塞
```

---

## 7. 生命周期标注决策树

```text
函数使用引用参数?
├── 否 → 不需要生命周期
│         └── fn foo(x: T) { ... }
│
└── 是 → 多个引用参数?
          │
          ├── 否 → 省略规则适用?
          │         │
          │         ├── 是 → 省略不写
          │         │         └── fn foo(x: &T) -> &U { ... }
          │         │
          │         └── 否 → 显式标注 'a
│         │                   └── fn foo<'a>(x: &'a T) -> &'a U { ... }
          │
          └── 是 → 引用之间有关系?
                    │
                    ├── 无关系 → 独立生命周期
                    │             └── fn foo<'a, 'b>(x: &'a T, y: &'b U)
                    │
                    └── 有关系 → 约束关系
                                 ├── 相同生命周期
                                 │   └── fn foo<'a>(x: &'a T, y: &'a U)
                                 │
                                 └── 包含关系
                                     └── fn foo<'a, 'b: 'a>(x: &'a T, y: &'b U)
                                         ('b 至少和 'a 一样长)
```

---

## 8. 何时使用unsafe决策树

```text
需要使用unsafe?
│
├── 否 (能用safe Rust实现) → 坚持用safe!
│                             └── Rust的保证值得保留
│
└── 是 → 使用场景?
          │
          ├── FFI (与C交互)
          │         ├── 声明extern函数
          │         ├── 原始指针操作
          │         └── 安全封装为Safe API
          │
          ├── 性能关键路径
          │         ├── 原始指针算术
          │         ├── unchecked索引
          │         └── 内联汇编
          │
          ├── 底层内存操作
          │         ├── MaybeUninit
          │         ├── 自定义分配器
          │         └── transmute
          │
          └── 特殊数据结构
                    ├── 自引用结构 (Pin)
                    ├── 侵入式链表
                    └── 共享可变 (原始指针)

unsafe使用原则:
1. 最小化unsafe代码块
2. 文档化安全不变式
3. 封装为safe API
4. 用Miri测试验证
```

---

## 快速参考表

| 场景 | 推荐选择 | 避免 |
|:---|:---|:---|
| 唯一堆所有权 | `Box<T>` | `Rc<T>` / `Arc<T>` |
| 单线程共享 | `Rc<T>` | `Arc<T>` (原子操作开销) |
| 多线程共享 | `Arc<T>` | `Rc<T>` (!Send) |
| 内部可变 | `RefCell<T>` / `Mutex<T>` | 全局可变状态 |
| 可选值 | `Option<T>` | `null` 指针 |
| 错误处理 | `Result<T,E>` | `panic!` (可恢复错误) |
| 并发通信 | `Channel` | 共享可变状态 |

---

**维护者**: Rust Decision Trees Team
**更新日期**: 2026-03-05
**对齐版本**: Rust 1.93.1
