# 所有权转移选择决策树

> **创建日期**: 2026-02-24
> **级别**: L1/L2
> **类型**: 决策树

---

## 决策流程

```text
数据需要如何使用？
│
├── 单一所有者
│   ├── 需要转移所有权
│   │   ├── 值较大 → 使用Box<T>
│   │   └── 值较小 → 直接Move
│   │
│   └── 不需要转移
│       ├── 固定大小 → 栈分配
│       └── 动态大小 → 使用Vec/String
│
├── 多所有者
│   ├── 只读共享
│   │   ├── 编译期确定 → 使用引用&
│   │   └── 运行期共享 → 使用Rc<T>
│   │       └── 跨线程 → 使用Arc<T>
│   │
│   └── 可变共享
│       ├── 单线程 → 使用RefCell<T> + Rc<T>
│       └── 跨线程 → 使用Mutex<T> + Arc<T>
│               └── 或 RwLock<T> + Arc<T>
│
└── 特殊场景
    ├── 循环引用
    │   └── 使用Weak<T>
    │
    └── 临时借用
        └── 使用& / &mut
```

---

## 选择矩阵

| 场景 | 类型 | 线程安全 |
| :--- | :--- | :--- |
| 单所有 | `Box<T>` | 取决于T |
| 多共享只读 | `Rc<T>` | ❌ |
| 多共享只读(跨线程) | `Arc<T>` | ✅ |
| 多可变(单线程) | `Rc<RefCell<T>>` | ❌ |
| 多可变(跨线程) | `Arc<Mutex<T>>` | ✅ |
| 循环引用 | `Weak<T>` | 取决于容器 |

---

## 代码示例

```rust
// 单所有
let data = Box::new(vec![1, 2, 3]);

// 多共享
let shared = Rc::new(vec![1, 2, 3]);
let shared2 = Rc::clone(&shared);

// 跨线程共享
let thread_safe = Arc::new(Mutex::new(0));
let thread_safe2 = Arc::clone(&thread_safe);
```

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-24
**状态**: ✅ 已完成 - 决策树 9/10
