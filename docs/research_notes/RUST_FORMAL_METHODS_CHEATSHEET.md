# Rust形式化方法速查卡

> **一页纸速查** - 核心概念、定理、模式快速参考

---

## 核心概念 (Core Concepts)

### 所有权三规则

```
1. 每个值有且只有一个所有者
2. 所有者离开作用域，值被丢弃
3. 所有权可以转移(Move)或借用(Borrow)
```

### 借用两规则

```
规则1: 要么一个可变引用(&mut)，要么多个不可变引用(&)
规则2: 引用必须始终有效（不能悬垂）
```

### 生命周期关系

```
'a: 'b  →  'a 至少和 'b 一样长
&'a T   →  引用存活至少 'a
T: 'a   →  T中所有引用存活至少 'a
```

---

## 核心定理 (Core Theorems)

| 定理 | 陈述 | 直觉 |
| :--- | :--- | :--- |
| **T-OW2** | 每个值只有一个所有者 | 防止重复释放 |
| **T-BR1** | 借用检查通过 ⇒ 无数据竞争 | 编译时并发安全 |
| **T-TY3** | 良类型程序不会崩溃 | 类型即证明 |
| **T-LF2** | 引用不活得比数据长 | 防止悬垂指针 |

---

## Send与Sync矩阵

| 类型 | Send | Sync | 使用场景 |
| :--- | :--- | :--- | :--- |
| `T` | ✅(若T:Send) | ✅(若T:Sync) | 普通类型 |
| `&T` | ✅(若T:Sync) | ✅(若T:Sync) | 共享引用 |
| `&mut T` | ✅(若T:Send) | ✅(若T:Sync) | 可变引用 |
| `Box<T>` | ✅ | ✅(若T:Sync) | 堆分配 |
| `Rc<T>` | ❌ | ❌ | 单线程引用计数 |
| `Arc<T>` | ✅ | ✅(若T:Sync) | 多线程引用计数 |
| `Cell<T>` | ✅ | ❌ | 内部可变性 |
| `RefCell<T>` | ✅ | ❌ | 运行时借用检查 |
| `Mutex<T>` | ✅ | ✅ | 互斥锁 |
| `RwLock<T>` | ✅ | ✅ | 读写锁 |

**记忆口诀**: `Sync` = `&T: Send`

---

## 型变规则 (Variance)

```
协变 (+):  Box<T>      T <: U → Box<T> <: Box<U>
协变 (+):  Vec<T>      T <: U → Vec<T> <: Vec<U>
协变 (+):  Option<T>   T <: U → Option<T> <: Option<U>

逆变 (-):  fn(T)       T <: U → fn(U) <: fn(T)

不变 (=):  &mut T      T = U → &mut T = &mut U
不变 (=):  Cell<T>     T = U → Cell<T> = Cell<U>
```

---

## 分布式模式速查

| 模式 | 问题 | 解决方案 | Rust实现 |
| :--- | :--- | :--- | :--- |
| **Saga** | 长事务 | 分解+补偿 | Result链+回滚函数 |
| **CQRS** | 读写冲突 | 分离读写模型 | Event Store + 投影 |
| **Circuit Breaker** | 级联故障 | 快速失败 | 状态机+错误计数 |
| **Bulkhead** | 资源耗尽 | 资源隔离 | Semaphore/semaphore |
| **Retry** | 瞬时故障 | 重试+退避 | backoff crate |

---

## 常见错误与修复

### 错误1: 使用已移动值

```rust
// ❌ 错误
let x = String::from("hello");
let y = x;
println!("{}", x);  // x已被移动

// ✅ 修复
let y = x.clone();   // 克隆
// 或
let y = &x;          // 借用
```

### 错误2: 借用冲突

```rust
// ❌ 错误
let mut x = 5;
let r1 = &x;
let r2 = &mut x;  // 不能同时有不可变和可变借用
println!("{}", r1);

// ✅ 修复
{
    let r1 = &x;
    println!("{}", r1);
} // r1在这里结束
let r2 = &mut x;  // OK
```

### 错误3: Rc跨线程

```rust
// ❌ 错误
let data = Rc::new(5);
thread::spawn(move || {
    println!("{}", data);  // Rc不是Send
});

// ✅ 修复
let data = Arc::new(5);  // 使用Arc代替Rc
thread::spawn(move || {
    println!("{}", data);  // OK
});
```

---

## 证明技术速查

| 技术 | 适用场景 | 关键步骤 |
| :--- | :--- | :--- |
| **结构归纳** | 归纳数据类型 | 基础+归纳步骤 |
| **规则归纳** | 归纳关系 | 覆盖所有规则 |
| **反证法** | 否定性质 | 假设反面→矛盾 |
| **案例分析** | 有限情况 | 穷举所有情况 |

---

## 学习路径速查

### 初学者 (2-4周)

```
所有权 → 借用 → 生命周期 → Send/Sync
```

### 进阶者 (4-8周)

```
形式化定义 → 核心定理 → 型变 → 证明思路
```

### 专家 (8-24周)

```
Coq → Iris → RustBelt → 工具开发
```

---

## 文档导航

| 需求 | 文档 |
| :--- | :--- |
| 查概念定义 | [形式化概念百科](./FORMAL_CONCEPTS_ENCYCLOPEDIA.md) |
| 查定理证明 | [定理汇编](./THEOREMS_AND_PROOF_STRATEGIES.md) |
| 查学习路径 | [学习路径](./LEARNING_PATH_COMPREHENSIVE.md) |
| 查错误修复 | [反例汇编](./COUNTER_EXAMPLES_COMPENDIUM.md) |
| 查方法论 | [认知论证框架](./COGNITIVE_ARGUMENTATION_FRAMEWORK.md) |

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-23
**用途**: 快速参考，一页纸掌握核心
