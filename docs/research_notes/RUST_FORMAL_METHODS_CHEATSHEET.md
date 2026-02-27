# Rust形式化方法速查卡

> **创建日期**: 2026-02-24
> **最后更新**: 2026-02-28
> **状态**: ✅ 已扩展
> **版本**: Rust 1.93.0+ (Edition 2024)

---

## 核心概念速查

### 所有权规则

```rust
// 1. 每个值有唯一所有者
let s = String::from("hello");  // s是所有者

// 2. 值离开作用域时被释放
{ let s = String::from("hi"); }  // s在这里drop

// 3. 所有权可以移动
let s1 = s;  // s所有权移动到s1，s失效

// 4. 借用不获取所有权
let len = calculate_length(&s1);  // 借用s1
```

### 借用规则

| 规则 | 说明 | 代码 |
| :--- | :--- | :--- |
| R1 | 可多不可变借用 | `let r1 = &s; let r2 = &s;` |
| R2 | 仅一可变借用 | `let r = &mut s;` |
| R3 | 不可共存 | `&s` 和 `&mut s` 不能同时 |

---

## 生命周期速查

### 语法

```rust
// 显式标注
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str

// 生命周期约束
fn foo<'a, 'b>(x: &'a str, y: &'b str) -> &'a str
where 'a: 'b  // 'a 至少和 'b 一样长

// 结构体
struct Parser<'a> { input: &'a str }
```

### 省略规则

1. 每个引用参数有自己的生命周期
2. 单一输入 → 应用到输出
3. `&self` → 应用到输出

---

## Send/Sync速查

| 类型 | Send | Sync | 说明 |
| :--- | :--- | :--- | :--- |
| `i32`, `bool` | ✅ | ✅ | 原始类型 |
| `String`, `Vec` | ✅ | ✅ | 拥有数据 |
| `Rc` | ❌ | ❌ | 非原子计数 |
| `Arc` | ✅ | ✅ | 原子计数 |
| `RefCell` | ✅ | ❌ | 内部可变 |
| `Mutex` | ✅ | ✅ | 提供Sync |

**规则**: `T: Sync` 当且仅当 `&T: Send`

---

## 核心定理速查

| 定理 | 内容 | 位置 |
| :--- | :--- | :--- |
| T-OW2 | 所有权唯一性 | ownership_model.md |
| T-BR1 | 数据竞争自由 | borrow_checker_proof.md |
| T-TY3 | 类型安全 | type_system_foundations.md |
| LF-T1 | 生命周期正确性 | lifetime_formalization.md |
| T-ASYNC | 异步安全 | async_state_machine.md |
| PIN-T1 | Pin位置稳定性 | pin_self_referential.md |

---

## 证明技术速查

| 技术 | 适用场景 | 形式化工具 |
| :--- | :--- | :--- |
| 结构归纳 | 归纳类型 | Coq induction |
| 反证法 | 否定性质 | Coq unfold not |
| 分离逻辑 | 资源推理 | Iris |
| 类型推导 | 进展+保持 | Coq typing |
| 不变式 | 循环/递归 | assert |

---

## 验证工具速查

| 工具 | 类型 | 用途 | 命令 |
| :--- | :--- | :--- | :--- |
| Miri | 解释器 | UB检测 | `cargo +nightly miri test` |
| Kani | 模型检测 | 自动验证 | `cargo kani` |
| Clippy | Lint | 代码质量 | `cargo clippy` |
| Creusot | 演绎验证 | 契约证明 | `cargo creusot` |

---

## 设计模式速查

### 创建型

| 模式 | 用途 | Rust特色 |
| :--- | :--- | :--- |
| Factory | 对象创建 | 结合泛型 |
| Builder | 复杂构造 | 消费式builder |
| Singleton | 唯一实例 | `LazyLock` |

### 结构型

| 模式 | 用途 | Rust特色 |
| :--- | :--- | :--- |
| Adapter | 接口适配 | Trait实现 |
| Decorator | 动态增强 | Trait对象 |
| Proxy | 访问控制 | 智能指针 |

### 行为型

| 模式 | 用途 | Rust特色 |
| :--- | :--- | :--- |
| Iterator | 遍历 | 内置支持 |
| Observer | 事件通知 | 通道替代 |
| Strategy | 算法替换 | Trait对象 |

---

## unsafe速查

### 安全承诺

```rust
unsafe {
    // 开发者保证:
    // 1. 裸指针有效
    // 2. 不违反借用规则
    // 3. 满足类型不变式
}
```

### 常见unsafe操作

| 操作 | 安全条件 | 示例 |
| :--- | :--- | :--- |
| 裸指针解引用 | 指针有效 | `*ptr` |
| `transmute` | 布局兼容 | `mem::transmute` |
| `static mut` | 同步访问 | `unsafe { STATIC }` |
| FFI调用 | C契约满足 | `extern "C"` |

---

## 异步速查

### Future基础

```rust
async fn foo() -> i32 { 42 }

// 等价于
fn foo() -> impl Future<Output = i32> {
    async { 42 }
}
```

### 组合操作

| 操作 | 说明 | 示例 |
| :--- | :--- | :--- |
| `await` | 等待完成 | `let x = future.await;` |
| `join!` | 并行等待 | `join!(f1, f2)` |
| `select!` | 竞赛等待 | `select!(f1, f2)` |
| `spawn` | 后台任务 | `tokio::spawn(future)` |

### 取消安全

```rust
// ✅ 取消安全: 使用临时文件
async fn safe_write(path: &str, data: &[u8]) {
    let temp = format!("{}.tmp", path);
    tokio::fs::write(&temp, data).await?;
    tokio::fs::rename(&temp, path).await?;
}
```

---

## 并发模式速查

### 共享状态

```rust
// Mutex
let counter = Arc::new(Mutex::new(0));
*counter.lock().unwrap() += 1;

// RwLock
let data = Arc::new(RwLock::new(vec![]));
data.read().unwrap();
data.write().unwrap().push(1);
```

### 消息传递

```rust
// mpsc
let (tx, rx) = mpsc::channel();
tx.send(42).unwrap();
let val = rx.recv().unwrap();

// 广播
let (tx, _rx) = broadcast::channel(16);
tx.send("hello").unwrap();
```

---

## 常见错误速查

| 错误 | 原因 | 解决 |
| :--- | :--- | :--- |
| E0382 | 使用已移动值 | 克隆或重新设计 |
| E0499 | 多重可变借用 | 限制作用域 |
| E0502 | 借用冲突 | 分离使用 |
| E0597 | 引用活不长 | 扩大作用域 |

---

## 资源导航

| 资源 | 位置 | 用途 |
| :--- | :--- | :--- |
| 核心证明 | formal_methods/ | 形式化定义 |
| 设计模式 | software_design_theory/ | 架构参考 |
| 教程 | TUTORIAL_*.md | 学习路径 |
| 速查 | *_CHEATSHEET.md | 快速参考 |

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

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-28
**状态**: ✅ 已扩展 - Rust形式化方法速查卡完整版
