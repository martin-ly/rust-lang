# 反模式与边界

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-12
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 100% 完成

---

## 宗旨

将设计模式反例、反模式与形式化边界衔接，提供**实质内容**：形式化对应、与安全边界关系、规避策略、与 FORMAL_PROOF_SYSTEM_GUIDE 反例索引的衔接。

---

## 一、反模式与安全边界

### 1.1 形式化定义

**Def AP1（反模式）**：违反设计模式不变式或 Rust 安全规则的实现；$\mathit{SafeB}(P) = \mathrm{Inexpr}$ 或违反 [ownership_model](../../formal_methods/ownership_model.md)、[borrow_checker_proof](../../formal_methods/borrow_checker_proof.md) 规则。

**Axiom AP1**：反模式导致 UB、数据竞争、或逻辑错误；与 [safe_unsafe_matrix](05_boundary_system/safe_unsafe_matrix.md) SBM-T2、SBM-L2 衔接。

### 1.2 反模式分类

| 分类 | 边界 | 示例 |
| :--- | :--- | :--- |
| **所有权反模式** | 违反 ownership | 使用已移动值、循环引用泄漏 |
| **借用反模式** | 违反 borrow | 双重可变借用、迭代中修改集合 |
| **并发反模式** | 违反 Send/Sync | Rc 跨线程、共享可变无同步 |
| **设计模式反模式** | 违反模式不变式 | 违反 Builder 必填、Singleton 多实例 |

---

## 二、13 反例索引（与 FORMAL_PROOF_SYSTEM_GUIDE 衔接）

| 模式 | 反例 | 后果 | 规避 |
| :--- | :--- | :--- | :--- |
| Singleton | 全局可变未同步 | 数据竞争 | OnceLock、LazyLock |
| Observer | 共享可变无 Mutex | 数据竞争 | channel、Arc\<Mutex> |
| Composite | 循环引用 | 所有权无法表达 | 避免自引用、用 Weak |
| Builder | build 前必填未设 | 运行时错误 | 类型状态、ok_or |
| Memento | 恢复非法状态 | 不变式违反 | 校验、Clone 约束 |
| Iterator | 迭代中修改集合 | 借用冲突 | 借用规则 1 |
| Prototype | Clone 浅拷贝共享 | 隐式耦合 | 深拷贝、显式 |
| Flyweight | 跨线程用 Rc | 编译错误 | Arc |
| Mediator | 循环引用 | 泄漏 | Weak 打破环 |
| Chain | 链成环 | 无限循环 | 无环约束 |
| 其他 | 见 FORMAL_PROOF_SYSTEM_GUIDE | - | - |

**完整反例**：见 [FORMAL_PROOF_SYSTEM_GUIDE](../../FORMAL_PROOF_SYSTEM_GUIDE.md#设计模式反例)。

---

## 三、常见反模式详解（含代码示例）

### 3.1 所有权反模式

| 反模式 | 形式化 | 规避 |
| :--- | :--- | :--- |
| 使用已移动值 | 违反 ownership 规则 2 | 移动后不再使用 |
| 循环 Rc | $\text{strong\_count} \geq 1$ 永不归零 | 用 Weak 打破环 |
| 过早 drop | 违反 outlives | 显式生命周期 |

**代码示例：使用已移动值**:

```rust
// 错误：s 已移动至 s2，不能再使用
let s = String::from("hello");
let s2 = s;
println!("{}", s);  // 编译错误：value used after move
```

**代码示例：循环 Rc 泄漏**:

```rust
use std::rc::Rc;
use std::cell::RefCell;

struct Node {
    next: Option<Rc<RefCell<Node>>>,
}
let a = Rc::new(RefCell::new(Node { next: None }));
let b = Rc::new(RefCell::new(Node { next: Some(a.clone()) }));
a.borrow_mut().next = Some(b.clone());  // 环：a → b → a
// drop 时 strong_count 永不归零，内存泄漏
```

### 3.2 借用反模式

| 反模式 | 形式化 | 规避 |
| :--- | :--- | :--- |
| 双重可变借用 | 违反 borrow 规则 1 | 作用域分离 |
| 迭代中修改 | 违反 borrow 规则 1 | 先收集再修改 |
| 返回局部引用 | 违反 lifetime 规则 | 返回 owned 或 'a 引用 |

**代码示例：迭代中修改集合**:

```rust
// 错误：for 循环持有 &mut v，与 v.push 冲突
let mut v = vec![1, 2, 3];
for x in &mut v {
    v.push(*x + 1);  // 编译错误：cannot borrow `v` as mutable
}
```

**代码示例：Clone 满足借用（过度克隆）**:

```rust
// 反模式：为满足借用而频繁 clone，丧失零成本抽象
fn process(data: &Vec<String>) -> Vec<String> {
    data.iter()
        .map(|s| s.clone())  // 每次迭代 clone
        .filter(|s| s.len() > 0)
        .map(|s| s.clone())  // 再次 clone
        .collect()
}
// 更好：用 &str、迭代器链、或 Cow 避免不必要的 clone
```

### 3.3 设计模式反模式

| 反模式 | 形式化 | 规避 |
| :--- | :--- | :--- |
| 单产品用 Abstract Factory | 过度设计 | Factory Method |
| 简单调用用 Chain | 不必要的链 | 直接调用 |
| 无共享用 Flyweight | 无收益 | 普通创建 |
| 顺序操作用 Mediator | 过度解耦 | 直接调用 |

**代码示例：过度泛型**:

```rust
// 反模式：三层泛型，调用处类型推断困难，编译慢
fn process<A, B, C, F, G>(a: A, b: B, f: F, g: G) -> C
where
    A: Trait1,
    B: Trait2<A>,
    F: Fn(A) -> B,
    G: Fn(B) -> C,
{ g(f(a)) }
// 更好：按需抽象，优先 impl Trait 或具体类型
```

### 3.4 并发反模式

| 反模式 | 形式化 | 规避 |
| :--- | :--- | :--- |
| Rc 跨线程 | 违反 Send | 用 Arc |
| static mut 无同步 | 数据竞争 | OnceLock、Mutex |
| 共享可变无锁 | 数据竞争 | Mutex、Channel |

---

## 四、反模式与三维边界

| 反模式 | 安全边界 | 支持边界 | 表达边界 |
| :--- | :--- | :--- | :--- |
| static mut 多线程 | Inexpr | - | - |
| Rc 跨线程 | 编译错误 | - | - |
| 双重可变借用 | 编译错误 | - | - |
| 误选模式 | - | - | 过度设计 |

---

## 五、反模式规避策略（实质指南）

| 反模式类 | 规避策略 | 工具/模式 |
| :--- | :--- | :--- |
| 所有权 | 显式作用域、避免自引用环 | Weak 打破 Rc 环 |
| 借用 | 先 collect 再修改、缩短借用范围 | `std::mem::take` 转移 |
| 并发 | 选 Send/Sync 类型、消息传递优先 | channel、Arc\<Mutex> |
| 设计模式误选 | 按需求查 [03_semantic_boundary_map](02_workflow_safe_complete_models/03_semantic_boundary_map.md) | 模式选取示例 |
| 过度抽象 | 从具体开始，按需泛型 | impl Trait、trait 按需 |

---

## 八、完整规避示例（场景→反模式→正确写法）

### 场景 1：需要共享可变

**反模式**：`Rc<RefCell<T>>` 跨线程。

```rust
// 错误：Rc 非 Send
let data = Rc::new(RefCell::new(0));
thread::spawn(move || {
    data.borrow_mut().add(1);  // 编译错误
});
```

**正确**：`Arc<Mutex<T>>`。

```rust
let data = Arc::new(Mutex::new(0));
let data_clone = Arc::clone(&data);
thread::spawn(move || {
    *data_clone.lock().unwrap() += 1;
});
```

### 场景 2：迭代中修改

**反模式**：`for x in &mut v { v.push(...); }`。

**正确**：先收集再修改。

```rust
let to_add: Vec<_> = v.iter().filter(|x| x > 0).cloned().collect();
v.extend(to_add);
```

### 场景 3：单产品却用 Abstract Factory

**反模式**：仅需一种按钮却定义 `ButtonFactory` 产品族。

**正确**：用 Factory Method。

```rust
trait Creator {
    fn create(&self) -> Box<dyn Button>;
}
```

### 场景 4：无共享用 Flyweight

**反模式**：对象仅创建一次却用 `Arc` 缓存。

**正确**：直接创建。

```rust
let item = Item::new();  // 无需缓存
```

### 场景 5：错误类型用 unwrap

**反模式**：`let x = result.unwrap();` 在库代码中。

**正确**：`?` 传播或 `match` 处理。

```rust
let x = result?;
// 或
let x = match result {
    Ok(v) => v,
    Err(e) => return Err(e.into()),
};
```

---

## 六、与 05_boundary_system 衔接

- [safe_unsafe_matrix](05_boundary_system/safe_unsafe_matrix.md)：SBM-L2 反模式边界
- [02_workflow 03_semantic_boundary_map](02_workflow_safe_complete_models/03_semantic_boundary_map.md)：反模式误选表
- [01_design_patterns_formal](01_design_patterns_formal/README.md)：各模式反例

---

## 七、引用

- [FORMAL_PROOF_SYSTEM_GUIDE](../../FORMAL_PROOF_SYSTEM_GUIDE.md#设计模式反例)
- [rust-unofficial/patterns](https://rust-unofficial.github.io/patterns/) Anti-patterns
- [safe_unsafe_matrix](05_boundary_system/safe_unsafe_matrix.md)
