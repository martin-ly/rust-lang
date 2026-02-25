# Rust形式化方法 FAQ 汇总

> **创建日期**: 2026-02-24
> **目标**: 解答学习者最常见的问题
> **级别**: L1 (给人看的)

---

## 快速导航

- [Rust形式化方法 FAQ 汇总](#rust形式化方法-faq-汇总)
  - [快速导航](#快速导航)
  - [一、所有权与借用 (15问)](#一所有权与借用-15问)
    - [Q1: 什么是所有权？一句话解释](#q1-什么是所有权一句话解释)
    - [Q2: Move和Copy有什么区别？](#q2-move和copy有什么区别)
    - [Q3: 为什么需要借用？](#q3-为什么需要借用)
    - [Q4: \&和\&mut为什么不能同时存在？](#q4-和mut为什么不能同时存在)
    - [Q5: 什么是悬垂引用？Rust如何防止？](#q5-什么是悬垂引用rust如何防止)
    - [Q6: 如何理解"所有权系统防止内存泄漏"？](#q6-如何理解所有权系统防止内存泄漏)
    - [Q7: 为什么`Rc`不能跨线程？](#q7-为什么rc不能跨线程)
    - [Q8: `RefCell`和`Mutex`有什么区别？](#q8-refcell和mutex有什么区别)
    - [Q9: 什么是"内部可变性"模式？](#q9-什么是内部可变性模式)
    - [Q10: 如何理解`Box`、`Rc`、`Arc`的区别？](#q10-如何理解boxrcarc的区别)
    - [Q11: 为什么String不能Copy？](#q11-为什么string不能copy)
    - [Q12: `clone()`和`to_owned()`有什么区别？](#q12-clone和to_owned有什么区别)
    - [Q13: 如何修复"cannot borrow as mutable"错误？](#q13-如何修复cannot-borrow-as-mutable错误)
    - [Q14: `mem::swap`和`mem::replace`有什么用？](#q14-memswap和memreplace有什么用)
    - [Q15: 什么是"零成本抽象"？](#q15-什么是零成本抽象)
  - [二、类型系统 (10问)](#二类型系统-10问)
    - [Q16: 什么是类型安全？](#q16-什么是类型安全)
    - [Q17: `Sized` trait是什么？](#q17-sized-trait是什么)
    - [Q18: `impl Trait`和`dyn Trait`有什么区别？](#q18-impl-trait和dyn-trait有什么区别)
    - [Q19: 什么是型变(Variance)？](#q19-什么是型变variance)
    - [Q20: `'static`生命周期是什么意思？](#q20-static生命周期是什么意思)
    - [Q21: 什么是关联类型(Associated Type)？](#q21-什么是关联类型associated-type)
    - [Q22: 什么是泛型关联类型(GAT)？](#q22-什么是泛型关联类型gat)
    - [Q23: `const fn`和`fn`有什么区别？](#q23-const-fn和fn有什么区别)
    - [Q24: 什么是特化(Specialization)？](#q24-什么是特化specialization)
    - [Q25: 什么是空指针优化(Null Pointer Optimization)？](#q25-什么是空指针优化null-pointer-optimization)
  - [三、生命周期 (10问)](#三生命周期-10问)
    - [Q26: 生命周期省略规则是什么？](#q26-生命周期省略规则是什么)
    - [Q27: 生命周期约束如何写？](#q27-生命周期约束如何写)
    - [Q28: 什么是生命周期子类型？](#q28-什么是生命周期子类型)
    - [Q29: 为什么需要显式生命周期标注？](#q29-为什么需要显式生命周期标注)
    - [Q30: `for<'a>`语法是什么？](#q30-fora语法是什么)
    - [Q31: 结构体中的生命周期如何工作？](#q31-结构体中的生命周期如何工作)
    - [Q32: 自引用结构如何处理？](#q32-自引用结构如何处理)
    - [Q33: 异步函数中的生命周期](#q33-异步函数中的生命周期)
    - [Q34: 什么是`PhantomData`？](#q34-什么是phantomdata)
    - [Q35: 生命周期和泛型如何结合？](#q35-生命周期和泛型如何结合)
  - [四、并发与异步 (10问)](#四并发与异步-10问)
    - [Q36: Send和Sync有什么区别？](#q36-send和sync有什么区别)
    - [Q37: 为什么`Cell`不是Sync？](#q37-为什么cell不是sync)
    - [Q38: `Mutex`和`RwLock`怎么选？](#q38-mutex和rwlock怎么选)
    - [Q39: 什么是死锁？如何避免？](#q39-什么是死锁如何避免)
    - [Q40: async/await原理是什么？](#q40-asyncawait原理是什么)
    - [Q41: `Pin`是什么？为什么需要？](#q41-pin是什么为什么需要)
    - [Q42: `tokio::spawn`和`thread::spawn`区别？](#q42-tokiospawn和threadspawn区别)
    - [Q43: 什么是`Unpin`？](#q43-什么是unpin)
    - [Q44: `select!`宏是什么？](#q44-select宏是什么)
    - [Q45: 如何避免跨await持锁？](#q45-如何避免跨await持锁)
  - [五、形式化方法 (10问)](#五形式化方法-10问)
    - [Q46: 什么是L1/L2/L3证明？](#q46-什么是l1l2l3证明)
    - [Q47: T-OW2定理是什么？](#q47-t-ow2定理是什么)
    - [Q48: T-BR1定理是什么？](#q48-t-br1定理是什么)
    - [Q49: 形式化方法对普通开发者有什么用？](#q49-形式化方法对普通开发者有什么用)
    - [Q50: 如何学习形式化方法？](#q50-如何学习形式化方法)
  - [六、分布式与工作流 (5问)](#六分布式与工作流-5问)
    - [Q51: Saga模式解决什么问题？](#q51-saga模式解决什么问题)
    - [Q52: CQRS适合什么场景？](#q52-cqrs适合什么场景)
    - [Q53: 熔断器模式如何工作？](#q53-熔断器模式如何工作)
    - [Q54: 如何选择工作流引擎？](#q54-如何选择工作流引擎)
    - [Q55: 什么是补偿事务？](#q55-什么是补偿事务)

---

## 一、所有权与借用 (15问)

### Q1: 什么是所有权？一句话解释

**A**: 每个值在任意时刻有且只有一个所有者（变量），所有者离开作用域时值被自动释放。

**类比**: 就像一本书只能在一个人的书架上，当你把书送给别人，你的书架上就不再有这本书了。

---

### Q2: Move和Copy有什么区别？

**A**:

- **Move**: 转移所有权，原变量不再有效
- **Copy**: 复制值，原变量仍然有效

```rust
// Move示例
let x = String::from("hello");  // String不实现Copy
let y = x;                      // 所有权转移到y
// println!("{}", x);           // 错误！x已无效

// Copy示例
let x = 5;                      // i32实现Copy
let y = x;                      // 复制值
println!("{}", x);              // OK！x仍然有效
```

**记忆**: 复杂类型Move，简单类型Copy。

---

### Q3: 为什么需要借用？

**A**: 借用允许你临时使用值而不获取所有权，避免频繁转移所有权的麻烦。

```rust
fn print_length(s: &String) {  // 借用，不获取所有权
    println!("{}", s.len());
} // s在这里归还，但原变量仍然有效

fn main() {
    let s = String::from("hello");
    print_length(&s);  // 借用s
    print_length(&s);  // 可以再次借用！
    println!("{}", s); // OK，s仍然有效
}
```

---

### Q4: &和&mut为什么不能同时存在？

**A**: 防止数据竞争。如果允许多个读者和一个写者同时存在，读者可能读到正在被修改的数据。

**类比**: 图书馆的书

- `&`: 多人可以同时阅读（不可变借用）
- `&mut`: 一个人借走修改时，其他人不能看（可变借用）

```rust
let mut x = 5;
let r1 = &x;        // 读者1
let r2 = &x;        // 读者2
// let r3 = &mut x; // 错误！不能有写者
println!("{} {}", r1, r2); // 读者还在用
```

---

### Q5: 什么是悬垂引用？Rust如何防止？

**A**: 悬垂引用是指引用指向已经被释放的内存。Rust通过生命周期检查在编译时防止。

```rust
// ❌ 编译错误
fn dangling() -> &String {
    let s = String::from("hello");
    &s  // 错误！s将在函数结束时被释放
}

// ✅ 正确做法
fn not_dangling() -> String {
    let s = String::from("hello");
    s  // 转移所有权
}
```

---

### Q6: 如何理解"所有权系统防止内存泄漏"？

**A**: 严格来说，所有权系统主要防止**内存不安全**（use-after-free, double-free），而不是内存泄漏。

但Rust确实有助于减少内存泄漏：

- RAII模式：离开作用域自动释放
- 编译时检查：避免忘记释放

注意：`Rc`循环引用、`mem::forget`仍可能导致泄漏。

---

### Q7: 为什么`Rc`不能跨线程？

**A**: `Rc`使用非原子引用计数（不是线程安全的）。跨线程使用会导致数据竞争（计数更新冲突）。

使用`Arc`（原子引用计数）代替：

```rust
use std::sync::Arc;
use std::thread;

let data = Arc::new(5);
thread::spawn(move || {
    println!("{}", data);  // OK
});
```

---

### Q8: `RefCell`和`Mutex`有什么区别？

**A**:

- **RefCell**: 单线程运行时借用检查
- **Mutex**: 多线程互斥锁

```rust
use std::cell::RefCell;
use std::sync::Mutex;

// RefCell - 单线程
let cell = RefCell::new(5);
*cell.borrow_mut() = 10;  // 运行时检查

// Mutex - 多线程
let mutex = Mutex::new(5);
*mutex.lock().unwrap() = 10;  // 线程安全
```

---

### Q9: 什么是"内部可变性"模式？

**A**: 允许在不可变引用下修改数据，通过运行时检查保证安全。

常见类型：

- `Cell<T>`: 对于Copy类型
- `RefCell<T>`: 运行时借用检查
- `Mutex<T>`: 线程安全版本

使用场景：

- 缓存
- 计数器
- 延迟初始化

---

### Q10: 如何理解`Box`、`Rc`、`Arc`的区别？

**A**:

| 类型 | 所有权 | 线程安全 | 使用场景 |
| :--- | :--- | :--- | :--- |
| `Box<T>` | 唯一 | ✅ | 堆分配，单一所有者 |
| `Rc<T>` | 共享 | ❌ | 单线程共享所有权 |
| `Arc<T>` | 共享 | ✅ | 多线程共享所有权 |

```rust
// Box: 唯一所有权
let b = Box::new(5);

// Rc: 单线程共享
use std::rc::Rc;
let rc = Rc::new(5);
let rc2 = Rc::clone(&rc);  // 引用计数+1

// Arc: 多线程共享
use std::sync::Arc;
let arc = Arc::new(5);
let arc2 = Arc::clone(&arc);
```

---

### Q11: 为什么String不能Copy？

**A**: `String`包含堆分配的缓冲区，复制需要深拷贝（昂贵）。Rust默认只给"廉价复制"的类型实现Copy。

实现Copy的条件：

- 只包含标量值
- 或者包含其他Copy类型

```rust
// Copy类型
i32, f64, bool, char, (i32, i32), [i32; 4]

// 非Copy类型
String, Vec<T>, Box<T>, Rc<T>
```

---

### Q12: `clone()`和`to_owned()`有什么区别？

**A**:

- `clone()`: 通用克隆方法
- `to_owned()`: 从借用创建拥有值

```rust
let s: &str = "hello";
let s2 = s.to_owned();  // String

let v = vec![1, 2, 3];
let v2 = v.clone();  // Vec<i32>
```

---

### Q13: 如何修复"cannot borrow as mutable"错误？

**A**: 缩小不可变借用的作用域：

```rust
// ❌ 错误
let mut x = 5;
let r1 = &x;
let r2 = &mut x;  // 错误！r1还在用
println!("{}", r1);

// ✅ 修复
let mut x = 5;
{
    let r1 = &x;
    println!("{}", r1);
}  // r1在这里结束
let r2 = &mut x;  // OK
```

---

### Q14: `mem::swap`和`mem::replace`有什么用？

**A**:

- `swap`: 交换两个可变引用指向的值
- `replace`: 替换值并返回旧值

```rust
use std::mem;

let mut x = 5;
let mut y = 10;
mem::swap(&mut x, &mut y);
assert_eq!(x, 10);
assert_eq!(y, 5);

let mut s = String::from("hello");
let old = mem::replace(&mut s, String::from("world"));
assert_eq!(old, "hello");
assert_eq!(s, "world");
```

---

### Q15: 什么是"零成本抽象"？

**A**: 抽象不带来运行时开销。所有权检查在编译时完成，运行时无额外成本。

对比：

- GC语言：运行时有垃圾回收开销
- Rust：编译时检查，运行时直接内存操作

---

## 二、类型系统 (10问)

### Q16: 什么是类型安全？

**A**: 良类型的程序不会陷入未定义行为。Rust的类型系统保证：

- 不会访问无效内存
- 不会类型混淆
- 不会悬垂引用

**形式化**: Γ ⊢ e : τ → ~stuck(e)

---

### Q17: `Sized` trait是什么？

**A**: 标记编译时已知大小的类型。

```rust
// 自动实现Sized的类型
i32, f64, [i32; 5], String

// 非Sized类型（DST）
str, [i32], dyn Trait
```

使用：

```rust
fn foo<T: Sized>(x: T) {}  // 默认约束
fn bar<T: ?Sized>(x: &T) {}  // 允许DST
```

---

### Q18: `impl Trait`和`dyn Trait`有什么区别？

**A**:

- `impl Trait`: 静态分发，编译时确定具体类型
- `dyn Trait`: 动态分发，运行时确定（有虚表开销）

```rust
// 静态分发，无运行时开销
fn foo(x: impl Trait) {}

// 动态分发，有虚表查找
fn bar(x: &dyn Trait) {}
```

---

### Q19: 什么是型变(Variance)？

**A**: 描述复合类型如何继承组成部分的子类型关系。

```rust
// 协变: T <: U → Box<T> <: Box<U>
Box<&'static str> <: Box<&'a str>

// 逆变: T <: U → fn(U) <: fn(T)
fn(&'a str) <: fn(&'static str)

// 不变: &mut T
&mut &'static str 和 &mut &'a str 无关
```

---

### Q20: `'static`生命周期是什么意思？

**A**: 整个程序运行期间都有效。

常见`'static`类型：

- 字符串字面量：`&'static str`
- 全局常量
- 拥有所有权的类型（隐式）

```rust
let s: &'static str = "hello";  // 字面量
const X: i32 = 5;  // 'static
```

---

### Q21: 什么是关联类型(Associated Type)？

**A**: Trait中定义的占位类型，由实现者指定。

```rust
trait Iterator {
    type Item;  // 关联类型
    fn next(&mut self) -> Option<Self::Item>;
}

impl Iterator for Vec<i32> {
    type Item = i32;  // 指定为i32
    fn next(&mut self) -> Option<i32> { ... }
}
```

对比泛型参数：

- 关联类型：每个实现一个类型
- 泛型参数：可以实现多个（Vec<i32>, Vec<String>）

---

### Q22: 什么是泛型关联类型(GAT)？

**A**: 允许关联类型有泛型参数。

```rust
trait Container {
    type Item<'a>;  // GAT
    fn get(&self, index: usize) -> Option<Self::Item<'_>>;
}
```

使用场景：

- 返回借用的迭代器
- 类型族定义

---

### Q23: `const fn`和`fn`有什么区别？

**A**: `const fn`可以在编译时执行。

```rust
const fn add(a: i32, b: i32) -> i32 {
    a + b
}

const X: i32 = add(1, 2);  // 编译时常量
```

限制：

- 不能使用堆分配
- 不能使用运行时特性

---

### Q24: 什么是特化(Specialization)？

**A**: 为特定类型提供泛型的特殊实现。

```rust
// 通用实现
trait Trait {
    fn method(&self);
}

impl<T> Trait for T {
    default fn method(&self) { ... }
}

// 特定类型的特化
impl Trait for i32 {
    fn method(&self) { ... }  // 专门优化
}
```

**注意**: 目前不稳定，需要`#![feature(specialization)]`

---

### Q25: 什么是空指针优化(Null Pointer Optimization)？

**A**: `Option<&T>`和`&T`大小相同，用0表示`None`。

```rust
use std::mem::size_of;

assert_eq!(size_of::<Option<&i32>>(), size_of::<&i32>());
// 两者都是8字节（64位系统）
```

好处：

- `Option<&T>`无额外开销
- 类似C的nullable指针但类型安全

---

## 三、生命周期 (10问)

### Q26: 生命周期省略规则是什么？

**A**: 编译器自动推断生命周期的三条规则：

1. 每个引用参数有自己的生命周期
2. 只有一个输入生命周期 → 赋给输出
3. `&self`存在 → `self`的生命周期赋给输出

```rust
// 省略前
fn foo<'a>(x: &'a str) -> &'a str { x }

// 省略后
fn foo(x: &str) -> &str { x }  // 规则2
```

---

### Q27: 生命周期约束如何写？

**A**: `'a: 'b`表示`'a`至少和`'b`一样长。

```rust
// T中所有引用至少存活'a
struct Container<'a, T: 'a> {
    data: &'a T,
}

// 多重约束
fn longest<'a, 'b>(x: &'a str, y: &'b str) -> &'a str
where
    'a: 'b,  // 'a 至少和 'b 一样长
{
    x
}
```

---

### Q28: 什么是生命周期子类型？

**A**: `'static`是`'a`的子类型（`'static <: 'a`），因为`'static`更长。

```rust
let s: &'static str = "hello";
take_str(s);  // 可以传给需要&'a str的函数

fn take_str<'a>(s: &'a str) {}
```

协变：可以用长生命周期代替短生命周期。

---

### Q29: 为什么需要显式生命周期标注？

**A**: 当编译器无法确定返回引用与哪个参数关联时。

```rust
// ❌ 编译错误 - 不知道返回的引用来自x还是y
fn longest(x: &str, y: &str) -> &str {
    if x.len() > y.len() { x } else { y }
}

// ✅ 正确 - 显式标注
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}
```

---

### Q30: `for<'a>`语法是什么？

**A**: 高阶 trait bound (HRTB)，表示"对于所有生命周期"。

```rust
// 接受任何生命周期的闭包
fn foo<F>(f: F)
where
    F: for<'a> Fn(&'a str) -> &'a str,
{
    f("hello");
}
```

使用场景：

- 回调函数
- 泛型约束

---

### Q31: 结构体中的生命周期如何工作？

**A**: 结构体存活期间，其引用字段指向的数据必须有效。

```rust
struct Person<'a> {
    name: &'a str,  // name必须活得比Person长
}

fn main() {
    let name = String::from("Alice");
    let p = Person { name: &name };
    // name在这里不能drop
    println!("{}", p.name);
} // name和p同时结束，OK
```

---

### Q32: 自引用结构如何处理？

**A**: 使用`Pin`保证结构不会被移动。

```rust
use std::pin::Pin;

struct SelfReferential {
    data: String,
    ptr_to_data: *const String,  // 指向data
}

// 使用Pin防止移动
let mut pinned = Pin::new(Box::new(SelfReferential {
    data: String::from("hello"),
    ptr_to_data: std::ptr::null(),
}));
```

---

### Q33: 异步函数中的生命周期

**A**: async函数返回的Future捕获所有参数的生命周期。

```rust
async fn foo(x: &str) {  // 等价于 fn foo<'a>(x: &'a str) -> impl Future<Output = ()> + 'a
    println!("{}", x);
}

fn main() {
    let s = String::from("hello");
    let fut = foo(&s);  // Future<'a>
    // s必须活到Future执行完成
}
```

---

### Q34: 什么是`PhantomData`？

**A**: 零大小类型，用于告诉编译器你"使用"了某个类型，影响生命周期。

```rust
use std::marker::PhantomData;

struct Slice<'a, T: 'a> {
    ptr: *const T,
    len: usize,
    _marker: PhantomData<&'a T>,  // 告诉编译器我们拥有&'a T
}
```

---

### Q35: 生命周期和泛型如何结合？

**A**:

```rust
struct Container<'a, T>
where
    T: 'a,  // T中所有引用至少存活'a
{
    data: &'a T,
}
```

约束：

- `T: 'a`表示T不包含比`'a`短的引用

---

## 四、并发与异步 (10问)

### Q36: Send和Sync有什么区别？

**A**:

- **Send**: 可以跨线程转移所有权
- **Sync**: 可以跨线程共享（通过`&T`）

**等价定义**: `T: Sync ⇔ &T: Send`

```rust
// Rc既不是Send也不是Sync
use std::rc::Rc;
let data: Rc<i32> = Rc::new(5);
// thread::spawn(move || { *data });  // 错误！

// Arc是Send+Sync（如果T:Sync）
use std::sync::Arc;
let data: Arc<i32> = Arc::new(5);
thread::spawn(move || { println!("{}", data); });  // OK
```

---

### Q37: 为什么`Cell`不是Sync？

**A**: `Cell`提供内部可变性但没有同步机制，多线程同时修改会导致数据竞争。

```rust
use std::cell::Cell;
let cell = Cell::new(0);
// thread::spawn(|| cell.set(1));  // 错误！Cell不是Send也不是Sync
```

使用`Mutex`或`RwLock`进行线程安全的内部可变性。

---

### Q38: `Mutex`和`RwLock`怎么选？

**A**:

| 场景 | 推荐 | 理由 |
| :--- | :--- | :--- |
| 读多写少 | `RwLock` | 并发读 |
| 读写均衡 | `Mutex` | 简单高效 |
| 写多读少 | `Mutex` | 避免写者饥饿 |
| 需要升级锁 | `RwLock` | 读锁升级写锁 |

---

### Q39: 什么是死锁？如何避免？

**A**: 死锁是两个线程互相等待对方释放锁。

避免策略：

1. 锁顺序一致
2. 使用`try_lock`
3. 避免嵌套锁
4. 使用作用域锁

```rust
// 良好实践：使用作用域
{
    let guard = mutex.lock().unwrap();
    // 使用数据
}  // 自动释放
```

---

### Q40: async/await原理是什么？

**A**: 编译器将async函数转换为状态机。

```rust
async fn foo() {
    println!("A");
    bar().await;  // 挂起点
    println!("B");
}

// 大致转换为：
enum FooFuture {
    Start,
    WaitingBar,
    Done,
}
```

执行器轮询Future，在`.await`处可能让出线程。

---

### Q41: `Pin`是什么？为什么需要？

**A**: `Pin`保证值不会被移动，用于自引用结构。

```rust
use std::pin::Pin;

async fn self_referential() {
    let s = String::from("hello");
    let ptr = &s as *const _;  // 指向s
    // 如果s被移动，ptr就悬垂了
    some_async().await;  // 可能被移动！

    // Pin防止移动
}
```

---

### Q42: `tokio::spawn`和`thread::spawn`区别？

**A**:

- `thread::spawn`: 创建OS线程，成本高
- `tokio::spawn`: 创建任务，调度到线程池

```rust
// OS线程
thread::spawn(|| {
    // 独立线程执行
});

// 异步任务
tokio::spawn(async {
    // 在tokio运行时调度
});
```

数量：

- OS线程：几百个
- 异步任务：数百万个

---

### Q43: 什么是`Unpin`？

**A**: 标记可以安全移动的类型。大多数类型都是`Unpin`。

```rust
// 自动Unpin
i32, String, Vec<T>

// 非Unpin（自引用）
async fn, Pin<&mut T>
```

---

### Q44: `select!`宏是什么？

**A**: 等待多个Future，哪个先完成就执行哪个。

```rust
tokio::select! {
    result = task1 => println!("task1 done: {:?}", result),
    result = task2 => println!("task2 done: {:?}", result),
    _ = timeout => println!("timeout!"),
}
```

---

### Q45: 如何避免跨await持锁？

**A**: `.await`前释放锁：

```rust
// ❌ 危险
let guard = mutex.lock().unwrap();
some_async().await;  // 可能死锁

// ✅ 安全
{
    let guard = mutex.lock().unwrap();
    // 使用guard
}  // 释放锁
some_async().await;  // OK

// 或使用tokio::sync::Mutex
let guard = tokio_mutex.lock().await;
```

---

## 五、形式化方法 (10问)

### Q46: 什么是L1/L2/L3证明？

**A**:

- **L1**: 证明思路（给人看的）
- **L2**: 完整数学证明（详细推导）
- **L3**: 机器证明（Coq/Lean可验证）

本项目重点是L1和L2。

---

### Q47: T-OW2定理是什么？

**A**: **所有权唯一性定理** - 每个值在任意时刻只有一个所有者。

**直觉**: 防止双重释放。

---

### Q48: T-BR1定理是什么？

**A**: **数据竞争自由定理** - 借用检查通过 ⇒ 无数据竞争。

**直觉**: 编译时保证并发安全。

---

### Q49: 形式化方法对普通开发者有什么用？

**A**:

1. 理解为什么Rust安全
2. 更好地设计系统
3. 避免常见错误
4. 技术决策依据

不需要写Coq证明，理解概念即可。

---

### Q50: 如何学习形式化方法？

**A**: 学习路径：

1. 初学者：概念百科 + 反例集
2. 进阶者：定理汇编 + 证明思路
3. 专家：Coq + Iris + 论文

---

## 六、分布式与工作流 (5问)

### Q51: Saga模式解决什么问题？

**A**: 长事务问题。将大事务分解为多个小事务，每个有补偿操作。

```rust
// 编排式
let saga = Saga::new()
    .step(reserve_inventory, compensate_inventory)
    .step(process_payment, refund_payment)
    .step(create_shipment, cancel_shipment);
```

---

### Q52: CQRS适合什么场景？

**A**: 读多写少、复杂查询、需要事件溯源。

---

### Q53: 熔断器模式如何工作？

**A**:

- Closed: 正常
- Open: 错误率过高，快速失败
- Half-Open: 试探恢复

---

### Q54: 如何选择工作流引擎？

**A**:

- 需要持久化 → Temporal/Cadence
- 简单流程 → 自研状态机
- 人工任务 → Camunda

---

### Q55: 什么是补偿事务？

**A**: 分布式系统中，通过执行补偿操作撤销已完成操作，达到最终一致性。

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-24
**状态**: ✅ 已完成 - FAQ汇总 (55问)
