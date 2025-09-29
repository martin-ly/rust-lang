# 借用与解借用

下面介绍下 Rust 中关于借用（&T 和 &mut T）以及所谓“接借用”（即先解借用再取借用，如 `&*r`）的定义、等价形式和它们之间的等价关系。

## 1. 借用与借用的基本概念

在 Rust 中，**借用**本质上就是对某个值的借用。

- **不可变借用**：类型为 `&T`，借用后只能对共享数据进行只读访问。
- **可变借用**：类型为 `&mut T`，在借用期间允许通过该借用修改数据，但同时要求在同一作用域内不能存在其他借用。

当你写出表达式 `&x` 时，实际上就是对 `x` 的一次借用操作。
借用和借用在 Rust 的语义中是同一概念，都是在不取得所有权的前提下对数据进行访问。

## 2. 解借用与接借用的等价形式

在 Rust 中，**解借用**操作符 `*` 用于从借用中取出其指向值；而**取借用**操作符 `&` 则是获取某个值的地址。
当对一个借用先做解借用再取借用时，实际上起到了“取消”解借用的作用，即：

```text
r \equiv &*r
```

同样，对于可变借用也成立：

```text
r \equiv &mut *r
```

### 原理说明

给定一个借用 `r`（例如 `r: &T`），则执行下面这步：

- `*r` 会解借用，结果得到类型 `T` 的值（注意：这里只是“访问”，并不发生所有权转移）
- 对 `*r` 再取地址，即 `&*r`，则会生成一个新的借用，其类型还是 `&T`，且指向的地址与原借用 `r` 所指相同。

因此，**对一个借用先解借用再取借用，结果与原借用是等价的**。
这就是 Rust 中“接借用”的等价形式。
在编译器的自动解借用（auto-deref）和重新借用（reborrowing）机制下，这种等价关系经常在代码中隐式发挥作用。

## 3. 代码示例

下面给出两个简单的例子说明不可变借用和可变借用的等价形式。

### 不可变借用示例

```rust
fn main() {
    let x = 42;
    let r: &i32 = &x;
    // &*r 与 r 等价
    let r2: &i32 = &*r;
    assert_eq!(r, r2);
}
```

在上面的例子中，`r` 是一个 `&i32` 类型的借用，`&*r` 先解借用后取借用，仍然是一个指向 `x` 的 `&i32` 类型借用，与 `r` 完全等价。

### 可变借用示例

```rust
fn main() {
    let mut x = 42;
    let r: &mut i32 = &mut x;
    // &mut *r 与 r 等价
    let r2: &mut i32 = &mut *r;
    *r2 += 1;
    assert_eq!(x, 43);
}
```

这里，`r` 是一个可变借用，通过 `&mut *r` 得到的 `r2` 与 `r` 等价，同样指向变量 `x`。

## 4. 自动解借用与重新借用

Rust 编译器在方法调用等场景中会自动进行解借用（auto-deref）和重新借用（reborrowing）：  

- **自动解借用**：当方法调用时，编译器会自动沿着实现了 `Deref` trait 的类型进行多次解借用，使得调用链更简洁。
  
- **重新借用**：当传递借用给函数时，若函数参数类型的生命周期比原借用短，
编译器会自动创建一个局部的借用借用，这个过程可以看作是 `&*r` 或 `&mut *r` 的隐式应用。

例如：

```rust
fn print_str(s: &str) {
    println!("{}", s);
}

fn main() {
    let s = String::from("hello");
    // s.as_str() 返回的是 &str，而这里编译器也允许将 &String 自动转换为 &str，其中也涉及了自动解借用
    print_str(&s);
}
```

## 5. 等价关系总结

- 对于任意不可变借用 `r: &T`，都有：  
  **`r ≡ &*r`**

- 对于任意可变借用 `r: &mut T`，也有：  
  **`r ≡ &mut *r`**

这些等价关系体现了**取地址**和**解借用**操作互为逆操作的性质。
同时，根据 Rust 的借用检查规则，只要多个借用满足借用规则（例如不可变借用可以共存，可变借用则要求独占），
它们在内存上的指向是一致的，均可安全地访问同一数据。

## 小结

- **借用**（&T 和 &mut T）表示对值**借用**。
- 对借用执行 `*` （解借用），再对结果取地址 `&`（接借用），得到的结果与原来的借用完全等价。  
- 这种等价形式不仅使得手写代码时可以灵活转换，也为 Rust 自动解借用和重新借用机制提供了理论基础，从而大大简化了代码的书写和阅读。

通过理解这些等价关系，我们可以更清晰地看到 Rust 在处理借用和借用时背后的设计哲学，从而写出更安全、简洁的代码。

## RUST多级借用

在 Rust 中，解借用操作符 `*` 用于从借用中取得其指向的值。当存在嵌套借用时（比如 `&&T` 或者 `Box<Box<T>>`），
我们需要多次使用 `*` 运算符来逐层获取内部的值，这种写法可以等价地写成一次连续书写的 `**p`，其实内部的含义就是 `*(*p)`。
例如，考虑下面这个简单例子：

```rust
fn main() {
    let x = 123;
    let rx = &x;    // rx 的类型为 &i32
    let rrx = &&x;  // rrx 的类型为 &&i32

    // **rrx 等价于 *(*rrx)，即先解借用一次得到 &i32，再解借用得到 i32
    assert_eq!(x, **rrx);
}
```

在上面的代码中：

- `*rrx` 得到的是一个 `&i32`；
- 对 `*rrx` 再使用 `*`，即 `*(*rrx)`，得到的就是原始的 `i32` 值 `x`。

对于智能指针来说，Rust 通过实现 `Deref` trait 提供了类似的解借用方式。
例如，对 `Box<T>`、`Rc<T>` 或自定义的智能指针类型，当这些类型实现了 `Deref` 后，我们可以使用自动解借用机制。
下面是一个自定义智能指针的示例：

```rust
use std::ops::Deref;

struct MyBox<T>(T);

impl<T> Deref for MyBox<T> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.0
    }
}

fn main() {
    let x = 10;
    let boxed = MyBox(MyBox(x));
    
    // boxed 的类型为 MyBox<MyBox<i32>>
    // *boxed 得到 MyBox<i32>，对其再解借用 **boxed 则得到 i32，即 x 的值
    assert_eq!(x, **boxed);
}
```

在这个例子中：

- `*boxed` 调用了 `MyBox<T>` 上的 `deref` 方法，结果是 `MyBox<i32>`；
- 对此再使用 `*`，即 `**boxed`，就得到了最内层的 `i32` 值。

总的来说，在 Rust 中：

- 嵌套的解借用操作 `**p` 就等价于 `*(*p)`；
- 编译器在需要时会自动沿用 `Deref` trait 对智能指针进行多次解借用（auto-deref），使得我们在调用方法或其他运算时无需手动写出所有的 `*` 操作。

这种多层解借用的等价化简让代码在面对复杂嵌套借用时依然可以保持清晰和简洁。

## Rust 的多级借用有哪些常见错误

以下是一些常见的错误及其解决方案：

### **1. 解借用层数不匹配**

当尝试解借用多级借用时，如果解借用的层数不正确，Rust 编译器会报错。例如：

```rust
fn main() {
    let a = 10;
    let b = &a;        // 一级借用
    let c = &b;        // 二级借用

    let value = *c;    // 错误：只解借用了一次
}
```

**错误信息**：

```text
error[E0614]: type `&&i32` cannot be dereferenced
 --> src/main.rs:6:15
  |
6 |     let value = *c;
  |               ^^
```

**解决方案**：确保解借用的层数与借用的层数匹配。在这个例子中，需要两次解借用：

```rust
fn main() {
    let a = 10;
    let b = &a;        // 一级借用
    let c = &b;        // 二级借用

    let value = **c;   // 正确：解借用两次
    println!("{}", value);
}
```

### **2. 生命周期不匹配**

多级借用的生命周期必须匹配，否则会导致编译错误。例如：

```rust
fn process_data<'a>(data: &'a str) {
    let ref_to_data = data; // 这里 data 的生命周期与 ref_to_data 不匹配
    // ...
}
```

**错误信息**：

```text
error[E0495]: cannot infer an appropriate lifetime for borrow expression due to conflicting requirements
 --> src/main.rs:2:21
  |
2 |     let ref_to_data = data;
  |                     ^^^^^^
```

**解决方案**：使用相同的生命周期注解来确保借用的生命周期一致：

```rust
fn process_data<'a>(data: &'a str) {
    let ref_to_data: &'a str = data; // 使用相同的生命周期注解
    // ...
}
```

### **3. 可变借用与不可变借用冲突**

在同一作用域内，不能同时存在可变借用和不可变借用。例如：

```rust
fn main() {
    let mut s = String::from("hello");

    let r1 = &s;        // 不可变借用
    let r2 = &mut s;    // 可变借用
    println!("{}", r1);
}
```

**错误信息**：

```text
error[E0502]: cannot borrow `s` as mutable because it is also borrowed as immutable
 --> src/main.rs:5:14
  |
4 |     let r1 = &s;        // 不可变借用
  |              -- immutable borrow occurs here
5 |     let r2 = &mut s;    // 可变借用
  |              ^^^^^^ mutable borrow occurs here
6 |     println!("{}", r1);
  |                    -- immutable borrow later used here
```

**解决方案**：确保在同一作用域内不同时存在可变借用和不可变借用：

```rust
fn main() {
    let mut s = String::from("hello");

    let r1 = &s;        // 不可变借用
    println!("{}", r1);

    let r2 = &mut s;    // 可变借用
    println!("{}", r2);
}
```

### **4. 多级借用的错误使用**

在某些复杂场景中，多级借用可能会导致难以理解的错误。例如：

```rust
fn main() {
    let mut a = 10;
    let b = &mut a;       // 一级可变借用
    let c = &b;           // 二级借用
    let d = &c;           // 三级借用

    *d = 20;              // 错误：只解借用了一次
}
```

**错误信息**：

```text
error[E0614]: type `&&&i32` cannot be dereferenced
 --> src/main.rs:9:5
  |
9 |     *d = 20;
  |     ^^
```

**解决方案**：确保解借用的层数与借用的层数匹配。在这个例子中，需要三次解借用：

```rust
fn main() {
    let mut a = 10;
    let b = &mut a;       // 一级可变借用
    let c = &b;           // 二级借用
    let d = &c;           // 三级借用

    ***d = 20;            // 正确：解借用三次
    println!("{}", a);    // 输出 20
}
```

### **5. 生命周期结束前的错误借用**

借用的作用域从声明的地方开始，一直持续到最后一次使用为止。
如果在借用的作用域结束前尝试使用它，可能会导致编译错误。例如：

```rust
fn main() {
    let mut s = String::from("hello");

    let r1 = &s;        // 不可变借用
    let r2 = &mut s;    // 可变借用
    println!("{}", r1); // 错误：r1 的作用域尚未结束
}
```

**错误信息**：

```text
error[E0502]: cannot borrow `s` as mutable because it is also borrowed as immutable
 --> src/main.rs:5:14
  |
4 |     let r1 = &s;        // 不可变借用
  |              -- immutable borrow occurs here
5 |     let r2 = &mut s;    // 可变借用
  |              ^^^^^^ mutable borrow occurs here
6 |     println!("{}", r1); // immutable borrow later used here
```

**解决方案**：确保借用的作用域不重叠：

```rust
fn main() {
    let mut s = String::from("hello");

    let r1 = &s;        // 不可变借用
    println!("{}", r1); // 使用 r1

    let r2 = &mut s;    // 可变借用
    println!("{}", r2); // 使用 r2
}
```

### **总结**

Rust 的多级借用在使用时需要注意以下几点：

1. 确保解借用的层数与借用的层数匹配。
2. 确保借用的生命周期匹配，避免生命周期不匹配的错误。
3. 遵守 Rust 的借用规则，避免在同一作用域内同时存在可变借用和不可变借用。
4. 确保借用的作用域不重叠，避免在借用的作用域结束前错误地使用它。

通过这些规则，可以有效避免多级借用带来的常见错误，确保代码的安全性和正确性。
