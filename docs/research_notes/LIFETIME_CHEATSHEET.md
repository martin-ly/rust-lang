# 生命周期速查卡

> **一页纸速查** - 生命周期语法、规则、常见模式

---

## 生命周期语法

```rust
// 显式标注
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str

// 多个独立生命周期
fn parse<'a, 'b>(input: &'a str, config: &'b Config) -> &'a Token

// 生命周期约束
fn process<'a, 'b>(x: &'a Data, y: &'b Data) -> &'a Data
where
    'a: 'b,  // 'a 至少和 'b 一样长
```

---

## 生命周期省略规则

编译器自动应用以下规则：

1. **每个引用参数有独立生命周期**

   ```rust
   fn foo(x: &i32, y: &i32)  // 隐式: fn foo<'a, 'b>(x: &'a i32, y: &'b i32)
   ```

2. **单一输入生命周期应用到输出**

   ```rust
   fn foo(x: &i32) -> &i32   // 隐式: fn foo<'a>(x: &'a i32) -> &'a i32
   ```

3. **`&self`的生命周期应用到输出**

   ```rust
   fn foo(&self) -> &T       // 隐式: fn foo<'a>(&'a self) -> &'a T
   fn foo(&self, x: &T) -> &T  // 规则1+3: fn foo<'a, 'b>(&'a self, x: &'b T) -> &'a T
   ```

---

## 结构体生命周期

```rust
// 持有引用需要生命周期参数
struct Parser<'a> {
    input: &'a str,
    position: usize,
}

impl<'a> Parser<'a> {
    fn new(input: &'a str) -> Self {
        Self { input, position: 0 }
    }

    fn peek(&self) -> Option<&'a str> {
        // 返回与输入相同生命周期的引用
        self.input.get(self.position..self.position+1)
    }
}
```

---

## 'static 生命周期

```rust
// 字符串字面量是'static
let s: &'static str = "I live forever";

// 与泛型结合
fn spawn_thread<F>(f: F)
where
    F: FnOnce() + 'static,  // 闭包不捕获非'static引用
{}

// 全局常量
static GLOBAL: i32 = 42;
```

---

## 高阶Trait Bound (HRTB)

```rust
// 对所有生命周期都成立
fn call_with_ref<F>(f: F)
where
    F: for<'a> Fn(&'a str),
{
    f("hello");
}

// 与闭包一起使用
let closure = |s: &str| println!("{}", s);
call_with_ref(closure);
```

---

## 常见模式

### 输入输出相同生命周期

```rust
fn identity<'a>(x: &'a str) -> &'a str {
    x
}
```

### 返回与特定输入关联

```rust
fn get_name<'a>(person: &'a Person) -> &'a str {
    &person.name
}
```

### 多个输入，返回其中一个

```rust
fn choose<'a>(first: &'a str, second: &'a str, use_first: bool) -> &'a str {
    if use_first { first } else { second }
}
```

---

## 生命周期错误与修复

| 错误 | 代码 | 修复 |
| :--- | :--- | :--- |
| 悬垂引用 | `fn bad() -> &str { let s = ""; &s }` | 返回 `String` 或 `'static` |
| 生命周期不匹配 | `let r; { let x = 5; r = &x; }` | 扩大值的作用域 |
| 借用冲突 | `&mut` 同时有 `&` | 分离使用范围 |

---

## Trait对象生命周期

```rust
// 默认'static
trait Trait {}
Box<dyn Trait>           // Box<dyn Trait + 'static>

// 显式生命周期
trait Parser<'a> {}
Box<dyn Parser<'a> + 'a>

// 省略形式
trait Read {}
&dyn Read                // &'_ dyn Read (匿名生命周期)
```

---

## 型变与生命周期

```rust
// &'a T 对 'a 协变
// &'a T <: &'b T  当 'a: 'b (a比b长)

fn example() {
    let s: &'static str = "static";
    let r: &str = s;  // OK: 'static <: any lifetime
}

// &'a mut T 对 'a 不变
// &'a mut T 对 T 不变
```

---

## 与泛型结合

```rust
// 泛型函数带生命周期
fn process<'a, T>(data: &'a [T]) -> impl Iterator<Item = &'a T> {
    data.iter()
}

// 泛型结构体
struct Wrapper<'a, T: 'a> {
    data: &'a T,
}

// Trait Bound
fn use_display<'a, T>(x: &'a T) -> &'a T
where
    T: Display + 'a,
{ x }
```

---

## 自我引用结构

```rust
// 需要Pin
use std::pin::Pin;
use std::marker::PhantomPinned;

struct SelfReferential {
    data: String,
    ptr_to_data: *const String,
    _pin: PhantomPinned,
}

impl SelfReferential {
    fn new(data: String) -> Pin<Box<Self>> {
        let mut boxed = Box::pin(Self {
            data,
            ptr_to_data: std::ptr::null(),
            _pin: PhantomPinned,
        });

        let ptr = &boxed.data as *const String;
        unsafe {
            boxed.as_mut().get_unchecked_mut().ptr_to_data = ptr;
        }

        boxed
    }
}
```

---

## 快速诊断

```
错误: "borrowed value does not live long enough"
原因: 引用的值比引用先死
解决: 扩大值作用域或改变所有权

错误: "lifetime mismatch"
原因: 输入输出生命周期不匹配
解决: 添加生命周期标注或调整返回类型

错误: "cannot return reference to local variable"
原因: 返回局部变量的引用
解决: 返回值所有权或'static
```

## 生命周期基础

### 生命周期关系

```rust
'a: 'b  // 'a 至少和 'b 一样长（'a 包含 'b）
T: 'a   // T 中所有引用至少存活 'a
```

### 常见生命周期

| 标注 | 含义 | 示例 |
| :--- | :--- | :--- |
| `'static` | 程序整个运行期间 | `&'static str` |
| `'a` | 泛型生命周期 | `&'a i32` |
| `'_` | 让编译器推断 | `&'_ i32` |

---

## 生命周期省略规则

### 三条规则

```
1. 每个引用参数有自己的生命周期
2. 只有一个输入生命周期 → 赋给所有输出
3. `&self`/`&mut self`存在 → self的生命周期赋给输出
```

### 示例

```rust
// 省略前
fn foo<'a>(x: &'a str) -> &'a str { x }

// 省略后
fn foo(x: &str) -> &str { x }  // 规则2

// 方法省略
fn method(&self, x: &str) -> &str { self.0 }
// 等价于: fn method<'a, 'b>(&'a self, x: &'b str) -> &'a str
```

---

## 常见生命周期模式

### 模式1: 输入输出相同

```rust
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}
```

### 模式2: 返回self的引用

```rust
impl<'a> Parser<'a> {
    fn input(&self) -> &'a str { self.input }
}
```

### 模式3: 独立生命周期

```rust
fn parse<'a, 'b>(input: &'a str, config: &'b Config) -> &'a str {
    // 返回与input关联的数据
}
```

---

## 生命周期约束

### HRTB (高阶trait bound)

```rust
F: for<'a> Fn(&'a str) -> &'a str
```

### 多重约束

```rust
trait Foo<'a, 'b>
where
    'a: 'b,  // 'a 至少和 'b 一样长
    T: 'a,   // T 中所有引用至少 'a
{}
```

---

## 常见错误

### 错误1: 返回局部引用

```rust
// ❌ 错误
fn bad() -> &str {
    let s = String::from("hello");
    &s  // s 在函数结束时被释放
}

// ✅ 修复
fn good() -> String {
    String::from("hello")  // 转移所有权
}
```

### 错误2: 生命周期不匹配

```rust
// ❌ 错误
fn longest(x: &str, y: &str) -> &str { ... }

// ✅ 修复
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str { ... }
```

---

## 结构体生命周期

```rust
struct Person<'a> {
    name: &'a str,  // name 必须活得比 Person 长
}

// 使用
let name = String::from("Alice");
let p = Person { name: &name };
// name 必须在这里之后才能 drop
```

---

## 生命周期与子类型

```
'static <: 'a <: 'b <: ...

长生命周期是短生命周期的子类型
```

```rust
let s: &'static str = "hello";
take_str(s);  // 可以传给需要 &'a str 的函数

fn take_str<'a>(s: &'a str) {}
```

---

## 技巧

### 技巧1: `'static`默认

```rust
// 拥有所有权的类型隐式 'static
struct OwnedData {
    data: String,  // 等价于 data: String + 'static
}
```

### 技巧2: 生命周期推断

```rust
// 大多数情况下不需要显式标注
let r = &x;  // 编译器自动推断
```

### 技巧3: 显式drop

```rust
{
    let r = &x;
    // 使用 r
    drop(r);  // 显式结束借用
}  // 或等待作用域结束
// 现在可以修改 x 了
```

---

## 快速决策

```text
需要显式生命周期？
├── 返回引用？
│   ├── 来自参数 → 标注与参数相同
│   └── 来自self → 标注self的生命周期
├── 结构体包含引用？
│   └── 需要生命周期参数
└── 泛型约束？
    └── T: 'a
```

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-28
**状态**: ✅ 已扩展 - 生命周期速查卡完整版
