# 生命周期速查卡

> **一页纸速查** - 生命周期规则、省略、常见模式

---

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

```
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
**最后更新**: 2026-02-24
**状态**: ✅ 已完成 - 生命周期速查卡
