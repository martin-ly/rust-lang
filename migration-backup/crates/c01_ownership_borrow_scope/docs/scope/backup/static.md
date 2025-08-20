# 'static 生命周期

在 Rust 中，`'static` 生命周期表示一个引用或数据的生命周期是整个程序的运行时间。
具体来说，`'static` 可以用于以下几种情况：

## 1. **静态数据**

任何在程序编译时就已知并存储在程序的二进制文件中的数据都具有 `'static` 生命周期。
例如，字符串字面量（如 `"hello"`）是 `'static` 的，因为它们在程序的整个运行期间都有效。

```rust
let s: &'static str = "hello"; // 字符串字面量具有 'static 生命周期
```

## 2. **全局变量**

使用 `static` 关键字定义的全局变量也具有 `'static` 生命周期。

```rust
static GLOBAL: i32 = 42; // 全局变量具有 'static 生命周期
```

## 3. **Trait 对象**

当你在 trait 对象中使用 `'static` 时，表示该 trait 对象的引用必须是 `'static` 的。
这意味着你不能使用引用到局部变量或非 `'static` 数据的 trait 对象。

```rust
trait MyTrait {
    fn do_something(&self);
}

fn takes_static_trait_object(obj: &'static dyn MyTrait) {
    // 这里的 obj 必须是 'static 的
}
```

## 4. **泛型参数**

在泛型中使用 `'static` 作为约束，表示该类型参数必须是 `'static` 的。
这通常用于确保某些数据在整个程序运行期间都是有效的。

```rust
fn takes_static<T: 'static>(value: T) {
    // T 必须是 'static 的
}
```

## 总结

`'static` 生命周期表示数据在程序的整个运行期间都是有效的。
它通常用于静态数据、全局变量、trait 对象和泛型约束中，以确保引用或数据的有效性。
