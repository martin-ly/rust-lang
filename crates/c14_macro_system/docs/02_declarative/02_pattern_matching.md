# 模式匹配

> **文档定位**: 声明宏中的模式匹配技巧和高级用法  
> **难度级别**: ⭐⭐ 进阶  
> **预计时间**: 3小时  
> **最后更新**: 2025-10-20

---

## 📋 学习目标

完成本章后，你将能够：

- ✅ 掌握宏模式匹配的语法和规则
- ✅ 理解不同片段指定符的使用场景
- ✅ 实现复杂的模式匹配逻辑
- ✅ 处理模式匹配的边界情况
- ✅ 优化宏的性能和可读性

---

## 1. 模式匹配基础

### 1.1 什么是模式匹配？

**模式匹配**是宏根据输入选择不同展开规则的过程：

```rust
macro_rules! calc {
    // 模式1: 加法
    (add $a:expr, $b:expr) => {
        $a + $b
    };
    // 模式2: 减法
    (sub $a:expr, $b:expr) => {
        $a - $b
    };
    // 模式3: 乘法
    (mul $a:expr, $b:expr) => {
        $a * $b
    };
}

let result1 = calc!(add 5, 3);  // 8
let result2 = calc!(sub 10, 4); // 6
let result3 = calc!(mul 2, 7);  // 14
```

### 1.2 匹配规则

宏按**从上到下**的顺序尝试匹配：

```rust
macro_rules! test_order {
    ($x:expr) => { println!("Expression: {}", $x); };
    (special) => { println!("Special case!"); };  // ❌ 永远不会匹配
}

test_order!(special);  // 输出: Expression: special
```

**正确顺序**（具体到通用）：

```rust
macro_rules! test_order {
    (special) => { println!("Special case!"); };  // ✅ 先匹配特殊情况
    ($x:expr) => { println!("Expression: {}", $x); };
}

test_order!(special);  // 输出: Special case!
test_order!(42);       // 输出: Expression: 42
```

---

## 2. 片段指定符详解

### 2.1 完整指定符列表

| 指定符 | 匹配内容 | 示例 |
|--------|---------|------|
| `expr` | 表达式 | `1 + 2`, `foo()` |
| `ident` | 标识符 | `foo`, `bar` |
| `ty` | 类型 | `i32`, `Vec<T>` |
| `pat` | 模式 | `Some(x)`, `Point { x, y }` |
| `stmt` | 语句 | `let x = 1;` |
| `block` | 代码块 | `{ ... }` |
| `item` | 项 | `fn foo() {}`, `struct Bar;` |
| `path` | 路径 | `std::vec::Vec` |
| `tt` | Token树 | 任意token |
| `meta` | 属性内容 | `derive(Debug)` |
| `lifetime` | 生命周期 | `'a` |
| `vis` | 可见性 | `pub` |
| `literal` | 字面量 | `42`, `"text"` |

### 2.2 常用指定符实践

#### expr - 表达式

```rust
macro_rules! debug_expr {
    ($e:expr) => {
        println!("{} = {:?}", stringify!($e), $e);
    };
}

debug_expr!(1 + 2 * 3);        // 输出: 1 + 2 * 3 = 7
debug_expr!(vec![1, 2, 3]);    // 输出: vec![1, 2, 3] = [1, 2, 3]
debug_expr!(some_function());  // 输出: some_function() = <result>
```

#### ident - 标识符

```rust
macro_rules! create_variable {
    ($name:ident, $value:expr) => {
        let $name = $value;
    };
}

create_variable!(my_var, 42);
println!("{}", my_var);  // 输出: 42
```

#### ty - 类型

```rust
macro_rules! create_vector {
    ($ty:ty, $($val:expr),*) => {
        {
            let mut v: Vec<$ty> = Vec::new();
            $(v.push($val);)*
            v
        }
    };
}

let int_vec = create_vector!(i32, 1, 2, 3);
let str_vec = create_vector!(&str, "a", "b", "c");
```

#### pat - 模式

```rust
macro_rules! match_pattern {
    ($value:expr, $pat:pat => $result:expr) => {
        match $value {
            $pat => $result,
            _ => panic!("Pattern did not match"),
        }
    };
}

let result = match_pattern!(Some(42), Some(x) => x * 2);
println!("{}", result);  // 输出: 84
```

---

## 3. 复杂模式匹配

### 3.1 多参数模式

```rust
macro_rules! create_struct {
    // 无字段结构体
    ($name:ident) => {
        struct $name;
    };
    // 单个字段
    ($name:ident { $field:ident: $ty:ty }) => {
        struct $name {
            $field: $ty,
        }
    };
    // 多个字段
    ($name:ident { $($field:ident: $ty:ty),+ }) => {
        struct $name {
            $($field: $ty),+
        }
    };
}

create_struct!(Empty);
create_struct!(Point { x: i32 });
create_struct!(Person {
    name: String,
    age: u32,
    email: String,
});
```

### 3.2 条件模式

```rust
macro_rules! conditional_impl {
    // 为实现了Clone的类型实现
    ($t:ty where Clone) => {
        impl Clone for $t {
            fn clone(&self) -> Self {
                // 假设类型实现了Clone
                self.clone()
            }
        }
    };
    // 为其他类型实现
    ($t:ty) => {
        impl Default for $t {
            fn default() -> Self {
                // 默认实现
                unsafe { std::mem::zeroed() }
            }
        }
    };
}
```

### 3.3 嵌套模式

```rust
macro_rules! nested_match {
    // 匹配函数定义
    (fn $name:ident($($param:ident: $ty:ty),*) -> $ret:ty $body:block) => {
        fn $name($($param: $ty),*) -> $ret $body
    };
    // 匹配结构体定义
    (struct $name:ident { $($field:ident: $ty:ty),* }) => {
        struct $name {
            $($field: $ty),*
        }
    };
}

nested_match! {
    fn add(a: i32, b: i32) -> i32 {
        a + b
    }
}

nested_match! {
    struct Point {
        x: f64,
        y: f64,
    }
}
```

---

## 4. 高级模式技巧

### 4.1 使用tt进行灵活匹配

`tt`（Token Tree）是最灵活的指定符：

```rust
macro_rules! flexible_macro {
    // 匹配任意token序列
    ($($tokens:tt)*) => {
        // 处理任意输入
        println!("Received: {}", stringify!($($tokens)*));
    };
}

flexible_macro!(1 + 2 * 3);
flexible_macro!(if true { "yes" } else { "no" });
flexible_macro!(struct MyStruct { field: i32 });
```

### 4.2 模式守卫

虽然Rust宏没有模式守卫，但可以通过多个规则模拟：

```rust
macro_rules! guarded_match {
    // 匹配数字字面量
    ($n:literal) => {
        if $n > 0 {
            println!("Positive: {}", $n);
        } else {
            println!("Non-positive: {}", $n);
        }
    };
    // 匹配其他表达式
    ($e:expr) => {
        println!("Expression: {}", $e);
    };
}

guarded_match!(5);      // 输出: Positive: 5
guarded_match!(-3);     // 输出: Non-positive: -3
guarded_match!(1 + 2);  // 输出: Expression: 3
```

### 4.3 模式组合

```rust
macro_rules! complex_pattern {
    // 匹配函数调用
    ($func:ident!($($arg:expr),*)) => {
        $func!($($arg),*)
    };
    // 匹配方法调用
    ($obj:expr.$method:ident($($arg:expr),*)) => {
        $obj.$method($($arg),*)
    };
    // 匹配字段访问
    ($obj:expr.$field:ident) => {
        $obj.$field
    };
}

// 使用示例
let result = complex_pattern!(println!("Hello"));
let len = complex_pattern!("hello".len());
let first = complex_pattern!(vec![1, 2, 3].first());
```

---

## 5. 错误处理模式

### 5.1 编译时错误

```rust
macro_rules! validate_type {
    ($x:expr, i32) => { $x };
    ($x:expr, $t:ty) => {
        compile_error!(concat!(
            "Expected i32, got ",
            stringify!($t)
        ));
    };
}

let valid = validate_type!(42, i32);  // ✅
// let invalid = validate_type!("text", i32);  // ❌ 编译错误
```

### 5.2 运行时错误

```rust
macro_rules! safe_divide {
    ($a:expr, $b:expr) => {
        if $b == 0 {
            panic!("Division by zero!");
        } else {
            $a / $b
        }
    };
}

let result = safe_divide!(10, 2);  // 5
// let error = safe_divide!(10, 0);  // panic!
```

### 5.3 优雅降级

```rust
macro_rules! optional_feature {
    // 如果支持某个特性
    (feature $name:ident => $code:block) => {
        #[cfg(feature = stringify!($name))]
        $code
        
        #[cfg(not(feature = stringify!($name)))]
        {
            // 降级实现
            println!("Feature {} not available", stringify!($name));
        }
    };
}

optional_feature!(feature advanced => {
    println!("Using advanced features");
});
```

---

## 6. 性能优化模式

### 6.1 避免重复计算

```rust
macro_rules! cached_calc {
    ($e:expr) => {{
        static mut CACHE: Option<i32> = None;
        static mut LAST_EXPR: &'static str = "";
        let expr_str = stringify!($e);
        
        unsafe {
            if LAST_EXPR == expr_str {
                CACHE.unwrap()
            } else {
                let result = $e;
                CACHE = Some(result);
                LAST_EXPR = expr_str;
                result
            }
        }
    }};
}
```

### 6.2 条件编译优化

```rust
macro_rules! optimized_print {
    ($($arg:expr),*) => {
        #[cfg(debug_assertions)]
        {
            $(println!("{:?}", $arg);)*
        }
        
        #[cfg(not(debug_assertions))]
        {
            // Release模式下的优化实现
        }
    };
}
```

---

## 7. 实际应用案例

### 7.1 配置宏

```rust
macro_rules! config {
    // 字符串配置
    ($name:ident = $value:expr) => {
        pub const $name: &str = $value;
    };
    // 数字配置
    ($name:ident = $value:expr, $ty:ty) => {
        pub const $name: $ty = $value;
    };
    // 布尔配置
    ($name:ident = true) => {
        pub const $name: bool = true;
    };
    ($name:ident = false) => {
        pub const $name: bool = false;
    };
}

config!(APP_NAME = "MyApp");
config!(MAX_CONNECTIONS = 100, usize);
config!(DEBUG_MODE = true);
```

### 7.2 测试宏

```rust
macro_rules! test_cases {
    // 单个测试
    ($name:ident: $input:expr => $expected:expr) => {
        #[test]
        fn $name() {
            assert_eq!($input, $expected);
        }
    };
    // 多个测试
    ($($name:ident: $input:expr => $expected:expr;)*) => {
        $(
            test_cases!($name: $input => $expected);
        )*
    };
}

test_cases! {
    test_add: 1 + 1 => 2;
    test_sub: 5 - 3 => 2;
    test_mul: 2 * 3 => 6;
}
```

### 7.3 序列化宏

```rust
macro_rules! serialize {
    // 基本类型
    ($value:expr, $ty:ty) => {
        serde_json::to_string(&$value as &$ty).unwrap()
    };
    // 结构体
    ($struct:ident { $($field:ident: $value:expr),* }) => {
        {
            let obj = $struct {
                $($field: $value),*
            };
            serde_json::to_string(&obj).unwrap()
        }
    };
}
```

---

## 8. 调试技巧

### 8.1 模式调试

```rust
macro_rules! debug_pattern {
    ($($tokens:tt)*) => {
        compile_error!(concat!(
            "Pattern debug: ",
            stringify!($($tokens)*)
        ));
    };
}

// 取消注释来调试模式
// debug_pattern!(add 1, 2);
```

### 8.2 展开调试

```rust
macro_rules! trace_expansion {
    ($($tokens:tt)*) => {
        {
            println!("Expanding: {}", stringify!($($tokens)*));
            $($tokens)*
        }
    };
}
```

---

## 9. 最佳实践

### ✅ 推荐做法

1. **具体优先** - 将具体模式放在通用模式之前
2. **清晰命名** - 使用描述性的变量名
3. **文档注释** - 为复杂模式添加说明
4. **错误处理** - 提供清晰的错误信息
5. **测试覆盖** - 为所有模式编写测试

### ❌ 避免做法

1. **过度复杂** - 避免过于复杂的嵌套模式
2. **模糊匹配** - 避免使用过于宽泛的`tt`模式
3. **性能陷阱** - 注意宏展开的性能影响
4. **维护困难** - 避免难以理解和维护的模式

---

## 10. 实践练习

### 练习1: 计算器宏

**任务**: 创建一个支持多种运算的计算器宏。

```rust
macro_rules! calculator {
    // 实现加法、减法、乘法、除法
    // 支持链式运算
}

// 测试
let result = calculator!(add 5, 3);
let result = calculator!(mul 2, add 1, 2);
```

### 练习2: 日志宏

**任务**: 创建支持不同日志级别的宏。

```rust
macro_rules! log {
    // 支持 info, warn, error 级别
    // 支持格式化字符串
}

// 测试
log!(info "User {} logged in", username);
log!(warn "Memory usage high: {}%", usage);
log!(error "Database connection failed");
```

### 练习3: 验证宏

**任务**: 创建数据验证宏。

```rust
macro_rules! validate {
    // 支持范围检查、类型检查、非空检查
}

// 测试
validate!(age: 25 in 18..65);
validate!(email: "user@example.com" is email);
validate!(name: "John" is not_empty);
```

---

## 📚 总结

### 关键要点

1. **模式顺序很重要** - 具体模式优先于通用模式
2. **片段指定符选择** - 选择合适的指定符提高精确性
3. **错误处理** - 提供清晰的编译时和运行时错误
4. **性能考虑** - 避免不必要的重复计算
5. **调试技巧** - 使用工具和技巧调试复杂模式

### 下一步

- 📖 学习 [重复语法](./03_repetition_syntax.md)
- 📖 实践 [高级模式](./04_advanced_patterns.md)
- 💻 运行: `cargo run --example 02_pattern_matching`

---

**作者**: Rust学习社区  
**最后更新**: 2025-10-20  
**许可**: MIT
