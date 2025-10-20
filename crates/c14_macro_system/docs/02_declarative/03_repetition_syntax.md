# 重复语法

> **文档定位**: 声明宏中的重复模式和语法  
> **难度级别**: ⭐⭐ 进阶  
> **预计时间**: 3小时  
> **最后更新**: 2025-10-20

---

## 📋 学习目标

完成本章后，你将能够：

- ✅ 掌握重复语法的基本概念和符号
- ✅ 理解`$(...)*`、`$(...)+`、`$(...)?`的区别
- ✅ 实现复杂的重复模式
- ✅ 处理重复中的分隔符和尾随逗号
- ✅ 优化重复宏的性能

---

## 1. 重复语法基础

### 1.1 什么是重复语法？

**重复语法**允许宏处理可变数量的参数：

```rust
macro_rules! print_all {
    ($($arg:expr),*) => {
        $(println!("{}", $arg);)*
    };
}

print_all!(1, 2, 3, 4, 5);
// 展开为:
// println!("{}", 1);
// println!("{}", 2);
// println!("{}", 3);
// println!("{}", 4);
// println!("{}", 5);
```

### 1.2 重复符号

| 符号 | 含义 | 最少匹配次数 |
|------|------|-------------|
| `$(...)*` | 零个或多个 | 0 |
| `$(...)+` | 一个或多个 | 1 |
| `$(...)?` | 零个或一个 | 0 |

---

## 2. 基本重复模式

### 2.1 零个或多个 `$(...)*`

```rust
macro_rules! vec_of_strings {
    ($($x:expr),*) => {
        vec![$($x.to_string()),*]
    };
}

let empty = vec_of_strings!();           // []
let single = vec_of_strings!("hello");   // ["hello"]
let multiple = vec_of_strings!("a", "b", "c");  // ["a", "b", "c"]
```

### 2.2 一个或多个 `$(...)+`

```rust
macro_rules! sum {
    ($($x:expr),+) => {
        {
            let mut total = 0;
            $(total += $x;)*
            total
        }
    };
}

let result = sum!(1, 2, 3, 4, 5);  // 15
// let empty = sum!();  // ❌ 编译错误
```

### 2.3 零个或一个 `$(...)?`

```rust
macro_rules! optional_debug {
    ($msg:expr $(, $extra:expr)?) => {
        println!("{}", $msg);
        $(println!("Extra: {}", $extra);)?
    };
}

optional_debug!("Hello");                    // 只打印 "Hello"
optional_debug!("Hello", "World");          // 打印 "Hello" 和 "Extra: World"
```

---

## 3. 分隔符处理

### 3.1 常见分隔符

```rust
// 逗号分隔
macro_rules! comma_separated {
    ($($x:expr),*) => {
        vec![$($x),*]
    };
}

// 分号分隔
macro_rules! semicolon_separated {
    ($($x:expr);*) => {
        vec![$($x),*]
    };
}

// 空格分隔
macro_rules! space_separated {
    ($($x:expr)*) => {
        vec![$($x),*]
    };
}

let a = comma_separated!(1, 2, 3);
let b = semicolon_separated!(1; 2; 3);
let c = space_separated!(1 2 3);
```

### 3.2 尾随分隔符

```rust
macro_rules! flexible_vec {
    ($($x:expr),* $(,)?) => {  // 允许尾随逗号
        vec![$($x),*]
    };
}

let v1 = flexible_vec!(1, 2, 3);    // ✅
let v2 = flexible_vec!(1, 2, 3,);  // ✅ 尾随逗号
let v3 = flexible_vec!();           // ✅ 空参数
```

---

## 4. 嵌套重复

### 4.1 简单嵌套

```rust
macro_rules! matrix {
    ($($($x:expr),*);*) => {
        vec![
            $(
                vec![$($x),*]
            ),*
        ]
    };
}

let m = matrix!(
    1, 2, 3;
    4, 5, 6;
    7, 8, 9
);
// 结果: [[1, 2, 3], [4, 5, 6], [7, 8, 9]]
```

### 4.2 复杂嵌套

```rust
macro_rules! create_structs {
    ($($name:ident { $($field:ident: $ty:ty),* });*) => {
        $(
            struct $name {
                $($field: $ty),*
            }
        )*
    };
}

create_structs!(
    Point { x: f64, y: f64 };
    Color { r: u8, g: u8, b: u8 };
    Size { width: u32, height: u32 }
);
```

---

## 5. 重复中的条件

### 5.1 条件重复

```rust
macro_rules! conditional_repeat {
    ($($x:expr),*; $condition:expr) => {
        $(
            if $condition {
                println!("{}", $x);
            }
        )*
    };
}

conditional_repeat!(1, 2, 3, 4, 5; true);   // 打印所有
conditional_repeat!(1, 2, 3, 4, 5; false);  // 不打印任何
```

### 5.2 过滤重复

```rust
macro_rules! filter_positive {
    ($($x:expr),*) => {
        vec![
            $(
                if $x > 0 { Some($x) } else { None }
            ),*
        ].into_iter().flatten().collect::<Vec<_>>()
    };
}

let filtered = filter_positive!(-1, 2, -3, 4, -5);  // [2, 4]
```

---

## 6. 高级重复技巧

### 6.1 重复计数

```rust
macro_rules! count_args {
    ($($x:expr),*) => {
        {
            let mut count = 0;
            $(count += 1;)*
            count
        }
    };
}

let num_args = count_args!(1, 2, 3, 4, 5);  // 5
```

### 6.2 重复索引

```rust
macro_rules! indexed_print {
    ($($x:expr),*) => {
        {
            let mut index = 0;
            $(
                println!("[{}]: {}", index, $x);
                index += 1;
            )*
        }
    };
}

indexed_print!("first", "second", "third");
// 输出:
// [0]: first
// [1]: second
// [2]: third
```

### 6.3 重复分组

```rust
macro_rules! group_by_two {
    ($($x:expr),*) => {
        {
            let mut pairs = Vec::new();
            let mut iter = vec![$($x),*].into_iter();
            while let (Some(a), Some(b)) = (iter.next(), iter.next()) {
                pairs.push((a, b));
            }
            pairs
        }
    };
}

let pairs = group_by_two!(1, 2, 3, 4, 5, 6);  // [(1, 2), (3, 4), (5, 6)]
```

---

## 7. 性能优化

### 7.1 避免重复计算

```rust
macro_rules! efficient_sum {
    ($($x:expr),*) => {
        {
            // 使用迭代器避免重复计算
            [$($x),*].iter().sum()
        }
    };
}

let sum = efficient_sum!(1, 2, 3, 4, 5);
```

### 7.2 预分配容量

```rust
macro_rules! preallocated_vec {
    ($($x:expr),*) => {
        {
            let mut vec = Vec::with_capacity(count_args!($($x),*));
            $(vec.push($x);)*
            vec
        }
    };
}
```

---

## 8. 实际应用案例

### 8.1 HashMap创建宏

```rust
macro_rules! hashmap {
    ($($key:expr => $value:expr),* $(,)?) => {
        {
            let mut map = std::collections::HashMap::new();
            $(map.insert($key, $value);)*
            map
        }
    };
}

let config = hashmap! {
    "host" => "localhost",
    "port" => 8080,
    "debug" => true,
};
```

### 8.2 测试用例宏

```rust
macro_rules! test_cases {
    ($($name:ident: $input:expr => $expected:expr;)*) => {
        $(
            #[test]
            fn $name() {
                assert_eq!($input, $expected);
            }
        )*
    };
}

test_cases! {
    test_add: 1 + 1 => 2;
    test_sub: 5 - 3 => 2;
    test_mul: 2 * 3 => 6;
    test_div: 6 / 2 => 3;
}
```

### 8.3 序列化宏

```rust
macro_rules! serialize_fields {
    ($obj:expr, $($field:ident),*) => {
        {
            let mut map = std::collections::HashMap::new();
            $(
                map.insert(stringify!($field), serde_json::to_value(&$obj.$field).unwrap());
            )*
            serde_json::to_string(&map).unwrap()
        }
    };
}

struct Person {
    name: String,
    age: u32,
}

let person = Person { name: "Alice".to_string(), age: 30 };
let json = serialize_fields!(person, name, age);
```

---

## 9. 调试重复宏

### 9.1 展开调试

```rust
macro_rules! debug_repeat {
    ($($x:expr),*) => {
        {
            println!("Received {} arguments:", count_args!($($x),*));
            $(
                println!("  - {}", $x);
            )*
        }
    };
}

debug_repeat!(1, 2, 3, 4, 5);
```

### 9.2 模式调试

```rust
macro_rules! debug_pattern {
    ($($tokens:tt)*) => {
        compile_error!(concat!(
            "Pattern: ",
            stringify!($($tokens)*)
        ));
    };
}

// 取消注释来调试
// debug_pattern!(1, 2, 3, 4, 5);
```

---

## 10. 常见陷阱

### 10.1 重复不匹配

```rust
macro_rules! bad_repeat {
    ($($x:expr),*; $($y:expr),*) => {
        // ❌ 两个重复必须匹配相同的次数
        vec![$($x),*]
    };
}
```

**正确做法**：

```rust
macro_rules! good_repeat {
    ($($x:expr),*; $($y:expr),*) => {
        {
            let mut result = Vec::new();
            let mut x_iter = vec![$($x),*].into_iter();
            let mut y_iter = vec![$($y),*].into_iter();
            while let (Some(x), Some(y)) = (x_iter.next(), y_iter.next()) {
                result.push((x, y));
            }
            result
        }
    };
}
```

### 10.2 分隔符不一致

```rust
macro_rules! inconsistent_separator {
    ($($x:expr),*; $($y:expr);*) => {
        // ❌ 分隔符不一致
        vec![$($x),*]
    };
}
```

### 10.3 嵌套重复错误

```rust
macro_rules! bad_nested {
    ($($($x:expr),*;)*) => {
        // ❌ 嵌套重复语法错误
        vec![$($x),*]
    };
}
```

---

## 11. 最佳实践

### ✅ 推荐做法

1. **使用尾随逗号** - `$(...)* $(,)?` 提高灵活性
2. **明确分隔符** - 选择合适的分隔符
3. **性能考虑** - 避免不必要的重复计算
4. **错误处理** - 提供清晰的错误信息
5. **文档注释** - 解释复杂的重复模式

### ❌ 避免做法

1. **过度嵌套** - 避免过于复杂的嵌套重复
2. **性能陷阱** - 注意重复展开的性能影响
3. **不一致模式** - 保持重复模式的一致性
4. **调试困难** - 避免难以调试的复杂模式

---

## 12. 实践练习

### 练习1: 统计宏

**任务**: 创建统计函数宏。

```rust
macro_rules! stats {
    // 实现 min, max, sum, average
}

// 测试
let numbers = stats!(min 1, 5, 3, 9, 2);
let total = stats!(sum 1, 2, 3, 4, 5);
let avg = stats!(average 1, 2, 3, 4, 5);
```

### 练习2: 格式化宏

**任务**: 创建灵活的格式化宏。

```rust
macro_rules! format_table {
    // 支持表格格式化
}

// 测试
format_table!(
    "Name" | "Age" | "City";
    "Alice" | 25 | "New York";
    "Bob" | 30 | "London";
    "Charlie" | 35 | "Tokyo"
);
```

### 练习3: 配置宏

**任务**: 创建配置管理宏。

```rust
macro_rules! config {
    // 支持不同类型的配置项
}

// 测试
config! {
    app_name: "MyApp";
    version: "1.0.0";
    debug: true;
    max_connections: 100;
}
```

---

## 📚 总结

### 关键要点

1. **重复符号** - `*`、`+`、`?` 控制匹配次数
2. **分隔符** - 选择合适的分隔符提高可读性
3. **嵌套重复** - 支持复杂的嵌套模式
4. **性能优化** - 避免不必要的重复计算
5. **调试技巧** - 使用工具调试复杂重复

### 下一步

- 📖 学习 [高级模式](./04_advanced_patterns.md)
- 📖 实践 [递归宏](./05_recursive_macros.md)
- 💻 运行: `cargo run --example 03_repetition`

---

**作者**: Rust学习社区  
**最后更新**: 2025-10-20  
**许可**: MIT
