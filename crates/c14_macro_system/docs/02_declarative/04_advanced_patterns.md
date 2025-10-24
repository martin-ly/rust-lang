# 高级模式

> **文档定位**: 声明宏的高级技巧和模式  
> **难度级别**: ⭐⭐⭐ 高级  
> **预计时间**: 4小时  
> **最后更新**: 2025-10-20

---

## 📊 目录

- [高级模式](#高级模式)
  - [📊 目录](#-目录)
  - [📋 学习目标](#-学习目标)
  - [1. TT Muncher模式](#1-tt-muncher模式)
    - [1.1 基本概念](#11-基本概念)
    - [1.2 经典实现](#12-经典实现)
    - [1.3 应用：解析表达式](#13-应用解析表达式)
  - [2. Push-down Accumulation](#2-push-down-accumulation)
    - [2.1 累积器模式](#21-累积器模式)
    - [2.2 应用：树遍历](#22-应用树遍历)
  - [3. 内部规则模式](#3-内部规则模式)
    - [3.1 使用@前缀](#31-使用前缀)
    - [3.2 多阶段处理](#32-多阶段处理)
  - [4. 回调模式](#4-回调模式)
    - [4.1 基本回调](#41-基本回调)
    - [4.2 高阶宏](#42-高阶宏)
  - [5. 续延传递风格(CPS)](#5-续延传递风格cps)
    - [5.1 CPS基础](#51-cps基础)
    - [5.2 复杂控制流](#52-复杂控制流)
  - [6. 类型级编程](#6-类型级编程)
    - [6.1 类型计算](#61-类型计算)
    - [6.2 类型转换宏](#62-类型转换宏)
  - [7. DSL构建技巧](#7-dsl构建技巧)
    - [7.1 声明式DSL](#71-声明式dsl)
    - [7.2 命令式DSL](#72-命令式dsl)
  - [8. 性能优化技巧](#8-性能优化技巧)
    - [8.1 编译期常量](#81-编译期常量)
    - [8.2 避免重复展开](#82-避免重复展开)
  - [9. 调试高级宏](#9-调试高级宏)
    - [9.1 追踪展开](#91-追踪展开)
    - [9.2 断言宏](#92-断言宏)
  - [10. 实际应用案例](#10-实际应用案例)
    - [10.1 SQL查询构建器](#101-sql查询构建器)
    - [10.2 测试框架](#102-测试框架)
    - [10.3 配置管理器](#103-配置管理器)
  - [11. 最佳实践](#11-最佳实践)
    - [✅ 推荐做法](#-推荐做法)
    - [❌ 避免做法](#-避免做法)
  - [12. 实践练习](#12-实践练习)
    - [练习1: JSON构建器](#练习1-json构建器)
    - [练习2: 状态机DSL](#练习2-状态机dsl)
    - [练习3: 管道操作符](#练习3-管道操作符)
  - [📚 总结](#-总结)
    - [关键要点](#关键要点)
    - [下一步](#下一步)

## 📋 学习目标

完成本章后，你将能够：

- ✅ 掌握TT Muncher模式
- ✅ 理解Push-down Accumulation
- ✅ 实现内部规则模式
- ✅ 使用回调和续延技巧
- ✅ 构建复杂的DSL

---

## 1. TT Muncher模式

### 1.1 基本概念

**TT Muncher**（Token Tree Muncher）逐个处理token：

```rust
macro_rules! count_tts {
    () => { 0 };
    ($odd:tt $($a:tt $b:tt)*) => {
        (count_tts!($($a)*) << 1) | 1
    };
    ($($a:tt $even:tt)*) => {
        count_tts!($($a)*) << 1
    };
}

let count = count_tts!(a b c d e);  // 5
```

### 1.2 经典实现

```rust
macro_rules! tt_muncher {
    // 基础情况：没有更多token
    () => { 0 };
    // 递归情况：处理一个token
    ($tt:tt $($rest:tt)*) => {
        1 + tt_muncher!($($rest)*)
    };
}

let count = tt_muncher!(hello world foo bar);  // 4
```

### 1.3 应用：解析表达式

```rust
macro_rules! parse_expr {
    // 数字字面量
    (@munch $acc:expr, $num:literal $($rest:tt)*) => {
        parse_expr!(@munch $acc + $num, $($rest)*)
    };
    // 加法运算符
    (@munch $acc:expr, + $($rest:tt)*) => {
        parse_expr!(@munch $acc, $($rest)*)
    };
    // 完成解析
    (@munch $acc:expr, ) => { $acc };
    // 入口
    ($($tokens:tt)*) => {
        parse_expr!(@munch 0, $($tokens)*)
    };
}

let result = parse_expr!(1 + 2 + 3 + 4);  // 10
```

---

## 2. Push-down Accumulation

### 2.1 累积器模式

**Push-down Accumulation**使用累积器收集结果：

```rust
macro_rules! reverse {
    // 内部规则：使用累积器
    (@acc [$($rev:tt)*] []) => {
        [$($rev)*]
    };
    (@acc [$($rev:tt)*] [$first:tt $($rest:tt)*]) => {
        reverse!(@acc [$first $($rev)*] [$($rest)*])
    };
    // 公共入口
    ([$($input:tt)*]) => {
        reverse!(@acc [] [$($input)*])
    };
}

let reversed = reverse!([1, 2, 3, 4, 5]);  // [5, 4, 3, 2, 1]
```

### 2.2 应用：树遍历

```rust
macro_rules! flatten_tree {
    // 累积器：收集所有叶子节点
    (@acc [$($acc:tt)*] []) => {
        [$($acc)*]
    };
    // 遇到分支：展开子树
    (@acc [$($acc:tt)*] [($($branch:tt)*) $($rest:tt)*]) => {
        flatten_tree!(@acc [$($acc)*] [$($branch)* $($rest)*])
    };
    // 遇到叶子：添加到累积器
    (@acc [$($acc:tt)*] [$leaf:tt $($rest:tt)*]) => {
        flatten_tree!(@acc [$($acc)* $leaf] [$($rest)*])
    };
    // 入口
    ($($tree:tt)*) => {
        flatten_tree!(@acc [] [$($tree)*])
    };
}

let flat = flatten_tree!((1 (2 3) 4) (5 6));  // [1, 2, 3, 4, 5, 6]
```

---

## 3. 内部规则模式

### 3.1 使用@前缀

**内部规则**是宏的私有辅助规则：

```rust
macro_rules! public_macro {
    // 公共接口
    ($($arg:tt)*) => {
        public_macro!(@internal parse $($arg)*)
    };
    // 内部规则：解析
    (@internal parse $($tokens:tt)*) => {
        public_macro!(@internal process $($tokens)*)
    };
    // 内部规则：处理
    (@internal process $($tokens:tt)*) => {
        // 实际实现
        stringify!($($tokens)*)
    };
}

let result = public_macro!(hello world);
```

### 3.2 多阶段处理

```rust
macro_rules! multi_stage {
    // 阶段1：收集输入
    (@stage1 [$($collected:tt)*] $next:tt $($rest:tt)*) => {
        multi_stage!(@stage1 [$($collected)* $next] $($rest)*)
    };
    (@stage1 [$($collected:tt)*]) => {
        multi_stage!(@stage2 $($collected)*)
    };
    // 阶段2：转换
    (@stage2 $($tokens:tt)*) => {
        multi_stage!(@stage3 $($tokens)*)
    };
    // 阶段3：输出
    (@stage3 $($tokens:tt)*) => {
        vec![$($tokens),*]
    };
    // 公共入口
    ($($input:tt)*) => {
        multi_stage!(@stage1 [] $($input)*)
    };
}
```

---

## 4. 回调模式

### 4.1 基本回调

```rust
macro_rules! with_callback {
    // 执行操作后调用回调
    ($op:expr, $callback:ident) => {
        {
            let result = $op;
            $callback!(result)
        }
    };
}

macro_rules! print_callback {
    ($x:expr) => {
        println!("Result: {}", $x);
    };
}

with_callback!(1 + 2, print_callback);  // 输出: Result: 3
```

### 4.2 高阶宏

```rust
macro_rules! map_macro {
    ($mapper:ident, $($item:expr),*) => {
        vec![$($mapper!($item)),*]
    };
}

macro_rules! double {
    ($x:expr) => { $x * 2 };
}

macro_rules! square {
    ($x:expr) => { $x * $x };
}

let doubled = map_macro!(double, 1, 2, 3, 4);  // [2, 4, 6, 8]
let squared = map_macro!(square, 1, 2, 3, 4);  // [1, 4, 9, 16]
```

---

## 5. 续延传递风格(CPS)

### 5.1 CPS基础

```rust
macro_rules! cps_add {
    ($a:expr, $b:expr, $cont:ident) => {
        $cont!($a + $b)
    };
}

macro_rules! cps_mul {
    ($a:expr, $b:expr, $cont:ident) => {
        $cont!($a * $b)
    };
}

macro_rules! print_cont {
    ($result:expr) => {
        println!("Final result: {}", $result);
    };
}

// 链式计算：(2 + 3) * 4
cps_add!(2, 3, intermediate_cont);

macro_rules! intermediate_cont {
    ($x:expr) => {
        cps_mul!($x, 4, print_cont)
    };
}
```

### 5.2 复杂控制流

```rust
macro_rules! if_then_else {
    ($cond:expr, $then:ident, $else:ident) => {
        if $cond {
            $then!()
        } else {
            $else!()
        }
    };
}

macro_rules! then_branch {
    () => { println!("Condition was true"); };
}

macro_rules! else_branch {
    () => { println!("Condition was false"); };
}

if_then_else!(true, then_branch, else_branch);
```

---

## 6. 类型级编程

### 6.1 类型计算

```rust
macro_rules! type_eq {
    ($a:ty, $b:ty) => {
        {
            fn _type_check(_: $a) -> $b { unimplemented!() }
            true
        }
    };
}

// 检查类型相等
let is_same = type_eq!(i32, i32);  // true
```

### 6.2 类型转换宏

```rust
macro_rules! convert_type {
    // 数字类型转换
    ($value:expr, i32 => f64) => {
        $value as f64
    };
    ($value:expr, f64 => i32) => {
        $value as i32
    };
    // 字符串转换
    ($value:expr, &str => String) => {
        $value.to_string()
    };
    ($value:expr, String => &str) => {
        &$value[..]
    };
}

let f = convert_type!(42, i32 => f64);
let s = convert_type!("hello", &str => String);
```

---

## 7. DSL构建技巧

### 7.1 声明式DSL

```rust
macro_rules! html {
    // 标签：<tag>content</tag>
    ($tag:ident { $($content:tt)* }) => {
        format!("<{}>{}</{}>",
            stringify!($tag),
            html!($($content)*),
            stringify!($tag)
        )
    };
    // 标签带属性：<tag attr="value">content</tag>
    ($tag:ident [$($attr:ident = $val:expr),*] { $($content:tt)* }) => {
        format!("<{} {}>{}</{}>",
            stringify!($tag),
            vec![$(format!("{}=\"{}\"", stringify!($attr), $val)),*].join(" "),
            html!($($content)*),
            stringify!($tag)
        )
    };
    // 文本内容
    ($text:expr) => { $text };
}

let page = html! {
    html {
        body [class = "container"] {
            h1 { "Welcome" }
            p { "Hello, World!" }
        }
    }
};
```

### 7.2 命令式DSL

```rust
macro_rules! state_machine {
    (
        states { $($state:ident),* }
        transitions {
            $($from:ident => $to:ident on $event:ident),*
        }
    ) => {
        enum State {
            $($state),*
        }
        
        impl State {
            fn transition(&mut self, event: Event) {
                match (self, event) {
                    $(
                        (State::$from, Event::$event) => {
                            *self = State::$to;
                        }
                    ),*
                    _ => {}
                }
            }
        }
    };
}

state_machine! {
    states { Idle, Running, Stopped }
    transitions {
        Idle => Running on Start,
        Running => Stopped on Stop,
        Stopped => Idle on Reset
    }
}
```

---

## 8. 性能优化技巧

### 8.1 编译期常量

```rust
macro_rules! const_expr {
    ($expr:expr) => {
        {
            const VALUE: _ = $expr;
            VALUE
        }
    };
}

let x = const_expr!(2 + 3 * 4);  // 编译期计算
```

### 8.2 避免重复展开

```rust
macro_rules! cached_computation {
    ($expensive:expr) => {
        {
            static CACHE: std::sync::Once = std::sync::Once::new();
            static mut RESULT: Option<_> = None;
            
            unsafe {
                CACHE.call_once(|| {
                    RESULT = Some($expensive);
                });
                RESULT.unwrap()
            }
        }
    };
}
```

---

## 9. 调试高级宏

### 9.1 追踪展开

```rust
macro_rules! trace {
    ($($tokens:tt)*) => {
        {
            eprintln!("Trace: {}", stringify!($($tokens)*));
            $($tokens)*
        }
    };
}
```

### 9.2 断言宏

```rust
macro_rules! static_assert {
    ($condition:expr) => {
        const _: () = assert!($condition);
    };
}

static_assert!(size_of::<i32>() == 4);
```

---

## 10. 实际应用案例

### 10.1 SQL查询构建器

```rust
macro_rules! sql_query {
    (SELECT $($field:ident),* FROM $table:ident WHERE $($condition:tt)*) => {
        format!(
            "SELECT {} FROM {} WHERE {}",
            stringify!($($field),*),
            stringify!($table),
            stringify!($($condition)*)
        )
    };
}

let query = sql_query!(SELECT id, name, email FROM users WHERE age > 18);
```

### 10.2 测试框架

```rust
macro_rules! test_suite {
    (
        $suite_name:ident {
            $(
                $test_name:ident: $test_body:block
            )*
        }
    ) => {
        mod $suite_name {
            $(
                #[test]
                fn $test_name() $test_body
            )*
        }
    };
}

test_suite! {
    math_tests {
        test_addition: {
            assert_eq!(1 + 1, 2);
        }
        test_subtraction: {
            assert_eq!(5 - 3, 2);
        }
        test_multiplication: {
            assert_eq!(2 * 3, 6);
        }
    }
}
```

### 10.3 配置管理器

```rust
macro_rules! config_manager {
    (
        $(
            $section:ident {
                $($key:ident: $ty:ty = $default:expr),*
            }
        )*
    ) => {
        pub struct Config {
            $(
                pub struct $section {
                    $(pub $key: $ty),*
                }
            )*
        }
        
        impl Default for Config {
            fn default() -> Self {
                Config {
                    $(
                        $section: $section {
                            $($key: $default),*
                        }
                    ),*
                }
            }
        }
    };
}

config_manager! {
    database {
        host: String = "localhost".to_string(),
        port: u16 = 5432,
        max_connections: usize = 100
    }
    logging {
        level: String = "info".to_string(),
        file: Option<String> = None
    }
}
```

---

## 11. 最佳实践

### ✅ 推荐做法

1. **使用内部规则** - 通过@前缀组织复杂逻辑
2. **累积器模式** - 处理需要收集的操作
3. **TT Muncher** - 逐个处理token
4. **文档完善** - 详细说明高级技巧的用法
5. **性能测试** - 验证编译时间影响

### ❌ 避免做法

1. **过度复杂** - 避免不必要的高级技巧
2. **难以维护** - 保持代码可读性
3. **性能陷阱** - 注意递归深度限制
4. **缺少测试** - 为复杂宏编写充分测试

---

## 12. 实践练习

### 练习1: JSON构建器

**任务**: 创建JSON DSL宏。

```rust
macro_rules! json {
    // 实现JSON构建语法
}

// 测试
let json_obj = json! {
    "name": "Alice",
    "age": 30,
    "hobbies": ["reading", "coding"],
    "address": {
        "city": "New York",
        "zip": "10001"
    }
};
```

### 练习2: 状态机DSL

**任务**: 创建完整的状态机DSL。

```rust
macro_rules! fsm {
    // 实现状态机定义语法
}

// 测试
fsm! {
    initial: Idle;
    states: Idle, Running, Paused, Stopped;
    transitions {
        Idle -> Running on Start,
        Running -> Paused on Pause,
        Paused -> Running on Resume,
        Running -> Stopped on Stop
    };
}
```

### 练习3: 管道操作符

**任务**: 实现函数管道宏。

```rust
macro_rules! pipe {
    // 实现管道语法 value |> func1 |> func2 |> func3
}

// 测试
let result = pipe!(
    5
    |> (|x| x * 2)
    |> (|x| x + 1)
    |> (|x| x.to_string())
);
```

---

## 📚 总结

### 关键要点

1. **TT Muncher** - 逐个处理token的强大模式
2. **累积器** - 收集和转换数据
3. **内部规则** - 组织复杂宏逻辑
4. **回调模式** - 实现高阶宏
5. **DSL构建** - 创建领域特定语言

### 下一步

- 📖 学习 [递归宏](./05_recursive_macros.md)
- 📖 探索 [过程宏](../03_procedural/01_proc_macro_basics.md)
- 💻 实践项目：构建自己的DSL

---

**作者**: Rust学习社区  
**最后更新**: 2025-10-20  
**许可**: MIT
