# 递归宏

> **文档定位**: 声明宏中的递归技术和应用  
> **难度级别**: ⭐⭐⭐ 高级  
> **预计时间**: 4小时  
> **最后更新**: 2025-10-20

---

## 📋 学习目标

完成本章后，你将能够：

- ✅ 理解宏递归的基本原理
- ✅ 实现各种递归模式
- ✅ 处理递归深度限制
- ✅ 优化递归宏性能
- ✅ 应用递归宏解决复杂问题

---

## 1. 递归基础

### 1.1 什么是递归宏？

**递归宏**是在自己的定义中调用自己的宏：

```rust
macro_rules! count {
    // 基础情况
    () => { 0 };
    // 递归情况
    ($x:tt $($rest:tt)*) => {
        1 + count!($($rest)*)
    };
}

let n = count!(a b c d e);  // 5
```

### 1.2 递归结构

递归宏通常包含：

1. **基础情况** (Base Case) - 停止递归的条件
2. **递归情况** (Recursive Case) - 调用自己并减小问题规模

```rust
macro_rules! factorial {
    (0) => { 1 };                    // 基础情况
    ($n:expr) => {                   // 递归情况
        $n * factorial!($n - 1)      // 递归调用
    };
}
```

---

## 2. 基本递归模式

### 2.1 计数递归

```rust
macro_rules! count {
    () => { 0 };
    ($head:tt $($tail:tt)*) => {
        1 + count!($($tail)*)
    };
}

assert_eq!(count!(), 0);
assert_eq!(count!(a), 1);
assert_eq!(count!(a b c d e), 5);
```

### 2.2 求和递归

```rust
macro_rules! sum {
    () => { 0 };
    ($x:expr) => { $x };
    ($x:expr, $($rest:expr),+) => {
        $x + sum!($($rest),+)
    };
}

assert_eq!(sum!(), 0);
assert_eq!(sum!(5), 5);
assert_eq!(sum!(1, 2, 3, 4, 5), 15);
```

### 2.3 查找递归

```rust
macro_rules! find_max {
    ($x:expr) => { $x };
    ($x:expr, $($rest:expr),+) => {
        {
            let rest_max = find_max!($($rest),+);
            if $x > rest_max { $x } else { rest_max }
        }
    };
}

assert_eq!(find_max!(5), 5);
assert_eq!(find_max!(1, 5, 3, 9, 2), 9);
```

---

## 3. 列表处理

### 3.1 列表反转

```rust
macro_rules! reverse {
    // 内部规则：使用累积器
    (@acc [] [$($rev:tt)*]) => {
        [$($rev)*]
    };
    (@acc [$first:tt $($rest:tt)*] [$($rev:tt)*]) => {
        reverse!(@acc [$($rest)*] [$first $($rev)*])
    };
    // 公共接口
    ([$($list:tt)*]) => {
        reverse!(@acc [$($list)*] [])
    };
}

let reversed = reverse!([1, 2, 3, 4, 5]);
// 结果: [5, 4, 3, 2, 1]
```

### 3.2 列表过滤

```rust
macro_rules! filter_positive {
    (@acc [$($acc:expr),*] []) => {
        vec![$($acc),*]
    };
    (@acc [$($acc:expr),*] [$first:expr, $($rest:expr),*]) => {
        filter_positive!(
            @acc
            [$($acc,)* $first]
            [$($rest),*]
        )
    };
    (@acc [$($acc:expr),*] [$first:expr $(, $rest:expr)*]) => {
        filter_positive!(@acc [$($acc),*] [$($rest),*])
    };
    ($($list:expr),*) => {
        filter_positive!(@acc [] [$($list),*])
    };
}
```

### 3.3 列表映射

```rust
macro_rules! map_double {
    (@acc [$($acc:expr),*] []) => {
        vec![$($acc),*]
    };
    (@acc [$($acc:expr),*] [$first:expr, $($rest:expr),*]) => {
        map_double!(@acc [$($acc,)* $first * 2] [$($rest),*])
    };
    ($($list:expr),*) => {
        map_double!(@acc [] [$($list),*])
    };
}

let doubled = map_double!(1, 2, 3, 4, 5);
// 结果: [2, 4, 6, 8, 10]
```

---

## 4. 树结构递归

### 4.1 树深度计算

```rust
macro_rules! tree_depth {
    // 叶子节点
    (leaf $value:expr) => { 1 };
    // 分支节点
    (node $left:tt $right:tt) => {
        {
            let left_depth = tree_depth!($left);
            let right_depth = tree_depth!($right);
            1 + if left_depth > right_depth {
                left_depth
            } else {
                right_depth
            }
        }
    };
}

let depth = tree_depth!(
    node
        (node (leaf 1) (leaf 2))
        (leaf 3)
);  // 3
```

### 4.2 树遍历

```rust
macro_rules! traverse_tree {
    // 叶子节点
    (@acc [$($acc:expr),*] leaf $value:expr) => {
        vec![$($acc,)* $value]
    };
    // 分支节点
    (@acc [$($acc:expr),*] node $left:tt $right:tt) => {
        {
            let left_vals = traverse_tree!(@acc [$($acc),*] $left);
            traverse_tree!(@acc left_vals $right)
        }
    };
    // 公共接口
    ($tree:tt) => {
        traverse_tree!(@acc [] $tree)
    };
}
```

---

## 5. 数学计算

### 5.1 阶乘

```rust
macro_rules! factorial {
    (0) => { 1 };
    (1) => { 1 };
    ($n:expr) => {
        $n * factorial!($n - 1)
    };
}

const FACT_5: usize = factorial!(5);  // 120
```

### 5.2 斐波那契

```rust
macro_rules! fibonacci {
    (0) => { 0 };
    (1) => { 1 };
    ($n:expr) => {
        fibonacci!($n - 1) + fibonacci!($n - 2)
    };
}

const FIB_10: usize = fibonacci!(10);  // 55
```

### 5.3 最大公约数

```rust
macro_rules! gcd {
    ($a:expr, 0) => { $a };
    ($a:expr, $b:expr) => {
        gcd!($b, $a % $b)
    };
}

const GCD: usize = gcd!(48, 18);  // 6
```

---

## 6. 递归深度管理

### 6.1 默认限制

Rust默认限制宏递归深度为128层：

```rust
#![recursion_limit = "128"]  // 默认值
```

### 6.2 增加限制

```rust
#![recursion_limit = "256"]  // 增加到256层

macro_rules! deep_recursion {
    (0) => { 0 };
    ($n:expr) => {
        1 + deep_recursion!($n - 1)
    };
}

const DEEP: usize = deep_recursion!(200);
```

### 6.3 避免深度问题

使用累积器模式避免深递归：

```rust
macro_rules! tail_recursive_sum {
    // 尾递归：使用累积器
    (@acc $acc:expr, 0) => { $acc };
    (@acc $acc:expr, $n:expr) => {
        tail_recursive_sum!(@acc $acc + $n, $n - 1)
    };
    ($n:expr) => {
        tail_recursive_sum!(@acc 0, $n)
    };
}
```

---

## 7. 优化技巧

### 7.1 尾递归优化

```rust
// 非尾递归（可能栈溢出）
macro_rules! bad_sum {
    ($x:expr) => { $x };
    ($x:expr, $($rest:expr),+) => {
        $x + bad_sum!($($rest),+)  // 不是尾递归
    };
}

// 尾递归（使用累积器）
macro_rules! good_sum {
    (@acc $acc:expr,) => { $acc };
    (@acc $acc:expr, $x:expr, $($rest:expr),*) => {
        good_sum!(@acc $acc + $x, $($rest),*)  // 尾递归
    };
    ($($x:expr),+) => {
        good_sum!(@acc 0, $($x),+)
    };
}
```

### 7.2 记忆化

```rust
macro_rules! memoized_fib {
    (0) => { 0 };
    (1) => { 1 };
    ($n:expr) => {
        {
            static mut CACHE: [Option<usize>; 100] = [None; 100];
            unsafe {
                if let Some(result) = CACHE[$n] {
                    result
                } else {
                    let result = memoized_fib!($n - 1) + memoized_fib!($n - 2);
                    CACHE[$n] = Some(result);
                    result
                }
            }
        }
    };
}
```

---

## 8. 复杂递归应用

### 8.1 表达式求值

```rust
macro_rules! eval_expr {
    // 数字
    ($num:literal) => { $num };
    // 加法
    ((add $left:tt $right:tt)) => {
        eval_expr!($left) + eval_expr!($right)
    };
    // 乘法
    ((mul $left:tt $right:tt)) => {
        eval_expr!($left) * eval_expr!($right)
    };
    // 减法
    ((sub $left:tt $right:tt)) => {
        eval_expr!($left) - eval_expr!($right)
    };
}

let result = eval_expr!((add (mul 2 3) (sub 10 5)));  // 11
```

### 8.2 类型级自然数

```rust
macro_rules! type_nat {
    (Z) => { () };  // 零
    (S $n:tt) => { (type_nat!($n),) };  // 后继
}

type Zero = type_nat!(Z);
type One = type_nat!(S Z);
type Two = type_nat!(S S Z);
type Three = type_nat!(S S S Z);
```

### 8.3 模式匹配树

```rust
macro_rules! match_tree {
    // 叶子模式
    (@match $value:expr, leaf $pat:pat => $result:expr) => {
        match $value {
            $pat => $result,
            _ => panic!("No match"),
        }
    };
    // 分支模式
    (@match $value:expr, node $left_pat:tt $right_pat:tt => $result:expr) => {
        match $value {
            ($left, $right) => {
                let left_result = match_tree!(@match $left, $left_pat => ());
                let right_result = match_tree!(@match $right, $right_pat => ());
                $result
            }
            _ => panic!("No match"),
        }
    };
}
```

---

## 9. 调试递归宏

### 9.1 追踪递归

```rust
macro_rules! trace_recursive {
    (@depth 0, $($arg:tt)*) => {
        println!("Base case reached");
        0
    };
    (@depth $n:expr, $($arg:tt)*) => {
        {
            println!("Depth: {}", $n);
            1 + trace_recursive!(@depth $n - 1, $($arg)*)
        }
    };
    ($n:expr) => {
        trace_recursive!(@depth $n,)
    };
}

let depth = trace_recursive!(5);
```

### 9.2 递归可视化

```rust
macro_rules! visualize_recursion {
    (@indent $indent:expr, $msg:expr) => {
        println!("{}{}", "  ".repeat($indent), $msg);
    };
    (@rec $indent:expr, 0) => {
        {
            visualize_recursion!(@indent $indent, "→ Base case: 0");
            0
        }
    };
    (@rec $indent:expr, $n:expr) => {
        {
            visualize_recursion!(@indent $indent, format!("→ Computing: {}", $n));
            let result = 1 + visualize_recursion!(@rec $indent + 1, $n - 1);
            visualize_recursion!(@indent $indent, format!("← Result: {}", result));
            result
        }
    };
    ($n:expr) => {
        visualize_recursion!(@rec 0, $n)
    };
}
```

---

## 10. 实际应用案例

### 10.1 JSON解析器

```rust
macro_rules! parse_json {
    // 对象
    ({ $($key:ident: $value:tt),* }) => {
        {
            let mut map = std::collections::HashMap::new();
            $(
                map.insert(
                    stringify!($key).to_string(),
                    parse_json!($value)
                );
            )*
            map
        }
    };
    // 数组
    ([ $($item:tt),* ]) => {
        vec![$(parse_json!($item)),*]
    };
    // 字符串
    ($string:expr) => {
        $string.to_string()
    };
}

let json = parse_json!({
    name: "Alice",
    age: 30,
    hobbies: ["reading", "coding"]
});
```

### 10.2 路径解析器

```rust
macro_rules! parse_path {
    // 根路径
    (/) => { vec!["/".to_string()] };
    // 递归解析
    (/ $segment:ident $($rest:tt)*) => {
        {
            let mut path = vec![stringify!($segment).to_string()];
            path.extend(parse_path!($($rest)*));
            path
        }
    };
    // 基础情况
    () => { vec![] };
}

let path = parse_path!(/ users / 123 / profile);
// 结果: ["users", "123", "profile"]
```

---

## 11. 最佳实践

### ✅ 推荐做法

1. **明确基础情况** - 确保递归有明确的终止条件
2. **使用累积器** - 避免深度递归
3. **限制递归深度** - 适当设置`recursion_limit`
4. **添加调试** - 为复杂递归添加追踪
5. **性能测试** - 验证编译时间影响

### ❌ 避免做法

1. **无限递归** - 确保有退出条件
2. **深度过大** - 注意递归深度限制
3. **低效模式** - 避免指数级复杂度
4. **难以调试** - 保持递归逻辑清晰

---

## 12. 实践练习

### 练习1: 快速排序

**任务**: 实现递归快速排序宏。

```rust
macro_rules! quicksort {
    // 实现快速排序逻辑
}

// 测试
let sorted = quicksort!(5, 2, 8, 1, 9, 3);
```

### 练习2: 二叉搜索树

**任务**: 实现BST操作宏。

```rust
macro_rules! bst {
    // 实现插入、查找、删除
}

// 测试
let tree = bst!(insert 5, insert 3, insert 7, insert 1);
let found = bst!(search tree, 3);
```

### 练习3: 表达式简化

**任务**: 实现代数表达式简化宏。

```rust
macro_rules! simplify {
    // 实现 0 + x = x, 1 * x = x 等规则
}

// 测试
let simplified = simplify!((add 0 (mul 1 x)));
// 结果应该是: x
```

---

## 📚 总结

### 关键要点

1. **基础与递归** - 明确基础情况和递归情况
2. **累积器模式** - 避免深度递归
3. **递归限制** - 注意深度限制和性能
4. **优化技巧** - 尾递归和记忆化
5. **调试方法** - 追踪和可视化递归

### 下一步

- 📖 学习 [过程宏基础](../03_procedural/01_proc_macro_basics.md)
- 📖 探索 [最佳实践](../05_practice/01_common_patterns.md)
- 💻 运行: `cargo run --example 04_recursive_macros`

---

**作者**: Rust学习社区  
**最后更新**: 2025-10-20  
**许可**: MIT
