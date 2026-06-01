//! 编译时元编程（Compile-Time Metaprogramming）

/// 常量元编程：利用 `const fn` 和 `const` 泛型在编译期完成计算
/// constant ： `const fn` and `const` generic in complete
/// constant ： `const fn` and `const` generic in
/// 两者结合可以实现零运行时开销的元编程。
/// can runtime overhead 。
pub struct ConstMetaprogramming;

impl ConstMetaprogramming {
    /// 返回 `const fn` 概念文档
    /// `const fn` concept
    pub fn const_fn_concept() -> &'static str {
        r#"
# `const fn` 作为编译时计算工具

`const fn` 是 Rust 中在编译期执行计算的主要机制之一。与宏不同，
`const fn` 操作的是值而非语法树，因此具有完整的类型检查和语义分析。

## `const fn` vs 宏

| 维度 | `const fn` | 宏 (macro_rules!) |
|------|-----------|-------------------|
| 操作对象 | 值 / 类型 | 语法树 (TokenTree) |
| 类型检查 | 完整 | 展开后才检查 |
| 适用场景 | 数值/结构计算 | 代码生成/模式匹配 |
| 递归限制 | 受 const 求值限制 | 受递归深度限制 |
| 调试体验 | 更好（有类型信息） | 较难（需看展开结果）|

## 典型应用
- 数组长度计算
- 查找表生成
- 编译期断言 (`const_assert!`)
- 位掩码计算
        "#
    }

    /// 展示 `const fn` 计算数组长度
    /// `const fn` array
    /// `const fn`
    pub const fn array_len_from_const_fn() -> usize {
        // 在编译期计算长度
        const fn compute_size(base: usize, multiplier: usize) -> usize {
            base * multiplier
        }

        compute_size(4, 8)
    }

    /// 返回 `const` 泛型概念文档
    /// `const` generic concept
    pub fn const_generics_concept() -> &'static str {
        r#"
# `const` 泛型用于类型级计算

`const N: usize` 等 const 泛型参数将编译期常量提升到类型系统中，
使得类型可以携带数值信息，实现依赖类型的轻量级版本。

## 核心能力
- 定长数组 `[T; N]` 的泛化抽象
- 编译期维度检查（矩阵运算、物理量）
- 类型状态机（Type-State Pattern）

## 与 `const fn` 的协同
`const` 泛型提供"类型层面的常量"，`const fn` 提供"值层面的计算"，
两者在 `where` 约束和关联常量中可以交互。
        "#
    }

    /// 使用 const 泛型进行编译期维度检查
    /// const generic dimension
    pub fn matrix_dimension_demo() {
        /// 定长向量，长度在类型中编码
        /// ，in type in
        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        pub struct Vector<T, const N: usize>([T; N]);

        impl<T: Copy + Default, const N: usize> Vector<T, N> {
            /// 创建零向量
            pub fn zero() -> Self {
                Self([T::default(); N])
            }

            /// 向量长度（编译期已知）
            /// （）
            pub const fn len(&self) -> usize {
                N
            }
        }

        // 只有相同维度的向量才能相加
        impl<T: core::ops::Add<Output = T> + Copy, const N: usize> core::ops::Add for Vector<T, N> {
            type Output = Self;

            #[allow(clippy::needless_range_loop)]
            fn add(self, rhs: Self) -> Self::Output {
                let mut result = self.0;
                for i in 0..N {
                    result[i] = self.0[i] + rhs.0[i];
                }
                Self(result)
            }
        }

        let a = Vector::<i32, 3>([1, 2, 3]);
        let b = Vector::<i32, 3>([4, 5, 6]);
        let _c = a + b;
        // let d = Vector::<i32, 4>([1, 2, 3, 4]);
        // _c + d; // 编译错误：维度不匹配

        // 编译期已知长度
        let len = a.len();
        assert_eq!(len, 3);

        // 使用零向量避免 dead_code 警告
        let _z = Vector::<i32, 3>::zero();
    }

    /// 返回 `std::mem::size_of` 概念文档
    /// `std::mem::size_of` concept
    pub fn size_of_concept() -> &'static str {
        r#"
# `std::mem::size_of` 与其他 const 操作

`size_of::<T>()` 是 Rust 中最基础的编译期内省操作之一，
它返回类型 `T` 的字节大小，且是一个 `const fn`。

## 常用编译期内省操作
- `size_of::<T>()` / `size_of_val(&v)` — 类型/值的大小
- `align_of::<T>()` — 类型的对齐要求
- `offset_of!(Struct, field)` — 字段偏移量（Rust 1.77+）
- `variant_count::<T>()` — 枚举变体数量（Rust 1.70+）

## 应用场景
- 缓冲区大小预分配
- FFI 布局验证
- 静态断言类型大小
        "#
    }

    /// 编译期断言类型大小
    /// type
    pub const fn assert_type_size<T>() {
        // 使用 const 断言确保类型大小符合预期
        const fn check_size<T>() {
            assert!(core::mem::size_of::<T>() > 0, "ZST not allowed here");
        }
        check_size::<T>();
    }

    /// 返回 const 求值限制概念文档
    /// const concept
    pub fn const_limitations_concept() -> &'static str {
        r#"
# const 求值的限制

尽管 Rust 的 const 求值能力不断增强，仍存在一些编译期限制：

## 当前限制（截至 Rust 1.95+）
1. **浮点运算**：`const fn` 中允许，但某些操作（如 `transmute`）受限
2. **内存分配**：不能在 const 上下文中使用 `Box::new`、`Vec::new` 等
3. **循环**：稳定，但复杂控制流仍可能触发求值限制
4. **trait 对象**：`dyn Trait` 不能在 const 中使用
5. **递归深度**：const 求值有内部步骤限制（默认约 1_000_000 步）

## 与宏的互补
当 const 求值无法完成时（如需生成新类型名、动态代码结构），
宏仍然是必要的编译时工具。两者是互补而非替代关系。
        "#
    }
}

/// 将两者结合可以生成高效的编译期数据结构。
/// will can efficient data structure 。
pub struct MacroAndConstSynergy;

impl MacroAndConstSynergy {
    pub fn macro_generates_const_concept() -> &'static str {
        r#"
# 宏生成 `const` 声明

宏可以在编译期展开为多个 `const` 声明，将运行时的查找表、
配置映射等数据提升到编译期。

## 优势
- 运行时零开销：所有数据已内联到代码中
- 类型安全：生成的常量仍经过类型检查
- 可读性：源代码保持简洁，宏隐藏重复样板

## 典型模式
```rust
macro_rules! define_consts {
    ($($name:ident = $value:expr),* $(,)?) => {
        $(
            pub const $name: i32 = $value;
        )*
    };
}
```
        "#
    }

    /// 宏生成 const 查找表
    /// const
    pub fn const_lookup_table_demo() {
        /// 生成编译期查找表的宏
        macro_rules! const_lookup_table {
            ($name:ident: [$ty:ty; $len:expr] = $default:expr, { $($key:expr => $value:expr),* $(,)? }) => {
                const $name: [$ty; $len] = {
                    let mut table = [$default; $len];
                    $(
                        table[$key] = $value;
                    )*
                    table
                };
            };
        }

        // 生成一个编译期 ASCII 控制字符检测表
        const_lookup_table!(
            ASCII_CONTROL_TABLE: [bool; 128] = false, {
                0x00 => true, 0x01 => true, 0x02 => true, 0x03 => true,
                0x04 => true, 0x05 => true, 0x06 => true, 0x07 => true,
                0x08 => true, 0x09 => true, 0x0A => true, 0x0B => true,
                0x0C => true, 0x0D => true, 0x0E => true, 0x0F => true,
                0x10 => true, 0x11 => true, 0x12 => true, 0x13 => true,
                0x14 => true, 0x15 => true, 0x16 => true, 0x17 => true,
                0x18 => true, 0x19 => true, 0x1A => true, 0x1B => true,
                0x1C => true, 0x1D => true, 0x1E => true, 0x1F => true,
                0x7F => true,
            }
        );

        assert!(ASCII_CONTROL_TABLE[0x00]);
        assert!(ASCII_CONTROL_TABLE[0x09]); // TAB
        assert!(ASCII_CONTROL_TABLE[0x0A]); // LF
        assert!(!ASCII_CONTROL_TABLE[0x41]); // 'A'
    }

    /// 宏生成 const match 分支
    /// const match
    /// 宏Generate const match 分支
    pub fn const_match_arms_demo() {
        /// 将枚举变体映射到编译期字符串的宏
        /// will enum volume to
        macro_rules! define_enum_str {
            (
                $vis:vis enum $name:ident {
                    $($variant:ident),* $(,)?
                }
            ) => {
                #[derive(Debug, Clone, Copy, PartialEq, Eq)]
                $vis enum $name {
                    $($variant,)*
                }

                impl $name {
                    /// 编译期已知的名称映射
                    $vis const fn as_str(&self) -> &'static str {
                        match self {
                            $(
                                Self::$variant => stringify!($variant),
                            )*
                        }
                    }
                }
            };
        }

        define_enum_str! {
            pub enum HttpStatus {
                Ok,
                NotFound,
                ServerError,
            }
        }

        assert_eq!(HttpStatus::Ok.as_str(), "Ok");
        assert_eq!(HttpStatus::NotFound.as_str(), "NotFound");
        assert_eq!(HttpStatus::ServerError.as_str(), "ServerError");
    }

    /// 返回完美哈希函数概念文档
    /// perfect function concept
    pub fn perfect_hash_concept() -> &'static str {
        r#"
# 编译期完美哈希函数

完美哈希函数（Perfect Hash Function）是一种将键集合无碰撞地映射到
整数范围的哈希函数。在编译期构建完美哈希，可以实现 O(1) 的字符串匹配。

## 宏构建完美哈希的步骤
1. 收集所有键（编译期已知）
2. 尝试找到一个哈希参数（如乘法因子）使得无碰撞
3. 生成对应的 match 表达式或查找表

## 限制
- 键集合必须在编译期完全确定
- 哈希参数搜索可能耗时（宏展开阶段）
- 对于大型键集合，可能需要更复杂的算法（如 CHD 算法）
        "#
    }

    /// 展示宏构建的简单完美哈希
    /// simple perfect
    pub fn simple_perfect_hash_demo() {
        /// 为少量编译期已知字符串生成完美哈希的宏
        /// as perfect
        /// （简化版：使用长度+首字符作为哈希）
        /// （：+as ）
        macro_rules! perfect_hash_match {
            (
                $input:expr,
                {
                    $($key:expr => $value:expr),* $(,)?
                }
            ) => {{
                const fn ph_hash(s: &str) -> u32 {
                    let bytes = s.as_bytes();
                    if bytes.is_empty() {
                        return 0;
                    }
                    ((bytes.len() as u32) << 8) | (bytes[0] as u32)
                }

                match ph_hash($input) {
                    $(
                        _ if $input == $key => Some($value),
                    )*
                    _ => None,
                }
            }};
        }

        let result = perfect_hash_match!("GET", {
            "GET" => 1,
            "POST" => 2,
            "PUT" => 3,
            "DELETE" => 4,
        });

        assert_eq!(result, Some(1));
    }
}

/// TT Muncher 模式：递归解析 Token Tree
pub struct TtMuncherPattern;

impl TtMuncherPattern {
    /// 返回 tt muncher 概念文档
    /// tt muncher concept
    pub fn tt_muncher_concept() -> &'static str {
        r#"
# TT Muncher 模式

TT Muncher（Token Tree Muncher）是声明宏中的一种递归处理模式，
宏每次匹配并处理一个 token tree（tt），然后将剩余部分递归传递。

## 核心结构
```rust
macro_rules! my_muncher {
    // 终止条件：没有剩余 token
    () => { ... };

    // 递归条件：吃掉一个 tt，递归处理剩余部分
    ($head:tt $($tail:tt)*) => {
        ... process $head ...
        my_muncher!($($tail)*);
    };
}
```

## 与重复模式 `$(...)*` 的区别
| 特性 | TT Muncher | 重复模式 `$(...)*` |
|------|-----------|-------------------|
| 控制能力 | 高（可逐 token 处理） | 低（批量处理） |
| 递归深度 | 受宏递归限制 | 无递归限制 |
| 适用场景 | 复杂解析、条件处理 | 简单批量生成 |
| 代码复杂度 | 较高 | 较低 |

## 常见用途
- 计数参数
- 构建递归数据结构
- 逐 token 转换
- 条件编译代码生成
        "#
    }

    /// 使用 tt muncher 编译期计数参数
    /// tt muncher parameter
    /// Use tt muncher 编译期计数parameter
    pub fn count_args_demo() {
        macro_rules! count_args {
            // 终止条件
            () => { 0 };
            // 跳过逗号
            (, $($tail:tt)*) => {
                count_args!($($tail)*)
            };
            // 递归：吃掉一个 tt
            ($_head:tt $($tail:tt)*) => {
                1 + count_args!($($tail)*)
            };
        }

        const C0: usize = count_args!();
        const C1: usize = count_args!(a);
        const C3: usize = count_args!(a, b, c);
        const C5: usize = count_args!(1, 2, 3, 4, 5);

        assert_eq!(C0, 0);
        assert_eq!(C1, 1);
        assert_eq!(C3, 3);
        assert_eq!(C5, 5);
    }

    /// 使用 tt muncher 从 token 列表构建元组
    /// tt muncher from token
    /// Use tt muncher from token 列表构建tuple
    pub fn build_tuple_demo() {
        macro_rules! as_tuple {
            // 终止：空元组
            () => { () };
            // 单个元素
            ($single:expr) => { ($single,) };
            // 多个元素：递归构建
            ($first:expr, $($rest:expr),+ $(,)?) => {
                ($first, $($rest),+)
            };
            // tt muncher 变体：逐 token 构建
            ($first:tt $($rest:tt)*) => {
                as_tuple!(@accum ($first) $($rest)*)
            };
            // 内部积累规则
            (@accum ($($acc:expr),*)) => { ($($acc,)* ) };
            (@accum ($($acc:expr),*) $next:tt $($rest:tt)*) => {
                as_tuple!(@accum ($($acc,)* $next) $($rest)*)
            };
        }

        let t1: (i32,) = as_tuple!(42);
        let t2: (i32, i32) = as_tuple!(1, 2);
        let t3: (i32, i32, i32) = as_tuple!(1, 2, 3);

        assert_eq!(t1, (42,));
        assert_eq!(t2, (1, 2));
        assert_eq!(t3, (1, 2, 3));
    }

    /// 返回递归宏模式概念文档
    /// recursive concept
    /// concept
    pub fn recursive_macro_pattern_concept() -> &'static str {
        r#"
# 递归宏模式解析 Token Tree

声明宏的递归能力来源于 `macro_rules!` 可以调用自身。
这种递归与函数递归类似，但必须显式定义终止条件。

## 终止条件设计
终止条件必须覆盖所有"空"或"基础"情况，否则会导致无限递归：
```rust
macro_rules! bad_recursion {
    ($x:tt) => { bad_recursion!($x) }; // 无限递归！
}
```

## 正确模式
```rust
macro_rules! good_recursion {
    () => { 0 };                       // 终止
    ($x:tt) => { 1 };                  // 单元素
    ($x:tt $($rest:tt)*) => {
        1 + good_recursion!($($rest)*)
    };
}
```

## 编译器保护
Rust 编译器对宏递归深度有限制（默认约 128 层），
超过限制会产生 "recursion limit reached" 错误。
可以通过 `#![recursion_limit = "256"]` 调整。
        "#
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ========== ConstMetaprogramming 测试 ==========

    #[test]
    fn test_const_fn_concept() {
        let doc = ConstMetaprogramming::const_fn_concept();
        assert!(doc.contains("const fn"));
        assert!(doc.contains("vs 宏"));
    }

    #[test]
    fn test_array_len_from_const_fn() {
        const LEN: usize = ConstMetaprogramming::array_len_from_const_fn();
        assert_eq!(LEN, 32);
    }

    #[test]
    fn test_const_generics_concept() {
        let doc = ConstMetaprogramming::const_generics_concept();
        assert!(doc.contains("const 泛型"));
    }

    #[test]
    fn test_matrix_dimension_demo() {
        // 运行不 panic 即成功
        ConstMetaprogramming::matrix_dimension_demo();
    }

    #[test]
    fn test_size_of_concept() {
        let doc = ConstMetaprogramming::size_of_concept();
        assert!(doc.contains("size_of"));
    }

    #[test]
    fn test_assert_type_size() {
        // 编译期函数，调用即验证
        ConstMetaprogramming::assert_type_size::<u64>();
    }

    #[test]
    fn test_const_limitations_concept() {
        let doc = ConstMetaprogramming::const_limitations_concept();
        assert!(doc.contains("限制"));
    }

    // ========== MacroAndConstSynergy 测试 ==========

    #[test]
    fn test_macro_generates_const_concept() {
        let doc = MacroAndConstSynergy::macro_generates_const_concept();
        assert!(doc.contains("const"));
    }

    #[test]
    fn test_const_lookup_table_demo() {
        MacroAndConstSynergy::const_lookup_table_demo();
    }

    #[test]
    fn test_const_match_arms_demo() {
        MacroAndConstSynergy::const_match_arms_demo();
    }

    #[test]
    fn test_perfect_hash_concept() {
        let doc = MacroAndConstSynergy::perfect_hash_concept();
        assert!(doc.contains("完美哈希"));
    }

    #[test]
    fn test_simple_perfect_hash_demo() {
        MacroAndConstSynergy::simple_perfect_hash_demo();
    }

    // ========== TtMuncherPattern 测试 ==========

    #[test]
    fn test_tt_muncher_concept() {
        let doc = TtMuncherPattern::tt_muncher_concept();
        assert!(doc.contains("TT Muncher"));
    }

    #[test]
    fn test_count_args_demo() {
        TtMuncherPattern::count_args_demo();
    }

    #[test]
    fn test_build_tuple_demo() {
        TtMuncherPattern::build_tuple_demo();
    }

    #[test]
    fn test_recursive_macro_pattern_concept() {
        let doc = TtMuncherPattern::recursive_macro_pattern_concept();
        assert!(doc.contains("递归"));
    }
}
