# 宏开发最佳实践

> **文档定位**: Rust宏开发的专业实践指南  
> **难度级别**: ⭐⭐ 进阶  
> **预计时间**: 3小时  
> **最后更新**: 2025-10-20

---

## 📋 学习目标

完成本章后,你将能够：

- ✅ 遵循宏开发的最佳实践
- ✅ 编写可维护的宏代码
- ✅ 提供良好的用户体验
- ✅ 避免常见的设计缺陷

---

## 1. 命名约定

### 1.1 宏命名

**✅ 推荐**:

```rust
// 使用小写+下划线，与函数命名一致
macro_rules! create_struct { ... }
macro_rules! impl_trait_for { ... }
macro_rules! generate_tests { ... }

// 对于DSL类宏，可以使用更自然的名称
macro_rules! html { ... }
macro_rules! sql { ... }
```

**❌ 避免**:

```rust
// 避免全大写（除非是常量宏）
macro_rules! CREATE_STRUCT { ... }

// 避免CamelCase（这是类型命名）
macro_rules! CreateStruct { ... }
```

### 1.2 内部规则命名

**✅ 推荐**:

```rust
macro_rules! complex_macro {
    // 使用@前缀标记内部规则
    (@internal_step1 $($tt:tt)*) => { ... };
    (@internal_step2 $($tt:tt)*) => { ... };
    
    // 使用__前缀也可以（但@更常见）
    (__helper $($tt:tt)*) => { ... };
    
    // 公共接口
    ($($input:tt)*) => {
        complex_macro!(@internal_step1 $($input)*)
    };
}
```

---

## 2. 文档编写

### 2.1 宏文档

**✅ 完整的文档示例**:

```rust
/// 为类型自动实现`Display` trait。
///
/// # 示例
///
/// ```
/// use my_crate::impl_display;
///
/// struct User {
///     name: String,
///     age: u32,
/// }
///
/// impl_display!(User, "{} (age: {})", self.name, self.age);
///
/// let user = User { name: "Alice".into(), age: 30 };
/// assert_eq!(format!("{}", user), "Alice (age: 30)");
/// ```
///
/// # 生成的代码
///
/// 该宏会展开为:
/// ```ignore
/// impl std::fmt::Display for User {
///     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
///         write!(f, "{} (age: {})", self.name, self.age)
///     }
/// }
/// ```
///
/// # 限制
///
/// - 格式字符串必须是字面量
/// - 字段访问必须通过`self`
///
/// # 参见
///
/// - [`std::fmt::Display`]
/// - [`format!`]
#[macro_export]
macro_rules! impl_display {
    ($type:ty, $fmt:literal, $($args:expr),*) => {
        impl std::fmt::Display for $type {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, $fmt, $($args),*)
            }
        }
    };
}
```

### 2.2 文档结构

**必需部分**:

1. **简短描述** - 一句话说明宏的作用
2. **示例** - 至少一个完整的使用示例
3. **参数说明** - 每个参数的含义和类型
4. **生成代码** - 展开后的代码示例（可选）
5. **限制** - 已知的限制和约束
6. **参见** - 相关的宏、函数或文档

---

## 3. 错误处理

### 3.1 编译时错误

**✅ 提供清晰的错误信息**:

```rust
macro_rules! validate_input {
    // 正确的输入
    (valid $($tt:tt)*) => { ... };
    
    // 错误的输入：提供帮助信息
    ($($tt:tt)*) => {
        compile_error!(
            "Invalid input to validate_input! macro.\n\
             Expected: validate_input!(valid <expression>)\n\
             Example: validate_input!(valid 42)"
        )
    };
}
```

**✅ 位置特定的错误**:

```rust
macro_rules! check_bounds {
    ($value:expr, $min:expr, $max:expr) => {
        {
            let val = $value;
            let min_val = $min;
            let max_val = $max;
            
            if val < min_val || val > max_val {
                panic!(
                    "Value {} out of bounds [{}, {}] at {}:{}",
                    val, min_val, max_val,
                    file!(), line!()
                );
            }
            val
        }
    };
}
```

### 3.2 友好的错误消息

**✅ 推荐**:

```rust
macro_rules! require_feature {
    ($feature:literal) => {
        #[cfg(not(feature = $feature))]
        compile_error!(
            concat!(
                "This macro requires the '",
                $feature,
                "' feature.\n",
                "Add to Cargo.toml: features = [\"",
                $feature,
                "\"]"
            )
        );
    };
}
```

**❌ 避免**:

```rust
// 错误信息过于简单
compile_error!("Error");

// 没有提供解决方案
compile_error!("Invalid input");
```

---

## 4. 卫生性处理

### 4.1 使用$crate

**✅ 推荐**:

```rust
// 在库crate中定义的宏
#[macro_export]
macro_rules! log_info {
    ($($arg:tt)*) => {
        // 使用$crate引用本crate的模块
        $crate::logging::info(format!($($arg)*))
    };
}
```

### 4.2 避免名称冲突

**✅ 推荐**:

```rust
macro_rules! with_temp_var {
    ($value:expr, $body:expr) => {
        {
            // 使用不太可能冲突的名称
            let __with_temp_var_internal__ = $value;
            $body(__with_temp_var_internal__)
        }
    };
}
```

**❌ 避免**:

```rust
macro_rules! with_temp_var {
    ($value:expr, $body:expr) => {
        {
            // 可能与用户代码冲突
            let temp = $value;
            $body(temp)
        }
    };
}
```

---

## 5. 性能考虑

### 5.1 编译时优化

**✅ 推荐**:

```rust
// 尽量在编译时完成计算
macro_rules! const_max {
    ($a:expr, $b:expr) => {
        {
            const A: usize = $a;
            const B: usize = $b;
            if A > B { A } else { B }
        }
    };
}
```

### 5.2 避免过度展开

**✅ 推荐**:

```rust
// 使用内部规则减少展开层次
macro_rules! repeat_n {
    (@impl $body:expr, 0) => {};
    (@impl $body:expr, $n:expr) => {
        $body;
        repeat_n!(@impl $body, $n - 1);
    };
    
    ($n:expr, $body:expr) => {
        repeat_n!(@impl $body, $n)
    };
}
```

**❌ 避免**:

```rust
// 直接递归可能导致深层展开
macro_rules! repeat_n {
    (0, $body:expr) => {};
    ($n:expr, $body:expr) => {
        $body;
        repeat_n!($n - 1, $body);
    };
}
```

---

## 6. 类型安全

### 6.1 类型约束

**✅ 推荐**:

```rust
macro_rules! swap_values {
    ($a:expr, $b:expr) => {
        {
            // 确保两个值类型相同
            fn type_check<T>(_: &T, _: &T) {}
            type_check(&$a, &$b);
            
            let temp = $a;
            $a = $b;
            $b = temp;
        }
    };
}
```

### 6.2 Trait约束

**✅ 推荐**:

```rust
macro_rules! assert_comparable {
    ($value:expr) => {
        {
            // 确保类型实现了PartialOrd
            fn require_comparable<T: PartialOrd>(_: &T) {}
            require_comparable(&$value);
            $value
        }
    };
}
```

---

## 7. 可维护性

### 7.1 保持简单

**✅ 推荐**:

```rust
// 简单、清晰的宏
macro_rules! unwrap_or_return {
    ($result:expr) => {
        match $result {
            Ok(val) => val,
            Err(e) => return Err(e.into()),
        }
    };
}
```

**❌ 避免**:

```rust
// 过于复杂，难以理解和维护
macro_rules! complex_unwrap {
    (@step1 @step2 @step3 $($tt:tt)*) => { ... };
    (@step1 @step2 $($tt:tt)*) => { ... };
    // ... 更多复杂规则
}
```

### 7.2 分解复杂逻辑

**✅ 推荐**:

```rust
// 将复杂宏分解为多个简单宏
macro_rules! parse_input {
    ($($tt:tt)*) => {
        parse_input!(@validate $($tt)*)
    };
    (@validate $($tt:tt)*) => {
        parse_input!(@process $($tt)*)
    };
    (@process $($tt:tt)*) => {
        parse_input!(@generate $($tt)*)
    };
    (@generate $($tt:tt)*) => { ... };
}
```

---

## 8. 测试策略

### 8.1 单元测试

**✅ 推荐**:

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_usage() {
        let result = my_macro!(input);
        assert_eq!(result, expected);
    }

    #[test]
    fn test_edge_cases() {
        my_macro!();  // 空输入
        my_macro!(single);  // 单个参数
        my_macro!(a, b, c);  // 多个参数
    }

    #[test]
    #[should_panic]
    fn test_invalid_input() {
        my_macro!(invalid syntax);
    }
}
```

### 8.2 展开测试

**✅ 推荐**:

```rust
#[cfg(test)]
mod expansion_tests {
    use super::*;

    macro_rules! assert_expands_to {
        ($input:tt => $expected:tt) => {
            // 使用cargo-expand或macrotest验证展开结果
        };
    }

    #[test]
    fn test_expansion() {
        // 验证宏展开是否符合预期
        assert_expands_to!(
            my_macro!(x) => { let x = 42; }
        );
    }
}
```

---

## 9. 兼容性

### 9.1 版本标注

**✅ 推荐**:

```rust
/// 该宏需要Rust 1.56+（稳定版支持）
///
/// # Edition要求
///
/// 需要Rust 2018 edition或更高版本
///
/// # 特性依赖
///
/// 需要启用`macro_feature`特性
#[cfg(feature = "macro_feature")]
#[macro_export]
macro_rules! advanced_macro {
    // ...
}
```

### 9.2 Edition处理

**✅ 推荐**:

```rust
#[cfg(edition2021)]
macro_rules! edition_specific {
    // 2021 edition特定实现
}

#[cfg(not(edition2021))]
macro_rules! edition_specific {
    // 旧版本兼容实现
}
```

---

## 10. API设计

### 10.1 一致的接口

**✅ 推荐**:

```rust
// 保持API风格一致
macro_rules! create_getter {
    ($name:ident => $field:ident: $ty:ty) => { ... };
}

macro_rules! create_setter {
    ($name:ident => $field:ident: $ty:ty) => { ... };
}

// 用法一致
create_getter!(get_name => name: String);
create_setter!(set_name => name: String);
```

### 10.2 可扩展性

**✅ 推荐**:

```rust
// 支持可选参数和未来扩展
macro_rules! flexible_macro {
    // 必需参数
    ($required:expr) => {
        flexible_macro!($required, {})
    };
    
    // 必需参数 + 可选配置
    ($required:expr, { $($config:tt)* }) => {
        // 实现
    };
}
```

---

## 11. 调试支持

### 11.1 调试模式

**✅ 推荐**:

```rust
macro_rules! debug_trace {
    ($($tt:tt)*) => {
        #[cfg(feature = "macro_debug")]
        {
            eprintln!(
                "[MACRO DEBUG {}:{}:{}] {}",
                file!(),
                line!(),
                column!(),
                stringify!($($tt)*)
            );
        }
    };
}
```

### 11.2 展开可视化

**✅ 推荐**:

```rust
// 提供展开可视化辅助
macro_rules! explain {
    ($macro_call:tt) => {
        {
            #[cfg(feature = "explain_macros")]
            println!("Input: {}", stringify!($macro_call));
            
            let result = $macro_call;
            
            #[cfg(feature = "explain_macros")]
            println!("Output: {}", stringify!(result));
            
            result
        }
    };
}
```

---

## 12. 安全性

### 12.1 避免unsafe

**✅ 推荐**:

```rust
// 尽可能避免生成unsafe代码
macro_rules! safe_access {
    ($array:expr, $index:expr) => {
        $array.get($index).copied()
    };
}
```

**⚠️ 必要时使用unsafe**:

```rust
// 如果必须使用，添加安全注释
macro_rules! unsafe_cast {
    ($value:expr => $ty:ty) => {
        {
            // SAFETY: 调用者必须确保类型转换是安全的
            // 这要求：
            // 1. 源类型和目标类型有相同的内存布局
            // 2. 没有违反目标类型的不变量
            unsafe { std::mem::transmute::<_, $ty>($value) }
        }
    };
}
```

---

## 13. 性能最佳实践

### 13.1 零成本抽象

**✅ 推荐**:

```rust
// 确保宏展开后能被优化器处理
macro_rules! inline_if {
    ($cond:expr, $then:expr, $else:expr) => {
        {
            #[inline(always)]
            fn select<T>(cond: bool, then_val: T, else_val: T) -> T {
                if cond { then_val } else { else_val }
            }
            select($cond, $then, $else)
        }
    };
}
```

### 13.2 编译时间

**✅ 推荐**:

```rust
// 避免过度复杂的递归
#![recursion_limit = "128"]  // 合理设置递归限制

macro_rules! efficient_repeat {
    // 使用迭代而不是深度递归
    ($n:expr, $body:block) => {
        {
            for _ in 0..$n {
                $body
            }
        }
    };
}
```

---

## 14. 实践清单

### ✅ 命名和组织

- [ ] 使用一致的命名约定
- [ ] 内部规则使用@或__前缀
- [ ] 导出的宏使用#[macro_export]
- [ ] 合理组织宏模块

### ✅ 文档

- [ ] 每个公开宏都有文档
- [ ] 包含使用示例
- [ ] 说明限制和注意事项
- [ ] 提供参见链接

### ✅ 错误处理

- [ ] 提供清晰的错误消息
- [ ] 包含解决方案建议
- [ ] 标注错误位置

### ✅ 测试

- [ ] 编写单元测试
- [ ] 测试边界情况
- [ ] 验证宏展开结果
- [ ] 性能测试（如需要）

### ✅ 性能

- [ ] 避免不必要的递归
- [ ] 编译时优化
- [ ] 合理设置递归限制

### ✅ 安全性

- [ ] 避免生成unsafe代码
- [ ] 类型安全检查
- [ ] 卫生性处理

---

## 📚 总结

### 核心原则

1. **清晰优于智能** - 可读性第一
2. **文档完善** - 帮助用户正确使用
3. **错误友好** - 提供有用的错误信息
4. **测试充分** - 确保正确性
5. **性能意识** - 注意编译时间影响

### 下一步

- 📖 学习 [反模式](./03_anti_patterns.md)
- 📖 查看 [真实案例](./04_real_world_examples.md)
- 💻 在项目中应用这些实践

---

**作者**: Rust学习社区  
**最后更新**: 2025-10-20  
**许可**: MIT
