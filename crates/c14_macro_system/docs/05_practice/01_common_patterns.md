# 常用宏模式

> **文档定位**: Rust宏开发中的常见模式和惯用法  
> **难度级别**: ⭐⭐ 进阶  
> **预计时间**: 3小时  
> **最后更新**: 2025-10-20

---

## 📋 学习目标

完成本章后，你将能够：

- ✅ 掌握20+种常用宏模式
- ✅ 识别何时使用特定模式
- ✅ 实现可重用的宏组件
- ✅ 提高宏开发效率

---

## 1. 构建器模式 (Builder Pattern)

### 1.1 基本实现

```rust
macro_rules! builder {
    (
        $(#[$struct_attr:meta])*
        struct $name:ident {
            $(
                $(#[$field_attr:meta])*
                $field:ident: $ty:ty
            ),* $(,)?
        }
    ) => {
        $(#[$struct_attr])*
        pub struct $name {
            $(pub $field: $ty),*
        }

        paste::paste! {
            pub struct [<$name Builder>] {
                $($field: Option<$ty>),*
            }

            impl $name {
                pub fn builder() -> [<$name Builder>] {
                    [<$name Builder>] {
                        $($field: None),*
                    }
                }
            }

            impl [<$name Builder>] {
                $(
                    pub fn $field(mut self, value: $ty) -> Self {
                        self.$field = Some(value);
                        self
                    }
                )*

                pub fn build(self) -> Result<$name, &'static str> {
                    Ok($name {
                        $(
                            $field: self.$field
                                .ok_or(concat!("Field '", stringify!($field), "' not set"))?
                        ),*
                    })
                }
            }
        }
    };
}

// 使用示例
builder! {
    #[derive(Debug, Clone)]
    struct Config {
        host: String,
        port: u16,
        timeout: u64,
    }
}
```

### 1.2 带默认值的构建器

```rust
macro_rules! builder_with_defaults {
    (
        struct $name:ident {
            $(
                $field:ident: $ty:ty = $default:expr
            ),* $(,)?
        }
    ) => {
        pub struct $name {
            $(pub $field: $ty),*
        }

        impl Default for $name {
            fn default() -> Self {
                Self {
                    $($field: $default),*
                }
            }
        }

        impl $name {
            $(
                pub fn $field(mut self, value: $ty) -> Self {
                    self.$field = value;
                    self
                }
            )*
        }
    };
}

// 使用示例
builder_with_defaults! {
    struct ServerConfig {
        host: String = "localhost".to_string(),
        port: u16 = 8080,
        workers: usize = 4,
    }
}
```

---

## 2. 枚举派生模式

### 2.1 字符串转换

```rust
macro_rules! enum_str {
    (
        $(#[$attr:meta])*
        $vis:vis enum $name:ident {
            $(
                $(#[$variant_attr:meta])*
                $variant:ident $(= $str:literal)?
            ),* $(,)?
        }
    ) => {
        $(#[$attr])*
        $vis enum $name {
            $($(#[$variant_attr])* $variant),*
        }

        impl $name {
            pub fn as_str(&self) -> &'static str {
                match self {
                    $(
                        Self::$variant => enum_str!(@str $variant $(, $str)?),
                    )*
                }
            }
        }

        impl std::str::FromStr for $name {
            type Err = String;

            fn from_str(s: &str) -> Result<Self, Self::Err> {
                match s {
                    $(
                        enum_str!(@str $variant $(, $str)?) => Ok(Self::$variant),
                    )*
                    _ => Err(format!("Invalid {} variant: {}", stringify!($name), s))
                }
            }
        }
    };

    (@str $variant:ident, $str:literal) => { $str };
    (@str $variant:ident) => { stringify!($variant) };
}

// 使用示例
enum_str! {
    #[derive(Debug, Clone, Copy, PartialEq)]
    pub enum HttpMethod {
        Get = "GET",
        Post = "POST",
        Put = "PUT",
        Delete = "DELETE",
    }
}
```

### 2.2 迭代器生成

```rust
macro_rules! enum_iterator {
    (
        enum $name:ident {
            $($variant:ident),* $(,)?
        }
    ) => {
        impl $name {
            pub fn all() -> &'static [Self] {
                &[$(Self::$variant),*]
            }

            pub fn iter() -> std::slice::Iter<'static, Self> {
                Self::all().iter()
            }

            pub fn count() -> usize {
                [$( stringify!($variant) ),*].len()
            }
        }
    };
}
```

---

## 3. 错误处理模式

### 3.1 自定义错误类型

```rust
macro_rules! define_error {
    (
        $(#[$attr:meta])*
        $vis:vis enum $name:ident {
            $(
                $(#[$variant_attr:meta])*
                $variant:ident $(( $($field:ty),+ ))? => $msg:literal
            ),* $(,)?
        }
    ) => {
        $(#[$attr])*
        $vis enum $name {
            $(
                $(#[$variant_attr])*
                $variant $(( $($field),+ ))?
            ),*
        }

        impl std::fmt::Display for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                match self {
                    $(
                        Self::$variant $(($(ref $field),+))? => {
                            write!(f, $msg $($(, $field)+)?)
                        }
                    ),*
                }
            }
        }

        impl std::error::Error for $name {}
    };
}

// 使用示例
define_error! {
    #[derive(Debug)]
    pub enum AppError {
        NotFound(String) => "Resource not found: {}",
        InvalidInput(String) => "Invalid input: {}",
        DatabaseError(String) => "Database error: {}",
        Unauthorized => "Unauthorized access",
    }
}
```

### 3.2 Result包装器

```rust
macro_rules! result_ext {
    ($err_type:ty) => {
        pub trait ResultExt<T> {
            fn context(self, msg: &str) -> Result<T, $err_type>;
            fn with_context<F>(self, f: F) -> Result<T, $err_type>
            where
                F: FnOnce() -> String;
        }

        impl<T, E: std::fmt::Display> ResultExt<T> for Result<T, E> {
            fn context(self, msg: &str) -> Result<T, $err_type> {
                self.map_err(|e| format!("{}: {}", msg, e).into())
            }

            fn with_context<F>(self, f: F) -> Result<T, $err_type>
            where
                F: FnOnce() -> String,
            {
                self.map_err(|e| format!("{}: {}", f(), e).into())
            }
        }
    };
}
```

---

## 4. 配置管理模式

### 4.1 环境变量配置

```rust
macro_rules! env_config {
    (
        struct $name:ident {
            $(
                $field:ident: $ty:ty = $env_var:literal $(, default = $default:expr)?
            ),* $(,)?
        }
    ) => {
        pub struct $name {
            $(pub $field: $ty),*
        }

        impl $name {
            pub fn from_env() -> Result<Self, String> {
                Ok(Self {
                    $(
                        $field: env_config!(@parse $ty, $env_var $(, $default)?)?
                    ),*
                })
            }
        }
    };

    (@parse $ty:ty, $env_var:literal, $default:expr) => {
        std::env::var($env_var)
            .ok()
            .and_then(|s| s.parse::<$ty>().ok())
            .unwrap_or($default)
    };

    (@parse $ty:ty, $env_var:literal) => {
        std::env::var($env_var)
            .map_err(|_| format!("Missing environment variable: {}", $env_var))?
            .parse::<$ty>()
            .map_err(|_| format!("Invalid value for {}", $env_var))?
    };
}

// 使用示例
env_config! {
    struct ServerConfig {
        host: String = "HOST", default = "localhost".to_string(),
        port: u16 = "PORT", default = 8080,
        workers: usize = "WORKERS", default = 4,
        database_url: String = "DATABASE_URL",
    }
}
```

---

## 5. 日志和调试模式

### 5.1 条件日志

```rust
macro_rules! log_if {
    ($level:ident, $cond:expr, $($arg:tt)*) => {
        if $cond {
            log::$level!($($arg)*);
        }
    };
}

macro_rules! debug_log {
    ($($arg:tt)*) => {
        #[cfg(debug_assertions)]
        {
            eprintln!("[DEBUG {}:{}] {}", file!(), line!(), format!($($arg)*));
        }
    };
}

macro_rules! trace_fn {
    () => {
        #[cfg(debug_assertions)]
        eprintln!("[TRACE] Entering: {}::{}", module_path!(), 
                 stdext::function_name!());
    };
}
```

### 5.2 性能追踪

```rust
macro_rules! time_it {
    ($name:expr, $body:block) => {
        {
            let start = std::time::Instant::now();
            let result = $body;
            let elapsed = start.elapsed();
            eprintln!("[PERF] {}: {:?}", $name, elapsed);
            result
        }
    };
}

macro_rules! measure {
    ($name:expr => $body:expr) => {
        time_it!($name, { $body })
    };
}
```

---

## 6. 测试辅助模式

### 6.1 测试用例生成

```rust
macro_rules! test_cases {
    (
        fn $test_name:ident($param:ident: $ty:ty) $body:block
        cases {
            $($case_name:ident: $value:expr),* $(,)?
        }
    ) => {
        $(
            #[test]
            fn $case_name() {
                let $param: $ty = $value;
                $body
            }
        )*
    };
}

// 使用示例
test_cases! {
    fn test_is_even(n: i32) {
        assert_eq!(n % 2 == 0, true);
    }
    cases {
        test_zero: 0,
        test_two: 2,
        test_four: 4,
    }
}
```

### 6.2 快照测试

```rust
macro_rules! snapshot {
    ($name:expr, $value:expr) => {
        {
            let snapshot_path = format!("tests/snapshots/{}.snap", $name);
            let value_str = format!("{:#?}", $value);
            
            #[cfg(feature = "update-snapshots")]
            {
                std::fs::write(&snapshot_path, &value_str)
                    .expect("Failed to write snapshot");
            }
            
            #[cfg(not(feature = "update-snapshots"))]
            {
                let expected = std::fs::read_to_string(&snapshot_path)
                    .expect("Failed to read snapshot");
                assert_eq!(value_str, expected, "Snapshot mismatch for {}", $name);
            }
        }
    };
}
```

---

## 7. 序列化模式

### 7.1 简单序列化

```rust
macro_rules! impl_serialize {
    ($struct_name:ident { $($field:ident),* $(,)? }) => {
        impl $struct_name {
            pub fn to_json(&self) -> String {
                format!(
                    "{{{}}}",
                    vec![
                        $(format!("\"{}\": {:?}", stringify!($field), self.$field)),*
                    ].join(", ")
                )
            }
        }
    };
}
```

### 7.2 键值序列化

```rust
macro_rules! to_map {
    ($struct_val:expr => { $($field:ident),* $(,)? }) => {
        {
            let mut map = std::collections::HashMap::new();
            $(
                map.insert(
                    stringify!($field).to_string(),
                    format!("{:?}", $struct_val.$field)
                );
            )*
            map
        }
    };
}
```

---

## 8. 集合操作模式

### 8.1 集合构建

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

macro_rules! hashset {
    ($($value:expr),* $(,)?) => {
        {
            let mut set = std::collections::HashSet::new();
            $(set.insert($value);)*
            set
        }
    };
}
```

### 8.2 集合过滤

```rust
macro_rules! filter_map {
    ($collection:expr, |$item:ident| $pred:expr => $transform:expr) => {
        $collection
            .into_iter()
            .filter(|$item| $pred)
            .map(|$item| $transform)
            .collect()
    };
}
```

---

## 9. 类型转换模式

### 9.1 From/Into实现

```rust
macro_rules! impl_from {
    ($from:ty => $to:ty, |$var:ident| $body:expr) => {
        impl From<$from> for $to {
            fn from($var: $from) -> Self {
                $body
            }
        }
    };
}

// 使用示例
impl_from!(String => UserId, |s| UserId(s));
impl_from!(i32 => Score, |n| Score(n as u32));
```

### 9.2 TryFrom实现

```rust
macro_rules! impl_try_from {
    (
        $from:ty => $to:ty,
        error = $err:ty,
        |$var:ident| $body:expr
    ) => {
        impl std::convert::TryFrom<$from> for $to {
            type Error = $err;

            fn try_from($var: $from) -> Result<Self, Self::Error> {
                $body
            }
        }
    };
}
```

---

## 10. 单例模式

### 10.1 线程安全单例

```rust
macro_rules! singleton {
    (
        $(#[$attr:meta])*
        $vis:vis static $name:ident: $ty:ty = $init:expr;
    ) => {
        $(#[$attr])*
        $vis static $name: once_cell::sync::Lazy<$ty> = 
            once_cell::sync::Lazy::new(|| $init);
    };
}

// 使用示例
singleton! {
    pub static CONFIG: Config = Config::load();
}
```

### 10.2 可变单例

```rust
macro_rules! mutable_singleton {
    (
        $vis:vis static mut $name:ident: $ty:ty = $init:expr;
    ) => {
        $vis static $name: std::sync::RwLock<once_cell::sync::Lazy<$ty>> = 
            std::sync::RwLock::new(once_cell::sync::Lazy::new(|| $init));
    };
}
```

---

## 11. 资源管理模式

### 11.1 RAII守卫

```rust
macro_rules! guard {
    ($name:ident, on_drop => $cleanup:expr) => {
        struct $name;

        impl Drop for $name {
            fn drop(&mut self) {
                $cleanup
            }
        }
    };
}

// 使用示例
guard!(FileGuard, on_drop => {
    println!("Cleaning up file resources");
});
```

### 11.2 作用域守卫

```rust
macro_rules! scoped {
    (setup => $setup:expr, teardown => $teardown:expr, $body:block) => {
        {
            $setup;
            let result = (|| $body)();
            $teardown;
            result
        }
    };
}
```

---

## 12. 状态机模式

### 12.1 简单状态机

```rust
macro_rules! state_machine {
    (
        enum $name:ident {
            $($state:ident),* $(,)?
        }
        
        transitions {
            $($from:ident => $to:ident on $event:ident),* $(,)?
        }
    ) => {
        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        pub enum $name {
            $($state),*
        }

        pub enum Event {
            $($event),*
        }

        impl $name {
            pub fn transition(&self, event: Event) -> Option<Self> {
                match (self, event) {
                    $(
                        (Self::$from, Event::$event) => Some(Self::$to),
                    )*
                    _ => None,
                }
            }
        }
    };
}
```

---

## 13. 链式调用模式

### 13.1 流式接口

```rust
macro_rules! fluent {
    (
        impl $name:ident {
            $(
                fn $method:ident(&mut self, $param:ident: $ty:ty) {
                    $body:expr
                }
            )*
        }
    ) => {
        impl $name {
            $(
                pub fn $method(mut self, $param: $ty) -> Self {
                    $body;
                    self
                }
            )*
        }
    };
}
```

---

## 14. 实践建议

### ✅ 推荐做法

1. **选择合适的模式** - 根据实际需求选择
2. **文档完善** - 为每个宏模式提供文档
3. **测试充分** - 编写测试验证宏行为
4. **保持简单** - 避免过度复杂的模式
5. **代码复用** - 提取通用的宏模式

### ❌ 避免做法

1. **过度使用** - 不是所有场景都需要宏
2. **模式堆砌** - 避免不必要的模式组合
3. **缺少文档** - 必须说明用法和限制
4. **忽略错误** - 提供清晰的错误信息

---

## 📚 总结

### 关键要点

1. **构建器模式** - 优雅地构造复杂对象
2. **错误处理** - 统一的错误定义和处理
3. **配置管理** - 类型安全的配置加载
4. **测试辅助** - 简化测试代码编写
5. **资源管理** - RAII和作用域守卫

### 下一步

- 📖 学习 [最佳实践](./02_best_practices.md)
- 📖 了解 [反模式](./03_anti_patterns.md)
- 💻 在项目中应用这些模式

---

**作者**: Rust学习社区  
**最后更新**: 2025-10-20  
**许可**: MIT
