//! 宏设计模式
//! design
//! 常见的宏设计模式和最佳实践。
//! design and best practice 。
//! design and 。

#[macro_export]
/// 为字段生成 getter 和 setter 方法的宏
/// macro generating getter and setter methods for fields
macro_rules! getter_setter {
    // 为每个字段生成getter和setter
    ($($field:ident: $type:ty),* $(,)?) => {
        $(
            paste::paste! {
                pub fn $field(&self) -> &$type {
                    &self.$field
                }

                pub fn [<set_ $field>](&mut self, value: $type) {
                    self.$field = value;
                }
            }
        )*
    };
}

#[macro_export]
/// 为类型生成 Builder 模式的宏
/// macro generating Builder pattern for a type
macro_rules! builder {
    ($name:ident { $($field:ident: $type:ty),* $(,)? }) => {
        pub struct $name {
            $(
                $field: Option<$type>,
            )*
        }

        impl $name {
            pub fn new() -> Self {
                Self {
                    $(
                        $field: None,
                    )*
                }
            }

            $(
                pub fn $field(mut self, value: $type) -> Self {
                    self.$field = Some(value);
                    self
                }
            )*

            pub fn build(self) -> Result<$name, &'static str> {
                Ok($name {
                    $(
                        $field: self.$field.ok_or(concat!(stringify!($field), " is required"))?,
                    )*
                })
            }
        }
    };
}

#[macro_export]
/// 定义错误枚举和 Display 实现的宏
/// macro defining error enum and Display implementation
macro_rules! define_error {
    (
        $name:ident {
            $(
                $variant:ident => $msg:expr
            ),* $(,)?
        }
    ) => {
        #[derive(Debug)]
        pub enum $name {
            $(
                $variant,
            )*
        }

        impl std::fmt::Display for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                match self {
                    $(
                        Self::$variant => write!(f, $msg),
                    )*
                }
            }
        }

        impl std::error::Error for $name {}
    };
}

#[macro_export]
/// 为新类型模式生成代码的宏
/// macro generating code for newtype pattern
macro_rules! newtype {
    ($name:ident, $type:ty) => {
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
        pub struct $name($type);

        impl $name {
            pub fn new(value: $type) -> Self {
                Self(value)
            }

            pub fn get(&self) -> &$type {
                &self.0
            }

            pub fn into_inner(self) -> $type {
                self.0
            }
        }

        impl From<$type> for $name {
            fn from(value: $type) -> Self {
                Self(value)
            }
        }

        impl From<$name> for $type {
            fn from(value: $name) -> $type {
                value.0
            }
        }
    };
}

/// 静态注册表宏
#[macro_export]
macro_rules! registry {
    ($registry:ident: $type:ty; $($name:ident => $value:expr),* $(,)?) => {
        lazy_static::lazy_static! {
            pub static ref $registry: std::collections::HashMap<&'static str, $type> = {
                let mut m = std::collections::HashMap::new();
                $(
                    m.insert(stringify!($name), $value);
                )*
                m
            };
        }
    };
}

/// 单元测试简化宏
#[macro_export]
macro_rules! test_suite {
    ($name:ident, { $($test_name:ident: $body:block),* $(,)? }) => {
        mod $name {
            $(
                #[test]
                fn $test_name() {
                    $body
                }
            )*
        }
    };
}

#[cfg(test)]
mod tests {
    // 测试newtype宏
    newtype!(UserId, u64);

    #[test]
    fn test_newtype() {
        let id = UserId::new(42);
        assert_eq!(*id.get(), 42);
    }

    // 测试define_error宏
    define_error!(MyError {
        NotFound => "Resource not found",
        Timeout => "Operation timed out",
    });

    #[test]
    fn test_error_macro() {
        let err = MyError::NotFound;
        assert_eq!(err.to_string(), "Resource not found");

        // 使用 Timeout 变体来避免 dead_code 警告
        let timeout = MyError::Timeout;
        assert_eq!(timeout.to_string(), "Operation timed out");
    }
}
