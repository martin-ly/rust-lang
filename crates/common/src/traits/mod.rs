//! 公共 trait 定义模块
//! 
//! 定义跨 crate 共享的核心 trait，用于统一接口和行为。

/// 可验证 trait
/// 
/// 用于需要验证自身状态或内容的类型
pub trait Validatable {
    /// 错误类型
    type Error;
    
    /// 验证自身
    fn validate(&self) -> Result<(), Self::Error>;
    
    /// 验证并返回自身（用于链式调用）
    fn validated(self) -> Result<Self, Self::Error>
    where
        Self: Sized,
    {
        self.validate()?;
        Ok(self)
    }
}

/// 可序列化 ID trait
/// 
/// 用于具有唯一标识符的类型
pub trait Identifiable {
    /// ID 类型
    type Id: Clone + std::fmt::Display + std::fmt::Debug;
    
    /// 获取 ID
    fn id(&self) -> &Self::Id;
}

/// 可度量 trait
/// 
/// 用于可以计算大小的类型
pub trait Measurable {
    /// 获取大小（字节）
    fn size_bytes(&self) -> usize;
    
    /// 是否为空
    fn is_empty(&self) -> bool {
        self.size_bytes() == 0
    }
}

/// 可重置 trait
/// 
/// 用于可以重置为初始状态的类型
pub trait Resettable {
    /// 重置为初始状态
    fn reset(&mut self);
}

/// 可命名 trait
/// 
/// 用于具有名称的类型
pub trait Named {
    /// 获取名称
    fn name(&self) -> &str;
    
    /// 设置名称
    fn set_name(&mut self, name: impl Into<String>);
}

/// 可描述 trait
/// 
/// 用于具有描述的类型
pub trait Describable {
    /// 获取描述
    fn description(&self) -> &str;
    
    /// 设置描述
    fn set_description(&mut self, description: impl Into<String>);
}

/// 构建器 trait
/// 
/// 用于实现构建者模式
pub trait Builder: Sized {
    /// 构建的目标类型
    type Output;
    /// 错误类型
    type Error;
    
    /// 构建实例
    fn build(self) -> Result<Self::Output, Self::Error>;
}

/// 转换 trait
/// 
/// 用于类型之间的转换
pub trait Convertible<T>: Sized {
    /// 转换为目标类型
    fn convert(&self) -> T;
    
    /// 尝试转换
    fn try_convert(&self) -> Option<T>;
}

/// 可克隆配置 trait
/// 
/// 用于可以克隆并修改配置的类型
pub trait CloneableConfig: Clone {
    /// 获取配置副本
    fn clone_config(&self) -> Self {
        self.clone()
    }
}

/// 资源管理 trait
/// 
/// 用于需要显式资源管理的类型
pub trait ManagedResource {
    /// 检查资源是否已释放
    fn is_released(&self) -> bool;
    
    /// 释放资源
    fn release(&mut self) -> Result<(), crate::RustLangError>;
}

/// 生命周期管理 trait
/// 
/// 用于具有生命周期的类型
pub trait Lifecycle {
    /// 初始化
    fn initialize(&mut self) -> Result<(), crate::RustLangError>;
    
    /// 启动
    fn start(&mut self) -> Result<(), crate::RustLangError>;
    
    /// 停止
    fn stop(&mut self) -> Result<(), crate::RustLangError>;
    
    /// 检查是否运行中
    fn is_running(&self) -> bool;
}

#[cfg(feature = "async")]
mod async_traits {
    use std::future::Future;
    use std::pin::Pin;
    
    /// 异步可验证 trait
    pub trait AsyncValidatable {
        type Error;
        
        fn validate_async(&self) -> Pin<Box<dyn Future<Output = Result<(), Self::Error>> + Send + '_>>;
    }
    
    /// 异步生命周期管理 trait
    pub trait AsyncLifecycle {
        fn initialize_async(&mut self) -> Pin<Box<dyn Future<Output = Result<(), crate::RustLangError>> + Send + '_>>;
        fn start_async(&mut self) -> Pin<Box<dyn Future<Output = Result<(), crate::RustLangError>> + Send + '_>>;
        fn stop_async(&mut self) -> Pin<Box<dyn Future<Output = Result<(), crate::RustLangError>> + Send + '_>>;
    }
}

#[cfg(feature = "async")]
pub use async_traits::*;

#[cfg(test)]
mod tests {
    use super::*;
    
    #[derive(Debug, Clone)]
    struct TestItem {
        id: String,
        value: i32,
    }
    
    impl Identifiable for TestItem {
        type Id = String;
        
        fn id(&self) -> &Self::Id {
            &self.id
        }
    }
    
    impl Measurable for TestItem {
        fn size_bytes(&self) -> usize {
            std::mem::size_of::<Self>() + self.id.len()
        }
    }
    
    use super::{Identifiable, Measurable};
    
    #[test]
    fn test_identifiable() {
        let item = TestItem {
            id: "test-123".to_string(),
            value: 42,
        };
        assert_eq!(item.id(), "test-123");
    }
    
    #[test]
    fn test_measurable() {
        let item = TestItem {
            id: "test".to_string(),
            value: 42,
        };
        assert!(item.size_bytes() > 0);
        assert!(!item.is_empty());
    }
}
