//! 型变（variance）：协变、逆变、不变。
//!
//! 型变描述泛型构造器如何保持或反转子类型关系：
//!
//! - **协变**：`&T`、`Box<T>`、`Option<T>` 等保持子类型关系。
//! - **逆变**：函数参数位置会反转子类型关系。
//! - **不变**：内部可变性容器（`Cell<T>`、`RefCell<T>`、`*mut T`）不接受任何子类型化。
//!
//! 正确理解型变对生命周期、API 设计与 unsafe 抽象至关重要。

pub mod contravariance;
pub mod covariance;
pub mod invariance;
