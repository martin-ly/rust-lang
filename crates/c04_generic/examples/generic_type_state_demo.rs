//! 类型状态模式（Type State Pattern）示例
//!
//! 本示例展示如何使用Rust的类型系统实现类型状态模式：
//! - 使用类型参数表示状态
//! - 状态转换的类型安全保证
//! - 编译时状态验证
//!
//! 运行方式:
//! ```bash
//! cargo run --example generic_type_state_demo
//! ```

/// 未初始化状态标记
pub struct Uninitialized;

/// 已初始化状态标记
pub struct Initialized;

/// 运行中状态标记
pub struct Running;

/// 已停止状态标记
pub struct Stopped;

/// 使用类型状态的状态机
pub struct StateMachine<S> {
    state: std::marker::PhantomData<S>,
    value: Option<i32>,
}

impl StateMachine<Uninitialized> {
    /// 创建未初始化的状态机
    pub fn new() -> Self {
        Self {
            state: std::marker::PhantomData,
            value: None,
        }
    }

    /// 初始化状态机
    pub fn initialize(self, value: i32) -> StateMachine<Initialized> {
        StateMachine {
            state: std::marker::PhantomData,
            value: Some(value),
        }
    }
}

impl StateMachine<Initialized> {
    /// 获取值（只能在已初始化状态下调用）
    pub fn get_value(&self) -> i32 {
        self.value.unwrap()
    }

    /// 启动状态机
    pub fn start(self) -> StateMachine<Running> {
        StateMachine {
            state: std::marker::PhantomData,
            value: self.value,
        }
    }
}

impl StateMachine<Running> {
    /// 获取值（运行中状态）
    pub fn get_value(&self) -> i32 {
        self.value.unwrap()
    }

    /// 停止状态机
    pub fn stop(self) -> StateMachine<Stopped> {
        StateMachine {
            state: std::marker::PhantomData,
            value: self.value,
        }
    }
}

impl StateMachine<Stopped> {
    /// 获取值（已停止状态）
    pub fn get_value(&self) -> i32 {
        self.value.unwrap()
    }

    /// 重置状态机
    pub fn reset(self) -> StateMachine<Uninitialized> {
        StateMachine {
            state: std::marker::PhantomData,
            value: None,
        }
    }
}

fn main() {
    println!("🚀 类型状态模式示例\n");
    println!("{}", "=".repeat(60));

    // 1. 创建未初始化的状态机
    println!("\n📊 状态转换示例:");
    println!("{}", "-".repeat(60));

    let machine = StateMachine::new();
    println!("✅ 创建未初始化状态机");

    // 2. 初始化
    let machine = machine.initialize(42);
    println!("✅ 初始化状态机，值: {}", machine.get_value());

    // 3. 启动
    let machine = machine.start();
    println!("✅ 启动状态机，值: {}", machine.get_value());

    // 4. 停止
    let machine = machine.stop();
    println!("✅ 停止状态机，值: {}", machine.get_value());

    // 5. 重置
    let _machine = machine.reset();
    println!("✅ 重置状态机");

    // 编译时检查：以下代码会编译错误
    // let machine = StateMachine::new();
    // machine.get_value(); // ❌ 编译错误：Uninitialized状态没有get_value方法
    // let machine = machine.initialize(42);
    // machine.start(); // ❌ 编译错误：必须先start再stop

    println!("\n💡 类型状态模式的优势:");
    println!("{}", "-".repeat(60));
    println!("  ✅ 编译时状态验证");
    println!("  ✅ 防止无效状态转换");
    println!("  ✅ 类型安全的状态管理");
    println!("  ✅ 零运行时开销");

    println!("\n✅ 演示完成！");
}
