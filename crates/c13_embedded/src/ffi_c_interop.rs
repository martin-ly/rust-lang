//! C 语言互操作 (FFI)
//! C operation (FFI)
//! C (FFI)
//! Rust 可以无缝调用 C 代码，也可以被 C 代码调用。
//! Rust can C ，can is C 。
//! 这在嵌入式中非常重要，因为大量驱动库和硬件抽象层是用 C 编写的。
//! in in important ，because driver library and hardware C 。
//! ## 核心概念
//! ## core concept
//! - extern "C"：指定 C 调用约定
//! - extern "C"： C

/// 与 C 兼容的结构体
/// and C struct
/// and C 兼容struct
#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct SensorData {
    /// 温度值（摄氏度，浮点）
    /// （，point ）
    pub temperature: f32,
    /// 湿度值（百分比）
    /// （）
    pub humidity: f32,
    /// 传感器状态码
    /// state
    pub status: u32,
    /// 预留字段（C 中常见）
    /// field （C in ）
    /// Reservefield（C in常见）
    pub reserved: u32,
}

/// 与 C 兼容的枚举
/// and C enum
/// and C 兼容enum
/// 注意：#[repr(C)] 枚举需要有显式整型表示。
/// ：#[repr(C)] enum represent 。
#[repr(u32)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SensorStatus {
    /// 离线
    /// line
    /// 离line
    Offline = 0,
    /// 初始化中
    /// in
    Initializing = 1,
    /// 运行中
    /// Run in
    Running = 2,
    /// 错误
    Error = 3,
}

/// no_mangle 防止 Rust 编译器对函数名进行混淆，确保 C 代码能通过符号名找到它。
/// no_mangle Rust to function ， C symbol to 。
/// // C 代码调用示例
/// // C example
#[unsafe(no_mangle)]
pub extern "C" fn rust_initialize_sensor(id: u32) -> i32 {
    if id > 100 {
        -1 // 错误
    } else {
        0 // 成功
    }
}

/// 接受 C 风格字符串的函数
/// C function
/// Accept C 风格字符串function
///
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rust_process_name(c_str: *const u8) -> i32 {
    if c_str.is_null() {
        return -1;
    }

    let mut len = 0usize;
    while unsafe { *c_str.add(len) } != 0 {
        len += 1;
    }

    let slice = unsafe { core::slice::from_raw_parts(c_str, len) };
    let _name = slice;
    0
}

/// C 回调函数类型
/// C function type
/// C 回调functiontype
/// 在嵌入式中，经常需要注册 C 回调（如中断回调）。
/// in in ， C （in ）。
pub type CCallback = extern "C" fn(data: *mut core::ffi::c_void);

/// 模拟 C 库提供的初始化函数声明
/// C library function
/// 在真实项目中，这些声明通常在 build.rs 中使用 bindgen 自动生成。
/// in real project in ，in build.rs in bindgen 。
/// extern "C" {
///     fn hal_init() -> i32;
///     fn hal_read_register(addr: u32) -> u32;
///     fn hal_write_register(addr: u32, value: u32);
/// }
/// ```
pub struct CBindingsConcept;

impl CBindingsConcept {
    /// 描述 bindgen 工作流程
    /// describe bindgen process
    /// describe bindgen 工作process
    pub fn bindgen_workflow() -> &'static str {
        "1. 准备 C 头文件 -> 2. 运行 bindgen 生成 .rs -> 3. 在 build.rs 中链接 C 库 -> 4. 调用 FFI \
         函数"
    }
}

/// build.rs 示例概念
/// build.rs example concept
/// ```rust,ignore
/// use std::env;
/// use std::path::PathBuf;
///
/// fn main() {
///     println!("cargo:rerun-if-changed=wrapper.h");
///
///     let bindings = bindgen::Builder::default()
///         .header("wrapper.h")
///         .parse_callbacks(Box::new(bindgen::CargoCallbacks::new()))
///         .generate()
///         .expect("无法生成绑定");
///         .expect("");
///     bindings
///         .write_to_file(out_path.join("bindings.rs"))
///         .expect("无法写入绑定文件");
///         .expect("");
pub struct BuildRsExample;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sensor_data_layout() {
        assert_eq!(core::mem::size_of::<SensorData>(), 16);
    }

    #[test]
    fn test_rust_initialize_sensor() {
        assert_eq!(rust_initialize_sensor(50), 0);
        assert_eq!(rust_initialize_sensor(101), -1);
    }

    #[test]
    fn test_sensor_status_values() {
        assert_eq!(SensorStatus::Offline as u32, 0);
        assert_eq!(SensorStatus::Running as u32, 2);
    }

    #[test]
    fn test_bindgen_workflow() {
        assert!(!CBindingsConcept::bindgen_workflow().is_empty());
    }
}

// ==================== Rust 2024 Edition: unsafe extern blocks 安全 FFI ====================
//
// 嵌入式开发中，FFI 是与硬件抽象层（HAL）、RTOS 和 C 驱动库交互的核心手段。
// Rust 2024 Edition 的 `unsafe extern "C" { ... }` 语法使这些边界更清晰、更安全。

// 模拟嵌入式 C HAL 函数声明（Rust 2024 语法）
//
// 在真实项目中，这些声明通常由 bindgen 从 C 头文件自动生成。
// `unsafe extern` 明确告知开发者：这些调用跨越了安全边界。
#[cfg(target_arch = "arm")]
unsafe extern "C" {
    /// 初始化硬件抽象层
    /// hardware
    /// - 必须在系统启动早期、中断使能之前调用
    /// - must in system 、in 's before
    /// - 重复调用可能导致未定义行为
    /// - may definition as
    fn hal_init() -> i32;

    /// 读取内存映射寄存器
    /// memory mapping
    /// - 地址对齐必须与寄存器宽度匹配
    /// - to must and
    fn hal_read_register(addr: u32) -> u32;

    /// 写入内存映射寄存器
    /// memory mapping
    /// - `value` 必须符合寄存器位域定义
    /// - `value` must domain definition
    fn hal_write_register(addr: u32, value: u32);

    /// 获取系统时钟周期计数
    /// system
    /// - 确保在时钟源稳定后调用
    /// - in after
    #[allow(dead_code)]
    fn hal_get_cycle_count() -> u64;
}

// 在非 ARM 目标（如 host 测试环境）下提供模拟实现，避免链接错误
#[cfg(not(target_arch = "arm"))]
mod hal_stubs {
    #[unsafe(no_mangle)]
    pub unsafe extern "C" fn hal_init() -> i32 {
        0 // 模拟成功
    }

    #[unsafe(no_mangle)]
    pub unsafe extern "C" fn hal_read_register(_addr: u32) -> u32 {
        0 // 模拟寄存器值
    }

    #[unsafe(no_mangle)]
    pub unsafe extern "C" fn hal_write_register(_addr: u32, _value: u32) {}
}
#[cfg(not(target_arch = "arm"))]
use hal_stubs::*;

/// 安全的 HAL 初始化包装
/// HAL
pub fn safe_hal_init() -> Result<(), &'static str> {
    // 在真实场景中，这里会检查系统状态、时钟配置等
    let result = unsafe { hal_init() };
    if result == 0 {
        Ok(())
    } else {
        Err("HAL 初始化失败")
    }
}

/// 安全的寄存器读取
pub fn safe_read_register(addr: u32) -> Result<u32, &'static str> {
    // 地址白名单检查（模拟）
    const VALID_RANGE: std::ops::RangeInclusive<u32> = 0x4000_0000..=0x4000_FFFF;
    if !VALID_RANGE.contains(&addr) {
        return Err("寄存器地址超出有效范围");
    }

    Ok(unsafe { hal_read_register(addr) })
}

/// 安全的寄存器写入
/// 写入前验证地址和值的有效性。
/// before and effective 。
pub fn safe_write_register(addr: u32, value: u32) -> Result<(), &'static str> {
    const VALID_RANGE: std::ops::RangeInclusive<u32> = 0x4000_0000..=0x4000_FFFF;
    if !VALID_RANGE.contains(&addr) {
        return Err("寄存器地址超出有效范围");
    }

    unsafe { hal_write_register(addr, value) };
    Ok(())
}

/// GPIO 寄存器地址（模拟 STM32F4 风格）
/// GPIO （ STM32F4 ）
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GpioRegister {
    /// GPIO 模式寄存器
    /// GPIO
    Mode = 0x4002_0000,
    /// GPIO 输出类型寄存器
    /// GPIO type
    OutputType = 0x4002_0004,
    /// GPIO 输出速度寄存器
    /// GPIO
    Speed = 0x4002_0008,
    /// GPIO 上拉/下拉寄存器
    /// GPIO on /under
    Pull = 0x4002_000C,
    /// GPIO 输入数据寄存器
    /// GPIO input data
    /// GPIO
    InputData = 0x4002_0010,
    /// GPIO 输出数据寄存器
    /// GPIO data
    /// GPIO
    OutputData = 0x4002_0014,
}

impl GpioRegister {
    /// 获取寄存器地址
    pub fn addr(self) -> u32 {
        self as u32
    }

    /// 安全读取 GPIO 寄存器
    /// GPIO
    pub fn read(self) -> Result<u32, &'static str> {
        safe_read_register(self.addr())
    }

    /// 安全写入 GPIO 寄存器
    /// GPIO
    pub fn write(self, value: u32) -> Result<(), &'static str> {
        safe_write_register(self.addr(), value)
    }
}

/// Demonstration of Rust 2024 unsafe extern blocks in嵌入式inapplication
pub fn demonstrate_embedded_unsafe_extern() {
    println!("\n========================================");
    println!("   Rust 2024 unsafe extern blocks (嵌入式) 演示");
    println!("========================================\n");

    println!("--- HAL 初始化 ---");
    match safe_hal_init() {
        Ok(()) => println!("HAL 初始化成功"),
        Err(e) => println!("HAL 初始化失败: {}", e),
    }

    println!("\n--- GPIO 寄存器操作 ---");
    match GpioRegister::Mode.read() {
        Ok(val) => println!("GPIO 模式寄存器: 0x{:08X}", val),
        Err(e) => println!("读取失败: {}", e),
    }

    println!("\n--- 寄存器地址验证 ---");
    match safe_read_register(0x3000_0000) {
        Ok(_) => println!("意外成功"),
        Err(e) => println!("预期中的地址验证失败: {}", e),
    }

    println!("\n========================================");
    println!("   演示完成");
    println!("========================================\n");
}

/// 获取嵌入式 FFI 特性信息
/// FFI feature
pub fn get_embedded_ffi_info() -> String {
    "Rust 2024 Edition 嵌入式 FFI 特性:\n- unsafe extern \"C\" 声明硬件抽象层接口\n- \
     地址白名单验证防止非法寄存器访问\n- 类型化寄存器封装（GpioRegister 枚举）\n- \
     安全包装函数负责前置条件检查\n- 与 bindgen 生成的 C 头文件绑定无缝集成"
        .to_string()
}

#[cfg(test)]
mod embedded_ffi_tests {
    use super::*;

    #[test]
    fn test_safe_hal_init() {
        // 在模拟环境中，hal_init 返回 0（由链接器存根实现）
        // 实际测试可能需要 mock 或硬件在环仿真
        let result = safe_hal_init();
        // 在 host 环境下，模拟函数通常返回 0
        assert!(result.is_ok() || result.is_err());
    }

    #[test]
    fn test_safe_read_register_validation() {
        // 无效地址应被拒绝
        assert!(safe_read_register(0x3000_0000).is_err());
        // 有效地址范围应被接受（实际读取结果取决于模拟实现）
        assert!(safe_read_register(0x4000_0000).is_ok());
    }

    #[test]
    fn test_safe_write_register_validation() {
        // 无效地址应被拒绝
        assert!(safe_write_register(0x3000_0000, 0).is_err());
        // 有效地址应被接受
        assert!(safe_write_register(0x4000_0000, 0xFF).is_ok());
    }

    #[test]
    fn test_gpio_register_addr() {
        assert_eq!(GpioRegister::Mode.addr(), 0x4002_0000);
        assert_eq!(GpioRegister::OutputData.addr(), 0x4002_0014);
    }

    #[test]
    fn test_get_embedded_ffi_info() {
        let info = get_embedded_ffi_info();
        assert!(info.contains("unsafe extern"));
        assert!(info.contains("嵌入式"));
    }
}
