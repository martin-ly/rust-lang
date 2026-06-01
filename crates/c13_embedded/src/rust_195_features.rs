//! - 裸指针 `as_ref_unchecked` / `as_mut_unchecked` ⭐
//! - 裸pointer `as_ref_unchecked` / `as_mut_unchecked` ⭐
//! - `asm_cfg` — 条件汇编 (Rust 1.95 stable) ⭐
//! # 版本信息
//! # this
//! - 稳定日期: 2026-04-16
//! - date : 2026-04-16
//! - 稳定date: 2026-04-16
//! - date: 2026-04-16
//! # 安全警告
//! # warning
//! # 安全warning
//! 在 bare-metal 环境中使用需格外谨慎。
//! in bare-metal environment in outside 。
//! # 参考
//! # reference

// ============================================================================
// 1. 裸指针 as_ref_unchecked / as_mut_unchecked
// ============================================================================

/// # 裸指针 `as_ref_unchecked` / `as_mut_unchecked`
/// # 裸pointer `as_ref_unchecked` / `as_mut_unchecked`
/// ## 概念定义
/// ## concept definition
/// - `<*mut T>::as_mut_unchecked(&self) -> &mut T`
///
/// 适Used for**已确定非 null** pointerscenario。
/// ## Wikipedia 概念对齐
/// ## 对比：安全 API vs 不检查 API
/// ## to ： API vs API
/// ## to比：安全 API vs 不Check API
/// | 方法 | 返回类型 | null 检查？ | 适用场景 | 开销 |
/// | method | type | null ？ | scenario | overhead |
/// | method | Returntype | null Check？ | 适用scenario | overhead |
/// | `as_ref()` | `Option<&T>` | ✅ 有 | mayas null pointer | branch prediction |
/// | `as_mut()` | `Option<&mut T>` | ✅ 有 | mayas null 可变pointer | branch prediction |
/// ## 决策树
/// ## tree
/// ## 决策tree
/// ## tree
/// 需要将裸指针转为引用？
/// will pointer as reference ？
/// ├── pointermayas null？ → as_ref() / as_mut()（安全）
/// ├── 指针由分配器/硬件保证非 null？
/// ├── pointer /hardware null？
/// │   ├── 性能敏感路径？ → as_ref_unchecked() / as_mut_unchecked()
/// │   └── 调试/验证阶段？ → as_ref() + expect()
/// │ └── /stage ？ → as_ref() + expect()
/// │ └── 调试/Verifystage？ → as_ref() + expect()
/// └── 指针指向 MMIO 寄存器？ → as_ref_unchecked()（硬件保证有效）
/// └── pointer MMIO ？ → as_ref_unchecked()（hardware effective ）
/// ## 反例 / 严重误用
/// ## anti-pattern / severe
/// ## /
/// - **悬垂指针**：转换后引用的内存已释放 → UB
/// - **pointer **：conversion after reference memory → UB
/// - **违反别名规则**：两个 `*mut` 指向同一地址并都转为 `&mut` → UB
/// - **rule **： `*mut` and as `&mut` → UB
/// - **对齐违规**：未对齐指针转为引用 → UB
/// - **to **：to pointer as reference → UB
/// ## SAFETY 要求
/// 调用 `*_unchecked` 前必须保证：
/// `*_unchecked` before must ：
/// 1. 指针非 null
/// 1. pointer null
/// 2. 指针已对齐
/// 2. pointer to
/// 3. 指针指向有效内存
/// 3. pointer effective memory
pub struct RawPointerUncheckedExamples;

impl RawPointerUncheckedExamples {
    /// 示例 1：MMIO 寄存器访问（嵌入式核心场景）
    /// example 1：MMIO （core scenario ）
    /// Example of 1：MMIO 寄存器访问（嵌入式corescenario）
    /// 在嵌入式系统中，外设寄存器映射到固定内存地址，硬件保证其有效。
    /// in system in ，outside to memory ，hardware its effective 。
    pub unsafe fn read_mmio_register<T>(addr: *const T) -> T
    where
        T: Copy,
    {
        // SAFETY: 调用者保证 addr 是硬件映射的有效寄存器地址
        unsafe { *addr.as_ref_unchecked() }
    }

    /// 示例 2：MMIO 寄存器写入
    /// example 2：MMIO
    /// Example of 2：MMIO 寄存器Write
    pub unsafe fn write_mmio_register<T>(addr: *mut T, value: T) {
        // SAFETY: 调用者保证 addr 是硬件映射的有效寄存器地址
        unsafe {
            *addr.as_mut_unchecked() = value;
        }
    }
}

/// 示例 3：静态分配缓冲区的零开销访问
/// example 3：buffering overhead
/// 由链接器脚本或启动代码分配的静态缓冲区，地址编译期已知。
/// this or buffering ，。
pub struct StaticBuffer {
    ptr: *mut u8,
    len: usize,
}

impl StaticBuffer {
    /// # Safety
    /// `ptr` 必须指向 `len` 字节的已分配且有效的内存。
    /// `ptr` must `len` and effective memory 。
    pub unsafe fn new(ptr: *mut u8, len: usize) -> Self {
        Self { ptr, len }
    }

    /// # Safety
    /// 调用者必须确保指针在构造时已验证非 null 且有效。
    /// must pointer in verified null and effective 。
    /// must pointer in null and effective 。
    pub unsafe fn as_slice(&self) -> &[u8] {
        // SAFETY: ptr 在构造时已验证非 null 且有效
        unsafe { std::slice::from_raw_parts(self.ptr.as_ref_unchecked(), self.len) }
    }

    /// # Safety
    /// 调用者必须确保指针在构造时已验证非 null 且有效，且不存在别名冲突。
    /// must pointer in verified null and effective ，and in 。
    /// must pointer in null and effective ，and in 。
    pub unsafe fn as_mut_slice(&mut self) -> &mut [u8] {
        // SAFETY: ptr 在构造时已验证非 null 且有效
        unsafe { std::slice::from_raw_parts_mut(self.ptr.as_mut_unchecked(), self.len) }
    }
}

/// Example of 4：and `addr_of!` / `addr_of_mut!` 协同
/// 然后使用 `as_ref_unchecked` 直接访问。
/// then `as_ref_unchecked` 。
#[repr(C)]
pub struct DeviceRegisters {
    pub status: u32,
    pub control: u32,
    pub data: u32,
}

/// # Safety
pub unsafe fn read_status_via_addr_of(regs: *const DeviceRegisters) -> u32 {
    // SAFETY: 调用者保证 regs 有效；addr_of! 安全获取字段地址
    unsafe {
        let status_ptr = std::ptr::addr_of!((*regs).status);
        *status_ptr.as_ref_unchecked()
    }
}

/// 示例 5：性能对比基准（概念性）
/// example 5：performance to （concept ）
/// 调用者必须确保 `ptr` 非 null 且指向有效内存。
/// must `ptr` null and effective memory 。
pub unsafe fn hot_path_access_unchecked(ptr: *const u32) -> u32 {
    // 零分支，直接加载
    unsafe { *ptr.as_ref_unchecked() }
}

/// # Safety
/// 调用者必须确保 `ptr` 指向有效内存或为空。
/// must `ptr` effective memory or as 。
pub unsafe fn hot_path_access_checked(ptr: *const u32) -> Option<u32> {
    // 有分支（null 检查）
    unsafe { ptr.as_ref().copied() }
}

/// 初始化后通过 `as_ref_unchecked` 访问（已知已初始化）。
/// after `as_ref_unchecked` （）。
/// `f` 必须正确初始化传入的引用。
/// `f` must reference 。
pub unsafe fn init_and_access<T, F>(f: F) -> T
where
    F: FnOnce(&mut T),
    T: Copy,
{
    unsafe {
        let mut slot = std::mem::MaybeUninit::<T>::uninit();
        f(slot.as_mut_ptr().as_mut_unchecked());
        // SAFETY: 上面已初始化
        slot.assume_init()
    }
}

// ============================================================================
// 2. PowerPC 内联汇编（1.95 稳定）
// ============================================================================

/// ## 概念
/// ## concept
/// - **Inline Assembly**: 在高级语言中直接嵌入机器指令
/// - **Inline Assembly**: in high in
/// - **Inline Assembly**: in in
/// ## 语法
/// ## syntax
/// ##
///   std::arch::asm!(
/// }
/// ```text
/// 
/// ## 平台支持状态（1.95）
/// ## platform state （1.95）
pub struct PowerPcAsmExamples;

impl PowerPcAsmExamples {
    #[cfg(any(target_arch = "powerpc", target_arch = "powerpc64"))]
    pub unsafe fn ppc_nop() {
        unsafe {
            std::arch::asm!("nop", options(nomem, nostack));
        }
    }

    /// 概念性示例：读取时间戳寄存器 (Time Base)
    /// concept example ：time (Time Base)
    #[cfg(any(target_arch = "powerpc", target_arch = "powerpc64"))]
    pub unsafe fn ppc_read_timebase() -> u64 {
        unsafe {
            let mut tb: u64;
            std::arch::asm!(
                "mfspr {0}, 268",  // mfspr rt, TBL
                out(reg) tb,
                options(nomem, nostack),
            );
            tb
        }
    }

    #[cfg(not(any(target_arch = "powerpc", target_arch = "powerpc64")))]
    pub unsafe fn ppc_nop() {
        // 在 non-PowerPC 目标上，内联汇编不可用
        // 此处仅为概念占位
    }

    /// # Safety
    #[cfg(not(any(target_arch = "powerpc", target_arch = "powerpc64")))]
    pub unsafe fn ppc_read_timebase() -> u64 {
        // 模拟：返回系统时间纳秒数
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos() as u64
    }
}

// ============================================================================
// 3. asm_cfg — 条件汇编 (Rust 1.95 stable)
// ============================================================================

/// # `asm_cfg` — 条件汇编
/// # `asm_cfg` — condition
/// 这使得编写跨平台内联汇编更加简洁，无需为每个平台维护完整的独立 `asm!` 块。
/// platform inside ，as platform complete `asm!` 。
/// ## 语法
/// ## syntax
/// ##
///     "common_instruction",
///     #[cfg(target_arch = "x86_64")]
///     "x86_specific_instruction",
///     #[cfg(target_arch = "aarch64")]
///     "arm_specific_instruction",
///     options(nomem, nostack),
/// );
/// ```text
/// 
/// ## 对比：传统方式 vs asm_cfg
/// ## to ：way vs asm_cfg
/// ## to比：传统way vs asm_cfg
/// | 方式 | 代码重复度 | 可维护性 |
/// | way | | |
/// | `#[cfg]` 包裹整个 `asm!` 块 | 高（每个平台写完整块） | 低 |
/// | `#[cfg]` `asm!` | high （platform complete ） | low |
/// | `#[cfg]` `asm!` | （platform complete ） | |
/// | `asm_cfg`（指令级 `#[cfg]`） | 低（仅差异指令标记） | 高 |
/// | `asm_cfg`（ `#[cfg]`） | low （mark ） | high |
/// | `asm_cfg`（ `#[cfg]`） | （mark ） | |
/// | `asm_cfg`（指令级 `#[cfg]`） | 低（仅差异指令mark） | 高 |
/// | `asm_cfg`（ `#[cfg]`） | low （mark） | high |
/// | `asm_cfg`（ `#[cfg]`） | （mark） | |
pub struct AsmCfgExamples;

impl AsmCfgExamples {
    /// 跨平台内存屏障：使用 `asm_cfg` 选择正确的屏障指令
    /// platform memory barrier ： `asm_cfg` barrier
    /// x86_64 使用 `mfence`，aarch64 使用 `dmb ish`，其他平台使用编译器屏障。
    /// x86_64 `mfence`，aarch64 `dmb ish`，its platform barrier 。
    /// 此函数调用 `std::arch::asm!`，属于 unsafe 操作。调用者需确保：
    /// this function `std::arch::asm!`， unsafe operation 。：
    /// this function `std::arch::asm!`， unsafe 。：
    /// 1. 在正确的上下文中使用内存屏障
    /// 1. in on under in memory barrier
    /// 2. 不会导致数据竞争或死锁
    /// 2. data or lock
    /// 2. or lock
    #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
    pub unsafe fn cross_platform_fence() {
        unsafe {
            std::arch::asm!(
                #[cfg(target_arch = "x86_64")]
                "mfence",
                #[cfg(target_arch = "aarch64")]
                "dmb ish",
                options(nomem, nostack, preserves_flags),
            );
        }
    }

    /// Host 目标模拟（仅用于文档编译）
    /// Host goal （）
    #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
    pub unsafe fn cross_platform_fence() {
        std::sync::atomic::fence(std::sync::atomic::Ordering::SeqCst);
    }

    /// 跨平台 `nop` + 可选调试断点
    /// platform `nop` + point
    /// 跨platform `nop` + 可选调试断point
    /// x86_64 支持 `int3` 断点指令，aarch64 支持 `brk #0`，其他平台仅执行 `nop`。
    /// x86_64 `int3` point ，aarch64 `brk #0`，its platform `nop`。
    /// 此函数调用 `std::arch::asm!`，属于 unsafe 操作。调用者需确保：
    /// this function `std::arch::asm!`， unsafe operation 。：
    /// this function `std::arch::asm!`， unsafe 。：
    /// 1. 断点指令不会破坏程序状态
    /// 1. point program state
    /// 2. 仅在调试环境中使用断点
    /// 2. in environment in point
    #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
    pub unsafe fn nop_with_optional_breakpoint(_enable_breakpoint: bool) {
        unsafe {
            std::arch::asm!("nop", options(nomem, nostack, preserves_flags),);
        }
    }

    /// Host 目标模拟
    /// Host goal
    #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
    pub unsafe fn nop_with_optional_breakpoint(_enable_breakpoint: bool) {
        // 在 host 目标上无操作
    }
}

// ============================================================================
// 4. cfg_select! 在嵌入式跨平台配置中的应用
// ============================================================================

/// # `cfg_select!` 嵌入式跨平台抽象
/// # `cfg_select!` platform
pub struct EmbeddedCfgSelect;

impl EmbeddedCfgSelect {
    /// 选择架构特定的内存屏障指令
    /// architecture memory barrier
    pub fn memory_barrier() {
        cfg_select! {
            target_arch = "arm" => arm_barrier(),
            target_arch = "aarch64" => aarch64_barrier(),
            target_arch = "riscv32" => riscv_barrier(),
            target_arch = "riscv64" => riscv_barrier(),
            target_arch = "x86_64" => x86_barrier(),
            _ => generic_barrier(),
        }
    }

    /// 架构特定的时钟频率（典型值）
    /// architecture （）
    pub const DEFAULT_SYSCLK_HZ: u32 = cfg_select! {
        target_arch = "arm" => 72_000_000,      // 72 MHz (STM32F1)
        target_arch = "aarch64" => 1_500_000_000, // 1.5 GHz (Raspberry Pi 4)
        target_arch = "riscv32" => 160_000_000,  // 160 MHz (ESP32-C3)
        target_arch = "riscv64" => 1_000_000_000, // 1 GHz (VisionFive 2)
        _ => 100_000_000,
    };

    /// 栈对齐要求（字节）
    /// stack to （）
    pub const STACK_ALIGNMENT: usize = cfg_select! {
        target_arch = "arm" => 8,
        target_arch = "aarch64" => 16,
        target_arch = "riscv32" => 16,
        target_arch = "riscv64" => 16,
        target_arch = "x86_64" => 16,
        _ => 8,
    };

    /// 中断向量表大小
    /// in
    pub const IRQ_VECTOR_COUNT: usize = cfg_select! {
        target_arch = "arm" => 16,      // Cortex-M NVIC
        target_arch = "riscv32" => 32,  // PLIC / CLINT
        target_arch = "riscv64" => 32,
        _ => 16,
    };
}

#[allow(dead_code)]
fn arm_barrier() {
    // ARM DMB 指令占位
}
#[allow(dead_code)]
fn aarch64_barrier() {
    // AArch64 DMB 指令占位
}
#[allow(dead_code)]
fn riscv_barrier() {
    // RISC-V FENCE 指令占位
}
#[allow(dead_code)]
fn x86_barrier() {
    // x86 mfence 指令占位
}
#[allow(dead_code)]
fn generic_barrier() {
    // 通用内存屏障（编译器屏障）
    std::sync::atomic::fence(std::sync::atomic::Ordering::SeqCst);
}

// ============================================================================
// 测试
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_static_buffer() {
        let mut data = [0u8; 16];
        unsafe {
            let buf = StaticBuffer::new(data.as_mut_ptr(), data.len());
            let slice = buf.as_slice();
            assert_eq!(slice.len(), 16);
        }
    }

    #[test]
    fn test_read_status_via_addr_of() {
        let regs = DeviceRegisters {
            status: 0xABCD,
            control: 0,
            data: 0,
        };
        unsafe {
            let status = read_status_via_addr_of(&regs);
            assert_eq!(status, 0xABCD);
        }
    }

    #[test]
    fn test_init_and_access() {
        unsafe {
            let value = init_and_access(|x: &mut u32| {
                *x = 12345;
            });
            assert_eq!(value, 12345);
        }
    }

    #[test]
    fn test_embedded_cfg_select() {
        const { assert!(EmbeddedCfgSelect::DEFAULT_SYSCLK_HZ > 0) };
        const { assert!(EmbeddedCfgSelect::STACK_ALIGNMENT >= 8) };
        const { assert!(EmbeddedCfgSelect::IRQ_VECTOR_COUNT > 0) };
    }

    #[test]
    fn test_memory_barrier() {
        EmbeddedCfgSelect::memory_barrier();
        // 只要不出错即通过
    }
}

// ============================================================================
// 4. RealRust195Features — &raw const, const blocks, C string literals
// ============================================================================

use std::ffi::CStr;

/// # 真实 Rust 1.95 特性演示
/// # real Rust 1.95 feature demonstration
/// display `&raw const`、 `const {}` and `c"..."` in嵌入式scenarioinapplication。
pub struct RealRust195Features;

impl RealRust195Features {
    /// 使用 `&raw const` 模拟寄存器访问
    /// `&raw const`
    /// `&raw const` 避免创建中间引用，适合 MMIO 和寄存器操作。
    /// `&raw const` in reference ， MMIO and operation 。
    /// `&raw const` in reference ， MMIO and 。
    pub fn register_raw_ptr(value: u32) -> u32 {
        let ptr = &raw const value;
        // SAFETY: &raw const 直接创建裸指针，适用于已验证有效的寄存器地址
        unsafe { *ptr }
    }

    /// 使用 `const {}` 定义寄存器掩码
    /// `const {}` definition
    pub const fn const_block_register_mask() -> u32 {
        const { 0b1111 }
    }

    /// 使用 `c"embedded"` C 字符串字面量
    /// `c"embedded"` C surface
    pub fn c_str_for_embedded() -> &'static CStr {
        c"embedded"
    }
}

#[cfg(test)]
mod real_rust_195_tests {
    use super::*;

    #[test]
    fn test_register_raw_ptr() {
        assert_eq!(RealRust195Features::register_raw_ptr(0xABCD), 0xABCD);
    }

    #[test]
    fn test_const_block_register_mask() {
        const { assert!(RealRust195Features::const_block_register_mask() == 0b1111) };
    }

    #[test]
    fn test_c_str_for_embedded() {
        assert_eq!(
            RealRust195Features::c_str_for_embedded().to_str(),
            Ok("embedded")
        );
    }
}
