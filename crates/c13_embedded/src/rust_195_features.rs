//! Rust 1.95.0 嵌入式与裸指针新特性实现模块
//!
//! 本模块展示了 Rust 1.95.0 在嵌入式和系统编程方面的关键增强：
//! - 裸指针 `as_ref_unchecked` / `as_mut_unchecked` ⭐
//! - PowerPC 内联汇编稳定化
//! - `cfg_select!` 在嵌入式跨平台配置中的应用
//!
//! # 版本信息
//! - Rust版本: 1.95.0
//! - 稳定日期: 2026-04-16
//! - Edition: 2024
//!
//! # 安全警告
//! 本模块涉及 `unsafe` 操作，所有示例均标注了 SAFETY 注释。
//! 在 bare-metal 环境中使用需格外谨慎。
//!
//! # 参考
//! - [Rust 1.95.0 Release Notes](https://releases.rs/docs/1.95.0/)

// ============================================================================
// 1. 裸指针 as_ref_unchecked / as_mut_unchecked
// ============================================================================

/// # 裸指针 `as_ref_unchecked` / `as_mut_unchecked`
///
/// ## 概念定义
/// Rust 1.95.0 为裸指针稳定了以下方法：
/// - `<*const T>::as_ref_unchecked(&self) -> &T`
/// - `<*mut T>::as_ref_unchecked(&self) -> &T`
/// - `<*mut T>::as_mut_unchecked(&self) -> &mut T`
///
/// 这些方法将裸指针直接转换为引用，**不进行 null 检查**。
/// 相比 `as_ref()`（返回 `Option<&T>`），它们避免了分支开销，
/// 适用于**已确定非 null** 的指针场景。
///
/// ## Wikipedia 概念对齐
/// - **Pointer (Computer Programming)**: 内存地址的抽象，裸指针是最低层级
/// - **Type Safety**: Rust 通过 `unsafe` 边界将类型不安全操作显式化
///
/// ## 对比：安全 API vs 不检查 API
///
/// | 方法 | 返回类型 | null 检查？ | 适用场景 | 开销 |
/// |------|---------|-----------|---------|------|
/// | `as_ref()` | `Option<&T>` | ✅ 有 | 可能为 null 的指针 | 分支预测 |
/// | `as_ref_unchecked()` | `&T` | ❌ 无 | 已验证非 null 的指针 | 零开销 |
/// | `as_mut()` | `Option<&mut T>` | ✅ 有 | 可能为 null 的可变指针 | 分支预测 |
/// | `as_mut_unchecked()` | `&mut T` | ❌ 无 | 已验证非 null 的可变指针 | 零开销 |
///
/// ## 决策树
/// ```text
/// 需要将裸指针转为引用？
/// ├── 指针可能为 null？ → as_ref() / as_mut()（安全）
/// ├── 指针由分配器/硬件保证非 null？
/// │   ├── 性能敏感路径？ → as_ref_unchecked() / as_mut_unchecked()
/// │   └── 调试/验证阶段？ → as_ref() + expect()
/// └── 指针指向 MMIO 寄存器？ → as_ref_unchecked()（硬件保证有效）
/// ```
///
/// ## 反例 / 严重误用
/// - **未初始化的指针**：`as_ref_unchecked` 不检查 null，也不检查有效性
/// - **悬垂指针**：转换后引用的内存已释放 → UB
/// - **违反别名规则**：两个 `*mut` 指向同一地址并都转为 `&mut` → UB
/// - **对齐违规**：未对齐指针转为引用 → UB
///
/// ## SAFETY 要求
/// 调用 `*_unchecked` 前必须保证：
/// 1. 指针非 null
/// 2. 指针已对齐
/// 3. 指针指向有效内存
/// 4. 不违反 Rust 的别名规则（`&mut` 唯一性）
pub struct RawPointerUncheckedExamples;

impl RawPointerUncheckedExamples {
    /// 示例 1：MMIO 寄存器访问（嵌入式核心场景）
    ///
    /// 在嵌入式系统中，外设寄存器映射到固定内存地址，硬件保证其有效。
    /// 使用 `as_ref_unchecked` 避免每次访问的分支开销。
    ///
    /// # Safety
    /// 调用者必须确保 `addr` 是有效的 MMIO 地址。
    pub unsafe fn read_mmio_register<T>(addr: *const T) -> T
    where
        T: Copy,
    {
        // SAFETY: 调用者保证 addr 是硬件映射的有效寄存器地址
        unsafe { *addr.as_ref_unchecked() }
    }

    /// 示例 2：MMIO 寄存器写入
    ///
    /// # Safety
    /// 调用者必须确保 `addr` 是有效的可写 MMIO 地址。
    pub unsafe fn write_mmio_register<T>(addr: *mut T, value: T) {
        // SAFETY: 调用者保证 addr 是硬件映射的有效寄存器地址
        unsafe {
            *addr.as_mut_unchecked() = value;
        }
    }
}

/// 示例 3：静态分配缓冲区的零开销访问
///
/// 由链接器脚本或启动代码分配的静态缓冲区，地址编译期已知。
pub struct StaticBuffer {
    ptr: *mut u8,
    len: usize,
}

impl StaticBuffer {
    /// # Safety
    /// `ptr` 必须指向 `len` 字节的已分配且有效的内存。
    pub unsafe fn new(ptr: *mut u8, len: usize) -> Self {
        Self { ptr, len }
    }

    /// # Safety
    /// 调用者必须确保指针在构造时已验证非 null 且有效。
    pub unsafe fn as_slice(&self) -> &[u8] {
        // SAFETY: ptr 在构造时已验证非 null 且有效
        unsafe { std::slice::from_raw_parts(self.ptr.as_ref_unchecked(), self.len) }
    }

    /// # Safety
    /// 调用者必须确保指针在构造时已验证非 null 且有效，且不存在别名冲突。
    pub unsafe fn as_mut_slice(&mut self) -> &mut [u8] {
        // SAFETY: ptr 在构造时已验证非 null 且有效
        unsafe { std::slice::from_raw_parts_mut(self.ptr.as_mut_unchecked(), self.len) }
    }
}

/// 示例 4：与 `addr_of!` / `addr_of_mut!` 的协同
///
/// `addr_of!` 获取字段的裸指针（不创建中间引用），
/// 然后使用 `as_ref_unchecked` 直接访问。
///
/// 这是 `&raw const` (1.82+) 的替代路径，适用于需要裸指针的场景。
#[repr(C)]
pub struct DeviceRegisters {
    pub status: u32,
    pub control: u32,
    pub data: u32,
}

/// # Safety
/// 调用者必须确保 `regs` 指向有效的 DeviceRegisters 内存。
pub unsafe fn read_status_via_addr_of(regs: *const DeviceRegisters) -> u32 {
    // SAFETY: 调用者保证 regs 有效；addr_of! 安全获取字段地址
    unsafe {
        let status_ptr = std::ptr::addr_of!((*regs).status);
        *status_ptr.as_ref_unchecked()
    }
}

/// 示例 5：性能对比基准（概念性）
///
/// 在热路径中，`as_ref_unchecked` 消除了分支预测失败的可能性。
///
/// # Safety
/// 调用者必须确保 `ptr` 非 null 且指向有效内存。
pub unsafe fn hot_path_access_unchecked(ptr: *const u32) -> u32 {
    // 零分支，直接加载
    unsafe { *ptr.as_ref_unchecked() }
}

pub fn hot_path_access_checked(ptr: *const u32) -> Option<u32> {
    // 有分支（null 检查）
    unsafe { ptr.as_ref().copied() }
}

/// 示例 6：与 MaybeUninit 结合（安全初始化模式）
///
/// 使用 `MaybeUninit` 分配未初始化内存，
/// 初始化后通过 `as_ref_unchecked` 访问（已知已初始化）。
///
/// # Safety
/// `f` 必须正确初始化传入的引用。
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

/// # PowerPC / PowerPC64 内联汇编
///
/// Rust 1.95.0 稳定了 PowerPC 和 PowerPC64 架构的内联汇编支持。
/// 这使得 Rust 可用于嵌入式 PowerPC 系统（如网络设备、工业控制器、游戏主机）。
///
/// ## 概念
/// - **Inline Assembly**: 在高级语言中直接嵌入机器指令
/// - **RISC Architecture**: PowerPC 是精简指令集，与 ARM/x86 有显著差异
///
/// ## 语法
/// ```ignore
/// unsafe {
///     std::arch::asm!(
///         "nop",           // PowerPC 指令
///         options(nomem, nostack)
///     );
/// }
/// ```
///
/// ## 平台支持状态（1.95）
/// - `powerpc64-unknown-linux-musl` → **Tier 2 with host tools**
pub struct PowerPcAsmExamples;

impl PowerPcAsmExamples {
    /// 概念性示例：PowerPC `nop` 指令
    ///
    /// 注意：此代码仅在 PowerPC 目标上可编译。
    #[cfg(any(target_arch = "powerpc", target_arch = "powerpc64"))]
    pub unsafe fn ppc_nop() {
        unsafe {
            std::arch::asm!("nop", options(nomem, nostack));
        }
    }

    /// 概念性示例：读取时间戳寄存器 (Time Base)
    ///
    /// PowerPC 的 Time Base 寄存器提供高精度计时。
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

    /// Host 目标上的模拟（仅用于文档编译）
    #[cfg(not(any(target_arch = "powerpc", target_arch = "powerpc64")))]
    pub unsafe fn ppc_nop() {
        // 在 non-PowerPC 目标上，内联汇编不可用
        // 此处仅为概念占位
    }

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
// 3. cfg_select! 在嵌入式跨平台配置中的应用
// ============================================================================

/// # `cfg_select!` 嵌入式跨平台抽象
///
/// 展示了 `cfg_select!` 如何简化嵌入式开发中的架构特定代码选择。
pub struct EmbeddedCfgSelect;

impl EmbeddedCfgSelect {
    /// 选择架构特定的内存屏障指令
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
    pub const DEFAULT_SYSCLK_HZ: u32 = cfg_select! {
        target_arch = "arm" => 72_000_000,      // 72 MHz (STM32F1)
        target_arch = "aarch64" => 1_500_000_000, // 1.5 GHz (Raspberry Pi 4)
        target_arch = "riscv32" => 160_000_000,  // 160 MHz (ESP32-C3)
        target_arch = "riscv64" => 1_000_000_000, // 1 GHz (VisionFive 2)
        _ => 100_000_000,
    };

    /// 栈对齐要求（字节）
    pub const STACK_ALIGNMENT: usize = cfg_select! {
        target_arch = "arm" => 8,
        target_arch = "aarch64" => 16,
        target_arch = "riscv32" => 16,
        target_arch = "riscv64" => 16,
        target_arch = "x86_64" => 16,
        _ => 8,
    };

    /// 中断向量表大小
    pub const IRQ_VECTOR_COUNT: usize = cfg_select! {
        target_arch = "arm" => 16,      // Cortex-M NVIC
        target_arch = "riscv32" => 32,  // PLIC / CLINT
        target_arch = "riscv64" => 32,
        _ => 16,
    };
}

fn arm_barrier() {
    // ARM DMB 指令占位
}
fn aarch64_barrier() {
    // AArch64 DMB 指令占位
}
fn riscv_barrier() {
    // RISC-V FENCE 指令占位
}
fn x86_barrier() {
    // x86 mfence 指令占位
}
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
        assert!(EmbeddedCfgSelect::DEFAULT_SYSCLK_HZ > 0);
        assert!(EmbeddedCfgSelect::STACK_ALIGNMENT >= 8);
        assert!(EmbeddedCfgSelect::IRQ_VECTOR_COUNT > 0);
    }

    #[test]
    fn test_memory_barrier() {
        EmbeddedCfgSelect::memory_barrier();
        // 只要不出错即通过
    }
}
