//! Raw Pointers Advanced

/// 裸指针基础操作
/// pointer foundation operation
/// pointer foundation
/// - 裸pointercanas null
/// - 裸指针允许多个 `*mut` 指向同一地址（别名）
/// - pointer allow `*mut` （）
/// - pointer `*mut` （）
/// - 裸指针不自动解引用，也不受借用规则约束
/// - pointer reference ，borrowing rule constraint
/// - pointer reference ，borrowing rule
pub mod raw_pointer_basics {
    /// 安全地将引用转换为裸指针
    /// will reference conversion as pointer
    pub fn ref_to_raw<T>(r: &T) -> *const T {
        r as *const T
    }

    /// 安全地将可变引用转换为可变裸指针
    /// will reference conversion as pointer
    pub fn mut_ref_to_raw<T>(r: &mut T) -> *mut T {
        r as *mut T
    }

    /// 演示别名规则差异
    /// demonstration rule
    /// 引用不允许可变别名，但裸指针允许。
    /// reference allow ，but pointer allow 。
    /// reference ，but pointer 。
    ///
    /// 调用者必须确保不会导致数据竞争。
    /// must data 。
    /// must 。
    pub unsafe fn aliased_mutate(val: *mut i32) {
        let a = val;
        let b = val;
        unsafe {
            *a = 1;
            *b = 2;
        }
    }
}

/// Volatile 内存访问
/// Volatile memory
/// `core::ptr::read_volatile` / `write_volatile` 阻止编译器优化。
/// `core::ptr::read_volatile` / `write_volatile` 阻止编译器optimization。
pub mod volatile_access {
    /// 概念性 GPIO 寄存器地址
    /// concept GPIO
    pub const GPIO_BASE: usize = 0x4002_0000;

    /// 使用 volatile read 读取寄存器
    /// volatile read
    pub unsafe fn read_register(addr: *const u32) -> u32 {
        unsafe { addr.read_volatile() }
    }

    /// 使用 volatile write 写入寄存器
    /// volatile write
    pub unsafe fn write_register(addr: *mut u32, value: u32) {
        unsafe {
            addr.write_volatile(value);
        }
    }

    /// 修改寄存器的特定位（读-修改-写）
    /// （--）
    ///
    /// 地址必须有效。
    /// must effective 。
    /// 地址musteffective。
    pub unsafe fn modify_register_bits(addr: *mut u32, mask: u32, value: u32) {
        let current = unsafe { addr.read_volatile() };
        unsafe {
            addr.write_volatile((current & !mask) | (value & mask));
        }
    }
}

/// 内联汇编概念（Rust 1.59+ `asm!` 已稳定）
/// inside concept （Rust 1.59+ `asm!` ）
/// `core::arch::asm!` 允许在 Rust 中直接嵌入汇编代码。
/// `core::arch::asm!` allow in Rust in 。
/// `core::arch::asm!` in Rust in 。
/// `core::arch::asm!` Allowsin Rust in直接嵌入汇编代码。
pub mod inline_asm_concepts {
    /// 获取当前 CPU 核心 ID（x86_64 概念演示）
    /// when before CPU core ID（x86_64 concept demonstration ）
    #[cfg(target_arch = "x86_64")]
    pub fn get_cpu_core_id() -> u32 {
        let result = core::arch::x86_64::__cpuid_count(1, 0);
        (result.ebx >> 24) & 0xFF
    }

    /// 空操作（NOP）概念演示
    /// operation （NOP）concept demonstration
    /// （NOP）concept demonstration
    #[cfg(target_arch = "x86_64")]
    pub fn nop() {
        unsafe {
            core::arch::asm!("nop", options(nostack, nomem));
        }
    }

    /// 获取时间戳计数器（x86_64 rdtsc）
    /// time （x86_64 rdtsc）
    #[cfg(target_arch = "x86_64")]
    pub fn rdtsc() -> u64 {
        let mut low: u32;
        let mut high: u32;
        unsafe {
            core::arch::asm!(
                "rdtsc",
                lateout("eax") low,
                lateout("edx") high,
                options(nomem, nostack),
            );
        }
        ((high as u64) << 32) | (low as u64)
    }

    /// 内存屏障概念（ARM64）
    /// memory barrier concept （ARM64）
    #[cfg(target_arch = "aarch64")]
    pub fn memory_barrier() {
        unsafe {
            core::arch::asm!("dmb ish", options(nostack, preserves_flags));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_raw_pointer_alias() {
        let mut x = 0;
        unsafe {
            raw_pointer_basics::aliased_mutate(&mut x);
        }
        assert_eq!(x, 2);
    }

    #[test]
    fn test_volatile_read_write() {
        let mut buf = 0u32;
        unsafe {
            let val = volatile_access::read_register(&buf);
            assert_eq!(val, 0);
            volatile_access::write_register(&mut buf, 0xDEAD_BEEF);
            assert_eq!(buf, 0xDEAD_BEEF);
        }
    }

    #[test]
    #[cfg(target_arch = "x86_64")]
    #[cfg_attr(miri, ignore)]
    fn test_asm_nop() {
        inline_asm_concepts::nop();
    }

    #[test]
    #[cfg(target_arch = "x86_64")]
    #[cfg_attr(miri, ignore)]
    fn test_rdtsc() {
        let t1 = inline_asm_concepts::rdtsc();
        let t2 = inline_asm_concepts::rdtsc();
        assert!(t2 >= t1);
    }
}
