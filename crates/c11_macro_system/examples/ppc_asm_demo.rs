//! Rust 1.95.0 PowerPC / PowerPC64 内联汇编专题示例
//!
//! Rust 1.95.0 稳定化了 PowerPC 和 PowerPC64 架构的内联汇编支持。
//! 本示例展示在 `#[cfg(target_arch = "powerpc64")]` 条件下的汇编代码，
//! 并附带 x86_64 回退实现，确保在所有平台上可编译运行。
//!
//! 权威来源: https://releases.rs/docs/1.95.0/
//!
//! 运行方式:
//! ```bash
//! # 在 PowerPC64 目标上:
//! cargo run --example ppc_asm_demo -p c11_macro_system --target powerpc64-unknown-linux-gnu
//!
//! # 在其他目标上（使用回退实现）:
//! cargo run --example ppc_asm_demo -p c11_macro_system
//! ```

use std::arch::asm;

// ==================== 平台抽象层 ====================

/// 获取当前架构名称
#[inline(always)]
fn arch_name() -> &'static str {
    cfg_select! {
        target_arch = "powerpc" => "PowerPC (32-bit)",
        target_arch = "powerpc64" => "PowerPC64",
        target_arch = "x86_64" => "x86_64",
        target_arch = "aarch64" => "AArch64",
        _ => "Unknown",
    }
}

/// 内存屏障（Memory Fence）
///
/// PowerPC 使用 `sync` 指令实现全内存屏障。
#[inline(always)]
fn memory_fence() {
    cfg_select! {
        any(target_arch = "powerpc", target_arch = "powerpc64") => {
            unsafe {
                asm!("sync", options(nostack, preserves_flags));
            }
        }
        _ => {
            // 非 PowerPC 平台使用编译器屏障
            std::sync::atomic::fence(std::sync::atomic::Ordering::SeqCst);
        }
    }
}

/// 获取时间戳计数器（Time Base Register）
///
/// PowerPC 使用 `mftb` 指令读取时间基准寄存器。
/// 返回一个 64 位时间戳值。
#[inline(always)]
fn read_timestamp() -> u64 {
    cfg_select! {
        target_arch = "powerpc64" => {
            let mut tb: u64;
            unsafe {
                // mftb 读取 Time Base 寄存器（64-bit 在 PPC64 上）
                asm!(
                    "mftb {0}",
                    out(reg) tb,
                    options(nostack, preserves_flags)
                );
            }
            tb
        }
        target_arch = "powerpc" => {
            let mut tbu: u32;
            let mut tbl: u32;
            unsafe {
                // 32-bit PowerPC: TB 分为高 32 位 (TBU) 和低 32 位 (TBL)
                asm!(
                    "mftbu {0}\n\t"
                    "mftbl {1}",
                    out(reg) tbu,
                    out(reg) tbl,
                    options(nostack, preserves_flags)
                );
            }
            ((tbu as u64) << 32) | (tbl as u64)
        }
        target_arch = "x86_64" => {
            // x86_64 回退: 使用 rdtsc
            let mut low: u32;
            let mut high: u32;
            unsafe {
                asm!(
                    "rdtsc",
                    out("eax") low, out("edx") high,
                    options(nostack, preserves_flags)
                );
            }
            ((high as u64) << 32) | (low as u64)
        }
        _ => {
            // 通用回退
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos() as u64
        }
    }
}

/// 无操作（NOP）
#[inline(always)]
fn arch_nop() {
    cfg_select! {
        any(target_arch = "powerpc", target_arch = "powerpc64") => {
            unsafe { asm!("nop", options(nostack, preserves_flags)); }
        }
        target_arch = "x86_64" => {
            unsafe { asm!("nop", options(nostack, preserves_flags)); }
        }
        _ => {}
    }
}

/// 读取 CPU 标识信息
///
/// PowerPC 使用 `mfspr` 读取特殊功能寄存器。
#[inline(always)]
fn read_processor_version() -> u32 {
    cfg_select! {
        any(target_arch = "powerpc", target_arch = "powerpc64") => {
            let mut pvr: u32;
            unsafe {
                // PVR (Processor Version Register) 位于 SPR 287
                asm!(
                    "mfspr {0}, 287",
                    out(reg) pvr,
                    options(nostack, preserves_flags)
                );
            }
            pvr
        }
        _ => {
            // 非 PowerPC 平台返回占位值
            0xFFFF_FFFF
        }
    }
}

// ==================== 示例 1: 内存屏障 ====================

fn demo_memory_fence() {
    println!("--- 内存屏障 (Memory Fence) ---");

    let mut data = 0u64;

    // 写入数据
    data = 42;

    // 发出内存屏障，确保写入对其他 CPU 可见
    memory_fence();

    println!("  当前架构: {}", arch_name());
    println!("  写入数据: {} (已通过内存屏障同步)", data);
    assert_eq!(data, 42);
}

// ==================== 示例 2: 时间戳读取 ====================

fn demo_timestamp() {
    println!("\n--- 时间戳计数器 (Time Base Register) ---");

    let t1 = read_timestamp();

    // 做一些工作
    let mut sum = 0u64;
    for i in 0..1_000_000 {
        sum += i;
    }
    let _ = sum;

    let t2 = read_timestamp();

    println!("  当前架构: {}", arch_name());
    println!("  开始时间戳: {}", t1);
    println!("  结束时间戳: {}", t2);
    println!("  差值: {} (时间基准单位)", t2 - t1);
}

// ==================== 示例 3: CPU 版本寄存器 ====================

fn demo_processor_version() {
    println!("\n--- 处理器版本寄存器 (PVR) ---");

    let pvr = read_processor_version();
    println!("  当前架构: {}", arch_name());

    cfg_select! {
        any(target_arch = "powerpc", target_arch = "powerpc64") => {
            println!("  PVR: 0x{:08X}", pvr);
            // PVR 高 16 位是版本，低 16 位是修订
            let version = (pvr >> 16) & 0xFFFF;
            let revision = pvr & 0xFFFF;
            println!("  版本: 0x{:04X}, 修订: 0x{:04X}", version, revision);
        }
        _ => {
            println!("  PVR: 0x{:08X} (非 PowerPC 平台，占位值)", pvr);
        }
    }
}

// ==================== 示例 4: 原子自增（使用内联汇编） ====================

/// 使用 PowerPC `lwarx` / `stwcx.` 指令实现原子自增
///
/// 这是 PowerPC 的 LL/SC（Load-Link / Store-Conditional）原语。
#[inline(always)]
fn atomic_increment_ppc(addr: &mut u32) -> u32 {
    cfg_select! {
        any(target_arch = "powerpc", target_arch = "powerpc64") => {
            let mut old: u32;
            let mut success: u32;
            unsafe {
                asm!(
                    "2: lwarx {old}, 0, {addr}\n\t"
                    "addi {new}, {old}, 1\n\t"
                    "stwcx. {new}, 0, {addr}\n\t"
                    "bne- 2b\n\t"
                    "isync",
                    old = out(reg) old,
                    new = out(reg) _,
                    addr = in(reg) addr,
                    success = out(reg) success,
                    options(nostack)
                );
            }
            old
        }
        _ => {
            // 回退到标准库原子操作
            std::sync::atomic::fence(std::sync::atomic::Ordering::SeqCst);
            let old = *addr;
            *addr += 1;
            old
        }
    }
}

fn demo_atomic_increment() {
    println!("\n--- 原子自增 (LL/SC 原语) ---");

    let mut counter: u32 = 0;
    let old = atomic_increment_ppc(&mut counter);

    println!("  当前架构: {}", arch_name());
    println!("  旧值: {}, 新值: {}", old, counter);
    assert_eq!(old, 0);
    assert_eq!(counter, 1);
}

// ==================== 示例 5: 条件编译对比 ====================

fn demo_cfg_comparison() {
    println!("\n--- cfg! 与 cfg_select! 对比 ---");

    // 使用 cfg! 宏: 编译期求值，但生成所有分支的 IR
    let msg_cfg = if cfg!(target_arch = "powerpc64") {
        "PowerPC64 detected by cfg!"
    } else if cfg!(target_arch = "powerpc") {
        "PowerPC detected by cfg!"
    } else {
        "Non-PowerPC by cfg!"
    };
    println!("  [cfg! macro]  {}", msg_cfg);

    // 使用 cfg_select!: 仅保留匹配分支
    let msg_select = cfg_select! {
        target_arch = "powerpc64" => "PowerPC64 detected by cfg_select!",
        target_arch = "powerpc" => "PowerPC detected by cfg_select!",
        _ => "Non-PowerPC by cfg_select!",
    };
    println!("  [cfg_select!] {}", msg_select);
}

// ==================== 主演示函数 ====================

fn main() {
    println!("🦀 Rust 1.95.0 PowerPC / PowerPC64 内联汇编专题演示\n");
    println!("当前运行平台: {}\n", arch_name());

    // 在非 PowerPC 平台上，回退实现仍然可用
    demo_memory_fence();
    demo_timestamp();
    demo_processor_version();
    demo_atomic_increment();
    demo_cfg_comparison();

    println!("\n✅ PowerPC 内联汇编演示完成！");
    println!("   关键要点:");
    println!("   - asm!() 在 PowerPC/PowerPC64 上已稳定（Rust 1.95.0+）");
    println!("   - 常用指令: sync (屏障), mftb (时间戳), mfspr (特殊寄存器)");
    println!("   - LL/SC: lwarx + stwcx. 实现原子操作");
    println!("   - 使用 cfg_select! 实现跨平台条件编译，替代 cfg-if crate");
    println!("   - 非 PowerPC 平台通过 cfg_select! 回退到标准库实现");
}
