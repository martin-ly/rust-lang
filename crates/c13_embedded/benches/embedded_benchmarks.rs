//! C13 Embedded 模块性能基准测试
//!
//! 测试 bare-metal 编程概念在 host 模拟环境下的性能表现。
//! 由于真实硬件环境不可用，这些基准测试主要用于验证算法逻辑的正确性和相对性能。

use criterion::{Criterion, criterion_group, criterion_main};

/// 模拟 MMIO 寄存器访问性能
/// 对应真实场景：嵌入式系统中频繁的寄存器读写
fn bench_mmio_register_access(c: &mut Criterion) {
    c.bench_function("mmio_register_read_write", |b| {
        b.iter(|| {
            // 模拟 32 位寄存器读写
            let mut regs = [0u32; 16];
            for i in 0..regs.len() {
                regs[i] = (i as u32).wrapping_mul(0xDEADBEEF);
            }
            let _sum: u32 = regs.iter().fold(0, |a, b| a.wrapping_add(*b));
            std::hint::black_box(_sum);
        });
    });
}

/// 模拟位操作性能（嵌入式常见操作）
/// 对应真实场景：GPIO 控制、标志位处理
fn bench_bit_manipulation(c: &mut Criterion) {
    c.bench_function("bit_manipulation", |b| {
        b.iter(|| {
            let mut val: u32 = 0;
            // 设置位
            val |= 1 << 3;
            val |= 1 << 7;
            val |= 1 << 15;
            // 清除位
            val &= !(1 << 3);
            // 翻转位
            val ^= 1 << 7;
            // 读取位
            let _bit3 = (val >> 3) & 1;
            let _bit7 = (val >> 7) & 1;
            std::hint::black_box(val);
        });
    });
}

/// 模拟 CRC 计算（常用于嵌入式通信校验）
fn bench_crc32_calculation(c: &mut Criterion) {
    c.bench_function("crc32_calculation", |b| {
        let data: Vec<u8> = (0..256).map(|i| i as u8).collect();
        b.iter(|| {
            let mut crc: u32 = 0xFFFFFFFF;
            for byte in &data {
                crc ^= (*byte as u32) << 24;
                for _ in 0..8 {
                    if crc & 0x80000000 != 0 {
                        crc = (crc << 1) ^ 0x04C11DB7;
                    } else {
                        crc <<= 1;
                    }
                }
            }
            std::hint::black_box(crc ^ 0xFFFFFFFF);
        });
    });
}

/// 模拟固定点数学运算（无 FPU 的嵌入式设备常用）
fn bench_fixed_point_math(c: &mut Criterion) {
    c.bench_function("fixed_point_math", |b| {
        b.iter(|| {
            // Q16.16 固定点表示
            let a: i32 = 2_000_000; // ~30.5
            let b: i32 = 1_000_000; // ~15.25
            let _mul = ((a as i64 * b as i64) >> 16) as i32;
            let _div = ((a as i64) << 16) / (b as i64);
            let _add = a + b;
            std::hint::black_box((_mul, _div, _add));
        });
    });
}

/// 模拟环形缓冲区操作（UART/通信常用）
fn bench_ring_buffer(c: &mut Criterion) {
    c.bench_function("ring_buffer_operations", |b| {
        const SIZE: usize = 64;
        b.iter(|| {
            let mut buffer = [0u8; SIZE];
            let mut head = 0usize;
            let mut tail = 0usize;
            let mut count = 0usize;

            // 写入数据
            for i in 0..32u8 {
                if count < SIZE {
                    buffer[head] = i;
                    head = (head + 1) % SIZE;
                    count += 1;
                }
            }

            // 读取数据
            let mut _sum = 0u16;
            while count > 0 {
                _sum = _sum.wrapping_add(buffer[tail] as u16);
                tail = (tail + 1) % SIZE;
                count -= 1;
            }
            std::hint::black_box(_sum);
        });
    });
}

/// 模拟中断上下文切换（简化版）
fn bench_interrupt_context_save(c: &mut Criterion) {
    c.bench_function("interrupt_context_save_restore", |b| {
        b.iter(|| {
            // 模拟寄存器保存
            let mut context = [0u32; 8];
            for (i, reg) in context.iter_mut().enumerate() {
                *reg = (i as u32).wrapping_mul(0x1111_1111);
            }
            // 模拟寄存器恢复
            let _restored: u32 = context.iter().fold(0, |a, b| a ^ b);
            std::hint::black_box(_restored);
        });
    });
}

criterion_group!(
    benches,
    bench_mmio_register_access,
    bench_bit_manipulation,
    bench_crc32_calculation,
    bench_fixed_point_math,
    bench_ring_buffer,
    bench_interrupt_context_save,
);
criterion_main!(benches);
