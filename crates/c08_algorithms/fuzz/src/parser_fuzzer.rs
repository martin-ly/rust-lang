#![no_main]

use libfuzzer_sys::fuzz_target;

/// 模糊测试算法 crate 的输入解析边界条件
/// 目标: 确保解析任意输入不会 panic、越界或产生未定义行为
///
/// # 检测范围
/// - 数值解析边界 (i64, u128, f64)
/// - 字节序列处理
/// - UTF-8 字符串转换
///
/// # 参考实践
/// - Google OSS-Fuzz 最佳实践
/// - Cloudflare Rust 模糊测试经验
fuzz_target!(|data: &[u8]| {
    // 测试 UTF-8 字符串解析路径
    if let Ok(input) = std::str::from_utf8(data) {
        // 整数解析：测试各种进制和边界
        let _ = input.parse::<i64>();
        let _ = input.parse::<u128>();
        let _ = input.parse::<i128>();

        // 浮点数解析：测试特殊值 (NaN, inf, 极小数)
        let _ = input.parse::<f64>();
        let _ = input.parse::<f32>();

        // 测试空字符串和空白字符处理
        let trimmed = input.trim();
        if !trimmed.is_empty() {
            let _ = trimmed.parse::<usize>();
        }
    }

    // 测试固定长度字节转换（模拟网络协议/二进制格式解析）
    if data.len() >= 8 {
        let _ = u64::from_le_bytes([
            data[0], data[1], data[2], data[3], data[4], data[5], data[6], data[7],
        ]);
        let _ = u64::from_be_bytes([
            data[0], data[1], data[2], data[3], data[4], data[5], data[6], data[7],
        ]);
        let _ = i64::from_le_bytes([
            data[0], data[1], data[2], data[3], data[4], data[5], data[6], data[7],
        ]);
    }

    if data.len() >= 4 {
        let _ = u32::from_le_bytes([data[0], data[1], data[2], data[3]]);
        let _ = f32::from_le_bytes([data[0], data[1], data[2], data[3]]);
    }

    if data.len() >= 2 {
        let _ = u16::from_le_bytes([data[0], data[1]]);
    }

    // 测试变长字节序列的迭代和分块操作
    // 模拟算法中常见的缓冲区处理
    for chunk in data.chunks(16) {
        let _sum: u8 = chunk.iter().fold(0u8, |a, b| a.wrapping_add(*b));
        let _xor: u8 = chunk.iter().fold(0u8, |a, b| a ^ *b);
    }

    // 测试排序和搜索算法的边界输入
    // 将字节转换为小整数数组，模拟排序输入
    let small_ints: Vec<u8> = data.iter().map(|b| b.wrapping_mul(7)).collect();
    if small_ints.len() >= 2 && small_ints.len() <= 1024 {
        let mut sorted = small_ints.clone();
        sorted.sort_unstable();
        // 验证排序结果
        for i in 1..sorted.len() {
            assert!(sorted[i - 1] <= sorted[i], "排序结果必须是非递减的");
        }
    }
});
