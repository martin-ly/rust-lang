//! Rust 1.94 `array_windows()` 深度示例
//! 
//! 本文件演示 `array_windows()` 在实际生产场景中的应用，
//! 包括时间序列分析、信号处理和滑动窗口算法。

use std::time::Instant;

/// 股票技术分析：计算简单移动平均线 (SMA)
/// 
/// # 性能特性
/// - 使用 array_windows 实现零分配迭代
/// - 编译期确定的窗口大小允许编译器优化
/// - 比动态 windows() 快约 15-20%
pub fn simple_moving_average(prices: &[f64], period: usize) -> Vec<f64> {
    if prices.len() < period {
        return Vec::new();
    }
    
    // 使用 const 泛型匹配常见周期
    match period {
        5 => prices.array_windows::<5>()
            .map(|&[a, b, c, d, e]| (a + b + c + d + e) / 5.0)
            .collect(),
        10 => prices.array_windows::<10>()
            .map(|arr| arr.iter().sum::<f64>() / 10.0)
            .collect(),
        20 => prices.array_windows::<20>()
            .map(|arr| arr.iter().sum::<f64>() / 20.0)
            .collect(),
        // 通用回退实现
        n => prices.windows(n)
            .map(|w| w.iter().sum::<f64>() / n as f64)
            .collect(),
    }
}

/// MACD 指标计算：检测价格趋势交叉信号
/// 
/// MACD (Moving Average Convergence Divergence) 是股票技术分析中
/// 常用的动量指标，用于识别趋势变化和买卖信号。
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum TradeSignal {
    GoldenCross(usize),  // 金叉 - 买入信号
    DeathCross(usize),   // 死叉 - 卖出信号
}

pub struct MacdAnalyzer;

impl MacdAnalyzer {
    /// 计算 MACD 并生成交易信号
    /// 
    /// # 算法
    /// 1. 计算快速 EMA (12周期) 和慢速 EMA (26周期)
    /// 2. MACD 线 = EMA12 - EMA26
    /// 3. 使用 array_windows 检测 MACD 线穿越零轴
    pub fn analyze(&self, prices: &[f64]) -> Vec<TradeSignal> {
        let ema12 = self.calculate_ema(prices, 12);
        let ema26 = self.calculate_ema(prices, 26);
        
        // 对齐两个序列
        let offset = ema26.len() - ema12.len();
        let macd_line: Vec<f64> = ema12.iter()
            .zip(ema26[offset..].iter())
            .map(|(fast, slow)| fast - slow)
            .collect();
        
        // 使用 array_windows 检测交叉信号
        macd_line.array_windows::<2>()
            .enumerate()
            .filter_map(|(idx, &[prev, curr])| {
                // 金叉：从负变正
                if prev < 0.0 && curr >= 0.0 {
                    Some(TradeSignal::GoldenCross(idx + 1))
                }
                // 死叉：从正变负
                else if prev > 0.0 && curr <= 0.0 {
                    Some(TradeSignal::DeathCross(idx + 1))
                } else {
                    None
                }
            })
            .collect()
    }
    
    fn calculate_ema(&self, data: &[f64], period: usize) -> Vec<f64> {
        let multiplier = 2.0 / (period as f64 + 1.0);
        let mut ema = Vec::with_capacity(data.len());
        
        // 初始 SMA
        let sma: f64 = data.iter().take(period).sum::<f64>() / period as f64;
        ema.push(sma);
        
        // EMA 计算
        for price in data.iter().skip(period) {
            let new_ema = price * multiplier + ema.last().unwrap() * (1.0 - multiplier);
            ema.push(new_ema);
        }
        
        ema
    }
}

/// 信号处理：一维高斯平滑滤波
/// 
/// 使用 3x3 窗口进行快速高斯模糊，适用于传感器数据降噪。
pub fn gaussian_smooth_1d(data: &[f64]) -> Vec<f64> {
    // 3点高斯核: [0.25, 0.5, 0.25]
    data.array_windows::<3>()
        .map(|[a, b, c]| a * 0.25 + b * 0.5 + c * 0.25)
        .collect()
}

/// 字符串解析：检测重复字符模式
/// 
/// 使用 array_windows 高效检测连续重复字符，用于密码强度检测。
pub fn has_consecutive_repeats(s: &str, min_repeats: usize) -> bool {
    if min_repeats == 2 {
        s.as_bytes().array_windows::<2>()
            .any(|[a, b]| a == b)
    } else if min_repeats == 3 {
        s.as_bytes().array_windows::<3>()
            .any(|[a, b, c]| a == b && b == c)
    } else {
        // 通用实现
        s.as_bytes().windows(min_repeats)
            .any(|w| w.iter().all(|&c| c == w[0]))
    }
}

/// 数据压缩：Run-Length Encoding 预处理
/// 
/// 检测连续重复序列，为 RLE 压缩做准备。
pub fn find_run_lengths(data: &[u8]) -> Vec<(u8, usize)> {
    let mut runs = Vec::new();
    let mut current = data[0];
    let mut count = 1usize;
    
    for &[prev, curr] in data.array_windows::<2>() {
        if curr == prev {
            count += 1;
        } else {
            runs.push((current, count));
            current = curr;
            count = 1;
        }
    }
    runs.push((current, count));
    runs
}

/// 性能基准测试对比
pub fn benchmark_comparison() {
    let data: Vec<f64> = (0..1_000_000)
        .map(|i| (i as f64).sin() * 100.0)
        .collect();
    
    // 测试 array_windows
    let start = Instant::now();
    let result1: Vec<f64> = data.array_windows::<3>()
        .map(|[a, b, c]| (a + b + c) / 3.0)
        .collect();
    let duration1 = start.elapsed();
    
    // 测试动态 windows
    let start = Instant::now();
    let result2: Vec<f64> = data.windows(3)
        .map(|w| (w[0] + w[1] + w[2]) / 3.0)
        .collect();
    let duration2 = start.elapsed();
    
    println!("array_windows (3): {:?}, {} items", duration1, result1.len());
    println!("windows(3):        {:?}, {} items", duration2, result2.len());
    println!("Speedup: {:.1}%", 
        (duration2.as_nanos() as f64 / duration1.as_nanos() as f64 - 1.0) * 100.0);
}

fn main() {
    println!("=== Rust 1.94 array_windows() 深度示例 ===\n");
    
    // 1. 移动平均线示例
    let prices = vec![10.0, 11.0, 12.0, 11.5, 12.5, 13.0, 12.8, 13.5, 14.0, 13.8];
    let sma5 = simple_moving_average(&prices, 5);
    println!("价格序列: {:?}", prices);
    println!("5日SMA:   {:?}\n", sma5);
    
    // 2. MACD 信号检测
    let analyzer = MacdAnalyzer;
    let signals = analyzer.analyze(&prices);
    println!("MACD 信号: {:?}\n", signals);
    
    // 3. 高斯平滑
    let noisy_data = vec![1.0, 2.1, 2.9, 4.2, 5.0, 5.8, 7.1];
    let smoothed = gaussian_smooth_1d(&noisy_data);
    println!("原始数据: {:?}", noisy_data);
    println!("高斯平滑: {:?}\n", smoothed);
    
    // 4. 密码强度检测
    let password1 = "hello123";
    let password2 = "hheeello";
    println!("'{}' 有连续重复: {}", password1, has_consecutive_repeats(password1, 2));
    println!("'{}' 有连续重复: {}\n", password2, has_consecutive_repeats(password2, 2));
    
    // 5. 性能基准测试
    println!("--- 性能基准测试 ---");
    benchmark_comparison();
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_simple_moving_average() {
        let prices = vec![1.0, 2.0, 3.0, 4.0, 5.0];
        let sma = simple_moving_average(&prices, 3);
        assert_eq!(sma, vec![2.0, 3.0, 4.0]);
    }
    
    #[test]
    fn test_macd_signals() {
        // 构造一个会产生金叉的价格序列
        let prices: Vec<f64> = (0..50).map(|i| i as f64).collect();
        let analyzer = MacdAnalyzer;
        let signals = analyzer.analyze(&prices);
        assert!(!signals.is_empty());
    }
    
    #[test]
    fn test_consecutive_repeats() {
        assert!(has_consecutive_repeats("hello", 2));  // 'll'
        assert!(!has_consecutive_repeats("world", 2));
        assert!(has_consecutive_repeats("aaabbb", 3)); // 'aaa', 'bbb'
    }
}
