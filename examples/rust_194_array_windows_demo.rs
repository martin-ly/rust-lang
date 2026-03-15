//! Rust 1.94 array_windows 特性完整示例
//! 
//! 运行方式: rustc --edition 2024 examples/rust_194_array_windows_demo.rs && ./rust_194_array_windows_demo

#![allow(dead_code)]

use std::time::Instant;

// =============================================================================
// 基础示例
// =============================================================================

/// 检测 ABBA 模式
/// 示例: xyyx, abba
fn has_abba(s: &str) -> bool {
    s.as_bytes()
        .array_windows()
        .any(|[a1, b1, b2, a2]| (a1 != b1) && (a1 == a2) && (b1 == b2))
}

/// 计算滑动窗口平均值
fn moving_average(data: &[f64], window_size: usize) -> Vec<f64> {
    match window_size {
        3 => data.array_windows::<3>()
            .map(|&[a, b, c]| (a + b + c) / 3.0)
            .collect(),
        5 => data.array_windows::<5>()
            .map(|arr| arr.iter().sum::<f64>() / 5.0)
            .collect(),
        _ => panic!("不支持的窗口大小: {}", window_size),
    }
}

// =============================================================================
// 高级示例: 金融技术分析
// =============================================================================

/// 股票技术指标分析器
struct TechnicalAnalyzer;

impl TechnicalAnalyzer {
    /// 计算简单移动平均线 (SMA)
    fn calculate_sma(prices: &[f64], period: usize) -> Vec<f64> {
        if prices.len() < period {
            return Vec::new();
        }
        
        match period {
            5 => prices.array_windows::<5>()
                .map(|arr| arr.iter().sum::<f64>() / 5.0)
                .collect(),
            10 => prices.array_windows::<10>()
                .map(|arr| arr.iter().sum::<f64>() / 10.0)
                .collect(),
            20 => prices.array_windows::<20>()
                .map(|arr| arr.iter().sum::<f64>() / 20.0)
                .collect(),
            _ => {
                // 通用实现
                prices.windows(period)
                    .map(|w| w.iter().sum::<f64>() / period as f64)
                    .collect()
            }
        }
    }
    
    /// 计算指数移动平均线 (EMA)
    fn calculate_ema(prices: &[f64], period: usize) -> Vec<f64> {
        if prices.len() < period {
            return Vec::new();
        }
        
        let multiplier = 2.0 / (period as f64 + 1.0);
        let mut ema = Vec::with_capacity(prices.len() - period + 1);
        
        // 初始 EMA 使用 SMA
        let sma: f64 = prices[0..period].iter().sum::<f64>() / period as f64;
        ema.push(sma);
        
        // 计算后续 EMA
        for i in period..prices.len() {
            let current_ema = (prices[i] - ema.last().unwrap()) * multiplier + ema.last().unwrap();
            ema.push(current_ema);
        }
        
        ema
    }
    
    /// 检测 MACD 交叉信号
    fn detect_macd_signals(short_term: &[f64], long_term: &[f64]) -> Vec<TradeSignal> {
        short_term.iter()
            .zip(long_term.iter())
            .map(|(s, l)| s - l)
            .collect::<Vec<_>>()
            .array_windows::<2>()
            .enumerate()
            .filter_map(|(idx, &[prev, curr])| {
                match (prev.signum() as i8, curr.signum() as i8) {
                    (-1, 1) => Some(TradeSignal::GoldenCross(idx + 1)),
                    (1, -1) => Some(TradeSignal::DeathCross(idx + 1)),
                    _ => None,
                }
            })
            .collect()
    }
    
    /// 计算布林带
    fn calculate_bollinger_bands(prices: &[f64], period: usize, std_dev: f64) -> (Vec<f64>, Vec<f64>, Vec<f64>) {
        let sma = Self::calculate_sma(prices, period);
        let mut upper = Vec::with_capacity(sma.len());
        let mut lower = Vec::with_capacity(sma.len());
        
        for (i, &middle) in sma.iter().enumerate() {
            let start = i;
            let end = i + period;
            if end > prices.len() {
                break;
            }
            
            let variance: f64 = prices[start..end].iter()
                .map(|&p| (p - middle).powi(2))
                .sum::<f64>() / period as f64;
            let std = variance.sqrt();
            
            upper.push(middle + std_dev * std);
            lower.push(middle - std_dev * std);
        }
        
        (upper, sma, lower)
    }
}

#[derive(Debug, Clone, Copy)]
enum TradeSignal {
    GoldenCross(usize),  // 金叉 - 买入信号
    DeathCross(usize),   // 死叉 - 卖出信号
}

// =============================================================================
// 高级示例: 信号处理
// =============================================================================

/// 简单移动平均滤波器
fn moving_average_filter(signal: &[f64], window_size: usize) -> Vec<f64> {
    match window_size {
        3 => signal.array_windows::<3>()
            .map(|&[a, b, c]| (a + b + c) / 3.0)
            .collect(),
        5 => signal.array_windows::<5>()
            .map(|arr| arr.iter().sum::<f64>() / 5.0)
            .collect(),
        _ => signal.windows(window_size)
            .map(|w| w.iter().sum::<f64>() / window_size as f64)
            .collect(),
    }
}

/// 边缘检测 (Sobel 算子简化版)
fn edge_detection_1d(data: &[f64]) -> Vec<f64> {
    data.array_windows::<3>()
        .map(|&[a, b, c]| {
            // 简化梯度计算
            ((c - a) / 2.0).abs()
        })
        .collect()
}

/// 峰值检测
fn detect_peaks(data: &[f64]) -> Vec<usize> {
    data.array_windows::<3>()
        .enumerate()
        .filter_map(|(idx, &[a, b, c])| {
            if b > a && b > c {
                Some(idx + 1)
            } else {
                None
            }
        })
        .collect()
}

// =============================================================================
// 性能对比测试
// =============================================================================

fn benchmark_comparison() {
    println!("\n=== 性能对比测试 ===");
    
    // 生成测试数据
    let data: Vec<f64> = (0..100_000)
        .map(|i| (i as f64).sin() * 100.0 + 50.0)
        .collect();
    
    // 测试 array_windows
    let start = Instant::now();
    let result1: Vec<f64> = data.array_windows::<3>()
        .map(|&[a, b, c]| (a + b + c) / 3.0)
        .collect();
    let time1 = start.elapsed();
    
    // 测试传统 windows
    let start = Instant::now();
    let result2: Vec<f64> = data.windows(3)
        .map(|w| (w[0] + w[1] + w[2]) / 3.0)
        .collect();
    let time2 = start.elapsed();
    
    // 测试手动索引
    let start = Instant::now();
    let mut result3 = Vec::with_capacity(data.len() - 2);
    for i in 0..data.len() - 2 {
        result3.push((data[i] + data[i + 1] + data[i + 2]) / 3.0);
    }
    let time3 = start.elapsed();
    
    println!("数据大小: {}", data.len());
    println!("array_windows::<3>: {:?}", time1);
    println!("windows(3):         {:?}", time2);
    println!("手动索引:           {:?}", time3);
    println!("结果一致性: {}", result1 == result2 && result2 == result3);
    
    // 计算加速比
    let speedup = time2.as_secs_f64() / time1.as_secs_f64();
    println!("加速比: {:.2}x", speedup);
}

// =============================================================================
// 主函数
// =============================================================================

fn main() {
    println!("=== Rust 1.94 array_windows 特性演示 ===\n");
    
    // 1. 基础示例
    println!("1. ABBA 模式检测");
    let test_strings = ["abba", "xyyx", "abcd", "abbaac"];
    for s in test_strings {
        println!("  {}: {}", s, has_abba(s));
    }
    
    // 2. 滑动平均
    println!("\n2. 滑动平均计算");
    let data = vec![1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0];
    let avg3 = moving_average(&data, 3);
    println!("  原始数据: {:?}", data);
    println!("  3期平均:  {:?}", avg3);
    
    // 3. 技术分析
    println!("\n3. 股票技术分析");
    let prices: Vec<f64> = (0..50)
        .map(|i| 100.0 + (i as f64).sin() * 10.0 + i as f64 * 0.5)
        .collect();
    
    let sma5 = TechnicalAnalyzer::calculate_sma(&prices, 5);
    println!("  SMA(5) 前5个值: {:?}", &sma5[..5.min(sma5.len())]);
    
    // 4. 峰值检测
    println!("\n4. 峰值检测");
    let signal = vec![1.0, 3.0, 5.0, 4.0, 2.0, 6.0, 8.0, 7.0, 5.0];
    let peaks = detect_peaks(&signal);
    println!("  信号: {:?}", signal);
    println!("  峰值位置: {:?}", peaks);
    
    // 5. 性能测试
    benchmark_comparison();
    
    println!("\n=== 演示完成 ===");
}
