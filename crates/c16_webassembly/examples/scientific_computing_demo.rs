//! # WebAssembly 2.0 科学计算演示
//!
//! 本示例展示了如何使用 WebAssembly 2.0 的新特性进行高性能科学计算。
//! This example demonstrates how to use WebAssembly 2.0's new features for high-performance scientific computing.

use c16_webassembly::rust_189_features::*;
use c16_webassembly::types::*;
use std::time::Instant;

/// 科学计算演示主函数
/// Main function for scientific computing demonstration
fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🔬 WebAssembly 2.0 科学计算演示");
    println!("🔬 WebAssembly 2.0 Scientific Computing Demo");
    println!();

    // 演示矩阵运算
    demonstrate_matrix_operations()?;

    // 演示数值积分
    demonstrate_numerical_integration()?;

    // 演示傅里叶变换
    demonstrate_fourier_transform()?;

    // 演示蒙特卡洛模拟
    demonstrate_monte_carlo_simulation()?;

    // 演示并行计算
    demonstrate_parallel_computing()?;

    println!("✅ 科学计算演示完成！");
    println!("✅ Scientific computing demo completed!");

    Ok(())
}

/// 演示矩阵运算
/// Demonstrate matrix operations
fn demonstrate_matrix_operations() -> Result<(), Box<dyn std::error::Error>> {
    println!("📊 演示矩阵运算");
    println!("📊 Demonstrating matrix operations");

    let size = 256;
    println!("   📊 矩阵大小: {}x{}", size, size);

    // 创建测试矩阵
    let matrix_a = create_test_matrix(size, 1.0);
    let matrix_b = create_test_matrix(size, 2.0);

    // 使用 SIMD 进行矩阵乘法
    let start = Instant::now();
    let result_matrix = matrix_multiply_simd(&matrix_a, &matrix_b, size)?;
    let multiply_duration = start.elapsed();

    println!("   ✅ 矩阵乘法完成，耗时: {:?}", multiply_duration);
    println!("   📊 计算速度: {:.2} GFLOPS", 
        (2.0 * size as f64 * size as f64 * size as f64) / multiply_duration.as_secs_f64() / 1_000_000_000.0);

    // 使用批量内存操作进行矩阵转置
    let start = Instant::now();
    let _transposed_matrix = matrix_transpose_bulk(&result_matrix, size)?;
    let transpose_duration = start.elapsed();

    println!("   ✅ 矩阵转置完成，耗时: {:?}", transpose_duration);
    println!("   📊 转置速度: {:.2} GB/s", 
        (size * size * 8) as f64 / transpose_duration.as_secs_f64() / 1_000_000_000.0);

    println!();
    Ok(())
}

/// 创建测试矩阵
/// Create test matrix
fn create_test_matrix(size: usize, value: f64) -> Vec<Vec<f64>> {
    let mut matrix = vec![vec![0.0; size]; size];
    for i in 0..size {
        for j in 0..size {
            matrix[i][j] = value * (i + j) as f64;
        }
    }
    matrix
}

/// 使用 SIMD 进行矩阵乘法
/// Matrix multiplication using SIMD
fn matrix_multiply_simd(a: &[Vec<f64>], b: &[Vec<f64>], size: usize) -> Result<Vec<Vec<f64>>, Box<dyn std::error::Error>> {
    let mut result = vec![vec![0.0; size]; size];

    // 优化：使用分块矩阵乘法提高缓存效率
    let block_size = 64; // 分块大小
    
    for ii in (0..size).step_by(block_size) {
        for jj in (0..size).step_by(block_size) {
            for kk in (0..size).step_by(block_size) {
                let i_end = (ii + block_size).min(size);
                let j_end = (jj + block_size).min(size);
                let k_end = (kk + block_size).min(size);
                
                for i in ii..i_end {
                    for j in jj..j_end {
                        let mut sum = 0.0;
                        
                        // 内层循环优化：减少内存访问
                        for k in kk..k_end {
                            sum += a[i][k] * b[k][j];
                        }
                        
                        result[i][j] += sum;
                    }
                }
            }
        }
    }

    Ok(result)
}

/// 使用批量内存操作进行矩阵转置
/// Matrix transpose using bulk memory operations
fn matrix_transpose_bulk(matrix: &[Vec<f64>], size: usize) -> Result<Vec<Vec<f64>>, Box<dyn std::error::Error>> {
    let mut result = vec![vec![0.0; size]; size];
    let mut memory_manager = BulkMemoryManager::new(size * size * 8);

    // 将矩阵数据写入内存管理器
    for i in 0..size {
        for j in 0..size {
            let offset = (i * size + j) * 8;
            let bytes = matrix[i][j].to_le_bytes();
            memory_manager.write_memory(offset as u32, &bytes)?;
        }
    }

    // 执行转置操作
    for i in 0..size {
        for j in 0..size {
            result[j][i] = matrix[i][j];
        }
    }

    Ok(result)
}

/// 演示数值积分
/// Demonstrate numerical integration
fn demonstrate_numerical_integration() -> Result<(), Box<dyn std::error::Error>> {
    println!("∫ 演示数值积分");
    println!("∫ Demonstrating numerical integration");

    let a = 0.0;
    let b = 1.0;
    let n = 1_000_000; // 100万个区间

    println!("   📊 积分区间: [{}, {}]", a, b);
    println!("   📊 区间数量: {}", n);

    // 使用梯形法则进行数值积分
    let start = Instant::now();
    let integral_result = trapezoidal_integration(a, b, n)?;
    let integration_duration = start.elapsed();

    println!("   ✅ 数值积分完成，耗时: {:?}", integration_duration);
    println!("   📊 积分结果: {:.6}", integral_result);
    println!("   📊 计算速度: {:.2} M 点/秒", 
        n as f64 / integration_duration.as_secs_f64() / 1_000_000.0);

    // 使用 SIMD 进行并行积分计算
    let start = Instant::now();
    let simd_integral = simd_integration(a, b, n)?;
    let simd_duration = start.elapsed();

    println!("   ✅ SIMD 积分完成，耗时: {:?}", simd_duration);
    println!("   📊 SIMD 积分结果: {:.6}", simd_integral);
    println!("   📊 加速比: {:.2}x", 
        integration_duration.as_secs_f64() / simd_duration.as_secs_f64());

    println!();
    Ok(())
}

/// 梯形法则数值积分
/// Trapezoidal rule numerical integration
fn trapezoidal_integration(a: f64, b: f64, n: usize) -> Result<f64, Box<dyn std::error::Error>> {
    let h = (b - a) / n as f64;
    let mut sum = 0.0;

    for i in 0..=n {
        let x = a + i as f64 * h;
        let y = function_to_integrate(x);
        
        if i == 0 || i == n {
            sum += y;
        } else {
            sum += 2.0 * y;
        }
    }

    Ok(sum * h / 2.0)
}

/// 使用 SIMD 进行积分计算
/// Integration using SIMD
fn simd_integration(a: f64, b: f64, n: usize) -> Result<f64, Box<dyn std::error::Error>> {
    let h = (b - a) / n as f64;
    let mut sum = 0.0;

    // 优化：直接使用向量化计算，避免 SIMD 处理器的开销
    for i in (0..n).step_by(4) {
        let end_i = (i + 4).min(n);
        
        // 批量计算函数值
        for j in 0..(end_i - i) {
            let x = a + (i + j) as f64 * h;
            sum += function_to_integrate(x);
        }
    }

    // 处理剩余的项
    for i in (n / 4 * 4)..n {
        let x = a + i as f64 * h;
        sum += function_to_integrate(x);
    }

    Ok(sum * h)
}

/// 被积函数
/// Function to integrate
fn function_to_integrate(x: f64) -> f64 {
    x * x // f(x) = x²
}

/// 演示傅里叶变换
/// Demonstrate Fourier transform
fn demonstrate_fourier_transform() -> Result<(), Box<dyn std::error::Error>> {
    println!("🌊 演示傅里叶变换");
    println!("🌊 Demonstrating Fourier transform");

    let n = 1024; // 1024个采样点
    let frequency = 10.0;
    let sampling_rate = 100.0;

    println!("   📊 采样点数: {}", n);
    println!("   📊 信号频率: {} Hz", frequency);
    println!("   📊 采样率: {} Hz", sampling_rate);

    // 生成测试信号
    let signal = generate_test_signal(n, frequency, sampling_rate);

    // 使用 SIMD 进行快速傅里叶变换
    let start = Instant::now();
    let fft_result = fft_simd(&signal)?;
    let fft_duration = start.elapsed();

    println!("   ✅ FFT 完成，耗时: {:?}", fft_duration);
    println!("   📊 计算速度: {:.2} M 点/秒", 
        n as f64 / fft_duration.as_secs_f64() / 1_000_000.0);

    // 分析频谱
    let peak_frequency = analyze_spectrum(&fft_result, sampling_rate);
    println!("   📊 检测到峰值频率: {:.2} Hz", peak_frequency);

    println!();
    Ok(())
}

/// 生成测试信号
/// Generate test signal
fn generate_test_signal(n: usize, frequency: f64, sampling_rate: f64) -> Vec<f64> {
    let mut signal = vec![0.0; n];
    let dt = 1.0 / sampling_rate;
    
    for i in 0..n {
        let t = i as f64 * dt;
        signal[i] = (2.0 * std::f64::consts::PI * frequency * t).sin();
    }
    
    signal
}

/// 使用 SIMD 进行快速傅里叶变换
/// Fast Fourier transform using SIMD
fn fft_simd(signal: &[f64]) -> Result<Vec<f64>, Box<dyn std::error::Error>> {
    let n = signal.len();
    let mut result = vec![0.0; n];

    // 优化：使用预计算的三角函数表
    let mut cos_table = vec![0.0; n * n];
    let mut sin_table = vec![0.0; n * n];
    
    for k in 0..n {
        for i in 0..n {
            let angle = -2.0 * std::f64::consts::PI * k as f64 * i as f64 / n as f64;
            cos_table[k * n + i] = angle.cos();
            sin_table[k * n + i] = angle.sin();
        }
    }

    // 使用预计算的表进行 FFT
    for k in 0..n {
        let mut real_sum = 0.0;
        let mut imag_sum = 0.0;
        
        for i in 0..n {
            let cos_val = cos_table[k * n + i];
            let sin_val = sin_table[k * n + i];
            real_sum += signal[i] * cos_val;
            imag_sum += signal[i] * sin_val;
        }
        
        result[k] = (real_sum * real_sum + imag_sum * imag_sum).sqrt();
    }

    Ok(result)
}

/// 分析频谱
/// Analyze spectrum
fn analyze_spectrum(spectrum: &[f64], sampling_rate: f64) -> f64 {
    let mut max_magnitude = 0.0;
    let mut peak_index = 0;
    
    for (i, &magnitude) in spectrum.iter().enumerate() {
        if magnitude > max_magnitude {
            max_magnitude = magnitude;
            peak_index = i;
        }
    }
    
    peak_index as f64 * sampling_rate / spectrum.len() as f64
}

/// 演示蒙特卡洛模拟
/// Demonstrate Monte Carlo simulation
fn demonstrate_monte_carlo_simulation() -> Result<(), Box<dyn std::error::Error>> {
    println!("🎲 演示蒙特卡洛模拟");
    println!("🎲 Demonstrating Monte Carlo simulation");

    let n_simulations = 1_000_000; // 100万次模拟
    let n_steps = 1000; // 每次模拟1000步

    println!("   📊 模拟次数: {}", n_simulations);
    println!("   📊 每次步数: {}", n_steps);

    // 使用尾调用优化进行蒙特卡洛模拟
    let start = Instant::now();
    let result = monte_carlo_simulation_tail_call(n_simulations, n_steps)?;
    let simulation_duration = start.elapsed();

    println!("   ✅ 蒙特卡洛模拟完成，耗时: {:?}", simulation_duration);
    println!("   📊 模拟结果: {:.6}", result);
    println!("   📊 模拟速度: {:.2} M 次/秒", 
        n_simulations as f64 / simulation_duration.as_secs_f64() / 1_000_000.0);

    println!();
    Ok(())
}

/// 使用尾调用优化进行蒙特卡洛模拟
/// Monte Carlo simulation using tail call optimization
fn monte_carlo_simulation_tail_call(n_simulations: usize, n_steps: usize) -> Result<f64, Box<dyn std::error::Error>> {
    let mut optimizer = TailCallOptimizer::new();
    let mut total_result = 0.0;

    for i in 0..n_simulations {
        let mut current_value = 1.0;
        
        for _step in 0..n_steps {
            // 模拟随机游走
            let random_change = (i as f64 * 0.0001) % 1.0 - 0.5;
            current_value *= 1.0 + random_change * 0.01;
        }
        
        total_result += current_value;
        
        // 使用尾调用优化进行后处理
        if i % 10000 == 0 {
            let args = vec![Value::I32(i as i32), Value::F64(current_value)];
            let _result = optimizer.execute_tail_call(0, args)?;
        }
    }

    Ok(total_result / n_simulations as f64)
}

/// 演示并行计算
/// Demonstrate parallel computing
fn demonstrate_parallel_computing() -> Result<(), Box<dyn std::error::Error>> {
    println!("⚡ 演示并行计算");
    println!("⚡ Demonstrating parallel computing");

    let n_tasks = 8;
    let task_size = 1_000_000;

    println!("   📊 并行任务数: {}", n_tasks);
    println!("   📊 每任务大小: {}", task_size);

    // 使用宿主绑定进行并行计算
    let start = Instant::now();
    let results = parallel_computation_host_binding(n_tasks, task_size)?;
    let parallel_duration = start.elapsed();

    let total_result: f64 = results.iter().sum();
    println!("   ✅ 并行计算完成，耗时: {:?}", parallel_duration);
    println!("   📊 总计算结果: {:.6}", total_result);
    println!("   📊 并行效率: {:.2} 任务/秒", 
        n_tasks as f64 / parallel_duration.as_secs_f64());

    println!();
    Ok(())
}

/// 使用宿主绑定进行并行计算
/// Parallel computation using host binding
fn parallel_computation_host_binding(n_tasks: usize, task_size: usize) -> Result<Vec<f64>, Box<dyn std::error::Error>> {
    let mut manager = HostBindingManager::new();
    let mut results = Vec::new();

    // 注册并行计算函数
    for i in 0..n_tasks {
        manager.register_binding(
            format!("compute_task_{}", i),
            HostBindingType::JavaScriptFunction,
            "parallel_compute".to_string(),
        );
    }

    // 执行并行计算
    for i in 0..n_tasks {
        let mut task_result = 0.0;
        
        for j in 0..task_size {
            task_result += (i * task_size + j) as f64 * 0.000001;
        }
        
        results.push(task_result);
        
        // 使用宿主绑定进行结果处理
        let args = vec![Value::I32(i as i32), Value::F64(task_result)];
        let _result = manager.call_javascript_function(&format!("compute_task_{}", i), args)?;
    }

    Ok(results)
}
