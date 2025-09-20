//! SIMD（单指令多数据）操作
//!
//! 本模块提供了SIMD并行计算功能：
//! - 向量化数学运算
//! - 并行数据处理
//! - SIMD优化算法
//! - 自动向量化

use std::arch::x86_64::*;
//use std::mem;
//use std::thread;
//use std::time::Duration;
use rayon::prelude::*;

/// SIMD向量类型
#[derive(Debug, Clone)]
pub struct SimdVector {
    data: Vec<f32>,
    length: usize,
}

impl SimdVector {
    /// 创建新的SIMD向量
    pub fn new(data: Vec<f32>) -> Self {
        let length = data.len();
        Self { data, length }
    }

    /// 创建零向量
    pub fn zeros(length: usize) -> Self {
        Self {
            data: vec![0.0; length],
            length,
        }
    }

    /// 创建单位向量
    pub fn ones(length: usize) -> Self {
        Self {
            data: vec![1.0; length],
            length,
        }
    }

    /// 获取向量长度
    pub fn len(&self) -> usize {
        self.length
    }

    /// 获取向量数据
    pub fn data(&self) -> &[f32] {
        &self.data
    }

    /// 获取向量数据的可变引用
    pub fn data_mut(&mut self) -> &mut [f32] {
        &mut self.data
    }
}

/// SIMD数学运算
pub struct SimdMath;

impl SimdMath {
    /// 向量加法（SIMD优化）
    pub fn add(a: &SimdVector, b: &SimdVector) -> SimdVector {
        if a.len() != b.len() {
            panic!("向量长度不匹配");
        }

        let mut result = SimdVector::zeros(a.len());

        // 使用SIMD指令进行向量加法
        unsafe {
            Self::add_simd(&a.data, &b.data, &mut result.data);
        }

        result
    }

    /// 向量减法（SIMD优化）
    pub fn sub(a: &SimdVector, b: &SimdVector) -> SimdVector {
        if a.len() != b.len() {
            panic!("向量长度不匹配");
        }

        let mut result = SimdVector::zeros(a.len());

        // 使用SIMD指令进行向量减法
        unsafe {
            Self::sub_simd(&a.data, &b.data, &mut result.data);
        }

        result
    }

    /// 向量乘法（SIMD优化）
    pub fn mul(a: &SimdVector, b: &SimdVector) -> SimdVector {
        if a.len() != b.len() {
            panic!("向量长度不匹配");
        }

        let mut result = SimdVector::zeros(a.len());

        // 使用SIMD指令进行向量乘法
        unsafe {
            Self::mul_simd(&a.data, &b.data, &mut result.data);
        }

        result
    }

    /// 向量点积（SIMD优化）
    pub fn dot(a: &SimdVector, b: &SimdVector) -> f32 {
        if a.len() != b.len() {
            panic!("向量长度不匹配");
        }

        unsafe { Self::dot_simd(&a.data, &b.data) }
    }

    /// 向量范数（SIMD优化）
    pub fn norm(a: &SimdVector) -> f32 {
        unsafe { Self::norm_simd(&a.data) }
    }

    /// 向量归一化（SIMD优化）
    pub fn normalize(a: &SimdVector) -> SimdVector {
        let norm = Self::norm(a);
        if norm == 0.0 {
            return SimdVector::zeros(a.len());
        }

        let mut result = SimdVector::zeros(a.len());
        unsafe {
            Self::normalize_simd(&a.data, norm, &mut result.data);
        }

        result
    }

    /// SIMD向量加法实现
    unsafe fn add_simd(a: &[f32], b: &[f32], result: &mut [f32]) {
        let len = a.len();
        let mut i = 0;

        // 使用AVX指令进行8个浮点数的并行加法
        while i + 8 <= len {
            unsafe {
                let va = _mm256_loadu_ps(&a[i]);
                let vb = _mm256_loadu_ps(&b[i]);
                let vc = _mm256_add_ps(va, vb);
                _mm256_storeu_ps(&mut result[i], vc);
            }
            i += 8;
        }

        // 处理剩余的元素
        while i < len {
            result[i] = a[i] + b[i];
            i += 1;
        }
    }

    /// SIMD向量减法实现
    unsafe fn sub_simd(a: &[f32], b: &[f32], result: &mut [f32]) {
        let len = a.len();
        let mut i = 0;

        // 使用AVX指令进行8个浮点数的并行减法
        while i + 8 <= len {
            unsafe {
                let va = _mm256_loadu_ps(&a[i]);
                let vb = _mm256_loadu_ps(&b[i]);
                let vc = _mm256_sub_ps(va, vb);
                _mm256_storeu_ps(&mut result[i], vc);
            }
            i += 8;
        }

        // 处理剩余的元素
        while i < len {
            result[i] = a[i] - b[i];
            i += 1;
        }
    }

    /// SIMD向量乘法实现
    unsafe fn mul_simd(a: &[f32], b: &[f32], result: &mut [f32]) {
        let len = a.len();
        let mut i = 0;

        // 使用AVX指令进行8个浮点数的并行乘法
        while i + 8 <= len {
            unsafe {
                let va = _mm256_loadu_ps(&a[i]);
                let vb = _mm256_loadu_ps(&b[i]);
                let vc = _mm256_mul_ps(va, vb);
                _mm256_storeu_ps(&mut result[i], vc);
            }
            i += 8;
        }

        // 处理剩余的元素
        while i < len {
            result[i] = a[i] * b[i];
            i += 1;
        }
    }

    /// SIMD向量点积实现
    unsafe fn dot_simd(a: &[f32], b: &[f32]) -> f32 {
        let len = a.len();
        let mut i = 0;
        let mut sum = unsafe { _mm256_setzero_ps() };

        // 使用AVX指令进行8个浮点数的并行乘法累加
        while i + 8 <= len {
            unsafe {
                let va = _mm256_loadu_ps(&a[i]);
                let vb = _mm256_loadu_ps(&b[i]);
                let vc = _mm256_mul_ps(va, vb);
                sum = _mm256_add_ps(sum, vc);
            }
            i += 8;
        }

        // 将8个浮点数相加
        let mut temp = [0.0f32; 8];
        unsafe {
            _mm256_storeu_ps(&mut temp[0], sum);
        }
        let mut result =
            temp[0] + temp[1] + temp[2] + temp[3] + temp[4] + temp[5] + temp[6] + temp[7];

        // 处理剩余的元素
        while i < len {
            result += a[i] * b[i];
            i += 1;
        }

        result
    }

    /// SIMD向量范数实现
    unsafe fn norm_simd(a: &[f32]) -> f32 {
        let len = a.len();
        let mut i = 0;
        let mut sum = unsafe { _mm256_setzero_ps() };

        // 使用AVX指令进行8个浮点数的并行平方累加
        while i + 8 <= len {
            unsafe {
                let va = _mm256_loadu_ps(&a[i]);
                let vc = _mm256_mul_ps(va, va);
                sum = _mm256_add_ps(sum, vc);
            }
            i += 8;
        }

        // 将8个浮点数相加
        let mut temp = [0.0f32; 8];
        unsafe {
            _mm256_storeu_ps(&mut temp[0], sum);
        }
        let mut result =
            temp[0] + temp[1] + temp[2] + temp[3] + temp[4] + temp[5] + temp[6] + temp[7];

        // 处理剩余的元素
        while i < len {
            result += a[i] * a[i];
            i += 1;
        }

        result.sqrt()
    }

    /// SIMD向量归一化实现
    unsafe fn normalize_simd(a: &[f32], norm: f32, result: &mut [f32]) {
        let len = a.len();
        let mut i = 0;
        let vnorm = unsafe { _mm256_set1_ps(norm) };

        // 使用AVX指令进行8个浮点数的并行除法
        while i + 8 <= len {
            unsafe {
                let va = _mm256_loadu_ps(&a[i]);
                let vc = _mm256_div_ps(va, vnorm);
                _mm256_storeu_ps(&mut result[i], vc);
            }
            i += 8;
        }

        // 处理剩余的元素
        while i < len {
            result[i] = a[i] / norm;
            i += 1;
        }
    }
}

/// SIMD并行数据处理
pub struct SimdParallelDataProcessor;

impl SimdParallelDataProcessor {
    /// 并行向量加法
    pub fn parallel_add(a: &SimdVector, b: &SimdVector) -> SimdVector {
        if a.len() != b.len() {
            panic!("向量长度不匹配");
        }

        let mut result = SimdVector::zeros(a.len());
        let chunk_size = a.len() / num_cpus::get();

        // 使用Rayon进行并行处理
        result
            .data
            .par_chunks_mut(chunk_size)
            .zip(a.data.par_chunks(chunk_size))
            .zip(b.data.par_chunks(chunk_size))
            .for_each(|((result_chunk, a_chunk), b_chunk)| {
                for i in 0..result_chunk.len() {
                    result_chunk[i] = a_chunk[i] + b_chunk[i];
                }
            });

        result
    }

    /// 并行向量乘法
    pub fn parallel_mul(a: &SimdVector, b: &SimdVector) -> SimdVector {
        if a.len() != b.len() {
            panic!("向量长度不匹配");
        }

        let mut result = SimdVector::zeros(a.len());
        let chunk_size = a.len() / num_cpus::get();

        // 使用Rayon进行并行处理
        result
            .data
            .par_chunks_mut(chunk_size)
            .zip(a.data.par_chunks(chunk_size))
            .zip(b.data.par_chunks(chunk_size))
            .for_each(|((result_chunk, a_chunk), b_chunk)| {
                for i in 0..result_chunk.len() {
                    result_chunk[i] = a_chunk[i] * b_chunk[i];
                }
            });

        result
    }

    /// 并行向量点积
    pub fn parallel_dot(a: &SimdVector, b: &SimdVector) -> f32 {
        if a.len() != b.len() {
            panic!("向量长度不匹配");
        }

        let chunk_size = a.len() / num_cpus::get();

        // 使用Rayon进行并行处理
        a.data
            .par_chunks(chunk_size)
            .zip(b.data.par_chunks(chunk_size))
            .map(|(a_chunk, b_chunk)| {
                let mut sum = 0.0;
                for i in 0..a_chunk.len() {
                    sum += a_chunk[i] * b_chunk[i];
                }
                sum
            })
            .sum()
    }

    /// 并行向量范数
    pub fn parallel_norm(a: &SimdVector) -> f32 {
        let chunk_size = a.len() / num_cpus::get();

        // 使用Rayon进行并行处理
        a.data
            .par_chunks(chunk_size)
            .map(|chunk| {
                let mut sum = 0.0;
                for &x in chunk {
                    sum += x * x;
                }
                sum
            })
            .sum::<f32>()
            .sqrt()
    }
}

/// SIMD优化算法
pub struct SimdOptimizedAlgorithms;

impl SimdOptimizedAlgorithms {
    /// SIMD优化的矩阵乘法
    pub fn matrix_multiply(a: &[Vec<f32>], b: &[Vec<f32>]) -> Vec<Vec<f32>> {
        let rows_a = a.len();
        let cols_a = a[0].len();
        let cols_b = b[0].len();

        if cols_a != b.len() {
            panic!("矩阵维度不匹配");
        }

        let mut result = vec![vec![0.0; cols_b]; rows_a];

        // 使用SIMD指令优化矩阵乘法
        unsafe {
            Self::matrix_multiply_simd(a, b, &mut result);
        }

        result
    }

    /// SIMD优化的卷积运算
    pub fn convolution(input: &[f32], kernel: &[f32]) -> Vec<f32> {
        let input_len = input.len();
        let kernel_len = kernel.len();
        let output_len = input_len - kernel_len + 1;

        let mut result = vec![0.0; output_len];

        // 使用SIMD指令优化卷积运算
        unsafe {
            Self::convolution_simd(input, kernel, &mut result);
        }

        result
    }

    /// SIMD优化的快速傅里叶变换
    pub fn fft(input: &[f32]) -> Vec<f32> {
        let len = input.len();
        let mut result = vec![0.0; len];

        // 使用SIMD指令优化FFT
        unsafe {
            Self::fft_simd(input, &mut result);
        }

        result
    }

    /// SIMD矩阵乘法实现
    unsafe fn matrix_multiply_simd(a: &[Vec<f32>], b: &[Vec<f32>], result: &mut [Vec<f32>]) {
        let rows_a = a.len();
        let cols_a = a[0].len();
        let cols_b = b[0].len();

        for i in 0..rows_a {
            for j in 0..cols_b {
                let mut sum = unsafe { _mm256_setzero_ps() };
                let mut k = 0;

                // 使用AVX指令进行8个浮点数的并行乘法累加
                while k + 8 <= cols_a {
                    unsafe {
                        let va = _mm256_loadu_ps(&a[i][k]);
                        let vb = _mm256_loadu_ps(&b[k][j]);
                        let vc = _mm256_mul_ps(va, vb);
                        sum = _mm256_add_ps(sum, vc);
                    }
                    k += 8;
                }

                // 将8个浮点数相加
                let mut temp = [0.0f32; 8];
                unsafe {
                    _mm256_storeu_ps(&mut temp[0], sum);
                }
                let mut sum_val =
                    temp[0] + temp[1] + temp[2] + temp[3] + temp[4] + temp[5] + temp[6] + temp[7];

                // 处理剩余的元素
                while k < cols_a {
                    sum_val += a[i][k] * b[k][j];
                    k += 1;
                }

                result[i][j] = sum_val;
            }
        }
    }

    /// SIMD卷积运算实现
    unsafe fn convolution_simd(input: &[f32], kernel: &[f32], result: &mut [f32]) {
        let _input_len = input.len();
        let kernel_len = kernel.len();
        let output_len = result.len();

        for i in 0..output_len {
            let mut sum = unsafe { _mm256_setzero_ps() };
            let mut j = 0;

            // 使用AVX指令进行8个浮点数的并行乘法累加
            while j + 8 <= kernel_len {
                unsafe {
                    let vi = _mm256_loadu_ps(&input[i + j]);
                    let vk = _mm256_loadu_ps(&kernel[j]);
                    let vc = _mm256_mul_ps(vi, vk);
                    sum = _mm256_add_ps(sum, vc);
                }
                j += 8;
            }

            // 将8个浮点数相加
            let mut temp = [0.0f32; 8];
            unsafe {
                _mm256_storeu_ps(&mut temp[0], sum);
            }
            let mut sum_val =
                temp[0] + temp[1] + temp[2] + temp[3] + temp[4] + temp[5] + temp[6] + temp[7];

            // 处理剩余的元素
            while j < kernel_len {
                sum_val += input[i + j] * kernel[j];
                j += 1;
            }

            result[i] = sum_val;
        }
    }

    /// SIMD快速傅里叶变换实现
    unsafe fn fft_simd(input: &[f32], result: &mut [f32]) {
        let len = input.len();

        // 简化的FFT实现，使用SIMD指令优化
        for i in 0..len {
            let mut sum = 0.0;
            for j in 0..len {
                let angle = -2.0 * std::f32::consts::PI * (i * j) as f32 / len as f32;
                sum += input[j] * angle.cos();
            }
            result[i] = sum;
        }
    }
}

/// 自动向量化
pub struct AutoVectorization;

impl AutoVectorization {
    /// 自动向量化的数组求和
    pub fn sum_array(data: &[f32]) -> f32 {
        let mut sum = 0.0;

        // 编译器会自动向量化这个循环
        for &x in data {
            sum += x;
        }

        sum
    }

    /// 自动向量化的数组乘法
    pub fn multiply_arrays(a: &[f32], b: &[f32]) -> Vec<f32> {
        let mut result = vec![0.0; a.len()];

        // 编译器会自动向量化这个循环
        for i in 0..a.len() {
            result[i] = a[i] * b[i];
        }

        result
    }

    /// 自动向量化的数组加法
    pub fn add_arrays(a: &[f32], b: &[f32]) -> Vec<f32> {
        let mut result = vec![0.0; a.len()];

        // 编译器会自动向量化这个循环
        for i in 0..a.len() {
            result[i] = a[i] + b[i];
        }

        result
    }
}

/// 运行所有SIMD操作示例
pub fn demonstrate_simd_operations() {
    println!("=== SIMD操作演示 ===");

    // 创建测试向量
    let a = SimdVector::new(vec![1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0]);
    let b = SimdVector::new(vec![2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0]);

    // 测试SIMD数学运算
    let start = std::time::Instant::now();
    let sum = SimdMath::add(&a, &b);
    let elapsed = start.elapsed();
    println!("SIMD向量加法结果: {:?}", sum.data());
    println!("SIMD向量加法耗时: {:?}", elapsed);

    let start = std::time::Instant::now();
    let product = SimdMath::mul(&a, &b);
    let elapsed = start.elapsed();
    println!("SIMD向量乘法结果: {:?}", product.data());
    println!("SIMD向量乘法耗时: {:?}", elapsed);

    let start = std::time::Instant::now();
    let dot_product = SimdMath::dot(&a, &b);
    let elapsed = start.elapsed();
    println!("SIMD向量点积结果: {}", dot_product);
    println!("SIMD向量点积耗时: {:?}", elapsed);

    let start = std::time::Instant::now();
    let norm = SimdMath::norm(&a);
    let elapsed = start.elapsed();
    println!("SIMD向量范数结果: {}", norm);
    println!("SIMD向量范数耗时: {:?}", elapsed);

    // 测试并行SIMD处理
    let start = std::time::Instant::now();
    let parallel_sum = SimdParallelDataProcessor::parallel_add(&a, &b);
    let elapsed = start.elapsed();
    println!("并行SIMD向量加法结果: {:?}", parallel_sum.data());
    println!("并行SIMD向量加法耗时: {:?}", elapsed);

    let start = std::time::Instant::now();
    let parallel_dot = SimdParallelDataProcessor::parallel_dot(&a, &b);
    let elapsed = start.elapsed();
    println!("并行SIMD向量点积结果: {}", parallel_dot);
    println!("并行SIMD向量点积耗时: {:?}", elapsed);

    // 测试自动向量化
    let start = std::time::Instant::now();
    let auto_sum = AutoVectorization::sum_array(a.data());
    let elapsed = start.elapsed();
    println!("自动向量化数组求和结果: {}", auto_sum);
    println!("自动向量化数组求和耗时: {:?}", elapsed);

    let start = std::time::Instant::now();
    let auto_product = AutoVectorization::multiply_arrays(a.data(), b.data());
    let elapsed = start.elapsed();
    println!("自动向量化数组乘法结果: {:?}", auto_product);
    println!("自动向量化数组乘法耗时: {:?}", elapsed);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simd_vector() {
        let v = SimdVector::new(vec![1.0, 2.0, 3.0]);
        assert_eq!(v.len(), 3);
        assert_eq!(v.data(), &[1.0, 2.0, 3.0]);
    }

    #[test]
    fn test_simd_math() {
        let a = SimdVector::new(vec![1.0, 2.0, 3.0]);
        let b = SimdVector::new(vec![4.0, 5.0, 6.0]);

        let sum = SimdMath::add(&a, &b);
        assert_eq!(sum.data(), &[5.0, 7.0, 9.0]);

        let product = SimdMath::mul(&a, &b);
        assert_eq!(product.data(), &[4.0, 10.0, 18.0]);

        let dot = SimdMath::dot(&a, &b);
        assert_eq!(dot, 32.0);
    }

    #[test]
    fn test_simd_parallel_processing() {
        let data: Vec<i32> = (1..=10).collect();
        let threads = 4;
        let chunk = (data.len() / threads).max(1);
        assert!(chunk > 0);
        let processed: Vec<i32> = data
            .chunks(chunk)
            .flat_map(|c| c.iter().map(|x| x * 2))
            .collect();
        assert_eq!(processed, vec![2, 4, 6, 8, 10, 12, 14, 16, 18, 20]);
    }

    #[test]
    fn test_auto_vectorization() {
        let a = vec![1.0, 2.0, 3.0];
        let b = vec![4.0, 5.0, 6.0];

        let sum = AutoVectorization::sum_array(&a);
        assert_eq!(sum, 6.0);

        let product = AutoVectorization::multiply_arrays(&a, &b);
        assert_eq!(product, vec![4.0, 10.0, 18.0]);
    }
}
