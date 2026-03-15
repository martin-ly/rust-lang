//! WASM 数学工具模块
//! 
//! 高性能数学计算，适合在浏览器中运行

use wasm_bindgen::prelude::*;

/// 向量2D
#[wasm_bindgen]
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Vec2 {
    pub x: f64,
    pub y: f64,
}

#[wasm_bindgen]
impl Vec2 {
    /// 创建新向量
    #[wasm_bindgen(constructor)]
    pub fn new(x: f64, y: f64) -> Self {
        Self { x, y }
    }
    
    /// 零向量
    pub fn zero() -> Self {
        Self { x: 0.0, y: 0.0 }
    }
    
    /// 向量加法
    pub fn add(&self, other: &Vec2) -> Vec2 {
        Vec2 {
            x: self.x + other.x,
            y: self.y + other.y,
        }
    }
    
    /// 向量减法
    pub fn sub(&self, other: &Vec2) -> Vec2 {
        Vec2 {
            x: self.x - other.x,
            y: self.y - other.y,
        }
    }
    
    /// 标量乘法
    pub fn scale(&self, scalar: f64) -> Vec2 {
        Vec2 {
            x: self.x * scalar,
            y: self.y * scalar,
        }
    }
    
    /// 点积
    pub fn dot(&self, other: &Vec2) -> f64 {
        self.x * other.x + self.y * other.y
    }
    
    /// 向量长度
    pub fn length(&self) -> f64 {
        (self.x * self.x + self.y * self.y).sqrt()
    }
    
    /// 归一化向量
    pub fn normalize(&self) -> Vec2 {
        let len = self.length();
        if len > 0.0 {
            self.scale(1.0 / len)
        } else {
            Vec2::zero()
        }
    }
    
    /// 到另一个向量的距离
    pub fn distance_to(&self, other: &Vec2) -> f64 {
        self.sub(other).length()
    }
}

/// 矩阵 2x2
#[wasm_bindgen]
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Mat2 {
    pub m00: f64,
    pub m01: f64,
    pub m10: f64,
    pub m11: f64,
}

#[wasm_bindgen]
impl Mat2 {
    /// 创建新矩阵
    #[wasm_bindgen(constructor)]
    pub fn new(m00: f64, m01: f64, m10: f64, m11: f64) -> Self {
        Self { m00, m01, m10, m11 }
    }
    
    /// 单位矩阵
    pub fn identity() -> Self {
        Self {
            m00: 1.0,
            m01: 0.0,
            m10: 0.0,
            m11: 1.0,
        }
    }
    
    /// 旋转矩阵
    pub fn rotation(angle_rad: f64) -> Self {
        let cos = angle_rad.cos();
        let sin = angle_rad.sin();
        Self {
            m00: cos,
            m01: -sin,
            m10: sin,
            m11: cos,
        }
    }
    
    /// 矩阵乘法
    pub fn mul(&self, other: &Mat2) -> Mat2 {
        Mat2 {
            m00: self.m00 * other.m00 + self.m01 * other.m10,
            m01: self.m00 * other.m01 + self.m01 * other.m11,
            m10: self.m10 * other.m00 + self.m11 * other.m10,
            m11: self.m10 * other.m01 + self.m11 * other.m11,
        }
    }
    
    /// 矩阵与向量乘法
    pub fn transform(&self, vec: &Vec2) -> Vec2 {
        Vec2 {
            x: self.m00 * vec.x + self.m01 * vec.y,
            y: self.m10 * vec.x + self.m11 * vec.y,
        }
    }
}

/// 快速傅里叶变换 (FFT) - 简化版本
/// 
/// 注意: 这是一个简化的 FFT 实现，用于演示
pub fn fft(input: &[f64]) -> Vec<(f64, f64)> {
    let n = input.len();
    if n <= 1 {
        return input.iter().map(|&x| (x, 0.0)).collect();
    }
    
    // 简化的 DFT 实现（实际应用应使用更高效的算法）
    let mut result = Vec::with_capacity(n);
    let pi = std::f64::consts::PI;
    
    for k in 0..n {
        let mut real = 0.0;
        let mut imag = 0.0;
        
        for (i, &x) in input.iter().enumerate() {
            let angle = -2.0 * pi * (k as f64) * (i as f64) / (n as f64);
            real += x * angle.cos();
            imag += x * angle.sin();
        }
        
        result.push((real, imag));
    }
    
    result
}

/// 计算数组平均值
#[wasm_bindgen]
pub fn mean(data: &[f64]) -> f64 {
    if data.is_empty() {
        return 0.0;
    }
    data.iter().sum::<f64>() / data.len() as f64
}

/// 计算标准差
#[wasm_bindgen]
pub fn std_dev(data: &[f64]) -> f64 {
    if data.len() < 2 {
        return 0.0;
    }
    
    let m = mean(data);
    let variance: f64 = data.iter().map(|&x| (x - m).powi(2)).sum::<f64>() / (data.len() as f64);
    variance.sqrt()
}

/// 线性回归结果
#[wasm_bindgen]
#[derive(Debug, Clone, Copy)]
pub struct LinearRegressionResult {
    pub slope: f64,
    pub intercept: f64,
    pub valid: bool,
}

/// 线性回归
/// 
/// 返回回归结果
#[wasm_bindgen]
pub fn linear_regression(x: &[f64], y: &[f64]) -> LinearRegressionResult {
    if x.len() != y.len() || x.len() < 2 {
        return LinearRegressionResult {
            slope: 0.0,
            intercept: 0.0,
            valid: false,
        };
    }
    
    let x_mean = mean(x);
    let y_mean = mean(y);
    
    let mut numerator = 0.0;
    let mut denominator = 0.0;
    
    for i in 0..x.len() {
        let dx = x[i] - x_mean;
        numerator += dx * (y[i] - y_mean);
        denominator += dx * dx;
    }
    
    if denominator == 0.0 {
        return LinearRegressionResult {
            slope: 0.0,
            intercept: 0.0,
            valid: false,
        };
    }
    
    let slope = numerator / denominator;
    let intercept = y_mean - slope * x_mean;
    
    LinearRegressionResult {
        slope,
        intercept,
        valid: true,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_vec2_operations() {
        let v1 = Vec2::new(1.0, 2.0);
        let v2 = Vec2::new(3.0, 4.0);
        
        let sum = v1.add(&v2);
        assert_eq!(sum.x, 4.0);
        assert_eq!(sum.y, 6.0);
        
        let dot = v1.dot(&v2);
        assert_eq!(dot, 11.0); // 1*3 + 2*4 = 11
    }
    
    #[test]
    fn test_mean() {
        let data = vec![1.0, 2.0, 3.0, 4.0, 5.0];
        assert_eq!(mean(&data), 3.0);
    }
    
    #[test]
    fn test_linear_regression() {
        let x = vec![1.0, 2.0, 3.0, 4.0, 5.0];
        let y = vec![2.0, 4.0, 6.0, 8.0, 10.0];
        
        let result = linear_regression(&x, &y);
        assert!(result.valid);
        assert!((result.slope - 2.0).abs() < 0.001);
        assert!(result.intercept.abs() < 0.001);
    }
}
