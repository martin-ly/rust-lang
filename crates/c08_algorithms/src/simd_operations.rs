//! Portable SIMD 向量化操作
//! Portable SIMD vector operation
//! This module demonstrates Rust vectorization ：
//! - `std::simd` (portable_simd): 跨平台 SIMD 抽象（需要 nightly feature `portable_simd`）
//!
//! ## 条件编译
//! ## condition
//!
//! - 启用 `portable_simd` feature 时，使用 `core::simd` 进行跨平台 SIMD 编程
//! - loweruse `std::arch::x86_64` SSE2/AVX implementation

#[cfg(feature = "portable_simd")]
pub mod portable {
    use core::simd::Simd;
    use std::simd::cmp::SimdPartialEq;

    /// SIMD 数组加法（portable_simd）
    /// 8-lane f32 SIMD （256-bit）， 8 element 。
    pub fn simd_array_add(a: &[f32], b: &[f32], result: &mut [f32]) {
        assert_eq!(a.len(), b.len());
        assert_eq!(a.len(), result.len());

        const LANES: usize = 8;
        let chunks = a.len() / LANES;

        for i in 0..chunks {
            let va = Simd::<f32, LANES>::from_slice(&a[i * LANES..]);
            let vb = Simd::<f32, LANES>::from_slice(&b[i * LANES..]);
            let vr = va + vb;
            vr.copy_to_slice(&mut result[i * LANES..]);
        }

        // 处理剩余元素（标量回退）
        for i in (chunks * LANES)..a.len() {
            result[i] = a[i] + b[i];
        }
    }

    /// SIMD 向量化搜索（线性查找等于目标值的索引）
    /// SIMD vectorization （line etc. goal ）
    pub fn simd_search(arr: &[f32], target: f32) -> Option<usize> {
        const LANES: usize = 8;
        let target_vec = Simd::<f32, LANES>::splat(target);
        let chunks = arr.len() / LANES;

        for i in 0..chunks {
            let v = Simd::<f32, LANES>::from_slice(&arr[i * LANES..]);
            let mask = v.simd_eq(target_vec);
            if mask.any() {
                // 找到第一个匹配
                let offset = mask.to_array().iter().position(|&x| x).unwrap_or(0);
                return Some(i * LANES + offset);
            }
        }

        // 剩余元素
        arr.iter()
            .enumerate()
            .skip(chunks * LANES)
            .find(|&(_, x)| (*x - target).abs() < f32::EPSILON)
            .map(|(i, _)| i)
    }
}

#[cfg(not(feature = "portable_simd"))]
pub mod fallback {
    //! 默认回退实现：使用平台特定 SIMD（x86_64 SSE2/AVX）或标量代码

    /// 数组加法（优先 AVX2，其次 SSE2，最后标量）
    /// （ AVX2，second SSE2，finally ）
    pub fn simd_array_add(a: &[f32], b: &[f32], result: &mut [f32]) {
        assert_eq!(a.len(), b.len());
        assert_eq!(a.len(), result.len());

        if cfg!(all(target_arch = "x86_64", target_feature = "avx2")) {
            unsafe {
                avx2_array_add(a, b, result);
            }
        } else if cfg!(all(target_arch = "x86_64", target_feature = "sse2")) {
            unsafe {
                sse2_array_add(a, b, result);
            }
        } else {
            // 纯标量回退
            for i in 0..a.len() {
                result[i] = a[i] + b[i];
            }
        }
    }

    /// AVX2 加速数组加法（256-bit，8x f32）
    /// AVX2 （256-bit，8x f32）
    ///
    /// # Safety
    ///
    /// 调用者必须确保 CPU 支持 AVX2。
    /// must CPU AVX2。
    #[cfg(target_arch = "x86_64")]
    #[target_feature(enable = "avx2")]
    unsafe fn avx2_array_add(a: &[f32], b: &[f32], result: &mut [f32]) {
        use std::arch::x86_64::*;
        let chunks = a.len() / 8;
        for i in 0..chunks {
            let va = unsafe { _mm256_loadu_ps(a.as_ptr().add(i * 8)) };
            let vb = unsafe { _mm256_loadu_ps(b.as_ptr().add(i * 8)) };
            let vr = _mm256_add_ps(va, vb);
            unsafe { _mm256_storeu_ps(result.as_mut_ptr().add(i * 8), vr) };
        }
        for i in (chunks * 8)..a.len() {
            result[i] = a[i] + b[i];
        }
    }

    /// SSE2 加速数组加法（128-bit，4x f32）
    /// SSE2 （128-bit，4x f32）
    ///
    /// # Safety
    ///
    /// 调用者必须确保 CPU 支持 SSE2。
    /// must CPU SSE2。
    #[cfg(target_arch = "x86_64")]
    #[target_feature(enable = "sse2")]
    unsafe fn sse2_array_add(a: &[f32], b: &[f32], result: &mut [f32]) {
        use std::arch::x86_64::*;
        let chunks = a.len() / 4;
        for i in 0..chunks {
            let va = unsafe { _mm_loadu_ps(a.as_ptr().add(i * 4)) };
            let vb = unsafe { _mm_loadu_ps(b.as_ptr().add(i * 4)) };
            let vr = _mm_add_ps(va, vb);
            unsafe { _mm_storeu_ps(result.as_mut_ptr().add(i * 4), vr) };
        }
        for i in (chunks * 4)..a.len() {
            result[i] = a[i] + b[i];
        }
    }

    /// 标量搜索
    pub fn simd_search(arr: &[f32], target: f32) -> Option<usize> {
        arr.iter().position(|&x| (x - target).abs() < f32::EPSILON)
    }
}

// ========== 统一接口 ==========

/// 向量化数组加法（portable_simd 启用时使用核心 SIMD 实现）
/// vectorization （portable_simd core SIMD ）
#[cfg(feature = "portable_simd")]
pub fn array_add(a: &[f32], b: &[f32], result: &mut [f32]) {
    portable::simd_array_add(a, b, result);
}

/// 向量化数组加法（回退实现）
#[cfg(not(feature = "portable_simd"))]
pub fn array_add(a: &[f32], b: &[f32], result: &mut [f32]) {
    fallback::simd_array_add(a, b, result);
}

/// 向量化搜索（portable_simd 启用时使用核心 SIMD 实现）
/// vectorization （portable_simd core SIMD ）
#[cfg(feature = "portable_simd")]
pub fn search(arr: &[f32], target: f32) -> Option<usize> {
    portable::simd_search(arr, target)
}

/// 向量化搜索（回退实现）
#[cfg(not(feature = "portable_simd"))]
pub fn search(arr: &[f32], target: f32) -> Option<usize> {
    fallback::simd_search(arr, target)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_array_add() {
        let a: Vec<f32> = (0..16).map(|i| i as f32).collect();
        let b: Vec<f32> = (0..16).map(|i| (i * 2) as f32).collect();
        let mut result = vec![0.0f32; 16];

        array_add(&a, &b, &mut result);

        for i in 0..16 {
            assert!((result[i] - (a[i] + b[i])).abs() < f32::EPSILON);
        }
    }

    #[test]
    fn test_search() {
        let arr = vec![1.0, 2.0, 3.0, 4.0, 5.0];
        assert_eq!(search(&arr, 3.0), Some(2));
        assert_eq!(search(&arr, 99.0), None);
    }

    #[test]
    fn test_array_add_odd_length() {
        let a: Vec<f32> = (0..5).map(|i| i as f32).collect();
        let b: Vec<f32> = (0..5).map(|i| (i + 1) as f32).collect();
        let mut result = vec![0.0f32; 5];
        array_add(&a, &b, &mut result);
        for i in 0..5 {
            assert!((result[i] - (a[i] + b[i])).abs() < f32::EPSILON);
        }
    }
}
