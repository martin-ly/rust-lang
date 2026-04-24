//! Portable SIMD 向量化操作
//!
//! 本模块展示 Rust 的向量化编程：
//! - `std::simd` (portable_simd): 跨平台 SIMD 抽象（需要 nightly feature `portable_simd`）
//! - `std::arch`: 平台特定的 SIMD 指令（stable）
//!
//! ## 条件编译
//!
//! - 启用 `portable_simd` feature 时，使用 `core::simd` 进行跨平台 SIMD 编程
//! - 默认情况下，使用 `std::arch::x86_64` 的 SSE2/AVX 回退或纯标量实现

#[cfg(feature = "portable_simd")]
pub mod portable {
    use core::simd::Simd;
    use std::simd::cmp::SimdPartialEq;

    /// SIMD 数组加法（portable_simd）
    ///
    /// 使用 8-lane f32 SIMD（256-bit），一次处理 8 个元素。
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
        for i in (chunks * LANES)..arr.len() {
            if (arr[i] - target).abs() < f32::EPSILON {
                return Some(i);
            }
        }
        None
    }
}

#[cfg(not(feature = "portable_simd"))]
pub mod fallback {
    //! 默认回退实现：使用平台特定 SIMD（x86_64 SSE2/AVX）或标量代码

    /// 数组加法（优先 AVX2，其次 SSE2，最后标量）
    pub fn simd_array_add(a: &[f32], b: &[f32], result: &mut [f32]) {
        assert_eq!(a.len(), b.len());
        assert_eq!(a.len(), result.len());

        if cfg!(all(target_arch = "x86_64", target_feature = "avx2")) {
            unsafe { avx2_array_add(a, b, result); }
        } else if cfg!(all(target_arch = "x86_64", target_feature = "sse2")) {
            unsafe { sse2_array_add(a, b, result); }
        } else {
            // 纯标量回退
            for i in 0..a.len() {
                result[i] = a[i] + b[i];
            }
        }
    }

    /// AVX2 加速数组加法（256-bit，8x f32）
    ///
    /// # Safety
    ///
    /// 调用者必须确保 CPU 支持 AVX2。
    #[cfg(target_arch = "x86_64")]
    #[target_feature(enable = "avx2")]
    unsafe fn avx2_array_add(a: &[f32], b: &[f32], result: &mut [f32]) {
        use std::arch::x86_64::*;
        let chunks = a.len() / 8;
        for i in 0..chunks {
            let va = unsafe { _mm256_loadu_ps(a.as_ptr().add(i * 8)) };
            let vb = unsafe { _mm256_loadu_ps(b.as_ptr().add(i * 8)) };
            let vr = unsafe { _mm256_add_ps(va, vb) };
            unsafe { _mm256_storeu_ps(result.as_mut_ptr().add(i * 8), vr) };
        }
        for i in (chunks * 8)..a.len() {
            result[i] = a[i] + b[i];
        }
    }

    /// SSE2 加速数组加法（128-bit，4x f32）
    ///
    /// # Safety
    ///
    /// 调用者必须确保 CPU 支持 SSE2。
    #[cfg(target_arch = "x86_64")]
    #[target_feature(enable = "sse2")]
    unsafe fn sse2_array_add(a: &[f32], b: &[f32], result: &mut [f32]) {
        use std::arch::x86_64::*;
        let chunks = a.len() / 4;
        for i in 0..chunks {
            let va = unsafe { _mm_loadu_ps(a.as_ptr().add(i * 4)) };
            let vb = unsafe { _mm_loadu_ps(b.as_ptr().add(i * 4)) };
            let vr = unsafe { _mm_add_ps(va, vb) };
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
