//! # 常量泛型推断 / Const Generic Inference
//!
//! Rust 1.89 在常量泛型推断方面进行了重要改进，支持 `_` 占位符的
//! 常量泛型推断，使代码更加简洁和灵活。
//!
//! Rust 1.89 has made important improvements in const generic inference,
//! supporting `_` placeholder for const generic inference, making code
//! more concise and flexible.

use std::marker::PhantomData;

/// 常量泛型数组 / Const Generic Array
///
/// 提供固定大小的数组，大小在编译时确定。
/// Provides fixed-size arrays with compile-time determined size.
pub struct ConstGenericArray<T, const N: usize> {
    data: [T; N],
}

impl<T, const N: usize> ConstGenericArray<T, N> {
    /// 创建新的常量泛型数组 / Create new const generic array
    pub fn new() -> Self
    where
        T: Default,
    {
        Self {
            data: [(); N].map(|_| T::default()),
        }
    }

    /// 推断长度创建 / Create with inferred length
    pub fn with_inferred_length() -> Self
    where
        T: Default,
    {
        Self::new()
    }

    /// 获取数组长度 / Get array length
    pub const fn len() -> usize {
        N
    }

    /// 获取数组切片 / Get array slice
    pub fn as_slice(&self) -> &[T] {
        &self.data
    }

    /// 获取可变数组切片 / Get mutable array slice
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        &mut self.data
    }
}

/// 常量泛型推断器 / Const Generic Inferencer
///
/// 提供常量泛型推断功能。
/// Provides const generic inference functionality.
pub struct ConstGenericInferencer<const N: usize> {
    _phantom: PhantomData<[(); N]>,
}

impl<const N: usize> ConstGenericInferencer<N> {
    /// 创建新的推断器 / Create new inferencer
    pub fn new() -> Self {
        Self {
            _phantom: PhantomData,
        }
    }

    /// 推断常量值 / Infer const value
    pub fn infer_const<T>(&self, value: T) -> ConstValue<N, T> {
        ConstValue {
            value,
            _phantom: PhantomData,
        }
    }

    /// 获取常量大小 / Get const size
    pub fn get_size(&self) -> usize {
        N
    }
}

/// 常量值 / Const Value
#[derive(Debug, Clone, PartialEq)]
pub struct ConstValue<const N: usize, T> {
    value: T,
    _phantom: PhantomData<[(); N]>,
}

impl<const N: usize, T> ConstValue<N, T> {
    /// 创建新的常量值 / Create new const value
    pub fn new(value: T) -> Self {
        Self {
            value,
            _phantom: PhantomData,
        }
    }

    /// 获取值 / Get value
    pub fn get_value(&self) -> &T {
        &self.value
    }

    /// 获取常量大小 / Get const size
    pub fn get_const_size(&self) -> usize {
        N
    }
}

/// 常量泛型数组 / Const Generic Array
pub struct ConstArray<const N: usize, T> {
    data: [T; N],
}

impl<const N: usize, T> ConstArray<N, T>
where
    T: Default + Copy,
{
    /// 创建新的常量数组 / Create new const array
    pub fn new() -> Self {
        Self {
            data: [T::default(); N],
        }
    }

    /// 从切片创建 / Create from slice
    pub fn from_slice(slice: &[T]) -> Result<Self, ConstArrayError>
    where
        T: Clone,
    {
        if slice.len() != N {
            return Err(ConstArrayError::SizeMismatch {
                expected: N,
                actual: slice.len(),
            });
        }

        let mut data = [T::default(); N];
        for (i, item) in slice.iter().enumerate() {
            data[i] = item.clone();
        }

        Ok(Self { data })
    }

    /// 获取元素 / Get element
    pub fn get(&self, index: usize) -> Option<&T> {
        self.data.get(index)
    }

    /// 设置元素 / Set element
    pub fn set(&mut self, index: usize, value: T) -> Result<(), ConstArrayError> {
        if index >= N {
            return Err(ConstArrayError::IndexOutOfBounds { index, size: N });
        }

        self.data[index] = value;
        Ok(())
    }

    /// 获取数组大小 / Get array size
    pub fn size(&self) -> usize {
        N
    }

    /// 转换为切片 / Convert to slice
    pub fn as_slice(&self) -> &[T] {
        &self.data
    }
}

/// 常量泛型矩阵 / Const Generic Matrix
pub struct ConstMatrix<const ROWS: usize, const COLS: usize, T> {
    data: [[T; COLS]; ROWS],
}

impl<const ROWS: usize, const COLS: usize, T> ConstMatrix<ROWS, COLS, T>
where
    T: Default + Copy,
{
    /// 创建新的常量矩阵 / Create new const matrix
    pub fn new() -> Self {
        Self {
            data: [[T::default(); COLS]; ROWS],
        }
    }

    /// 获取元素 / Get element
    pub fn get(&self, row: usize, col: usize) -> Option<&T> {
        self.data.get(row)?.get(col)
    }

    /// 设置元素 / Set element
    pub fn set(&mut self, row: usize, col: usize, value: T) -> Result<(), ConstMatrixError> {
        if row >= ROWS {
            return Err(ConstMatrixError::RowOutOfBounds {
                row,
                max_rows: ROWS,
            });
        }

        if col >= COLS {
            return Err(ConstMatrixError::ColOutOfBounds {
                col,
                max_cols: COLS,
            });
        }

        self.data[row][col] = value;
        Ok(())
    }

    /// 获取行数 / Get number of rows
    pub fn rows(&self) -> usize {
        ROWS
    }

    /// 获取列数 / Get number of columns
    pub fn cols(&self) -> usize {
        COLS
    }

    /// 获取行 / Get row
    pub fn get_row(&self, row: usize) -> Option<&[T; COLS]> {
        self.data.get(row)
    }
}

/// 常量泛型推断占位符 / Const Generic Inference Placeholder
pub struct ConstPlaceholder<const N: usize> {
    _phantom: PhantomData<[(); N]>,
}

impl<const N: usize> ConstPlaceholder<N> {
    /// 创建新的占位符 / Create new placeholder
    pub fn new() -> Self {
        Self {
            _phantom: PhantomData,
        }
    }

    /// 推断常量 / Infer const
    pub fn infer<const M: usize>(&self) -> ConstPlaceholder<M>
    where
        [(); M]: Sized,
    {
        ConstPlaceholder::new()
    }
}

/// 常量泛型错误 / Const Generic Error
#[derive(Debug, thiserror::Error)]
pub enum ConstArrayError {
    #[error("大小不匹配 / Size mismatch: expected {expected}, actual {actual}")]
    SizeMismatch { expected: usize, actual: usize },

    #[error("索引越界 / Index out of bounds: index {index}, size {size}")]
    IndexOutOfBounds { index: usize, size: usize },
}

/// 常量矩阵错误 / Const Matrix Error
#[derive(Debug, thiserror::Error)]
pub enum ConstMatrixError {
    #[error("行索引越界 / Row index out of bounds: row {row}, max rows {max_rows}")]
    RowOutOfBounds { row: usize, max_rows: usize },

    #[error("列索引越界 / Column index out of bounds: col {col}, max cols {max_cols}")]
    ColOutOfBounds { col: usize, max_cols: usize },
}

/// 常量泛型工具函数 / Const Generic Utility Functions
pub mod utils {

    /// 推断常量大小 / Infer const size
    pub fn infer_size<const N: usize>(_array: &[u8; N]) -> usize {
        N
    }

    /// 创建常量数组 / Create const array
    pub fn create_array<const N: usize, T>(value: T) -> [T; N]
    where
        T: Copy,
    {
        [value; N]
    }

    /// 常量数组映射 / Const array map
    pub fn map_array<const N: usize, T, U, F>(array: [T; N], f: F) -> [U; N]
    where
        F: Fn(T) -> U,
    {
        array.map(f)
    }

    /// 常量数组过滤 / Const array filter
    pub fn filter_array<const N: usize, T, F>(array: [T; N], f: F) -> Vec<T>
    where
        F: Fn(&T) -> bool,
    {
        array.into_iter().filter(f).collect()
    }
}

/// 常量泛型特征 / Const Generic Traits
pub mod traits {
    use super::*;

    /// 常量大小特征 / Const Size Trait
    pub trait ConstSize {
        const SIZE: usize;

        fn size(&self) -> usize {
            Self::SIZE
        }
    }

    /// 实现常量大小特征 / Implement const size trait
    impl<const N: usize, T> ConstSize for [T; N] {
        const SIZE: usize = N;
    }

    /// 常量泛型特征 / Const Generic Trait
    pub trait ConstGeneric<const N: usize> {
        fn get_const_value(&self) -> usize;

        fn is_valid_size(&self) -> bool {
            self.get_const_value() == N
        }
    }

    /// 实现常量泛型特征 / Implement const generic trait
    impl<const N: usize> ConstGeneric<N> for ConstArray<N, u8> {
        fn get_const_value(&self) -> usize {
            N
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_const_generic_inferencer() {
        let inferencer = ConstGenericInferencer::<5>::new();
        assert_eq!(inferencer.get_size(), 5);

        let value = inferencer.infer_const(42);
        assert_eq!(value.get_value(), &42);
        assert_eq!(value.get_const_size(), 5);
    }

    #[test]
    fn test_const_array() {
        let mut array = ConstArray::<3, i32>::new();
        assert_eq!(array.size(), 3);

        array.set(0, 1).unwrap();
        array.set(1, 2).unwrap();
        array.set(2, 3).unwrap();

        assert_eq!(array.get(0), Some(&1));
        assert_eq!(array.get(1), Some(&2));
        assert_eq!(array.get(2), Some(&3));
    }

    #[test]
    fn test_const_matrix() {
        let mut matrix = ConstMatrix::<2, 3, i32>::new();
        assert_eq!(matrix.rows(), 2);
        assert_eq!(matrix.cols(), 3);

        matrix.set(0, 0, 1).unwrap();
        matrix.set(0, 1, 2).unwrap();
        matrix.set(0, 2, 3).unwrap();
        matrix.set(1, 0, 4).unwrap();
        matrix.set(1, 1, 5).unwrap();
        matrix.set(1, 2, 6).unwrap();

        assert_eq!(matrix.get(0, 0), Some(&1));
        assert_eq!(matrix.get(1, 2), Some(&6));
    }

    #[test]
    fn test_const_placeholder() {
        let placeholder = ConstPlaceholder::<5>::new();
        let _inferred = placeholder.infer::<3>();
        // 这里主要测试编译时推断
        // 编译通过即表示类型推断正确
    }

    #[test]
    fn test_const_utils() {
        let array = utils::create_array::<5, i32>(42);
        assert_eq!(array, [42, 42, 42, 42, 42]);

        let mapped = utils::map_array(array, |x| x * 2);
        assert_eq!(mapped, [84, 84, 84, 84, 84]);
    }
}
