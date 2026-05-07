//! Rust 1.95.0 所有权与内存安全新特性实现模块
//!
//! 本模块展示了 Rust 1.95.0 在所有权、借用和内存安全方面的关键增强：
//! - `MaybeUninit<[T; N]>` ↔ `[MaybeUninit<T>; N]` 互转 ⭐
//! - `Cell<[T; N]>` AsRef traits ⭐
//!
//! # 版本信息
//! - Rust版本: 1.95.0
//! - 稳定日期: 2026-04-16
//! - Edition: 2024
//!
//! # 参考
//! - [Rust 1.95.0 Release Notes](https://releases.rs/docs/1.95.0/)

use std::cell::Cell;
use std::mem::MaybeUninit;

// ============================================================================
// 1. MaybeUninit 数组互转
// ============================================================================

/// # `MaybeUninit<[T; N]>` ↔ `[MaybeUninit<T>; N]` 互转
///
/// ## 概念定义
/// Rust 1.95.0 稳定了以下 trait 实现，允许 `MaybeUninit` 与数组之间安全转换：
/// - `MaybeUninit<[T; N]>: From<[MaybeUninit<T>; N]>`
/// - `MaybeUninit<[T; N]>: AsRef<[MaybeUninit<T>; N]>`
/// - `MaybeUninit<[T; N]>: AsRef<[MaybeUninit<T>]>`
/// - `MaybeUninit<[T; N]>: AsMut<[MaybeUninit<T>; N]>`
/// - `MaybeUninit<[T; N]>: AsMut<[MaybeUninit<T>]>`
/// - `[MaybeUninit<T>; N]: From<MaybeUninit<[T; N]>>`
///
/// 这些转换使得**逐个元素初始化数组**后再整体转换为初始化数组变得安全且零开销。
///
/// ## Wikipedia 概念对齐
/// - **Uninitialized Variable**: 程序设计中未赋值的变量，`MaybeUninit` 是其类型安全表示
/// - **Type Safety**: 通过类型系统区分已初始化/未初始化状态，防止使用未初始化值
///
/// ## 核心模式：逐个初始化数组
///
/// ```text
/// 旧模式（1.95 之前）：
/// 1. 创建 [MaybeUninit<T>; N]
/// 2. 逐个初始化元素（通过指针）
/// 3. 使用 ptr::read 或 transmute_copy 转换为 [T; N]
/// 风险：容易忘记某些元素未初始化，或误用 transmute
///
/// 新模式（1.95+）：
/// 1. 创建 MaybeUninit<[T; N]>
/// 2. 通过 AsMut 获取 [MaybeUninit<T>; N] 视图
/// 3. 逐个初始化
/// 4. 通过 From/into 安全转换为 [MaybeUninit<T>; N]，再 assume_init
/// 或：从 [MaybeUninit<T>; N] 通过 From 直接转为 MaybeUninit<[T; N]>
/// ```
///
/// ## 决策树
/// ```text
/// 需要延迟初始化数组？
/// ├── 大小编译期已知？ → MaybeUninit<[T; N]> (1.95+ 推荐)
/// ├── 大小运行时确定？ → Vec<MaybeUninit<T>>
/// └── 仅需单个值？ → MaybeUninit<T>
/// ```
///
/// ## 反例 / 常见错误
/// - **在全部元素初始化前调用 `assume_init`** → UB
/// - **Drop 未初始化值**：`MaybeUninit` 不会自动调用元素的 Drop，需要手动处理
/// - **重复的 `assume_init`**：`assume_init` 消耗值，不可重复调用
/// - **使用 `mem::transmute`**：1.95 之前常用，但类型尺寸可能不匹配导致 UB
pub struct MaybeUninitArrayExamples;

impl MaybeUninitArrayExamples {
    /// 基础示例：安全地逐个初始化数组
    ///
    /// 展示了从 `MaybeUninit<[T; N]>` 开始，逐个初始化，最终安全获取 `[T; N]` 的完整流程。
    pub fn initialize_array_element_wise<T, F, const N: usize>(init: F) -> [T; N]
    where
        F: Fn(usize) -> T,
    {
        // 1. 创建未初始化的数组包装
        let mut uninit_array: MaybeUninit<[T; N]> = MaybeUninit::uninit();

        // 2. 通过 AsMut 获取元素级别的可变视图
        // SAFETY: 我们拥有唯一的可变访问，且不会重复初始化
        let slots: &mut [MaybeUninit<T>; N] = uninit_array.as_mut();

        // 3. 逐个初始化
        for (i, slot) in slots.iter_mut().enumerate() {
            *slot = MaybeUninit::new(init(i));
        }

        // 4. 所有元素已初始化，安全转换
        // SAFETY: 所有 N 个元素都已通过 MaybeUninit::new 写入
        unsafe { uninit_array.assume_init() }
    }

    /// 反向转换：从 [MaybeUninit<T>; N] 到 MaybeUninit<[T; N]>
    ///
    /// 这在需要将分散的未初始化槽位组合为统一数组类型时有用。
    pub fn combine_slots<T, const N: usize>(slots: [MaybeUninit<T>; N]) -> MaybeUninit<[T; N]> {
        // 使用 From trait 直接转换
        MaybeUninit::from(slots)
    }

    /// 部分初始化：仅填充前 k 个元素
    ///
    /// 展示了在无法完全初始化时的安全处理模式。
    pub fn partial_initialize<T, F, const N: usize>(
        init: F,
        count: usize,
    ) -> (MaybeUninit<[T; N]>, usize)
    where
        F: Fn(usize) -> T,
    {
        assert!(count <= N);

        let mut uninit_array: MaybeUninit<[T; N]> = MaybeUninit::uninit();
        let slots: &mut [MaybeUninit<T>; N] = uninit_array.as_mut();

        let mut initialized = 0;
        for i in 0..count {
            slots[i] = MaybeUninit::new(init(i));
            initialized += 1;
        }

        (uninit_array, initialized)
    }

    /// 与 `array::map` 的对比
    ///
    /// `array::map` (1.63+) 要求映射函数是 pure 且不会失败；
    /// `MaybeUninit` 模式允许失败、条件初始化、异步初始化等。
    pub fn conditional_initialize<T, F, const N: usize>(init: F) -> Option<[T; N]>
    where
        F: Fn(usize) -> Option<T>,
    {
        let mut uninit_array: MaybeUninit<[T; N]> = MaybeUninit::uninit();
        let slots: &mut [MaybeUninit<T>; N] = uninit_array.as_mut();

        for (i, slot) in slots.iter_mut().enumerate() {
            match init(i) {
                Some(value) => *slot = MaybeUninit::new(value),
                None => return None, // 安全：未初始化的 MaybeUninit 不会 Drop
            }
        }

        Some(unsafe { uninit_array.assume_init() })
    }

    /// 异步初始化模式（概念性）
    ///
    /// 在异步上下文中初始化数组元素。
    pub async fn async_initialize_array<T, F, Fut, const N: usize>(init: F) -> [T; N]
    where
        F: Fn(usize) -> Fut,
        Fut: std::future::Future<Output = T>,
    {
        let mut uninit_array: MaybeUninit<[T; N]> = MaybeUninit::uninit();
        let slots: &mut [MaybeUninit<T>; N] = uninit_array.as_mut();

        for i in 0..N {
            let value = init(i).await;
            slots[i] = MaybeUninit::new(value);
        }

        unsafe { uninit_array.assume_init() }
    }

    /// 与 Cell 结合：初始化后转为共享可变状态
    ///
    /// 展示了 `MaybeUninit` → `[T; N]` → `[Cell<T>; N]` 的转换链。
    pub fn initialize_then_freeze<T: Copy, const N: usize>(values: [T; N]) -> [Cell<T>; N] {
        // 使用 array::from_fn 安全初始化 Cell 数组
        std::array::from_fn(|i| Cell::new(values[i]))
    }
}

// ============================================================================
// 2. Cell<[T; N]> AsRef
// ============================================================================

/// # `Cell<[T; N]>` AsRef traits
///
/// Rust 1.95.0 稳定了以下 trait 实现：
/// - `Cell<[T; N]>: AsRef<[Cell<T>; N]>`
/// - `Cell<[T; N]>: AsRef<[Cell<T>]>`
/// - `Cell<[T]>: AsRef<[Cell<T>]>`
///
/// 这些实现允许将 `Cell<[T; N]>` 视为 `Cell<T>` 的数组，
/// 而无需手动解构或转换。
///
/// ## 概念
/// `Cell` 提供**内部可变性**（interior mutability）：即使拥有 `&Cell<T>`，
/// 也能通过 `get`/`set` 修改值。`Cell<[T; N]>` 将内部可变性扩展到数组。
///
/// ## Wikipedia 概念对齐
/// - **Interior Mutability**: 软件工程中的内部可变性模式，允许在不可变引用后修改
///
/// ## 反例
/// - `Cell` 要求 `T: Copy`，因此不能用于非 Copy 类型（需用 `RefCell`）
/// - `AsRef` 返回的引用生命周期受原始 `Cell` 借用约束
pub struct CellArrayExamples;

impl CellArrayExamples {
    /// 基础示例：将 Cell<[i32; 4]> 作为 Cell<i32> 数组访问
    pub fn cell_array_access() {
        let cell_array: Cell<[i32; 4]> = Cell::new([10, 20, 30, 40]);

        // 通过 AsRef 获取 [Cell<i32>; 4] 视图
        let cells: &[Cell<i32>; 4] = cell_array.as_ref();

        // 现在可以独立修改每个元素
        cells[0].set(100);
        cells[2].set(300);

        assert_eq!(cell_array.get(), [100, 20, 300, 40]);
    }

    /// 切片视角：Cell<[T]> 作为 [Cell<T>]
    ///
    /// 对于动态大小的数组切片同样适用。
    pub fn cell_slice_access() {
        let cell_slice: Cell<[i32; 5]> = Cell::new([1, 2, 3, 4, 5]);

        // 获取 [Cell<i32>] 切片视图
        let cells: &[Cell<i32>] = cell_slice.as_ref();

        for (i, cell) in cells.iter().enumerate() {
            cell.set(cell.get() * 2);
            assert_eq!(cell.get(), (i as i32 + 1) * 2);
        }
    }

    /// 并发场景：在线程间传递 Cell 数组视图
    ///
    /// `Cell` 不是 `Sync`，因此不能直接在多线程间共享，
    /// 但可以在单线程异步任务或 scoped threads 中传递引用。
    pub fn parallel_cell_update_single_threaded() {
        let cell_array: Cell<[i32; 8]> = Cell::new([0; 8]);
        let cells: &[Cell<i32>; 8] = cell_array.as_ref();

        // 在单线程中"并行"更新（模拟向量化操作）
        for (i, cell) in cells.iter().enumerate() {
            cell.set(i as i32 * i as i32);
        }

        let final_values = cell_array.get();
        assert_eq!(final_values, [0, 1, 4, 9, 16, 25, 36, 49]);
    }

    /// 与 MaybeUninit 协同：初始化 Cell 数组
    pub fn init_cell_array<const N: usize>(values: [i32; N]) -> Cell<[i32; N]> {
        Cell::new(values)
    }
}

// ============================================================================
// 3. 综合模式：安全数组初始化 + 内部可变性
// ============================================================================

/// 生产级模式：缓冲区池
///
/// 结合了 `MaybeUninit` 数组初始化和 `Cell` 内部可变性的实际应用场景。
pub struct BufferPool<const N: usize, const SIZE: usize> {
    buffers: [Cell<[u8; SIZE]>; N],
    available: Cell<u32>,
}

impl<const N: usize, const SIZE: usize> BufferPool<N, SIZE> {
    pub fn new() -> Self {
        let buffers = std::array::from_fn(|_| Cell::new([0u8; SIZE]));

        Self {
            buffers,
            available: Cell::new(N as u32),
        }
    }

    pub fn acquire(&self) -> Option<&Cell<[u8; SIZE]>> {
        let avail = self.available.get();
        if avail == 0 {
            return None;
        }
        self.available.set(avail - 1);
        Some(&self.buffers[N - avail as usize])
    }

    pub fn release(&self) {
        let avail = self.available.get();
        if avail < N as u32 {
            self.available.set(avail + 1);
        }
    }

    pub fn available_count(&self) -> u32 {
        self.available.get()
    }
}

impl<const N: usize, const SIZE: usize> Default for BufferPool<N, SIZE> {
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================================
// 测试
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_initialize_array_element_wise() {
        let arr = MaybeUninitArrayExamples::initialize_array_element_wise(|i| i * 2);
        assert_eq!(arr, [0, 2, 4, 6, 8]);
    }

    #[test]
    fn test_combine_slots() {
        let slots = [
            MaybeUninit::new(1),
            MaybeUninit::new(2),
            MaybeUninit::new(3),
        ];
        let combined = MaybeUninitArrayExamples::combine_slots(slots);
        unsafe {
            assert_eq!(combined.assume_init(), [1, 2, 3]);
        }
    }

    #[test]
    fn test_partial_initialize() {
        let (uninit, count) =
            MaybeUninitArrayExamples::partial_initialize::<i32, _, 5>(|i| i as i32 * 10, 3);
        assert_eq!(count, 3);
        // 注意：不能 assume_init，因为只初始化了 3/5 元素
        // 这里仅验证不 panic
        drop(uninit);
    }

    #[test]
    fn test_conditional_initialize() {
        let result = MaybeUninitArrayExamples::conditional_initialize::<usize, _, 5>(|i| {
            if i < 3 { Some(i * 10) } else { None }
        });
        assert_eq!(result, None); // 因为 i=3 时返回 None

        let result = MaybeUninitArrayExamples::conditional_initialize::<usize, _, 5>(|i| Some(i * 10));
        assert_eq!(result, Some([0, 10, 20, 30, 40]));
    }

    #[test]
    fn test_cell_array_access() {
        CellArrayExamples::cell_array_access();
    }

    #[test]
    fn test_cell_slice_access() {
        CellArrayExamples::cell_slice_access();
    }

    #[test]
    fn test_buffer_pool() {
        let pool: BufferPool<4, 256> = BufferPool::new();
        assert_eq!(pool.available_count(), 4);

        let buf1 = pool.acquire();
        assert!(buf1.is_some());
        assert_eq!(pool.available_count(), 3);

        buf1.unwrap().set([1u8; 256]);

        pool.release();
        assert_eq!(pool.available_count(), 4);
    }

    #[tokio::test]
    async fn test_async_initialize_array() {
        let arr = MaybeUninitArrayExamples::async_initialize_array(|i| async move { i * 3 }).await;
        assert_eq!(arr, [0, 3, 6, 9, 12]);
    }
}
