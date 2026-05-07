//! Rust 1.95.0 所有权与内存安全新特性实现模块
//!
//! 本模块展示了 Rust 1.95.0 在所有权、借用和内存安全方面的关键增强：
//! - `MaybeUninit<[T; N]>` ↔ `[MaybeUninit<T>; N]` 互转 ⭐
//! - `Cell<[T; N]>` AsRef traits ⭐
//! - `Layout` 辅助方法：`dangling_ptr`、`repeat`、`repeat_packed`、`extend_packed` ⭐
//!
//! # 版本信息
//! - Rust版本: 1.95.0
//! - 稳定日期: 2026-04-16
//! - Edition: 2024
//!
//! # 参考
//! - [Rust 1.95.0 Release Notes](https://releases.rs/docs/1.95.0/)

use std::alloc::Layout;
use std::cell::Cell;
use std::mem::MaybeUninit;
use std::ptr::NonNull;

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

    /// 反向转换：从 `[MaybeUninit<T>; N]` 到 `MaybeUninit<[T; N]>`
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
        for (i, slot) in slots.iter_mut().enumerate().take(count) {
            *slot = MaybeUninit::new(init(i));
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
            let value = init(i)?;
            *slot = MaybeUninit::new(value);
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

        for (i, slot) in slots.iter_mut().enumerate().take(N) {
            let value = init(i).await;
            *slot = MaybeUninit::new(value);
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
    /// 基础示例：将 `Cell<[i32; 4]>` 作为 `Cell<i32>` 数组访问
    pub fn cell_array_access() {
        let cell_array: Cell<[i32; 4]> = Cell::new([10, 20, 30, 40]);

        // 通过 AsRef 获取 [Cell<i32>; 4] 视图
        let cells: &[Cell<i32>; 4] = cell_array.as_ref();

        // 现在可以独立修改每个元素
        cells[0].set(100);
        cells[2].set(300);

        assert_eq!(cell_array.get(), [100, 20, 300, 40]);
    }

    /// 切片视角：`Cell<[T]>` 作为 `[Cell<T>]`
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
// 3. Layout 辅助方法
// ============================================================================

/// # `Layout` 辅助方法
///
/// Rust 1.95.0 稳定了 `std::alloc::Layout` 上的以下实用方法：
/// - `Layout::dangling_ptr`
/// - `Layout::repeat`
/// - `Layout::repeat_packed`
/// - `Layout::extend_packed`
///
/// 这些方法使得**手动内存布局计算**更加安全、明确，无需借助 `unsafe` 即可在类型系统内
/// 验证布局约束。
///
/// ## 概念定义
/// - **Memory Layout**: 内存中数据类型的排列方式，包括大小（size）和对齐（alignment）
/// - **Padding**: 编译器插入的填充字节，以满足对齐要求；`repeat` 保留填充，`repeat_packed` 消除填充
/// - **Dangling Pointer**: 指向有效对齐地址但不指向实际分配内存的指针，可用于零大小类型占位
///
/// ## Wikipedia 概念对齐
/// - **Data Structure Alignment**: 数据在内存中的排列方式，影响访问效率和硬件兼容性
/// - **Packed Data Structure**: 紧密排列的数据结构，无填充字节，常用于网络协议或文件格式
///
/// ## 决策树
/// ```text
/// 需要计算内存布局？
/// ├── 数组布局，需要自然对齐（含填充）？ → Layout::repeat
/// ├── 数组布局，需要紧密排列（无填充）？ → Layout::repeat_packed
/// ├── 结构体布局，需要紧密排列？ → Layout::extend_packed
/// └── 需要占位指针（零大小或未初始化）？ → Layout::dangling_ptr
/// ```
///
/// ## 反例 / 常见错误
/// - **混淆 `repeat` 与 `repeat_packed`**: `repeat` 保留元素间填充，适用于硬件对齐要求；
///   `repeat_packed` 消除填充，适用于序列化/反序列化场景
/// - **忽略 `LayoutError`**: 这些方法在溢出或对齐不匹配时返回 `Err`，必须处理
/// - **将 `dangling_ptr` 用于非零大小访问**: 该指针仅保证零字节访问有效，解引用实际数据是 UB
pub struct LayoutHelpersExamples;

impl LayoutHelpersExamples {
    /// `dangling_ptr`：获取对齐有效的占位指针
    ///
    /// 返回一个**对齐有效但无实际分配**的非空指针。
    /// 适用于：
    /// - 零大小类型（ZST）的占位
    /// - 未初始化内存的临时句柄
    /// - 需要满足 `NonNull<u8>` 约束但尚无实际分配的场景
    ///
    /// # 安全性说明
    /// 该指针保证**零字节读写**是安全的，但解引用以访问实际数据是未定义行为。
    pub fn placeholder_pointer<T>() -> NonNull<u8> {
        let layout = Layout::new::<T>();
        layout.dangling_ptr()
    }

    /// `repeat`：计算 `[T; N]` 的自然对齐布局
    ///
    /// 返回包含元素间填充的数组布局，以及单个元素之间的偏移量。
    /// 这与编译器为 `[T; N]` 生成的实际布局一致。
    pub fn array_layout<T>(count: usize) -> Option<(Layout, usize)> {
        let elem_layout = Layout::new::<T>();
        elem_layout.repeat(count).ok()
    }

    /// `repeat_packed`：计算紧密排列的数组布局
    ///
    /// 消除元素间的填充字节，总大小严格等于 `size_of::<T>() * N`。
    /// 适用于网络协议、文件格式等需要紧凑表示的场景。
    ///
    /// # 注意
    /// 紧密排列可能违反硬件对齐要求，实际访问 packed 数据时需要使用
    /// `std::ptr::read_unaligned` / `write_unaligned`。
    pub fn packed_array_layout<T>(count: usize) -> Option<Layout> {
        let elem_layout = Layout::new::<T>();
        elem_layout.repeat_packed(count).ok()
    }

    /// `extend_packed`：计算紧密排列的结构体布局
    ///
    /// 将两个 `Layout` 紧密拼接，不插入填充字节。
    /// 适用于自定义序列化格式中字段紧密排列的场景。
    ///
    /// # 示例场景
    /// 假设有一个协议头：`[u8; 3]`（标志） + `u16`（长度），紧密排列时总大小为 5 字节。
    pub fn packed_struct_layout(fields: &[Layout]) -> Option<Layout> {
        fields
            .iter()
            .copied()
            .try_fold(Layout::new::<()>(), |acc, field| {
                acc.extend_packed(field).ok()
            })
    }

    /// 对比：自然对齐布局 vs 紧密排列布局
    ///
    /// 展示同一类型在不同布局策略下的尺寸差异。
    pub fn compare_layouts<T>(count: usize) -> (Option<(Layout, usize)>, Option<Layout>)
    where
        T: Copy,
    {
        let natural = Self::array_layout::<T>(count);
        let packed = Self::packed_array_layout::<T>(count);
        (natural, packed)
    }

    /// 实际应用：计算动态数组的分配大小
    ///
    /// 在不实际分配内存的情况下，预先验证数组布局是否合法。
    pub fn validate_array_allocation<T>(count: usize) -> Result<Layout, String> {
        let elem = Layout::new::<T>();
        let (layout, _offset) = elem
            .repeat(count)
            .map_err(|_| format!("布局溢出或无效: [T; {}]", count))?;
        Ok(layout)
    }

    /// 实际应用：协议消息头布局计算
    ///
    /// 模拟一个网络协议头：版本(u8) + 标志(u8) + 长度(u16) + 校验和(u32)。
    /// 使用 `extend_packed` 计算紧密排列时的总大小。
    pub fn protocol_header_layout_packed() -> Option<Layout> {
        let version = Layout::new::<u8>();
        let flags = Layout::new::<u8>();
        let length = Layout::new::<u16>();
        let checksum = Layout::new::<u32>();

        version
            .extend_packed(flags)
            .ok()?
            .extend_packed(length)
            .ok()?
            .extend_packed(checksum)
            .ok()
    }

    /// 实际应用：协议消息头自然对齐布局计算
    ///
    /// 使用标准 `Layout::extend`（Rust 已有 API）计算含填充的自然对齐布局，
    /// 与 `extend_packed` 形成对比。
    pub fn protocol_header_layout_aligned() -> Option<Layout> {
        let version = Layout::new::<u8>();
        let flags = Layout::new::<u8>();
        let length = Layout::new::<u16>();
        let checksum = Layout::new::<u32>();

        version
            .extend(flags)
            .ok()
            .map(|(l, _)| l)
            .and_then(|l| l.extend(length).ok())
            .map(|(l, _)| l)
            .and_then(|l| l.extend(checksum).ok())
            .map(|(l, _)| l)
    }
}

// ============================================================================
// 4. 综合模式：安全数组初始化 + 内部可变性
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
        let _ = uninit;
    }

    #[test]
    fn test_conditional_initialize() {
        let result = MaybeUninitArrayExamples::conditional_initialize::<usize, _, 5>(|i| {
            if i < 3 { Some(i * 10) } else { None }
        });
        assert_eq!(result, None); // 因为 i=3 时返回 None

        let result =
            MaybeUninitArrayExamples::conditional_initialize::<usize, _, 5>(|i| Some(i * 10));
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

    // ------------------------------------------------------------------------
    // Layout 辅助方法测试
    // ------------------------------------------------------------------------

    #[test]
    fn test_dangling_ptr_alignment() {
        let ptr = LayoutHelpersExamples::placeholder_pointer::<u64>();
        // dangling_ptr 返回的指针对齐于类型的对齐要求
        assert_eq!(ptr.as_ptr() as usize % align_of::<u64>(), 0);
    }

    #[test]
    fn test_array_layout_natural() {
        let (layout, offset) = LayoutHelpersExamples::array_layout::<u32>(4).unwrap();
        // [u32; 4] 每个元素 4 字节，无额外填充（因为 align=4 已满足）
        assert_eq!(layout.size(), 16);
        assert_eq!(layout.align(), 4);
        assert_eq!(offset, 4);
    }

    #[test]
    fn test_array_layout_with_padding() {
        // 使用一个对齐大于大小的类型来观察填充效果较困难，
        // 这里验证 repeat 与 repeat_packed 在 u64 上的差异（通常无差异）
        let (natural, _) = LayoutHelpersExamples::array_layout::<u64>(2).unwrap();
        let packed = LayoutHelpersExamples::packed_array_layout::<u64>(2).unwrap();
        // u64 的自然对齐数组通常无填充
        assert_eq!(natural.size(), packed.size());
    }

    #[test]
    fn test_packed_array_layout() {
        let layout = LayoutHelpersExamples::packed_array_layout::<u8>(10).unwrap();
        // 紧密排列：10 * 1 = 10 字节，对齐为 1
        assert_eq!(layout.size(), 10);
        assert_eq!(layout.align(), 1);
    }

    #[test]
    fn test_packed_struct_layout() {
        let fields = vec![
            Layout::new::<u8>(),
            Layout::new::<u8>(),
            Layout::new::<u16>(),
            Layout::new::<u32>(),
        ];
        let layout = LayoutHelpersExamples::packed_struct_layout(&fields).unwrap();
        // 紧密排列：1 + 1 + 2 + 4 = 8
        assert_eq!(layout.size(), 8);
        assert_eq!(layout.align(), 1);
    }

    #[test]
    fn test_compare_layouts() {
        let (natural, packed) = LayoutHelpersExamples::compare_layouts::<u8>(5);
        assert!(natural.is_some());
        assert!(packed.is_some());
        // u8 数组自然对齐和紧密排列通常一致（因为 align=1）
        assert_eq!(natural.unwrap().0.size(), packed.unwrap().size());
    }

    #[test]
    fn test_validate_array_allocation() {
        let layout = LayoutHelpersExamples::validate_array_allocation::<u64>(100);
        assert!(layout.is_ok());
        assert_eq!(layout.unwrap().size(), 800);
    }

    #[test]
    fn test_validate_array_allocation_overflow() {
        // usize::MAX 元素必然导致溢出
        let result = LayoutHelpersExamples::validate_array_allocation::<u64>(usize::MAX);
        assert!(result.is_err());
    }

    #[test]
    fn test_protocol_header_layout_packed() {
        let layout = LayoutHelpersExamples::protocol_header_layout_packed().unwrap();
        // 紧密排列：u8 + u8 + u16 + u32 = 8 字节
        assert_eq!(layout.size(), 8);
        assert_eq!(layout.align(), 1);
    }

    #[test]
    fn test_protocol_header_layout_aligned() {
        let layout = LayoutHelpersExamples::protocol_header_layout_aligned().unwrap();
        // 自然对齐通常会有填充：u8 + [pad1] + u8 + [pad1] + u16 + u32
        // 实际布局取决于 extend 的实现，但 align 至少为 4
        assert!(layout.align() >= 4);
        // 大小应大于等于紧密排列的 8 字节
        assert!(layout.size() >= 8);
    }
}
