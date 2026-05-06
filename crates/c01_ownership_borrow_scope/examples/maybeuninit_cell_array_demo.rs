//! Rust 1.95.0 `MaybeUninit` / `Cell` 数组转换专题示例
//!
//! Rust 1.95.0 稳定化了以下转换：
//! - `MaybeUninit<[T; N]>: From<[MaybeUninit<T>; N]>`
//! - `MaybeUninit<[T; N]>: AsRef<[MaybeUninit<T>]>`, `AsMut<[MaybeUninit<T>]>`
//! - `[MaybeUninit<T>; N]: From<MaybeUninit<[T; N]>>`
//! - `Cell<[T; N]>: AsRef<[Cell<T>; N]>`, `AsRef<[Cell<T>]>`
//! - `Cell<[T]>: AsRef<[Cell<T>]>`
//!
//! 这些转换对 unsafe 代码、FFI 和自定义容器非常有用。
//!
//! 权威来源: https://releases.rs/docs/1.95.0/
//!
//! 运行方式:
//! ```bash
//! cargo run --example maybeuninit_cell_array_demo -p c01_ownership_borrow_scope
//! ```

use std::cell::Cell;
use std::mem::MaybeUninit;

// ==================== 示例 1: [MaybeUninit<T>; N] → MaybeUninit<[T; N]> ====================

/// 将已部分初始化的 MaybeUninit 数组打包为未初始化数组
fn demo_uninit_array_to_array_uninit() {
    println!("--- [MaybeUninit<T>; N] -> MaybeUninit<[T; N]> ---");

    // 创建一个 MaybeUninit 元素数组
    let elems: [MaybeUninit<i32>; 3] = [
        MaybeUninit::new(10),
        MaybeUninit::new(20),
        MaybeUninit::new(30),
    ];

    // 使用 From 转换为 MaybeUninit<[i32; 3]>
    let arr_uninit: MaybeUninit<[i32; 3]> = MaybeUninit::from(elems);

    // 安全: 我们知道所有元素都已初始化
    unsafe {
        let arr = arr_uninit.assume_init();
        println!("  初始化后的数组: {:?}", arr);
        assert_eq!(arr, [10, 20, 30]);
    }
}

// ==================== 示例 2: MaybeUninit<[T; N]> → [MaybeUninit<T>; N] ====================

/// 将未初始化数组拆分为独立的 MaybeUninit 元素
fn demo_array_uninit_to_uninit_array() {
    println!("\n--- MaybeUninit<[T; N]> -> [MaybeUninit<T>; N] ---");

    // 分配一个未初始化的 [String; 3]
    let arr_uninit: MaybeUninit<[String; 3]> = MaybeUninit::uninit();

    // 拆分为独立的 MaybeUninit<String> 元素
    let mut elems: [MaybeUninit<String>; 3] = arr_uninit.into();

    // 逐个初始化
    elems[0] = MaybeUninit::new("first".to_string());
    elems[1] = MaybeUninit::new("second".to_string());
    elems[2] = MaybeUninit::new("third".to_string());

    // 重新打包并假设初始化
    let arr_uninit: MaybeUninit<[String; 3]> = MaybeUninit::from(elems);
    unsafe {
        let arr = arr_uninit.assume_init();
        println!("  逐个初始化后的数组: {:?}", arr);
        assert_eq!(arr[0], "first");
        assert_eq!(arr[1], "second");
        assert_eq!(arr[2], "third");
    }
}

// ==================== 示例 3: MaybeUninit<[T; N]> 的 AsRef/AsMut ====================

/// 通过引用访问 MaybeUninit 数组的内部元素
fn demo_as_ref_as_mut() {
    println!("\n--- MaybeUninit<[T; N]>::as_ref / as_mut ---");

    let mut arr_uninit: MaybeUninit<[i32; 4]> = MaybeUninit::uninit();

    // as_mut: 获取 [MaybeUninit<i32>] 的可变引用
    let slice_mut: &mut [MaybeUninit<i32>] = arr_uninit.as_mut();
    println!("  未初始化切片长度: {}", slice_mut.len());

    // 逐个写入
    for (i, slot) in slice_mut.iter_mut().enumerate() {
        *slot = MaybeUninit::new((i * 10) as i32);
    }

    // as_ref: 获取不可变引用进行验证
    let slice_ref: &[MaybeUninit<i32>] = arr_uninit.as_ref();
    unsafe {
        print!("  写入后: [");
        for (i, slot) in slice_ref.iter().enumerate() {
            if i > 0 {
                print!(", ");
            }
            print!("{}", slot.assume_init_ref());
        }
        println!("]");
    }

    // 安全地假设整个数组已初始化
    unsafe {
        let arr = arr_uninit.assume_init();
        assert_eq!(arr, [0, 10, 20, 30]);
    }
}

// ==================== 示例 4: Cell<[T; N]>: AsRef<[Cell<T>]> ====================

/// 将 Cell 数组拆分为独立 Cell 元素的引用
fn demo_cell_array_as_ref() {
    println!("\n--- Cell<[T; N]>::as_ref -> [Cell<T>] ---");

    let cell_arr: Cell<[i32; 4]> = Cell::new([10, 20, 30, 40]);

    // as_ref: 获取 &[Cell<i32>; 4]
    let cells_ref: &[Cell<i32>; 4] = cell_arr.as_ref();
    println!("  独立 Cell 引用数组长度: {}", cells_ref.len());

    // 通过独立引用修改元素
    cells_ref[0].set(100);
    cells_ref[2].set(300);

    // 通过原始 Cell 数组读取
    let arr = cell_arr.get();
    println!("  修改后: {:?}", arr);
    assert_eq!(arr, [100, 20, 300, 40]);
}

// ==================== 示例 5: Cell<[T]>: AsRef<[Cell<T>]> ====================

/// 将 Cell 切片拆分为独立 Cell 元素的切片引用
fn demo_cell_slice_as_ref() {
    println!("\n--- Cell<[T]>::as_ref -> [Cell<T>] ---");

    // 使用 Cell::from_mut 从 &mut [T] 创建 Cell<[T]>
    let mut data = [1u8, 2, 3, 4, 5];
    let cell_slice: &Cell<[u8]> = Cell::from_mut(&mut data[..]);

    // as_ref: 获取 &[Cell<u8>]
    let cells: &[Cell<u8>] = cell_slice.as_ref();
    println!("  Cell 切片长度: {}", cells.len());

    // 独立修改元素
    cells[0].set(10);
    cells[4].set(50);

    // 读取原始数据验证
    println!("  修改后数据: {:?}", data);
    assert_eq!(data, [10, 2, 3, 4, 50]);
}

// ==================== 示例 6: 自定义栈上缓冲区 — MaybeUninit 数组转换 ====================

/// 使用 MaybeUninit 数组转换实现安全的栈上缓冲区
struct StackBuffer<T, const N: usize> {
    data: MaybeUninit<[T; N]>,
    len: usize,
}

impl<T, const N: usize> StackBuffer<T, N> {
    fn new() -> Self {
        Self {
            data: MaybeUninit::uninit(),
            len: 0,
        }
    }

    /// 在缓冲区末尾添加元素
    fn push(&mut self, value: T) -> Result<(), &'static str> {
        if self.len >= N {
            return Err("buffer full");
        }

        // 使用 as_mut 获取未初始化切片，写入新元素
        let slots: &mut [MaybeUninit<T>] = self.data.as_mut();
        slots[self.len] = MaybeUninit::new(value);
        self.len += 1;
        Ok(())
    }

    /// 获取已初始化部分的不可变引用
    fn as_slice(&self) -> &[T] {
        unsafe {
            let slots: &[MaybeUninit<T>] = self.data.as_ref();
            // 安全: 前 len 个元素已初始化
            std::slice::from_raw_parts(slots.as_ptr() as *const T, self.len)
        }
    }
}

impl<T, const N: usize> Drop for StackBuffer<T, N> {
    fn drop(&mut self) {
        // 安全: 只析构已初始化的元素
        unsafe {
            let slots: &mut [MaybeUninit<T>] = self.data.as_mut();
            for slot in &mut slots[..self.len] {
                slot.assume_init_drop();
            }
        }
    }
}

fn demo_stack_buffer() {
    println!("\n--- 自定义栈上缓冲区 (StackBuffer) ---");

    let mut buf = StackBuffer::<i32, 4>::new();

    buf.push(100).unwrap();
    buf.push(200).unwrap();
    buf.push(300).unwrap();

    println!("  缓冲区内容: {:?}", buf.as_slice());
    println!("  长度: {}", buf.as_slice().len());

    assert_eq!(buf.as_slice(), [100, 200, 300]);

    // 测试溢出
    buf.push(400).unwrap();
    let result = buf.push(500);
    assert!(result.is_err());
    println!("  溢出尝试: {:?}", result);
}

// ==================== 示例 7: Cell 数组的并行修改 ====================

/// 利用 Cell 数组拆分实现无需 &mut 的并行修改
fn demo_cell_parallel_update() {
    println!("\n--- Cell 数组的并行修改 ---");

    let cell_arr: Cell<[i32; 6]> = Cell::new([0; 6]);

    // 获取独立 Cell 引用
    let cells: &[Cell<i32>; 6] = cell_arr.as_ref();

    // 无需 &mut cell_arr，即可修改各个元素
    cells[0].set(1);
    cells[1].set(2);
    cells[2].set(3);
    cells[3].set(5);
    cells[4].set(8);
    cells[5].set(13);

    let result = cell_arr.get();
    println!("  斐波那契数列: {:?}", result);
    assert_eq!(result, [1, 2, 3, 5, 8, 13]);
}

// ==================== 主演示函数 ====================

fn main() {
    println!("🦀 Rust 1.95.0 `MaybeUninit` / `Cell` 数组转换专题演示\n");

    demo_uninit_array_to_array_uninit();
    demo_array_uninit_to_uninit_array();
    demo_as_ref_as_mut();
    demo_cell_array_as_ref();
    demo_cell_slice_as_ref();
    demo_stack_buffer();
    demo_cell_parallel_update();

    println!("\n✅ `MaybeUninit` / `Cell` 数组转换演示完成！");
    println!("   关键要点:");
    println!("   - MaybeUninit<[T; N]> <-> [MaybeUninit<T>; N]: 数组级别的打包/拆包");
    println!("   - MaybeUninit::as_ref/as_mut: 以切片形式访问未初始化元素");
    println!("   - Cell<[T; N]>::as_ref: 拆分为 [Cell<T>; N]，独立修改元素");
    println!("   - Cell<[T]>::as_ref: 拆分为 [Cell<T>]，适用于动态长度切片");
    println!("   - 所有转换都是零开销的，仅改变类型视角，不复制数据");
}
