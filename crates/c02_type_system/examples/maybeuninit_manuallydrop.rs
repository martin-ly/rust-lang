use std::mem::{ManuallyDrop, MaybeUninit};

struct Buffer { data: Vec<u8> }

fn main() {
    // MaybeUninit: 延迟初始化
    let mut slot: MaybeUninit<Buffer> = MaybeUninit::uninit();
    unsafe { slot.as_mut_ptr().write(Buffer { data: vec![1,2,3] }); }
    let buf = unsafe { slot.assume_init() };
    println!("len={}", buf.data.len());

    // ManuallyDrop: 抑制自动析构
    let m = ManuallyDrop::new(Buffer { data: vec![9,9] });
    // 显式 drop（将其转回所有权或使用 ManuallyDrop::into_inner）
    let inner = ManuallyDrop::into_inner(m);
    drop(inner);
}


