use std::mem::{ManuallyDrop, MaybeUninit};

struct Buffer { data: Vec<u8> }

#[test]
fn test_maybeuninit_init() {
    let mut slot: MaybeUninit<Buffer> = MaybeUninit::uninit();
    unsafe { slot.as_mut_ptr().write(Buffer { data: vec![1,2] }); }
    let buf = unsafe { slot.assume_init() };
    assert_eq!(buf.data, vec![1,2]);
}

#[test]
fn test_manuallydrop_into_inner() {
    let m = ManuallyDrop::new(Buffer { data: vec![3] });
    let inner = ManuallyDrop::into_inner(m);
    assert_eq!(inner.data, vec![3]);
}


