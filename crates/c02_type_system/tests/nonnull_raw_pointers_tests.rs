use std::ptr::NonNull;

#[test]
fn test_nonnull_write() {
    let mut v = vec![0, 0, 0];
    let p = NonNull::new(v.as_mut_ptr()).unwrap();
    unsafe { *p.as_ptr() = 5; }
    assert_eq!(v[0], 5);
}


