use std::pin::Pin;

#[derive(Debug)]
struct SelfRef {
    data: String,
    ptr: *const u8,
    len: usize,
}

impl SelfRef {
    fn new(data: String) -> Pin<Box<SelfRef>> {
        let mut boxed = Box::pin(SelfRef { data, ptr: std::ptr::null(), len: 0 });
        unsafe {
            let this = Pin::as_mut(&mut boxed).get_unchecked_mut();
            let data_ptr = this.data.as_ptr();
            let data_len = this.data.len();
            this.ptr = data_ptr;
            this.len = data_len;
        }
        boxed
    }

    fn get(&self) -> &str {
        unsafe { std::str::from_utf8_unchecked(std::slice::from_raw_parts(self.ptr, self.len)) }
    }
}

#[test]
fn test_self_ref_basic() {
    let s = SelfRef::new("hi".to_string());
    assert_eq!(s.get(), "hi");
}


