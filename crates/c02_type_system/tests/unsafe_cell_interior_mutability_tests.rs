use std::cell::{Cell, RefCell};

#[test]
fn test_cell_refcell() {
    let c = Cell::new(3);
    c.set(5);
    assert_eq!(c.get(), 5);

    let r = RefCell::new(String::from("a"));
    {
        let mut b = r.borrow_mut();
        b.push('b');
    }
    assert_eq!(r.borrow().as_str(), "ab");
}


