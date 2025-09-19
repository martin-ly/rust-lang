use std::cell::{Cell, RefCell};

fn main() {
    let c = Cell::new(1);
    c.set(2);
    println!("cell {}", c.get());

    let r = RefCell::new(String::from("hi"));
    {
        let mut b = r.borrow_mut();
        b.push_str(" rust");
    }
    println!("refcell {}", r.borrow());
}


