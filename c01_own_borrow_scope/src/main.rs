
fn main() {
    borrow_scope();
    println!("main exit!");
}

fn borrow_scope() {
    let x = String::from("hello");
    let y = x;
    println!("{}", y);
}
