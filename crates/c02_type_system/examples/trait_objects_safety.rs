trait Greeter {
    fn greet(&self) -> String;

    // 非对象安全的方法通常需要限制为仅在具体类型可用
    fn clone_box(&self) -> Box<dyn Greeter>
    where
        Self: Sized,
    {
        Box::new(SimpleGreeter(self.greet()))
    }
}

struct SimpleGreeter(String);

impl Greeter for SimpleGreeter {
    fn greet(&self) -> String { format!("Hello, {}", self.0) }
    fn clone_box(&self) -> Box<dyn Greeter>
    where
        Self: Sized,
    {
        Box::new(SimpleGreeter(self.0.clone()))
    }
}

fn main() {
    let g: Box<dyn Greeter> = Box::new(SimpleGreeter(String::from("Rust")));
    println!("{}", g.greet());

    // clone_box 在 trait 对象上不可用（因 `Self: Sized`），但在具体类型上可用：
    let s = SimpleGreeter(String::from("World"));
    let _boxed = s.clone_box();
}


