trait Greeter {
    fn greet(&self) -> String;
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

#[test]
fn test_greeter_dyn_and_sized_method() {
    let g: Box<dyn Greeter> = Box::new(SimpleGreeter(String::from("Rust")));
    assert_eq!(g.greet(), "Hello, Rust");

    let s = SimpleGreeter(String::from("Alice"));
    let b = s.clone_box();
    assert_eq!(b.greet(), "Hello, Alice");
}


