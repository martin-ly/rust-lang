struct Person {
    name: String,
    age: u32,
}

impl Person {
    fn new(name: String, age: u32) -> Self {
        Person { name, age }
    }

    // 使用移动语义解构结构体
    fn display(self) {
        // 这里 self.name 和 self.age 会被移动
        println!("Name: {}, Age: {}", self.name, self.age);
    }
}

fn main() {
    let person = Person::new(String::from("Alice"), 30);

    // 调用 display 方法，移动 person 的所有权
    person.display();

    // 此时 person 已经被移动，不能再使用
    // println!("{:?}", person); // 这行代码会导致编译错误
}
