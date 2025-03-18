#[derive(Debug)]
struct Creator {
    name: String,
}

impl Creator {
    // 创建一个新的 Creator 实例
    fn new(name: String) -> Self {
        Creator { name }
    }

    // 使用移动语义返回 Creator 的名称
    fn get_name(self) -> String {
        self.name // 这里会移动 self.name
    }
}

fn main() {
    let creator = Creator::new(String::from("Alice"));
    println!("{:?}", creator); // 这行代码会导致编译错误

    // 使用移动语义获取名称
    let name = creator.get_name();
    
    println!("Creator's name: {}", name);
    // 此时 creator 已经被移动，不能再使用
    //println!("{:?}", creator); // 这行代码会导致编译错误
}
