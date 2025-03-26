// 定义一个 trait
trait Animal {
    fn sound(&self) -> &'static str;
}

// 实现 trait 的具体类型
struct Dog;
struct Cat;

impl Animal for Dog {
    fn sound(&self) -> &'static str {
        "Woof"
    }
}

impl Animal for Cat {
    fn sound(&self) -> &'static str {
        "Meow"
    }
}

#[allow(unused)]
// 定义一个函数，接受一个实现 Animal trait 的参数
fn make_sound(animal: &dyn Animal) {
    println!("{}", animal.sound());
}

#[allow(unused)]
fn test01() {
    let dog = Dog;
    make_sound(&dog);
    let cat = Cat;
    make_sound(&cat);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_animal_sound() {
        test01();
    }
}
