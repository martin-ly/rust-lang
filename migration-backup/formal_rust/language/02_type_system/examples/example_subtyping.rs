// 类型系统案例：子类型与型变
// 理论映射：对应“子类型”与“型变”理论（见 01_formal_type_system.md 附录）

trait Animal {
    fn speak(&self);
}

struct Dog;
impl Animal for Dog {
    fn speak(&self) { println!("汪汪"); }
}

struct Cat;
impl Animal for Cat {
    fn speak(&self) { println!("喵喵"); }
}

fn animal_speak(a: &dyn Animal) {
    a.speak();
}

fn main() {
    let dog = Dog;
    let cat = Cat;
    animal_speak(&dog); // Dog <: dyn Animal
    animal_speak(&cat); // Cat <: dyn Animal
} 