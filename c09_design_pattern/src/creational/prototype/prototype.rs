use std::fmt::Debug;
//use std::marker::PhantomData;

#[allow(non_snake_case)]
// 定义一个原型 trait
trait Prototype<T: Clone + Debug> {
    fn Clone(&self) -> T;
}

#[allow(unused)]
// 定义一个具体的产品结构体
#[derive(Clone, Debug)]
struct ConcretePrototype {
    id: u32,
    name: String,
}


// 实现 Prototype trait
impl Prototype<ConcretePrototype> for ConcretePrototype {
    fn Clone(&self) -> ConcretePrototype {
        self.clone() // 使用 Clone trait 的 clone 方法
    }
}

// 定义一个原型管理器
struct PrototypeManager<T: Prototype<T> + Clone + Debug> {
    prototypes: Vec<T>,
}

impl<T: Prototype<T> + Clone + Debug> PrototypeManager<T> {
    fn new() -> Self {
        PrototypeManager {
            prototypes: Vec::new(),
        }
    }

    // 添加原型
    fn add_prototype(&mut self, prototype: T) {
        self.prototypes.push(prototype);
    }

    // 克隆原型
    fn clone_prototype(&self, index: usize) -> Option<T> {
        if index < self.prototypes.len() {
            Some(self.prototypes[index].Clone())
        } else {
            None
        }
    }
}

#[allow(unused)]
pub fn test_prototype() {
    let mut manager = PrototypeManager::new();

    // 创建一个具体的原型
    let prototype1 = ConcretePrototype {
        id: 1,
        name: "原型1".to_string(),
    };

    // 将原型添加到管理器
    manager.add_prototype(prototype1);

    // 克隆原型
    if let Some(cloned_prototype) = manager.clone_prototype(0) {
        println!("克隆的原型: {:?}", cloned_prototype);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_prototype01() {
        test_prototype();
    }
}
