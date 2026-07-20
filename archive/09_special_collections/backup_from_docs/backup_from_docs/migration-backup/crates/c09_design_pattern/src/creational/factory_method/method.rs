// 定义一个 trait，表示产品的接口
#[allow(unused)]
pub trait Product {
    fn operation(&self) -> String;
}

// 定义具体的产品 A
#[allow(unused)]
struct ConcreteProductA;

impl Product for ConcreteProductA {
    fn operation(&self) -> String {
        "产品 A 的操作".to_string()
    }
}

// 定义具体的产品 B
#[allow(unused)]
struct ConcreteProductB;

impl Product for ConcreteProductB {
    fn operation(&self) -> String {
        "产品 B 的操作".to_string()
    }
}

// 定义一个工厂 trait
trait Factory<T: Product> {
    fn create(&self) -> T;
}

// 定义具体的工厂 A
#[allow(unused)]
struct ConcreteFactoryA;

impl Factory<ConcreteProductA> for ConcreteFactoryA {
    fn create(&self) -> ConcreteProductA {
        ConcreteProductA
    }
}

// 定义具体的工厂 B
#[allow(unused)]
struct ConcreteFactoryB;

impl Factory<ConcreteProductB> for ConcreteFactoryB {
    fn create(&self) -> ConcreteProductB {
        ConcreteProductB
    }
}

#[allow(unused)]
pub fn test_factory_method() {
    // 使用工厂 A 创建产品 A
    let factory_a = ConcreteFactoryA;
    let product_a = factory_a.create();
    println!("{}", product_a.operation());

    // 使用工厂 B 创建产品 B
    let factory_b = ConcreteFactoryB;
    let product_b = factory_b.create();
    println!("{}", product_b.operation());
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_factory_method01() {
        test_factory_method();
    }
}
