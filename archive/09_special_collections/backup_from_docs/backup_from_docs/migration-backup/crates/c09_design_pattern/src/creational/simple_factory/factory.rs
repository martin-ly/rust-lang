// 定义一个 trait，表示产品的接口
trait Product {
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

// 定义一个简单工厂
#[allow(unused)]
struct SimpleFactory;

impl SimpleFactory {
    // 创建产品的方法
    fn create_product(product_type: &str) -> Option<Box<dyn Product>> {
        match product_type {
            "A" => Some(Box::new(ConcreteProductA::default())),
            "B" => Some(Box::new(ConcreteProductB::default())),
            _ => None,
        }
    }
}

// 为产品实现 Default trait
impl Default for ConcreteProductA {
    fn default() -> Self {
        ConcreteProductA
    }
}

impl Default for ConcreteProductB {
    fn default() -> Self {
        ConcreteProductB
    }
}

#[allow(unused)]
pub fn test_simple_factory() {
    // 使用简单工厂创建产品 A
    if let Some(product_a) = SimpleFactory::create_product("A") {
        println!("{}", product_a.operation());
    }

    // 使用简单工厂创建产品 B
    if let Some(product_b) = SimpleFactory::create_product("B") {
        println!("{}", product_b.operation());
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_factory01() {
        test_simple_factory();
    }
}
