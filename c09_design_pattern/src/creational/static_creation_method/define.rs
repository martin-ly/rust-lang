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

// 定义一个工厂结构体
#[allow(unused)]
struct Factory;

impl Factory {
    // 静态创建方法，使用泛型
    pub fn create_product<T: Product + Default>() -> T {
        T::default()
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

// 示例使用
#[allow(unused)]
pub fn test_static_creation_method() {
    let product_a: ConcreteProductA = Factory::create_product();
    println!("{}", product_a.operation());

    let product_b: ConcreteProductB = Factory::create_product();
    println!("{}", product_b.operation());
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_static_creation_method01() {
        test_static_creation_method();
    }
}

