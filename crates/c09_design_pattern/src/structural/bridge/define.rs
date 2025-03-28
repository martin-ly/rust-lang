// 定义实现部分的 trait
trait Implementor {
    fn operation_impl(&self) -> String;
}

// 定义具体的实现类 A
#[allow(unused)]
struct ConcreteImplementorA;

impl Implementor for ConcreteImplementorA {
    fn operation_impl(&self) -> String {
        "具体实现 A".to_string()
    }
}

// 定义具体的实现类 B
#[allow(unused)]
struct ConcreteImplementorB;

impl Implementor for ConcreteImplementorB {
    fn operation_impl(&self) -> String {
        "具体实现 B".to_string()
    }
}

// 定义抽象部分的 trait
trait Abstraction<T: Implementor> {
    fn operation(&self) -> String;
}

// 定义具体的抽象类
#[allow(unused)]
struct RefinedAbstraction<T: Implementor> {
    implementor: T,
}

impl<T: Implementor> Abstraction<T> for RefinedAbstraction<T> {
    fn operation(&self) -> String {
        format!("抽象操作: {}", self.implementor.operation_impl())
    }
}

// 示例使用
#[allow(unused)]
pub fn test_bridge() {
    let implementor_a = ConcreteImplementorA;
    let implementor_b = ConcreteImplementorB;

    let abstraction_a = RefinedAbstraction { implementor: implementor_a };
    let abstraction_b = RefinedAbstraction { implementor: implementor_b };

    println!("{}", abstraction_a.operation());
    println!("{}", abstraction_b.operation());
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bridge01() {
        test_bridge();
    }
}

