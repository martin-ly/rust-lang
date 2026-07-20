// 定义一个 Flyweight trait
#[allow(unused)]
trait Flyweight {
    fn operation(&self, extrinsic_state: &str);
}

// 具体的 Flyweight 实现
#[allow(unused)]
struct ConcreteFlyweight<T> {
    intrinsic_state: T,
}

impl<T: std::fmt::Display> Flyweight for ConcreteFlyweight<T> {
    fn operation(&self, extrinsic_state: &str) {
        println!(
            "Intrinsic State: {}, Extrinsic State: {}",
            self.intrinsic_state, extrinsic_state
        );
    }
}

// Flyweight 工厂
#[allow(unused)]
struct FlyweightFactory<T> {
    flyweights: std::collections::HashMap<String, ConcreteFlyweight<T>>,
}

impl<T: std::hash::Hash + Eq + std::fmt::Display> FlyweightFactory<T> {
    #[allow(unused)]
    fn new() -> Self {
        FlyweightFactory {
            flyweights: std::collections::HashMap::new(),
        }
    }

    #[allow(unused)]
    fn get_flyweight(&mut self, key: &str, intrinsic_state: T) -> &ConcreteFlyweight<T> {
        if !self.flyweights.contains_key(key) {
            self.flyweights
                .insert(key.to_string(), ConcreteFlyweight { intrinsic_state });
        }
        self.flyweights.get(key).unwrap()
    }
}

// 使用示例
#[allow(unused)]
pub fn test_flyweight() {
    let mut factory = FlyweightFactory::new();

    let flyweight1 = factory.get_flyweight("A", "Intrinsic State A");
    flyweight1.operation("Extrinsic State 1");

    let flyweight2 = factory.get_flyweight("B", "Intrinsic State B");
    flyweight2.operation("Extrinsic State 2");

    let flyweight3 = factory.get_flyweight("A", "Intrinsic State A");
    flyweight3.operation("Extrinsic State 3");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_flyweight01() {
        test_flyweight();
    }
}
