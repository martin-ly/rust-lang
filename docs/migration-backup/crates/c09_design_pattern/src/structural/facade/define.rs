// 定义子系统 A
#[allow(unused)]
struct SubsystemA;

impl SubsystemA {
    fn operation_a(&self) -> String {
        "子系统 A 的操作".to_string()
    }
}

// 定义子系统 B
#[allow(unused)]
struct SubsystemB;

impl SubsystemB {
    fn operation_b(&self) -> String {
        "子系统 B 的操作".to_string()
    }
}

// 定义外观结构体，使用泛型
#[allow(unused)]
struct Facade<A: Subsystem, B: Subsystem> {
    subsystem_a: A,
    subsystem_b: B,
}

impl<A: Subsystem, B: Subsystem> Facade<A, B> {
    fn new(subsystem_a: A, subsystem_b: B) -> Self {
        Facade {
            subsystem_a,
            subsystem_b,
        }
    }

    // 定义外观操作，调用子系统的操作
    fn operation(&self) -> String {
        format!(
            "{}\n{}",
            self.subsystem_a.operation_a(),
            self.subsystem_b.operation_b()
        )
    }
}

// 定义一个 trait 以便于使用泛型
trait Subsystem {
    fn operation_a(&self) -> String;
    fn operation_b(&self) -> String;
}

// 为子系统 A 和 B 实现 Subsystem trait
impl Subsystem for SubsystemA {
    fn operation_a(&self) -> String {
        self.operation_a()
    }

    fn operation_b(&self) -> String {
        "子系统 A 不支持 B 的操作".to_string()
    }
}

impl Subsystem for SubsystemB {
    fn operation_a(&self) -> String {
        "子系统 B 不支持 A 的操作".to_string()
    }

    fn operation_b(&self) -> String {
        self.operation_b()
    }
}

// 示例使用
#[allow(unused)]
pub fn test_facade() {
    let subsystem_a = SubsystemA;
    let subsystem_b = SubsystemB;

    let facade = Facade::new(subsystem_a, subsystem_b);
    println!("{}", facade.operation());
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_facade01() {
        test_facade();
    }
}
