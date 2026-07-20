// 定义目标接口
trait Target {
    fn request(&self) -> String;
}

// 定义一个具体的目标实现
#[allow(unused)]
struct ConcreteTarget;

impl Target for ConcreteTarget {
    fn request(&self) -> String {
        "具体目标的请求".to_string()
    }
}

// 定义一个适配者接口
trait Adaptee {
    fn specific_request(&self) -> String;
}

// 定义一个具体的适配者实现
#[allow(unused)]
struct ConcreteAdaptee;

impl Adaptee for ConcreteAdaptee {
    fn specific_request(&self) -> String {
        "具体适配者的请求".to_string()
    }
}

// 定义适配器结构体，使用泛型
#[allow(unused)]
struct Adapter<T: Adaptee> {
    adaptee: T,
}

impl<T: Adaptee> Target for Adapter<T> {
    fn request(&self) -> String {
        // 将适配者的请求转换为目标接口的请求
        self.adaptee.specific_request()
    }
}

// 示例使用
#[allow(unused)]
pub fn test_adapter() {
    let adaptee = ConcreteAdaptee;
    let adapter = Adapter { adaptee };

    // 使用适配器
    let target: &dyn Target = &adapter;
    println!("{}", target.request());
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_adapter01() {
        test_adapter();
    }
}
