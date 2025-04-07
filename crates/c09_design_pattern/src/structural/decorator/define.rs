// 定义组件 trait
trait Component {
    fn operation(&self) -> String;
}

// 定义具体的组件
#[allow(unused)]
struct ConcreteComponent;

impl Component for ConcreteComponent {
    fn operation(&self) -> String {
        "具体组件的操作".to_string()
    }
}

// 定义装饰器结构体，使用泛型
#[allow(unused)]
struct Decorator<T: Component> {
    component: T,
}

impl<T: Component> Component for Decorator<T> {
    fn operation(&self) -> String {
        // 在调用原始组件的操作之前或之后添加额外的行为
        format!("装饰器的操作 + {}", self.component.operation())
    }
}

// 示例使用
#[allow(unused)]
pub fn test_decorator() {
    let component = ConcreteComponent;

    // 使用装饰器增强组件
    let decorated_component = Decorator { component };

    println!("{}", decorated_component.operation());
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_decorator01() {
        test_decorator();
    }
}
