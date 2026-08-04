// 定义组件 trait
trait Component {
    fn operation(&self) -> String;
}

// 定义叶子节点
#[allow(unused)]
struct Leaf<T> {
    name: T,
}

impl<T: ToString> Component for Leaf<T> {
    fn operation(&self) -> String {
        format!("叶子节点: {}", self.name.to_string())
    }
}

// 定义组合节点
#[allow(unused)]
struct Composite<T> {
    children: Vec<Box<dyn Component>>,
    name: T,
}

impl<T: ToString> Composite<T> {
    fn new(name: T) -> Self {
        Composite {
            children: Vec::new(),
            name,
        }
    }

    fn add(&mut self, component: Box<dyn Component>) {
        self.children.push(component);
    }
}

impl<T: ToString> Component for Composite<T> {
    fn operation(&self) -> String {
        let mut result = format!("组合节点: {}", self.name.to_string());
        for child in &self.children {
            result.push_str(&format!("\n  {}", child.operation()));
        }
        result
    }
}

// 示例使用
#[allow(unused)]
pub fn test_composite() {
    let leaf1 = Box::new(Leaf { name: "叶子1" });
    let leaf2 = Box::new(Leaf { name: "叶子2" });

    let mut composite = Composite::new("组合1");
    composite.add(leaf1);
    composite.add(leaf2);

    let leaf3 = Box::new(Leaf { name: "叶子3" });
    let mut composite2 = Composite::new("组合2");
    composite2.add(leaf3);
    composite2.add(Box::new(composite));

    println!("{}", composite2.operation());
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_composite01() {
        test_composite();
    }
}
