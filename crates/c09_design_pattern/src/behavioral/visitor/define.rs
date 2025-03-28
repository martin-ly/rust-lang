// 定义一个访问者 trait
#[allow(unused)]
trait Visitor {
    fn visit_element_a(&self, element: &ElementA);
    fn visit_element_b(&self, element: &ElementB);
}

// 定义一个元素 trait
#[allow(unused)]
trait Element {
    fn accept(&self, visitor: &dyn Visitor);
}

// 具体元素 A
#[allow(unused)]
struct ElementA;
impl Element for ElementA {
    fn accept(&self, visitor: &dyn Visitor) {
        visitor.visit_element_a(self);
    }
}

// 具体元素 B
#[allow(unused)]
struct ElementB;
impl Element for ElementB {
    fn accept(&self, visitor: &dyn Visitor) {
        visitor.visit_element_b(self);
    }
}

// 具体访问者
#[allow(unused)]
struct ConcreteVisitor;
impl Visitor for ConcreteVisitor {
    fn visit_element_a(&self, _element: &ElementA) {
        println!("Visiting Element A");
    }

    fn visit_element_b(&self, _element: &ElementB) {
        println!("Visiting Element B");
    }
}

// 上下文
#[allow(unused)]
struct ObjectStructure {
    elements: Vec<Box<dyn Element>>,
}

impl ObjectStructure {
    fn new() -> Self {
        ObjectStructure {
            elements: Vec::new(),
        }
    }

    fn attach(&mut self, element: Box<dyn Element>) {
        self.elements.push(element);
    }

    fn accept(&self, visitor: &dyn Visitor) {
        for element in &self.elements {
            element.accept(visitor);
        }
    }
}

/*
代码说明
    访问者 Trait：
        定义了一个 Visitor trait，包含对不同元素的访问方法。
    元素 Trait：
        定义了一个 Element trait，包含一个 accept 方法，用于接受访问者。
    具体元素：
        实现了两个具体元素 ElementA 和 ElementB，它们实现了 accept 方法。
    具体访问者：
        实现了一个具体访问者 ConcreteVisitor，定义了对每个元素的访问操作。
    上下文：
        ObjectStructure 结构体用于管理元素，
        提供 attach 方法添加元素和 accept 方法接受访问者。
    执行访问：
        在函数中，创建了 ObjectStructure 的实例，添加了元素，并使用访问者进行访问。
*/

#[allow(unused)]
fn visitor_test() {
    let mut object_structure = ObjectStructure::new();
    object_structure.attach(Box::new(ElementA));
    object_structure.attach(Box::new(ElementB));

    let visitor = ConcreteVisitor;
    object_structure.accept(&visitor);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_visitor01() {
        visitor_test();
    }
}


