// 定义一个模板 trait
#[allow(unused)]
trait Template {
    fn template_method(&self) {
        self.step_one();
        self.step_two();
        self.step_three();
    }

    fn step_one(&self);
    fn step_two(&self);
    fn step_three(&self);
}

// 实现具体模板
#[allow(unused)]
struct ConcreteClassA;
impl Template for ConcreteClassA {
    fn step_one(&self) {
        println!("ConcreteClassA: Step One");
    }

    fn step_two(&self) {
        println!("ConcreteClassA: Step Two");
    }

    fn step_three(&self) {
        println!("ConcreteClassA: Step Three");
    }
}

#[allow(unused)]
struct ConcreteClassB;
impl Template for ConcreteClassB {
    fn step_one(&self) {
        println!("ConcreteClassB: Step One");
    }

    fn step_two(&self) {
        println!("ConcreteClassB: Step Two");
    }

    fn step_three(&self) {
        println!("ConcreteClassB: Step Three");
    }
}

// 上下文结构体，使用泛型来接受不同的模板
#[allow(unused)]
struct Context<T: Template> {
    template: T,
}

#[allow(unused)]
impl<T: Template> Context<T> {
    fn new(template: T) -> Self {
        Context { template }
    }

    fn execute_template(&self) {
        self.template.template_method();
    }
}

/*
代码说明
    模板 Trait：
        定义了一个 Template trait，包含一个 template_method 方法。
        三个步骤方法 step_one、step_two 和 step_three。
    具体模板：
        ConcreteClassA 和 ConcreteClassB 是实现了 Template trait 的具体模板。
    上下文：
        Context 结构体使用泛型 T 来接受任何实现了 Template trait 的模板。
    执行模板：
        Context 的实例可以执行模板方法。
*/

#[allow(unused)]
fn template_method_test() {
    let context_a = Context::new(ConcreteClassA);
    context_a.execute_template();

    let context_b = Context::new(ConcreteClassB);
    context_b.execute_template();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_template_method01() {
        template_method_test();
    }
}
