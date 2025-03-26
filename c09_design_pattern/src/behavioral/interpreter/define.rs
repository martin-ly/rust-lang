use std::collections::HashMap;
use std::marker::PhantomData;

// 表达式 trait
trait Expression<T> {
    fn interpret(&self, context: &HashMap<String, T>) -> T;
}

// 具体表达式：常量
#[allow(unused)]
struct Constant<T> {
    value: T,
}

impl<T: Copy> Expression<T> for Constant<T> {
    fn interpret(&self, _context: &HashMap<String, T>) -> T {
        self.value
    }
}

// 具体表达式：变量
#[allow(unused)]
struct Variable<T> {
    name: String,
    _marker: PhantomData<T>, // 使用 PhantomData 占位
}

impl<T: Copy> Expression<T> for Variable<T> {
    fn interpret(&self, context: &HashMap<String, T>) -> T {
        *context.get(&self.name).expect("变量未定义")
    }
}

// 具体表达式：加法
#[allow(unused)]
struct Add<T> {
    left: Box<dyn Expression<T>>,
    right: Box<dyn Expression<T>>,
}

impl<T: Copy + std::ops::Add<Output = T>> Expression<T> for Add<T> {
    fn interpret(&self, context: &HashMap<String, T>) -> T {
        self.left.interpret(context) + self.right.interpret(context)
    }
}

// 具体表达式：减法
#[allow(unused)]
struct Subtract<T> {
    left: Box<dyn Expression<T>>,
    right: Box<dyn Expression<T>>,
}

impl<T: Copy + std::ops::Sub<Output = T>> Expression<T> for Subtract<T> {
    fn interpret(&self, context: &HashMap<String, T>) -> T {
        self.left.interpret(context) - self.right.interpret(context)
    }
}

/*
代码说明：
    表达式 Trait：
    定义了一个 Expression trait，包含 interpret 方法，用于解释表达式。

具体表达式：
    Constant：表示常量值。
    Variable：表示变量，通过上下文获取其值。
    Add：表示加法操作，包含两个表达式。
    Subtract：表示减法操作，包含两个表达式。
主函数：
    在主函数中创建上下文，定义表达式 x + y - 3，并解释该表达式。
*/
#[allow(unused)]
fn interpreter() {
    // 创建上下文
    let mut context = HashMap::new();
    context.insert("x".to_string(), 10);
    context.insert("y".to_string(), 5);

    // 表达式：x + y - 3
    let expression: Box<dyn Expression<i32>> = Box::new(Subtract {
        left: Box::new(Add {
            left: Box::new(Variable{
                name: "x".to_string(),
                _marker: PhantomData,
            }),
            right: Box::new(Variable{
                name: "y".to_string(),
                _marker: PhantomData,
            }),
        }),
        right: Box::new(Constant::<i32> { value: 3}),
    });

    // 解释表达式
    let result = expression.interpret(&context);
    println!("结果: {}", result); // 输出: 12
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_interpreter01() {
        interpreter();
    }
}
