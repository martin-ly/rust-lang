/*

1. 多重实现：Rust允许为不同类型实现相同的特征，使得代码更加灵活和可重用。
2. 约束与生命周期：特征可以与生命周期结合使用，以确保引用的有效性。
3. 条件实现：可以根据特定条件实现特征，处理不同类型。
4. 静态与动态调度：特征可以通过静态调度和动态调度来使用。
5. 组合与继承：特征可以组合在一起，允许一个特征继承另一个特征的行为。
6. 关联常量：特征可以定义关联常量，使得特征的实现更加灵活。
7. 动态分发与性能：使用特征对象时，Rust会进行动态分发，可能影响性能。

*/

/*
1. 特征的多重实现
Rust允许为不同类型实现相同的特征，这使得代码更加灵活和可重用。
*/

#[allow(unused)]
pub fn advance_trait_01(){
    trait Describable {
        fn describe(&self) -> String;
    }
    
    struct Dog;
    struct Cat;
    
    impl Describable for Dog {
        fn describe(&self) -> String {
            String::from("This is a dog.")
        }
    }
    
    impl Describable for Cat {
        fn describe(&self) -> String {
            String::from("This is a cat.")
        }
    }
    
    fn print_description<T: Describable>(item: T) {
        println!("{}", item.describe());
    }
    
    println!("1. 特征的多重实现");
    let dog = Dog;
    let cat = Cat;

    print_description(dog); // 输出: This is a dog.
    print_description(cat);  // 输出: This is a cat.
    
}

/*
2. 特征的约束与生命周期
特征可以与生命周期结合使用，以确保引用的有效性。
*/

#[allow(unused)]
pub fn advance_trait_02(){
    trait Displayable<'a> {
        fn display(&self) -> &'a str;
    }
    
    struct Message<'a> {
        content: &'a str,
    }
    
    impl<'a> Displayable<'a> for Message<'a> {
        fn display(&self) -> &'a str {
            self.content
        }
    }
    
    println!("2. 特征的约束与生命周期");
    let msg = Message { content: "Hello, Rust!" };
    println!("{}", msg.display()); // 输出: Hello, Rust!
    
}


/*
3. 特征的条件实现（特征约束）
可以根据特定条件实现特征，这在处理不同类型时非常有用。
*/

#[allow(unused)]
pub fn advance_trait_03(){
    trait Summable {
        fn sum(&self) -> i32;
    }
    
    impl Summable for Vec<i32> {
        fn sum(&self) -> i32 {
            self.iter().sum()
        }
    }
    
    impl Summable for (i32, i32) {
        fn sum(&self) -> i32 {
            self.0 + self.1
        }
    }
    
    fn total<T: Summable>(items: T) -> i32 {
        items.sum()
    }
    
    println!("3. 特征的条件实现（特征约束）");
    let numbers = vec![1, 2, 3, 4, 5];
    let tuple = (10, 20);

    println!("Total of vector: {}", total(numbers)); // 输出: Total of vector: 15
    println!("Total of tuple: {}", total(tuple));    // 输出: Total of tuple: 30
    
}

/*
4. 特征的静态与动态调度
    Rust中的特征可以通过静态调度（在编译时确定类型）和动态调度（在运行时确定类型）来使用。

*/

#[allow(unused)]
pub fn advance_trait_04(){
    trait Shape {
        fn area(&self) -> f64;
    }

    fn print_shape<T: Shape>(shape: T) {
        println!("Area: {}", shape.area());
    }
    fn print_shape_dynamic(shape: &dyn Shape) {
        println!("Area: {}", shape.area());
    }

    println!("4. 特征的静态与动态调度");
}


/*
5. 特征的组合与继承
特征可以组合在一起，允许一个特征继承另一个特征的行为。
*/

#[allow(unused)]
pub fn advance_trait_05(){
    trait Shape {
        fn area(&self) -> f64;
    }
    
    trait Color {
        fn color(&self) -> &str;
    }
    
    trait ColoredShape: Shape + Color {}
    
    struct Circle {
        radius: f64,
    }
    
    impl Shape for Circle {
        fn area(&self) -> f64 {
            std::f64::consts::PI * self.radius * self.radius
        }
    }
    
    impl Color for Circle {
        fn color(&self) -> &str {
            "Red"
        }
    }
    
    impl ColoredShape for Circle {}
        
    println!("5. 特征的组合与继承");
    let circle = Circle { radius: 2.0 };
    println!("Area: {}", circle.area()); // 输出: Area: 12.566370614359172
    println!("Color: {}", circle.color()); // 输出: Color: Red

}


/*
6. 特征的关联常量
特征可以定义关联常量，使得特征的实现更加灵活。
*/


#[allow(unused)]
pub fn advance_trait_06(){
    trait Constants {
        const PI: f64;
    }
    
    struct Circle;
    
    impl Constants for Circle {
        const PI: f64 = 3.14159;
    }
    
    println!("6. 特征的关联常量");
    println!("Circle PI: {}", Circle::PI); // 输出: Circle PI: 3.14159
    
}


/*
7. 特征的条件实现与泛型
特征可以与泛型结合使用，以实现更灵活的代码。    
*/

#[allow(unused)]
pub fn advance_trait_07(){
    trait Describable {
        fn describe(&self) -> String;
    }
    
    impl Describable for i32 {
        fn describe(&self) -> String {
            format!("This is an integer: {}", self)
        }
    }
    
    impl Describable for String {
        fn describe(&self) -> String {
            format!("This is a string: {}", self)
        }
    }
    
    fn print_description<T: Describable>(item: T) {
        println!("{}", item.describe());
    }
    
    println!("7. 特征的条件实现与泛型");
    let number: i32 = 42;
    let text: String = String::from("Hello");

    print_description(number); // 输出: This is an integer: 42
    print_description(text);    // 输出: This is a string: Hello
    
}

/*
8. 特征的动态分发与性能
    使用特征对象时，Rust会进行动态分发，这可能会影响性能。
    在性能敏感的场景中，考虑使用静态分发。
*/

#[allow(unused)]
pub fn advance_trait_08(){
    trait Speak {
        fn speak(&self);
    }
    
    struct Dog;
    struct Cat;
    
    impl Speak for Dog {
        fn speak(&self) {
            println!("Woof!");
        }
    }
    
    impl Speak for Cat {
        fn speak(&self) {
            println!("Meow!");
        }
    }
    
    fn make_speak(speaker: &dyn Speak) {
        speaker.speak();
    }
    
    println!("8. 特征的动态分发与性能");
    let dog = Dog;
    let cat = Cat;

    make_speak(&dog); // 输出: Woof!
    make_speak(&cat); // 输出: Meow!
    
}
