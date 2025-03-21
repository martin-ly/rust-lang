/*
在Rust中，特征（trait）是一种定义共享行为的机制。
特征（trait）：用于定义接口或行为的集合。
特征允许不同类型实现相同的方法，从而实现多态性。
特征定义：使用trait关键字定义特征。
特征实现：为类型实现特征，以便该类型可以满足特征的要求。
特征继承：特征可以继承其他特征，从而扩展其功能。
特征约束：特征可以作为泛型约束，限制泛型类型必须实现特定特征。

示例:
1. 默认实现：特征可以提供方法的默认实现，允许类型选择性地覆盖。
2. 特征约束：通过特征约束限制泛型类型，确保它们实现特定特征。
3. 特征组合：特征可以组合在一起，允许一个特征继承另一个特征的行为。
4. 特征对象：特征对象允许在运行时使用不同类型的对象，只要它们实现了相同的特征。
5. 关联类型：特征可以定义关联类型，使得特征的实现更加灵活。
6. 静态与动态调度：特征可以通过静态调度和动态调度来使用。
7. 泛型与特征：特征可以与泛型结合使用，以实现更灵活的代码。
8. 条件实现：可以根据特定条件实现特征，处理不同类型。

*/

/*
1. 特征的默认实现
    特征可以提供方法的默认实现，允许实现特征的类型选择性地覆盖这些方法。
*/

#[allow(unused)]
pub fn define_trait_01() {
    println!("1. 特征的默认实现");

    trait Speak {
        fn speak(&self) {
            println!("I am a default speaker.");
        }
    }
    
    struct Dog;
    struct Cat;
    
    impl Speak for Dog {
        fn speak(&self) {
            println!("Woof!");
        }
    }
    
    impl Speak for Cat {} // 使用默认实现

    let dog = Dog;
    let cat = Cat;

    dog.speak(); // 输出: Woof!
    cat.speak(); // 输出: I am a default speaker.

}

/*
2. 特征约束（Trait Bounds）
    特征约束用于限制泛型类型，确保它们实现了特定的特征。
    这在编写通用代码时非常有用。
*/

#[allow(unused)]
pub fn define_trait_02() {
    fn print_area<T: Shape>(shape: T) {
        println!("Area: {}", shape.area());
    }
    
    trait Shape {
        fn area(&self) -> f64;
    }
    
    struct Circle {
        radius: f64,
    }
    
    impl Shape for Circle {
        fn area(&self) -> f64 {
            std::f64::consts::PI * self.radius * self.radius
        }
    }
    println!("2. 特征约束");
    let circle = Circle { radius: 2.0 };
    print_area(circle); // 输出: Area: 12.566370614359172

}

/*
3. 特征组合
    特征继承（Trait Inheritance）
    特征组合允许一个特征继承另一个特征的行为。这在需要扩展特征功能时非常有用。
*/

#[allow(unused)]
pub fn define_trait_03() {
    trait Shape {
        fn area(&self) -> f64;
    }
    
    trait Color {
        fn color(&self) -> &str;
    }
    
    #[allow(unused)]
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

    println!("3. 特征组合继承");
    let circle = Circle { radius: 2.0 };
    println!("Area: {}", circle.area()); // 输出: Area: 12.566370614359172
    println!("Color: {}", circle.color()); // 输出: Color: Red
}

/*
4. 特征对象（Trait Objects）
    特征对象允许在运行时使用不同类型的对象，只要它们实现了相同的特征。这使得动态调度成为可能。
    特征对象可以用于处理不同类型，但需要确保类型实现了所需的特征。
*/  

#[allow(unused)]
pub fn define_trait_04(){
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

    println!("4. 特征对象");
    let dog = Dog;
    let cat = Cat;

    make_speak(&dog); // 输出: Woof!
    make_speak(&cat); // 输出: Meow!

}


/*
5. 关联类型（Associated Types）
    关联类型允许特征定义一个类型参数，该类型参数在特征的实现中可以被具体类型替换。
    这使得特征的实现更加灵活，可以处理不同类型的数据。
*/

#[allow(unused)]
pub fn define_trait_05(){
    #[allow(unused)]
    trait Container {
        type Item;
    
        fn add(&mut self, item: Self::Item);
    }
    
    struct Bag {
        items: Vec<String>,
    }
    
    impl Container for Bag {
        type Item = String;
    
        fn add(&mut self, item: Self::Item) {
            self.items.push(item);
        }
    }
    println!("5. 关联类型");
    let mut bag = Bag { items: Vec::new() };
    bag.add("Apple".to_string());
    bag.add("Banana".to_string());

    println!("{:?}", bag.items); // 输出: ["Apple", "Banana"]
    
}

/*
6. 静态与动态调度（Static vs Dynamic Dispatch）
    特征可以通过静态调度和动态调度来使用。静态调度在编译时确定类型，而动态调度在运行时确定类型。
*/

#[allow(unused)]
pub fn define_trait_06(){
    #[allow(unused)]
    trait Shape {
        fn area(&self) -> f64;
    }

    #[allow(unused)]
    fn print_shape<T: Shape>(shape: T) {
        println!("Area: {}", shape.area());
    }
    
    #[allow(unused)]
    fn print_shape_dynamic(shape: &dyn Shape) {
        println!("Area: {}", shape.area());
    }

    println!("6. 静态与动态调度");
}

/*
7. 泛型与特征（Generics and Traits）
    特征可以与泛型结合使用，以实现更灵活的代码。
*/

#[allow(unused)]
pub fn define_trait_07(){
    trait Summable {
        fn sum(&self) -> i32;
    }
    
    impl Summable for Vec<i32> {
        fn sum(&self) -> i32 {
            self.iter().sum()
        }
    }
    
    fn total<T: Summable>(items: T) -> i32 {
        items.sum()
    }
    
    println!("7. 泛型与特征");
    let numbers = vec![1, 2, 3, 4, 5];
    println!("Total: {}", total(numbers)); // 输出: Total: 15
    
}

/*
8. 条件实现（Conditional Implementation）
    可以根据特定条件实现特征，处理不同类型。
*/

#[allow(unused)]
pub fn define_trait_08(){
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
    
    println!("8. 条件实现");
    let number: i32 = 42;
    let text: String = String::from("Hello");

    println!("{}", number.describe()); // 输出: This is an integer: 42
    println!("{}", text.describe());    // 输出: This is a string: Hello

}
