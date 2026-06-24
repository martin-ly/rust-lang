//! # Rust 1.95.0 元组 Coercion 特性示例
//! # Rust 1.95.0 Coercion feature example
//! # 文件信息
//! # File Information
//! #
//! - 文件: rust_196_tuple_coercion.rs
//! - 创建日期: 2026-04-10
//! - date : 2026-04-10
//! - 版本: 1.0
//! - Version: 1.0
//! - this : 1.0
//! - 版this: 1.0

// use std::any::Any;
// use std::sync::Arc;

/// `if let` guards 允许在 match arm 上直接进行模式匹配和条件判断，
/// `if let` guards in match arm on and condition ，
/// 减少嵌套层级，使代码更扁平、更易读。
/// Decreases嵌套层级，使代码更扁平、更易读。
/// ，、。
pub struct TypeIfLetGuardExamples;

impl TypeIfLetGuardExamples {
    /// 安全地解析类型标识符
    /// type
    pub fn parse_type_id(input: Option<&str>) -> Result<usize, &'static str> {
        match input {
            Some(s) if let Ok(id) = s.parse::<usize>() => Ok(id),
            Some(_) => Err("类型标识符必须是数字"),
            None => Err("输入为空"),
        }
    }

    /// 验证类型转换结果
    /// Validates类型转换结果
    /// type conversion result
    pub fn validate_conversion(result: Result<Option<i32>, &'static str>) -> &'static str {
        match result {
            Ok(Some(v)) if v >= 0 => "非负整数",
            Ok(Some(_)) => "负数",
            Ok(None) => "空值",
            Err(_) => "转换错误",
        }
    }
}

// ==================== 1. 基础元组 Coercion ====================

/// # 基础元组 Coercion
/// # foundation Coercion
/// 这意味着可以在元组构造时自动进行类型转换。
/// can in type conversion 。
/// ## 主要特性
/// ## main feature
/// - 数组到切片的转换
/// - to conversion
/// - 函数指针的转换
/// - function pointer conversion
/// - 自定义类型的自动转换
/// - definition type conversion
pub mod basic_coercion {
    pub fn tuple_to_trait_object() {
        // 创建具体类型的引用
        let x: i32 = 42;
        let y: i64 = 100;

        // Rust 1.95.0: 元组元素自动 coercion 到 trait object
        // let tuple: (&dyn std::any::Any, &dyn std::any::Any) = (&x, &y);

        // 当前实现（等效代码）
        let tuple: (&dyn std::any::Any, &dyn std::any::Any) =
            (&x as &dyn std::any::Any, &y as &dyn std::any::Any);

        println!(
            "Tuple with trait objects: ({:?}, {:?})",
            tuple.0.type_id(),
            tuple.1.type_id()
        );
    }

    /// 展示元组中的数组到切片转换
    /// in to conversion
    pub fn tuple_array_to_slice() {
        let arr1 = [1, 2, 3];
        let arr2 = [4, 5, 6, 7, 8];

        // Rust 1.95.0: 元组元素自动 coercion 到切片
        // let tuple: (&[i32], &[i32]) = (&arr1, &arr2);

        // 当前实现
        let tuple: (&[i32], &[i32]) = (&arr1[..], &arr2[..]);

        println!("Tuple with slices: ({:?}, {:?})", tuple.0, tuple.1);
    }

    /// 展示元组中的函数指针转换
    /// in function pointer conversion
    /// Rust 1.95.0: 具体函数可以自动 coercion 到函数指针
    /// Rust 1.95.0: volume function can coercion to function pointer
    pub fn tuple_fn_pointer_coercion() {
        fn add_one(x: i32) -> i32 {
            x + 1
        }
        fn double(x: i32) -> i32 {
            x * 2
        }

        // Rust 1.95.0: 函数自动 coercion 到函数指针
        // let ops: (fn(i32) -> i32, fn(i32) -> i32) = (add_one, double);

        // 当前实现
        let ops: (fn(i32) -> i32, fn(i32) -> i32) =
            (add_one as fn(i32) -> i32, double as fn(i32) -> i32);

        println!(
            "Function pointer tuple: add_one(5)={}, double(5)={}",
            (ops.0)(5),
            (ops.1)(5)
        );
    }

    /// 展示元组中的自定义类型转换
    /// in definition type conversion
    /// 通过实现 From trait 实现自动转换
    /// From trait conversion
    #[derive(Debug, Clone)]
    pub struct Wrapper<T>(pub T);

    impl<T> From<T> for Wrapper<T> {
        fn from(value: T) -> Self {
            Wrapper(value)
        }
    }

    pub fn tuple_custom_coercion() {
        // Rust 1.95.0: 元组元素自动 coercion 到目标类型
        // let tuple: (Wrapper<i32>, Wrapper<String>) = (42, "hello".to_string());

        // 当前实现
        let tuple: (Wrapper<i32>, Wrapper<String>) =
            (Wrapper::from(42), Wrapper::from("hello".to_string()));

        println!("Custom coercion tuple: {:?}, {:?}", tuple.0, tuple.1);
    }
}

// ==================== 2. 嵌套元组 Coercion ====================

/// # 嵌套元组 Coercion
/// # Coercion
/// # 嵌套tuple Coercion
pub mod nested_coercion {
    // Wrapper not used, removed unused import

    pub fn nested_tuple_coercion() {
        let inner1 = (1, 2);
        let inner2 = (3, 4);

        // 嵌套元组的 coercion
        // Rust 1.95.0: 自动处理嵌套结构
        // let nested: ((Wrapper<i32>, Wrapper<i32>), (Wrapper<i32>, Wrapper<i32>)) =
        //     (inner1, inner2);

        // 当前实现
        let nested: ((Wrapper<i32>, Wrapper<i32>), (Wrapper<i32>, Wrapper<i32>)) = (
            (Wrapper(inner1.0), Wrapper(inner1.1)),
            (Wrapper(inner2.0), Wrapper(inner2.1)),
        );

        println!("Nested tuple: {:?}, {:?}", nested.0, nested.1);
    }

    pub fn higher_order_tuple_coercion() {
        let x = 1u8;
        let y = 2u16;
        let z = 3u32;

        // 三元组 coercion
        // Rust 1.95.0: 支持不同大小的整数提升到共同类型
        // let triple: (i64, i64, i64) = (x, y, z);

        // 当前实现
        let triple: (i64, i64, i64) = (x as i64, y as i64, z as i64);

        println!("Triple coercion: {:?}", triple);
    }

    pub fn tuple_array_coercion() {
        let tuples = [(1, 2), (3, 4), (5, 6)];

        // 元组数组元素的 coercion
        // Rust 1.95.0: 数组元素也可以进行 coercion
        // let wrapped: [(Wrapper<i32>, Wrapper<i32>); 3] = tuples;

        // 当前实现
        let wrapped: Vec<(Wrapper<i32>, Wrapper<i32>)> = tuples
            .iter()
            .map(|&(a, b)| (Wrapper(a), Wrapper(b)))
            .collect();

        println!("Tuple array coercion: {:?}", wrapped);
    }

    #[derive(Debug, Clone, Copy)]
    struct Wrapper<T>(T);
}

// ==================== 3. 智能指针与元组 Coercion ====================

pub mod smart_pointer_coercion {
    use std::rc::Rc;
    use std::sync::Arc;

    pub fn arc_coercion() {
        let x = Arc::new(42i32);
        let y = Arc::new("hello");

        // Arc 到 trait object 的 coercion
        // Rust 1.95.0: 元组中自动 coercion
        // let tuple: (Arc<dyn std::any::Any + Send + Sync>, Arc<dyn std::any::Any + Send + Sync>) =
        //     (x, y);

        // 当前实现
        let _tuple: (
            Arc<dyn std::any::Any + Send + Sync>,
            Arc<dyn std::any::Any + Send + Sync>,
        ) = (
            x as Arc<dyn std::any::Any + Send + Sync>,
            y as Arc<dyn std::any::Any + Send + Sync>,
        );

        println!("Arc coercion tuple created");
    }

    pub fn rc_coercion() {
        let _x = Rc::new(vec![1, 2, 3]);
        let _y = Rc::new(vec![4, 5, 6]);

        // Rc 到 trait object 的 coercion
        let tuple: (Rc<[i32]>, Rc<[i32]>) = (Rc::from(vec![1, 2, 3]), Rc::from(vec![4, 5, 6]));

        println!("Rc coercion tuple: {:?}, {:?}", tuple.0, tuple.1);
    }

    pub fn box_coercion() {
        trait Drawable {
            fn draw(&self);
        }

        struct Circle {
            radius: f64,
        }
        struct Rectangle {
            width: f64,
            height: f64,
        }

        impl Drawable for Circle {
            fn draw(&self) {
                println!("Drawing circle with radius {}", self.radius);
            }
        }

        impl Drawable for Rectangle {
            fn draw(&self) {
                println!("Drawing rectangle {}x{}", self.width, self.height);
            }
        }

        // Box 到 trait object 的 coercion
        // Rust 1.95.0: 元组中自动 coercion
        // let shapes: (Box<dyn Drawable>, Box<dyn Drawable>) =
        //     (Box::new(Circle { radius: 5.0 }), Box::new(Rectangle { width: 10.0, height: 20.0 }));

        // 当前实现
        let shapes: (Box<dyn Drawable>, Box<dyn Drawable>) = (
            Box::new(Circle { radius: 5.0 }) as Box<dyn Drawable>,
            Box::new(Rectangle {
                width: 10.0,
                height: 20.0,
            }) as Box<dyn Drawable>,
        );

        shapes.0.draw();
        shapes.1.draw();
    }
}

// ==================== 4. 生命周期与元组 Coercion ====================

pub mod lifetime_coercion {
    /// Rust 1.95.0: 正确传播生命周期约束
    /// Rust 1.95.0: propagation lifetime
    pub fn lifetime_propagation<'a>(x: &'a i32, y: &'a i32) -> (&'a i32, &'a i32) {
        // 返回元组时，生命周期自动传播
        (x, y)
    }

    pub fn static_lifetime_coercion() -> (&'static str, &'static str) {
        // 静态字符串的 coercion
        ("hello", "world")
    }

    pub fn elided_lifetime_coercion<'a>(s1: &'a str, s2: &'a str) -> (&'a str, &'a str) {
        // 生命周期省略规则仍然适用
        (s1, s2)
    }

    pub fn complex_lifetime<'a, 'b>(x: &'a i32, y: &'b str) -> (&'a i32, &'b str)
    where
        'a: 'b, // 'a 至少和 'b 一样长
    {
        (x, y)
    }
}

// ==================== 5. 实际应用场景 ====================

pub mod practical_applications {
    use std::collections::HashMap;

    /// 将不同类型的错误统一处理
    /// will type
    #[derive(Debug)]
    pub enum AppError {
        Io(std::io::Error),
        Parse(std::num::ParseIntError),
        Custom(String),
    }

    impl From<std::io::Error> for AppError {
        fn from(e: std::io::Error) -> Self {
            AppError::Io(e)
        }
    }

    impl From<std::num::ParseIntError> for AppError {
        fn from(e: std::num::ParseIntError) -> Self {
            AppError::Parse(e)
        }
    }

    /// 多结果处理
    /// result
    /// Rust 1.95.0: 自动 coercion 错误类型
    /// Rust 1.95.0: coercion error type
    /// Rust 1.95.0: 自动 coercion error type
    pub fn process_multiple_results() -> Result<(i32, String), AppError> {
        // 不同类型的错误自动 coercion 到 AppError
        // Rust 1.95.0: 在元组构造时自动处理
        let num: i32 = "42".parse()?;
        let text = "processed".to_string();

        Ok((num, text))
    }

    /// 配置参数传递
    /// parameter
    /// 使用元组传递不同类型但相关的配置
    /// type but
    pub struct Config {
        pub timeout: u64,
        pub retries: u32,
        pub enabled: bool,
    }

    impl From<(u64, u32, bool)> for Config {
        fn from(tuple: (u64, u32, bool)) -> Self {
            Config {
                timeout: tuple.0,
                retries: tuple.1,
                enabled: tuple.2,
            }
        }
    }

    /// 展示配置 coercion
    /// coercion
    pub fn create_config() -> Config {
        // Rust 1.95.0: 元组自动 coercion 到 Config
        // let config: Config = (30, 3, true);

        // 当前实现
        Config::from((30, 3, true))
    }

    /// 数据库查询结果处理
    /// database result
    /// 使用元组表示多列查询结果
    /// represent result
    pub fn process_query_results() -> Vec<(i32, String, Option<f64>)> {
        // 模拟数据库查询结果
        vec![
            (1, "Alice".to_string(), Some(95.5)),
            (2, "Bob".to_string(), Some(87.0)),
            (3, "Charlie".to_string(), None),
        ]
    }

    /// API 响应处理
    /// API
    /// API 响应Handle
    /// 使用元组表示 API 响应的不同部分
    /// represent API part
    /// Usetuplerepresent API 响应不同part
    pub type ApiResponse<T> = (u16, HashMap<String, String>, T);

    pub fn process_api_response<T>(response: ApiResponse<T>) -> T {
        let (status, headers, body) = response;
        println!("Status: {}, Headers: {:?}", status, headers);
        body
    }

    /// 坐标转换
    /// coordinate conversion
    pub trait Coordinate {
        fn to_cartesian(&self) -> (f64, f64, f64);
    }

    pub struct Polar {
        pub r: f64,
        pub theta: f64,
        pub phi: f64,
    }
    pub struct Cylindrical {
        pub rho: f64,
        pub phi: f64,
        pub z: f64,
    }

    impl Coordinate for Polar {
        fn to_cartesian(&self) -> (f64, f64, f64) {
            let x = self.r * self.theta.cos() * self.phi.sin();
            let y = self.r * self.theta.sin() * self.phi.sin();
            let z = self.r * self.phi.cos();
            (x, y, z)
        }
    }

    impl Coordinate for Cylindrical {
        fn to_cartesian(&self) -> (f64, f64, f64) {
            let x = self.rho * self.phi.cos();
            let y = self.rho * self.phi.sin();
            (x, y, self.z)
        }
    }

    /// 展示坐标 coercion
    /// coordinate coercion
    pub fn convert_coordinates(coords: &[Box<dyn Coordinate>]) -> Vec<(f64, f64, f64)> {
        // Rust 1.95.0: 元组结果自动 coercion
        coords.iter().map(|c| c.to_cartesian()).collect()
    }
}

// ==================== 6. 类型擦除与元组 ====================

/// # 类型擦除与元组
/// # type and
/// 展示元组在类型擦除中的应用。
/// in type in application 。
pub mod type_erasure {
    use std::any::Any;

    /// 异构元组存储
    pub struct HeterogeneousTuple {
        elements: Vec<Box<dyn Any>>,
    }

    impl Default for HeterogeneousTuple {
        fn default() -> Self {
            Self::new()
        }
    }

    impl HeterogeneousTuple {
        pub fn new() -> Self {
            Self {
                elements: Vec::new(),
            }
        }

        pub fn push<T: 'static>(&mut self, value: T) {
            self.elements.push(Box::new(value));
        }

        pub fn get<T: 'static>(&self, index: usize) -> Option<&T> {
            self.elements.get(index)?.downcast_ref::<T>()
        }
    }

    /// 使用元组进行类型擦除
    /// type
    pub fn create_heterogeneous_data() -> (Box<dyn Any>, Box<dyn Any>, Box<dyn Any>) {
        // 不同类型擦除到统一的 trait object
        let x: Box<dyn Any> = Box::new(42i32);
        let y: Box<dyn Any> = Box::new("hello".to_string());
        let z: Box<dyn Any> = Box::new(vec![1, 2, 3]);

        (x, y, z)
    }

    /// 动态分派元组
    /// 使用元组传递动态分派的函数
    /// function
    pub type DynFnTuple<'a> = (Box<dyn Fn() + 'a>, Box<dyn Fn(i32) -> i32 + 'a>);

    pub fn create_dynamic_functions() -> DynFnTuple<'static> {
        let f1: Box<dyn Fn()> = Box::new(|| println!("Hello from dynamic fn!"));
        let f2: Box<dyn Fn(i32) -> i32> = Box::new(|x| x * x);

        (f1, f2)
    }
}

// ==================== 7. 演示函数 ====================

/// 演示基础元组 coercion
/// Demonstrates基础元组 coercion
/// demonstration foundation coercion
#[allow(dead_code)]
pub fn demonstrate_basic_coercion() {
    println!("\n=== 基础元组 Coercion 演示 ===\n");

    basic_coercion::tuple_to_trait_object();
    basic_coercion::tuple_array_to_slice();
    basic_coercion::tuple_fn_pointer_coercion();
    basic_coercion::tuple_custom_coercion();
}

/// 演示嵌套元组 coercion
/// Demonstrates嵌套元组 coercion
/// demonstration coercion
/// Demonstration of嵌套tuple coercion
#[allow(dead_code)]
pub fn demonstrate_nested_coercion() {
    println!("\n=== 嵌套元组 Coercion 演示 ===\n");

    nested_coercion::nested_tuple_coercion();
    nested_coercion::higher_order_tuple_coercion();
    nested_coercion::tuple_array_coercion();
}

/// 演示智能指针 coercion
/// Demonstrates智能指针 coercion
/// demonstration pointer coercion
#[allow(dead_code)]
pub fn demonstrate_smart_pointer_coercion() {
    println!("\n=== 智能指针 Coercion 演示 ===\n");

    smart_pointer_coercion::arc_coercion();
    smart_pointer_coercion::rc_coercion();
    smart_pointer_coercion::box_coercion();
}

/// 演示实际应用场景
/// Demonstrates实际应用场景
/// demonstration actual application scenario
#[allow(dead_code)]
pub fn demonstrate_practical_applications() {
    println!("\n=== 实际应用场景演示 ===\n");

    // 配置创建
    let config = practical_applications::create_config();
    println!(
        "Config: timeout={}, retries={}, enabled={}",
        config.timeout, config.retries, config.enabled
    );

    // 查询结果处理
    let results = practical_applications::process_query_results();
    println!("Query results:");
    for (id, name, score) in results {
        match score {
            Some(s) => println!("  ID: {}, Name: {}, Score: {:.1}", id, name, s),
            None => println!("  ID: {}, Name: {}, Score: N/A", id, name),
        }
    }

    // 坐标转换
    use practical_applications::Coordinate;
    let polar = practical_applications::Polar {
        r: 1.0,
        theta: 0.0,
        phi: std::f64::consts::FRAC_PI_2,
    };
    let cartesian = polar.to_cartesian();
    println!("Polar to Cartesian: {:?}", cartesian);
}

/// 演示 Rust 1.95.0 元组 coercion 特性
/// Demonstrates Rust 1.95.0 元组 coercion 特性
/// demonstration Rust 1.95.0 coercion feature
pub fn demonstrate_rust_196_tuple_coercion() {
    println!("\n========================================");
    println!("   Rust 1.95.0 元组 Coercion 特性演示");
    println!("========================================\n");

    demonstrate_basic_coercion();
    demonstrate_nested_coercion();
    demonstrate_smart_pointer_coercion();
    demonstrate_practical_applications();

    println!("\n========================================");
    println!("   演示完成");
    println!("========================================\n");

    println!("说明: 元组 coercion 是 Rust 1.95.0 的稳定特性，");
    println!("      允许元组元素作为 coercion site 进行自动类型转换。");
}

/// 获取 Rust 1.95.0 元组 coercion 特性信息
/// Gets Rust 1.95.0 元组 coercion 特性信息
/// Rust 1.95.0 coercion feature
pub fn get_rust_196_tuple_info() -> String {
    "Rust 1.95.0 元组 Coercion 特性:\n- 元组元素作为 coercion site\n- 支持引用到 trait object \
     的转换\n- 支持数组到切片的转换\n- 支持智能指针的 coercion\n- 与生命周期系统正确交互"
        .to_string()
}

// ==================== 测试 ====================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lifetime_propagation() {
        let x = 42;
        let y = 100;
        let result = lifetime_coercion::lifetime_propagation(&x, &y);
        assert_eq!(*result.0, 42);
        assert_eq!(*result.1, 100);
    }

    #[test]
    fn test_static_lifetime_coercion() {
        let result = lifetime_coercion::static_lifetime_coercion();
        assert_eq!(result.0, "hello");
        assert_eq!(result.1, "world");
    }

    #[test]
    fn test_elided_lifetime_coercion() {
        let result = lifetime_coercion::elided_lifetime_coercion("foo", "bar");
        assert_eq!(result.0, "foo");
        assert_eq!(result.1, "bar");
    }

    #[test]
    fn test_complex_lifetime() {
        let x = 42;
        let y = "test";
        let result = lifetime_coercion::complex_lifetime(&x, y);
        assert_eq!(*result.0, 42);
        assert_eq!(result.1, "test");
    }

    #[test]
    fn test_config_creation() {
        let config = practical_applications::create_config();
        assert_eq!(config.timeout, 30);
        assert_eq!(config.retries, 3);
        assert!(config.enabled);
    }

    #[test]
    fn test_query_results() {
        let results = practical_applications::process_query_results();
        assert_eq!(results.len(), 3);
        assert_eq!(results[0].0, 1);
        assert_eq!(results[0].1, "Alice");
        assert_eq!(results[0].2, Some(95.5));
    }

    #[test]
    fn test_coordinate_conversion() {
        use practical_applications::{Coordinate, Polar};

        let polar = Polar {
            r: 1.0,
            theta: 0.0,
            phi: std::f64::consts::FRAC_PI_2,
        };
        let (x, y, z) = polar.to_cartesian();

        // r=1, theta=0, phi=pi/2 应该得到 (1, 0, 0)
        assert!((x - 1.0).abs() < 1e-10);
        assert!(y.abs() < 1e-10);
        assert!(z.abs() < 1e-10);
    }

    #[test]
    fn test_heterogeneous_tuple() {
        let mut tuple = type_erasure::HeterogeneousTuple::new();
        tuple.push(42i32);
        tuple.push("hello");
        tuple.push(vec![1, 2, 3]);

        assert_eq!(tuple.get::<i32>(0), Some(&42));
        assert_eq!(tuple.get::<&str>(1), Some(&"hello"));
        assert!(tuple.get::<f64>(0).is_none());
    }

    #[test]
    fn test_dynamic_functions() {
        let (f1, f2) = type_erasure::create_dynamic_functions();
        f1(); // 不应该 panic
        assert_eq!(f2(5), 25);
    }

    #[test]
    fn test_parse_type_id() {
        assert_eq!(TypeIfLetGuardExamples::parse_type_id(Some("42")), Ok(42));
        assert_eq!(
            TypeIfLetGuardExamples::parse_type_id(Some("abc")),
            Err("类型标识符必须是数字")
        );
        assert_eq!(TypeIfLetGuardExamples::parse_type_id(None), Err("输入为空"));
    }

    #[test]
    fn test_validate_conversion() {
        assert_eq!(
            TypeIfLetGuardExamples::validate_conversion(Ok(Some(10))),
            "非负整数"
        );
        assert_eq!(
            TypeIfLetGuardExamples::validate_conversion(Ok(Some(-5))),
            "负数"
        );
        assert_eq!(
            TypeIfLetGuardExamples::validate_conversion(Ok(None)),
            "空值"
        );
        assert_eq!(
            TypeIfLetGuardExamples::validate_conversion(Err("失败")),
            "转换错误"
        );
    }

    #[test]
    fn test_wrapper_coercion() {
        let tuple: (
            basic_coercion::Wrapper<i32>,
            basic_coercion::Wrapper<String>,
        ) = (
            basic_coercion::Wrapper::from(42),
            basic_coercion::Wrapper::from("test".to_string()),
        );
        assert_eq!(tuple.0.0, 42);
        assert_eq!(tuple.1.0, "test");
    }
}
