//! 生命周期专项测试
//!
//! 测试Rust生命周期系统的各种场景

// ============================================
// 显式生命周期
// ============================================

#[test]
fn test_explicit_lifetime_annotation() {
    fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
        if x.len() > y.len() { x } else { y }
    }
    
    let s1 = String::from("long string");
    let s2 = "short";
    let result = longest(&s1, s2);
    assert_eq!(result, "long string");
}

#[test]
fn test_different_lifetimes() {
    fn first<'a>(x: &'a str, _y: &str) -> &'a str {
        x  // 只与x的生命周期相关
    }
    
    let s1 = String::from("first");
    {
        let s2 = String::from("second");
        let result = first(&s1, &s2);
        assert_eq!(result, "first");
    }  // s2 结束，但result仍然有效
    
    // result 的生命周期与s1相同
}

// ============================================
// 生命周期省略
// ============================================

#[test]
fn test_lifetime_elision_rules() {
    // 规则1：每个引用参数获得独立生命周期
    fn rule1(x: &str) -> &str { x }
    fn rule1_explicit<'a>(x: &'a str) -> &'a str { x }
    
    // 规则2：只有一个输入时，输出使用相同生命周期
    fn rule2<'a>(x: &'a str, _y: &'a str) -> &'a str { x }
    fn rule2_explicit<'a, 'b>(x: &'a str, _y: &'b str) -> &'a str { x }
    
    // 规则3：&self方法，输出使用self的生命周期
    struct MyStruct<'a> {
        data: &'a str,
    }
    
    impl<'a> MyStruct<'a> {
        fn get_data(&self) -> &str { self.data }
    }
    
    let s = String::from("test");
    let obj = MyStruct { data: &s };
    assert_eq!(obj.get_data(), "test");
}

// ============================================
// 结构体生命周期
// ============================================

#[test]
fn test_struct_lifetime() {
    struct BorrowedString<'a> {
        data: &'a str,
    }
    
    let s = String::from("hello");
    let borrowed = BorrowedString { data: &s };
    assert_eq!(borrowed.data, "hello");
    // borrowed 必须在 s 之前结束
}

#[test]
fn test_multiple_lifetimes_struct() {
    struct TwoRefs<'a, 'b> {
        first: &'a str,
        second: &'b str,
    }
    
    let s1 = String::from("first");
    let result;
    {
        let s2 = String::from("second");
        let refs = TwoRefs {
            first: &s1,
            second: &s2,
        };
        result = refs.first;  // 只使用first
        assert_eq!(result, "first");
    }  // s2 结束，但result（引用s1）仍然有效
    
    assert_eq!(result, "first");
}

// ============================================
// 生命周期约束
// ============================================

#[test]
fn test_lifetime_bounds() {
    struct Parser<'a, 'b: 'a> {
        input: &'a str,
        pattern: &'b str,
    }
    
    impl<'a, 'b: 'a> Parser<'a, 'b> {
        fn parse(&self) -> Vec<&'a str> {
            self.input.split(self.pattern).collect()
        }
    }
    
    let input = String::from("a,b,c");
    let parser = Parser {
        input: &input,
        pattern: ",",
    };
    let result = parser.parse();
    assert_eq!(result, vec!["a", "b", "c"]);
}

// ============================================
// trait对象生命周期
// ============================================

#[test]
fn test_trait_object_lifetime() {
    trait Displayable {
        fn display(&self) -> &str;
    }
    
    struct Item<'a> {
        name: &'a str,
    }
    
    impl<'a> Displayable for Item<'a> {
        fn display(&self) -> &str {
            self.name
        }
    }
    
    fn show(item: &dyn Displayable) -> &str {
        item.display()
    }
    
    let s = String::from("item");
    let item = Item { name: &s };
    assert_eq!(show(&item), "item");
}

// ============================================
// 生命周期子类型
// ============================================

#[test]
fn test_variance() {
    struct Container<'a> {
        data: &'a str,
    }
    
    // 'static 是 'a 的子类型（对于任何'a）
    fn accept_any<'a>(_c: Container<'a>) {}
    
    let static_str: &'static str = "static";
    let c = Container { data: static_str };
    accept_any(c);  // 'static 可以转换为任何生命周期
}

// ============================================
// 高级生命周期模式
// ============================================

#[test]
fn test_lifetime_in_type_parameter() {
    fn process_with_closure<'a, F>(s: &'a str, f: F) -> String
    where
        F: Fn(&'a str) -> String,
    {
        f(s)
    }
    
    let s = String::from("hello");
    let result = process_with_closure(&s, |x| x.to_uppercase());
    assert_eq!(result, "HELLO");
}

#[test]
fn test_higher_rank_trait_bounds() {
    fn with_closure<F>(f: F)
    where
        F: for<'a> Fn(&'a str) -> usize,
    {
        let s1 = String::from("short");
        let s2 = String::from("loooong");
        assert_eq!(f(&s1), 5);
        assert_eq!(f(&s2), 7);
    }
    
    with_closure(|s| s.len());
}

// ============================================
// 生命周期与迭代器
// ============================================

#[test]
fn test_iterator_lifetime() {
    fn find_first<'a>(items: &'a [String], target: &str) -> Option<&'a String> {
        items.iter().find(|&s| s == target)
    }
    
    let items = vec![
        String::from("a"),
        String::from("b"),
        String::from("c"),
    ];
    let result = find_first(&items, "b");
    assert_eq!(result, Some(&String::from("b")));
}

// ============================================
// 生命周期与泛型
// ============================================

#[test]
fn test_lifetime_with_generic() {
    struct Wrapper<'a, T: 'a> {
        data: &'a T,
    }
    
    let value = 42i32;
    let wrapper = Wrapper { data: &value };
    assert_eq!(*wrapper.data, 42);
}

#[test]
fn test_lifetime_bounds_on_generics() {
    trait Processor<'a> {
        fn process(&self, input: &'a str) -> &'a str;
    }
    
    struct IdentityProcessor;
    
    impl<'a> Processor<'a> for IdentityProcessor {
        fn process(&self, input: &'a str) -> &'a str {
            input
        }
    }
    
    fn use_processor<'a, P>(p: &P, input: &'a str) -> &'a str
    where
        P: Processor<'a>,
    {
        p.process(input)
    }
    
    let processor = IdentityProcessor;
    let result = use_processor(&processor, "test");
    assert_eq!(result, "test");
}
