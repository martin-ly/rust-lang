//! 针对 Rust 1.90 示例的基础断言测试

fn sum_array<const N: usize>(arr: [i32; N]) -> i32 { arr.iter().sum() }

#[test]
fn test_const_generics_sum() {
    assert_eq!(sum_array([1, 2, 3]), 6);
    assert_eq!(sum_array([1, 2, 3, 4]), 10);
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Point { x: i32, y: i32 }

#[test]
fn test_struct_destructure() {
    let p = Point { x: 7, y: -1 };
    let Point { x, y } = p;
    assert_eq!((x, y), (7, -1));
}

fn lifetime_passthrough<'a>(x: &'a i32) -> &'a i32 { x }

#[test]
fn test_lifetime_passthrough() {
    let v = 10;
    let r = lifetime_passthrough(&v);
    assert_eq!(*r, 10);
}


