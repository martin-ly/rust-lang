//! `type_variance` 模块的集成测试。

use c02_type_system::type_variance::contravariance::{elided_handler, use_static_handler};
use c02_type_system::type_variance::covariance::{
    box_covariance, option_covariance, static_to_any,
};
use c02_type_system::type_variance::invariance::cell_invariance_example;

#[test]
fn covariance_lifetime_and_containers() {
    assert_eq!(static_to_any(), "static");

    let b: Box<&'static str> = Box::new("boxed");
    let b_any: Box<&str> = box_covariance(b);
    assert_eq!(*b_any, "boxed");

    let o: Option<&'static str> = Some("optional");
    let o_any: Option<&str> = option_covariance(o);
    assert_eq!(o_any, Some("optional"));
}

#[test]
fn invariance_cell_example() {
    cell_invariance_example();
}

#[test]
fn contravariance_function_pointer() {
    use_static_handler(elided_handler);
}
