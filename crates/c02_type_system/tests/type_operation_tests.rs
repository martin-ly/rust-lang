//! `type_operation` 模块的集成测试。

use c02_type_system::type_operation::newtype::{Identifier, ProductId, UserId};
use c02_type_system::type_operation::subtype_relation::{Cat, Dog, make_sound};
use c02_type_system::type_operation::type_aliases::{Point, Result, distance};
use c02_type_system::type_operation::type_composition::{Circle, Rectangle, total_area};
use c02_type_system::type_operation::type_conversion::{Celsius, Fahrenheit, parse_i32};
use c02_type_system::type_operation::type_definition::{Point3D, Shape, area};
use c02_type_system::type_operation::type_equality::{alias_same_size, double};
use c02_type_system::type_operation::type_equivalence::{Coordinate, Meters};

#[test]
fn type_definition_and_area() {
    let circle = Shape::Circle {
        center: c02_type_system::type_operation::type_definition::Point { x: 0.0, y: 0.0 },
        radius: 1.0,
    };
    assert!((area(&circle) - std::f64::consts::PI).abs() < 1e-10);

    let p3d: Point3D = (1.0, 2.0, 3.0);
    assert_eq!(p3d.2, 3.0);
}

#[test]
fn type_conversion_roundtrip() {
    let f: Fahrenheit = Celsius(25.0).into();
    let c: Celsius = f.into();
    assert!((c.0 - 25.0).abs() < 1e-10);

    assert_eq!(parse_i32("99").unwrap(), 99);
}

#[test]
fn aliases_and_distance() {
    let a: Point = (0.0, 0.0);
    let b: Point = (3.0, 4.0);
    assert!((distance(a, b) - 5.0).abs() < 1e-10);

    let r: Result<i32> = Ok(7);
    assert_eq!(r.ok(), Some(7));
}

#[test]
fn newtype_distinctness() {
    let user = UserId(1);
    let product = ProductId(1);
    assert_eq!(user.0, product.0);
    assert_eq!(UserId::namespace(), "user");
    assert_eq!(ProductId::namespace(), "product");
}

#[test]
fn composition_total_area() {
    let circle = Circle(1.0);
    let rect = Rectangle(2.0, 3.0);
    let area = total_area(&[&circle, &rect]);
    assert!((area - (std::f64::consts::PI + 6.0)).abs() < 1e-10);
}

#[test]
fn type_equality_and_equivalence() {
    assert!(alias_same_size());
    assert_eq!(double(21_i32), 42);

    let c = Coordinate { x: 1.0, y: 2.0 };
    assert_eq!(c.to_tuple(), (1.0, 2.0));

    let m = Meters(10.0);
    assert_eq!(m.0, 10.0);
}

#[test]
fn subtype_relation() {
    assert_eq!(make_sound(Dog), "Woof");
    assert_eq!(make_sound(Cat), "Meow");

    let s: &'static str = "static";
    assert_eq!(make_sound(Dog), "Woof");
    assert_eq!(s, "static");
}
