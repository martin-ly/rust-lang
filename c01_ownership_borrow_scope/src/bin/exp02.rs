use c01_ownership_borrow_scope::copy_move::r#struct::*;

fn main() {
    let mut group = ShapeGroup::new();
    
    group.add_shape(Box::new(Circle { radius: 5.0 }));
    group.add_shape(Box::new(Rectangle { width: 4.0, height: 3.0 }));

    println!("Total area: {}", group.total_area());
}