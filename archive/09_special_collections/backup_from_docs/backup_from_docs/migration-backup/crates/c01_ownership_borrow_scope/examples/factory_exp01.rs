use c01_ownership_borrow_scope::copy_move::factory::*;

fn main() {
    let factory = Factory;

    let product1 = factory.create_product(1); // 创建产品 1
    let product2 = factory.create_product(2); // 创建产品 2

    println!("Product 1 ID: {}", product1.get_id()); // 输出 1
    println!("Product 2 ID: {}", product2.get_id()); // 输出 2
}
