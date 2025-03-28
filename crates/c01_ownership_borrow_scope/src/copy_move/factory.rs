#[allow(unused)]
#[derive(Copy, Clone)]
pub struct Product {
    id: i32,
}

#[allow(unused)]
impl Product {
    pub fn new(id: i32) -> Self {
        Product { id }
    }

    pub fn get_id(&self) -> i32 {
        self.id
    }
}

#[allow(unused)]
pub struct Factory;

#[allow(unused)]
impl Factory {
    pub fn create_product(&self, id: i32) -> Product {
        Product::new(id) // 使用 Move 语义返回新创建的产品
    }
}
