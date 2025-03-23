#[allow(dead_code)]
#[derive(Copy, Clone)]
pub struct Product {
    id: i32,
}

#[allow(dead_code)]
impl Product {
    pub fn new(id: i32) -> Self {
        Product { id }
    }

    pub fn get_id(&self) -> i32 {
        self.id
    }
}

#[allow(dead_code)]
pub struct Factory;

#[allow(dead_code)]
impl Factory {
    pub fn create_product(&self, id: i32) -> Product {
        Product::new(id) // 使用 Move 语义返回新创建的产品
    }
}
