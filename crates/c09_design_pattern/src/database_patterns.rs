//! 数据库系统设计模式应用
//!
//! 本模块展示了在数据库系统中应用各种设计模式的实践案例，
//! 包括DAO、Active Record、Unit of Work等经典模式。

use std::any::Any;
use std::collections::HashMap;

// ============================================================================
// DAO (Data Access Object) 模式
// ============================================================================

/// 数据库连接接口
pub trait DatabaseConnection {
    fn execute(&mut self, query: &str) -> Result<(), String>;
    fn query(&self, query: &str) -> Result<Vec<HashMap<String, String>>, String>;
    fn begin_transaction(&mut self) -> Result<(), String>;
    fn commit(&mut self) -> Result<(), String>;
    fn rollback(&mut self) -> Result<(), String>;
}

/// 模拟数据库连接
pub struct MockDatabaseConnection {
    data: HashMap<String, Vec<HashMap<String, String>>>,
    in_transaction: bool,
}

impl Default for MockDatabaseConnection {
    fn default() -> Self {
        Self::new()
    }
}

impl MockDatabaseConnection {
    pub fn new() -> Self {
        let mut data = HashMap::new();
        data.insert("users".to_string(), Vec::new());
        data.insert("products".to_string(), Vec::new());

        Self {
            data,
            in_transaction: false,
        }
    }
}

impl DatabaseConnection for MockDatabaseConnection {
    fn execute(&mut self, query: &str) -> Result<(), String> {
        if query.to_lowercase().contains("insert into users") {
            // 模拟插入用户
            let mut user = HashMap::new();
            user.insert("id".to_string(), "1".to_string());
            user.insert("name".to_string(), "John Doe".to_string());
            user.insert("email".to_string(), "john@example.com".to_string());

            if let Some(users) = self.data.get_mut("users") {
                users.push(user);
            }
        }
        Ok(())
    }

    fn query(&self, query: &str) -> Result<Vec<HashMap<String, String>>, String> {
        if query.to_lowercase().contains("select") && query.to_lowercase().contains("users") {
            Ok(self.data.get("users").cloned().unwrap_or_default())
        } else {
            Ok(Vec::new())
        }
    }

    fn begin_transaction(&mut self) -> Result<(), String> {
        self.in_transaction = true;
        Ok(())
    }

    fn commit(&mut self) -> Result<(), String> {
        self.in_transaction = false;
        Ok(())
    }

    fn rollback(&mut self) -> Result<(), String> {
        self.in_transaction = false;
        Ok(())
    }
}

/// 用户实体
#[derive(Debug, Clone)]
pub struct User {
    pub id: Option<i32>,
    pub name: String,
    pub email: String,
}

/// 用户DAO接口
pub trait UserDao {
    fn find_by_id(&self, id: i32) -> Result<Option<User>, String>;
    fn find_all(&self) -> Result<Vec<User>, String>;
    fn save(&mut self, user: &User) -> Result<i32, String>;
    fn update(&mut self, user: &User) -> Result<(), String>;
    fn delete(&mut self, id: i32) -> Result<(), String>;
}

/// 用户DAO实现
pub struct UserDaoImpl {
    connection: Box<dyn DatabaseConnection>,
}

impl UserDaoImpl {
    pub fn new(connection: Box<dyn DatabaseConnection>) -> Self {
        Self { connection }
    }
}

impl UserDao for UserDaoImpl {
    fn find_by_id(&self, id: i32) -> Result<Option<User>, String> {
        let query = format!("SELECT * FROM users WHERE id = {}", id);
        let results = self.connection.query(&query)?;

        if let Some(row) = results.first() {
            let user = User {
                id: Some(id),
                name: row.get("name").cloned().unwrap_or_default(),
                email: row.get("email").cloned().unwrap_or_default(),
            };
            Ok(Some(user))
        } else {
            Ok(None)
        }
    }

    fn find_all(&self) -> Result<Vec<User>, String> {
        let query = "SELECT * FROM users";
        let results = self.connection.query(query)?;

        let users = results
            .into_iter()
            .map(|row| User {
                id: row.get("id").and_then(|s| s.parse().ok()),
                name: row.get("name").cloned().unwrap_or_default(),
                email: row.get("email").cloned().unwrap_or_default(),
            })
            .collect();

        Ok(users)
    }

    fn save(&mut self, user: &User) -> Result<i32, String> {
        let query = format!(
            "INSERT INTO users (name, email) VALUES ('{}', '{}')",
            user.name, user.email
        );
        self.connection.execute(&query)?;
        Ok(1) // 模拟返回插入的ID
    }

    fn update(&mut self, user: &User) -> Result<(), String> {
        if let Some(id) = user.id {
            let query = format!(
                "UPDATE users SET name = '{}', email = '{}' WHERE id = {}",
                user.name, user.email, id
            );
            self.connection.execute(&query)?;
        }
        Ok(())
    }

    fn delete(&mut self, id: i32) -> Result<(), String> {
        let query = format!("DELETE FROM users WHERE id = {}", id);
        self.connection.execute(&query)?;
        Ok(())
    }
}

// ============================================================================
// Active Record 模式
// ============================================================================

/// Active Record基类
pub trait ActiveRecord {
    fn save(&mut self) -> Result<(), String>;
    fn delete(&mut self) -> Result<(), String>;
    fn find_by_id(id: i32) -> Result<Option<Self>, String>
    where
        Self: Sized;
    fn find_all() -> Result<Vec<Self>, String>
    where
        Self: Sized;
}

/// 产品实体（Active Record实现）
#[derive(Debug, Clone)]
pub struct Product {
    pub id: Option<i32>,
    pub name: String,
    pub price: f64,
    pub description: String,
}

impl Product {
    pub fn new(name: String, price: f64, description: String) -> Self {
        Self {
            id: None,
            name,
            price,
            description,
        }
    }

    pub fn set_id(&mut self, id: i32) {
        self.id = Some(id);
    }
}

impl ActiveRecord for Product {
    fn save(&mut self) -> Result<(), String> {
        if self.id.is_some() {
            // 更新
            let query = format!(
                "UPDATE products SET name = '{}', price = {}, description = '{}' WHERE id = {}",
                self.name,
                self.price,
                self.description,
                self.id.unwrap()
            );
            // 这里应该执行数据库操作
            println!("执行更新: {}", query);
        } else {
            // 插入
            let query = format!(
                "INSERT INTO products (name, price, description) VALUES ('{}', {}, '{}')",
                self.name, self.price, self.description
            );
            // 这里应该执行数据库操作
            println!("执行插入: {}", query);
            self.id = Some(1); // 模拟设置ID
        }
        Ok(())
    }

    fn delete(&mut self) -> Result<(), String> {
        if let Some(id) = self.id {
            let query = format!("DELETE FROM products WHERE id = {}", id);
            // 这里应该执行数据库操作
            println!("执行删除: {}", query);
        }
        Ok(())
    }

    fn find_by_id(id: i32) -> Result<Option<Self>, String> {
        // 模拟从数据库查找
        if id == 1 {
            Ok(Some(Product {
                id: Some(id),
                name: "示例产品".to_string(),
                price: 99.99,
                description: "这是一个示例产品".to_string(),
            }))
        } else {
            Ok(None)
        }
    }

    fn find_all() -> Result<Vec<Self>, String> {
        // 模拟从数据库查找所有产品
        Ok(vec![
            Product {
                id: Some(1),
                name: "产品1".to_string(),
                price: 99.99,
                description: "产品1描述".to_string(),
            },
            Product {
                id: Some(2),
                name: "产品2".to_string(),
                price: 199.99,
                description: "产品2描述".to_string(),
            },
        ])
    }
}

// ============================================================================
// Unit of Work 模式
// ============================================================================

/// 实体状态
#[derive(Debug, Clone, PartialEq)]
pub enum EntityState {
    Unchanged,
    Added,
    Modified,
    Deleted,
}

/// 实体跟踪器
pub struct EntityTracker<T> {
    entity: T,
    state: EntityState,
}

impl<T> EntityTracker<T> {
    pub fn new(entity: T) -> Self {
        Self {
            entity,
            state: EntityState::Unchanged,
        }
    }

    pub fn mark_as_added(&mut self) {
        self.state = EntityState::Added;
    }

    pub fn mark_as_modified(&mut self) {
        if self.state != EntityState::Added {
            self.state = EntityState::Modified;
        }
    }

    pub fn mark_as_deleted(&mut self) {
        self.state = EntityState::Deleted;
    }

    pub fn get_entity(&self) -> &T {
        &self.entity
    }

    pub fn get_entity_mut(&mut self) -> &mut T {
        &mut self.entity
    }

    pub fn get_state(&self) -> &EntityState {
        &self.state
    }
}

/// Unit of Work接口
pub trait UnitOfWork {
    fn register_new<T>(&mut self, entity: T)
    where
        T: 'static;
    fn register_dirty<T>(&mut self, entity: T)
    where
        T: 'static;
    fn register_deleted<T>(&mut self, entity: T)
    where
        T: 'static;
    fn commit(&mut self) -> Result<(), String>;
    fn rollback(&mut self) -> Result<(), String>;
}

/// Unit of Work实现
pub struct UnitOfWorkImpl {
    trackers: Vec<Box<dyn Any>>,
}

impl Default for UnitOfWorkImpl {
    fn default() -> Self {
        Self::new()
    }
}

impl UnitOfWorkImpl {
    pub fn new() -> Self {
        Self {
            trackers: Vec::new(),
        }
    }
}

impl UnitOfWork for UnitOfWorkImpl {
    fn register_new<T>(&mut self, entity: T)
    where
        T: 'static,
    {
        let mut tracker = EntityTracker::new(entity);
        tracker.mark_as_added();
        self.trackers.push(Box::new(tracker));
    }

    fn register_dirty<T>(&mut self, entity: T)
    where
        T: 'static,
    {
        let mut tracker = EntityTracker::new(entity);
        tracker.mark_as_modified();
        self.trackers.push(Box::new(tracker));
    }

    fn register_deleted<T>(&mut self, entity: T)
    where
        T: 'static,
    {
        let mut tracker = EntityTracker::new(entity);
        tracker.mark_as_deleted();
        self.trackers.push(Box::new(tracker));
    }

    fn commit(&mut self) -> Result<(), String> {
        // 模拟提交事务
        println!("提交事务，处理 {} 个实体", self.trackers.len());

        for tracker in &self.trackers {
            if let Some(user_tracker) = tracker.downcast_ref::<EntityTracker<User>>() {
                match user_tracker.get_state() {
                    EntityState::Added => println!("添加用户: {:?}", user_tracker.get_entity()),
                    EntityState::Modified => println!("修改用户: {:?}", user_tracker.get_entity()),
                    EntityState::Deleted => println!("删除用户: {:?}", user_tracker.get_entity()),
                    EntityState::Unchanged => {
                        println!("用户未变更: {:?}", user_tracker.get_entity())
                    }
                }
            }
        }

        self.trackers.clear();
        Ok(())
    }

    fn rollback(&mut self) -> Result<(), String> {
        println!("回滚事务");
        self.trackers.clear();
        Ok(())
    }
}

// ============================================================================
// Repository 模式与 Unit of Work 结合
// ============================================================================

/// 通用Repository接口
pub trait Repository<T> {
    fn add(&mut self, entity: T) -> Result<(), String>;
    fn update(&mut self, entity: T) -> Result<(), String>;
    fn delete(&mut self, entity: T) -> Result<(), String>;
    fn find_by_id(&self, id: i32) -> Result<Option<T>, String>;
    fn find_all(&self) -> Result<Vec<T>, String>;
}

/// 用户Repository实现
pub struct UserRepository {
    unit_of_work: UnitOfWorkImpl,
}

impl Default for UserRepository {
    fn default() -> Self {
        Self::new()
    }
}

impl UserRepository {
    pub fn new() -> Self {
        Self {
            unit_of_work: UnitOfWorkImpl::new(),
        }
    }

    pub fn commit(&mut self) -> Result<(), String> {
        self.unit_of_work.commit()
    }

    pub fn rollback(&mut self) -> Result<(), String> {
        self.unit_of_work.rollback()
    }
}

impl Repository<User> for UserRepository {
    fn add(&mut self, entity: User) -> Result<(), String> {
        self.unit_of_work.register_new(entity);
        Ok(())
    }

    fn update(&mut self, entity: User) -> Result<(), String> {
        self.unit_of_work.register_dirty(entity);
        Ok(())
    }

    fn delete(&mut self, entity: User) -> Result<(), String> {
        self.unit_of_work.register_deleted(entity);
        Ok(())
    }

    fn find_by_id(&self, id: i32) -> Result<Option<User>, String> {
        // 模拟从数据库查找
        if id == 1 {
            Ok(Some(User {
                id: Some(id),
                name: "John Doe".to_string(),
                email: "john@example.com".to_string(),
            }))
        } else {
            Ok(None)
        }
    }

    fn find_all(&self) -> Result<Vec<User>, String> {
        // 模拟从数据库查找所有用户
        Ok(vec![
            User {
                id: Some(1),
                name: "John Doe".to_string(),
                email: "john@example.com".to_string(),
            },
            User {
                id: Some(2),
                name: "Jane Smith".to_string(),
                email: "jane@example.com".to_string(),
            },
        ])
    }
}

// ============================================================================
// 单元测试
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dao_pattern() {
        let connection = MockDatabaseConnection::new();
        let mut dao = UserDaoImpl::new(Box::new(connection));

        let user = User {
            id: None,
            name: "Test User".to_string(),
            email: "test@example.com".to_string(),
        };

        let id = dao.save(&user).unwrap();
        assert_eq!(id, 1);

        let found_user = dao.find_by_id(1).unwrap();
        assert!(found_user.is_some());
    }

    #[test]
    fn test_active_record_pattern() {
        let mut product = Product::new(
            "测试产品".to_string(),
            99.99,
            "这是一个测试产品".to_string(),
        );

        // 保存产品
        product.save().unwrap();
        assert!(product.id.is_some());

        // 查找产品
        let found_product = Product::find_by_id(1).unwrap();
        assert!(found_product.is_some());
        assert_eq!(found_product.unwrap().name, "示例产品");

        // 查找所有产品
        let all_products = Product::find_all().unwrap();
        assert_eq!(all_products.len(), 2);
    }

    #[test]
    fn test_unit_of_work_pattern() {
        let mut unit_of_work = UnitOfWorkImpl::new();

        let user1 = User {
            id: None,
            name: "User 1".to_string(),
            email: "user1@example.com".to_string(),
        };

        let user2 = User {
            id: Some(2),
            name: "User 2".to_string(),
            email: "user2@example.com".to_string(),
        };

        // 注册新实体
        unit_of_work.register_new(user1);

        // 注册修改的实体
        unit_of_work.register_dirty(user2);

        // 提交事务
        unit_of_work.commit().unwrap();
    }

    #[test]
    fn test_repository_with_unit_of_work() {
        let mut repository = UserRepository::new();

        let user = User {
            id: None,
            name: "Test User".to_string(),
            email: "test@example.com".to_string(),
        };

        // 添加用户
        repository.add(user).unwrap();

        // 提交事务
        repository.commit().unwrap();

        // 查找用户
        let found_user = repository.find_by_id(1).unwrap();
        assert!(found_user.is_some());
    }
}
