// 定义一个结构体
#[allow(unused)]
pub struct User<T> {
    username: String,
    email: String,
    age: Option<T>,
}

// 定义一个Builder结构体
#[allow(unused)]
pub struct UserBuilder<T> {
    username: String,
    email: String,
    age: Option<T>,
}

impl<T> UserBuilder<T> {
    // 创建一个新的Builder实例
    fn new(username: &str, email: &str) -> Self {
        UserBuilder {
            username: username.to_string(),
            email: email.to_string(),
            age: None,
        }
    }

    // 设置年龄
    fn age(mut self, age: T) -> Self {
        self.age = Some(age);
        self
    }

    // 构建User实例
    fn build(self) -> User<T> {
        User {
            username: self.username,
            email: self.email,
            age: self.age,
        }
    }
}

#[allow(unused)]
pub fn test_builder() {
    // 使用Builder模式创建User实例
    let user = UserBuilder::new("Alice", "alice@example.com")
        .age(30) // 可选设置年龄
        .build();

    println!("用户名: {}, 邮箱: {}, 年龄: {:?}", user.username, user.email, user.age);

        // 使用Builder模式创建User实例，年龄为String类型
        let user2 = UserBuilder::new("Bob", "bob@example.com")
        .age("未知".to_string()) // 设置年龄为String
        .build();

    println!("用户名: {}, 邮箱: {}, 年龄: {:?}", user2.username, user2.email, user2.age);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_builder01() {
        test_builder();
    }
}
