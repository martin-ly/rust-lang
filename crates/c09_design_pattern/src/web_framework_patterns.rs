//! Web框架设计模式应用
//! 
//! 本模块展示了在Web框架中应用各种设计模式的实践案例，
//! 包括MVC、MVVM、Repository等经典模式。

use std::collections::HashMap;
use std::any::Any;

// ============================================================================
// MVC (Model-View-Controller) 模式
// ============================================================================

/// 用户模型
#[derive(Debug, Clone)]
pub struct User {
    pub id: u64,
    pub username: String,
    pub email: String,
    pub created_at: String,
}

/// 用户数据访问层
pub trait UserRepository {
    fn find_by_id(&self, id: u64) -> Option<User>;
    fn save(&mut self, user: User) -> Result<(), String>;
    fn delete(&mut self, id: u64) -> Result<(), String>;
    fn find_all(&self) -> Vec<User>;
}

/// 内存中的用户存储实现
pub struct InMemoryUserRepository {
    users: HashMap<u64, User>,
    next_id: u64,
}

impl InMemoryUserRepository {
    pub fn new() -> Self {
        Self {
            users: HashMap::new(),
            next_id: 1,
        }
    }
}

impl UserRepository for InMemoryUserRepository {
    fn find_by_id(&self, id: u64) -> Option<User> {
        self.users.get(&id).cloned()
    }

    fn save(&mut self, mut user: User) -> Result<(), String> {
        if user.id == 0 {
            user.id = self.next_id;
            self.next_id += 1;
        }
        self.users.insert(user.id, user);
        Ok(())
    }

    fn delete(&mut self, id: u64) -> Result<(), String> {
        self.users.remove(&id);
        Ok(())
    }

    fn find_all(&self) -> Vec<User> {
        self.users.values().cloned().collect()
    }
}

/// 用户控制器
pub struct UserController {
    repository: Box<dyn UserRepository>,
}

impl UserController {
    pub fn new(repository: Box<dyn UserRepository>) -> Self {
        Self { repository }
    }

    pub fn get_user(&self, id: u64) -> Option<User> {
        self.repository.find_by_id(id)
    }

    pub fn create_user(&mut self, username: String, email: String) -> Result<User, String> {
        let user = User {
            id: 0,
            username,
            email,
            created_at: "2025-01-27".to_string(),
        };
        self.repository.save(user.clone())?;
        Ok(user)
    }

    pub fn update_user(&mut self, user: User) -> Result<(), String> {
        self.repository.save(user)
    }

    pub fn delete_user(&mut self, id: u64) -> Result<(), String> {
        self.repository.delete(id)
    }

    pub fn list_users(&self) -> Vec<User> {
        self.repository.find_all()
    }
}

/// 视图接口
pub trait View {
    fn render(&self, data: &dyn Any) -> String;
}

/// HTML视图实现
pub struct HtmlView;

impl View for HtmlView {
    fn render(&self, data: &dyn Any) -> String {
        if let Some(users) = data.downcast_ref::<Vec<User>>() {
            let mut html = String::from("<html><body><h1>用户列表</h1><ul>");
            for user in users {
                html.push_str(&format!(
                    "<li>ID: {}, 用户名: {}, 邮箱: {}</li>",
                    user.id, user.username, user.email
                ));
            }
            html.push_str("</ul></body></html>");
            html
        } else {
            "数据格式错误".to_string()
        }
    }
}

/// JSON视图实现
pub struct JsonView;

impl View for JsonView {
    fn render(&self, data: &dyn Any) -> String {
        if let Some(users) = data.downcast_ref::<Vec<User>>() {
            format!("{:?}", users)
        } else {
            "数据格式错误".to_string()
        }
    }
}

// ============================================================================
// MVVM (Model-View-ViewModel) 模式
// ============================================================================

/// 用户视图模型
pub struct UserViewModel {
    users: Vec<User>,
    selected_user: Option<User>,
    search_term: String,
}

impl UserViewModel {
    pub fn new() -> Self {
        Self {
            users: Vec::new(),
            selected_user: None,
            search_term: String::new(),
        }
    }

    pub fn load_users(&mut self, users: Vec<User>) {
        self.users = users;
    }

    pub fn select_user(&mut self, id: u64) {
        self.selected_user = self.users.iter().find(|u| u.id == id).cloned();
    }

    pub fn set_search_term(&mut self, term: String) {
        self.search_term = term;
    }

    pub fn get_filtered_users(&self) -> Vec<User> {
        if self.search_term.is_empty() {
            self.users.clone()
        } else {
            self.users
                .iter()
                .filter(|user| {
                    user.username.contains(&self.search_term)
                        || user.email.contains(&self.search_term)
                })
                .cloned()
                .collect()
        }
    }

    pub fn get_selected_user(&self) -> Option<User> {
        self.selected_user.clone()
    }

    pub fn get_user_count(&self) -> usize {
        self.users.len()
    }
}

// ============================================================================
// Repository 模式扩展
// ============================================================================

/// 通用Repository接口
pub trait Repository<T> {
    fn find_by_id(&self, id: u64) -> Option<T>;
    fn save(&mut self, entity: T) -> Result<(), String>;
    fn delete(&mut self, id: u64) -> Result<(), String>;
    fn find_all(&self) -> Vec<T>;
    fn find_by_criteria(&self, criteria: &str) -> Vec<T>;
}

/// 文章模型
#[derive(Debug, Clone)]
pub struct Article {
    pub id: u64,
    pub title: String,
    pub content: String,
    pub author_id: u64,
    pub published: bool,
}

/// 文章Repository实现
pub struct ArticleRepository {
    articles: HashMap<u64, Article>,
    next_id: u64,
}

impl ArticleRepository {
    pub fn new() -> Self {
        Self {
            articles: HashMap::new(),
            next_id: 1,
        }
    }
}

impl Repository<Article> for ArticleRepository {
    fn find_by_id(&self, id: u64) -> Option<Article> {
        self.articles.get(&id).cloned()
    }

    fn save(&mut self, mut article: Article) -> Result<(), String> {
        if article.id == 0 {
            article.id = self.next_id;
            self.next_id += 1;
        }
        self.articles.insert(article.id, article);
        Ok(())
    }

    fn delete(&mut self, id: u64) -> Result<(), String> {
        self.articles.remove(&id);
        Ok(())
    }

    fn find_all(&self) -> Vec<Article> {
        self.articles.values().cloned().collect()
    }

    fn find_by_criteria(&self, criteria: &str) -> Vec<Article> {
        self.articles
            .values()
            .filter(|article| {
                article.title.contains(criteria)
                    || article.content.contains(criteria)
            })
            .cloned()
            .collect()
    }
}

// ============================================================================
// 单元测试
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mvc_pattern() {
        let mut repository = InMemoryUserRepository::new();
        let mut controller = UserController::new(Box::new(repository));

        // 创建用户
        let user = controller
            .create_user("test_user".to_string(), "test@example.com".to_string())
            .unwrap();
        assert_eq!(user.username, "test_user");

        // 获取用户
        let retrieved_user = controller.get_user(user.id);
        assert!(retrieved_user.is_some());
        assert_eq!(retrieved_user.unwrap().email, "test@example.com");

        // 测试视图
        let html_view = HtmlView;
        let users = controller.list_users();
        let html = html_view.render(&users);
        assert!(html.contains("test_user"));
    }

    #[test]
    fn test_mvvm_pattern() {
        let mut view_model = UserViewModel::new();
        let users = vec![
            User {
                id: 1,
                username: "user1".to_string(),
                email: "user1@example.com".to_string(),
                created_at: "2025-01-27".to_string(),
            },
            User {
                id: 2,
                username: "user2".to_string(),
                email: "user2@example.com".to_string(),
                created_at: "2025-01-27".to_string(),
            },
        ];

        view_model.load_users(users);
        assert_eq!(view_model.get_user_count(), 2);

        view_model.set_search_term("user1".to_string());
        let filtered = view_model.get_filtered_users();
        assert_eq!(filtered.len(), 1);
        assert_eq!(filtered[0].username, "user1");
    }

    #[test]
    fn test_repository_pattern() {
        let mut repository = ArticleRepository::new();
        let article = Article {
            id: 0,
            title: "Rust设计模式".to_string(),
            content: "本文介绍Rust中的设计模式".to_string(),
            author_id: 1,
            published: true,
        };

        repository.save(article).unwrap();
        let articles = repository.find_all();
        assert_eq!(articles.len(), 1);

        let found = repository.find_by_criteria("设计模式");
        assert_eq!(found.len(), 1);
        assert_eq!(found[0].title, "Rust设计模式");
    }
}
