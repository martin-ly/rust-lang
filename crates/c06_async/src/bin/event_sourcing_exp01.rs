use anyhow::{Result, anyhow};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;
use uuid::Uuid;

/// 领域事件基类
#[derive(Debug, Clone, Serialize, Deserialize)]
struct DomainEvent {
    id: String,
    aggregate_id: String,
    event_type: String,
    timestamp: u64,
    version: u32,
    data: serde_json::Value,
}

impl DomainEvent {
    fn new(aggregate_id: &str, event_type: &str, data: serde_json::Value) -> Self {
        Self {
            id: Uuid::new_v4().to_string(),
            aggregate_id: aggregate_id.to_string(),
            event_type: event_type.to_string(),
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap_or_default()
                .as_secs(),
            version: 1,
            data,
        }
    }
}

/// 用户聚合根
#[derive(Debug, Clone, Serialize, Deserialize)]
struct User {
    id: String,
    username: String,
    email: String,
    status: UserStatus,
    created_at: u64,
    updated_at: u64,
    version: u32,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
enum UserStatus {
    Active,
    Inactive,
    Suspended,
}

impl User {
    fn new(username: String, email: String) -> Self {
        let now = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap_or_default()
            .as_secs();

        Self {
            id: Uuid::new_v4().to_string(),
            username,
            email,
            status: UserStatus::Active,
            created_at: now,
            updated_at: now,
            version: 1,
        }
    }

    fn apply_event(&mut self, event: &DomainEvent) {
        match event.event_type.as_str() {
            "UserCreated" => {
                // 用户创建事件已在构造函数中处理
            }
            "UserUpdated" => {
                if let Some(data) = event.data.as_object() {
                    if let Some(username) = data.get("username").and_then(|v| v.as_str()) {
                        self.username = username.to_string();
                    }
                    if let Some(email) = data.get("email").and_then(|v| v.as_str()) {
                        self.email = email.to_string();
                    }
                }
                self.updated_at = event.timestamp;
            }
            "UserStatusChanged" => {
                if let Some(data) = event.data.as_object() {
                    if let Some(status) = data.get("status").and_then(|v| v.as_str()) {
                        self.status = match status {
                            "active" => UserStatus::Active,
                            "inactive" => UserStatus::Inactive,
                            "suspended" => UserStatus::Suspended,
                            _ => UserStatus::Active,
                        };
                    }
                }
                self.updated_at = event.timestamp;
            }
            _ => {}
        }
        self.version = event.version;
    }
}

/// 事件存储
struct EventStore {
    events: Arc<RwLock<HashMap<String, Vec<DomainEvent>>>>,
}

impl EventStore {
    fn new() -> Self {
        Self {
            events: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// 存储事件
    async fn store_event(&self, event: DomainEvent) -> Result<()> {
        let mut events = self.events.write().await;
        let aggregate_events = events
            .entry(event.aggregate_id.clone())
            .or_insert_with(Vec::new);

        let event_type = event.event_type.clone();
        let aggregate_id = event.aggregate_id.clone();
        aggregate_events.push(event);
        println!("📝 事件已存储: {} -> {}", event_type, aggregate_id);
        Ok(())
    }

    /// 获取聚合的所有事件
    async fn get_events(&self, aggregate_id: &str) -> Vec<DomainEvent> {
        let events = self.events.read().await;
        events.get(aggregate_id).cloned().unwrap_or_default()
    }

    /// 获取所有事件
    async fn get_all_events(&self) -> Vec<DomainEvent> {
        let events = self.events.read().await;
        events.values().flatten().cloned().collect()
    }
}

/// 命令处理器
struct CommandHandler {
    event_store: Arc<EventStore>,
}

impl CommandHandler {
    fn new(event_store: Arc<EventStore>) -> Self {
        Self { event_store }
    }

    /// 创建用户
    async fn create_user(&self, username: String, email: String) -> Result<String> {
        let user = User::new(username, email);

        let event = DomainEvent::new(
            &user.id,
            "UserCreated",
            serde_json::json!({
                "username": user.username,
                "email": user.email,
                "status": "active"
            }),
        );

        self.event_store.store_event(event).await?;
        println!("✅ 用户已创建: {}", user.id);
        Ok(user.id)
    }

    /// 更新用户
    async fn update_user(
        &self,
        user_id: &str,
        username: Option<String>,
        email: Option<String>,
    ) -> Result<()> {
        let events = self.event_store.get_events(user_id).await;
        if events.is_empty() {
            return Err(anyhow!("用户不存在: {}", user_id));
        }

        let mut data = serde_json::Map::new();
        if let Some(username) = username {
            data.insert("username".to_string(), serde_json::Value::String(username));
        }
        if let Some(email) = email {
            data.insert("email".to_string(), serde_json::Value::String(email));
        }

        let event = DomainEvent::new(user_id, "UserUpdated", serde_json::Value::Object(data));

        self.event_store.store_event(event).await?;
        println!("✅ 用户已更新: {}", user_id);
        Ok(())
    }

    /// 更改用户状态
    async fn change_user_status(&self, user_id: &str, status: &str) -> Result<()> {
        let events = self.event_store.get_events(user_id).await;
        if events.is_empty() {
            return Err(anyhow!("用户不存在: {}", user_id));
        }

        let event = DomainEvent::new(
            user_id,
            "UserStatusChanged",
            serde_json::json!({
                "status": status
            }),
        );

        self.event_store.store_event(event).await?;
        println!("✅ 用户状态已更改: {} -> {}", user_id, status);
        Ok(())
    }
}

/// 查询处理器 (CQRS 的查询端)
struct QueryHandler {
    event_store: Arc<EventStore>,
    read_models: Arc<RwLock<HashMap<String, User>>>,
}

impl QueryHandler {
    fn new(event_store: Arc<EventStore>) -> Self {
        Self {
            event_store,
            read_models: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// 构建读取模型
    async fn build_read_models(&self) -> Result<()> {
        let all_events = self.event_store.get_all_events().await;
        let mut read_models = self.read_models.write().await;
        read_models.clear();

        // 按聚合 ID 分组事件
        let mut events_by_aggregate: HashMap<String, Vec<DomainEvent>> = HashMap::new();
        for event in all_events {
            events_by_aggregate
                .entry(event.aggregate_id.clone())
                .or_insert_with(Vec::new)
                .push(event);
        }

        // 为每个聚合构建读取模型
        for (aggregate_id, events) in events_by_aggregate {
            let mut user = User::new("".to_string(), "".to_string());
            user.id = aggregate_id.clone();

            for event in events {
                user.apply_event(&event);
            }

            read_models.insert(aggregate_id, user);
        }

        println!("📊 读取模型已构建，共 {} 个用户", read_models.len());
        Ok(())
    }

    /// 获取用户
    async fn get_user(&self, user_id: &str) -> Option<User> {
        let read_models = self.read_models.read().await;
        read_models.get(user_id).cloned()
    }

    /// 获取所有用户
    async fn get_all_users(&self) -> Vec<User> {
        let read_models = self.read_models.read().await;
        read_models.values().cloned().collect()
    }

    /// 按状态查询用户
    async fn get_users_by_status(&self, status: &str) -> Vec<User> {
        let read_models = self.read_models.read().await;
        read_models
            .values()
            .filter(|user| {
                matches!(
                    (status, &user.status),
                    ("active", UserStatus::Active)
                        | ("inactive", UserStatus::Inactive)
                        | ("suspended", UserStatus::Suspended)
                )
            })
            .cloned()
            .collect()
    }
}

/// 事件溯源系统
struct EventSourcingSystem {
    event_store: Arc<EventStore>,
    command_handler: Arc<CommandHandler>,
    query_handler: Arc<QueryHandler>,
}

impl EventSourcingSystem {
    fn new() -> Self {
        let event_store = Arc::new(EventStore::new());
        let command_handler = Arc::new(CommandHandler::new(Arc::clone(&event_store)));
        let query_handler = Arc::new(QueryHandler::new(Arc::clone(&event_store)));

        Self {
            event_store,
            command_handler,
            query_handler,
        }
    }

    /// 运行事件溯源示例
    async fn run_example(&self) -> Result<()> {
        println!("🚀 事件溯源示例启动");
        println!("{}", "=".repeat(50));

        // 1. 创建用户
        println!("\n📝 创建用户...");
        let user1_id = self
            .command_handler
            .create_user("alice".to_string(), "alice@example.com".to_string())
            .await?;

        let user2_id = self
            .command_handler
            .create_user("bob".to_string(), "bob@example.com".to_string())
            .await?;

        // 2. 更新用户
        println!("\n📝 更新用户...");
        self.command_handler
            .update_user(&user1_id, Some("alice_updated".to_string()), None)
            .await?;

        // 3. 更改用户状态
        println!("\n📝 更改用户状态...");
        self.command_handler
            .change_user_status(&user2_id, "suspended")
            .await?;

        // 4. 构建读取模型
        println!("\n📊 构建读取模型...");
        self.query_handler.build_read_models().await?;

        // 5. 查询用户
        println!("\n🔍 查询用户...");
        if let Some(user) = self.query_handler.get_user(&user1_id).await {
            println!("  用户 {}: {} ({})", user.id, user.username, user.email);
        }

        let all_users = self.query_handler.get_all_users().await;
        println!("  总用户数: {}", all_users.len());

        let active_users = self.query_handler.get_users_by_status("active").await;
        println!("  活跃用户数: {}", active_users.len());

        let suspended_users = self.query_handler.get_users_by_status("suspended").await;
        println!("  暂停用户数: {}", suspended_users.len());

        // 6. 显示事件历史
        println!("\n📜 事件历史...");
        let events = self.event_store.get_all_events().await;
        for event in events {
            println!(
                "  {}: {} -> {} (v{})",
                event.timestamp, event.event_type, event.aggregate_id, event.version
            );
        }

        println!("\n{}", "=".repeat(50));
        println!("🎯 事件溯源示例完成");
        Ok(())
    }
}

#[tokio::main]
async fn main() -> Result<()> {
    let system = EventSourcingSystem::new();
    system.run_example().await
}
