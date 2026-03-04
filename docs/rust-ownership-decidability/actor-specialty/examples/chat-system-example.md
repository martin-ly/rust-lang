# 实战示例：分布式聊天系统

> **基于Actor模型的完整聊天系统实现**

---

## 1. 系统架构

```text
分布式聊天系统架构:

┌─────────────────────────────────────────────────────────────────┐
│                        客户端层                                  │
│  ┌─────────┐  ┌─────────┐  ┌─────────┐                          │
│  │ Client 1│  │ Client 2│  │ Client N│                          │
│  │ (Web)   │  │ (Mobile)│  │ (Desktop)│                         │
│  └────┬────┘  └────┬────┘  └────┬────┘                          │
└───────┼────────────┼────────────┼────────────────────────────────┘
        │            │            │
        └────────────┼────────────┘
                     │ WebSocket
                     ▼
┌─────────────────────────────────────────────────────────────────┐
│                      网关层 (Gateway)                            │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │  Gateway Actor                                          │   │
│  │  - 管理WebSocket连接                                    │   │
│  │  - 用户认证                                             │   │
│  │  - 消息路由                                             │   │
│  └─────────────────────────────────────────────────────────┘   │
└─────────────────────────────────────────────────────────────────┘
                     │
                     ▼
┌─────────────────────────────────────────────────────────────────┐
│                     业务逻辑层                                   │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐             │
│  │ User Actor  │  │ Room Actor  │  │ Msg Actor   │             │
│  │ - 用户状态  │  │ - 房间管理  │  │ - 消息存储  │             │
│  │ - 好友列表  │  │ - 成员列表  │  │ - 历史记录  │             │
│  └─────────────┘  └─────────────┘  └─────────────┘             │
└─────────────────────────────────────────────────────────────────┘
                     │
                     ▼
┌─────────────────────────────────────────────────────────────────┐
│                      数据层                                      │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐             │
│  │  PostgreSQL │  │   Redis     │  │ Elasticsearch│             │
│  │  (用户数据) │  │  (在线状态) │  │  (消息搜索) │             │
│  └─────────────┘  └─────────────┘  └─────────────┘             │
└─────────────────────────────────────────────────────────────────┘
```

---

## 2. 核心Actor实现

### 2.1 用户Actor

```rust
use actix::prelude::*;
use std::collections::HashSet;

// 消息定义
#[derive(Message)]
#[rtype(result = "Result<UserProfile>")]
struct GetProfile;

#[derive(Message)]
#[rtype(result = "Result<()>")]
struct AddFriend { user_id: UserId };

#[derive(Message)]
#[rtype(result = "()")]
struct UpdateStatus { status: UserStatus };

// 用户Actor
pub struct UserActor {
    user_id: UserId,
    profile: UserProfile,
    friends: HashSet<UserId>,
    status: UserStatus,
    sessions: Vec<Addr<SessionActor>>,  // 多端登录
}

impl Actor for UserActor {
    type Context = Context<Self>;

    fn started(&mut self, ctx: &mut Self::Context) {
        println!("UserActor started for user: {}", self.user_id);
    }
}

impl Handler<GetProfile> for UserActor {
    type Result = Result<UserProfile>;

    fn handle(&mut self, _: GetProfile, _: &mut Context<Self>) -> Self::Result {
        Ok(self.profile.clone())
    }
}

impl Handler<UpdateStatus> for UserActor {
    type Result = ();

    fn handle(&mut self, msg: UpdateStatus, _: &mut Context<Self>) {
        self.status = msg.status;

        // 通知所有好友状态变更
        for friend_id in &self.friends {
            if let Some(addr) = get_user_actor(friend_id) {
                addr.do_send(FriendStatusChanged {
                    user_id: self.user_id.clone(),
                    status: msg.status.clone(),
                });
            }
        }
    }
}

impl Handler<SendMessage> for UserActor {
    type Result = ResponseFuture<Result<MessageId>>;

    fn handle(&mut self, msg: SendMessage, ctx: &mut Context<Self>) -> Self::Result {
        let user_id = self.user_id.clone();
        let db_pool = self.db_pool.clone();

        Box::pin(async move {
            // 保存消息
            let msg_id = save_message(&db_pool, &user_id, &msg).await?;

            // 如果是私信，通知接收者
            if let Some(to_user) = msg.to_user {
                if let Some(addr) = get_user_actor(&to_user) {
                    addr.do_send(NewMessage {
                        from: user_id,
                        message: msg,
                    });
                }
            }

            Ok(msg_id)
        })
    }
}
```

### 2.2 房间Actor (群聊)

```rust
pub struct RoomActor {
    room_id: RoomId,
    name: String,
    members: HashMap<UserId, MemberInfo>,
    message_history: Vec<ChatMessage>,
    max_history: usize,
}

impl Actor for RoomActor {
    type Context = Context<Self>;
}

impl Handler<JoinRoom> for RoomActor {
    type Result = Result<()>;

    fn handle(&mut self, msg: JoinRoom, ctx: &mut Context<Self>) -> Self::Result {
        // 检查是否已在房间
        if self.members.contains_key(&msg.user_id) {
            return Err(Error::AlreadyMember);
        }

        // 添加成员
        self.members.insert(msg.user_id.clone(), MemberInfo {
            joined_at: Instant::now(),
            session: msg.session_addr,
        });

        // 广播加入消息
        self.broadcast(SystemMessage {
            room_id: self.room_id.clone(),
            content: format!("{} joined the room", msg.username),
        });

        // 发送最近历史
        let history = self.message_history.clone();
        msg.session_addr.do_send(HistoryMessages { messages: history });

        Ok(())
    }
}

impl Handler<BroadcastMessage> for RoomActor {
    type Result = ();

    fn handle(&mut self, msg: BroadcastMessage, ctx: &mut Context<Self>) {
        let chat_msg = ChatMessage {
            id: generate_id(),
            room_id: self.room_id.clone(),
            from: msg.from,
            content: msg.content,
            timestamp: Instant::now(),
        };

        // 保存到历史
        self.message_history.push(chat_msg.clone());
        if self.message_history.len() > self.max_history {
            self.message_history.remove(0);
        }

        // 广播给所有成员
        for (user_id, member) in &self.members {
            member.session.do_send(chat_msg.clone());
        }

        // 异步持久化
        ctx.spawn(
            async move {
                persist_message(&chat_msg).await;
            }
            .into_actor(self),
        );
    }
}
```

### 2.3 会话Actor (WebSocket连接)

```rust
pub struct SessionActor {
    session_id: SessionId,
    user_id: Option<UserId>,
    ws: actix_web_actors::ws::WebsocketContext<Self>,
    heartbeat: Instant,
}

impl Actor for SessionActor {
    type Context = ws::WebsocketContext<Self>;

    fn started(&mut self, ctx: &mut Self::Context) {
        // 启动心跳检测
        self.heartbeat(ctx);
    }
}

impl StreamHandler<Result<ws::Message, ws::ProtocolError>> for SessionActor {
    fn handle(&mut self, msg: Result<ws::Message, ws::ProtocolError>, ctx: &mut Self::Context) {
        match msg {
            Ok(ws::Message::Ping(msg)) => {
                self.heartbeat = Instant::now();
                ctx.pong(&msg);
            }
            Ok(ws::Message::Pong(_)) => {
                self.heartbeat = Instant::now();
            }
            Ok(ws::Message::Text(text)) => {
                self.handle_client_message(text, ctx);
            }
            Ok(ws::Message::Close(reason)) => {
                ctx.close(reason);
                ctx.stop();
            }
            _ => {}
        }
    }
}

impl SessionActor {
    fn handle_client_message(&mut self, text: String, ctx: &mut ws::WebsocketContext<Self>) {
        let msg: ClientMessage = match serde_json::from_str(&text) {
            Ok(m) => m,
            Err(e) => {
                ctx.text(json!({"error": "Invalid message format"}).to_string());
                return;
            }
        };

        match msg {
            ClientMessage::Authenticate { token } => {
                // 验证token
                match verify_token(&token) {
                    Ok(user_id) => {
                        self.user_id = Some(user_id.clone());
                        // 关联到UserActor
                        if let Some(user_actor) = get_user_actor(&user_id) {
                            user_actor.do_send(AddSession {
                                session: ctx.address(),
                            });
                        }
                        ctx.text(json!({"type": "authenticated"}).to_string());
                    }
                    Err(_) => {
                        ctx.text(json!({"error": "Invalid token"}).to_string());
                    }
                }
            }
            ClientMessage::JoinRoom { room_id } => {
                if let Some(user_id) = &self.user_id {
                    if let Some(room) = get_room_actor(&room_id) {
                        room.do_send(JoinRoom {
                            user_id: user_id.clone(),
                            session_addr: ctx.address(),
                        });
                    }
                }
            }
            ClientMessage::Chat { room_id, content } => {
                if let Some(user_id) = &self.user_id {
                    if let Some(room) = get_room_actor(&room_id) {
                        room.do_send(BroadcastMessage {
                            from: user_id.clone(),
                            content,
                        });
                    }
                }
            }
            _ => {}
        }
    }

    fn heartbeat(&self, ctx: &mut ws::WebsocketContext<Self>) {
        ctx.run_interval(Duration::from_secs(5), |act, ctx| {
            if Instant::now().duration_since(act.heartbeat) > Duration::from_secs(10) {
                // 心跳超时，关闭连接
                ctx.stop();
                return;
            }
            ctx.ping(b"");
        });
    }
}

// 接收服务器消息并发送给客户端
impl Handler<ChatMessage> for SessionActor {
    type Result = ();

    fn handle(&mut self, msg: ChatMessage, ctx: &mut Self::Context) {
        let json = serde_json::to_string(&ServerMessage::NewMessage(msg)).unwrap();
        ctx.text(json);
    }
}
```

---

## 3. 系统集成

### 3.1 Actor系统启动

```rust
use actix::prelude::*;

pub struct ChatSystem {
    user_actors: HashMap<UserId, Addr<UserActor>>,
    room_actors: HashMap<RoomId, Addr<RoomActor>>,
    db_pool: DbPool,
}

impl ChatSystem {
    pub async fn new(db_pool: DbPool) -> Self {
        Self {
            user_actors: HashMap::new(),
            room_actors: HashMap::new(),
            db_pool,
        }
    }

    pub fn get_or_create_user(&mut self, user_id: UserId) -> Addr<UserActor> {
        self.user_actors.entry(user_id.clone())
            .or_insert_with(|| {
                UserActor {
                    user_id: user_id.clone(),
                    profile: load_profile(&user_id),
                    friends: load_friends(&user_id),
                    status: UserStatus::Offline,
                    sessions: Vec::new(),
                }.start()
            })
            .clone()
    }

    pub fn get_or_create_room(&mut self, room_id: RoomId) -> Addr<RoomActor> {
        self.room_actors.entry(room_id.clone())
            .or_insert_with(|| {
                RoomActor {
                    room_id: room_id.clone(),
                    name: format!("Room {}", room_id),
                    members: HashMap::new(),
                    message_history: Vec::new(),
                    max_history: 100,
                }.start()
            })
            .clone()
    }
}

// WebSocket路由
async fn ws_route(
    req: HttpRequest,
    stream: web::Payload,
    srv: web::Data<Addr<ChatSystem>>,
) -> Result<HttpResponse, Error> {
    ws::start(
        SessionActor {
            session_id: generate_session_id(),
            user_id: None,
            heartbeat: Instant::now(),
        },
        &req,
        stream,
    )
}
```

### 3.2 消息格式

```rust
// 客户端消息
#[derive(Deserialize)]
#[serde(tag = "type")]
enum ClientMessage {
    #[serde(rename = "auth")]
    Authenticate { token: String },

    #[serde(rename = "join")]
    JoinRoom { room_id: RoomId },

    #[serde(rename = "leave")]
    LeaveRoom { room_id: RoomId },

    #[serde(rename = "chat")]
    Chat { room_id: RoomId, content: String },

    #[serde(rename = "direct")]
    DirectMessage { to_user: UserId, content: String },

    #[serde(rename = "typing")]
    Typing { room_id: RoomId },
}

// 服务器消息
#[derive(Serialize)]
#[serde(tag = "type")]
enum ServerMessage {
    #[serde(rename = "authenticated")]
    Authenticated { user_id: UserId },

    #[serde(rename = "message")]
    NewMessage(ChatMessage),

    #[serde(rename = "user_joined")]
    UserJoined { room_id: RoomId, user: UserInfo },

    #[serde(rename = "user_left")]
    UserLeft { room_id: RoomId, user_id: UserId },

    #[serde(rename = "status")]
    StatusChanged { user_id: UserId, status: UserStatus },

    #[serde(rename = "typing")]
    UserTyping { room_id: RoomId, user_id: UserId },

    #[serde(rename = "history")]
    HistoryMessages { messages: Vec<ChatMessage> },

    #[serde(rename = "error")]
    Error { code: String, message: String },
}
```

---

## 4. 扩展功能

### 4.1 消息持久化

```rust
pub struct MessagePersistenceActor {
    db_pool: DbPool,
    buffer: Vec<ChatMessage>,
    flush_interval: Duration,
}

impl Actor for MessagePersistenceActor {
    type Context = Context<Self>;

    fn started(&mut self, ctx: &mut Self::Context) {
        // 定期刷新
        ctx.run_interval(self.flush_interval, |act, _| {
            act.flush_buffer();
        });
    }
}

impl MessagePersistenceActor {
    fn flush_buffer(&mut self) {
        if self.buffer.is_empty() {
            return;
        }

        let messages = std::mem::take(&mut self.buffer);
        let pool = self.db_pool.clone();

        actix::spawn(async move {
            if let Err(e) = batch_insert_messages(&pool, &messages).await {
                eprintln!("Failed to persist messages: {}", e);
            }
        });
    }
}
```

### 4.2 消息推送

```rust
pub struct PushNotificationActor {
    fcm_client: FcmClient,
    apns_client: ApnsClient,
}

impl Handler<NewMessage> for PushNotificationActor {
    type Result = ResponseFuture<()>;

    fn handle(&mut self, msg: NewMessage, _: &mut Context<Self>) -> Self::Result {
        let fcm = self.fcm_client.clone();
        let apns = self.apns_client.clone();

        Box::pin(async move {
            // 获取用户设备令牌
            let devices = get_user_devices(&msg.to_user).await;

            for device in devices {
                match device.platform {
                    Platform::Android => {
                        fcm.send(FcmMessage {
                            token: device.token,
                            title: format!("New message from {}", msg.from_username),
                            body: truncate(&msg.content, 100),
                        }).await.ok();
                    }
                    Platform::iOS => {
                        apns.send(ApnsMessage {
                            token: device.token,
                            alert: Alert {
                                title: Some(format!("New message from {}", msg.from_username)),
                                body: Some(truncate(&msg.content, 100)),
                            },
                            badge: Some(1),
                        }).await.ok();
                    }
                }
            }
        })
    }
}
```

---

## 5. 性能优化

### 5.1 水平扩展

```rust
// 使用一致性哈希分片
struct ShardedChatSystem {
    shards: HashMap<u64, Addr<ChatSystem>>,
}

impl ShardedChatSystem {
    fn route_to_shard(&self, user_id: &UserId) -> &Addr<ChatSystem> {
        let hash = hash_user_id(user_id);
        let shard_id = hash % self.shards.len() as u64;
        &self.shards[&shard_id]
    }
}
```

### 5.2 连接优化

```rust
// 使用连接池
impl ChatSystem {
    fn distribute_load(&self) {
        // 当单个Actor连接过多时，创建新的实例
        for (user_id, actor) in &self.user_actors {
            let connection_count = actor.send(GetConnectionCount).await.unwrap();
            if connection_count > 1000 {
                // 创建新的Actor实例
                self.spawn_new_instance(user_id);
            }
        }
    }
}
```

---

**维护者**: Rust Actor Examples Team
**更新日期**: 2026-03-05
