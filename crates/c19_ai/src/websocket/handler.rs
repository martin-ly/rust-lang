//! WebSocket处理器模块
//! 
//! 提供WebSocket消息处理逻辑

use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;
// use uuid::Uuid;
// use chrono::{DateTime, Utc};

use super::message::{WebSocketMessage, WebSocketMessageType, ConnectionInfo};
use super::client::WebSocketClient;
use super::room::Room;

/// WebSocket事件类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum WebSocketEvent {
    /// 客户端连接
    ClientConnected(ConnectionInfo),
    /// 客户端断开连接
    ClientDisconnected(String),
    /// 收到消息
    MessageReceived(WebSocketMessage),
    /// 房间加入
    RoomJoined(String, String), // room_id, client_id
    /// 房间离开
    RoomLeft(String, String), // room_id, client_id
    /// 错误事件
    Error(String),
}

/// WebSocket事件处理器
pub type EventHandler = Box<dyn Fn(WebSocketEvent) -> Result<()> + Send + Sync>;

/// WebSocket消息处理器
pub type MessageHandler = Box<dyn Fn(WebSocketMessage) -> Result<Option<WebSocketMessage>> + Send + Sync>;

/// WebSocket处理器管理器
pub struct WebSocketHandler {
    event_handlers: Arc<RwLock<HashMap<String, EventHandler>>>,
    message_handlers: Arc<RwLock<HashMap<WebSocketMessageType, MessageHandler>>>,
    clients: Arc<RwLock<HashMap<String, Arc<WebSocketClient>>>>,
    rooms: Arc<RwLock<HashMap<String, Arc<Room>>>>,
}

impl WebSocketHandler {
    /// 创建新的WebSocket处理器
    pub fn new() -> Self {
        Self {
            event_handlers: Arc::new(RwLock::new(HashMap::new())),
            message_handlers: Arc::new(RwLock::new(HashMap::new())),
            clients: Arc::new(RwLock::new(HashMap::new())),
            rooms: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// 注册事件处理器
    pub async fn register_event_handler(&self, event_type: String, handler: EventHandler) {
        let mut handlers = self.event_handlers.write().await;
        handlers.insert(event_type, handler);
    }

    /// 注册消息处理器
    pub async fn register_message_handler(&self, message_type: WebSocketMessageType, handler: MessageHandler) {
        let mut handlers = self.message_handlers.write().await;
        handlers.insert(message_type, handler);
    }

    /// 处理WebSocket事件
    pub async fn handle_event(&self, event: WebSocketEvent) -> Result<()> {
        match &event {
            WebSocketEvent::ClientConnected(conn_info) => {
                tracing::info!("Client connected: {}", conn_info.client_id);
                self.handle_client_connected(conn_info.clone()).await?;
            }
            WebSocketEvent::ClientDisconnected(client_id) => {
                tracing::info!("Client disconnected: {}", client_id);
                self.handle_client_disconnected(client_id.clone()).await?;
            }
            WebSocketEvent::MessageReceived(message) => {
                self.handle_message_received(message.clone()).await?;
            }
            WebSocketEvent::RoomJoined(room_id, client_id) => {
                tracing::info!("Client {} joined room {}", client_id, room_id);
                self.handle_room_joined(room_id.clone(), client_id.clone()).await?;
            }
            WebSocketEvent::RoomLeft(room_id, client_id) => {
                tracing::info!("Client {} left room {}", client_id, room_id);
                self.handle_room_left(room_id.clone(), client_id.clone()).await?;
            }
            WebSocketEvent::Error(error) => {
                tracing::error!("WebSocket error: {}", error);
            }
        }

        // 调用注册的事件处理器
        let handlers = self.event_handlers.read().await;
        for handler in handlers.values() {
            if let Err(e) = handler(event.clone()) {
                tracing::error!("Error in event handler: {}", e);
            }
        }

        Ok(())
    }

    /// 处理客户端连接
    async fn handle_client_connected(&self, conn_info: ConnectionInfo) -> Result<()> {
        let client = WebSocketClient::new(conn_info.client_id.clone());
        let client_arc = Arc::new(client);
        
        let mut clients = self.clients.write().await;
        clients.insert(conn_info.client_id, client_arc);
        
        Ok(())
    }

    /// 处理客户端断开连接
    async fn handle_client_disconnected(&self, client_id: String) -> Result<()> {
        let mut clients = self.clients.write().await;
        clients.remove(&client_id);
        
        // 从所有房间中移除客户端
        let rooms = self.rooms.write().await;
        for _room in rooms.values() {
            // TODO: 实现从房间移除客户端的逻辑
        }
        
        Ok(())
    }

    /// 处理收到的消息
    async fn handle_message_received(&self, message: WebSocketMessage) -> Result<()> {
        // 检查消息是否过期
        if message.is_expired() {
            tracing::warn!("Received expired message: {}", message.id);
            return Ok(());
        }

        // 调用注册的消息处理器
        let handlers = self.message_handlers.read().await;
        if let Some(handler) = handlers.get(&message.message_type) {
            if let Some(response) = handler(message.clone())? {
                // 发送响应消息
                self.send_message(response).await?;
            }
        }

        // 根据消息类型进行特殊处理
        match message.message_type {
            WebSocketMessageType::Ping => {
                let pong = WebSocketMessage::pong()
                    .with_sender(message.recipient_id.unwrap_or_default())
                    .with_recipient(message.sender_id.unwrap_or_default());
                self.send_message(pong).await?;
            }
            WebSocketMessageType::Broadcast => {
                if let Some(room_id) = &message.room_id {
                    self.broadcast_to_room(room_id.clone(), message).await?;
                }
            }
            _ => {
                // 其他消息类型的处理
            }
        }

        Ok(())
    }

    /// 处理房间加入
    async fn handle_room_joined(&self, room_id: String, client_id: String) -> Result<()> {
        let rooms = self.rooms.read().await;
        if let Some(_room) = rooms.get(&room_id) {
            let clients = self.clients.read().await;
            if let Some(_client) = clients.get(&client_id) {
                // TODO: 实现加入房间的逻辑
                tracing::info!("Client {} joined room {}", client_id, room_id);
            }
        }
        Ok(())
    }

    /// 处理房间离开
    async fn handle_room_left(&self, room_id: String, client_id: String) -> Result<()> {
        let rooms = self.rooms.read().await;
        if let Some(_room) = rooms.get(&room_id) {
            // TODO: 实现离开房间的逻辑
            tracing::info!("Client {} left room {}", client_id, room_id);
        }
        Ok(())
    }

    /// 发送消息
    async fn send_message(&self, message: WebSocketMessage) -> Result<()> {
        if let Some(recipient_id) = &message.recipient_id {
            let clients = self.clients.read().await;
            if let Some(client) = clients.get(recipient_id) {
                client.send(message).await?;
            }
        }
        Ok(())
    }

    /// 向房间广播消息
    async fn broadcast_to_room(&self, room_id: String, message: WebSocketMessage) -> Result<()> {
        let rooms = self.rooms.read().await;
        if let Some(_room) = rooms.get(&room_id) {
            // TODO: 实现房间广播逻辑
            tracing::info!("Broadcasting message to room {}", room_id);
        }
        Ok(())
    }

    /// 获取客户端数量
    pub async fn get_client_count(&self) -> usize {
        let clients = self.clients.read().await;
        clients.len()
    }

    /// 获取房间数量
    pub async fn get_room_count(&self) -> usize {
        let rooms = self.rooms.read().await;
        rooms.len()
    }

    /// 创建房间
    pub async fn create_room(&self, name: String) -> Result<String> {
        let room = Room::new(name);
        let room_id = room.id.to_string();
        let room_arc = Arc::new(room);
        
        let mut rooms = self.rooms.write().await;
        rooms.insert(room_id.clone(), room_arc);
        
        Ok(room_id)
    }

    /// 删除房间
    pub async fn delete_room(&self, room_id: String) -> Result<()> {
        let mut rooms = self.rooms.write().await;
        rooms.remove(&room_id);
        Ok(())
    }

    /// 获取所有房间
    pub async fn get_rooms(&self) -> Vec<String> {
        let rooms = self.rooms.read().await;
        rooms.keys().cloned().collect()
    }

    /// 获取所有客户端
    pub async fn get_clients(&self) -> Vec<String> {
        let clients = self.clients.read().await;
        clients.keys().cloned().collect()
    }
}

impl Default for WebSocketHandler {
    fn default() -> Self {
        Self::new()
    }
}