//! WebSocket管理器模块
//! 
//! 提供WebSocket连接和房间管理

use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;
use uuid::Uuid;
use chrono::{DateTime, Utc};

use super::message::{WebSocketMessage, ConnectionInfo, ConnectionStatus};
// use super::client::WebSocketClient;
use super::room::Room;
use super::handler::WebSocketHandler;
use super::server::WebSocketServer;

/// WebSocket管理器状态
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ManagerStatus {
    pub total_connections: usize,
    pub active_connections: usize,
    pub total_rooms: usize,
    pub total_messages: u64,
    pub uptime_seconds: u64,
    pub started_at: DateTime<Utc>,
}

/// WebSocket管理器
pub struct WebSocketManager {
    pub id: Uuid,
    pub name: String,
    pub created_at: DateTime<Utc>,
    server: Arc<WebSocketServer>,
    handler: Arc<WebSocketHandler>,
    connections: Arc<RwLock<HashMap<String, ConnectionInfo>>>,
    rooms: Arc<RwLock<HashMap<String, Arc<Room>>>>,
    message_count: Arc<RwLock<u64>>,
    started_at: Arc<RwLock<Option<DateTime<Utc>>>>,
}

impl WebSocketManager {
    /// 创建新的WebSocket管理器
    pub fn new(name: String) -> Self {
        Self {
            id: Uuid::new_v4(),
            name,
            created_at: Utc::now(),
            server: Arc::new(WebSocketServer::new("websocket_server".to_string())),
            handler: Arc::new(WebSocketHandler::new()),
            connections: Arc::new(RwLock::new(HashMap::new())),
            rooms: Arc::new(RwLock::new(HashMap::new())),
            message_count: Arc::new(RwLock::new(0)),
            started_at: Arc::new(RwLock::new(None)),
        }
    }

    /// 启动WebSocket管理器
    pub async fn start(&self) -> Result<()> {
        tracing::info!("Starting WebSocket manager: {}", self.name);
        
        // 记录启动时间
        {
            let mut started_at = self.started_at.write().await;
            *started_at = Some(Utc::now());
        }

        // 启动WebSocket服务器
        self.server.start().await?;

        // 注册默认消息处理器
        self.register_default_handlers().await;

        tracing::info!("WebSocket manager started successfully");
        Ok(())
    }

    /// 停止WebSocket管理器
    pub async fn stop(&self) -> Result<()> {
        tracing::info!("Stopping WebSocket manager: {}", self.name);
        
        // 停止WebSocket服务器
        self.server.stop().await?;

        // 清理所有连接
        {
            let mut connections = self.connections.write().await;
            connections.clear();
        }

        // 清理所有房间
        {
            let mut rooms = self.rooms.write().await;
            rooms.clear();
        }

        tracing::info!("WebSocket manager stopped successfully");
        Ok(())
    }

    /// 注册默认消息处理器
    async fn register_default_handlers(&self) {
        // 注册心跳处理器
        let _handler = self.handler.clone();
        self.handler.register_message_handler(
            super::message::WebSocketMessageType::Ping,
            Box::new(move |message| {
                tracing::debug!("Received ping from client: {:?}", message.sender_id);
                Ok(Some(WebSocketMessage::pong().with_recipient(
                    message.sender_id.unwrap_or_default()
                )))
            })
        ).await;

        // 注册系统消息处理器
        let _handler = self.handler.clone();
        self.handler.register_message_handler(
            super::message::WebSocketMessageType::System,
            Box::new(move |message| {
                tracing::info!("Received system message: {}", message.content);
                Ok(None)
            })
        ).await;
    }

    /// 处理新连接
    pub async fn handle_connection(&self, client_id: String, remote_addr: Option<String>, user_agent: Option<String>) -> Result<()> {
        let conn_info = ConnectionInfo {
            client_id: client_id.clone(),
            status: ConnectionStatus::Connected,
            connected_at: Utc::now(),
            last_ping: None,
            user_agent,
            remote_addr,
            metadata: None,
        };

        // 保存连接信息
        {
            let mut connections = self.connections.write().await;
            connections.insert(client_id.clone(), conn_info.clone());
        }

        // 发送连接事件
        self.handler.handle_event(
            super::handler::WebSocketEvent::ClientConnected(conn_info)
        ).await?;

        Ok(())
    }

    /// 处理连接断开
    pub async fn handle_disconnection(&self, client_id: String) -> Result<()> {
        // 移除连接信息
        {
            let mut connections = self.connections.write().await;
            connections.remove(&client_id);
        }

        // 发送断开连接事件
        self.handler.handle_event(
            super::handler::WebSocketEvent::ClientDisconnected(client_id)
        ).await?;

        Ok(())
    }

    /// 处理收到的消息
    pub async fn handle_message(&self, message: WebSocketMessage) -> Result<()> {
        // 更新消息计数
        {
            let mut count = self.message_count.write().await;
            *count += 1;
        }

        // 更新最后ping时间
        if matches!(message.message_type, super::message::WebSocketMessageType::Ping) {
            if let Some(sender_id) = &message.sender_id {
                let mut connections = self.connections.write().await;
                if let Some(conn_info) = connections.get_mut(sender_id) {
                    conn_info.update_ping();
                }
            }
        }

        // 处理消息
        self.handler.handle_event(
            super::handler::WebSocketEvent::MessageReceived(message)
        ).await?;

        Ok(())
    }

    /// 创建房间
    pub async fn create_room(&self, name: String) -> Result<String> {
        let room_id = self.handler.create_room(name).await?;
        
        let room = Room::new(room_id.clone());
        let room_arc = Arc::new(room);
        
        let mut rooms = self.rooms.write().await;
        rooms.insert(room_id.clone(), room_arc);
        
        tracing::info!("Created room: {}", room_id);
        Ok(room_id)
    }

    /// 删除房间
    pub async fn delete_room(&self, room_id: String) -> Result<()> {
        self.handler.delete_room(room_id.clone()).await?;
        
        let mut rooms = self.rooms.write().await;
        rooms.remove(&room_id);
        
        tracing::info!("Deleted room: {}", room_id);
        Ok(())
    }

    /// 加入房间
    pub async fn join_room(&self, room_id: String, client_id: String) -> Result<()> {
        let rooms = self.rooms.read().await;
        if let Some(_room) = rooms.get(&room_id) {
            // TODO: 实现加入房间的逻辑
            tracing::info!("Client {} joined room {}", client_id, room_id);
            
            // 发送房间加入事件
            self.handler.handle_event(
                super::handler::WebSocketEvent::RoomJoined(room_id, client_id)
            ).await?;
        } else {
            return Err(anyhow::anyhow!("Room not found: {}", room_id));
        }
        Ok(())
    }

    /// 离开房间
    pub async fn leave_room(&self, room_id: String, client_id: String) -> Result<()> {
        let rooms = self.rooms.read().await;
        if let Some(_room) = rooms.get(&room_id) {
            // TODO: 实现离开房间的逻辑
            tracing::info!("Client {} left room {}", client_id, room_id);
            
            // 发送房间离开事件
            self.handler.handle_event(
                super::handler::WebSocketEvent::RoomLeft(room_id, client_id)
            ).await?;
        } else {
            return Err(anyhow::anyhow!("Room not found: {}", room_id));
        }
        Ok(())
    }

    /// 向房间广播消息
    pub async fn broadcast_to_room(&self, room_id: String, _message: WebSocketMessage) -> Result<()> {
        let rooms = self.rooms.read().await;
        if let Some(_room) = rooms.get(&room_id) {
            // TODO: 实现房间广播逻辑
            tracing::info!("Broadcasting message to room {}", room_id);
        } else {
            return Err(anyhow::anyhow!("Room not found: {}", room_id));
        }
        Ok(())
    }

    /// 获取管理器状态
    pub async fn get_status(&self) -> ManagerStatus {
        let connections = self.connections.read().await;
        let rooms = self.rooms.read().await;
        let message_count = self.message_count.read().await;
        let started_at = self.started_at.read().await;

        let active_connections = connections.values()
            .filter(|conn| matches!(conn.status, ConnectionStatus::Connected))
            .count();

        let uptime = if let Some(start_time) = *started_at {
            Utc::now().signed_duration_since(start_time).num_seconds() as u64
        } else {
            0
        };

        ManagerStatus {
            total_connections: connections.len(),
            active_connections,
            total_rooms: rooms.len(),
            total_messages: *message_count,
            uptime_seconds: uptime,
            started_at: started_at.unwrap_or(self.created_at),
        }
    }

    /// 获取所有连接
    pub async fn get_connections(&self) -> Vec<ConnectionInfo> {
        let connections = self.connections.read().await;
        connections.values().cloned().collect()
    }

    /// 获取所有房间
    pub async fn get_rooms(&self) -> Vec<String> {
        let rooms = self.rooms.read().await;
        rooms.keys().cloned().collect()
    }

    /// 清理非活跃连接
    pub async fn cleanup_inactive_connections(&self, timeout_seconds: u64) -> Result<usize> {
        let mut connections = self.connections.write().await;
        let inactive_clients: Vec<String> = connections
            .iter()
            .filter(|(_, conn_info)| !conn_info.is_active(timeout_seconds))
            .map(|(client_id, _)| client_id.clone())
            .collect();

        let count = inactive_clients.len();
        for client_id in inactive_clients {
            connections.remove(&client_id);
            self.handle_disconnection(client_id).await?;
        }

        Ok(count)
    }
}