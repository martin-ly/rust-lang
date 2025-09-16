//! # 区块链网络模块 / Blockchain Network Module
//!
//! 本模块实现了区块链网络通信功能。
//! This module implements blockchain network communication functionality.
#![allow(dead_code)]

// use crate::types::*;
// use std::collections::HashMap;

/// 网络节点类型 / Network Node Type
#[derive(Debug, Clone)]
pub enum NodeType {
    Full,
    Light,
    Validator,
}

/// 网络节点 / Network Node
#[derive(Debug, Clone)]
pub struct NetworkNode {
    pub id: String,
    pub address: String,
    pub node_type: NodeType,
    pub is_connected: bool,
    pub peers: Vec<String>,
}

impl NetworkNode {
    pub fn new(id: String, address: String, node_type: NodeType) -> Self {
        Self {
            id,
            address,
            node_type,
            is_connected: false,
            peers: Vec::new(),
        }
    }

    pub fn connect(&mut self) {
        self.is_connected = true;
    }

    pub fn disconnect(&mut self) {
        self.is_connected = false;
    }

    pub fn add_peer(&mut self, peer_id: String) {
        if !self.peers.contains(&peer_id) {
            self.peers.push(peer_id);
        }
    }
}
