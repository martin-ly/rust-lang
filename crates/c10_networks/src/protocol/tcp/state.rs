//! TCP 状态机实现

use crate::error::NetworkError;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// TCP 连接状态
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum TcpState {
    Closed,
    Listen,
    SynSent,
    SynReceived,
    Established,
    FinWait1,
    FinWait2,
    CloseWait,
    Closing,
    LastAck,
    TimeWait,
}

impl TcpState {
    /// 检查状态是否允许发送数据
    pub fn can_send_data(&self) -> bool {
        matches!(self, TcpState::Established)
    }

    /// 检查状态是否允许接收数据
    pub fn can_receive_data(&self) -> bool {
        matches!(self, TcpState::Established | TcpState::CloseWait)
    }

    /// 检查连接是否已建立
    pub fn is_established(&self) -> bool {
        matches!(self, TcpState::Established)
    }

    /// 检查连接是否已关闭
    pub fn is_closed(&self) -> bool {
        matches!(self, TcpState::Closed)
    }
}

/// TCP 事件
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TcpEvent {
    Open,
    Send,
    Receive,
    Close,
    Timeout,
    Reset,
}

/// TCP 状态机
#[derive(Debug)]
pub struct TcpStateMachine {
    current_state: TcpState,
    transition_table: HashMap<(TcpState, TcpEvent), TcpState>,
}

impl TcpStateMachine {
    /// 创建新的状态机
    pub fn new() -> Self {
        let mut table = HashMap::new();
        
        // 定义状态转换规则
        table.insert((TcpState::Closed, TcpEvent::Open), TcpState::Listen);
        table.insert((TcpState::Listen, TcpEvent::Receive), TcpState::SynReceived);
        table.insert((TcpState::SynReceived, TcpEvent::Send), TcpState::Established);
        table.insert((TcpState::Established, TcpEvent::Close), TcpState::FinWait1);
        table.insert((TcpState::FinWait1, TcpEvent::Receive), TcpState::FinWait2);
        table.insert((TcpState::FinWait2, TcpEvent::Receive), TcpState::TimeWait);
        table.insert((TcpState::TimeWait, TcpEvent::Timeout), TcpState::Closed);
        
        Self {
            current_state: TcpState::Closed,
            transition_table: table,
        }
    }
    
    /// 执行状态转换
    pub fn transition(&mut self, event: TcpEvent) -> Result<(), NetworkError> {
        if let Some(new_state) = self.transition_table.get(&(self.current_state.clone(), event.clone())) {
            self.current_state = new_state.clone();
            Ok(())
        } else {
            Err(NetworkError::Protocol(format!(
                "Invalid transition from {:?} on event {:?}",
                self.current_state, event
            )))
        }
    }
    
    /// 获取当前状态
    pub fn current_state(&self) -> &TcpState {
        &self.current_state
    }
    
    /// 检查是否可以执行事件
    pub fn can_execute(&self, event: &TcpEvent) -> bool {
        self.transition_table.contains_key(&(self.current_state.clone(), event.clone()))
    }
}

impl Default for TcpStateMachine {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tcp_state_properties() {
        assert!(!TcpState::Closed.can_send_data());
        assert!(!TcpState::Closed.can_receive_data());
        assert!(TcpState::Closed.is_closed());
        assert!(!TcpState::Closed.is_established());
        
        assert!(TcpState::Established.can_send_data());
        assert!(TcpState::Established.can_receive_data());
        assert!(!TcpState::Established.is_closed());
        assert!(TcpState::Established.is_established());
    }

    #[test]
    fn test_tcp_state_machine() {
        let mut state_machine = TcpStateMachine::new();
        
        assert_eq!(*state_machine.current_state(), TcpState::Closed);
        
        // 测试有效转换
        assert!(state_machine.transition(TcpEvent::Open).is_ok());
        assert_eq!(*state_machine.current_state(), TcpState::Listen);
        
        // 测试无效转换
        assert!(state_machine.transition(TcpEvent::Close).is_err());
        assert_eq!(*state_machine.current_state(), TcpState::Listen);
    }

    #[test]
    fn test_tcp_state_machine_can_execute() {
        let state_machine = TcpStateMachine::new();
        
        assert!(state_machine.can_execute(&TcpEvent::Open));
        assert!(!state_machine.can_execute(&TcpEvent::Close));
    }
}
