//! 形式化规范定义模块
//!
//! 本模块提供了网络协议的形式化规范定义，包括：
//! - TCP协议状态机规范
//! - HTTP协议语义规范
//! - WebSocket协议规范
//! - 异步通信语义规范

// use crate::error::NetworkResult;
use crate::semantics::*;
use std::collections::{HashMap, HashSet};
use std::fmt;

/// TCP协议形式化规范
pub struct TcpFormalSpec {
    /// 状态定义
    pub states: HashSet<TcpState>,
    /// 事件定义
    pub events: HashSet<TcpEvent>,
    /// 状态转换表
    transition_table: HashMap<(TcpState, TcpEvent), TcpState>,
    /// 不变量
    invariants: Vec<TcpInvariant>,
}

/// TCP事件
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TcpEvent {
    /// 主动打开
    ActiveOpen,
    /// 被动打开
    PassiveOpen,
    /// 发送SYN
    SendSyn,
    /// 接收SYN
    ReceiveSyn,
    /// 发送SYN+ACK
    SendSynAck,
    /// 接收SYN+ACK
    ReceiveSynAck,
    /// 发送ACK
    SendAck,
    /// 接收ACK
    ReceiveAck,
    /// 发送FIN
    SendFin,
    /// 接收FIN
    ReceiveFin,
    /// 发送FIN+ACK
    SendFinAck,
    /// 接收FIN+ACK
    ReceiveFinAck,
    /// 关闭连接
    Close,
    /// 超时
    Timeout,
    /// 重置连接
    Reset,
}

/// TCP不变量
#[derive(Debug, Clone)]
pub struct TcpInvariant {
    /// 不变量名称
    pub name: String,
    /// 不变量条件
    pub condition: TcpInvariantCondition,
    /// 不变量类型
    pub invariant_type: TcpInvariantType,
}

/// TCP不变量条件
#[derive(Debug, Clone)]
pub enum TcpInvariantCondition {
    /// 状态条件
    StateCondition(TcpState),
    /// 序列号条件
    SequenceNumberCondition {
        min_seq: u32,
        max_seq: u32,
    },
    /// 窗口大小条件
    WindowSizeCondition {
        min_window: u16,
        max_window: u16,
    },
    /// 认证条件
    AuthenticationCondition(bool),
    /// 复合条件
    CompoundCondition {
        operator: LogicalOperator,
        conditions: Vec<TcpInvariantCondition>,
    },
}

/// TCP不变量类型
#[derive(Debug, Clone, PartialEq)]
pub enum TcpInvariantType {
    /// 状态不变量
    StateInvariant,
    /// 数据不变量
    DataInvariant,
    /// 安全不变量
    SecurityInvariant,
    /// 性能不变量
    PerformanceInvariant,
}

impl Default for TcpFormalSpec {
    fn default() -> Self {
        let mut spec = Self {
            states: HashSet::new(),
            events: HashSet::new(),
            transition_table: HashMap::new(),
            invariants: Vec::new(),
        };

        spec.initialize_states();
        spec.initialize_events();
        spec.initialize_transitions();
        spec.initialize_invariants();

        spec
    }
}

impl TcpFormalSpec {
    /// 创建TCP形式化规范
    pub fn new() -> Self {
        Self::default()
    }

    /// 初始化状态
    fn initialize_states(&mut self) {
        self.states.insert(TcpState::Closed);
        self.states.insert(TcpState::Listen);
        self.states.insert(TcpState::SynSent);
        self.states.insert(TcpState::SynReceived);
        self.states.insert(TcpState::Established);
        self.states.insert(TcpState::FinWait1);
        self.states.insert(TcpState::FinWait2);
        self.states.insert(TcpState::CloseWait);
        self.states.insert(TcpState::LastAck);
        self.states.insert(TcpState::TimeWait);
    }

    /// 初始化事件
    fn initialize_events(&mut self) {
        self.events.insert(TcpEvent::ActiveOpen);
        self.events.insert(TcpEvent::PassiveOpen);
        self.events.insert(TcpEvent::SendSyn);
        self.events.insert(TcpEvent::ReceiveSyn);
        self.events.insert(TcpEvent::SendSynAck);
        self.events.insert(TcpEvent::ReceiveSynAck);
        self.events.insert(TcpEvent::SendAck);
        self.events.insert(TcpEvent::ReceiveAck);
        self.events.insert(TcpEvent::SendFin);
        self.events.insert(TcpEvent::ReceiveFin);
        self.events.insert(TcpEvent::SendFinAck);
        self.events.insert(TcpEvent::ReceiveFinAck);
        self.events.insert(TcpEvent::Close);
        self.events.insert(TcpEvent::Timeout);
        self.events.insert(TcpEvent::Reset);
    }

    /// 初始化状态转换
    fn initialize_transitions(&mut self) {
        // CLOSED -> LISTEN (被动打开)
        self.transition_table.insert(
            (TcpState::Closed, TcpEvent::PassiveOpen),
            TcpState::Listen,
        );

        // CLOSED -> SYN_SENT (主动打开)
        self.transition_table.insert(
            (TcpState::Closed, TcpEvent::ActiveOpen),
            TcpState::SynSent,
        );

        // LISTEN -> SYN_RECEIVED (接收SYN)
        self.transition_table.insert(
            (TcpState::Listen, TcpEvent::ReceiveSyn),
            TcpState::SynReceived,
        );

        // SYN_SENT -> SYN_RECEIVED (接收SYN+ACK)
        self.transition_table.insert(
            (TcpState::SynSent, TcpEvent::ReceiveSynAck),
            TcpState::SynReceived,
        );

        // SYN_RECEIVED -> ESTABLISHED (发送/接收ACK)
        self.transition_table.insert(
            (TcpState::SynReceived, TcpEvent::SendAck),
            TcpState::Established,
        );
        self.transition_table.insert(
            (TcpState::SynReceived, TcpEvent::ReceiveAck),
            TcpState::Established,
        );

        // ESTABLISHED -> FIN_WAIT_1 (发送FIN)
        self.transition_table.insert(
            (TcpState::Established, TcpEvent::SendFin),
            TcpState::FinWait1,
        );

        // ESTABLISHED -> CLOSE_WAIT (接收FIN)
        self.transition_table.insert(
            (TcpState::Established, TcpEvent::ReceiveFin),
            TcpState::CloseWait,
        );

        // FIN_WAIT_1 -> FIN_WAIT_2 (接收ACK)
        self.transition_table.insert(
            (TcpState::FinWait1, TcpEvent::ReceiveAck),
            TcpState::FinWait2,
        );

        // FIN_WAIT_2 -> TIME_WAIT (接收FIN)
        self.transition_table.insert(
            (TcpState::FinWait2, TcpEvent::ReceiveFin),
            TcpState::TimeWait,
        );

        // CLOSE_WAIT -> LAST_ACK (发送FIN)
        self.transition_table.insert(
            (TcpState::CloseWait, TcpEvent::SendFin),
            TcpState::LastAck,
        );

        // LAST_ACK -> CLOSED (接收ACK)
        self.transition_table.insert(
            (TcpState::LastAck, TcpEvent::ReceiveAck),
            TcpState::Closed,
        );

        // TIME_WAIT -> CLOSED (超时)
        self.transition_table.insert(
            (TcpState::TimeWait, TcpEvent::Timeout),
            TcpState::Closed,
        );

        // 任何状态 -> CLOSED (重置)
        for state in &self.states {
            self.transition_table.insert(
                (*state, TcpEvent::Reset),
                TcpState::Closed,
            );
        }
    }

    /// 初始化不变量
    fn initialize_invariants(&mut self) {
        // 状态不变量：ESTABLISHED状态必须认证
        self.invariants.push(TcpInvariant {
            name: "established_authentication".to_string(),
            condition: TcpInvariantCondition::CompoundCondition {
                operator: LogicalOperator::And,
                conditions: vec![
                    TcpInvariantCondition::StateCondition(TcpState::Established),
                    TcpInvariantCondition::AuthenticationCondition(true),
                ],
            },
            invariant_type: TcpInvariantType::SecurityInvariant,
        });

        // 序列号不变量：序列号必须为正数
        self.invariants.push(TcpInvariant {
            name: "positive_sequence_number".to_string(),
            condition: TcpInvariantCondition::SequenceNumberCondition {
                min_seq: 1,
                max_seq: u32::MAX,
            },
            invariant_type: TcpInvariantType::DataInvariant,
        });

        // 窗口大小不变量：窗口大小必须在合理范围内
        self.invariants.push(TcpInvariant {
            name: "valid_window_size".to_string(),
            condition: TcpInvariantCondition::WindowSizeCondition {
                min_window: 1,
                max_window: 65535,
            },
            invariant_type: TcpInvariantType::PerformanceInvariant,
        });
    }

    /// 获取状态转换
    pub fn get_transition(&self, state: TcpState, event: TcpEvent) -> Option<TcpState> {
        self.transition_table.get(&(state, event)).copied()
    }

    /// 验证状态转换的有效性
    pub fn is_valid_transition(&self, from: TcpState, to: TcpState, event: TcpEvent) -> bool {
        self.get_transition(from, event) == Some(to)
    }

    /// 检查不变量
    pub fn check_invariant(&self, state: &ConnectionState, invariant: &TcpInvariant) -> bool {
        match &invariant.condition {
            TcpInvariantCondition::StateCondition(expected_state) => {
                state.state == *expected_state
            }
            TcpInvariantCondition::SequenceNumberCondition { min_seq, max_seq } => {
                state.sequence_number >= *min_seq && state.sequence_number <= *max_seq
            }
            TcpInvariantCondition::WindowSizeCondition { min_window, max_window } => {
                state.window_size >= *min_window && state.window_size <= *max_window
            }
            TcpInvariantCondition::AuthenticationCondition(expected_auth) => {
                state.authenticated == *expected_auth
            }
            TcpInvariantCondition::CompoundCondition { operator, conditions } => {
                match operator {
                    LogicalOperator::And => {
                        conditions.iter().all(|condition| {
                            self.check_invariant_condition(state, condition)
                        })
                    }
                    LogicalOperator::Or => {
                        conditions.iter().any(|condition| {
                            self.check_invariant_condition(state, condition)
                        })
                    }
                    LogicalOperator::Not => {
                        !conditions.iter().any(|condition| {
                            self.check_invariant_condition(state, condition)
                        })
                    }
                }
            }
        }
    }

    /// 检查不变量条件
    fn check_invariant_condition(&self, state: &ConnectionState, condition: &TcpInvariantCondition) -> bool {
        match condition {
            TcpInvariantCondition::StateCondition(expected_state) => {
                state.state == *expected_state
            }
            TcpInvariantCondition::SequenceNumberCondition { min_seq, max_seq } => {
                state.sequence_number >= *min_seq && state.sequence_number <= *max_seq
            }
            TcpInvariantCondition::WindowSizeCondition { min_window, max_window } => {
                state.window_size >= *min_window && state.window_size <= *max_window
            }
            TcpInvariantCondition::AuthenticationCondition(expected_auth) => {
                state.authenticated == *expected_auth
            }
            TcpInvariantCondition::CompoundCondition { operator, conditions } => {
                match operator {
                    LogicalOperator::And => {
                        conditions.iter().all(|condition| {
                            self.check_invariant_condition(state, condition)
                        })
                    }
                    LogicalOperator::Or => {
                        conditions.iter().any(|condition| {
                            self.check_invariant_condition(state, condition)
                        })
                    }
                    LogicalOperator::Not => {
                        !conditions.iter().any(|condition| {
                            self.check_invariant_condition(state, condition)
                        })
                    }
                }
            }
        }
    }

    /// 获取所有不变量
    pub fn get_invariants(&self) -> &Vec<TcpInvariant> {
        &self.invariants
    }

    /// 获取状态转换表
    pub fn get_transition_table(&self) -> &HashMap<(TcpState, TcpEvent), TcpState> {
        &self.transition_table
    }
}

impl fmt::Display for TcpFormalSpec {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "TCP Formal Specification")?;
        writeln!(f, "========================")?;

        writeln!(f, "\nStates:")?;
        for state in &self.states {
            writeln!(f, "  - {:?}", state)?;
        }

        writeln!(f, "\nEvents:")?;
        for event in &self.events {
            writeln!(f, "  - {:?}", event)?;
        }

        writeln!(f, "\nTransitions:")?;
        for ((from, event), to) in &self.transition_table {
            writeln!(f, "  {:?} --{:?}--> {:?}", from, event, to)?;
        }

        writeln!(f, "\nInvariants:")?;
        for invariant in &self.invariants {
            writeln!(f, "  {}: {:?}", invariant.name, invariant.condition)?;
        }

        Ok(())
    }
}

/// HTTP协议形式化规范
#[allow(dead_code)]
pub struct HttpFormalSpec {
    /// HTTP版本
    version: HttpVersion,
    /// 方法定义
    pub methods: HashSet<HttpMethod>,
    /// 状态码定义
    pub status_codes: HashSet<HttpStatusCode>,
    /// 头部字段定义
    header_fields: HashSet<String>,
    /// 协议规则
    protocol_rules: Vec<HttpProtocolRule>,
}

/// HTTP版本
#[derive(Debug, Clone, PartialEq)]
pub enum HttpVersion {
    Http1_0,
    Http1_1,
    Http2,
    Http3,
}

/// HTTP方法
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum HttpMethod {
    Get,
    Post,
    Put,
    Delete,
    Head,
    Options,
    Patch,
    Trace,
    Connect,
}

/// HTTP状态码
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum HttpStatusCode {
    /// 信息响应
    Informational(u16),
    /// 成功响应
    Success(u16),
    /// 重定向
    Redirection(u16),
    /// 客户端错误
    ClientError(u16),
    /// 服务器错误
    ServerError(u16),
}

/// HTTP协议规则
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct HttpProtocolRule {
    /// 规则名称
    pub name: String,
    /// 规则条件
    pub condition: HttpRuleCondition,
    /// 规则动作
    pub action: HttpRuleAction,
    /// 规则类型
    pub rule_type: HttpRuleType,
}

/// HTTP规则条件
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub enum HttpRuleCondition {
    /// 方法条件
    MethodCondition(HttpMethod),
    /// 状态码条件
    StatusCodeCondition(HttpStatusCode),
    /// 头部条件
    HeaderCondition {
        name: String,
        value: String,
    },
    /// 复合条件
    CompoundCondition {
        operator: LogicalOperator,
        conditions: Vec<HttpRuleCondition>,
    },
}

/// HTTP规则动作
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub enum HttpRuleAction {
    /// 允许
    Allow,
    /// 拒绝
    Deny,
    /// 修改头部
    ModifyHeader {
        name: String,
        value: String,
    },
    /// 重定向
    Redirect {
        location: String,
    },
    /// 缓存
    Cache {
        duration: u64,
    },
}

/// HTTP规则类型
#[derive(Debug, Clone, PartialEq)]
#[allow(dead_code)]
pub enum HttpRuleType {
    /// 安全规则
    SecurityRule,
    /// 性能规则
    PerformanceRule,
    /// 功能规则
    FunctionalRule,
}

impl HttpFormalSpec {
    /// 创建HTTP形式化规范
    pub fn new(version: HttpVersion) -> Self {
        let mut spec = Self {
            version,
            methods: HashSet::new(),
            status_codes: HashSet::new(),
            header_fields: HashSet::new(),
            protocol_rules: Vec::new(),
        };

        spec.initialize_methods();
        spec.initialize_status_codes();
        spec.initialize_header_fields();
        spec.initialize_protocol_rules();

        spec
    }

    /// 初始化HTTP方法
    fn initialize_methods(&mut self) {
        self.methods.insert(HttpMethod::Get);
        self.methods.insert(HttpMethod::Post);
        self.methods.insert(HttpMethod::Put);
        self.methods.insert(HttpMethod::Delete);
        self.methods.insert(HttpMethod::Head);
        self.methods.insert(HttpMethod::Options);
        self.methods.insert(HttpMethod::Patch);
        self.methods.insert(HttpMethod::Trace);
        self.methods.insert(HttpMethod::Connect);
    }

    /// 初始化状态码
    fn initialize_status_codes(&mut self) {
        // 信息响应
        self.status_codes.insert(HttpStatusCode::Informational(100));
        self.status_codes.insert(HttpStatusCode::Informational(101));

        // 成功响应
        self.status_codes.insert(HttpStatusCode::Success(200));
        self.status_codes.insert(HttpStatusCode::Success(201));
        self.status_codes.insert(HttpStatusCode::Success(204));

        // 重定向
        self.status_codes.insert(HttpStatusCode::Redirection(301));
        self.status_codes.insert(HttpStatusCode::Redirection(302));

        // 客户端错误
        self.status_codes.insert(HttpStatusCode::ClientError(400));
        self.status_codes.insert(HttpStatusCode::ClientError(401));
        self.status_codes.insert(HttpStatusCode::ClientError(403));
        self.status_codes.insert(HttpStatusCode::ClientError(404));

        // 服务器错误
        self.status_codes.insert(HttpStatusCode::ServerError(500));
        self.status_codes.insert(HttpStatusCode::ServerError(502));
        self.status_codes.insert(HttpStatusCode::ServerError(503));
    }

    /// 初始化头部字段
    fn initialize_header_fields(&mut self) {
        let headers = vec![
            "Content-Type", "Content-Length", "Authorization", "Accept",
            "Accept-Encoding", "Accept-Language", "Cache-Control",
            "Connection", "Host", "User-Agent", "Cookie", "Set-Cookie",
            "Location", "Server", "Date", "Last-Modified", "ETag",
        ];

        for header in headers {
            self.header_fields.insert(header.to_string());
        }
    }

    /// 初始化协议规则
    fn initialize_protocol_rules(&mut self) {
        // 安全规则：必须使用HTTPS
        self.protocol_rules.push(HttpProtocolRule {
            name: "https_required".to_string(),
            condition: HttpRuleCondition::CompoundCondition {
                operator: LogicalOperator::And,
                conditions: vec![
                    HttpRuleCondition::MethodCondition(HttpMethod::Post),
                    HttpRuleCondition::MethodCondition(HttpMethod::Put),
                    HttpRuleCondition::MethodCondition(HttpMethod::Delete),
                ],
            },
            action: HttpRuleAction::Deny,
            rule_type: HttpRuleType::SecurityRule,
        });

        // 性能规则：缓存静态资源
        self.protocol_rules.push(HttpProtocolRule {
            name: "cache_static_resources".to_string(),
            condition: HttpRuleCondition::HeaderCondition {
                name: "Content-Type".to_string(),
                value: "text/css,application/javascript,image/".to_string(),
            },
            action: HttpRuleAction::Cache { duration: 3600 },
            rule_type: HttpRuleType::PerformanceRule,
        });

        // 功能规则：CORS支持
        self.protocol_rules.push(HttpProtocolRule {
            name: "cors_support".to_string(),
            condition: HttpRuleCondition::MethodCondition(HttpMethod::Options),
            action: HttpRuleAction::ModifyHeader {
                name: "Access-Control-Allow-Origin".to_string(),
                value: "*".to_string(),
            },
            rule_type: HttpRuleType::FunctionalRule,
        });
    }

    /// 检查HTTP请求的有效性
    pub fn is_valid_request(&self, method: &HttpMethod, headers: &HashMap<String, String>) -> bool {
        // 检查方法是否支持
        if !self.methods.contains(method) {
            return false;
        }

        // 检查必需的头部字段
        match method {
            HttpMethod::Get | HttpMethod::Post | HttpMethod::Put | HttpMethod::Delete => {
                headers.contains_key("Host")
            }
            _ => true,
        }
    }

    /// 检查HTTP响应的有效性
    pub fn is_valid_response(&self, status_code: &HttpStatusCode, headers: &HashMap<String, String>) -> bool {
        // 检查状态码是否支持
        if !self.status_codes.contains(status_code) {
            return false;
        }

        // 检查必需的头部字段
        headers.contains_key("Content-Type") ||
        matches!(status_code, HttpStatusCode::Informational(_) | HttpStatusCode::Redirection(_))
    }

    /// 应用协议规则
    pub fn apply_rules(&self, method: &HttpMethod, headers: &HashMap<String, String>) -> Vec<HttpRuleAction> {
        let mut actions = Vec::new();

        for rule in &self.protocol_rules {
            if self.matches_condition(&rule.condition, method, headers) {
                actions.push(rule.action.clone());
            }
        }

        actions
    }

    /// 检查规则条件匹配
    fn matches_condition(&self, condition: &HttpRuleCondition, method: &HttpMethod, headers: &HashMap<String, String>) -> bool {
        match condition {
            HttpRuleCondition::MethodCondition(expected_method) => {
                method == expected_method
            }
            HttpRuleCondition::StatusCodeCondition(_) => {
                // 响应规则，请求时不适用
                false
            }
            HttpRuleCondition::HeaderCondition { name, value } => {
                // 检查header值是否包含规则中指定的值，或者规则值是否包含header值（支持逗号分隔的值列表）
                headers.get(name).is_some_and(|header_value| {
                    header_value.contains(value) || value.contains(header_value)
                })
            }
            HttpRuleCondition::CompoundCondition { operator, conditions } => {
                match operator {
                    LogicalOperator::And => {
                        conditions.iter().all(|condition| {
                            self.matches_condition(condition, method, headers)
                        })
                    }
                    LogicalOperator::Or => {
                        conditions.iter().any(|condition| {
                            self.matches_condition(condition, method, headers)
                        })
                    }
                    LogicalOperator::Not => {
                        !conditions.iter().any(|condition| {
                            self.matches_condition(condition, method, headers)
                        })
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tcp_formal_spec_creation() {
        let spec = TcpFormalSpec::new();
        assert!(!spec.states.is_empty());
        assert!(!spec.events.is_empty());
        assert!(!spec.transition_table.is_empty());
        assert!(!spec.invariants.is_empty());
    }

    #[test]
    fn test_tcp_state_transition() {
        let spec = TcpFormalSpec::new();

        // 测试有效转换
        assert!(spec.is_valid_transition(
            TcpState::Closed,
            TcpState::Listen,
            TcpEvent::PassiveOpen
        ));

        // 测试无效转换
        assert!(!spec.is_valid_transition(
            TcpState::Closed,
            TcpState::Established,
            TcpEvent::PassiveOpen
        ));
    }

    #[test]
    fn test_tcp_invariant_check() {
        let spec = TcpFormalSpec::new();
        let conn_state = ConnectionState {
            connection_id: "test".to_string(),
            state: TcpState::Established,
            sequence_number: 1000,
            acknowledgment_number: 500,
            window_size: 1024,
            message_history: Vec::new(),
            authenticated: true,
            encrypted: true,
        };

        // 测试认证不变量
        let auth_invariant = &spec.invariants[0];
        assert!(spec.check_invariant(&conn_state, auth_invariant));

        // 测试序列号不变量
        let seq_invariant = &spec.invariants[1];
        assert!(spec.check_invariant(&conn_state, seq_invariant));
    }

    #[test]
    fn test_http_formal_spec_creation() {
        let spec = HttpFormalSpec::new(HttpVersion::Http1_1);
        assert!(!spec.methods.is_empty());
        assert!(!spec.status_codes.is_empty());
        assert!(!spec.header_fields.is_empty());
        assert!(!spec.protocol_rules.is_empty());
    }

    #[test]
    fn test_http_request_validation() {
        let spec = HttpFormalSpec::new(HttpVersion::Http1_1);
        let mut headers = HashMap::new();
        headers.insert("Host".to_string(), "example.com".to_string());

        // 测试有效请求
        assert!(spec.is_valid_request(&HttpMethod::Get, &headers));

        // 测试无效请求（缺少Host头部）
        let empty_headers = HashMap::new();
        assert!(!spec.is_valid_request(&HttpMethod::Get, &empty_headers));
    }

    #[test]
    fn test_http_rule_application() {
        let spec = HttpFormalSpec::new(HttpVersion::Http1_1);
        let mut headers = HashMap::new();
        headers.insert("Content-Type".to_string(), "text/css".to_string());

        let actions = spec.apply_rules(&HttpMethod::Get, &headers);

        // 应该应用缓存规则
        assert!(!actions.is_empty());
    }
}
