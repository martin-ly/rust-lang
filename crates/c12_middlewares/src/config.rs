#[derive(Clone, Debug)]
pub struct RetryPolicy {
    pub max_retries: u32,
    pub initial_backoff_ms: u64,
    pub max_backoff_ms: u64,
}

impl Default for RetryPolicy {
    fn default() -> Self {
        Self {
            max_retries: 3,
            initial_backoff_ms: 100,
            max_backoff_ms: 2_000,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Timeouts {
    pub connect_timeout_ms: u64,
    pub op_timeout_ms: u64,
}

impl Default for Timeouts {
    fn default() -> Self {
        Self {
            connect_timeout_ms: 5_000,
            op_timeout_ms: 5_000,
        }
    }
}

#[derive(Clone, Debug)]
pub struct RedisConfig {
    pub url: String,
    pub timeouts: Timeouts,
    pub retry: RetryPolicy,
}

impl RedisConfig {
    pub fn new(url: impl Into<String>) -> Self {
        Self {
            url: url.into(),
            timeouts: Timeouts::default(),
            retry: RetryPolicy::default(),
        }
    }

    pub fn with_pool_size(self, _pool_size: u32) -> Self {
        // 这里可以扩展配置来支持连接池大小
        self
    }
}

#[derive(Clone, Debug)]
pub struct PostgresConfig {
    pub url: String,
    pub timeouts: Timeouts,
    pub retry: RetryPolicy,
}

impl PostgresConfig {
    pub fn new(url: impl Into<String>) -> Self {
        Self {
            url: url.into(),
            timeouts: Timeouts::default(),
            retry: RetryPolicy::default(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct NatsConfig {
    pub url: String,
    pub subject: String,
    pub timeouts: Timeouts,
    pub retry: RetryPolicy,
}

impl NatsConfig {
    pub fn new(url: impl Into<String>, subject: impl Into<String>) -> Self {
        Self {
            url: url.into(),
            subject: subject.into(),
            timeouts: Timeouts::default(),
            retry: RetryPolicy::default(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct MqttConfig {
    pub host: String,
    pub port: u16,
    pub client_id: String,
    pub timeouts: Timeouts,
    pub retry: RetryPolicy,
}

impl MqttConfig {
    pub fn new(host: impl Into<String>, port: u16, client_id: impl Into<String>) -> Self {
        Self {
            host: host.into(),
            port,
            client_id: client_id.into(),
            timeouts: Timeouts::default(),
            retry: RetryPolicy::default(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct KafkaConfig {
    pub bootstrap_servers: String,
    pub group_id: String,
    pub auto_offset_reset: String,
    pub timeouts: Timeouts,
    pub retry: RetryPolicy,
}

impl KafkaConfig {
    pub fn new(bootstrap_servers: impl Into<String>, group_id: impl Into<String>) -> Self {
        Self {
            bootstrap_servers: bootstrap_servers.into(),
            group_id: group_id.into(),
            auto_offset_reset: "earliest".to_string(),
            timeouts: Timeouts::default(),
            retry: RetryPolicy::default(),
        }
    }
}
