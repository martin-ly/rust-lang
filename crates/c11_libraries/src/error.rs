#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[cfg(feature = "kv-redis")]
    #[error("redis error: {0}")]
    Redis(#[from] redis::RedisError),

    #[cfg(feature = "sql-postgres")]
    #[error("postgres error: {0}")]
    Postgres(#[from] tokio_postgres::Error),

    #[cfg(feature = "sql-mysql")]
    #[error("mysql error: {0}")]
    Mysql(#[from] mysql_async::Error),

    #[cfg(feature = "sql-sqlite")]
    #[error("sqlite error: {0}")]
    Sqlite(#[from] rusqlite::Error),

    #[cfg(feature = "mq-nats")]
    #[error("nats error: {0}")]
    Nats(String),

    #[cfg(feature = "mq-kafka")]
    #[error("kafka error: {0}")]
    Kafka(#[from] rdkafka::error::KafkaError),

    #[error("io error: {0}")]
    Io(#[from] std::io::Error),

    #[error("other: {0}")]
    Other(String),

    #[cfg(feature = "tokio")]
    #[error("join error: {0}")]
    Join(#[from] tokio::task::JoinError),

    #[cfg(feature = "mq-nats")]
    #[error("nats subscribe error: {0}")]
    NatsSubscribe(#[from] async_nats::SubscribeError),

    #[cfg(feature = "mq-mqtt")]
    #[error("mqtt client error: {0}")]
    MqttClient(#[from] rumqttc::ClientError),

    #[cfg(feature = "mq-mqtt")]
    #[error("mqtt connection error: {0}")]
    MqttConnection(#[from] rumqttc::ConnectionError),
}

pub type Result<T> = std::result::Result<T, Error>;
