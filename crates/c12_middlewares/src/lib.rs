pub mod prelude {
    pub use crate::kv::KeyValueStore;
    pub use crate::mq::{MessageConsumer, MessageProducer};
    pub use crate::sql::{SqlDatabase, SqlRow};
}

pub mod kv;
pub mod mq;
pub mod sql;
pub mod config;
pub mod util;

mod error;
pub use error::Error;

#[cfg(feature = "kv-redis")]
pub mod redis_client;

#[cfg(feature = "sql-postgres")]
pub mod postgres_client;

#[cfg(feature = "sql-mysql")]
pub mod mysql_client;

#[cfg(feature = "sql-sqlite")]
pub mod sqlite_client;

#[cfg(feature = "mq-nats")]
pub mod nats_client;

#[cfg(feature = "mq-kafka")]
pub mod kafka_client;

#[cfg(feature = "mq-mqtt")]
pub mod mqtt_client;

#[cfg(feature = "proxy-pingora")]
pub mod pingora_proxy;

