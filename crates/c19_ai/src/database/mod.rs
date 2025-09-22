//! 数据库模块
//! 
//! 提供数据库连接、查询和事务管理功能

pub mod connection;
pub mod models;
pub mod migrations;
pub mod repository;
pub mod transaction;
pub mod orm;
pub mod entities;
pub mod schema;

// 连接模块导出
pub use connection::{
    DatabaseManager, DatabaseConnection, DatabaseType, DatabaseConfig, SslMode,
    QueryBuilder, QueryType, Condition, Operator, Join, JoinType, OrderBy, SortDirection
};

// 模型模块导出
pub use models::DatabaseModel;

// 迁移模块导出
pub use migrations::DatabaseMigrationRecord;

// 仓库模块导出
pub use repository::DatabaseRepository;

// 事务模块导出
pub use transaction::{
    TransactionManager, Transaction, TransactionStatus, IsolationLevel,
    TransactionOperation, OperationType, TransactionStats, TransactionBuilder, TransactionContext, TransactionError
};

// ORM模块导出
pub use orm::{
    OrmManager, EntityMetadata, ColumnMetadata, DataType, Constraint, IndexMetadata, IndexType,
    RelationshipMetadata, RelationshipType, CascadeOption, QueryCondition, QueryOperator,
    LogicalOperator, BaseEntity, UserEntity, ModelEntity, TrainingJobEntity, InferenceRequestEntity,
    DatasetEntity, OrmTransaction
};

// 实体模块导出
pub use entities::{
    UserRepository, ModelRepository, TrainingJobRepository, InferenceRequestRepository,
    DatasetRepository, ModelStats, InferenceStats, DatasetStats
};

// 模式模块导出
pub use schema::{
    SchemaManager, Migration, initialize_schema, get_entity_metadata
};
