//! 数据库模式模块
//! 
//! 定义数据库表结构和迁移脚本

use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use uuid::Uuid;
use chrono::{DateTime, Utc};

use super::orm::*;

/// 数据库模式管理器
#[derive(Debug)]
pub struct SchemaManager {
    migrations: Vec<Migration>,
    current_version: u32,
}

/// 数据库迁移
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Migration {
    pub id: Uuid,
    pub version: u32,
    pub name: String,
    pub description: String,
    pub up_sql: String,
    pub down_sql: String,
    pub created_at: DateTime<Utc>,
    pub applied_at: Option<DateTime<Utc>>,
}

impl Migration {
    pub fn new(version: u32, name: String, description: String, up_sql: String, down_sql: String) -> Self {
        Self {
            id: Uuid::new_v4(),
            version,
            name,
            description,
            up_sql,
            down_sql,
            created_at: Utc::now(),
            applied_at: None,
        }
    }
}

impl SchemaManager {
    pub fn new() -> Self {
        Self {
            migrations: Vec::new(),
            current_version: 0,
        }
    }

    /// 添加迁移
    pub fn add_migration(&mut self, migration: Migration) {
        self.migrations.push(migration);
        self.migrations.sort_by_key(|m| m.version);
    }

    /// 获取所有迁移
    pub fn get_migrations(&self) -> &Vec<Migration> {
        &self.migrations
    }

    /// 获取待应用的迁移
    pub fn get_pending_migrations(&self) -> Vec<&Migration> {
        self.migrations
            .iter()
            .filter(|m| m.version > self.current_version)
            .collect()
    }

    /// 应用迁移
    pub async fn apply_migration(&mut self, migration: &Migration) -> Result<()> {
        // TODO: 执行up_sql
        tracing::info!("Applying migration: {} - {}", migration.version, migration.name);
        
        // 更新当前版本
        self.current_version = migration.version;
        
        Ok(())
    }

    /// 回滚迁移
    pub async fn rollback_migration(&mut self, migration: &Migration) -> Result<()> {
        // TODO: 执行down_sql
        tracing::info!("Rolling back migration: {} - {}", migration.version, migration.name);
        
        // 更新当前版本
        if let Some(prev_migration) = self.migrations
            .iter()
            .rev()
            .find(|m| m.version < migration.version) {
            self.current_version = prev_migration.version;
        } else {
            self.current_version = 0;
        }
        
        Ok(())
    }

    /// 获取当前版本
    pub fn get_current_version(&self) -> u32 {
        self.current_version
    }
}

/// 初始化数据库模式
pub fn initialize_schema() -> SchemaManager {
    let mut schema_manager = SchemaManager::new();

    // 创建用户表迁移
    let create_users_table = Migration::new(
        1,
        "create_users_table".to_string(),
        "创建用户表".to_string(),
        r#"
        CREATE TABLE IF NOT EXISTS users (
            id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
            username VARCHAR(50) UNIQUE NOT NULL,
            email VARCHAR(255) UNIQUE NOT NULL,
            password_hash VARCHAR(255) NOT NULL,
            first_name VARCHAR(100),
            last_name VARCHAR(100),
            is_active BOOLEAN DEFAULT true,
            last_login TIMESTAMP WITH TIME ZONE,
            roles TEXT[] DEFAULT ARRAY['user'],
            created_at TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
            updated_at TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
            version INTEGER DEFAULT 1
        );

        CREATE INDEX IF NOT EXISTS idx_users_username ON users(username);
        CREATE INDEX IF NOT EXISTS idx_users_email ON users(email);
        CREATE INDEX IF NOT EXISTS idx_users_is_active ON users(is_active);
        "#
        .to_string(),
        "DROP TABLE IF EXISTS users;".to_string(),
    );

    // 创建模型表迁移
    let create_models_table = Migration::new(
        2,
        "create_models_table".to_string(),
        "创建模型表".to_string(),
        r#"
        CREATE TABLE IF NOT EXISTS models (
            id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
            name VARCHAR(255) NOT NULL,
            version VARCHAR(50) NOT NULL,
            framework VARCHAR(50) NOT NULL,
            model_type VARCHAR(100) NOT NULL,
            status VARCHAR(50) DEFAULT 'draft',
            file_path TEXT NOT NULL,
            metadata JSONB DEFAULT '{}',
            performance_metrics JSONB DEFAULT '{}',
            tags TEXT[] DEFAULT ARRAY[]::TEXT[],
            size_bytes BIGINT DEFAULT 0,
            checksum VARCHAR(64),
            created_at TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
            updated_at TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
            version INTEGER DEFAULT 1,
            UNIQUE(name, version)
        );

        CREATE INDEX IF NOT EXISTS idx_models_name ON models(name);
        CREATE INDEX IF NOT EXISTS idx_models_framework ON models(framework);
        CREATE INDEX IF NOT EXISTS idx_models_status ON models(status);
        CREATE INDEX IF NOT EXISTS idx_models_model_type ON models(model_type);
        CREATE INDEX IF NOT EXISTS idx_models_tags ON models USING GIN(tags);
        "#
        .to_string(),
        "DROP TABLE IF EXISTS models;".to_string(),
    );

    // 创建训练任务表迁移
    let create_training_jobs_table = Migration::new(
        3,
        "create_training_jobs_table".to_string(),
        "创建训练任务表".to_string(),
        r#"
        CREATE TABLE IF NOT EXISTS training_jobs (
            id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
            model_id UUID NOT NULL REFERENCES models(id) ON DELETE CASCADE,
            dataset_id UUID NOT NULL,
            status VARCHAR(50) DEFAULT 'pending',
            config JSONB DEFAULT '{}',
            progress DECIMAL(5,2) DEFAULT 0.0,
            current_epoch INTEGER DEFAULT 0,
            total_epochs INTEGER DEFAULT 0,
            metrics JSONB DEFAULT '{}',
            started_at TIMESTAMP WITH TIME ZONE,
            completed_at TIMESTAMP WITH TIME ZONE,
            error_message TEXT,
            created_at TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
            updated_at TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
            version INTEGER DEFAULT 1
        );

        CREATE INDEX IF NOT EXISTS idx_training_jobs_model_id ON training_jobs(model_id);
        CREATE INDEX IF NOT EXISTS idx_training_jobs_dataset_id ON training_jobs(dataset_id);
        CREATE INDEX IF NOT EXISTS idx_training_jobs_status ON training_jobs(status);
        CREATE INDEX IF NOT EXISTS idx_training_jobs_created_at ON training_jobs(created_at);
        "#
        .to_string(),
        "DROP TABLE IF EXISTS training_jobs;".to_string(),
    );

    // 创建推理请求表迁移
    let create_inference_requests_table = Migration::new(
        4,
        "create_inference_requests_table".to_string(),
        "创建推理请求表".to_string(),
        r#"
        CREATE TABLE IF NOT EXISTS inference_requests (
            id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
            model_id UUID NOT NULL REFERENCES models(id) ON DELETE CASCADE,
            user_id UUID REFERENCES users(id) ON DELETE SET NULL,
            input_data JSONB NOT NULL,
            parameters JSONB DEFAULT '{}',
            status VARCHAR(50) DEFAULT 'pending',
            result JSONB,
            processing_time_ms BIGINT,
            error_message TEXT,
            priority INTEGER DEFAULT 0,
            created_at TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
            updated_at TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
            version INTEGER DEFAULT 1
        );

        CREATE INDEX IF NOT EXISTS idx_inference_requests_model_id ON inference_requests(model_id);
        CREATE INDEX IF NOT EXISTS idx_inference_requests_user_id ON inference_requests(user_id);
        CREATE INDEX IF NOT EXISTS idx_inference_requests_status ON inference_requests(status);
        CREATE INDEX IF NOT EXISTS idx_inference_requests_priority ON inference_requests(priority);
        CREATE INDEX IF NOT EXISTS idx_inference_requests_created_at ON inference_requests(created_at);
        "#
        .to_string(),
        "DROP TABLE IF EXISTS inference_requests;".to_string(),
    );

    // 创建数据集表迁移
    let create_datasets_table = Migration::new(
        5,
        "create_datasets_table".to_string(),
        "创建数据集表".to_string(),
        r#"
        CREATE TABLE IF NOT EXISTS datasets (
            id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
            name VARCHAR(255) NOT NULL,
            description TEXT,
            file_path TEXT NOT NULL,
            size_bytes BIGINT DEFAULT 0,
            format VARCHAR(50) NOT NULL,
            schema JSONB DEFAULT '{}',
            tags TEXT[] DEFAULT ARRAY[]::TEXT[],
            is_public BOOLEAN DEFAULT false,
            owner_id UUID NOT NULL REFERENCES users(id) ON DELETE CASCADE,
            created_at TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
            updated_at TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
            version INTEGER DEFAULT 1
        );

        CREATE INDEX IF NOT EXISTS idx_datasets_name ON datasets(name);
        CREATE INDEX IF NOT EXISTS idx_datasets_owner_id ON datasets(owner_id);
        CREATE INDEX IF NOT EXISTS idx_datasets_format ON datasets(format);
        CREATE INDEX IF NOT EXISTS idx_datasets_is_public ON datasets(is_public);
        CREATE INDEX IF NOT EXISTS idx_datasets_tags ON datasets USING GIN(tags);
        "#
        .to_string(),
        "DROP TABLE IF EXISTS datasets;".to_string(),
    );

    // 创建缓存表迁移
    let create_cache_table = Migration::new(
        6,
        "create_cache_table".to_string(),
        "创建缓存表".to_string(),
        r#"
        CREATE TABLE IF NOT EXISTS cache_entries (
            id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
            cache_name VARCHAR(100) NOT NULL,
            key VARCHAR(255) NOT NULL,
            value JSONB NOT NULL,
            expires_at TIMESTAMP WITH TIME ZONE,
            created_at TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
            accessed_at TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
            access_count INTEGER DEFAULT 0,
            UNIQUE(cache_name, key)
        );

        CREATE INDEX IF NOT EXISTS idx_cache_entries_cache_name ON cache_entries(cache_name);
        CREATE INDEX IF NOT EXISTS idx_cache_entries_key ON cache_entries(key);
        CREATE INDEX IF NOT EXISTS idx_cache_entries_expires_at ON cache_entries(expires_at);
        CREATE INDEX IF NOT EXISTS idx_cache_entries_accessed_at ON cache_entries(accessed_at);
        "#
        .to_string(),
        "DROP TABLE IF EXISTS cache_entries;".to_string(),
    );

    // 创建消息队列表迁移
    let create_message_queue_table = Migration::new(
        7,
        "create_message_queue_table".to_string(),
        "创建消息队列表".to_string(),
        r#"
        CREATE TABLE IF NOT EXISTS message_queue (
            id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
            queue_name VARCHAR(100) NOT NULL,
            message_type VARCHAR(50) NOT NULL,
            payload JSONB NOT NULL,
            headers JSONB DEFAULT '{}',
            status VARCHAR(50) DEFAULT 'pending',
            priority INTEGER DEFAULT 0,
            retry_count INTEGER DEFAULT 0,
            max_retries INTEGER DEFAULT 3,
            scheduled_at TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
            processed_at TIMESTAMP WITH TIME ZONE,
            error_message TEXT,
            created_at TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
            updated_at TIMESTAMP WITH TIME ZONE DEFAULT NOW()
        );

        CREATE INDEX IF NOT EXISTS idx_message_queue_queue_name ON message_queue(queue_name);
        CREATE INDEX IF NOT EXISTS idx_message_queue_status ON message_queue(status);
        CREATE INDEX IF NOT EXISTS idx_message_queue_priority ON message_queue(priority);
        CREATE INDEX IF NOT EXISTS idx_message_queue_scheduled_at ON message_queue(scheduled_at);
        "#
        .to_string(),
        "DROP TABLE IF EXISTS message_queue;".to_string(),
    );

    // 创建系统配置表迁移
    let create_system_config_table = Migration::new(
        8,
        "create_system_config_table".to_string(),
        "创建系统配置表".to_string(),
        r#"
        CREATE TABLE IF NOT EXISTS system_config (
            id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
            key VARCHAR(255) UNIQUE NOT NULL,
            value JSONB NOT NULL,
            description TEXT,
            is_encrypted BOOLEAN DEFAULT false,
            created_at TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
            updated_at TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
            updated_by UUID REFERENCES users(id) ON DELETE SET NULL
        );

        CREATE INDEX IF NOT EXISTS idx_system_config_key ON system_config(key);
        "#
        .to_string(),
        "DROP TABLE IF EXISTS system_config;".to_string(),
    );

    // 创建审计日志表迁移
    let create_audit_log_table = Migration::new(
        9,
        "create_audit_log_table".to_string(),
        "创建审计日志表".to_string(),
        r#"
        CREATE TABLE IF NOT EXISTS audit_logs (
            id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
            user_id UUID REFERENCES users(id) ON DELETE SET NULL,
            action VARCHAR(100) NOT NULL,
            resource_type VARCHAR(100) NOT NULL,
            resource_id UUID,
            old_values JSONB,
            new_values JSONB,
            ip_address INET,
            user_agent TEXT,
            created_at TIMESTAMP WITH TIME ZONE DEFAULT NOW()
        );

        CREATE INDEX IF NOT EXISTS idx_audit_logs_user_id ON audit_logs(user_id);
        CREATE INDEX IF NOT EXISTS idx_audit_logs_action ON audit_logs(action);
        CREATE INDEX IF NOT EXISTS idx_audit_logs_resource_type ON audit_logs(resource_type);
        CREATE INDEX IF NOT EXISTS idx_audit_logs_resource_id ON audit_logs(resource_id);
        CREATE INDEX IF NOT EXISTS idx_audit_logs_created_at ON audit_logs(created_at);
        "#
        .to_string(),
        "DROP TABLE IF EXISTS audit_logs;".to_string(),
    );

    // 创建迁移历史表迁移
    let create_migration_history_table = Migration::new(
        10,
        "create_migration_history_table".to_string(),
        "创建迁移历史表".to_string(),
        r#"
        CREATE TABLE IF NOT EXISTS migration_history (
            id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
            version INTEGER UNIQUE NOT NULL,
            name VARCHAR(255) NOT NULL,
            description TEXT,
            applied_at TIMESTAMP WITH TIME ZONE DEFAULT NOW(),
            checksum VARCHAR(64)
        );

        CREATE INDEX IF NOT EXISTS idx_migration_history_version ON migration_history(version);
        "#
        .to_string(),
        "DROP TABLE IF EXISTS migration_history;".to_string(),
    );

    // 添加所有迁移
    schema_manager.add_migration(create_users_table);
    schema_manager.add_migration(create_models_table);
    schema_manager.add_migration(create_training_jobs_table);
    schema_manager.add_migration(create_inference_requests_table);
    schema_manager.add_migration(create_datasets_table);
    schema_manager.add_migration(create_cache_table);
    schema_manager.add_migration(create_message_queue_table);
    schema_manager.add_migration(create_system_config_table);
    schema_manager.add_migration(create_audit_log_table);
    schema_manager.add_migration(create_migration_history_table);

    schema_manager
}

/// 获取实体元数据定义
pub fn get_entity_metadata() -> HashMap<String, EntityMetadata> {
    let mut entities = HashMap::new();

    // 用户实体元数据
    let user_metadata = EntityMetadata {
        name: "User".to_string(),
        table_name: "users".to_string(),
        primary_key: "id".to_string(),
        columns: vec![
            ColumnMetadata {
                name: "id".to_string(),
                data_type: DataType::Uuid,
                is_nullable: false,
                is_primary_key: true,
                is_foreign_key: false,
                default_value: Some("gen_random_uuid()".to_string()),
                constraints: vec![],
            },
            ColumnMetadata {
                name: "username".to_string(),
                data_type: DataType::String(Some(50)),
                is_nullable: false,
                is_primary_key: false,
                is_foreign_key: false,
                default_value: None,
                constraints: vec![Constraint::Unique],
            },
            ColumnMetadata {
                name: "email".to_string(),
                data_type: DataType::String(Some(255)),
                is_nullable: false,
                is_primary_key: false,
                is_foreign_key: false,
                default_value: None,
                constraints: vec![Constraint::Unique],
            },
            ColumnMetadata {
                name: "password_hash".to_string(),
                data_type: DataType::String(Some(255)),
                is_nullable: false,
                is_primary_key: false,
                is_foreign_key: false,
                default_value: None,
                constraints: vec![],
            },
            ColumnMetadata {
                name: "first_name".to_string(),
                data_type: DataType::String(Some(100)),
                is_nullable: true,
                is_primary_key: false,
                is_foreign_key: false,
                default_value: None,
                constraints: vec![],
            },
            ColumnMetadata {
                name: "last_name".to_string(),
                data_type: DataType::String(Some(100)),
                is_nullable: true,
                is_primary_key: false,
                is_foreign_key: false,
                default_value: None,
                constraints: vec![],
            },
            ColumnMetadata {
                name: "is_active".to_string(),
                data_type: DataType::Boolean,
                is_nullable: false,
                is_primary_key: false,
                is_foreign_key: false,
                default_value: Some("true".to_string()),
                constraints: vec![],
            },
            ColumnMetadata {
                name: "last_login".to_string(),
                data_type: DataType::DateTime,
                is_nullable: true,
                is_primary_key: false,
                is_foreign_key: false,
                default_value: None,
                constraints: vec![],
            },
            ColumnMetadata {
                name: "roles".to_string(),
                data_type: DataType::Text, // PostgreSQL array
                is_nullable: false,
                is_primary_key: false,
                is_foreign_key: false,
                default_value: Some("ARRAY['user']".to_string()),
                constraints: vec![],
            },
            ColumnMetadata {
                name: "created_at".to_string(),
                data_type: DataType::DateTime,
                is_nullable: false,
                is_primary_key: false,
                is_foreign_key: false,
                default_value: Some("NOW()".to_string()),
                constraints: vec![],
            },
            ColumnMetadata {
                name: "updated_at".to_string(),
                data_type: DataType::DateTime,
                is_nullable: false,
                is_primary_key: false,
                is_foreign_key: false,
                default_value: Some("NOW()".to_string()),
                constraints: vec![],
            },
            ColumnMetadata {
                name: "version".to_string(),
                data_type: DataType::Integer,
                is_nullable: false,
                is_primary_key: false,
                is_foreign_key: false,
                default_value: Some("1".to_string()),
                constraints: vec![],
            },
        ],
        indexes: vec![
            IndexMetadata {
                name: "idx_users_username".to_string(),
                columns: vec!["username".to_string()],
                is_unique: true,
                index_type: IndexType::BTree,
            },
            IndexMetadata {
                name: "idx_users_email".to_string(),
                columns: vec!["email".to_string()],
                is_unique: true,
                index_type: IndexType::BTree,
            },
            IndexMetadata {
                name: "idx_users_is_active".to_string(),
                columns: vec!["is_active".to_string()],
                is_unique: false,
                index_type: IndexType::BTree,
            },
        ],
        relationships: vec![],
    };

    entities.insert("User".to_string(), user_metadata);

    // 模型实体元数据
    let model_metadata = EntityMetadata {
        name: "Model".to_string(),
        table_name: "models".to_string(),
        primary_key: "id".to_string(),
        columns: vec![
            ColumnMetadata {
                name: "id".to_string(),
                data_type: DataType::Uuid,
                is_nullable: false,
                is_primary_key: true,
                is_foreign_key: false,
                default_value: Some("gen_random_uuid()".to_string()),
                constraints: vec![],
            },
            ColumnMetadata {
                name: "name".to_string(),
                data_type: DataType::String(Some(255)),
                is_nullable: false,
                is_primary_key: false,
                is_foreign_key: false,
                default_value: None,
                constraints: vec![],
            },
            ColumnMetadata {
                name: "version".to_string(),
                data_type: DataType::String(Some(50)),
                is_nullable: false,
                is_primary_key: false,
                is_foreign_key: false,
                default_value: None,
                constraints: vec![],
            },
            ColumnMetadata {
                name: "framework".to_string(),
                data_type: DataType::String(Some(50)),
                is_nullable: false,
                is_primary_key: false,
                is_foreign_key: false,
                default_value: None,
                constraints: vec![],
            },
            ColumnMetadata {
                name: "model_type".to_string(),
                data_type: DataType::String(Some(100)),
                is_nullable: false,
                is_primary_key: false,
                is_foreign_key: false,
                default_value: None,
                constraints: vec![],
            },
            ColumnMetadata {
                name: "status".to_string(),
                data_type: DataType::String(Some(50)),
                is_nullable: false,
                is_primary_key: false,
                is_foreign_key: false,
                default_value: Some("'draft'".to_string()),
                constraints: vec![],
            },
            ColumnMetadata {
                name: "file_path".to_string(),
                data_type: DataType::Text,
                is_nullable: false,
                is_primary_key: false,
                is_foreign_key: false,
                default_value: None,
                constraints: vec![],
            },
            ColumnMetadata {
                name: "metadata".to_string(),
                data_type: DataType::Json,
                is_nullable: false,
                is_primary_key: false,
                is_foreign_key: false,
                default_value: Some("'{}'".to_string()),
                constraints: vec![],
            },
            ColumnMetadata {
                name: "performance_metrics".to_string(),
                data_type: DataType::Json,
                is_nullable: false,
                is_primary_key: false,
                is_foreign_key: false,
                default_value: Some("'{}'".to_string()),
                constraints: vec![],
            },
            ColumnMetadata {
                name: "tags".to_string(),
                data_type: DataType::Text, // PostgreSQL array
                is_nullable: false,
                is_primary_key: false,
                is_foreign_key: false,
                default_value: Some("ARRAY[]::TEXT[]".to_string()),
                constraints: vec![],
            },
            ColumnMetadata {
                name: "size_bytes".to_string(),
                data_type: DataType::BigInt,
                is_nullable: false,
                is_primary_key: false,
                is_foreign_key: false,
                default_value: Some("0".to_string()),
                constraints: vec![],
            },
            ColumnMetadata {
                name: "checksum".to_string(),
                data_type: DataType::String(Some(64)),
                is_nullable: true,
                is_primary_key: false,
                is_foreign_key: false,
                default_value: None,
                constraints: vec![],
            },
            ColumnMetadata {
                name: "created_at".to_string(),
                data_type: DataType::DateTime,
                is_nullable: false,
                is_primary_key: false,
                is_foreign_key: false,
                default_value: Some("NOW()".to_string()),
                constraints: vec![],
            },
            ColumnMetadata {
                name: "updated_at".to_string(),
                data_type: DataType::DateTime,
                is_nullable: false,
                is_primary_key: false,
                is_foreign_key: false,
                default_value: Some("NOW()".to_string()),
                constraints: vec![],
            },
            ColumnMetadata {
                name: "version".to_string(),
                data_type: DataType::Integer,
                is_nullable: false,
                is_primary_key: false,
                is_foreign_key: false,
                default_value: Some("1".to_string()),
                constraints: vec![],
            },
        ],
        indexes: vec![
            IndexMetadata {
                name: "idx_models_name".to_string(),
                columns: vec!["name".to_string()],
                is_unique: false,
                index_type: IndexType::BTree,
            },
            IndexMetadata {
                name: "idx_models_framework".to_string(),
                columns: vec!["framework".to_string()],
                is_unique: false,
                index_type: IndexType::BTree,
            },
            IndexMetadata {
                name: "idx_models_status".to_string(),
                columns: vec!["status".to_string()],
                is_unique: false,
                index_type: IndexType::BTree,
            },
            IndexMetadata {
                name: "idx_models_model_type".to_string(),
                columns: vec!["model_type".to_string()],
                is_unique: false,
                index_type: IndexType::BTree,
            },
            IndexMetadata {
                name: "idx_models_tags".to_string(),
                columns: vec!["tags".to_string()],
                is_unique: false,
                index_type: IndexType::Gin,
            },
        ],
        relationships: vec![],
    };

    entities.insert("Model".to_string(), model_metadata);

    entities
}
