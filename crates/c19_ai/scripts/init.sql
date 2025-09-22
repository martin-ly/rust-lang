-- C19 AI 数据库初始化脚本

-- 创建扩展
CREATE EXTENSION IF NOT EXISTS "uuid-ossp";
CREATE EXTENSION IF NOT EXISTS "pg_trgm";

-- 创建用户表
CREATE TABLE IF NOT EXISTS users (
    id UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
    username VARCHAR(50) UNIQUE NOT NULL,
    email VARCHAR(100) UNIQUE NOT NULL,
    password_hash VARCHAR(255) NOT NULL,
    created_at TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP,
    updated_at TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP,
    is_active BOOLEAN DEFAULT TRUE
);

-- 创建模型表
CREATE TABLE IF NOT EXISTS models (
    id UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
    name VARCHAR(100) NOT NULL,
    version VARCHAR(20) NOT NULL,
    model_type VARCHAR(50) NOT NULL,
    framework VARCHAR(50) NOT NULL,
    file_path TEXT NOT NULL,
    metadata JSONB,
    created_at TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP,
    updated_at TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP,
    is_active BOOLEAN DEFAULT TRUE,
    UNIQUE(name, version)
);

-- 创建训练任务表
CREATE TABLE IF NOT EXISTS training_jobs (
    id UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
    user_id UUID REFERENCES users(id),
    model_id UUID REFERENCES models(id),
    status VARCHAR(20) NOT NULL DEFAULT 'pending',
    config JSONB NOT NULL,
    metrics JSONB,
    started_at TIMESTAMP WITH TIME ZONE,
    completed_at TIMESTAMP WITH TIME ZONE,
    created_at TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP,
    updated_at TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP
);

-- 创建推理任务表
CREATE TABLE IF NOT EXISTS inference_jobs (
    id UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
    user_id UUID REFERENCES users(id),
    model_id UUID REFERENCES models(id),
    input_data JSONB NOT NULL,
    output_data JSONB,
    status VARCHAR(20) NOT NULL DEFAULT 'pending',
    processing_time_ms INTEGER,
    created_at TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP,
    completed_at TIMESTAMP WITH TIME ZONE
);

-- 创建数据集表
CREATE TABLE IF NOT EXISTS datasets (
    id UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
    name VARCHAR(100) NOT NULL,
    description TEXT,
    file_path TEXT NOT NULL,
    size_bytes BIGINT,
    row_count BIGINT,
    metadata JSONB,
    created_at TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP,
    updated_at TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP,
    is_active BOOLEAN DEFAULT TRUE
);

-- 创建性能指标表
CREATE TABLE IF NOT EXISTS performance_metrics (
    id UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
    model_id UUID REFERENCES models(id),
    metric_name VARCHAR(50) NOT NULL,
    metric_value DECIMAL(10,6) NOT NULL,
    metric_type VARCHAR(20) NOT NULL, -- 'accuracy', 'loss', 'latency', etc.
    recorded_at TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP
);

-- 创建审计日志表
CREATE TABLE IF NOT EXISTS audit_logs (
    id UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
    user_id UUID REFERENCES users(id),
    action VARCHAR(50) NOT NULL,
    resource_type VARCHAR(50) NOT NULL,
    resource_id UUID,
    details JSONB,
    ip_address INET,
    user_agent TEXT,
    created_at TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP
);

-- 创建索引
CREATE INDEX IF NOT EXISTS idx_users_username ON users(username);
CREATE INDEX IF NOT EXISTS idx_users_email ON users(email);
CREATE INDEX IF NOT EXISTS idx_models_name_version ON models(name, version);
CREATE INDEX IF NOT EXISTS idx_models_type ON models(model_type);
CREATE INDEX IF NOT EXISTS idx_training_jobs_user_id ON training_jobs(user_id);
CREATE INDEX IF NOT EXISTS idx_training_jobs_status ON training_jobs(status);
CREATE INDEX IF NOT EXISTS idx_inference_jobs_user_id ON inference_jobs(user_id);
CREATE INDEX IF NOT EXISTS idx_inference_jobs_model_id ON inference_jobs(model_id);
CREATE INDEX IF NOT EXISTS idx_inference_jobs_status ON inference_jobs(status);
CREATE INDEX IF NOT EXISTS idx_performance_metrics_model_id ON performance_metrics(model_id);
CREATE INDEX IF NOT EXISTS idx_performance_metrics_name ON performance_metrics(metric_name);
CREATE INDEX IF NOT EXISTS idx_audit_logs_user_id ON audit_logs(user_id);
CREATE INDEX IF NOT EXISTS idx_audit_logs_created_at ON audit_logs(created_at);

-- 创建触发器函数
CREATE OR REPLACE FUNCTION update_updated_at_column()
RETURNS TRIGGER AS $$
BEGIN
    NEW.updated_at = CURRENT_TIMESTAMP;
    RETURN NEW;
END;
$$ language 'plpgsql';

-- 创建触发器
CREATE TRIGGER update_users_updated_at BEFORE UPDATE ON users
    FOR EACH ROW EXECUTE FUNCTION update_updated_at_column();

CREATE TRIGGER update_models_updated_at BEFORE UPDATE ON models
    FOR EACH ROW EXECUTE FUNCTION update_updated_at_column();

CREATE TRIGGER update_training_jobs_updated_at BEFORE UPDATE ON training_jobs
    FOR EACH ROW EXECUTE FUNCTION update_updated_at_column();

CREATE TRIGGER update_datasets_updated_at BEFORE UPDATE ON datasets
    FOR EACH ROW EXECUTE FUNCTION update_updated_at_column();

-- 插入初始数据
INSERT INTO users (username, email, password_hash) VALUES
    ('admin', 'admin@c19-ai.com', '$2b$12$LQv3c1yqBWVHxkd0LHAkCOYz6TtxMQJqhN8/LewdBPj4J/8Kz8KzK') -- password: admin123
ON CONFLICT (username) DO NOTHING;

-- 创建视图
CREATE OR REPLACE VIEW model_performance_summary AS
SELECT 
    m.id,
    m.name,
    m.version,
    m.model_type,
    m.framework,
    COUNT(pm.id) as metric_count,
    AVG(CASE WHEN pm.metric_type = 'accuracy' THEN pm.metric_value END) as avg_accuracy,
    AVG(CASE WHEN pm.metric_type = 'latency' THEN pm.metric_value END) as avg_latency,
    MAX(pm.recorded_at) as last_metric_recorded
FROM models m
LEFT JOIN performance_metrics pm ON m.id = pm.model_id
WHERE m.is_active = TRUE
GROUP BY m.id, m.name, m.version, m.model_type, m.framework;

-- 创建存储过程
CREATE OR REPLACE FUNCTION cleanup_old_audit_logs(days_to_keep INTEGER DEFAULT 90)
RETURNS INTEGER AS $$
DECLARE
    deleted_count INTEGER;
BEGIN
    DELETE FROM audit_logs 
    WHERE created_at < CURRENT_TIMESTAMP - INTERVAL '1 day' * days_to_keep;
    
    GET DIAGNOSTICS deleted_count = ROW_COUNT;
    RETURN deleted_count;
END;
$$ LANGUAGE plpgsql;

-- 创建定期清理任务（需要pg_cron扩展）
-- SELECT cron.schedule('cleanup-audit-logs', '0 2 * * *', 'SELECT cleanup_old_audit_logs(90);');

-- 创建角色和权限表
CREATE TABLE IF NOT EXISTS roles (
    id UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
    name VARCHAR(50) UNIQUE NOT NULL,
    description TEXT,
    permissions JSONB,
    created_at TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP,
    updated_at TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP
);

CREATE TABLE IF NOT EXISTS user_roles (
    id UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
    user_id UUID REFERENCES users(id) ON DELETE CASCADE,
    role_id UUID REFERENCES roles(id) ON DELETE CASCADE,
    assigned_at TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP,
    assigned_by UUID REFERENCES users(id),
    UNIQUE(user_id, role_id)
);

-- 创建会话表
CREATE TABLE IF NOT EXISTS user_sessions (
    id UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
    user_id UUID REFERENCES users(id) ON DELETE CASCADE,
    session_token VARCHAR(255) UNIQUE NOT NULL,
    expires_at TIMESTAMP WITH TIME ZONE NOT NULL,
    ip_address INET,
    user_agent TEXT,
    created_at TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP,
    last_accessed TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP
);

-- 创建API密钥表
CREATE TABLE IF NOT EXISTS api_keys (
    id UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
    user_id UUID REFERENCES users(id) ON DELETE CASCADE,
    key_name VARCHAR(100) NOT NULL,
    key_hash VARCHAR(255) UNIQUE NOT NULL,
    permissions JSONB,
    expires_at TIMESTAMP WITH TIME ZONE,
    last_used TIMESTAMP WITH TIME ZONE,
    created_at TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP,
    is_active BOOLEAN DEFAULT TRUE
);

-- 创建系统配置表
CREATE TABLE IF NOT EXISTS system_config (
    id UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
    config_key VARCHAR(100) UNIQUE NOT NULL,
    config_value JSONB NOT NULL,
    description TEXT,
    created_at TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP,
    updated_at TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP
);

-- 创建缓存统计表
CREATE TABLE IF NOT EXISTS cache_statistics (
    id UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
    cache_name VARCHAR(100) NOT NULL,
    hit_count BIGINT DEFAULT 0,
    miss_count BIGINT DEFAULT 0,
    total_requests BIGINT DEFAULT 0,
    memory_usage_bytes BIGINT DEFAULT 0,
    last_updated TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP
);

-- 创建存储后端表
CREATE TABLE IF NOT EXISTS storage_backends (
    id UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
    name VARCHAR(100) UNIQUE NOT NULL,
    backend_type VARCHAR(50) NOT NULL, -- 'local', 's3', 'gcs', 'azure'
    configuration JSONB NOT NULL,
    is_active BOOLEAN DEFAULT TRUE,
    created_at TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP,
    updated_at TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP
);

-- 创建文件元数据表
CREATE TABLE IF NOT EXISTS file_metadata (
    id UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
    file_path TEXT NOT NULL,
    file_name VARCHAR(255) NOT NULL,
    file_size BIGINT NOT NULL,
    mime_type VARCHAR(100),
    checksum VARCHAR(64),
    storage_backend_id UUID REFERENCES storage_backends(id),
    created_at TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP,
    updated_at TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP
);

-- 添加新表的索引
CREATE INDEX IF NOT EXISTS idx_user_roles_user_id ON user_roles(user_id);
CREATE INDEX IF NOT EXISTS idx_user_roles_role_id ON user_roles(role_id);
CREATE INDEX IF NOT EXISTS idx_user_sessions_user_id ON user_sessions(user_id);
CREATE INDEX IF NOT EXISTS idx_user_sessions_token ON user_sessions(session_token);
CREATE INDEX IF NOT EXISTS idx_user_sessions_expires ON user_sessions(expires_at);
CREATE INDEX IF NOT EXISTS idx_api_keys_user_id ON api_keys(user_id);
CREATE INDEX IF NOT EXISTS idx_api_keys_hash ON api_keys(key_hash);
CREATE INDEX IF NOT EXISTS idx_api_keys_active ON api_keys(is_active);
CREATE INDEX IF NOT EXISTS idx_system_config_key ON system_config(config_key);
CREATE INDEX IF NOT EXISTS idx_cache_statistics_name ON cache_statistics(cache_name);
CREATE INDEX IF NOT EXISTS idx_storage_backends_type ON storage_backends(backend_type);
CREATE INDEX IF NOT EXISTS idx_storage_backends_active ON storage_backends(is_active);
CREATE INDEX IF NOT EXISTS idx_file_metadata_path ON file_metadata(file_path);
CREATE INDEX IF NOT EXISTS idx_file_metadata_backend ON file_metadata(storage_backend_id);

-- 为新表添加触发器
CREATE TRIGGER update_roles_updated_at BEFORE UPDATE ON roles
    FOR EACH ROW EXECUTE FUNCTION update_updated_at_column();

CREATE TRIGGER update_system_config_updated_at BEFORE UPDATE ON system_config
    FOR EACH ROW EXECUTE FUNCTION update_updated_at_column();

CREATE TRIGGER update_storage_backends_updated_at BEFORE UPDATE ON storage_backends
    FOR EACH ROW EXECUTE FUNCTION update_updated_at_column();

CREATE TRIGGER update_file_metadata_updated_at BEFORE UPDATE ON file_metadata
    FOR EACH ROW EXECUTE FUNCTION update_updated_at_column();

-- 插入默认角色
INSERT INTO roles (name, description, permissions) VALUES
    ('admin', '系统管理员', '{"all": true}'),
    ('user', '普通用户', '{"read": true, "write": true}'),
    ('viewer', '只读用户', '{"read": true}')
ON CONFLICT (name) DO NOTHING;

-- 插入默认系统配置
INSERT INTO system_config (config_key, config_value, description) VALUES
    ('max_file_size', '{"value": 104857600}', '最大文件大小（字节）'),
    ('allowed_file_types', '{"value": ["jpg", "png", "pdf", "txt", "json"]}', '允许的文件类型'),
    ('cache_ttl', '{"value": 3600}', '缓存生存时间（秒）'),
    ('max_concurrent_requests', '{"value": 100}', '最大并发请求数')
ON CONFLICT (config_key) DO NOTHING;

-- 插入默认存储后端
INSERT INTO storage_backends (name, backend_type, configuration) VALUES
    ('local_default', 'local', '{"base_path": "/tmp/c19_ai_storage"}'),
    ('s3_default', 's3', '{"bucket": "c19-ai-storage", "region": "us-east-1"}')
ON CONFLICT (name) DO NOTHING;