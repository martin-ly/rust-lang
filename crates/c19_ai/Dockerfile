# 多阶段构建Dockerfile for c19_ai
# 第一阶段：构建环境
FROM rust:1.75-slim as builder

# 安装系统依赖
RUN apt-get update && apt-get install -y \
    pkg-config \
    libssl-dev \
    libpq-dev \
    libsqlite3-dev \
    libmysqlclient-dev \
    build-essential \
    && rm -rf /var/lib/apt/lists/*

# 设置工作目录
WORKDIR /app

# 复制Cargo文件
COPY Cargo.toml Cargo.lock ./

# 复制源代码
COPY src ./src
COPY examples ./examples
COPY scripts ./scripts

# 构建应用
RUN cargo build --release --features "api-server"

# 第二阶段：运行环境
FROM debian:bookworm-slim

# 安装运行时依赖
RUN apt-get update && apt-get install -y \
    ca-certificates \
    libssl3 \
    libpq5 \
    libsqlite3-0 \
    libmysqlclient21 \
    && rm -rf /var/lib/apt/lists/*

# 创建非root用户
RUN groupadd -r c19ai && useradd -r -g c19ai c19ai

# 设置工作目录
WORKDIR /app

# 从构建阶段复制二进制文件
COPY --from=builder /app/target/release/c19_ai /app/c19_ai

# 复制配置文件
COPY --from=builder /app/scripts/init.sql /app/scripts/init.sql

# 创建数据目录
RUN mkdir -p /app/data /app/logs /app/config && \
    chown -R c19ai:c19ai /app

# 切换到非root用户
USER c19ai

# 暴露端口
EXPOSE 8080 8081

# 设置环境变量
ENV RUST_LOG=info
ENV RUST_BACKTRACE=1
ENV C19_AI_CONFIG_PATH=/app/config
ENV C19_AI_DATA_PATH=/app/data
ENV C19_AI_LOG_PATH=/app/logs

# 健康检查
HEALTHCHECK --interval=30s --timeout=10s --start-period=5s --retries=3 \
    CMD curl -f http://localhost:8080/health || exit 1

# 启动命令
CMD ["./c19_ai"]