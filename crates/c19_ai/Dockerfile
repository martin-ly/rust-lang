# 多阶段构建 - 构建阶段
FROM rust:1.90-slim as builder

# 安装系统依赖
RUN apt-get update && apt-get install -y \
    pkg-config \
    libssl-dev \
    libclang-dev \
    cmake \
    build-essential \
    && rm -rf /var/lib/apt/lists/*

# 设置工作目录
WORKDIR /app

# 复制Cargo文件
COPY Cargo.toml Cargo.lock ./

# 创建虚拟main.rs来缓存依赖
RUN mkdir src && echo "fn main() {}" > src/main.rs

# 构建依赖（利用Docker缓存）
RUN cargo build --release --features basic-ai
RUN rm -rf src

# 复制源代码
COPY src ./src
COPY examples ./examples
COPY benches ./benches

# 构建应用
RUN cargo build --release --features basic-ai

# 运行阶段
FROM debian:bookworm-slim

# 安装运行时依赖
RUN apt-get update && apt-get install -y \
    ca-certificates \
    libssl3 \
    && rm -rf /var/lib/apt/lists/*

# 创建非root用户
RUN groupadd -r appuser && useradd -r -g appuser appuser

# 设置工作目录
WORKDIR /app

# 从构建阶段复制二进制文件
COPY --from=builder /app/target/release/c19_ai /app/c19_ai

# 复制配置文件
COPY docs ./docs
COPY README.md ./

# 更改所有权
RUN chown -R appuser:appuser /app

# 切换到非root用户
USER appuser

# 暴露端口（如果需要）
EXPOSE 8080

# 健康检查
HEALTHCHECK --interval=30s --timeout=3s --start-period=5s --retries=3 \
    CMD curl -f http://localhost:8080/health || exit 1

# 设置环境变量
ENV RUST_LOG=info
ENV RUST_BACKTRACE=1

# 运行应用
CMD ["./c19_ai"]
