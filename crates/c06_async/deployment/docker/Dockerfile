# Rust 1.90 异步特性多阶段构建 Dockerfile
# 支持开发、测试和生产环境

# 阶段1: 构建环境
FROM rust:1.90-alpine AS builder

# 安装必要的系统依赖
RUN apk add --no-cache \
    musl-dev \
    openssl-dev \
    pkgconfig \
    libc-dev \
    linux-headers

# 设置工作目录
WORKDIR /app

# 复制 Cargo 文件
COPY Cargo.toml Cargo.lock ./
COPY crates/c06_async/Cargo.toml ./crates/c06_async/

# 创建虚拟项目以缓存依赖
RUN mkdir -p crates/c06_async/src && \
    echo "fn main() {}" > crates/c06_async/src/main.rs && \
    cargo build --release --manifest-path crates/c06_async/Cargo.toml && \
    rm -rf crates/c06_async/src

# 复制源代码
COPY crates/c06_async/src ./crates/c06_async/src/
COPY crates/c06_async/examples ./crates/c06_async/examples/
COPY crates/c06_async/tests ./crates/c06_async/tests/
COPY crates/c06_async/benches ./crates/c06_async/benches/

# 构建应用
RUN cargo build --release --manifest-path crates/c06_async/Cargo.toml

# 阶段2: 测试环境
FROM builder AS tester

# 安装测试依赖
RUN apk add --no-cache \
    curl \
    jq

# 运行测试
RUN cargo test --manifest-path crates/c06_async/Cargo.toml

# 运行集成测试
RUN cargo test --test integration_test_suite --manifest-path crates/c06_async/Cargo.toml

# 运行基准测试
RUN cargo bench --manifest-path crates/c06_async/Cargo.toml

# 阶段3: 生产环境
FROM alpine:3.18 AS runtime

# 安装运行时依赖
RUN apk add --no-cache \
    ca-certificates \
    tzdata \
    libgcc

# 创建非 root 用户
RUN addgroup -g 1000 rust && \
    adduser -D -s /bin/sh -u 1000 -G rust rust

# 设置工作目录
WORKDIR /app

# 从构建阶段复制二进制文件
COPY --from=builder /app/crates/c06_async/target/release/c06_async /app/c06_async
COPY --from=builder /app/crates/c06_async/target/release/examples/ /app/examples/

# 设置权限
RUN chown -R rust:rust /app

# 切换到非 root 用户
USER rust

# 健康检查
HEALTHCHECK --interval=30s --timeout=10s --start-period=5s --retries=3 \
    CMD curl -f http://localhost:8080/health || exit 1

# 暴露端口
EXPOSE 8080

# 设置环境变量
ENV RUST_LOG=info
ENV RUST_BACKTRACE=1

# 启动命令
CMD ["./c06_async"]

# 阶段4: 开发环境
FROM rust:1.90-alpine AS development

# 安装开发工具
RUN apk add --no-cache \
    musl-dev \
    openssl-dev \
    pkgconfig \
    libc-dev \
    linux-headers \
    git \
    vim \
    curl \
    jq \
    htop

# 安装有用的 Rust 工具
RUN cargo install \
    cargo-watch \
    cargo-expand \
    cargo-udeps \
    cargo-audit \
    cargo-deny \
    cargo-criterion

# 设置工作目录
WORKDIR /app

# 复制项目文件
COPY . .

# 构建项目
RUN cargo build

# 暴露端口
EXPOSE 8080 3000

# 开发模式启动命令
CMD ["cargo", "watch", "-x", "run"]

# 阶段5: 基准测试环境
FROM rust:1.90-alpine AS benchmark

# 安装基准测试依赖
RUN apk add --no-cache \
    musl-dev \
    openssl-dev \
    pkgconfig \
    libc-dev \
    linux-headers \
    python3 \
    py3-pip

# 安装 Python 基准测试工具
RUN pip3 install \
    matplotlib \
    numpy \
    pandas \
    seaborn

# 安装 Rust 基准测试工具
RUN cargo install \
    cargo-criterion \
    cargo-bench

# 设置工作目录
WORKDIR /app

# 复制项目文件
COPY . .

# 构建项目
RUN cargo build --release

# 运行基准测试
RUN cargo bench --manifest-path crates/c06_async/Cargo.toml

# 生成基准测试报告
RUN cargo criterion --manifest-path crates/c06_async/Cargo.toml

# 启动基准测试服务器
CMD ["cargo", "bench", "--manifest-path", "crates/c06_async/Cargo.toml"]
