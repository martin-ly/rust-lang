# 🚀 Rust项目CI/CD设置指南

**创建时间**: 2025年9月25日 14:00  
**版本**: v1.0  
**适用对象**: Rust开发者  

---

## 📋 概述

本文档介绍了如何为Rust项目设置持续集成和持续部署(CI/CD)流程，包括GitHub Actions、GitLab CI、Jenkins等平台的配置。

---

## 🎯 CI/CD目标

### 主要目标

- **自动化测试**: 自动运行所有测试
- **代码质量检查**: 自动检查代码质量
- **自动构建**: 自动构建项目
- **自动部署**: 自动部署到生产环境

### 具体目标

- 提高开发效率
- 减少人为错误
- 确保代码质量
- 快速发现问题

---

## 🔧 GitHub Actions配置

### 基础工作流

```yaml
# .github/workflows/ci.yml
name: CI

on:
  push:
    branches: [ main, develop ]
  pull_request:
    branches: [ main ]

env:
  CARGO_TERM_COLOR: always

jobs:
  test:
    name: Test
    runs-on: ubuntu-latest
    strategy:
      matrix:
        rust: [stable, beta, nightly]
    
    steps:
    - uses: actions/checkout@v3
    
    - name: Install Rust
      uses: dtolnay/rust-toolchain@stable
      with:
        components: rustfmt, clippy
    
    - name: Cache cargo registry
      uses: actions/cache@v3
      with:
        path: |
          ~/.cargo/registry
          ~/.cargo/git
          target
        key: ${{ runner.os }}-cargo-${{ hashFiles('**/Cargo.lock') }}
    
    - name: Check formatting
      run: cargo fmt --all -- --check
    
    - name: Run clippy
      run: cargo clippy --all-targets --all-features -- -D warnings
    
    - name: Run tests
      run: cargo test --all-features
    
    - name: Run tests (no default features)
      run: cargo test --no-default-features
```

### 高级工作流

```yaml
# .github/workflows/advanced-ci.yml
name: Advanced CI

on:
  push:
    branches: [ main ]
  pull_request:
    branches: [ main ]
  schedule:
    - cron: '0 0 * * *'  # 每日运行

env:
  CARGO_TERM_COLOR: always

jobs:
  test:
    name: Test
    runs-on: ubuntu-latest
    strategy:
      matrix:
        rust: [stable, beta, nightly]
        os: [ubuntu-latest, windows-latest, macos-latest]
    
    steps:
    - uses: actions/checkout@v3
    
    - name: Install Rust
      uses: dtolnay/rust-toolchain@stable
      with:
        components: rustfmt, clippy
    
    - name: Cache cargo registry
      uses: actions/cache@v3
      with:
        path: |
          ~/.cargo/registry
          ~/.cargo/git
          target
        key: ${{ runner.os }}-cargo-${{ hashFiles('**/Cargo.lock') }}
    
    - name: Check formatting
      run: cargo fmt --all -- --check
    
    - name: Run clippy
      run: cargo clippy --all-targets --all-features -- -D warnings
    
    - name: Run tests
      run: cargo test --all-features
    
    - name: Run tests (no default features)
      run: cargo test --no-default-features
    
    - name: Generate test coverage
      run: |
        cargo install cargo-tarpaulin
        cargo tarpaulin --out Xml
      if: runner.os == 'Linux'
    
    - name: Upload coverage to Codecov
      uses: codecov/codecov-action@v3
      with:
        file: ./coverage.xml
        if: runner.os == 'Linux'

  security:
    name: Security Audit
    runs-on: ubuntu-latest
    
    steps:
    - uses: actions/checkout@v3
    
    - name: Install Rust
      uses: dtolnay/rust-toolchain@stable
    
    - name: Install cargo-audit
      run: cargo install cargo-audit
    
    - name: Run security audit
      run: cargo audit

  benchmark:
    name: Benchmark
    runs-on: ubuntu-latest
    
    steps:
    - uses: actions/checkout@v3
    
    - name: Install Rust
      uses: dtolnay/rust-toolchain@stable
    
    - name: Run benchmarks
      run: cargo bench --features benchmark
      if: github.event_name == 'push' && github.ref == 'refs/heads/main'
```

### 部署工作流

```yaml
# .github/workflows/deploy.yml
name: Deploy

on:
  push:
    tags:
      - 'v*'
  workflow_dispatch:

jobs:
  deploy:
    name: Deploy
    runs-on: ubuntu-latest
    
    steps:
    - uses: actions/checkout@v3
    
    - name: Install Rust
      uses: dtolnay/rust-toolchain@stable
    
    - name: Build for release
      run: cargo build --release
    
    - name: Create release archive
      run: |
        tar -czf release.tar.gz target/release/
    
    - name: Create GitHub Release
      uses: actions/create-release@v1
      env:
        GITHUB_TOKEN: ${{ secrets.GITHUB_TOKEN }}
      with:
        tag_name: ${{ github.ref }}
        release_name: Release ${{ github.ref }}
        body: |
          Changes in this Release
          - Bug fixes
          - Performance improvements
          - New features
        draft: false
        prerelease: false
    
    - name: Upload Release Asset
      uses: actions/upload-release-asset@v1
      env:
        GITHUB_TOKEN: ${{ secrets.GITHUB_TOKEN }}
      with:
        upload_url: ${{ steps.create_release.outputs.upload_url }}
        asset_path: ./release.tar.gz
        asset_name: release.tar.gz
        asset_content_type: application/gzip
```

---

## 🐳 Docker集成

### Dockerfile

```dockerfile
# Dockerfile
FROM rust:1.70-slim as builder

WORKDIR /app

# 复制依赖文件
COPY Cargo.toml Cargo.lock ./

# 创建虚拟项目来缓存依赖
RUN mkdir src && echo "fn main() {}" > src/main.rs
RUN cargo build --release
RUN rm -rf src

# 复制源代码
COPY src ./src
COPY examples ./examples
COPY tests ./tests

# 构建项目
RUN cargo build --release

# 运行时镜像
FROM debian:bookworm-slim

RUN apt-get update && apt-get install -y \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /app

# 从构建阶段复制二进制文件
COPY --from=builder /app/target/release/my-app /app/my-app

# 设置环境变量
ENV RUST_LOG=info

# 暴露端口
EXPOSE 8080

# 运行应用
CMD ["./my-app"]
```

### Docker Compose

```yaml
# docker-compose.yml
version: '3.8'

services:
  app:
    build: .
    ports:
      - "8080:8080"
    environment:
      - RUST_LOG=info
    volumes:
      - ./logs:/app/logs
    
  redis:
    image: redis:7-alpine
    ports:
      - "6379:6379"
    
  postgres:
    image: postgres:15-alpine
    environment:
      POSTGRES_DB: myapp
      POSTGRES_USER: myapp
      POSTGRES_PASSWORD: myapp
    ports:
      - "5432:5432"
    volumes:
      - postgres_data:/var/lib/postgresql/data

volumes:
  postgres_data:
```

---

## 📊 代码质量检查

### Clippy配置

```toml
# clippy.toml
# 允许的警告
allow = [
    "clippy::too_many_arguments",
    "clippy::needless_pass_by_value",
]

# 禁止的警告
deny = [
    "clippy::all",
    "clippy::pedantic",
    "clippy::nursery",
    "clippy::cargo",
]

# 警告级别
warn = [
    "clippy::perf",
    "clippy::style",
    "clippy::correctness",
]
```

### Rustfmt配置

```toml
# rustfmt.toml
# 基本格式
edition = "2021"
max_width = 100
tab_spaces = 4
newline_style = "Unix"

# 导入排序
imports_granularity = "Crate"
group_imports = "StdExternalCrate"

# 函数格式
fn_args_layout = "Tall"
brace_style = "SameLineWhere"

# 其他设置
use_field_init_shorthand = true
use_try_shorthand = true
```

---

## 🔍 测试策略

### 单元测试

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_functionality() {
        assert!(true);
    }

    #[test]
    fn test_with_result() -> Result<(), String> {
        Ok(())
    }

    #[test]
    #[ignore]
    fn test_expensive_operation() {
        // 只在需要时运行
    }
}
```

### 集成测试

```rust
// tests/integration_test.rs
use my_crate::{Calculator, Database};

#[test]
fn test_calculator_integration() {
    let calc = Calculator::new();
    let result = calc.evaluate("2 + 3 * 4");
    assert_eq!(result, Ok(14));
}
```

### 基准测试

```rust
// benches/benchmark.rs
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use my_crate::fast_function;

fn bench_fast_function(c: &mut Criterion) {
    c.bench_function("fast_function", |b| {
        b.iter(|| fast_function(black_box(1000)))
    });
}

criterion_group!(benches, bench_fast_function);
criterion_main!(benches);
```

---

## 📈 性能监控

### 性能基准

```rust
// benches/performance.rs
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use std::time::Duration;

fn bench_algorithm(c: &mut Criterion) {
    let mut group = c.benchmark_group("algorithm");
    group.measurement_time(Duration::from_secs(10));
    
    group.bench_function("fast", |b| {
        b.iter(|| fast_algorithm(black_box(1000)))
    });
    
    group.bench_function("slow", |b| {
        b.iter(|| slow_algorithm(black_box(1000)))
    });
    
    group.finish();
}

criterion_group!(benches, bench_algorithm);
criterion_main!(benches);
```

### 内存分析

```rust
// 使用valgrind进行内存分析
// 安装valgrind: sudo apt-get install valgrind
// 运行: valgrind --leak-check=full ./target/release/my-app
```

---

## 🚀 部署策略

### 蓝绿部署

```yaml
# .github/workflows/blue-green-deploy.yml
name: Blue-Green Deploy

on:
  push:
    branches: [ main ]

jobs:
  deploy:
    name: Blue-Green Deploy
    runs-on: ubuntu-latest
    
    steps:
    - uses: actions/checkout@v3
    
    - name: Deploy to staging
      run: |
        # 部署到staging环境
        kubectl apply -f k8s/staging/
    
    - name: Run integration tests
      run: |
        # 运行集成测试
        cargo test --test integration
    
    - name: Deploy to production
      run: |
        # 部署到生产环境
        kubectl apply -f k8s/production/
    
    - name: Health check
      run: |
        # 健康检查
        curl -f http://my-app.example.com/health
```

### 滚动更新

```yaml
# k8s/deployment.yml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: my-app
spec:
  replicas: 3
  strategy:
    type: RollingUpdate
    rollingUpdate:
      maxUnavailable: 1
      maxSurge: 1
  selector:
    matchLabels:
      app: my-app
  template:
    metadata:
      labels:
        app: my-app
    spec:
      containers:
      - name: my-app
        image: my-app:latest
        ports:
        - containerPort: 8080
        livenessProbe:
          httpGet:
            path: /health
            port: 8080
          initialDelaySeconds: 30
          periodSeconds: 10
        readinessProbe:
          httpGet:
            path: /ready
            port: 8080
          initialDelaySeconds: 5
          periodSeconds: 5
```

---

## 📞 最佳实践

### CI/CD最佳实践

1. **快速反馈**: 保持CI流程快速
2. **并行执行**: 并行运行测试
3. **缓存优化**: 有效使用缓存
4. **安全扫描**: 定期进行安全扫描
5. **监控告警**: 设置监控和告警

### 代码质量最佳实践

1. **自动化检查**: 自动化代码质量检查
2. **测试覆盖**: 保持高测试覆盖率
3. **性能监控**: 监控性能指标
4. **安全审计**: 定期进行安全审计
5. **文档更新**: 保持文档更新

---

**设置状态**: 🔄 持续更新中  
**最后更新**: 2025年9月25日 14:00  
**适用版本**: Rust 1.70+  

---

*本CI/CD设置指南提供了完整的自动化流程配置，帮助您建立高效的开发工作流。如有任何问题或建议，欢迎反馈。*
