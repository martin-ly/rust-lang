# CI/CD 集成 (CI/CD Integration)

## 📋 目录

- [CI/CD 集成 (CI/CD Integration)](#cicd-集成-cicd-integration)
  - [📋 目录](#-目录)
  - [核心命题](#核心命题)
  - [GitHub Actions 工作流](#github-actions-工作流)
    - [基础 Wasm 构建](#基础-wasm-构建)
    - [多语言构建](#多语言构建)
  - [优化与压缩](#优化与压缩)
    - [自动优化流水线](#自动优化流水线)
  - [质量门控](#质量门控)
    - [验证与 Lint](#验证与-lint)
    - [测试覆盖率](#测试覆盖率)
  - [性能回归检测](#性能回归检测)
    - [自动基准测试](#自动基准测试)
  - [多环境部署](#多环境部署)
    - [Staging 与 Production](#staging-与-production)
  - [Docker 集成](#docker-集成)
    - [构建容器](#构建容器)
  - [GitLab CI/CD](#gitlab-cicd)
  - [Jenkins Pipeline](#jenkins-pipeline)
  - [版本管理与发布](#版本管理与发布)
    - [语义化版本](#语义化版本)
    - [npm 包发布](#npm-包发布)
  - [监控与告警](#监控与告警)
    - [部署健康检查](#部署健康检查)
  - [批判性分析](#批判性分析)
    - [CI/CD 复杂度](#cicd-复杂度)
    - [构建时间分析](#构建时间分析)
  - [最佳实践](#最佳实践)
    - [缓存策略](#缓存策略)
    - [增量构建](#增量构建)
    - [并行化](#并行化)
  - [参考文献](#参考文献)
  - [相关文档](#相关文档)

## 核心命题

**自动化投资回报**：
\[
\text{ROI}_{\text{CI/CD}} = \frac{\text{Time}_{\text{saved}} + \text{Bugs}\_{\text{prevented}}}{\text{Setup_cost} + \text{Maintenance_cost}}
\]

**构建可靠性定理**：
\[
\text{Reliability}_{\text{system}} = \prod_{i=1}^n \text{Reliability}\_{\text{component}\_i}
\]

**部署频率与质量**：
\[
\text{Quality} \propto \sqrt{\text{Deploy_frequency}} \quad (\text{DevOps 研究})
\]

---

## GitHub Actions 工作流

### 基础 Wasm 构建

**.github/workflows/build.yml**：

```yaml
name: Build WebAssembly

on:
  push:
    branches: [main, develop]
  pull_request:
    branches: [main]

jobs:
  build:
    runs-on: ${{ matrix.os }}
    strategy:
      matrix:
        os: [ubuntu-latest, macos-latest, windows-latest]
        toolchain: [stable, nightly]

    steps:
      - name: Checkout code
        uses: actions/checkout@v3

      - name: Install Rust
        uses: actions-rs/toolchain@v1
        with:
          toolchain: ${{ matrix.toolchain }}
          target: wasm32-wasi
          override: true

      - name: Cache cargo
        uses: actions/cache@v3
        with:
          path: |
            ~/.cargo/bin/
            ~/.cargo/registry/index/
            ~/.cargo/registry/cache/
            ~/.cargo/git/db/
            target/
          key: ${{ runner.os }}-cargo-${{ hashFiles('**/Cargo.lock') }}

      - name: Build
        run: cargo build --target wasm32-wasi --release

      - name: Run tests
        run: cargo test --target wasm32-wasi

      - name: Upload artifact
        uses: actions/upload-artifact@v3
        with:
          name: wasm-${{ matrix.os }}-${{ matrix.toolchain }}
          path: target/wasm32-wasi/release/*.wasm
```

### 多语言构建

**Emscripten + Rust 混合**：

```yaml
jobs:
  build-emscripten:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3

      - name: Setup Emscripten
        uses: mymindstorm/setup-emsdk@v12
        with:
          version: "latest"

      - name: Build C++ module
        run: |
          emcc src/main.cpp -o dist/module.js \
            -s WASM=1 -s MODULARIZE=1 -O3

      - name: Upload
        uses: actions/upload-artifact@v3
        with:
          name: emscripten-build
          path: dist/

  build-rust:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3

      - name: Install wasm-pack
        run: curl https://rustwasm.github.io/wasm-pack/installer/init.sh -sSf | sh

      - name: Build Rust module
        run: wasm-pack build --target web --release

      - name: Upload
        uses: actions/upload-artifact@v3
        with:
          name: rust-build
          path: pkg/
```

---

## 优化与压缩

### 自动优化流水线

```yaml
jobs:
  optimize:
    runs-on: ubuntu-latest
    needs: build
    steps:
      - name: Download artifact
        uses: actions/download-artifact@v3
        with:
          name: wasm-build

      - name: Install wasm-opt
        run: |
          wget https://github.com/WebAssembly/binaryen/releases/download/version_110/binaryen-version_110-x86_64-linux.tar.gz
          tar xzf binaryen-*.tar.gz
          echo "$PWD/binaryen-*/bin" >> $GITHUB_PATH

      - name: Optimize Wasm
        run: |
          wasm-opt -Oz module.wasm -o module.opt.wasm \
            --strip-debug --strip-producers \
            --enable-simd --enable-bulk-memory

      - name: Compare sizes
        run: |
          echo "Original: $(stat -f%z module.wasm) bytes"
          echo "Optimized: $(stat -f%z module.opt.wasm) bytes"

      - name: Compress with Brotli
        run: |
          brotli -9 module.opt.wasm -o module.opt.wasm.br
          echo "Compressed: $(stat -f%z module.opt.wasm.br) bytes"

      - name: Upload optimized
        uses: actions/upload-artifact@v3
        with:
          name: wasm-optimized
          path: |
            module.opt.wasm
            module.opt.wasm.br
```

---

## 质量门控

### 验证与 Lint

```yaml
jobs:
  quality-gates:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3

      - name: Install tools
        run: |
          cargo install wasm-pack
          npm install -g wasm-check

      - name: Validate Wasm
        run: |
          wasm-validate target/wasm32-wasi/release/*.wasm

      - name: Rust lint
        run: |
          cargo clippy --target wasm32-wasi -- -D warnings
          cargo fmt -- --check

      - name: Size check
        run: |
          SIZE=$(stat -f%z target/wasm32-wasi/release/module.wasm)
          if [ $SIZE -gt 1048576 ]; then
            echo "Error: Wasm module exceeds 1MB limit"
            exit 1
          fi

      - name: Security scan
        run: cargo audit
```

### 测试覆盖率

```yaml
jobs:
  coverage:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3

      - name: Install tarpaulin
        run: cargo install cargo-tarpaulin

      - name: Generate coverage
        run: |
          cargo tarpaulin --target wasm32-wasi \
            --out Xml --out Html --output-dir coverage

      - name: Upload coverage to Codecov
        uses: codecov/codecov-action@v3
        with:
          files: ./coverage/cobertura.xml
          flags: unittests
          fail_ci_if_error: true

      - name: Enforce minimum coverage
        run: |
          COVERAGE=$(grep -oP 'line-rate="\K[0-9.]+' coverage/cobertura.xml | head -1)
          if (( $(echo "$COVERAGE < 0.8" | bc -l) )); then
            echo "Coverage $COVERAGE is below 80%"
            exit 1
          fi
```

---

## 性能回归检测

### 自动基准测试

```yaml
jobs:
  benchmark:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
        with:
          fetch-depth: 0 # 获取完整历史

      - name: Run benchmarks
        run: cargo bench --target wasm32-wasi -- --save-baseline current

      - name: Compare with main
        run: |
          git checkout main
          cargo bench --target wasm32-wasi -- --save-baseline main
          git checkout -

          # 比较结果
          cargo bench -- --baseline main --load-baseline current

      - name: Comment PR
        uses: actions/github-script@v6
        with:
          script: |
            const fs = require('fs');
            const results = fs.readFileSync('benchmark_results.txt', 'utf8');

            github.rest.issues.createComment({
              issue_number: context.issue.number,
              owner: context.repo.owner,
              repo: context.repo.repo,
              body: `## Benchmark Results\n\n\`\`\`\n${results}\n\`\`\``
            });

      - name: Fail on regression
        run: |
          if grep -q "regressed" benchmark_results.txt; then
            echo "Performance regression detected!"
            exit 1
          fi
```

---

## 多环境部署

### Staging 与 Production

```yaml
jobs:
  deploy-staging:
    runs-on: ubuntu-latest
    if: github.ref == 'refs/heads/develop'
    steps:
      - uses: actions/checkout@v3

      - name: Build for staging
        run: |
          wasm-pack build --release --target web
          cp pkg/* dist/staging/

      - name: Deploy to staging
        uses: aws-actions/configure-aws-credentials@v2
        with:
          aws-access-key-id: ${{ secrets.AWS_ACCESS_KEY_ID }}
          aws-secret-access-key: ${{ secrets.AWS_SECRET_ACCESS_KEY }}
          aws-region: us-east-1

      - name: Upload to S3
        run: |
          aws s3 sync dist/staging/ s3://my-wasm-staging/ \
            --cache-control "max-age=3600" \
            --content-encoding br

      - name: Invalidate CloudFront
        run: |
          aws cloudfront create-invalidation \
            --distribution-id ${{ secrets.STAGING_DISTRIBUTION_ID }} \
            --paths "/*"

  deploy-production:
    runs-on: ubuntu-latest
    if: github.ref == 'refs/heads/main'
    needs: [build, quality-gates, benchmark]
    environment:
      name: production
      url: https://my-app.com
    steps:
      - uses: actions/checkout@v3

      - name: Build for production
        run: |
          wasm-pack build --release --target web
          wasm-opt pkg/module_bg.wasm -Oz -o pkg/module_bg.wasm

      - name: Deploy to production
        run: |
          aws s3 sync pkg/ s3://my-wasm-prod/ \
            --cache-control "max-age=31536000,immutable" \
            --content-encoding br
```

---

## Docker 集成

### 构建容器

**Dockerfile**：

```dockerfile
# 多阶段构建
FROM rust:1.70 as builder

# 安装 wasm 工具链
RUN rustup target add wasm32-wasi
RUN cargo install wasm-pack wasm-bindgen-cli

WORKDIR /app
COPY Cargo.toml Cargo.lock ./
COPY src ./src

# 构建 Wasm
RUN cargo build --target wasm32-wasi --release

# 优化阶段
FROM debian:bullseye-slim as optimizer
RUN apt-get update && apt-get install -y binaryen

COPY --from=builder /app/target/wasm32-wasi/release/*.wasm /wasm/
RUN wasm-opt -Oz /wasm/module.wasm -o /wasm/module.opt.wasm

# 最终镜像（仅运行时）
FROM wasmedge/wasmedge:latest

COPY --from=optimizer /wasm/module.opt.wasm /app/
EXPOSE 8080

CMD ["wasmedge", "--reactor", "/app/module.opt.wasm"]
```

**CI 集成**：

```yaml
jobs:
  docker:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3

      - name: Set up Docker Buildx
        uses: docker/setup-buildx-action@v2

      - name: Login to DockerHub
        uses: docker/login-action@v2
        with:
          username: ${{ secrets.DOCKERHUB_USERNAME }}
          password: ${{ secrets.DOCKERHUB_TOKEN }}

      - name: Build and push
        uses: docker/build-push-action@v4
        with:
          context: .
          push: true
          tags: myorg/wasm-app:${{ github.sha }}
          cache-from: type=registry,ref=myorg/wasm-app:buildcache
          cache-to: type=registry,ref=myorg/wasm-app:buildcache,mode=max
```

---

## GitLab CI/CD

**.gitlab-ci.yml**：

```yaml
stages:
  - build
  - test
  - optimize
  - deploy

variables:
  CARGO_HOME: ${CI_PROJECT_DIR}/.cargo

build:wasm:
  stage: build
  image: rust:1.70
  before_script:
    - rustup target add wasm32-wasi
  script:
    - cargo build --target wasm32-wasi --release
  artifacts:
    paths:
      - target/wasm32-wasi/release/*.wasm
    expire_in: 1 week
  cache:
    key: ${CI_COMMIT_REF_SLUG}
    paths:
      - .cargo/
      - target/

test:unit:
  stage: test
  image: rust:1.70
  script:
    - rustup target add wasm32-wasi
    - cargo test --target wasm32-wasi
  coverage: '/^\d+\.\d+% coverage/'

test:integration:
  stage: test
  image: node:18
  needs: [build:wasm]
  script:
    - npm ci
    - npm run test:integration
  artifacts:
    reports:
      junit: junit.xml

optimize:wasm:
  stage: optimize
  image: debian:bullseye
  needs: [build:wasm]
  before_script:
    - apt-get update && apt-get install -y wget
    - wget https://github.com/WebAssembly/binaryen/releases/download/version_110/binaryen-version_110-x86_64-linux.tar.gz
    - tar xzf binaryen-*.tar.gz
    - export PATH="$PWD/binaryen-*/bin:$PATH"
  script:
    - wasm-opt -Oz target/wasm32-wasi/release/*.wasm -o optimized.wasm
    - brotli -9 optimized.wasm
  artifacts:
    paths:
      - optimized.wasm
      - optimized.wasm.br

deploy:staging:
  stage: deploy
  only:
    - develop
  script:
    - aws s3 sync . s3://staging-bucket/
  environment:
    name: staging
    url: https://staging.myapp.com

deploy:production:
  stage: deploy
  only:
    - main
  when: manual
  script:
    - aws s3 sync . s3://prod-bucket/
  environment:
    name: production
    url: https://myapp.com
```

---

## Jenkins Pipeline

**Jenkinsfile**：

```groovy
pipeline {
    agent any

    environment {
        CARGO_HOME = "${WORKSPACE}/.cargo"
    }

    stages {
        stage('Setup') {
            steps {
                sh 'rustup target add wasm32-wasi'
                sh 'cargo install wasm-pack || true'
            }
        }

        stage('Build') {
            parallel {
                stage('Build Wasm') {
                    steps {
                        sh 'cargo build --target wasm32-wasi --release'
                    }
                }
                stage('Build npm package') {
                    steps {
                        sh 'wasm-pack build --release --target web'
                    }
                }
            }
        }

        stage('Test') {
            parallel {
                stage('Unit Tests') {
                    steps {
                        sh 'cargo test --target wasm32-wasi'
                    }
                }
                stage('Integration Tests') {
                    steps {
                        sh 'npm ci && npm test'
                    }
                }
            }
        }

        stage('Quality Gates') {
            steps {
                script {
                    def size = sh(returnStdout: true, script: 'stat -c%s target/wasm32-wasi/release/module.wasm').trim().toInteger()
                    if (size > 1048576) {
                        error("Wasm size ${size} exceeds 1MB limit")
                    }
                }
            }
        }

        stage('Deploy') {
            when {
                branch 'main'
            }
            steps {
                sh 'aws s3 sync pkg/ s3://my-bucket/'
            }
        }
    }

    post {
        always {
            archiveArtifacts artifacts: 'target/wasm32-wasi/release/*.wasm', fingerprint: true
            junit 'target/test-results/*.xml'
        }
        failure {
            mail to: 'team@example.com',
                 subject: "Build Failed: ${env.JOB_NAME} #${env.BUILD_NUMBER}",
                 body: "Check console output at ${env.BUILD_URL}"
        }
    }
}
```

---

## 版本管理与发布

### 语义化版本

**自动版本号**：

```yaml
jobs:
  release:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
        with:
          fetch-depth: 0

      - name: Determine version
        id: version
        run: |
          # 基于 git tag 确定版本
          if git describe --tags --exact-match 2>/dev/null; then
            VERSION=$(git describe --tags)
          else
            VERSION="0.0.0-dev+$(git rev-parse --short HEAD)"
          fi
          echo "VERSION=$VERSION" >> $GITHUB_OUTPUT

      - name: Update Cargo.toml
        run: |
          sed -i "s/^version = .*/version = \"${{ steps.version.outputs.VERSION }}\"/" Cargo.toml

      - name: Build release
        run: cargo build --target wasm32-wasi --release

      - name: Create GitHub Release
        uses: softprops/action-gh-release@v1
        if: startsWith(github.ref, 'refs/tags/')
        with:
          files: target/wasm32-wasi/release/*.wasm
```

### npm 包发布

```yaml
jobs:
  publish-npm:
    runs-on: ubuntu-latest
    if: startsWith(github.ref, 'refs/tags/v')
    steps:
      - uses: actions/checkout@v3

      - name: Setup Node.js
        uses: actions/setup-node@v3
        with:
          node-version: "18"
          registry-url: "https://registry.npmjs.org"

      - name: Build package
        run: wasm-pack build --release --target web

      - name: Publish to npm
        run: |
          cd pkg
          npm publish
        env:
          NODE_AUTH_TOKEN: ${{ secrets.NPM_TOKEN }}
```

---

## 监控与告警

### 部署健康检查

```yaml
jobs:
  healthcheck:
    runs-on: ubuntu-latest
    needs: deploy-production
    steps:
      - name: Wait for deployment
        run: sleep 60

      - name: Smoke test
        run: |
          RESPONSE=$(curl -s -o /dev/null -w "%{http_code}" https://myapp.com/health)
          if [ $RESPONSE -ne 200 ]; then
            echo "Health check failed: HTTP $RESPONSE"
            exit 1
          fi

      - name: Functional test
        run: |
          node << EOF
          (async () => {
            const module = await WebAssembly.instantiateStreaming(
              fetch('https://myapp.com/module.wasm')
            );
            const result = module.instance.exports.compute(42);
            if (result !== 1764) {
              throw new Error(\`Expected 1764, got \${result}\`);
            }
            console.log('Functional test passed');
          })();
          EOF

      - name: Notify on failure
        if: failure()
        uses: 8398a7/action-slack@v3
        with:
          status: ${{ job.status }}
          text: "Production deployment health check failed!"
          webhook_url: ${{ secrets.SLACK_WEBHOOK }}
```

---

## 批判性分析

### CI/CD 复杂度

**Wasm 特殊挑战**：

| 挑战       | 传统 Web | Wasm                 | 增加复杂度 |
| :--- | :--- | :--- | :--- || 构建时间   | 1-2 min  | 5-10 min             | +400%      |
| 工具链依赖 | npm      | Rust+Emscripten+WABT | +300%      |
| 测试环境   | Node.js  | 多运行时             | +200%      |
| 优化步骤   | Terser   | wasm-opt+brotli      | +100%      |

**批判**：

> Wasm 的 CI/CD 流水线显著复杂于纯 JS 项目。多语言工具链、跨运行时测试、额外优化步骤都增加了维护负担。

### 构建时间分析

**典型流水线时间**：

```text
总时间: 15-20 分钟

1. Setup (2 min)
   - 安装 Rust, Emscripten, Node.js
   - 恢复缓存

2. Build (5-8 min)
   - Cargo build --release
   - wasm-pack build
   - npm run build

3. Test (3-5 min)
   - 单元测试
   - 集成测试
   - E2E 测试

4. Optimize (2-3 min)
   - wasm-opt
   - Brotli 压缩

5. Deploy (1-2 min)
   - 上传 S3
   - CDN 失效
```

**批判**：

> 构建时间是纯 JS 项目的 3-5 倍。对于高频部署场景（如 Trunk-Based Development），等待时间成为开发瓶颈。

---

## 最佳实践

### 缓存策略

**最大化缓存命中**：

```yaml
- name: Cache optimization
  uses: actions/cache@v3
  with:
    path: |
      ~/.cargo/bin/
      ~/.cargo/registry/index/
      ~/.cargo/registry/cache/
      ~/.cargo/git/db/
      target/
      node_modules/
      .npm/
    key: ${{ runner.os }}-${{ hashFiles('**/Cargo.lock', '**/package-lock.json') }}
    restore-keys: |
      ${{ runner.os }}-
```

### 增量构建

**只构建变更模块**：

```bash
# 检测变更
CHANGED_FILES=$(git diff --name-only HEAD~1)

if echo "$CHANGED_FILES" | grep -q "^rust/"; then
  echo "Building Rust module..."
  cargo build --target wasm32-wasi --release
fi

if echo "$CHANGED_FILES" | grep -q "^cpp/"; then
  echo "Building C++ module..."
  emcc cpp/main.cpp -o dist/module.js
fi
```

### 并行化

**最大化并行度**：

```yaml
jobs:
  build-matrix:
    strategy:
      matrix:
        module: [auth, compute, storage, ui]
    steps:
      - name: Build ${{ matrix.module }}
        run: cargo build -p ${{ matrix.module }} --target wasm32-wasi
```

---

## 参考文献

1. **[GitHub Actions]** Workflow Syntax (<https://docs.github.com/en/actions/using-workflows/workflow-syntax-for-github-actions>)
2. **[DevOps Research]** Accelerate: State of DevOps Report
3. **[Continuous Delivery]** Jez Humble, David Farley. "Continuous Delivery" (2010)

---

## 相关文档

- **[09.1 开发工具链](09.1_Development_Toolchain.md)** - 构建工具详解
- **[09.2 测试策略](09.2_Testing_Strategies.md)** - CI 中的测试
- **[07.2 部署策略](../07_Engineering_Economics/07.2_Deployment_Strategies.md)** - 部署模式
