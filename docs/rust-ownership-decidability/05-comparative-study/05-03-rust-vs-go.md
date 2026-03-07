# Rust vs Go 深度对比

> **对比维度**: 性能、并发模型、内存管理、适用场景
> **难度**: 🟢 简单
> **目标读者**: 系统架构师、后端开发者

---

## 执行摘要

```
┌─────────────────────────────────────────────────────────┐
│                  Rust vs Go 速览                         │
├─────────────────────────────────────────────────────────┤
│                                                         │
│  维度              Rust              Go                 │
│  ─────────────────────────────────────────────────     │
│                                                         │
│  性能              ⭐⭐⭐⭐⭐          ⭐⭐⭐              │
│  开发速度          ⭐⭐⭐              ⭐⭐⭐⭐⭐          │
│  内存安全          ⭐⭐⭐⭐⭐          ⭐⭐⭐⭐            │
│  并发模型          所有权+类型系统     Goroutine+Channel │
│  学习曲线          陡峭               平缓              │
│  运行时            无                 GC                │
│                                                         │
│  选择 Rust: 系统编程、性能关键、嵌入式                   │
│  选择 Go:   Web 后端、云服务、快速开发                   │
│                                                         │
└─────────────────────────────────────────────────────────┘
```

---

## 1. 设计理念对比

### Rust: 零成本抽象 + 安全

```rust
// 编译期保证，运行时零开销
fn process(data: Vec<u8>) -> Result<Vec<u8>, Error> {
    // 所有权系统确保内存安全
    let processed: Vec<u8> = data
        .into_iter()
        .map(|b| b.wrapping_add(1))
        .collect();
    Ok(processed)
}  // 内存自动释放，无 GC 暂停
```

### Go: 简洁 + 工程效率

```go
// 简单直接，GC 管理内存
func process(data []byte) ([]byte, error) {
    processed := make([]byte, len(data))
    for i, b := range data {
        processed[i] = b + 1
    }
    return processed, nil  // GC 自动回收
}
```

---

## 2. 性能对比

### 基准测试

| 场景 | Rust | Go | 差异 |
|-----|------|-----|------|
| CPU 密集型 | 1x | 2-3x | Rust 更优 |
| 内存分配 | 1x | 3-5x | Rust 无 GC |
| 并发切换 | 200ns | 200ns | 相同 |
| 编译时间 | 10s | 2s | Go 更快 |
| 二进制大小 | 5MB | 15MB | Rust 更小 |

### 实际案例

```
Web 服务 (Hello World)
├── QPS
│   ├── Rust (Actix):    ~200k
│   └── Go (Gin):        ~120k
│
└── 内存占用
    ├── Rust:            ~5MB
    └── Go:              ~20MB
```

---

## 3. 并发模型对比

### Rust: 所有权驱动的并发

```rust
use std::thread;
use std::sync::mpsc;

// 编译期防止数据竞争
let (tx, rx) = mpsc::channel();

thread::spawn(move || {
    tx.send(42).unwrap();  // 所有权转移
});

let msg = rx.recv().unwrap();
```

**特点**:

- 编译期保证线程安全
- `Send`/`Sync` trait
- 零成本抽象

### Go: Goroutine + Channel

```go
ch := make(chan int)

go func() {
    ch <- 42  // 发送
}()

msg := <-ch  // 接收
```

**特点**:

- 轻量级线程 (2KB 栈)
- M:N 调度
- 内置 Channel

### 对比

| 特性 | Rust | Go |
|-----|------|-----|
| 线程/协程 | OS 线程 | Goroutine |
| 内存占用 | ~1MB | ~2KB |
| 调度 | OS | Go runtime |
| 数据竞争 | 编译期阻止 | 运行时检测 (race detector) |
| 并行 | 原生 | 原生 |

---

## 4. 错误处理对比

### Rust: 显式 Result

```rust
fn read_file(path: &str) -> Result<String, io::Error> {
    fs::read_to_string(path)?  // 传播错误
}

// 使用
match read_file("data.txt") {
    Ok(content) => println!("{}", content),
    Err(e) => eprintln!("Error: {}", e),
}
```

### Go: 多返回值

```go
func readFile(path string) (string, error) {
    data, err := os.ReadFile(path)
    if err != nil {
        return "", err  // 传播错误
    }
    return string(data), nil
}

// 使用
content, err := readFile("data.txt")
if err != nil {
    log.Fatal(err)
}
```

**对比**:

- Rust: 类型系统强制检查
- Go: 约定俗成，可能遗漏

---

## 5. 适用场景

### 选择 Rust 当

- 系统编程 (操作系统、嵌入式)
- 性能关键 (游戏引擎、高频交易)
- 无 GC 需求 (实时系统)
- 安全关键 (加密、区块链)

### 选择 Go 当

- Web 后端/API 服务
- 云原生/微服务
- DevOps 工具
- 快速原型开发

---

## 6. 生态对比

| 领域 | Rust | Go |
|-----|------|-----|
| Web 框架 | Actix, Axum | Gin, Echo |
| gRPC | tonic | grpc-go |
| 数据库 | sqlx, diesel | database/sql |
| 测试 | 内置 + 丰富 | 内置 |
| 包管理 | Cargo | Go Modules |

---

*文档版本: 1.0.0*
