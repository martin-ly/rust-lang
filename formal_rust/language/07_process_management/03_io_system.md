# Rust I/O系统 {#io系统}

## 目录

- [Rust I/O系统 {#io系统}](#rust-io系统-io系统)
  - [目录](#目录)
  - [I/O系统概述 {#io系统概述}](#io系统概述-io系统概述)
  - [I/O模型 {#io模型}](#io模型-io模型)
  - [文件操作 {#文件操作}](#文件操作-文件操作)
  - [网络I/O {#网络io}](#网络io-网络io)
  - [标准I/O {#标准io}](#标准io-标准io)
  - [I/O多路复用 {#io多路复用}](#io多路复用-io多路复用)
  - [缓冲策略 {#缓冲策略}](#缓冲策略-缓冲策略)
  - [错误处理 {#错误处理}](#错误处理-错误处理)
  - [形式化模型 {#形式化模型}](#形式化模型-形式化模型)

## I/O系统概述 {#io系统概述}

Rust的I/O系统提供了与操作系统I/O资源交互的安全抽象。它确保文件操作、网络通信和进程间I/O等操作保持Rust的内存安全性和类型安全性保证，同时提供高性能和跨平台兼容性。

**相关概念**:

- [资源管理](00_index.md#资源管理) (本模块)
- [错误处理](00_index.md#错误处理) (本模块)
- [异步I/O](../06_async_await/01_formal_async_system.md#核心概念) (模块 06)

## I/O模型 {#io模型}

Rust支持多种I/O模型，每种模型都有其适用场景:

1. **阻塞I/O** {#阻塞io} - 操作完成前线程阻塞

   ```rust
   let mut file = File::open("file.txt")?;
   let mut contents = String::new();
   file.read_to_string(&mut contents)?; // 阻塞直到完成
   ```

2. **非阻塞I/O** {#非阻塞io} - 操作立即返回，可能需要轮询

   ```rust
   let mut file = File::open("file.txt")?;
   file.set_nonblocking(true)?;
   let result = file.read(&mut buffer)?;
   ```

3. **异步I/O** {#异步io} - 通过Future抽象处理I/O完成通知

   ```rust
   let mut file = File::open("file.txt").await?;
   let contents = file.read_to_string().await?;
   ```

**相关概念**:

- [阻塞操作](../05_concurrency/04_sync_primitives.md#阻塞操作) (模块 05)
- [Future特质](../06_async_await/01_formal_async_system.md#futures) (模块 06)
- [轮询机制](../06_async_await/01_formal_async_system.md#轮询机制) (模块 06)

## 文件操作 {#文件操作}

Rust提供完整的文件系统操作抽象:

1. **文件读写** {#文件读写} - 读取和写入文件内容

   ```rust
   // 读取文件
   let contents = fs::read_to_string("file.txt")?;
   
   // 写入文件
   fs::write("file.txt", "Hello, world!")?;
   ```

2. **文件元数据** {#文件元数据} - 获取和修改文件属性

   ```rust
   let metadata = fs::metadata("file.txt")?;
   println!("大小: {} 字节", metadata.len());
   println!("修改时间: {:?}", metadata.modified()?);
   ```

3. **目录操作** {#目录操作} - 创建、遍历和删除目录

   ```rust
   // 创建目录
   fs::create_dir_all("path/to/dir")?;
   
   // 遍历目录
   for entry in fs::read_dir("path")? {
       let entry = entry?;
       println!("{:?}", entry.path());
   }
   ```

**相关概念**:

- [资源获取即初始化](../02_type_system/02_ownership_system.md#RAII模式) (模块 02)
- [错误处理](../03_control_flow/03_error_handling.md#错误处理定义) (模块 03)
- [迭代器](../08_algorithms/01_formal_theory.md#迭代器) (模块 08)

## 网络I/O {#网络io}

Rust提供跨平台的网络通信抽象:

1. **TCP通信** {#tcp通信} - 使用TCP协议的可靠流式通信

   ```rust
   // TCP服务器
   let listener = TcpListener::bind("127.0.0.1:8080")?;
   for stream in listener.incoming() {
       let stream = stream?;
       // 处理连接
   }
   
   // TCP客户端
   let mut stream = TcpStream::connect("127.0.0.1:8080")?;
   stream.write_all(b"Hello, server!")?;
   ```

2. **UDP通信** {#udp通信} - 使用UDP协议的无连接数据报通信

   ```rust
   let socket = UdpSocket::bind("127.0.0.1:8080")?;
   socket.send_to(&[1, 2, 3], "127.0.0.1:8081")?;
   ```

3. **套接字选项** {#套接字选项} - 配置网络套接字的行为

   ```rust
   let socket = TcpStream::connect("127.0.0.1:8080")?;
   socket.set_nodelay(true)?; // 禁用Nagle算法
   socket.set_ttl(128)?; // 设置TTL
   ```

**相关概念**:

- [错误处理](../03_control_flow/03_error_handling.md#错误处理定义) (模块 03)
- [并发服务器](../05_concurrency/01_formal_concurrency_model.md#并发服务器) (模块 05)
- [异步任务](../06_async_await/01_formal_async_system.md#任务) (模块 06)

## 标准I/O {#标准io}

Rust提供与进程标准I/O流交互的抽象:

1. **标准输入** {#标准输入} - 从控制台读取输入

   ```rust
   let mut input = String::new();
   std::io::stdin().read_line(&mut input)?;
   ```

2. **标准输出** {#标准输出} - 向控制台写入输出

   ```rust
   println!("Hello, world!"); // 标准输出
   eprintln!("Error message"); // 标准错误
   ```

3. **进程I/O重定向** {#io重定向} - 重定向子进程的I/O流

   ```rust
   let child = Command::new("ls")
       .stdin(Stdio::piped())
       .stdout(Stdio::piped())
       .spawn()?;
   ```

**相关概念**:

- [进程创建与管理](00_index.md#进程创建与管理) (本模块)
- [字符串处理](../08_algorithms/02_string_processing.md#字符串处理) (模块 08)
- [错误传播](../03_control_flow/03_error_handling.md#错误传播) (模块 03)

## I/O多路复用 {#io多路复用}

I/O多路复用允许单个线程监视多个I/O源:

1. **Poll模型** {#poll模型} - 使用轮询检查多个I/O源

   ```rust
   let mut poll = Poll::new()?;
   poll.registry().register(&mut stream, Token(0), Interest::READABLE)?;
   let mut events = Events::with_capacity(128);
   
   poll.poll(&mut events, Some(Duration::from_millis(100)))?;
   for event in events.iter() {
       // 处理就绪事件
   }
   ```

2. **异步运行时** {#异步运行时} - 通过异步运行时实现高效I/O多路复用

   ```rust
   // 使用tokio
   #[tokio::main]
   async fn main() -> Result<()> {
       let mut listener = TcpListener::bind("127.0.0.1:8080").await?;
       loop {
           let (socket, _) = listener.accept().await?;
           tokio::spawn(async move {
               // 处理连接
           });
       }
   }
   ```

**相关概念**:

- [事件循环](../06_async_await/01_formal_async_system.md#执行器与运行时) (模块 06)
- [反应器模式](../09_design_patterns/02_concurrency_patterns.md#反应器模式) (模块 09)
- [非阻塞操作](../05_concurrency/04_sync_primitives.md#非阻塞操作) (模块 05)

## 缓冲策略 {#缓冲策略}

Rust I/O系统提供多种缓冲策略:

1. **BufReader/BufWriter** {#缓冲读写器} - 为读写操作添加缓冲

   ```rust
   let file = File::open("file.txt")?;
   let reader = BufReader::new(file);
   for line in reader.lines() {
       println!("{}", line?);
   }
   
   let file = File::create("file.txt")?;
   let mut writer = BufWriter::new(file);
   writer.write_all(b"Hello, world!")?;
   ```

2. **自定义缓冲** {#自定义缓冲} - 通过`Read`/`Write` trait实现自定义缓冲

   ```rust
   struct CustomBuf<R> {
       inner: R,
       buffer: Vec<u8>,
   }
   
   impl<R: Read> Read for CustomBuf<R> {
       fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
           // 自定义读取实现
       }
   }
   ```

**相关概念**:

- [特质系统](../02_type_system/01_formal_type_system.md#trait系统) (模块 02)
- [零复制](../22_performance_optimization/02_memory_optimization.md#零复制) (模块 22)
- [迭代器](../08_algorithms/01_formal_theory.md#迭代器) (模块 08)

## 错误处理 {#错误处理}

I/O操作的错误处理:

1. **I/O Result类型** {#io-result} - `io::Result<T>`类型表示I/O操作结果

   ```rust
   fn read_file() -> io::Result<String> {
       let mut file = File::open("file.txt")?;
       let mut contents = String::new();
       file.read_to_string(&mut contents)?;
       Ok(contents)
   }
   ```

2. **错误类型** {#io-error} - `io::Error`类型表示I/O错误

   ```rust
   match error.kind() {
       ErrorKind::NotFound => {
           // 文件未找到
       }
       ErrorKind::PermissionDenied => {
           // 权限被拒绝
       }
       _ => {
           // 其他错误
       }
   }
   ```

**相关概念**:

- [结果类型](../03_control_flow/03_error_handling.md#结果类型) (模块 03)
- [错误传播](../03_control_flow/03_error_handling.md#错误传播) (模块 03)
- [模式匹配](../03_control_flow/02_pattern_matching_system.md#模式匹配) (模块 03)

## 形式化模型 {#形式化模型}

I/O系统的形式化模型:

1. **I/O资源抽象** {#io资源抽象}

   ```math
   \text{IOResource} = \text{File} \cup \text{Socket} \cup \text{Pipe} \cup \text{Console}
   ```

2. **I/O操作语义** {#io操作语义}

   ```math
   \text{read} : \text{IOResource} \times \text{Buffer} \times \text{Mode} \rightarrow \text{Result<Size>}
   \text{write} : \text{IOResource} \times \text{Data} \times \text{Mode} \rightarrow \text{Result<Size>}
   ```

3. **缓冲模型** {#缓冲模型}

   ```math
   \text{Buffer} = (\text{Capacity}, \text{Data}, \text{Position})
   ```

4. **I/O多路复用模型** {#多路复用模型}

   ```math
   \text{poll} : \mathcal{P}(\text{IOResource} \times \text{Interest}) \times \text{Timeout} \rightarrow \mathcal{P}(\text{IOResource} \times \text{Event})
   ```

**形式化保证**:

1. **资源安全性**

   ```math
   \forall r \in \text{IOResource}: \text{closed}(r) \Rightarrow \neg\text{accessible}(r)
   ```

2. **缓冲一致性**

   ```math
   \forall b \in \text{Buffer}, \forall d \in \text{Data}:
   \text{write}(b, d) \circ \text{read}(b) = \text{id}(d)
   ```

3. **错误处理正确性**

   ```math
   \forall r \in \text{IOResource}, \forall op \in \text{IOOp}:
   \text{failed}(op, r) \Rightarrow \text{Result::Err}
   ```

**相关概念**:

- [形式化语义](../20_theoretical_perspectives/04_mathematical_foundations.md#形式化语义) (模块 20)
- [资源安全](../13_safety_guarantees/01_formal_safety.md#资源安全) (模块 13)
- [类型系统](../02_type_system/01_formal_type_system.md#类型系统) (模块 02)
