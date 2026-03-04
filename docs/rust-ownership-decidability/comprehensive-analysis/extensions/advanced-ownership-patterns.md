# 高级所有权模式

> **超越基础的所有权技巧与模式**

---

## 1. 自引用结构

### 1.1 问题与解决方案

```rust
// 问题: 自引用结构
struct Parser {
    text: String,
    // 希望这里引用text
    current_token: &str,  // 错误! 需要生命周期
}

// 解决方案1: 使用索引
struct ParserSafe {
    text: String,
    token_start: usize,
    token_end: usize,
}

impl ParserSafe {
    fn current_token(&self) -> &str {
        &self.text[self.token_start..self.token_end]
    }
}

// 解决方案2: Pin + 不稳定特性
use std::pin::Pin;
use std::marker::PhantomPinned;

struct SelfReferential {
    data: String,
    // 使用指针而非引用
    ptr_to_data: *const u8,
    _pin: PhantomPinned,  // 禁止Unpin
}

impl SelfReferential {
    fn new(data: String) -> Pin<Box<Self>> {
        let mut boxed = Box::pin(Self {
            data,
            ptr_to_data: std::ptr::null(),
            _pin: PhantomPinned,
        });

        // Safety: 我们保证结构不会被移动
        let ptr = &boxed.data.as_bytes()[0] as *const u8;
        unsafe {
            let mut_ref = Pin::as_mut(&mut boxed);
            Pin::get_unchecked_mut(mut_ref).ptr_to_data = ptr;
        }

        boxed
    }

    fn data_ptr(&self) -> *const u8 {
        self.ptr_to_data
    }
}
```

### 1.2 rental / ouroboros crate

```rust
// 使用ouroboros简化自引用
use ouroboros::self_referencing;

#[self_referencing]
struct DataParser {
    data: String,
    #[borrows(data)]
    parser: Parser<'this>,
}

fn use_parser() {
    let parser = DataParser::new(
        "input data".to_string(),
        |data| Parser::new(data),
    );

    parser.with_parser(|p| {
        // 在这里使用parser
        p.parse_token();
    });
}
```

---

## 2. 所有权递归模式

### 2.1 链表实现

```rust
// 拥有所有权的链表
pub struct List<T> {
    head: Link<T>,
}

type Link<T> = Option<Box<Node<T>>>;

struct Node<T> {
    elem: T,
    next: Link<T>,
}

impl<T> List<T> {
    pub fn new() -> Self {
        List { head: None }
    }

    pub fn push(&mut self, elem: T) {
        let new_node = Box::new(Node {
            elem,
            next: self.head.take(),
        });
        self.head = Some(new_node);
    }

    pub fn pop(&mut self) -> Option<T> {
        self.head.take().map(|node| {
            self.head = node.next;
            node.elem
        })
    }

    // 获取头元素的引用
    pub fn peek(&self) -> Option<&T> {
        self.head.as_ref().map(|node| &node.elem)
    }

    // 获取头元素的可变引用
    pub fn peek_mut(&mut self) -> Option<&mut T> {
        self.head.as_mut().map(|node| &mut node.elem)
    }
}

impl<T> Drop for List<T> {
    fn drop(&mut self) {
        let mut cur_link = self.head.take();
        while let Some(mut boxed_node) = cur_link {
            cur_link = boxed_node.next.take();
            // boxed_node在这里被drop
        }
    }
}
```

### 2.2 Rc/Arc共享所有权

```rust
use std::rc::Rc;
use std::cell::RefCell;

// 共享所有权的图结构
pub struct Graph {
    nodes: Vec<Rc<RefCell<Node>>>,
}

struct Node {
    value: i32,
    edges: Vec<Rc<RefCell<Node>>>,
}

impl Graph {
    pub fn new() -> Self {
        Graph { nodes: vec![] }
    }

    pub fn add_node(&mut self, value: i32) -> Rc<RefCell<Node>> {
        let node = Rc::new(RefCell::new(Node {
            value,
            edges: vec![],
        }));
        self.nodes.push(Rc::clone(&node));
        node
    }

    pub fn add_edge(&self, from: &Rc<RefCell<Node>>, to: &Rc<RefCell<Node>>) {
        from.borrow_mut().edges.push(Rc::clone(to));
    }
}
```

---

## 3. 类型擦除与所有权

### 3.1 Trait对象

```rust
// 类型擦除的集合
pub struct ObjectPool {
    objects: Vec<Box<dyn Drawable>>,
}

pub trait Drawable {
    fn draw(&self, canvas: &mut Canvas);
    fn as_any(&self) -> &dyn Any;
}

impl ObjectPool {
    pub fn add<T: Drawable + 'static>(&mut self, obj: T) {
        self.objects.push(Box::new(obj));
    }

    pub fn draw_all(&self, canvas: &mut Canvas) {
        for obj in &self.objects {
            obj.draw(canvas);
        }
    }

    // 获取特定类型的对象
    pub fn get<T: Drawable + 'static>(&self, index: usize) -> Option<&T> {
        self.objects.get(index)?.as_any().downcast_ref::<T>()
    }
}
```

### 3.2 自定义vtable

```rust
// 手动类型擦除 (更可控)
pub struct ErasedHandle {
    data: *mut (),
    vtable: *const VTable,
}

struct VTable {
    drop: unsafe fn(*mut ()),
    clone: unsafe fn(*const ()) -> ErasedHandle,
    draw: unsafe fn(*const (), canvas: &mut Canvas),
}

impl ErasedHandle {
    pub fn new<T: Drawable + Clone>(value: T) -> Self {
        unsafe fn drop_fn<T>(data: *mut ()) {
            drop(Box::from_raw(data as *mut T));
        }

        unsafe fn clone_fn<T: Clone>(data: *const ()) -> ErasedHandle {
            let value = &*(data as *const T);
            ErasedHandle::new(value.clone())
        }

        unsafe fn draw_fn<T: Drawable>(data: *const (), canvas: &mut Canvas) {
            let value = &*(data as *const T);
            value.draw(canvas);
        }

        let data = Box::into_raw(Box::new(value)) as *mut ();

        static VTABLE: VTable = VTable {
            drop: drop_fn::<T>,
            clone: clone_fn::<T>,
            draw: draw_fn::<T>,
        };

        ErasedHandle {
            data,
            vtable: &VTABLE,
        }
    }
}

impl Drop for ErasedHandle {
    fn drop(&mut self) {
        unsafe {
            ((*self.vtable).drop)(self.data);
        }
    }
}
```

---

## 4. 编译时所有权检查

### 4.1 类型状态高级模式

```rust
// 数据库连接状态机
pub struct Connection<State> {
    config: Config,
    state: State,
}

// 状态标记
pub struct Disconnected;
pub struct Connected { conn: DbConn };
pub struct Transaction { txn: Txn };

// 状态转换实现
impl Connection<Disconnected> {
    pub fn new(config: Config) -> Self {
        Connection { config, state: Disconnected }
    }

    pub async fn connect(self) -> Result<Connection<Connected>, Error> {
        let conn = DbConn::connect(&self.config).await?;
        Ok(Connection {
            config: self.config,
            state: Connected { conn },
        })
    }
}

impl Connection<Connected> {
    pub async fn query(&mut self, sql: &str) -> Result<Rows, Error> {
        self.state.conn.query(sql).await
    }

    pub async fn begin_transaction(self) -> Result<Connection<Transaction>, Error> {
        let txn = self.state.conn.begin_transaction().await?;
        Ok(Connection {
            config: self.config,
            state: Transaction { txn },
        })
    }

    pub async fn disconnect(self) -> Connection<Disconnected> {
        self.state.conn.close().await;
        Connection {
            config: self.config,
            state: Disconnected,
        }
    }
}

impl Connection<Transaction> {
    pub async fn commit(self) -> Result<Connection<Connected>, Error> {
        self.state.txn.commit().await?;
        Ok(Connection {
            config: self.config,
            state: Connected { conn: self.state.txn.into_connection() },
        })
    }

    pub async fn rollback(self) -> Result<Connection<Connected>, Error> {
        self.state.txn.rollback().await?;
        Ok(Connection {
            config: self.config,
            state: Connected { conn: self.state.txn.into_connection() },
        })
    }
}

// 使用 - 编译时状态检查
async fn use_connection() -> Result<(), Error> {
    let conn = Connection::new(Config::default());
    // conn.query("SELECT 1");  // 编译错误! Disconnected状态

    let mut conn = conn.connect().await?;
    conn.query("SELECT 1").await?;  // OK

    let txn = conn.begin_transaction().await?;
    // txn.query("SELECT 1");  // 编译错误! 需要先使用txn的方法

    let conn = txn.commit().await?;
    // conn.commit();  // 编译错误! 不在Transaction状态

    let _ = conn.disconnect().await;
    Ok(())
}
```

---

## 5. 零拷贝模式

### 5.1 视图与切片

```rust
// 零拷贝数据解析
pub struct Packet<'a> {
    buffer: &'a [u8],
    header: &'a Header,
    payload: &'a [u8],
}

#[repr(C, packed)]
struct Header {
    magic: u16,
    version: u8,
    flags: u8,
    length: u32,
}

impl<'a> Packet<'a> {
    pub fn parse(buffer: &'a [u8]) -> Result<Self, Error> {
        if buffer.len() < std::mem::size_of::<Header>() {
            return Err(Error::TooShort);
        }

        // Safety: 我们检查了长度
        let header = unsafe {
            &*(buffer.as_ptr() as *const Header)
        };

        if header.magic != 0x1234 {
            return Err(Error::InvalidMagic);
        }

        let header_size = std::mem::size_of::<Header>();
        let payload = &buffer[header_size..];

        Ok(Packet {
            buffer,
            header,
            payload,
        })
    }

    pub fn payload(&self) -> &[u8] {
        self.payload
    }
}
```

### 5.2 IoSlice

```rust
use std::io::IoSlice;
use std::os::unix::io::AsRawFd;

// 分散/聚集IO
pub fn write_vectored(fd: RawFd, buffers: &[&[u8]]) -> io::Result<usize> {
    let mut slices: Vec<IoSlice> = buffers
        .iter()
        .map(|b| IoSlice::new(b))
        .collect();

    // 单个系统调用写入多个缓冲区
    let written = unsafe {
        libc::writev(fd, slices.as_ptr() as *const _, buffers.len() as _)
    };

    if written < 0 {
        Err(io::Error::last_os_error())
    } else {
        Ok(written as usize)
    }
}
```

---

## 6. 所有权与异步

### 6.1 Pin的深入理解

```rust
// Pin保证自引用安全
use std::pin::Pin;
use std::task::{Context, Poll};
use std::future::Future;

// 自引用Future示例
struct ReadFile {
    file: File,
    // 这个缓冲区被read操作引用
    buffer: Vec<u8>,
    // read操作正在进行的标志
    reading: bool,
}

impl Future for ReadFile {
    type Output = io::Result<usize>;

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        // Safety: 我们不会移动buffer
        let this = unsafe { self.as_mut().get_unchecked_mut() };

        if !this.reading {
            this.reading = true;
            // 开始异步读取
            this.file.read_async(&mut this.buffer, cx.waker());
            Poll::Pending
        } else {
            // 检查是否完成
            match this.file.poll_read_complete() {
                Some(n) => Poll::Ready(Ok(n)),
                None => Poll::Pending,
            }
        }
    }
}
```

### 6.2 Stream模式

```rust
use std::pin::Pin;
use std::task::{Context, Poll};

// 异步流
pub trait Stream {
    type Item;

    fn poll_next(
        self: Pin<&mut Self>,
        cx: &mut Context<'_>
    ) -> Poll<Option<Self::Item>>;
}

// 实现一个定时器流
pub struct Interval {
    next: Instant,
    period: Duration,
}

impl Stream for Interval {
    type Item = Instant;

    fn poll_next(
        mut self: Pin<&mut Self>,
        cx: &mut Context<'_>
    ) -> Poll<Option<Self::Item>> {
        let now = Instant::now();

        if now >= self.next {
            let current = self.next;
            self.next += self.period;
            Poll::Ready(Some(current))
        } else {
            // 注册定时器唤醒
            schedule_wake(self.next, cx.waker());
            Poll::Pending
        }
    }
}
```

---

## 7. 内存布局优化

### 7.1 内存对齐

```rust
// 控制内存布局
#[repr(C)]  // C兼容布局
struct PacketHeader {
    src: u32,
    dst: u32,
    len: u16,
    flags: u16,
}

#[repr(packed)]  // 无填充（注意性能影响）
struct CompactHeader {
    src: u32,
    dst: u32,
    len: u16,
    flags: u8,
}

#[repr(align(64))]  // 缓存行对齐
struct CacheLineAligned {
    data: [u8; 64],
}

// 使用std::alloc进行对齐分配
use std::alloc::{alloc, Layout};

fn aligned_alloc<T>(align: usize) -> *mut T {
    let layout = Layout::from_size_align(std::mem::size_of::<T>(), align)
        .expect("Invalid alignment");
    unsafe { alloc(layout) as *mut T }
}
```

### 7.2 SoA vs AoS

```rust
// AoS: Array of Structs (默认)
struct Particle {
    position: [f32; 3],
    velocity: [f32; 3],
    mass: f32,
}

struct AoSParticles {
    particles: Vec<Particle>,
}

// SoA: Struct of Arrays (SIMD友好)
struct SoAParticles {
    positions_x: Vec<f32>,
    positions_y: Vec<f32>,
    positions_z: Vec<f32>,
    velocities_x: Vec<f32>,
    velocities_y: Vec<f32>,
    velocities_z: Vec<f32>,
    masses: Vec<f32>,
}

impl SoAParticles {
    // SIMD友好的更新
    pub fn update_positions(&mut self, dt: f32) {
        // 可以并行处理连续的内存
        for i in 0..self.positions_x.len() {
            self.positions_x[i] += self.velocities_x[i] * dt;
            self.positions_y[i] += self.velocities_y[i] * dt;
            self.positions_z[i] += self.velocities_z[i] * dt;
        }
    }
}
```

---

## 8. 所有权与FFI

### 8.1 安全封装

```rust
// C库包装示例
pub struct SecureContext {
    ptr: *mut ffi::Context,
}

// Send + Sync 安全检查
unsafe impl Send for SecureContext {}
unsafe impl Sync for SecureContext {}

impl SecureContext {
    pub fn new() -> Result<Self, Error> {
        let ptr = unsafe { ffi::context_new() };
        if ptr.is_null() {
            return Err(Error::InitFailed);
        }
        Ok(SecureContext { ptr })
    }

    pub fn process(&mut self, data: &[u8]) -> Result<Vec<u8>, Error> {
        let mut out_len = 0;
        let out_ptr = unsafe {
            ffi::context_process(
                self.ptr,
                data.as_ptr(),
                data.len(),
                &mut out_len,
            )
        };

        if out_ptr.is_null() {
            return Err(Error::ProcessFailed);
        }

        // Safety: C库保证out_ptr有效且out_len正确
        let result = unsafe {
            let slice = std::slice::from_raw_parts(out_ptr, out_len);
            let vec = slice.to_vec();
            ffi::free_buffer(out_ptr);
            vec
        };

        Ok(result)
    }
}

impl Drop for SecureContext {
    fn drop(&mut self) {
        unsafe {
            ffi::context_free(self.ptr);
        }
    }
}
```

---

**维护者**: Rust Advanced Patterns Team
**更新日期**: 2026-03-05
