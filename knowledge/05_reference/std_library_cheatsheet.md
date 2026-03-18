# Rust 标准库速查表

> 本文档为 Rust 标准库常用模块、Trait 和宏的快速参考指南，适合日常开发查阅。

---

## 常用模块速查

### std::vec - 动态数组

```rust
let mut v = Vec::new();
let v = vec![1, 2, 3];           // 宏创建
let v = Vec::with_capacity(10);  // 预分配容量
```

| 方法 | 说明 | 示例 |
|------|------|------|
| `push(x)` | 尾部添加元素 | `v.push(42)` |
| `pop()` | 尾部移除元素 | `v.pop()` → `Option<T>` |
| `insert(i, x)` | 指定位置插入 | `v.insert(0, x)` |
| `remove(i)` | 指定位置移除 | `v.remove(0)` |
| `get(i)` | 安全获取 | `v.get(0)` → `Option<&T>` |
| `len()` | 元素个数 | `v.len()` |
| `is_empty()` | 是否为空 | `v.is_empty()` |
| `clear()` | 清空 | `v.clear()` |
| `contains(&x)` | 包含检查 | `v.contains(&5)` |
| `sort()` | 排序 | `v.sort()` |
| `sort_by(f)` | 自定义排序 | `v.sort_by(\|a,b\| a.cmp(b))` |
| `dedup()` | 去重（需先排序）| `v.dedup()` |
| `retain(f)` | 条件保留 | `v.retain(\|x\| x > 0)` |
| `extend(iter)` | 扩展 | `v.extend([1,2,3])` |
| `split_off(i)` | 分割 | `let v2 = v.split_off(3)` |
| `truncate(n)` | 截断 | `v.truncate(5)` |
| `swap_remove(i)` | 交换移除（O(1)）| `v.swap_remove(2)` |

---

### std::option - 可选值

```rust
let x: Option<i32> = Some(5);
let y: Option<i32> = None;
```

| 方法 | 说明 | 返回值 |
|------|------|--------|
| `is_some()` | 是否为 Some | `bool` |
| `is_none()` | 是否为 None | `bool` |
| `unwrap()` | 解包（Panic if None）| `T` |
| `expect(msg)` | 解包带错误信息 | `T` |
| `unwrap_or(default)` | 解包或默认值 | `T` |
| `unwrap_or_else(f)` | 解包或计算值 | `T` |
| `map(f)` | 映射 | `Option<U>` |
| `and_then(f)` | 扁平映射 | `Option<U>` |
| `filter(f)` | 条件过滤 | `Option<T>` |
| `ok_or(e)` | 转 Result | `Result<T, E>` |
| `ok_or_else(f)` | 延迟转 Result | `Result<T, E>` |
| `as_ref()` | 转引用 | `Option<&T>` |
| `take()` | 取出值置 None | `Option<T>` |
| `replace(val)` | 替换值 | `Option<T>` |
| `zip(other)` | 组合两个 Option | `Option<(T, U)>` |

```rust
// 常用模式
let x = Some(5).map(|n| n * 2);           // Some(10)
let x = Some(5).and_then(|n| Some(n*2));  // Some(10)
let x: Option<i32> = None.or(Some(3));    // Some(3)
```

---

### std::result - 错误处理

```rust
let x: Result<i32, &str> = Ok(5);
let y: Result<i32, &str> = Err("error");
```

| 方法 | 说明 | 返回值 |
|------|------|--------|
| `is_ok()` | 是否为 Ok | `bool` |
| `is_err()` | 是否为 Err | `bool` |
| `unwrap()` | 解包（Panic if Err）| `T` |
| `expect(msg)` | 解包带信息 | `T` |
| `unwrap_or(default)` | 解包或默认值 | `T` |
| `unwrap_or_else(f)` | 解包或计算值 | `T` |
| `unwrap_err()` | 解包错误 | `E` |
| `map(f)` | 映射 Ok 值 | `Result<U, E>` |
| `map_err(f)` | 映射 Err 值 | `Result<T, F>` |
| `and_then(f)` | 扁平映射 | `Result<U, E>` |
| `or_else(f)` | 错误恢复 | `Result<T, F>` |
| `as_ref()` | 转引用 | `Result<&T, &E>` |

```rust
// ? 运算符传播错误
fn read_file() -> Result<String, io::Error> {
    let content = fs::read_to_string("file.txt")?;
    Ok(content)
}
```

---

### std::collections - 集合类型

#### HashMap<K, V> / BTreeMap<K, V>

```rust
use std::collections::HashMap;
let mut m = HashMap::new();
m.insert("key", "value");

// 带初始容量的 HashMap
let mut m = HashMap::with_capacity(100);
```

| 方法 | 说明 |
|------|------|
| `insert(k, v)` | 插入/更新，返回旧值 `Option<V>` |
| `get(&k)` | 获取 `Option<&V>` |
| `get_mut(&k)` | 获取可变引用 `Option<&mut V>` |
| `remove(&k)` | 移除，返回 `Option<V>` |
| `contains_key(&k)` | 包含检查 |
| `entry(k)` | 获取 Entry（用于复杂操作）|
| `len()` / `is_empty()` | 数量/空检查 |
| `keys()` / `values()` | 键/值迭代器 |
| `iter()` | 键值对迭代器 |

```rust
// Entry API 模式
*m.entry("key").or_insert(0) += 1;
let val = m.entry("key").or_insert_with(|| compute());
```

#### HashSet<T> / BTreeSet<T>

```rust
use std::collections::HashSet;
let mut s = HashSet::new();
s.insert(42);
```

| 方法 | 说明 |
|------|------|
| `insert(x)` | 插入，返回是否已存在 `bool` |
| `remove(&x)` | 移除，返回是否存在 `bool` |
| `contains(&x)` | 包含检查 |
| `union(&other)` | 并集 |
| `intersection(&other)` | 交集 |
| `difference(&other)` | 差集 |
| `symmetric_difference(&other)` | 对称差集 |
| `is_disjoint(&other)` | 是否不相交 |
| `is_subset(&other)` | 是否为子集 |
| `is_superset(&other)` | 是否为超集 |

---

### std::string - 字符串

```rust
let mut s = String::new();
let s = String::from("hello");
let s = "hello".to_string();
```

| 方法 | 说明 |
|------|------|
| `push(c)` | 追加字符 |
| `push_str(&str)` | 追加字符串 |
| `pop()` | 弹出最后一个字符 `Option<char>` |
| `insert(i, c)` | 插入字符 |
| `remove(i)` | 移除字符（按字节索引）|
| `replace_range(range, &str)` | 替换范围 |
| `clear()` | 清空 |
| `len()` | 字节长度 |
| `is_empty()` | 是否为空 |
| `capacity()` | 容量 |
| `reserve(n)` | 预分配容量 |
| `shrink_to_fit()` | 收缩至合适大小 |
| `as_str()` | 转 &str |
| `split_whitespace()` | 按空白分割迭代器 |
| `lines()` | 按行分割迭代器 |
| `contains(&str)` | 子串检查 |
| `starts_with(&str)` / `ends_with(&str)` | 前缀/后缀检查 |
| `replace(a, b)` | 替换所有匹配 |
| `replacen(a, b, n)` | 替换前 n 个匹配 |
| `to_uppercase()` / `to_lowercase()` | 大小写转换 |
| `trim()` / `trim_start()` / `trim_end()` | 去除空白 |

```rust
// 格式化
let s = format!("{} + {} = {}", 1, 2, 3);
let s = format!("{:08}", 42);     // 前导零填充
let s = format!("{:.2}", 3.14159); // 小数位限制
```

---

### std::io - 输入输出

```rust
use std::io::{self, Read, Write, BufRead, BufReader, BufWriter};
```

#### Read Trait

| 方法 | 说明 |
|------|------|
| `read(&mut buf)` | 读取到缓冲区，返回字节数 |
| `read_exact(&mut buf)` | 精确读取，失败则 Err |
| `read_to_end(&mut vec)` | 读到 Vec |
| `read_to_string(&mut s)` | 读到 String |
| `bytes()` | 字节迭代器 |
| `chain(reader)` | 链接读取器 |
| `take(n)` | 限制读取字节数 |

#### Write Trait

| 方法 | 说明 |
|------|------|
| `write(&buf)` | 写入，返回字节数 |
| `write_all(&buf)` | 写入全部，失败则 Err |
| `write_fmt(args)` | 格式化写入 |
| `flush()` | 刷新缓冲区 |

#### BufRead Trait（需 BufReader）

| 方法 | 说明 |
|------|------|
| `fill_buf()` | 填充内部缓冲区 |
| `consume(n)` | 消费缓冲区字节 |
| `read_line(&mut s)` | 读取一行 |
| `lines()` | 行迭代器 |
| `read_until(byte, &mut vec)` | 读到指定字节 |
| `split(byte)` | 按字节分割迭代器 |

```rust
// 常用模式
let reader = BufReader::new(file);
for line in reader.lines() {
    let line = line?;
    println!("{}", line);
}

// 标准输入
let stdin = io::stdin();
let line = stdin.lock().lines().next();
```

---

### std::fs - 文件系统

```rust
use std::fs;
```

| 函数 | 说明 | 返回 |
|------|------|------|
| `read(path)` | 读取整个文件 | `io::Result<Vec<u8>>` |
| `read_to_string(path)` | 读取为字符串 | `io::Result<String>` |
| `write(path, contents)` | 写入文件 | `io::Result<()>` |
| `copy(from, to)` | 复制文件 | `io::Result<u64>`（字节数）|
| `remove_file(path)` | 删除文件 | `io::Result<()>` |
| `rename(from, to)` | 重命名 | `io::Result<()>` |
| `create_dir(path)` | 创建目录 | `io::Result<()>` |
| `create_dir_all(path)` | 递归创建目录 | `io::Result<()>` |
| `remove_dir(path)` | 删除空目录 | `io::Result<()>` |
| `remove_dir_all(path)` | 递归删除目录 | `io::Result<()>` |
| `read_dir(path)` | 读取目录条目 | `io::Result<ReadDir>` |
| `metadata(path)` | 获取元数据 | `io::Result<Metadata>` |
| `symlink_metadata(path)` | 获取符号链接元数据 | `io::Result<Metadata>` |
| `hard_link(src, dst)` | 创建硬链接 | `io::Result<()>` |
| `symlink(src, dst)` | 创建符号链接 | `io::Result<()>` |

```rust
// 文件操作
let mut file = fs::File::open("input.txt")?;
let mut contents = String::new();
file.read_to_string(&mut contents)?;

// 原子写入
fs::write("output.txt", "content")?;

// 遍历目录
for entry in fs::read_dir("./")? {
    let entry = entry?;
    println!("{}", entry.path().display());
}
```

---

### std::path - 路径处理

```rust
use std::path::{Path, PathBuf};
```

#### Path（不可变路径引用）

| 方法 | 说明 |
|------|------|
| `exists()` | 是否存在 |
| `is_file()` / `is_dir()` | 文件/目录检查 |
| `is_absolute()` / `is_relative()` | 绝对/相对路径检查 |
| `file_name()` | 文件名 `Option<&OsStr>` |
| `extension()` | 扩展名 `Option<&OsStr>` |
| `file_stem()` | 文件名（无扩展名）|
| `parent()` | 父目录 `Option<&Path>` |
| `join(path)` | 拼接路径 |
| `with_extension(ext)` | 更改扩展名 |
| `with_file_name(name)` | 更改文件名 |
| `components()` | 路径组件迭代器 |
| `display()` | 显示格式化 |
| `to_str()` | 转 &str（可能失败）|
| `to_string_lossy()` | 转 String（ lossy ）|

#### PathBuf（可变路径）

```rust
let mut p = PathBuf::from("/usr");
p.push("local");       // /usr/local
p.push("bin");         // /usr/local/bin
p.pop();               // /usr/local

let ext = p.extension();
let parent = p.parent();
```

---

### std::env - 环境变量

```rust
use std::env;
```

| 函数 | 说明 | 返回 |
|------|------|------|
| `var(key)` | 获取环境变量 | `Result<String, VarError>` |
| `var_os(key)` | 获取（OsString）| `Option<OsString>` |
| `set_var(key, val)` | 设置环境变量 | - |
| `remove_var(key)` | 移除环境变量 | - |
| `vars()` | 所有环境变量迭代器 | `Vars` |
| `vars_os()` | 所有环境变量（OsString）| `VarsOs` |
| `args()` | 命令行参数迭代器 | `Args` |
| `args_os()` | 命令行参数（OsString）| `ArgsOs` |
| `current_dir()` | 当前工作目录 | `io::Result<PathBuf>` |
| `set_current_dir(path)` | 设置工作目录 | `io::Result<()>` |
| `current_exe()` | 当前可执行文件路径 | `io::Result<PathBuf>` |
| `home_dir()` | 用户主目录（已弃用）| `Option<PathBuf>` |
| `temp_dir()` | 临时目录 | `PathBuf` |

```rust
// 常用模式
let path = env::var("PATH")?;
let args: Vec<String> = env::args().collect();
let key = env::var("API_KEY").unwrap_or_default();
```

---

### std::process - 进程管理

```rust
use std::process::{Command, Stdio};
```

#### Command 构建器

```rust
let output = Command::new("ls")
    .arg("-la")
    .arg("/tmp")
    .env("KEY", "value")
    .current_dir("/home")
    .stdout(Stdio::piped())
    .stderr(Stdio::piped())
    .output()?;  // 执行并等待

// 方法链
let mut child = Command::new("program")
    .args(&["-a", "-b", "-c"])
    .stdin(Stdio::piped())
    .spawn()?;   // 启动不等待
```

| 方法 | 说明 |
|------|------|
| `new(program)` | 创建命令 |
| `arg(a)` / `args(iter)` | 添加参数 |
| `env(k, v)` / `env_remove(k)` | 环境变量 |
| `current_dir(dir)` | 工作目录 |
| `stdin/stdout/stdio(cfg)` | 标准流配置 |
| `spawn()` | 启动子进程，返回 Child |
| `output()` | 执行并捕获输出 |
| `status()` | 执行仅获取状态 |

#### Child 进程控制

```rust
let mut child = Command::new("sleep").arg("10").spawn()?;
let pid = child.id();
child.kill()?;           // 终止进程
let status = child.wait()?;  // 等待结束
```

| 方法 | 说明 |
|------|------|
| `id()` | 进程 ID |
| `kill()` | 终止进程 |
| `wait()` | 等待结束 |
| `try_wait()` | 非阻塞检查 |
| `wait_with_output()` | 等待并获取输出 |

---

### std::thread - 多线程

```rust
use std::thread;
use std::time::Duration;
```

| 函数/方法 | 说明 |
|-----------|------|
| `spawn(f)` | 创建新线程 |
| `sleep(dur)` | 线程休眠 |
| `park()` | 阻塞当前线程 |
| `park_timeout(dur)` | 限时阻塞 |
| `unpark()` | 唤醒线程 |
| `current()` | 当前线程句柄 |
| `yield_now()` | 让出 CPU |
| `available_parallelism()` | 可用并行度 |

```rust
// 创建线程
let handle = thread::spawn(|| {
    println!("新线程");
    42  // 返回值
});

// 等待线程完成
let result = handle.join().unwrap();

// 带名称的线程
let handle = thread::Builder::new()
    .name("worker".to_string())
    .spawn(|| {
        println!("{}", thread::current().name().unwrap());
    })?;

// 作用域线程（Rust 1.63+）
thread::scope(|s| {
    s.spawn(|| println!("线程 A"));
    s.spawn(|| println!("线程 B"));
}); // 自动等待所有线程完成
```

---

### std::sync - 同步原语

#### Mutex<T> - 互斥锁

```rust
use std::sync::Mutex;

let m = Mutex::new(5);
{
    let mut num = m.lock().unwrap();
    *num = 6;
} // 自动解锁
```

| 方法 | 说明 |
|------|------|
| `lock()` | 获取锁，阻塞 `MutexGuard<T>` |
| `try_lock()` | 非阻塞尝试 `TryLockResult` |
| `into_inner()` | 消费锁获取数据 |
| `get_mut()` | 可变引用获取数据（无需锁）|

#### RwLock<T> - 读写锁

```rust
use std::sync::RwLock;

let lock = RwLock::new(5);
let r = lock.read().unwrap();   // 多个读
let w = lock.write().unwrap();  // 独占写
```

| 方法 | 说明 |
|------|------|
| `read()` | 获取读锁 `RwLockReadGuard` |
| `try_read()` | 非阻塞读 |
| `write()` | 获取写锁 `RwLockWriteGuard` |
| `try_write()` | 非阻塞写 |

#### Arc<T> - 原子引用计数

```rust
use std::sync::Arc;

let data = Arc::new(Mutex::new(0));
let data2 = Arc::clone(&data);

thread::spawn(move || {
    let mut d = data2.lock().unwrap();
    *d += 1;
});
```

| 方法 | 说明 |
|------|------|
| `new(x)` | 创建 Arc |
| `clone(&self)` | 克隆引用 |
| `strong_count(&self)` | 强引用计数 |
| `weak_count(&self)` | 弱引用计数 |
| `try_unwrap(self)` | 尝试解包（计数为1时）|

#### 其他同步类型

```rust
use std::sync::{
    Barrier,      // 屏障同步
    Condvar,      // 条件变量
    Once,         // 一次性初始化
    mpsc,         // 多生产者单消费者通道
};

// 通道
let (tx, rx) = mpsc::channel();
tx.send(42).unwrap();
let val = rx.recv().unwrap();
```

---

### std::time - 时间处理

```rust
use std::time::{Duration, Instant, SystemTime};
```

#### Duration - 时间间隔

```rust
let dur = Duration::from_secs(5);      // 5秒
let dur = Duration::from_millis(500);  // 500毫秒
let dur = Duration::from_nanos(1000);  // 1000纳秒
let dur = Duration::new(secs, nanos);  // 秒+纳秒

// 运算
let sum = dur1 + dur2;
let diff = dur1 - dur2;
let mul = dur * 3;
let div = dur / 2;
```

| 方法 | 说明 |
|------|------|
| `as_secs()` | 秒数（u64）|
| `as_millis()` | 毫秒数（u128）|
| `as_micros()` | 微秒数（u128）|
| `as_nanos()` | 纳秒数（u128）|
| `subsec_millis()` | 毫秒部分 |
| `subsec_micros()` | 微秒部分 |
| `subsec_nanos()` | 纳秒部分 |
| `is_zero()` | 是否为零 |
| `saturating_add/sub/mul/div` | 饱和运算 |

#### Instant - 单调时钟（测量间隔）

```rust
let start = Instant::now();
// ... 执行代码
let elapsed = start.elapsed();
println!("耗时: {:?}", elapsed);

// 检查是否超时
if start.elapsed() > Duration::from_secs(5) {
    println!("超时!");
}
```

| 方法 | 说明 |
|------|------|
| `now()` | 当前时刻 |
| `elapsed()` | 从该时刻到现在的时间 |
| `duration_since(instant)` | 计算间隔 |
| `saturating_duration_since(i)` | 饱和计算 |

#### SystemTime - 系统时间

```rust
let now = SystemTime::now();
let since_epoch = now.duration_since(SystemTime::UNIX_EPOCH)?;
```

---

### std::iter - 迭代器

#### Iterator Trait 方法

```rust
let v = vec![1, 2, 3, 4, 5];
```

| 方法 | 说明 | 消费/惰性 |
|------|------|-----------|
| `next()` | 下一个元素 | 消费 |
| `count()` | 元素个数 | 消费 |
| `sum()` | 求和 | 消费 |
| `product()` | 求积 | 消费 |
| `collect::<Vec<_>>()` | 收集 | 消费 |
| `fold(init, f)` | 折叠 | 消费 |
| `reduce(f)` | 归约 | 消费 |
| `for_each(f)` | 遍历执行 | 消费 |
| `any(f)` / `all(f)` | 任一/全部满足 | 消费 |
| `find(f)` | 查找 | 消费 |
| `position(f)` | 查找索引 | 消费 |
| `max()` / `min()` | 最大/最小 | 消费 |
| `max_by(f)` / `min_by(f)` | 自定义比较 | 消费 |
| `take(n)` | 取前 n 个 | 惰性 |
| `skip(n)` | 跳过 n 个 | 惰性 |
| `step_by(n)` | 步长 | 惰性 |
| `map(f)` | 映射 | 惰性 |
| `filter(f)` | 过滤 | 惰性 |
| `filter_map(f)` | 过滤+映射 | 惰性 |
| `flat_map(f)` | 扁平映射 | 惰性 |
| `flatten()` | 展平 | 惰性 |
| `zip(other)` | 拉链 | 惰性 |
| `chain(other)` | 链接 | 惰性 |
| `enumerate()` | 带索引 | 惰性 |
| `peekable()` | 可窥视 | 惰性 |
| `fuse()` | 熔断（None后始终None）| 惰性 |
| `cycle()` | 循环 | 惰性 |
| `rev()` | 反转（需 DoubleEndedIterator）| 惰性 |
| `cloned()` | 克隆（&T → T）| 惰性 |
| `copied()` | 复制（&T → T，需 Copy）| 惰性 |

```rust
// 迭代器链示例
let sum: i32 = (1..=100)
    .filter(|x| x % 2 == 0)
    .map(|x| x * x)
    .sum();

// 收集到集合
let set: HashSet<_> = [1,2,3].iter().collect();

// 查找
let first_even = [1,2,3,4].iter().find(|&&x| x % 2 == 0);
```

---

## 常用 Traits 速查

### 基础 Trait

| Trait | 方法 | 说明 |
|-------|------|------|
| `Debug` | `fmt(&self, f)` | 调试输出 `{:?}` |
| `Display` | `fmt(&self, f)` | 显示输出 `{}` |
| `Clone` | `clone(&self)` | 深克隆 `.clone()` |
| `Copy` | （标记 Trait）| 位复制（隐式）|

```rust
// 派生实现
#[derive(Debug, Clone, Copy)]
struct Point { x: i32, y: i32 }

// 手动实现 Display
impl fmt::Display for Point {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({}, {})", self.x, self.y)
    }
}
```

### 转换 Trait

| Trait | 方法 | 说明 |
|-------|------|------|
| `Default` | `default()` | 默认值 |
| `From<T>` | `from(T)` | 从 T 转换（不失败）|
| `Into<T>` | `into(self)` | 转换为 T（自动派生）|
| `TryFrom<T>` | `try_from(T)` | 尝试转换 `Result` |
| `TryInto<T>` | `try_into(self)` | 尝试转换 `Result` |

```rust
let s = String::from("hello");  // From<&str>
let s: String = "hello".into(); // Into<String>

// Default
let v: Vec<i32> = Vec::default();
let v = Vec::<i32>::new();  // 等价
```

### 引用转换 Trait

| Trait | 方法 | 说明 |
|-------|------|------|
| `AsRef<T>` | `as_ref(&self)` | 转为 &T 引用 |
| `AsMut<T>` | `as_mut(&mut self)` | 转为 &mut T |
| `Borrow<T>` | `borrow(&self)` | 等价借用（Hash/Eq一致）|
| `BorrowMut<T>` | `borrow_mut(&mut self)` | 可变等价借用 |
| `ToOwned` | `to_owned(&self)` | 创建拥有值 |

```rust
fn is_hello(s: impl AsRef<str>) -> bool {
    s.as_ref() == "hello"
}
is_hello("hello");      // &str
is_hello(String::new()); // String
```

### 智能指针 Trait

| Trait | 方法 | 说明 |
|-------|------|------|
| `Deref` | `deref(&self)` | 解引用 `*x` |
| `DerefMut` | `deref_mut(&mut self)` | 可变解引用 |
| `Drop` | `drop(&mut self)` | 析构时调用 |

```rust
struct MyBox<T>(T);
impl<T> Deref for MyBox<T> {
    type Target = T;
    fn deref(&self) -> &T { &self.0 }
}
```

### 迭代 Trait

| Trait | 方法 | 说明 |
|-------|------|------|
| `Iterator` | `next()` | 产生 `Option<Item>` |
| `IntoIterator` | `into_iter()` | 转为迭代器 |
| `FromIterator` | `from_iter(iter)` | 从迭代器构建 |
| `ExactSizeIterator` | `len()` / `is_empty()` | 已知长度 |
| `DoubleEndedIterator` | `next_back()` | 双向迭代 |
| `FusedIterator` | （标记）| 保证 None 后始终 None |

```rust
// IntoIterator 实现使 for 循环可用
for item in collection { }
// 等价于
for item in collection.into_iter() { }

// 借用迭代
for item in &collection { }     // iter()
for item in &mut collection { } // iter_mut()
```

---

## 常用宏速查

### 输出宏

| 宏 | 说明 | 示例 |
|----|------|------|
| `println!` | 打印到 stdout 并换行 | `println!("Hello")` |
| `print!` | 打印到 stdout 不换行 | `print!("Loading...")` |
| `eprintln!` | 打印到 stderr 并换行 | `eprintln!("Error")` |
| `eprint!` | 打印到 stderr 不换行 | `eprint!("Warning")` |
| `format!` | 格式化到 String | `format!("{}", x)` |
| `write!` | 写入缓冲区 | `write!(buf, "{}", x)` |
| `writeln!` | 写入缓冲区换行 | `writeln!(buf, "{}", x)?` |

### 格式语法

```rust
println!("{}", value);           // 默认显示
println!("{:?}", value);         // Debug 输出
println!("{:#?}", value);        // 美化 Debug
println!("{:b}", 42);            // 二进制 101010
println!("{:o}", 42);            // 八进制 52
println!("{:x}", 42);            // 十六进制 2a
println!("{:X}", 42);            // 十六进制 2A
println!("{:e}", 1234.5);        // 科学计数 1.2345e3
println!("{:08}", 42);           // 前导零填充 00000042
println!("{:>8}", 42);           // 右对齐      42
println!("{:<8}", 42);           // 左对齐 42
println!("{:^8}", 42);           // 居中   42
println!("{:.2}", 3.14159);      // 小数位 3.14
println!("{:?}", Some(5));       // Option(5)
println!("{val}", val=5);        // 命名参数
println!("{0} {1} {0}", a, b);   // 位置参数
```

### 集合宏

| 宏 | 说明 | 示例 |
|----|------|------|
| `vec!` | 创建 Vec | `vec![1, 2, 3]` |
| `vec![val; n]` | 重复值 | `vec![0; 10]` |
| `vec![val; n]` | 重复值 | `vec![0; 10]` |

### 开发辅助宏

| 宏 | 说明 | 用途 |
|----|------|------|
| `todo!()` | 待实现标记 | 编译通过，运行 Panic |
| `unimplemented!()` | 未实现标记 | 同 todo! |
| `unreachable!()` | 不可达代码 | 安全标记 |
| `panic!()` | 触发 Panic | 错误终止 |
| `assert!(cond)` | 断言 | 测试条件 |
| `assert_eq!(a, b)` | 相等断言 | 测试相等 |
| `assert_ne!(a, b)` | 不等断言 | 测试不等 |
| `debug_assert!(c)` | 调试断言 | 仅 debug 生效 |

```rust
fn new_feature() {
    todo!("实现新功能");  // 编译通过，运行时报错
}

match value {
    Some(x) => x,
    None => unreachable!("已检查过 None"),
}
```

### 其他常用宏

| 宏 | 说明 |
|----|------|
| `include_str!(path)` | 包含文件内容为 &str |
| `include_bytes!(path)` | 包含文件内容为 &[u8] |
| `include!(path)` | 包含并编译 Rust 代码 |
| `module_path!()` | 当前模块路径 |
| `file!()` | 当前文件名 |
| `line!()` | 当前行号 |
| `column!()` | 当前列号 |
| `stringify!(tokens)` | 转为字符串字面量 |
| `concat!(...)` | 连接字符串 |
| `cfg!(condition)` | 条件编译检查 |
| `option_env!(var)` | 可选环境变量 |

---

## 快速参考表

### 类型转换表

| 来源 | 目标 | 方法 |
|------|------|------|
| `&str` | `String` | `.to_string()` / `String::from()` |
| `String` | `&str` | `.as_str()` |
| `&[T]` | `Vec<T>` | `.to_vec()` |
| `Vec<T>` | `&[T]` | 自动解引用 |
| `i32` | `f64` | `as f64` |
| `f64` | `i32` | `as i32`（截断）|
| `&str` | `i32` | `.parse::<i32>()?` |
| `i32` | `String` | `.to_string()` |

### 错误处理速查

```rust
// Result 传播
let x = may_fail()?;

// Option 转 Result
let x = opt.ok_or(Error::NotFound)?;
let x = opt.ok_or_else(|| Error::new())?;

// Result 匹配
if let Ok(v) = result { }
if let Err(e) = result { }

// unwrap 变体
let x = result.unwrap();           // 失败 panic
let x = result.expect("msg");      // 带信息 panic
let x = result.unwrap_or(default); // 或默认值
let x = result.unwrap_or_default(); // 或 Default
```

### 生命周期标注模式

```rust
&'a T        // 'a 生命周期的引用
&'a mut T    // 可变引用
&'static str // 静态生命周期（程序全程）

fn foo<'a>(x: &'a str) -> &'a str  // 输入输出同生命周期
fn foo<'a, 'b>(x: &'a str, y: &'b str) -> &'a str  // 多生命周期
```

---

> **提示**: 本速查表涵盖最常用的标准库 API。更多详情请参阅 [Rust 标准库文档](https://doc.rust-lang.org/std/)。
