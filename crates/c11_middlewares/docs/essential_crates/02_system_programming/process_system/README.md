# 进程与系统接口

> **核心库**: nix, sysinfo, signal-hook, daemonize  
> **适用场景**: 进程管理、信号处理、系统信息、守护进程

---

## 📋 核心库概览

| 库 | 用途 | 特点 | 推荐度 |
|-----|------|------|--------|
| **nix** | Unix系统接口 | 完整、类型安全 | ⭐⭐⭐⭐⭐ |
| **sysinfo** | 系统信息 | 跨平台 | ⭐⭐⭐⭐⭐ |
| **signal-hook** | 信号处理 | 异步安全 | ⭐⭐⭐⭐ |

---

## 🖥️ sysinfo - 系统信息

```rust
use sysinfo::{System, SystemExt, ProcessExt};

fn main() {
    let mut sys = System::new_all();
    sys.refresh_all();
    
    // 系统信息
    println!("Total memory: {} KB", sys.total_memory());
    println!("Used memory: {} KB", sys.used_memory());
    println!("CPU count: {}", sys.cpus().len());
    
    // 进程信息
    for (pid, process) in sys.processes() {
        println!("[{}] {} - {} KB", 
            pid, process.name(), process.memory());
    }
}
```

---

## 📡 signal-hook - 信号处理

```rust
use signal_hook::{consts::SIGINT, iterator::Signals};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let term = Arc::new(AtomicBool::new(false));
    
    signal_hook::flag::register(SIGINT, Arc::clone(&term))?;
    
    while !term.load(Ordering::Relaxed) {
        // 主循环
        std::thread::sleep(std::time::Duration::from_secs(1));
    }
    
    println!("Terminating...");
    Ok(())
}
```

---

## 🔧 nix - Unix接口

```rust
use nix::unistd::{fork, ForkResult};

fn main() {
    match unsafe { fork() } {
        Ok(ForkResult::Parent { child }) => {
            println!("Parent process, child PID: {}", child);
        }
        Ok(ForkResult::Child) => {
            println!("Child process");
        }
        Err(e) => {
            eprintln!("Fork failed: {}", e);
        }
    }
}
```

---

**文档版本**: 1.0.0  
**最后更新**: 2025-10-20

