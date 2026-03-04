# LittleFS2嵌入式文件系统形式化分析

> **主题**: 闪存优化文件系统
> **形式化框架**: 写时复制 + 幂等性 + 磨损均衡
> **参考**: littlefs2 crate (<https://github.com/nabijaczleweli/littlefs2>)

---

## 目录

- [LittleFS2嵌入式文件系统形式化分析](#littlefs2嵌入式文件系统形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 文件系统模型](#2-文件系统模型)
    - [定义 FS-1 ( 文件系统组成 )](#定义-fs-1--文件系统组成-)
    - [定义 FS-2 ( 元数据对 )](#定义-fs-2--元数据对-)
  - [3. 写时复制](#3-写时复制)
    - [定义 COW-1 ( COW语义 )](#定义-cow-1--cow语义-)
    - [定理 COW-T1 ( 原子性 )](#定理-cow-t1--原子性-)
  - [4. 幂等性](#4-幂等性)
    - [定义 IDEMPOTENT-1 ( 幂等操作 )](#定义-idempotent-1--幂等操作-)
    - [定理 IDEMPOTENT-T1 ( LittleFS幂等性 )](#定理-idempotent-t1--littlefs幂等性-)
  - [5. 磨损均衡](#5-磨损均衡)
    - [定义 WEAR-1 ( 分配算法 )](#定义-wear-1--分配算法-)
    - [定理 WEAR-T1 ( 均衡保证 )](#定理-wear-t1--均衡保证-)
  - [6. 定理与证明](#6-定理与证明)
    - [定理 FS-T1 ( 掉电安全 )](#定理-fs-t1--掉电安全-)
    - [定理 FS-T2 ( 有限RAM使用 )](#定理-fs-t2--有限ram使用-)
  - [7. 代码示例](#7-代码示例)
    - [示例1: 基本文件操作](#示例1-基本文件操作)
    - [示例2: 目录操作](#示例2-目录操作)
    - [示例3: 掉电安全写入](#示例3-掉电安全写入)

---

## 1. 引言

LittleFS专为闪存设计：

- 掉电安全（Power-loss resilience）
- 磨损均衡
- 写时复制
- 有限的RAM使用
- 无堆分配选项

---

## 2. 文件系统模型

### 定义 FS-1 ( 文件系统组成 )

$$
\text{LittleFS} = (\text{storage}, \text{cache}, \text{lookahead})
$$

### 定义 FS-2 ( 元数据对 )

LittleFS使用双元数据块实现原子更新。

$$
\text{Metadata} = \{ (M_1, M_2) \mid M_i : \text{Block} \}
$$

**更新策略**:

$$
\text{commit} : \text{new\_metadata} \to \begin{cases}
\text{erase}(M_2) \\
\text{write}(M_2, \text{new\_metadata}) \\
\text{mark}(M_2 \text{ valid}) \\
\text{mark}(M_1 \text{ invalid})
\end{cases}
$$

---

## 3. 写时复制

### 定义 COW-1 ( COW语义 )

文件修改不就地更新，而是写入新块。

$$
\text{write}(f, data) : \text{new\_block} \leftarrow \text{data} \land \text{update\_pointer}(f, \text{new\_block})
$$

### 定理 COW-T1 ( 原子性 )

文件更新是原子的（要么完全成功，要么无变化）。

$$
\text{write}(f, d) \to \text{Success} \lor \text{file}(f) = \text{file}(f)_0
$$

**证明**: 新数据写入新块，元数据原子切换。失败时旧指针仍有效。$\square$

---

## 4. 幂等性

### 定义 IDEMPOTENT-1 ( 幂等操作 )

操作可重复执行而不改变结果。

$$
\forall op \in \text{Ops}.\ op; op \equiv op
$$

### 定理 IDEMPOTENT-T1 ( LittleFS幂等性 )

所有LittleFS操作都是幂等的。

$$
\text{write}(b, d); \text{write}(b, d) \equiv \text{write}(b, d)
$$

**原因**:

- COW避免覆盖
- 重复写入相同数据到相同块无变化
- 元数据更新标记管理

---

## 5. 磨损均衡

### 定义 WEAR-1 ( 分配算法 )

LittleFS使用轮询分配实现磨损均衡。

$$
\text{allocate}() = (\text{prev} + 1) \mod N
$$

### 定理 WEAR-T1 ( 均衡保证 )

长期运行后所有块擦除次数差异$\\ ext{max\_diff} \\leq 1$

$$
\lim_{t \\to \\infty} \\frac{\\max_i \\text{erase}_i(t) - \\min_i \\text{erase}_i(t)}{\\text{avg}} \\leq \\frac{1}{N}
$$

---

## 6. 定理与证明

### 定理 FS-T1 ( 掉电安全 )

任何时刻掉电不会损坏文件系统。

$$
\forall t.\ \text{power\_loss}(t) \to \exists \text{valid\_state}.\ \text{mount}() = \text{Ok}
$$

**证明**:

- 元数据双备份保证至少一个有效
- COW确保文件数据完整性
- 幂等操作允许恢复
- 因此总能挂载到一致状态。$\square$

### 定理 FS-T2 ( 有限RAM使用 )

RAM使用与存储大小无关。

$$
\text{RAM}(\text{LittleFS}) = O(\text{cache\_size} + \text{lookahead\_size})
$$

---

## 7. 代码示例

### 示例1: 基本文件操作

```rust
use littlefs2::fs::{Filesystem, Allocation, File, OpenOptions};
use littlefs2::io::{Read, Write, Result};

fn filesystem_example<S: embedded_storage::nor_flash::NorFlash>() -> Result<()> {
    let mut alloc = Allocation::new();
    let mut storage = MyFlash::new();

    // 格式化
    Filesystem::format(&mut storage)?;

    // 挂载
    let fs = Filesystem::mount(&mut alloc, &mut storage)?;

    // 创建并写入文件
    fs.open_file_with_options_and_then(
        |opt| opt.write(true).create(true).truncate(true),
        "test.txt",
        |file| {
            file.write_all(b"Hello, LittleFS!")?;
            Ok(())
        }
    )?;

    // 读取文件
    fs.open_file_with_options_and_then(
        |opt| opt.read(true),
        "test.txt",
        |file| {
            let mut buf = [0u8; 64];
            let n = file.read(&mut buf)?;
            assert_eq!(&buf[..n], b"Hello, LittleFS!");
            Ok(())
        }
    )?;

    Ok(())
}
```

### 示例2: 目录操作

```rust
use littlefs2::fs::Dir;
use littlefs2::path::PathBuf;

fn directory_example(fs: &Filesystem<MyFlash>) -> Result<()> {
    // 创建目录
    fs.create_dir("/config")?;
    fs.create_dir("/data")?;

    // 遍历目录
    fs.read_dir_and_then("/", |dir| {
        for entry in dir {
            let entry = entry?;
            defmt::info!("{}: {:?}", entry.file_name(), entry.file_type());
        }
        Ok(())
    })?;

    // 递归删除
    fs.remove_dir_all("/data")?;

    Ok(())
}
```

### 示例3: 掉电安全写入

```rust
fn robust_write(fs: &Filesystem<MyFlash>, path: &str, data: &[u8]) -> Result<()> {
    // 使用临时文件
    let temp_path = PathBuf::from(path).with_extension("tmp");

    // 写入临时文件
    fs.open_file_with_options_and_then(
        |opt| opt.write(true).create(true).truncate(true),
        &temp_path,
        |file| {
            file.write_all(data)?;
            file.sync()?;  // 确保写入存储
            Ok(())
        }
    )?;

    // 原子重命名
    fs.rename(&temp_path, path)?;

    Ok(())
}
```

---

**维护者**: Rust Embedded Formal Methods Team
**创建日期**: 2026-03-05
**状态**: ✅ 已对齐
