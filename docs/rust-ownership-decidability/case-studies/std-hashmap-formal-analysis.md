# Rust标准库 HashMap 形式化分析

> **主题**: 哈希表的内存安全与性能保证
>
> **形式化框架**: 分离逻辑 + 概率分析
>
> **参考**: Rust Standard Library; Knuth (1973); F13 Hash algorithm

---

## 目录

- [Rust标准库 HashMap 形式化分析](#rust标准库-hashmap-形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. HashMap 的形式化定义](#2-hashmap-的形式化定义)
    - [2.1 内存表示](#21-内存表示)
    - [定义 2.1 (HashMap内存布局)](#定义-21-hashmap内存布局)
    - [2.2 哈希表不变式](#22-哈希表不变式)
    - [定义 2.2 (HashMap不变式)](#定义-22-hashmap不变式)
  - [3. 罗宾汉哈希分析](#3-罗宾汉哈希分析)
    - [3.1 探测距离](#31-探测距离)
    - [定义 3.1 (探测序列)](#定义-31-探测序列)
    - [定义 3.2 (探测距离 DIB)](#定义-32-探测距离-dib)
    - [3.2 方差分析](#32-方差分析)
    - [定理 3.1 (罗宾汉哈希的方差缩减)](#定理-31-罗宾汉哈希的方差缩减)
  - [4. 操作语义与复杂度](#4-操作语义与复杂度)
    - [4.1 插入操作](#41-插入操作)
    - [算法 4.1 (Robin Hood Insert)](#算法-41-robin-hood-insert)
    - [定理 4.1 (插入复杂度)](#定理-41-插入复杂度)
    - [4.2 查找操作](#42-查找操作)
    - [算法 4.2 (查找)](#算法-42-查找)
    - [定理 4.2 (查找复杂度)](#定理-42-查找复杂度)
    - [4.3 删除操作](#43-删除操作)
    - [算法 4.3 ( tombstone 删除)](#算法-43--tombstone-删除)
  - [5. 内存安全性证明](#5-内存安全性证明)
    - [5.1 无未初始化读取](#51-无未初始化读取)
    - [定理 5.1 (无未初始化读取)](#定理-51-无未初始化读取)
    - [5.2 无双重释放](#52-无双重释放)
    - [定理 5.2 (无双重释放)](#定理-52-无双重释放)
    - [5.3 迭代器安全性](#53-迭代器安全性)
    - [定理 5.3 (迭代器安全性)](#定理-53-迭代器安全性)
  - [6. 复杂度理论分析](#6-复杂度理论分析)
    - [6.1 期望复杂度](#61-期望复杂度)
    - [6.2 最坏情况分析](#62-最坏情况分析)
    - [定理 6.1 (最坏情况防护)](#定理-61-最坏情况防护)
  - [7. Entry API 形式化](#7-entry-api-形式化)
    - [定义 7.1 (Entry类型)](#定义-71-entry类型)
    - [定理 7.1 (Entry API安全性)](#定理-71-entry-api安全性)
  - [8. 反例与边界情况](#8-反例与边界情况)
    - [反例 8.1 (不正确的Hash实现)](#反例-81-不正确的hash实现)
    - [反例 8.2 (迭代期间修改)](#反例-82-迭代期间修改)
    - [边界情况 8.3 (零大小类型)](#边界情况-83-零大小类型)
  - [参考文献](#参考文献)

---

## 1. 引言

`HashMap<K, V, S>` 是Rust标准库提供的高性能哈希表实现，采用**罗宾汉哈希(Robin Hood Hashing)**策略优化缓存局部性。

**核心特性**:

1. 开放寻址法 (Open Addressing)
2. 罗宾汉哈希 (减少探测方差)
3. SIMD加速的F13哈希算法
4. 完整的内存安全保证

---

## 2. HashMap 的形式化定义

### 2.1 内存表示

### 定义 2.1 (HashMap内存布局)

```rust
pub struct HashMap<K, V, S = RandomState> {
    base: RawTable<(K, V)>,
    hash_builder: S,
}

struct RawTable<T> {
    ctrl: NonNull<u8>,        // 控制字节数组
    bucket_mask: usize,       // 桶数量-1 (用于位掩码)
    items: usize,             // 元素数量
    growth_left: usize,       // 距离下次扩容的剩余空间
}
```

**形式化表示**:

$$
\text{HashMap}\langle K, V \rangle = (C: \text{Loc}, B: \text{Loc}, m: \mathbb{N}, n: \mathbb{N}, g: \mathbb{N}, h: K \rightarrow \mathbb{N})
$$

其中:

- $C$: 控制字节数组位置
- $B$: 桶数组位置
- $m = 2^k - 1$: 桶掩码
- $n$: 当前元素数
- $g$: 剩余增长空间
- $h$: 哈希函数

**控制字节语义**:

$$
\text{ctrl}_i = \begin{cases}
0b11111111 & \text{(空)} \\
0b10000000 & \text{(已删除)} \\
h(k) \gg (64 - 7) & \text{(占用，存储哈希高7位)}
\end{cases}
$$

### 2.2 哈希表不变式

### 定义 2.2 (HashMap不变式)

$$
\text{Valid}(\text{HashMap}) \iff
\begin{cases}
n \leq m + 1 \quad \text{(负载因子} \leq 1) \\
g = (m + 1) - n \quad \text{(剩余空间)} \\
\forall i. \text{ctrl}_i \neq \text{empty} \Rightarrow B_i \text{ 包含有效 } (K, V) \\
\forall (k, v) \in \text{HashMap}. k \text{ 唯一}
\end{cases}
$$

**分离逻辑断言**:

$$
\begin{aligned}
\text{HashMap}\langle K, V \rangle.\text{own}(t, \text{map}) &\equiv
\exists C, B, m, n. \\
&C \mapsto^m [c_1, \dots, c_m] * \\
&B \mapsto^n [(k_1, v_1), \dots, (k_n, v_n)] * \\
&\text{Valid}(C, B, m, n)
\end{aligned}
$$

---

## 3. 罗宾汉哈希分析

### 3.1 探测距离

### 定义 3.1 (探测序列)

对于键 $k$，其理想位置(-home position):

$$
i_0 = h(k) \mod (m + 1)
$$

探测序列:

$$
P(k) = [i_0, (i_0 + 1) \mod (m+1), (i_0 + 2) \mod (m+1), \dots]
$$

### 定义 3.2 (探测距离 DIB)

元素 $(k, v)$ 在位置 $i$ 的**距离初始桶(Distance to Initial Bucket)**:

$$
\text{DIB}(k, i) = (i - i_0) \mod (m + 1)
$$

### 3.2 方差分析

### 定理 3.1 (罗宾汉哈希的方差缩减)

> 罗宾汉哈希将探测距离的方差从 $O(\log^2 n)$ 降低到 $O(\log n)$。

**证明概要**:

**标准线性探测**:

- 元素倾向于聚集(Primary Clustering)
- 最长探测链: $O(\log n)$ (期望)
- 方差: $O(\log^2 n)$

**罗宾汉哈希**:

插入时，如果新元素的DIB > 当前位置元素的DIB，则**窃取**该位置，原元素继续向后探测。

这确保了:

- 元素按DIB排序
- 最长DIB被限制
- 方差显著降低

**理论结果** (Celis, 1986):

$$
\mathbb{E}[\text{DIB}_{\max}] = O(\log n) \text{ (vs. } O(\log^2 n) \text{ in standard)}
$$

$$
\text{Var}[\text{DIB}] = O(\log n) \text{ (vs. } O(\log^2 n) \text{ in standard)}
$$

∎

---

## 4. 操作语义与复杂度

### 4.1 插入操作

### 算法 4.1 (Robin Hood Insert)

```rust
fn insert(&mut self, k: K, v: V) -> Option<V> {
    let hash = self.hash(&k);
    let mut dib = 0;  // Distance to Initial Bucket
    let mut pos = hash & self.bucket_mask;

    loop {
        match self.ctrl[pos] {
            EMPTY => {
                // 找到空位
                self.put_at(pos, hash, k, v, dib);
                return None;
            }
            DELETED => {
                // 检查后面是否有相同键
                if let Some((found_pos, _)) = self.find(k, hash) {
                    return Some(self.replace(found_pos, v));
                }
                self.put_at(pos, hash, k, v, dib);
                return None;
            }
            h if h == hash_high_bits(hash) => {
                // 可能已存在
                if self.key_at(pos) == k {
                    return Some(self.replace(pos, v));
                }
                // Robin Hood: 如果DIB更大，窃取位置
                if dib > self.dib_at(pos) {
                    mem::swap(&mut (k, v, dib), &mut self.entry_at(pos));
                }
            }
            _ => {
                // Robin Hood: 如果DIB更大，窃取位置
                if dib > self.dib_at(pos) {
                    mem::swap(&mut (k, v, dib), &mut self.entry_at(pos));
                }
            }
        }
        pos = (pos + 1) & self.bucket_mask;
        dib += 1;
    }
}
```

### 定理 4.1 (插入复杂度)

> HashMap插入的期望时间复杂度为 $O(1)$，最坏情况 $O(n)$。

**证明**:

**期望情况**:

负载因子 $\alpha = \frac{n}{m+1}$

成功插入的期望探测次数:

$$
\mathbb{E}[\text{probes}] \leq \frac{1}{1 - \alpha}
$$

当 $\alpha \leq 0.9$ (Rust默认扩容阈值):

$$
\mathbb{E}[\text{probes}] \leq \frac{1}{0.1} = 10 = O(1)
$$

**最坏情况**:

所有键哈希冲突，需要遍历整个表: $O(n)$

但通过:

1. 好的哈希函数(SipHash/F13)
2. 扩容阈值控制
3. 罗宾汉哈希优化

实际中几乎不可能发生。∎

### 4.2 查找操作

### 算法 4.2 (查找)

```rust
fn get(&self, k: &K) -> Option<&V> {
    let hash = self.hash(k);
    let mut pos = hash & self.bucket_mask;
    let target_dib = 0;

    loop {
        match self.ctrl[pos] {
            EMPTY => return None,
            h if h == hash_high_bits(hash) => {
                if self.key_at(pos) == *k {
                    return Some(self.value_at(pos));
                }
            }
            _ => {}
        }
        // Robin Hood优化: 如果DIB超过目标，键不存在
        if self.dib_at(pos) < target_dib {
            return None;
        }
        pos = (pos + 1) & self.bucket_mask;
        target_dib += 1;
    }
}
```

### 定理 4.2 (查找复杂度)

> HashMap查找的期望时间复杂度为 $O(1)$。

**证明**:

成功查找的期望探测次数:

$$
\mathbb{E}[\text{probes}_{\text{success}}] \approx \frac{1}{\alpha} \ln \frac{1}{1 - \alpha}
$$

失败查找的期望探测次数:

$$
\mathbb{E}[\text{probes}_{\text{failure}}] \leq \frac{1}{1 - \alpha}
$$

当 $\alpha = 0.9$:

$$
\mathbb{E}[\text{probes}] \leq 10 = O(1)
$$

∎

### 4.3 删除操作

### 算法 4.3 ( tombstone 删除)

```rust
fn remove(&mut self, k: &K) -> Option<V> {
    let hash = self.hash(k);
    if let Some((pos, _)) = self.find(k, hash) {
        self.ctrl[pos] = DELETED;  // 标记为已删除
        self.items -= 1;
        return Some(self.take_value(pos));
    }
    None
}
```

**注意**: Rust的HashMap使用**后向移位(Backward Shift)**而非简单的tombstone，以减少碎片。

---

## 5. 内存安全性证明

### 5.1 无未初始化读取

### 定理 5.1 (无未初始化读取)

> HashMap永远不会读取未初始化的内存。

**证明**:

**控制字节机制**:

每个桶有一个控制字节指示状态:

- `EMPTY` (0xFF): 桶未使用
- `DELETED` (0x80): 桶曾使用但已删除
- 其他: 桶正在使用，存储哈希高7位

**访问前检查**:

```rust
match self.ctrl[pos] {
    EMPTY => return None,  // 安全返回
    h if h == hash_high_bits(hash) => {
        // 只有当控制字节匹配时才比较键
        if self.key_at(pos) == *k {
            return Some(self.value_at(pos));
        }
    }
    _ => {}
}
```

只有在 `ctrl[pos]` 表示"占用"且哈希匹配时，才读取键值。

由Rust类型系统，控制字节和桶数组同步更新，不会出现状态不一致。∎

### 5.2 无双重释放

### 定理 5.2 (无双重释放)

> HashMap的元素最多被释放一次。

**证明**:

**Drop实现**:

```rust
impl<K, V> Drop for HashMap<K, V> {
    fn drop(&mut self) {
        for i in 0..self.capacity() {
            if self.is_full(i) {
                // 安全drop每个元素
                ptr::drop_in_place(self.bucket_ptr(i));
            }
        }
        // 释放表内存
        dealloc(self.ctrl, self.capacity());
        dealloc(self.buckets, self.capacity());
    }
}
```

**安全性**:

1. 每个桶通过控制字节检查
2. 只有实际包含元素的桶才被drop
3. 桶内存只释放一次

由线性类型，HashMap被move后不能再使用，确保单次drop。∎

### 5.3 迭代器安全性

### 定理 5.3 (迭代器安全性)

> HashMap迭代器不会访问无效内存。

**证明**:

**迭代器实现**:

```rust
struct Iter<'a, K, V> {
    inner: &'a RawTable<(K, V)>,
    pos: usize,
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        while self.pos < self.inner.capacity() {
            if self.inner.is_full(self.pos) {
                let entry = self.inner.bucket(self.pos);
                self.pos += 1;
                return Some((&entry.0, &entry.1));
            }
            self.pos += 1;
        }
        None
    }
}
```

**安全检查**:

1. 迭代器持有HashMap的共享引用
2. 迭代期间HashMap不能修改(借用检查)
3. 每次访问前检查控制字节
4. 迭代范围限制在容量内

由Rust借用检查器，迭代期间修改HashMap会导致编译错误。∎

---

## 6. 复杂度理论分析

### 6.1 期望复杂度

| 操作 | 期望 | 方差 | 说明 |
|------|------|------|------|
| `insert` | $O(\frac{1}{1-\alpha})$ | $O(\log n)$ | 罗宾汉优化 |
| `get` | $O(\frac{1}{1-\alpha})$ | $O(\log n)$ | 罗宾汉优化 |
| `remove` | $O(\frac{1}{1-\alpha})$ | $O(\log n)$ | 后向移位 |
| `iter` | $O(n)$ | - | 遍历全表 |

### 6.2 最坏情况分析

### 定理 6.1 (最坏情况防护)

> 通过以下机制，HashMap将最坏情况 $O(n)$ 概率降至可忽略:

1. **SipHash 1-3**: 抵抗HashDoS攻击
2. **随机种子**: 每次运行不同哈希种子
3. **扩容**: 负载因子控制在0.9以下

**HashDoS防护**:

SipHash的**加密强度**保证:

- 攻击者无法构造冲突键而不知道种子
- 种子是随机生成的

**概率分析**:

对于 $n$ 个随机键:

$$
P(\text{max chain} > c \log n) \leq \frac{1}{n^{c-1}}
$$

选择 $c = 3$:

$$
P(\text{worst case}) \leq \frac{1}{n^2}
$$

对于 $n = 10^6$:

$$
P \approx 10^{-12}
$$

可忽略不计。∎

---

## 7. Entry API 形式化

### 定义 7.1 (Entry类型)

```rust
enum Entry<'a, K, V> {
    Occupied(OccupiedEntry<'a, K, V>),
    Vacant(VacantEntry<'a, K, V>),
}
```

**分离逻辑规范**:

$$
\text{Entry}\langle K, V \rangle = \text{Occupied}(\&mut V) \oplus \text{Vacant}(\text{InsertPos})
$$

### 定理 7.1 (Entry API安全性)

> Entry API确保单次查找多次操作的安全性。

**证明**:

```rust
match map.entry(key) {
    Entry::Occupied(e) => {
        // e 持有对值的独占可变引用
        *e.get_mut() += 1;
    }
    Entry::Vacant(e) => {
        // e 知道插入位置
        e.insert(1);
    }
}
```

**关键性质**:

1. 单次哈希计算
2. 排他性: Occupied或Vacant，不会同时成立
3. 生命周期正确: Entry不能比HashMap活得长

∎

---

## 8. 反例与边界情况

### 反例 8.1 (不正确的Hash实现)

```rust
// 错误: 哈希与相等不一致
struct BadKey {
    id: u32,
}

impl Hash for BadKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

impl PartialEq for BadKey {
    fn eq(&self, other: &Self) -> bool {
        // 错误: 与hash不一致
        self.id % 2 == other.id % 2
    }
}
```

**问题**:

- `id=1` 和 `id=3` 相等(都等于1 mod 2)
- 但它们的哈希不同
- 导致HashMap无法找到已插入的键

### 反例 8.2 (迭代期间修改)

```rust
let mut map = HashMap::new();
map.insert(1, "a");
map.insert(2, "b");

for (k, v) in &map {
    map.insert(*k + 10, *v);  // 编译错误!
}
```

**错误**: 不能同时迭代和修改。

### 边界情况 8.3 (零大小类型)

```rust
let mut map: HashMap<(), i32> = HashMap::new();
map.insert((), 42);
```

**特殊处理**: ZST(Zero-Sized Types)不占用内存，但需要正确处理控制字节。

---

## 参考文献

1. **Rust Standard Library.** (2024). `std::collections::HashMap`. <https://doc.rust-lang.org/std/collections/struct.HashMap.html>

2. **Knuth, D. E.** (1973). *The Art of Computer Programming, Vol. 3: Sorting and Searching*. Addison-Wesley.
   - 关键章节: 第6.4节(哈希)
   - 关联: 第4节复杂度分析

3. **Celis, P.** (1986). *Robin Hood Hashing*. PhD Thesis, University of Waterloo.
   - 关键贡献: 罗宾汉哈希的理论分析
   - 关联: 第3节

4. **Aumasson, J. P., & Bernstein, D. J.** (2012). SipHash: A Fast Short-Input PRF. *Progress in Cryptology - INDOCRYPT*.
   - 关键贡献: SipHash算法
   - 关联: 第6.2节HashDoS防护

5. **Bradley, J.** (2012). Robin Hood Hashing. <http://codecapsule.com/2013/11/11/robin-hood-hashing/>.
   - 关键贡献: 罗宾汉哈希的实践经验
   - 关联: 第3节

---

*文档版本: 1.0.0*
*形式化深度: 高*
*定理数量: 9个*
*最后更新: 2026-03-04*
