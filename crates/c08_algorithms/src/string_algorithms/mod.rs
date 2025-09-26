//! 字符串算法：KMP 与 Rabin-Karp（同步 / 异步）

#[cfg(feature = "with-aho")]
use aho_corasick::AhoCorasick;
use anyhow::Result;

// =========================
// KMP
// =========================

/// 计算前缀函数（最长相等真前后缀）
fn compute_lps(pat: &[u8]) -> Vec<usize> {
    let mut lps = vec![0usize; pat.len()];
    let (mut len, mut i) = (0usize, 1usize);
    while i < pat.len() {
        if pat[i] == pat[len] {
            len += 1;
            lps[i] = len;
            i += 1;
        } else if len != 0 {
            len = lps[len - 1];
        } else {
            lps[i] = 0;
            i += 1;
        }
    }
    lps
}

/// KMP 搜索：返回所有匹配的起始下标
pub fn kmp_search(text: &str, pattern: &str) -> Vec<usize> {
    if pattern.is_empty() {
        return (0..=text.len()).collect();
    }
    let t = text.as_bytes();
    let p = pattern.as_bytes();
    let lps = compute_lps(p);
    let (mut i, mut j) = (0usize, 0usize);
    let mut res = Vec::new();
    while i < t.len() {
        if t[i] == p[j] {
            i += 1;
            j += 1;
            if j == p.len() {
                res.push(i - j);
                j = lps[j - 1];
            }
        } else if j != 0 {
            j = lps[j - 1];
        } else {
            i += 1;
        }
    }
    res
}

pub async fn kmp_search_async(text: String, pattern: String) -> Result<Vec<usize>> {
    Ok(tokio::task::spawn_blocking(move || kmp_search(&text, &pattern)).await?)
}

// =========================
// Rabin-Karp（滚动哈希，简化 ASCII）
// =========================

/// Rabin-Karp 搜索：返回所有匹配的起始下标
pub fn rabin_karp_search(text: &str, pattern: &str) -> Vec<usize> {
    let n = text.len();
    let m = pattern.len();
    if m == 0 { return (0..=n).collect(); }
    if m > n {
        return Vec::new();
    }

    let base: u64 = 256; // ASCII 基
    let modp: u64 = 1_000_000_007; // 大素数

    let tb = text.as_bytes();
    let pb = pattern.as_bytes();

    let mut h: u64 = 1; // base^(m-1) % modp
    for _ in 1..m {
        h = (h * base) % modp;
    }

    let mut th: u64 = 0; // text 窗口 hash
    let mut ph: u64 = 0; // pattern hash
    for i in 0..m {
        th = (th * base + tb[i] as u64) % modp;
        ph = (ph * base + pb[i] as u64) % modp;
    }

    let mut res = Vec::new();
    for i in 0..=n - m {
        if th == ph {
            // 避免碰撞，做一次直接比较
            if &tb[i..i + m] == pb {
                res.push(i);
            }
        }
        if i < n - m {
            let lead = (tb[i] as u64 * h) % modp;
            th = (th + modp + modp - lead) % modp; // 去掉最高位
            th = (th * base + tb[i + m] as u64) % modp; // 加入新位
        }
    }
    res
}

pub async fn rabin_karp_search_async(text: String, pattern: String) -> Result<Vec<usize>> {
    Ok(tokio::task::spawn_blocking(move || rabin_karp_search(&text, &pattern)).await?)
}

// =========================
// Trie 与 Aho-Corasick 多模式匹配
// =========================

#[derive(Default)]
pub struct TrieNode {
    next: std::collections::HashMap<u8, usize>,
    out: Vec<usize>,
    fail: usize,
}

#[derive(Default)]
pub struct Trie {
    nodes: Vec<TrieNode>,
}

impl Trie {
    pub fn new() -> Self {
        Self {
            nodes: vec![TrieNode::default()],
        }
    }

    pub fn insert(&mut self, pattern: &[u8], id: usize) {
        let mut s = 0usize;
        for &ch in pattern {
            let nxt = if let Some(&v) = self.nodes[s].next.get(&ch) { v } else {
                let v = self.nodes.len();
                self.nodes[s].next.insert(ch, v);
                self.nodes.push(TrieNode::default());
                v
            };
            s = nxt;
        }
        self.nodes[s].out.push(id);
    }

    pub fn build_automaton(&mut self) {
        use std::collections::VecDeque;
        let mut q = VecDeque::new();
        for (&ch, &v) in self.nodes[0].next.clone().iter() {
            self.nodes[v].fail = 0;
            q.push_back(v);
            // 保证根缺边填充到根
            self.nodes[0].next.entry(ch).or_insert(v);
        }
        while let Some(u) = q.pop_front() {
            let fail_u = self.nodes[u].fail;
            let outs = self.nodes[fail_u].out.clone();
            // 继承输出
            for id in outs {
                if !self.nodes[u].out.contains(&id) {
                    self.nodes[u].out.push(id);
                }
            }
            let keys: Vec<u8> = self.nodes[u].next.keys().copied().collect();
            for ch in keys {
                let v = self.nodes[u].next[&ch];
                // 计算 fail 指针
                let mut f = fail_u;
                while f != 0 && !self.nodes[f].next.contains_key(&ch) {
                    f = self.nodes[f].fail;
                }
                let to = *self.nodes[f].next.get(&ch).unwrap_or(&0);
                self.nodes[v].fail = to;
                q.push_back(v);
            }
        }
    }

    /// Aho-Corasick 匹配，返回 (起始位置, 模式ID)
    pub fn ac_search(&self, text: &[u8], patterns: &[Vec<u8>]) -> Vec<(usize, usize)> {
        let mut res = Vec::new();
        let mut s = 0usize;
        for (i, &ch) in text.iter().enumerate() {
            let mut cur = s;
            while cur != 0 && !self.nodes[cur].next.contains_key(&ch) {
                cur = self.nodes[cur].fail;
            }
            s = *self.nodes[cur].next.get(&ch).unwrap_or(&0);
            for &pid in &self.nodes[s].out {
                let m = patterns[pid].len();
                if i + 1 >= m {
                    res.push((i + 1 - m, pid));
                }
            }
        }
        res
    }

    /// 返回只读节点迭代器视图（示例 API，Edition 2024：返回位置 impl Iterator）
    pub fn nodes_iter(&self) -> impl Iterator<Item = &TrieNode> {
        self.nodes.iter()
    }
}

pub fn build_trie(patterns: &[Vec<u8>]) -> Trie {
    let mut trie = Trie::new();
    for (id, p) in patterns.iter().enumerate() {
        trie.insert(p, id);
    }
    trie.build_automaton();
    trie
}

pub async fn ac_search_async(text: String, patterns: Vec<String>) -> Result<Vec<(usize, usize)>> {
    Ok(tokio::task::spawn_blocking(move || {
        let pats: Vec<Vec<u8>> = patterns.iter().map(|s| s.as_bytes().to_vec()).collect();
        let trie = build_trie(&pats);
        trie.ac_search(text.as_bytes(), &pats)
    })
    .await?)
}

#[cfg(feature = "with-aho")]
pub fn aho_search(text: &str, patterns: &[&str]) -> Vec<(usize, usize)> {
    let ac = AhoCorasick::new(patterns).unwrap();
    let mut res = Vec::new();
    for mat in ac.find_iter(text) {
        res.push((mat.start(), mat.pattern().as_usize()));
    }
    res
}

// =========================
// Z-Algorithm（线性时间前缀匹配）与 Suffix Array + Kasai
// =========================

/// 计算 Z 数组：`z[i]` 为 `s` 与 `s[i..]` 的最长公共前缀长度
pub fn z_algorithm(s: &str) -> Vec<usize> {
    let a = s.as_bytes();
    let n = a.len();
    let mut z = vec![0usize; n];
    let (mut l, mut r) = (0usize, 0usize);
    for i in 1..n {
        if i <= r {
            z[i] = (r - i + 1).min(z[i - l]);
        }
        while i + z[i] < n && a[z[i]] == a[i + z[i]] {
            z[i] += 1;
        }
        if i + z[i] - 1 > r {
            l = i;
            r = i + z[i] - 1;
        }
    }
    if n > 0 {
        z[0] = n;
    }
    z
}

/// 使用 Z-Algorithm 搜索 `pattern` 在 `text` 中的所有出现位置
pub fn z_search(text: &str, pattern: &str) -> Vec<usize> {
    if pattern.is_empty() {
        return (0..=text.len()).collect();
    }
    let sep = b'\x01'; // 取一个极小可能出现在文本中的分隔符（示例）
    let s = format!("{}{}{}", pattern, sep as char, text);
    let z = z_algorithm(&s);
    let m = pattern.len();
    let mut res = Vec::new();
    for (i, &v) in z.iter().enumerate().skip(m + 1) {
        if v == m {
            res.push(i - (m + 1));
        }
    }
    res
}

pub async fn z_search_async(text: String, pattern: String) -> Result<Vec<usize>> {
    Ok(tokio::task::spawn_blocking(move || z_search(&text, &pattern)).await?)
}

/// 构建 Suffix Array（SA-IS 略，使用 O(n log n) 朴素倍增法）
pub fn suffix_array(text: &str) -> Vec<usize> {
    let n = text.len();
    let s = text.as_bytes();
    let mut sa: Vec<usize> = (0..n).collect();
    let mut rank: Vec<i32> = s.iter().map(|&c| c as i32).collect();
    let mut tmp = vec![0i32; n];
    let mut k = 1usize;
    while k < n {
        sa.sort_by_key(|&i| (rank[i], if i + k < n { rank[i + k] } else { -1 }));
        tmp[sa[0]] = 0;
        for i in 1..n {
            let a = sa[i - 1];
            let b = sa[i];
            let prev = (rank[a], if a + k < n { rank[a + k] } else { -1 });
            let curr = (rank[b], if b + k < n { rank[b + k] } else { -1 });
            tmp[b] = tmp[a] + if curr > prev { 1 } else { 0 };
        }
        for i in 0..n {
            rank[i] = tmp[i];
        }
        if rank[sa[n - 1]] == (n as i32 - 1) {
            break;
        }
        k <<= 1;
    }
    sa
}

/// 构建 LCP（Kasai），与 SA 对应
pub fn lcp_kasai(text: &str, sa: &[usize]) -> Vec<usize> {
    let n = text.len();
    let s = text.as_bytes();
    let mut rank = vec![0usize; n];
    for i in 0..n {
        rank[sa[i]] = i;
    }
    let mut lcp = vec![0usize; n];
    let mut h = 0usize;
    for i in 0..n {
        let r = rank[i];
        if r > 0 {
            let j = sa[r - 1];
            while i + h < n && j + h < n && s[i + h] == s[j + h] {
                h += 1;
            }
            lcp[r] = h;
            h = h.saturating_sub(1);
        }
    }
    lcp
}

// =========================
// Manacher 最长回文子串（线性时间）
// =========================

pub fn manacher_longest_palindrome(s: &str) -> (usize, usize) {
    // 返回 (start, length)
    if s.is_empty() {
        return (0, 0);
    }
    let bytes = s.as_bytes();
    // 扩展字符串为 T = ^#a#b#...#$
    let mut t = Vec::with_capacity(bytes.len() * 2 + 3);
    t.push(b'^');
    t.push(b'#');
    for &ch in bytes {
        t.push(ch);
        t.push(b'#');
    }
    t.push(b'$');
    let n = t.len();
    let mut p = vec![0usize; n];
    let (mut center, mut right) = (0usize, 0usize);
    for i in 1..n - 1 {
        let mirror = {
            let m = (2 * center) as isize - (i as isize);
            if m >= 0 { m as usize } else { 0 }
        };
        if i < right {
            p[i] = p[mirror].min(right - i);
        }
        while {
            let left_idx = i.checked_sub(1 + p[i]);
            let right_idx = i + 1 + p[i];
            match (left_idx, right_idx < n) {
                (Some(l), true) => t[right_idx] == t[l],
                _ => false,
            }
        } {
            p[i] += 1;
        }
        if i + p[i] > right {
            center = i;
            right = i + p[i];
        }
    }
    let (mut max_len, mut center_idx) = (0usize, 0usize);
    for i in 1..n - 1 {
        if p[i] > max_len {
            max_len = p[i];
            center_idx = i;
        }
    }
    let start = (center_idx - max_len) / 2; // 映射回原串索引
    (start, max_len)
}

pub async fn manacher_longest_palindrome_async(s: String) -> Result<(usize, usize)> {
    Ok(tokio::task::spawn_blocking(move || manacher_longest_palindrome(&s)).await?)
}

// =========================
// Boyer–Moore–Horspool 子串搜索
// =========================

pub fn bmh_search(text: &str, pattern: &str) -> Vec<usize> {
    let n = text.len();
    let m = pattern.len();
    if m == 0 {
        return (0..=n).collect();
    }
    if m > n {
        return Vec::new();
    }
    let tb = text.as_bytes();
    let pb = pattern.as_bytes();
    let mut shift = [m; 256];
    for i in 0..m - 1 {
        shift[pb[i] as usize] = m - 1 - i;
    }
    let mut res = Vec::new();
    let mut i = 0usize;
    while i + m <= n {
        let mut j = (m - 1) as isize;
        while j >= 0 && pb[j as usize] == tb[i + j as usize] {
            j -= 1;
        }
        if j < 0 {
            res.push(i);
            i += 1;
        } else {
            i += shift[tb[i + m - 1] as usize];
        }
    }
    res
}

pub async fn bmh_search_async(text: String, pattern: String) -> Result<Vec<usize>> {
    Ok(tokio::task::spawn_blocking(move || bmh_search(&text, &pattern)).await?)
}

// =========================
// 后缀自动机 Suffix Automaton（SAM）
// =========================

#[derive(Clone)]
pub struct SamState {
    pub next: std::collections::HashMap<u8, usize>,
    pub link: isize,
    pub len: usize,
}

#[derive(Clone)]
pub struct SuffixAutomaton {
    pub st: Vec<SamState>,
    pub last: usize,
}

impl Default for SuffixAutomaton {
    fn default() -> Self {
        Self::new()
    }
}

impl SuffixAutomaton {
    pub fn new() -> Self {
        Self {
            st: vec![SamState {
                next: std::collections::HashMap::new(),
                link: -1,
                len: 0,
            }],
            last: 0,
        }
    }
    pub fn extend(&mut self, ch: u8) {
        let cur = self.st.len();
        self.st.push(SamState {
            next: std::collections::HashMap::new(),
            link: 0,
            len: self.st[self.last].len + 1,
        });
        let mut p = self.last as isize;
        while p >= 0 && !self.st[p as usize].next.contains_key(&ch) {
            self.st[p as usize].next.insert(ch, cur);
            p = self.st[p as usize].link;
        }
        if p == -1 {
            self.st[cur].link = 0;
        } else {
            let q = self.st[p as usize].next[&ch];
            if self.st[p as usize].len + 1 == self.st[q].len {
                self.st[cur].link = q as isize;
            } else {
                let clone = self.st.len();
                self.st.push(SamState {
                    next: self.st[q].next.clone(),
                    link: self.st[q].link,
                    len: self.st[p as usize].len + 1,
                });
                while p >= 0 && self.st[p as usize].next.get(&ch) == Some(&q) {
                    self.st[p as usize].next.insert(ch, clone);
                    p = self.st[p as usize].link;
                }
                self.st[q].link = clone as isize;
                self.st[cur].link = clone as isize;
            }
        }
        self.last = cur;
    }
    pub fn build_from_str(s: &str) -> Self {
        let mut sam = Self::new();
        for &b in s.as_bytes() {
            sam.extend(b);
        }
        sam
    }
    pub fn count_distinct_substrings(&self) -> usize {
        let mut total = 0usize;
        for i in 1..self.st.len() {
            let link_len = if self.st[i].link >= 0 {
                self.st[self.st[i].link as usize].len
            } else {
                0
            };
            total += self.st[i].len - link_len;
        }
        total
    }
    pub fn longest_common_substring_len(&self, t: &str) -> usize {
        let mut v = 0usize;
        let mut l = 0usize;
        let mut best = 0usize;
        for &ch in t.as_bytes() {
            if let Some(&to) = self.st[v].next.get(&ch) {
                v = to;
                l += 1;
            } else {
                while v != 0 && !self.st[v].next.contains_key(&ch) {
                    v = self.st[v].link as usize;
                }
                if let Some(&to) = self.st[v].next.get(&ch) {
                    l = self.st[v].len + 1;
                    v = to;
                } else {
                    l = 0;
                    v = 0;
                }
            }
            if l > best {
                best = l;
            }
        }
        best
    }
}

pub async fn sam_build_and_count_async(s: String) -> Result<(SuffixAutomaton, usize)> {
    Ok(tokio::task::spawn_blocking(move || {
        let sam = SuffixAutomaton::build_from_str(&s);
        let cnt = sam.count_distinct_substrings();
        (sam, cnt)
    })
    .await?)
}
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_kmp() {
        let text = "ababcabcabababd";
        let pat = "ababd";
        let r = kmp_search(text, pat);
        assert_eq!(r, vec![10]);
    }

    #[test]
    fn test_rk() {
        let text = "abracadabra";
        let pat = "abra";
        let r = rabin_karp_search(text, pat);
        assert_eq!(r, vec![0, 7]);
    }

    #[test]
    fn test_async_wraps() {
        let rt = tokio::runtime::Runtime::new().unwrap();
        let r = rt.block_on(async { kmp_search_async("aaaaa".into(), "aa".into()).await.unwrap() });
        assert_eq!(r, vec![0, 1, 2, 3]);
        let r2 = rt.block_on(async {
            rabin_karp_search_async("aaaaa".into(), "aa".into())
                .await
                .unwrap()
        });
        assert_eq!(r2, vec![0, 1, 2, 3]);
    }

    #[test]
    fn test_trie_ac() {
        let pats = vec![
            b"he".to_vec(),
            b"she".to_vec(),
            b"hers".to_vec(),
            b"his".to_vec(),
        ];
        let trie = build_trie(&pats);
        let text = b"ahishers";
        let mut res = trie.ac_search(text, &pats);
        res.sort();
        assert!(res.contains(&(1, 3)) || res.contains(&(1, 3))); // "his" at 1
        assert!(res.iter().any(|&(pos, id)| &pats[id] == b"she" && pos == 3));
        assert!(
            res.iter()
                .any(|&(pos, id)| &pats[id] == b"he" && (pos == 4 || pos == 5))
        );
    }

    #[test]
    fn test_z_algorithm_and_search() {
        let s = "aaaaa";
        let z = z_algorithm(s);
        assert_eq!(z[0], s.len());
        assert!(z[1] >= 3);
        let hits = z_search("ababaabababa", "ababa");
        assert_eq!(hits, vec![0, 5, 7]);
    }

    #[test]
    fn test_sa_kasai() {
        let s = "banana$"; // 末尾加入哨兵保证严格后缀排序
        let sa = suffix_array(s);
        // 常见 banana$ 的 SA 为 [6,5,3,1,0,4,2] 或等价序，测试基本性质
        assert_eq!(sa.len(), s.len());
        // SA 应按后缀字典序递增
        for i in 1..sa.len() {
            assert!(s[sa[i - 1]..] <= s[sa[i]..]);
        }
        let lcp = lcp_kasai(s, &sa);
        assert_eq!(lcp.len(), s.len());
        // LCP 非负且符合相邻后缀公共前缀性质
        for i in 1..sa.len() {
            let a = &s[sa[i - 1]..];
            let b = &s[sa[i]..];
            let mut k = 0;
            while k < a.len() && k < b.len() && a.as_bytes()[k] == b.as_bytes()[k] {
                k += 1;
            }
            assert_eq!(lcp[i], k);
        }
    }

    #[test]
    fn test_manacher() {
        let (_st, len) = manacher_longest_palindrome("babad");
        assert!(len >= 3); // "bab" or "aba"
        let (st2, len2) = manacher_longest_palindrome("cbbd");
        assert_eq!(len2, 2);
        assert_eq!(&"cbbd"[st2..st2 + len2], "bb");
    }

    #[test]
    fn test_bmh() {
        let t = "here is a simple example";
        let p = "example";
        let r = bmh_search(t, p);
        assert_eq!(r, vec![17]);
    }

    #[test]
    fn test_sam_basic() {
        let sam = SuffixAutomaton::build_from_str("ababa");
        assert_eq!(sam.count_distinct_substrings(), 9);
        assert_eq!(sam.longest_common_substring_len("babab"), 4);
    }
}
