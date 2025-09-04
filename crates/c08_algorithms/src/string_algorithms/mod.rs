//! 字符串算法：KMP 与 Rabin-Karp（同步 / 异步）

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
    if pattern.is_empty() { return (0..=text.len()).collect(); }
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
    if m > n { return Vec::new(); }

    let base: u64 = 256; // ASCII 基
    let modp: u64 = 1_000_000_007; // 大素数

    let tb = text.as_bytes();
    let pb = pattern.as_bytes();

    let mut h: u64 = 1; // base^(m-1) % modp
    for _ in 1..m { h = (h * base) % modp; }

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
            if &tb[i..i + m] == pb { res.push(i); }
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
        assert_eq!(r, vec![0,1,2,3]);
        let r2 = rt.block_on(async { rabin_karp_search_async("aaaaa".into(), "aa".into()).await.unwrap() });
        assert_eq!(r2, vec![0,1,2,3]);
    }
}


