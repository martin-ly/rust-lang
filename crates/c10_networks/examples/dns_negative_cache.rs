use c10_networks::protocol::dns::DnsResolver;
use std::collections::HashMap;
use std::time::{Duration, Instant};

#[derive(Clone, Debug)]
enum CacheEntry {
    Success {
        ips: Vec<std::net::IpAddr>,
        expire_at: Instant,
    },
    Failure {
        expire_at: Instant,
    },
}

struct NegativeCache {
    // 简易演示：进程内 HashMap；生产可替换为 LRU/TTL Map
    inner: HashMap<String, CacheEntry>,
    ttl_ok: Duration,
    ttl_fail: Duration,
}

impl NegativeCache {
    fn new(ttl_ok: Duration, ttl_fail: Duration) -> Self {
        Self {
            inner: HashMap::new(),
            ttl_ok,
            ttl_fail,
        }
    }

    fn get(&mut self, key: &str) -> Option<CacheEntry> {
        if let Some(entry) = self.inner.get(key) {
            match entry {
                CacheEntry::Success { ips, expire_at } if *expire_at > Instant::now() => {
                    return Some(CacheEntry::Success {
                        ips: ips.clone(),
                        expire_at: *expire_at,
                    });
                }
                CacheEntry::Failure { expire_at } if *expire_at > Instant::now() => {
                    return Some(CacheEntry::Failure {
                        expire_at: *expire_at,
                    });
                }
                _ => {}
            }
        }
        None
    }

    fn set_success(&mut self, key: String, ips: Vec<std::net::IpAddr>) {
        self.inner.insert(
            key,
            CacheEntry::Success {
                ips,
                expire_at: Instant::now() + self.ttl_ok,
            },
        );
    }

    fn set_failure(&mut self, key: String) {
        self.inner.insert(
            key,
            CacheEntry::Failure {
                expire_at: Instant::now() + self.ttl_fail,
            },
        );
    }
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let mut cache = NegativeCache::new(Duration::from_secs(60), Duration::from_secs(10));
    let r = DnsResolver::from_system().await?;

    let domain = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "nonexistent.example.invalid".to_string());

    if let Some(entry) = cache.get(&domain) {
        match entry {
            CacheEntry::Success { ips, .. } => {
                println!("cache hit (ok): {} => {:?}", domain, ips);
                return Ok(());
            }
            CacheEntry::Failure { .. } => {
                println!("cache hit (fail): {} (skip query)", domain);
                return Ok(());
            }
        }
    }

    match r.lookup_ips(&domain).await {
        Ok(ips) if !ips.is_empty() => {
            cache.set_success(domain.clone(), ips.clone());
            println!("resolved: {} => {:?}", domain, ips);
        }
        Ok(_) | Err(_) => {
            cache.set_failure(domain.clone());
            println!("resolve failed: {} (negative cached 10s)", domain);
        }
    }

    Ok(())
}
