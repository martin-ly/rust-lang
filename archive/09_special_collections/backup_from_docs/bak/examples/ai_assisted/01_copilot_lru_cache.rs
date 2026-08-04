// 🤖 AI辅助编程示例1：LRU缓存实现
// 
// 提示词：
// 实现一个线程安全的LRU缓存
// 输入：容量和键值对
// 输出：get/put操作
// 约束：O(1)时间复杂度，线程安全

use std::collections::HashMap;
use std::sync::{Arc, Mutex};

/// 线程安全的LRU缓存
/// 
/// # 特性
/// - O(1) get/put操作
/// - 线程安全（使用Arc<Mutex>）
/// - 自动淘汰最少使用的项
/// 
/// # 示例
/// ```
/// let cache = LruCache::new(2);
/// cache.put("key1", "value1");
/// cache.put("key2", "value2");
/// assert_eq!(cache.get("key1"), Some("value1".to_string()));
/// ```
pub struct LruCache<K, V>
where
    K: Eq + std::hash::Hash + Clone,
    V: Clone,
{
    capacity: usize,
    cache: Arc<Mutex<CacheInner<K, V>>>,
}

struct CacheInner<K, V>
where
    K: Eq + std::hash::Hash + Clone,
    V: Clone,
{
    map: HashMap<K, Node<K, V>>,
    head: Option<K>,
    tail: Option<K>,
}

#[derive(Clone)]
struct Node<K, V>
where
    K: Clone,
    V: Clone,
{
    key: K,
    value: V,
    prev: Option<K>,
    next: Option<K>,
}

impl<K, V> LruCache<K, V>
where
    K: Eq + std::hash::Hash + Clone,
    V: Clone,
{
    /// 创建指定容量的LRU缓存
    pub fn new(capacity: usize) -> Self {
        assert!(capacity > 0, "Capacity must be greater than 0");
        
        Self {
            capacity,
            cache: Arc::new(Mutex::new(CacheInner {
                map: HashMap::new(),
                head: None,
                tail: None,
            })),
        }
    }

    /// 获取缓存值
    /// 
    /// 如果key存在，将其移到最前面（最近使用）
    pub fn get(&self, key: &K) -> Option<V> {
        let mut cache = self.cache.lock().unwrap();
        
        if let Some(node) = cache.map.get(key) {
            let value = node.value.clone();
            // 移到最前面
            cache.move_to_front(key.clone());
            Some(value)
        } else {
            None
        }
    }

    /// 插入或更新缓存值
    /// 
    /// 如果缓存已满，淘汰最少使用的项
    pub fn put(&self, key: K, value: V) {
        let mut cache = self.cache.lock().unwrap();
        
        if cache.map.contains_key(&key) {
            // 更新现有值
            if let Some(node) = cache.map.get_mut(&key) {
                node.value = value;
            }
            cache.move_to_front(key);
        } else {
            // 插入新值
            if cache.map.len() >= self.capacity {
                // 淘汰最少使用的项
                if let Some(tail_key) = cache.tail.clone() {
                    cache.remove_node(&tail_key);
                }
            }
            
            let node = Node {
                key: key.clone(),
                value,
                prev: None,
                next: cache.head.clone(),
            };
            
            cache.map.insert(key.clone(), node);
            
            if let Some(old_head) = cache.head.clone() {
                if let Some(head_node) = cache.map.get_mut(&old_head) {
                    head_node.prev = Some(key.clone());
                }
            }
            
            cache.head = Some(key.clone());
            
            if cache.tail.is_none() {
                cache.tail = Some(key);
            }
        }
    }

    /// 获取当前缓存大小
    pub fn len(&self) -> usize {
        self.cache.lock().unwrap().map.len()
    }

    /// 检查缓存是否为空
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// 清空缓存
    pub fn clear(&self) {
        let mut cache = self.cache.lock().unwrap();
        cache.map.clear();
        cache.head = None;
        cache.tail = None;
    }
}

impl<K, V> CacheInner<K, V>
where
    K: Eq + std::hash::Hash + Clone,
    V: Clone,
{
    fn move_to_front(&mut self, key: K) {
        if self.head.as_ref() == Some(&key) {
            return;
        }
        
        // 从当前位置移除
        if let Some(node) = self.map.get(&key).cloned() {
            // 更新prev的next
            if let Some(prev_key) = node.prev.clone() {
                if let Some(prev_node) = self.map.get_mut(&prev_key) {
                    prev_node.next = node.next.clone();
                }
            }
            
            // 更新next的prev
            if let Some(next_key) = node.next.clone() {
                if let Some(next_node) = self.map.get_mut(&next_key) {
                    next_node.prev = node.prev.clone();
                }
            }
            
            // 如果是tail，更新tail
            if self.tail.as_ref() == Some(&key) {
                self.tail = node.prev.clone();
            }
        }
        
        // 插到最前面
        if let Some(node) = self.map.get_mut(&key) {
            node.prev = None;
            node.next = self.head.clone();
        }
        
        if let Some(old_head) = self.head.clone() {
            if let Some(head_node) = self.map.get_mut(&old_head) {
                head_node.prev = Some(key.clone());
            }
        }
        
        self.head = Some(key);
    }
    
    fn remove_node(&mut self, key: &K) {
        if let Some(node) = self.map.remove(key) {
            if let Some(prev_key) = node.prev {
                if let Some(prev_node) = self.map.get_mut(&prev_key) {
                    prev_node.next = node.next.clone();
                }
            }
            
            if let Some(next_key) = node.next {
                if let Some(next_node) = self.map.get_mut(&next_key) {
                    next_node.prev = node.prev.clone();
                }
            }
            
            if self.head.as_ref() == Some(key) {
                self.head = node.next;
            }
            
            if self.tail.as_ref() == Some(key) {
                self.tail = node.prev;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lru_basic() {
        let cache = LruCache::new(2);
        
        cache.put("key1", "value1");
        cache.put("key2", "value2");
        
        assert_eq!(cache.get(&"key1"), Some("value1".to_string()));
        assert_eq!(cache.get(&"key2"), Some("value2".to_string()));
    }

    #[test]
    fn test_lru_eviction() {
        let cache = LruCache::new(2);
        
        cache.put("key1", "value1");
        cache.put("key2", "value2");
        cache.put("key3", "value3"); // 应该淘汰key1
        
        assert_eq!(cache.get(&"key1"), None);
        assert_eq!(cache.get(&"key2"), Some("value2".to_string()));
        assert_eq!(cache.get(&"key3"), Some("value3".to_string()));
    }

    #[test]
    fn test_lru_update() {
        let cache = LruCache::new(2);
        
        cache.put("key1", "value1");
        cache.put("key2", "value2");
        cache.get(&"key1"); // key1变为最近使用
        cache.put("key3", "value3"); // 应该淘汰key2
        
        assert_eq!(cache.get(&"key1"), Some("value1".to_string()));
        assert_eq!(cache.get(&"key2"), None);
        assert_eq!(cache.get(&"key3"), Some("value3".to_string()));
    }

    #[test]
    fn test_thread_safety() {
        use std::thread;
        
        let cache = Arc::new(LruCache::new(100));
        let mut handles = vec![];
        
        for i in 0..10 {
            let cache_clone = Arc::clone(&cache);
            let handle = thread::spawn(move || {
                for j in 0..10 {
                    let key = format!("key_{}_{}", i, j);
                    let value = format!("value_{}_{}", i, j);
                    cache_clone.put(key.clone(), value.clone());
                    cache_clone.get(&key);
                }
            });
            handles.push(handle);
        }
        
        for handle in handles {
            handle.join().unwrap();
        }
        
        assert!(cache.len() <= 100);
    }
}

fn main() {
    println!("🤖 AI辅助编程示例：LRU缓存");
    println!("=====================================");
    
    let cache = LruCache::new(3);
    
    println!("\n1. 插入3个元素:");
    cache.put("rust", "🦀");
    cache.put("go", "🐹");
    cache.put("python", "🐍");
    println!("   缓存大小: {}", cache.len());
    
    println!("\n2. 获取元素:");
    println!("   rust = {:?}", cache.get(&"rust"));
    println!("   go = {:?}", cache.get(&"go"));
    
    println!("\n3. 插入第4个元素（触发LRU淘汰）:");
    cache.put("java", "☕");
    println!("   python（最少使用）= {:?}", cache.get(&"python"));
    println!("   java（新插入）= {:?}", cache.get(&"java"));
    
    println!("\n✅ 示例完成！");
}

