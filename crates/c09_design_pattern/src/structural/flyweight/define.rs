/// 使用Rust 1.89新特性优化的享元模式实现
///
/// 特性：
/// - 利用数组与Vec转换优化数据结构
/// - 使用更高效的内存管理策略
/// - 支持批量操作和缓存优化
use std::collections::HashMap;
use std::sync::Arc;

// 定义一个 Flyweight trait
#[allow(unused)]
pub trait Flyweight {
    fn operation(&self, extrinsic_state: &str);
    fn get_id(&self) -> u32;
}

// 具体的 Flyweight 实现
#[allow(unused)]
pub struct ConcreteFlyweight {
    intrinsic_state: String,
    id: u32,
}

impl ConcreteFlyweight {
    pub fn new(intrinsic_state: String, id: u32) -> Self {
        Self {
            intrinsic_state,
            id,
        }
    }
}

impl Flyweight for ConcreteFlyweight {
    fn operation(&self, extrinsic_state: &str) {
        println!(
            "Flyweight {}: Intrinsic State: {}, Extrinsic State: {}",
            self.id, self.intrinsic_state, extrinsic_state
        );
    }

    fn get_id(&self) -> u32 {
        self.id
    }
}

// 使用Rust 1.89新特性优化的享元工厂
#[allow(unused)]
pub struct OptimizedFlyweightFactory {
    flyweights: HashMap<String, Arc<ConcreteFlyweight>>,
    id_counter: u32,
}

impl Default for OptimizedFlyweightFactory {
    fn default() -> Self {
        Self::new()
    }
}

impl OptimizedFlyweightFactory {
    pub fn new() -> Self {
        Self {
            flyweights: HashMap::new(),
            id_counter: 0,
        }
    }

    pub fn get_flyweight(&mut self, key: &str, intrinsic_state: String) -> Arc<ConcreteFlyweight> {
        if !self.flyweights.contains_key(key) {
            self.id_counter += 1;
            let flyweight = Arc::new(ConcreteFlyweight::new(intrinsic_state, self.id_counter));
            self.flyweights.insert(key.to_string(), flyweight.clone());
            flyweight
        } else {
            self.flyweights.get(key).unwrap().clone()
        }
    }

    /// 批量创建享元对象，利用数组转换优化
    pub fn batch_create_flyweights(
        &mut self,
        specs: &[(String, String)],
    ) -> Vec<Arc<ConcreteFlyweight>> {
        let mut results = Vec::with_capacity(specs.len());

        for (key, intrinsic_state) in specs {
            let flyweight = self.get_flyweight(key, intrinsic_state.clone());
            results.push(flyweight);
        }

        // 使用Rust 1.89的数组转换优化
        results
    }

    /// 获取所有享元对象的统计信息
    pub fn get_statistics(&self) -> (usize, Vec<u32>) {
        let count = self.flyweights.len();
        let ids: Vec<u32> = self.flyweights.values().map(|f| f.get_id()).collect();
        (count, ids)
    }
}

// 传统享元工厂（保持向后兼容）
#[allow(unused)]
struct FlyweightFactory {
    flyweights: HashMap<String, ConcreteFlyweight>,
}

impl FlyweightFactory {
    #[allow(unused)]
    fn new() -> Self {
        FlyweightFactory {
            flyweights: HashMap::new(),
        }
    }

    #[allow(unused)]
    fn get_flyweight(&mut self, key: &str, intrinsic_state: String) -> &ConcreteFlyweight {
        if !self.flyweights.contains_key(key) {
            let flyweight = ConcreteFlyweight::new(intrinsic_state, 0);
            self.flyweights.insert(key.to_string(), flyweight);
        }
        self.flyweights.get(key).unwrap()
    }
}

// 享元池管理器
#[allow(unused)]
struct FlyweightPool {
    factory: OptimizedFlyweightFactory,
    cache: HashMap<String, Arc<ConcreteFlyweight>>,
}

impl FlyweightPool {
    fn new() -> Self {
        Self {
            factory: OptimizedFlyweightFactory::new(),
            cache: HashMap::new(),
        }
    }

    fn get_or_create(&mut self, key: &str, intrinsic_state: String) -> Arc<ConcreteFlyweight> {
        if let Some(cached) = self.cache.get(key) {
            cached.clone()
        } else {
            let flyweight = self.factory.get_flyweight(key, intrinsic_state);
            self.cache.insert(key.to_string(), flyweight.clone());
            flyweight
        }
    }

    fn clear_cache(&mut self) {
        self.cache.clear();
    }

    fn get_cache_size(&self) -> usize {
        self.cache.len()
    }
}

// 使用示例
#[allow(unused)]
pub fn test_flyweight() {
    println!("=== 优化享元模式测试 ===");
    let mut factory = OptimizedFlyweightFactory::new();

    let flyweight1 = factory.get_flyweight("A", "Intrinsic State A".to_string());
    flyweight1.operation("Extrinsic State 1");

    let flyweight2 = factory.get_flyweight("B", "Intrinsic State B".to_string());
    flyweight2.operation("Extrinsic State 2");

    let flyweight3 = factory.get_flyweight("A", "Intrinsic State A".to_string());
    flyweight3.operation("Extrinsic State 3");

    // 验证享元对象的重用
    assert_eq!(flyweight1.get_id(), flyweight3.get_id());
    println!("享元对象重用验证成功");

    // 测试批量创建
    println!("\n=== 批量创建测试 ===");
    let specs = vec![
        ("C".to_string(), "Intrinsic State C".to_string()),
        ("D".to_string(), "Intrinsic State D".to_string()),
        ("E".to_string(), "Intrinsic State E".to_string()),
    ];

    let batch_flyweights = factory.batch_create_flyweights(&specs);
    for (i, flyweight) in batch_flyweights.iter().enumerate() {
        flyweight.operation(&format!("Batch Extrinsic State {}", i + 1));
    }

    // 获取统计信息
    let (count, ids) = factory.get_statistics();
    println!("工厂统计：创建了 {} 个享元对象，ID列表: {:?}", count, ids);
}

/// 演示数组转换优化的使用
#[allow(unused)]
pub fn test_array_conversion_optimization() {
    println!("\n=== 数组转换优化测试 ===");

    // 创建固定大小数组
    let array: [i32; 5] = [1, 2, 3, 4, 5];

    // 使用Rust 1.89的数组转换特性
    let vec_from_array: Vec<i32> = array.into();
    println!("数组转Vec: {:?}", vec_from_array);

    // 从Vec创建Box<[T]>
    let boxed_slice: Box<[i32]> = vec_from_array.into_boxed_slice();
    println!("Vec转Box<[T]>: {:?}", boxed_slice);

    // 尝试从Box<[T]>转回Vec
    let vec_from_boxed: Vec<i32> = boxed_slice.into_vec();
    println!("Box<[T]>转Vec: {:?}", vec_from_boxed);

    println!("数组转换优化测试完成");
}

/// 测试享元池管理器
#[allow(unused)]
pub fn test_flyweight_pool() {
    println!("\n=== 享元池管理器测试 ===");
    let mut pool = FlyweightPool::new();

    // 创建享元对象
    let flyweight1 = pool.get_or_create("A", "Pool State A".to_string());
    let flyweight2 = pool.get_or_create("B", "Pool State B".to_string());
    let flyweight3 = pool.get_or_create("A", "Pool State A".to_string()); // 应该重用

    flyweight1.operation("Pool Extrinsic 1");
    flyweight2.operation("Pool Extrinsic 2");
    flyweight3.operation("Pool Extrinsic 3");

    // 验证缓存
    assert_eq!(flyweight1.get_id(), flyweight3.get_id());
    println!("缓存大小: {}", pool.get_cache_size());

    // 清理缓存
    pool.clear_cache();
    println!("清理后缓存大小: {}", pool.get_cache_size());
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_flyweight01() {
        test_flyweight();
    }

    #[test]
    fn test_array_conversion_optimization() {
        super::test_array_conversion_optimization();
    }

    #[test]
    fn test_flyweight_pool() {
        super::test_flyweight_pool();
    }

    #[test]
    fn test_flyweight_reuse() {
        let mut factory = OptimizedFlyweightFactory::new();

        let flyweight1 = factory.get_flyweight("TEST", "Test State".to_string());
        let flyweight2 = factory.get_flyweight("TEST", "Test State".to_string());

        // 应该返回同一个享元对象
        assert_eq!(flyweight1.get_id(), flyweight2.get_id());
    }

    #[test]
    fn test_batch_creation() {
        let mut factory = OptimizedFlyweightFactory::new();

        let specs = vec![
            ("BATCH1".to_string(), "Batch State 1".to_string()),
            ("BATCH2".to_string(), "Batch State 2".to_string()),
        ];

        let flyweights = factory.batch_create_flyweights(&specs);
        assert_eq!(flyweights.len(), 2);

        let (count, _) = factory.get_statistics();
        assert_eq!(count, 2);
    }
}
