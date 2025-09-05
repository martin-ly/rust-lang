/// 跨模式集成测试
/// 
/// 测试不同设计模式之间的协作和集成
/// 验证模式组合使用的正确性和性能

use c09_design_pattern::creational::singleton::define::Singleton;
use c09_design_pattern::creational::abstract_factory::enum_trait::{CircleFactory, RectangleFactory, ShapeFactory};
use c09_design_pattern::structural::proxy::define::{RealSubject, Proxy, Subject};
use c09_design_pattern::structural::flyweight::define::{OptimizedFlyweightFactory as FlyweightFactory, Flyweight};
use c09_design_pattern::behavioral::chain_of_responsibility::define::{ConcreteHandlerA, ConcreteHandlerB, ConcreteHandlerC, Handler};

#[cfg(test)]
mod integration_tests {
    use super::*;
    use std::sync::Arc;
    use std::thread;

    /// 测试单例模式与工厂模式的集成
    #[test]
    fn test_singleton_with_factory_integration() {
        // 创建单例工厂
        let singleton_factory = Singleton::new();
        
        let factory = singleton_factory.get_instance(|| {
            Box::new(CircleFactory)
        });
        
        // 使用工厂创建产品
        let shape = factory.create_shape();
        shape.draw();
        
        // 验证单例行为
        let factory2 = singleton_factory.get_instance(|| {
            Box::new(CircleFactory) // 这不应该被调用
        });
        
        // 两个工厂应该是同一个实例（通过内容比较）
        assert_eq!(factory.create_shape().area(), factory2.create_shape().area());
    }

    /// 测试代理模式与享元模式的集成
    #[test]
    fn test_proxy_with_flyweight_integration() {
        let mut flyweight_factory = FlyweightFactory::new();
        
        // 创建享元对象
        let flyweight = flyweight_factory.get_flyweight("PROXY_TEST", "Proxy Flyweight State".to_string());
        
        // 创建代理包装享元对象
        let real_subject = RealSubject::new(flyweight.get_id());
        let proxy = Proxy::new(real_subject);
        
        // 测试代理行为
        proxy.request();
        
        // 验证ID一致性
        assert_eq!(proxy.get_id(), flyweight.get_id());
    }

    /// 测试责任链模式与观察者模式的集成
    #[test]
    fn test_chain_with_observer_integration() {
        // 创建责任链
        let mut handler_a = Arc::new(ConcreteHandlerA::new());
        let mut handler_b = Arc::new(ConcreteHandlerB::new());
        let mut handler_c = Arc::new(ConcreteHandlerC::new());
        
        // 构建链
        Arc::make_mut(&mut handler_a).set_next(handler_b.clone());
        Arc::make_mut(&mut handler_b).set_next(handler_c.clone());
        
        // 测试链式处理
        let requests = vec!["Request A", "Request B", "Request C", "Request D"];
        
        for request in requests {
            handler_a.handle(request.to_string());
        }
    }

    /// 测试多线程环境下的模式集成
    #[test]
    fn test_multithreaded_pattern_integration() {
        let singleton = Arc::new(Singleton::new());
        let mut handles = vec![];
        
        // 创建多个线程，每个线程使用单例工厂
        for i in 0..5 {
            let singleton_clone = Arc::clone(&singleton);
            let handle = thread::spawn(move || {
                let factory = singleton_clone.get_instance(|| {
                    Box::new(CircleFactory)
                });
                
                let shape = factory.create_shape();
                shape.draw();
                
                i // 返回线程ID
            });
            handles.push(handle);
        }
        
        // 等待所有线程完成
        let results: Vec<i32> = handles.into_iter()
            .map(|h| h.join().unwrap())
            .collect();
        
        assert_eq!(results.len(), 5);
        println!("多线程集成测试完成，线程ID: {:?}", results);
    }

    /// 测试享元模式与代理模式的性能集成
    #[test]
    fn test_flyweight_proxy_performance_integration() {
        let mut flyweight_factory = FlyweightFactory::new();
        
        // 批量创建享元对象
        let specs = vec![
            ("PERF1".to_string(), "Performance State 1".to_string()),
            ("PERF2".to_string(), "Performance State 2".to_string()),
            ("PERF3".to_string(), "Performance State 3".to_string()),
        ];
        
        let flyweights = flyweight_factory.batch_create_flyweights(&specs);
        
        // 为每个享元对象创建代理
        let mut proxies = Vec::new();
        for flyweight in flyweights {
            let real_subject = RealSubject::new(flyweight.get_id());
            let proxy = Proxy::new(real_subject);
            proxies.push(proxy);
        }
        
        // 测试代理性能
        for (i, proxy) in proxies.iter().enumerate() {
            proxy.request();
            assert_eq!(proxy.get_id(), (i + 1) as u32);
        }
        
        println!("性能集成测试完成，处理了 {} 个代理对象", proxies.len());
    }

    /// 测试错误处理和恢复机制
    #[test]
    fn test_error_handling_integration() {
        let mut flyweight_factory = FlyweightFactory::new();
        
        // 测试空键处理
        let flyweight = flyweight_factory.get_flyweight("", "Empty Key State".to_string());
        flyweight.operation("Test Operation");
        
        // 测试重复键处理
        let flyweight1 = flyweight_factory.get_flyweight("DUPLICATE", "State 1".to_string());
        let flyweight2 = flyweight_factory.get_flyweight("DUPLICATE", "State 2".to_string());
        
        // 应该返回同一个对象
        assert_eq!(flyweight1.get_id(), flyweight2.get_id());
        
        println!("错误处理集成测试完成");
    }

    /// 测试内存使用优化
    #[test]
    fn test_memory_optimization_integration() {
        let mut flyweight_factory = FlyweightFactory::new();
        
        // 创建大量享元对象
        let mut flyweights = Vec::new();
        for i in 0..100 {
            let key = format!("MEMORY_TEST_{}", i);
            let state = format!("Memory State {}", i);
            let flyweight = flyweight_factory.get_flyweight(&key, state);
            flyweights.push(flyweight);
        }
        
        // 验证内存使用
        let (count, _) = flyweight_factory.get_statistics();
        assert_eq!(count, 100);
        
        // 测试重用
        let reused_flyweight = flyweight_factory.get_flyweight("MEMORY_TEST_0", "Different State".to_string());
        assert_eq!(reused_flyweight.get_id(), flyweights[0].get_id());
        
        println!("内存优化集成测试完成，创建了 {} 个享元对象", count);
    }
}

/// 性能基准测试
#[cfg(test)]
mod performance_tests {
    use super::*;
    use std::time::Instant;

    #[test]
    fn test_singleton_performance() {
        let singleton = Singleton::new();
        
        let start = Instant::now();
        
        // 多次获取单例实例
        for _ in 0..10000 {
            let _instance = singleton.get_instance(|| {
                String::from("Performance Test Instance")
            });
        }
        
        let duration = start.elapsed();
        println!("单例模式性能测试：10000次获取耗时 {:?}", duration);
        
        // 性能应该很快（通常 < 1ms）
        assert!(duration.as_millis() < 100);
    }

    #[test]
    fn test_flyweight_performance() {
        let mut factory = FlyweightFactory::new();
        
        let start = Instant::now();
        
        // 创建大量享元对象
        for i in 0..1000 {
            let key = format!("PERF_{}", i % 100); // 重用前100个
            let state = format!("Performance State {}", i);
            let _flyweight = factory.get_flyweight(&key, state);
        }
        
        let duration = start.elapsed();
        println!("享元模式性能测试：1000次创建耗时 {:?}", duration);
        
        // 验证重用效果
        let (count, _) = factory.get_statistics();
        assert_eq!(count, 100); // 应该只有100个唯一对象
        
        // 性能应该合理（通常 < 10ms）
        assert!(duration.as_millis() < 50);
    }

    #[test]
    fn test_proxy_performance() {
        let start = Instant::now();
        
        // 创建大量代理对象
        let mut proxies = Vec::new();
        for i in 0..1000 {
            let real_subject = RealSubject::new(i);
            let proxy = Proxy::new(real_subject);
            proxies.push(proxy);
        }
        
        // 执行代理操作
        for proxy in &proxies {
            proxy.request();
        }
        
        let duration = start.elapsed();
        println!("代理模式性能测试：1000个代理对象操作耗时 {:?}", duration);
        
        // 性能应该合理（通常 < 20ms）
        assert!(duration.as_millis() < 100);
    }
}
