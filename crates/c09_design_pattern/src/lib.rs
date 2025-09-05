//! Rust设计模式实践案例库
//! 
//! 本库提供了Rust中各种设计模式的完整实现和实际应用案例，
//! 包括基础设计模式、高级设计模式以及在特定领域的应用。

// 基础设计模式模块
pub mod creational;
pub mod structural;
pub mod behavioral;

// 高级设计模式模块
pub mod parallel;
pub mod concurrency;

// 领域特定设计模式应用
pub mod web_framework_patterns;
pub mod database_patterns;
pub mod game_engine_patterns;
pub mod os_patterns;

// 错误处理模块
pub mod error_handling;

// 示例程序
// pub mod bin; // 暂时注释掉，避免编译错误

/// 设计模式库版本信息
pub const VERSION: &str = "1.0.0";

/// 获取库版本信息
pub fn get_version() -> &'static str {
    VERSION
}

/// 设计模式分类
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PatternCategory {
    Creational,
    Structural,
    Behavioral,
    Parallel,
    Concurrency,
    DomainSpecific,
}

/// 设计模式信息
#[derive(Debug, Clone)]
pub struct PatternInfo {
    pub name: String,
    pub category: PatternCategory,
    pub description: String,
    pub use_cases: Vec<String>,
}

/// 获取所有设计模式信息
pub fn get_all_patterns() -> Vec<PatternInfo> {
    vec![
        // 创建型模式
        PatternInfo {
            name: "Singleton".to_string(),
            category: PatternCategory::Creational,
            description: "确保一个类只有一个实例，并提供全局访问点".to_string(),
            use_cases: vec![
                "系统资源管理器".to_string(),
                "配置管理器".to_string(),
                "日志记录器".to_string(),
            ],
        },
        PatternInfo {
            name: "Factory".to_string(),
            category: PatternCategory::Creational,
            description: "定义一个创建对象的接口，让子类决定实例化哪个类".to_string(),
            use_cases: vec![
                "设备工厂".to_string(),
                "UI组件工厂".to_string(),
                "数据库连接工厂".to_string(),
            ],
        },
        PatternInfo {
            name: "Builder".to_string(),
            category: PatternCategory::Creational,
            description: "将复杂对象的构建过程分离，使同样的构建过程可以创建不同的表示".to_string(),
            use_cases: vec![
                "SQL查询构建器".to_string(),
                "HTTP请求构建器".to_string(),
                "配置对象构建器".to_string(),
            ],
        },
        
        // 结构型模式
        PatternInfo {
            name: "Adapter".to_string(),
            category: PatternCategory::Structural,
            description: "将一个类的接口转换成客户希望的另一个接口".to_string(),
            use_cases: vec![
                "第三方库适配".to_string(),
                "API版本兼容".to_string(),
                "数据格式转换".to_string(),
            ],
        },
        PatternInfo {
            name: "Decorator".to_string(),
            category: PatternCategory::Structural,
            description: "动态地给对象添加额外的职责".to_string(),
            use_cases: vec![
                "日志装饰器".to_string(),
                "缓存装饰器".to_string(),
                "权限检查装饰器".to_string(),
            ],
        },
        PatternInfo {
            name: "Proxy".to_string(),
            category: PatternCategory::Structural,
            description: "为其他对象提供一种代理以控制对这个对象的访问".to_string(),
            use_cases: vec![
                "远程代理".to_string(),
                "虚拟代理".to_string(),
                "保护代理".to_string(),
            ],
        },
        
        // 行为型模式
        PatternInfo {
            name: "Observer".to_string(),
            category: PatternCategory::Behavioral,
            description: "定义对象间的一种一对多的依赖关系".to_string(),
            use_cases: vec![
                "事件系统".to_string(),
                "数据绑定".to_string(),
                "消息通知".to_string(),
            ],
        },
        PatternInfo {
            name: "Strategy".to_string(),
            category: PatternCategory::Behavioral,
            description: "定义一系列算法，把它们封装起来，并且使它们可以互相替换".to_string(),
            use_cases: vec![
                "排序算法策略".to_string(),
                "支付方式策略".to_string(),
                "压缩算法策略".to_string(),
            ],
        },
        PatternInfo {
            name: "Command".to_string(),
            category: PatternCategory::Behavioral,
            description: "将请求封装成对象，从而可以用不同的请求对客户进行参数化".to_string(),
            use_cases: vec![
                "撤销/重做".to_string(),
                "宏命令".to_string(),
                "队列请求".to_string(),
            ],
        },
        
        // 并行模式
        PatternInfo {
            name: "Parallel Iterator".to_string(),
            category: PatternCategory::Parallel,
            description: "并行处理集合中的元素".to_string(),
            use_cases: vec![
                "并行排序".to_string(),
                "并行搜索".to_string(),
                "并行计算".to_string(),
            ],
        },
        PatternInfo {
            name: "Fork-Join".to_string(),
            category: PatternCategory::Parallel,
            description: "将任务分解为子任务，并行执行后合并结果".to_string(),
            use_cases: vec![
                "并行归并排序".to_string(),
                "并行矩阵乘法".to_string(),
                "并行图像处理".to_string(),
            ],
        },
        
        // 并发模式
        PatternInfo {
            name: "Actor".to_string(),
            category: PatternCategory::Concurrency,
            description: "通过消息传递进行通信的并发模型".to_string(),
            use_cases: vec![
                "聊天系统".to_string(),
                "游戏服务器".to_string(),
                "分布式系统".to_string(),
            ],
        },
        PatternInfo {
            name: "Channel".to_string(),
            category: PatternCategory::Concurrency,
            description: "线程间安全通信的机制".to_string(),
            use_cases: vec![
                "生产者-消费者".to_string(),
                "工作队列".to_string(),
                "事件流处理".to_string(),
            ],
        },
        
        // 领域特定模式
        PatternInfo {
            name: "MVC".to_string(),
            category: PatternCategory::DomainSpecific,
            description: "Web应用架构模式".to_string(),
            use_cases: vec![
                "Web框架".to_string(),
                "桌面应用".to_string(),
                "移动应用".to_string(),
            ],
        },
        PatternInfo {
            name: "Repository".to_string(),
            category: PatternCategory::DomainSpecific,
            description: "数据访问层抽象".to_string(),
            use_cases: vec![
                "数据库操作".to_string(),
                "缓存管理".to_string(),
                "API集成".to_string(),
            ],
        },
        PatternInfo {
            name: "Component".to_string(),
            category: PatternCategory::DomainSpecific,
            description: "游戏引擎实体组件系统".to_string(),
            use_cases: vec![
                "游戏开发".to_string(),
                "模拟系统".to_string(),
                "可视化应用".to_string(),
            ],
        },
    ]
}

/// 根据分类获取设计模式
pub fn get_patterns_by_category(category: PatternCategory) -> Vec<PatternInfo> {
    get_all_patterns()
        .into_iter()
        .filter(|pattern| pattern.category == category)
        .collect()
}

/// 搜索设计模式
pub fn search_patterns(query: &str) -> Vec<PatternInfo> {
    let query_lower = query.to_lowercase();
    get_all_patterns()
        .into_iter()
        .filter(|pattern| {
            pattern.name.to_lowercase().contains(&query_lower)
                || pattern.description.to_lowercase().contains(&query_lower)
                || pattern.use_cases.iter().any(|case| case.to_lowercase().contains(&query_lower))
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_get_all_patterns() {
        let patterns = get_all_patterns();
        assert!(!patterns.is_empty());
        
        // 检查是否包含所有分类
        let categories: std::collections::HashSet<_> = patterns
            .iter()
            .map(|p| p.category.clone())
            .collect();
        
        assert!(categories.contains(&PatternCategory::Creational));
        assert!(categories.contains(&PatternCategory::Structural));
        assert!(categories.contains(&PatternCategory::Behavioral));
        assert!(categories.contains(&PatternCategory::Parallel));
        assert!(categories.contains(&PatternCategory::Concurrency));
        assert!(categories.contains(&PatternCategory::DomainSpecific));
    }

    #[test]
    fn test_get_patterns_by_category() {
        let creational_patterns = get_patterns_by_category(PatternCategory::Creational);
        assert!(!creational_patterns.is_empty());
        
        for pattern in creational_patterns {
            assert_eq!(pattern.category, PatternCategory::Creational);
        }
    }

    #[test]
    fn test_search_patterns() {
        let results = search_patterns("singleton");
        assert!(!results.is_empty());
        
        let results = search_patterns("web");
        assert!(!results.is_empty());
        
        let results = search_patterns("nonexistent");
        assert!(results.is_empty());
    }

    #[test]
    fn test_version() {
        assert_eq!(get_version(), "1.0.0");
    }
}
