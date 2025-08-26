//! c09 设计模式：事件与单例 集成测试与简单基准

use std::sync::{Arc, Mutex};
use std::time::Instant;

use c09_design_pattern::game_engine_patterns::{
    EventManager, AchievementSystem, LoggingSystem, GameEvent, Position
};
use c09_design_pattern::os_patterns::SystemResourceManagerSingleton;

#[test]
fn integration_event_dispatch_throughput() {
    let mut em = EventManager::new();
    em.subscribe(AchievementSystem::new());
    em.subscribe(LoggingSystem);

    let t0 = Instant::now();
    for i in 0..10_000u64 {
        em.publish(GameEvent::PlayerMoved { entity_id: i, new_position: Position { x: 1.0, y: 2.0, z: 0.0 } });
    }
    let dur = t0.elapsed();
    eprintln!("Event dispatch 10k took {:?}", dur);
}

#[test]
fn integration_singleton_shared_instance() {
    let singleton = SystemResourceManagerSingleton::new();
    let a = singleton.get_instance();
    let b = singleton.get_instance();

    // 两个 Arc 指向同一共享实例（通过修改可观测状态验证）
    {
        let mut mgr = a.lock().unwrap();
        mgr.create_process();
    }
    {
        let mgr = b.lock().unwrap();
        assert_eq!(mgr.get_process_count(), 1);
    }
}


