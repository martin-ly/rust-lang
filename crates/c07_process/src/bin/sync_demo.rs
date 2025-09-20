use c07_process::prelude::*;

fn main() -> Result<()> {
    println!("Sync Demo - 同步原语演示");

    // 创建同步管理器
    let mut sync = SyncManager::new(SyncConfig::default());

    // 创建互斥锁
    let mutex = sync.create_mutex("demo_mutex")?;
    println!("✅ 创建互斥锁: demo_mutex");

    // 创建读写锁
    let rwlock = sync.create_rwlock("demo_rwlock")?;
    println!("✅ 创建读写锁: demo_rwlock");

    // 创建条件变量
    let _condvar = sync.create_condvar("demo_condvar")?;
    println!("✅ 创建条件变量: demo_condvar");

    // 创建信号量
    let semaphore = sync.create_semaphore("demo_semaphore", 3)?;
    println!("✅ 创建信号量: demo_semaphore (许可数: 3)");

    // 创建屏障
    let barrier = sync.create_barrier("demo_barrier", 2)?;
    println!("✅ 创建屏障: demo_barrier (参与者数: 2)");

    // 列出所有同步原语
    let primitives = sync.get_primitive_names();
    println!("📋 当前同步原语列表: {:?}", primitives);

    // 测试互斥锁
    if let Ok(guard) = mutex.lock() {
        println!("🔒 获取互斥锁成功");
        // 在这里可以安全地访问共享资源
        drop(guard); // 释放锁
        println!("🔓 释放互斥锁");
    }

    // 测试读写锁
    if let Ok(read_guard) = rwlock.read() {
        println!("📖 获取读锁成功");
        drop(read_guard);
        println!("📖 释放读锁");
    }

    if let Ok(write_guard) = rwlock.write() {
        println!("✍️ 获取写锁成功");
        drop(write_guard);
        println!("✍️ 释放写锁");
    }

    // 测试信号量
    if let Some(permit) = semaphore.try_acquire() {
        println!("🎫 获取信号量许可成功");
        drop(permit); // 自动释放许可
        println!("🎫 释放信号量许可");
    }

    // 测试屏障
    println!("🚧 等待屏障...");
    if barrier.wait().is_ok() {
        println!("🚧 屏障已通过");
    }

    println!("🎉 同步原语演示完成!");
    Ok(())
}
