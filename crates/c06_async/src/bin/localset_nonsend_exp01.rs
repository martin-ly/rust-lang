// LocalSet 与 !Send 任务示例（Rust 1.90）
// 说明：在 LocalSet 上运行包含 Rc/RefCell 的 !Send 任务

use std::cell::RefCell;
use std::rc::Rc;

#[tokio::main(flavor = "multi_thread")]
async fn main() -> anyhow::Result<()> {
    let local = tokio::task::LocalSet::new();

    local
        .run_until(async move {
            let data = Rc::new(RefCell::new(0u32)); // !Send

            // 在本地任务中使用 !Send 数据
            let d1 = data.clone();
            let t1 = tokio::task::spawn_local(async move {
                *d1.borrow_mut() += 1;
                *d1.borrow()
            });

            let d2 = data.clone();
            let t2 = tokio::task::spawn_local(async move {
                *d2.borrow_mut() += 2;
                *d2.borrow()
            });

            let (a, b) = tokio::join!(t1, t2);
            println!("local values = {:?}, {:?}", a.unwrap(), b.unwrap());

            Ok::<_, anyhow::Error>(())
        })
        .await
}


