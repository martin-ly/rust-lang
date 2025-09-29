//! Actix 最小可运行示例：定义消息/Actor，发送并接收响应。
//! 
//! 用法：
//! - 库内调用异步版本：`actor_exp01().await`（需在 Actix 系统/运行时内）
//! - 可直接在可执行入口调用同步封装：`actor_exp01_run()`（内部启动并关闭系统）
//! 
//! 示例参见 `examples/actix_basic.rs`。

use actix::prelude::*;
use actix::System;

#[allow(unused)]
// 定义消息
struct Ping;

#[allow(unused)]
struct Pong;

// 实现消息 trait
impl Message for Ping {
    type Result = String;
}

// 定义 Actor
struct MyActor;

impl Actor for MyActor {
    type Context = Context<Self>;
}

// 实现消息处理
impl Handler<Ping> for MyActor {
    type Result = String;

    fn handle(&mut self, _msg: Ping, _: &mut Self::Context) -> Self::Result {
        "Pong".to_string()
    }
}

#[allow(unused)]
pub async fn actor_exp01() {
    // 创建 Actor 实例
    let addr = MyActor.start();

    // 发送消息
    let response = addr.send(Ping).await.unwrap();
    println!("Received: {}", response);

}

/// 同步封装：内部创建并运行 Actix `System`，方便示例/二进制入口直接调用
#[allow(unused)]
pub fn actor_exp01_run() {
    let sys = System::new();
    sys.block_on(async {
        actor_exp01().await;
    });
}
