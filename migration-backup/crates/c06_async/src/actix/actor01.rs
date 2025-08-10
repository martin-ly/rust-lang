use actix::prelude::*;
// use actix::Actor;
// use actix::Handler;
// use actix::Message;
// use actix::System;
// use actix::Context;

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
    // 启动 Actix 系统
    // let system = System::new();

    // 创建 Actor 实例
    let addr = MyActor.start();

    // 发送消息
    let response = addr.send(Ping).await.unwrap();
    println!("Received: {}", response);

    // 运行系统
    //system.run().unwrap();
}
