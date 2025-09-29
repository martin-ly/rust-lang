//! 运行方式：
//! cargo run -p c06_async --example actix_basic

fn main() {
    // 使用库内提供的同步封装，内部会启动 Actix System
    c06_async::actix::actor01::actor_exp01_run();
}


