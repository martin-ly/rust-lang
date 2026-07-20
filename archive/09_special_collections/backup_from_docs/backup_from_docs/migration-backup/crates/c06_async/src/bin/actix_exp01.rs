use c06_async::actix::actor01::*;

fn main() {
    // 启动 Actix 系统
    let system = actix_rt::System::new();
    system.block_on(actor_exp01());
}
