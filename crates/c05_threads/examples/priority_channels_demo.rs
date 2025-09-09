use c05_threads::message_passing::priority_channels as full;
use c05_threads::message_passing::priority_channels_simple as simple;

fn demo_simple() {
    let ch = simple::SimplePriorityChannel::new();
    ch.send(3, "low");
    ch.send(1, "high");
    ch.send(2, "mid");
    println!("simple -> {:?} {:?} {:?}", ch.recv(), ch.recv(), ch.recv());
}

fn demo_full() {
    let ch = full::PriorityChannel::new();
    ch.send(3, "low").unwrap();
    ch.send(1, "high").unwrap();
    ch.send(2, "mid").unwrap();
    println!("full -> {:?} {:?} {:?}", ch.recv(), ch.recv(), ch.recv());
}

fn main() {
    demo_simple();
    demo_full();
}
