use std::sync::Arc;
use std::thread;
use std::time::Duration;

use c05_threads::message_passing::backpressure_handling as bp;

fn main() {
    // Blocking
    {
        let ch = Arc::new(bp::BlockingBackpressureChannel::new(4));
        let p = {
            let ch = Arc::clone(&ch);
            thread::spawn(move || {
                for i in 0..8 {
                    let _ = ch.send(i);
                }
            })
        };
        let c = {
            let ch = Arc::clone(&ch);
            thread::spawn(move || {
                let mut out = Vec::new();
                for _ in 0..8 {
                    if let Some(v) = ch.recv() {
                        out.push(v);
                        thread::sleep(Duration::from_millis(5));
                    }
                }
                println!("blocking -> {:?}", out);
            })
        };
        p.join().unwrap();
        c.join().unwrap();
    }

    // Dropping
    {
        let ch = bp::DroppingBackpressureChannel::new(4, 0.75);
        for i in 0..16 {
            let _ = ch.send(i);
        }
        let mut out = Vec::new();
        while let Some(v) = ch.recv() {
            out.push(v);
        }
        println!("dropping -> len={}, dropped~{}", out.len(), 16 - out.len());
    }

    // Adaptive
    {
        let cfg = bp::BackpressureConfig {
            strategy: bp::BackpressureStrategy::Adaptive,
            buffer_size: 8,
            high_watermark: 0.7,
            low_watermark: 0.3,
            drop_threshold: 0.9,
            adaptation_interval: Duration::from_millis(50),
        };
        let ch = bp::AdaptiveBackpressureChannel::new(cfg);
        for i in 0..16 {
            let _ = ch.send(i);
        }
        let mut out = Vec::new();
        for _ in 0..16 {
            if let Some(v) = ch.recv() {
                out.push(v);
            }
        }
        println!("adaptive -> {} items", out.len());
    }

    // FlowControl
    {
        let ch = bp::FlowControlBackpressureChannel::new(8, 4, Duration::from_millis(100));
        for i in 0..16 {
            let _ = ch.send(i);
        }
        let mut out = Vec::new();
        for _ in 0..16 {
            if let Some(v) = ch.recv() {
                out.push(v);
            }
        }
        println!("flow_control -> {} items (window limited)", out.len());
    }
}
