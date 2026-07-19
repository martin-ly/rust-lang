use c03_control_fn::async_control_flow::AsyncControlFlowExecutor;
use std::cell::Cell;
use std::rc::Rc;

pub async fn run() {
    let exec = AsyncControlFlowExecutor;

    // if/else
    let v = exec.async_if_else(true, async { 10 }, async { 0 }).await;
    println!("if_else -> {}", v);

    // loop（3 次）
    let counter = Rc::new(Cell::new(0));
    let remaining = Cell::new(3);
    let c = counter.clone();
    exec
        .async_loop(
            move || {
                let r = remaining.get();
                if r > 0 { c.set(c.get() + 1); remaining.set(r - 1); true } else { false }
            },
            std::future::ready(()),
        )
        .await;
    println!("loop_count -> {}", counter.get());

    // for each
    let items = vec![1, 2, 3, 4, 5];
    let processed = exec.async_for(items.clone(), |x| async move { x }).await;
    let sum: i32 = processed.iter().copied().sum();
    println!("for_sum -> {}", sum);
}


