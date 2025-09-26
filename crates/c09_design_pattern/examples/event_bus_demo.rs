use c09_design_pattern::concurrency::message_passing::define::async_bus::EventBusString;
use c09_design_pattern::concurrency::message_passing::define::StringEventHandler;

fn block_on<F: core::future::Future>(mut fut: F) -> F::Output {
    use core::pin::Pin;
    use core::task::{Context, Poll, RawWaker, RawWakerVTable, Waker};
    fn dummy_raw_waker() -> RawWaker {
        fn no_op(_: *const ()) {}
        fn clone(_: *const ()) -> RawWaker { dummy_raw_waker() }
        static VTABLE: RawWakerVTable = RawWakerVTable::new(clone, no_op, no_op, no_op);
        RawWaker::new(core::ptr::null(), &VTABLE)
    }
    let waker = unsafe { Waker::from_raw(dummy_raw_waker()) };
    let mut cx = Context::from_waker(&waker);
    let mut fut = unsafe { Pin::new_unchecked(&mut fut) };
    loop {
        match fut.as_mut().poll(&mut cx) {
            Poll::Ready(v) => break v,
            Poll::Pending => {}
        }
    }
}

fn main() {
    let bus = EventBusString::new(StringEventHandler);
    let events: Vec<String> = (0..5).map(|i| format!("demo-{}", i)).collect();
    block_on(bus.run_with_backpressure(&events));
    block_on(bus.run_until_cancel(&events, true));
    println!("event_bus_demo: done");
}


