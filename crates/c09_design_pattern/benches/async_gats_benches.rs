use criterion::{criterion_group, criterion_main, Criterion};

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

fn bench_async_event_bus(c: &mut Criterion) {
    use c09_design_pattern::concurrency::message_passing::define::async_bus::{EventBusString, BackpressureStrategy};
    use c09_design_pattern::concurrency::message_passing::define::StringEventHandler;

    let bus = EventBusString::new(StringEventHandler);
    let events: Vec<String> = (0..1_000).map(|i| format!("ev{}", i)).collect();

    c.bench_function("async_event_bus_backpressure", |b| {
        b.iter(|| {
            block_on(bus.run_with_backpressure(&events));
        })
    });

    c.bench_function("async_event_bus_until_cancel", |b| {
        b.iter(|| {
            block_on(bus.run_until_cancel(&events, true));
        })
    });

    c.bench_function("async_event_bus_strategy_block", |b| {
        b.iter(|| {
            block_on(bus.run_with_strategy(&events, BackpressureStrategy::Block));
        })
    });

    c.bench_function("async_event_bus_strategy_drop_oldest", |b| {
        b.iter(|| {
            block_on(bus.run_with_strategy(&events, BackpressureStrategy::DropOldest));
        })
    });

    c.bench_function("async_event_bus_strategy_batch_8", |b| {
        b.iter(|| {
            block_on(bus.run_with_strategy(&events, BackpressureStrategy::Batch(8)));
        })
    });

    c.bench_function("async_event_bus_timeout_like_256", |b| {
        b.iter(|| {
            block_on(bus.run_with_timeout_like(&events, 256));
        })
    });
}

fn bench_gats_observer(c: &mut Criterion) {
    use c09_design_pattern::behavioral::observer::define::{BorrowingObserver, BorrowingSubjectString};

    let mut subject = BorrowingSubjectString::new();
    subject.register_observer(BorrowingObserver);
    let msg = String::from("message");

    c.bench_function("gats_observer_notify", |b| {
        b.iter(|| subject.notify_observers(&msg))
    });
}

criterion_group!(benches, bench_async_event_bus, bench_gats_observer);
criterion_main!(benches);


