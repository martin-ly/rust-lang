fn abort(msg: &str) -> ! { panic!("{}", msg); }

fn must(v: Option<i32>) -> i32 {
    v.unwrap_or_else(|| abort("none"))
}

fn only_true(b: bool) {
    match b {
        true => {}
        false => unreachable!(),
    }
}

fn never_returns() -> ! { loop {} }

fn main() {
    assert_eq!(must(Some(5)), 5);
    let _ = std::panic::catch_unwind(|| must(None));
    only_true(true);
    let _ = std::thread::spawn(|| {
        // 不要真的卡住测试
        if false { let _ = never_returns(); }
    }).join();
}


