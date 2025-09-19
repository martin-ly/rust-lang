fn diverge() -> ! { panic!("never returns") }

fn choose(flag: bool) -> i32 {
    if flag { 1 } else { diverge() }
}

fn main() {
    let _ = std::thread::spawn(|| {
        // 使用 loop 作为发散表达式
        let _x: i32 = if false { 0 } else { loop {} };
    });
    let _ = std::panic::catch_unwind(|| choose(false));
}


