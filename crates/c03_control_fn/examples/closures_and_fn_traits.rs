fn call_fn<F: Fn()>(f: F) { f(); }
fn call_fnmut<F: FnMut()>(mut f: F) { f(); }
fn call_fnonce<F: FnOnce()>(f: F) { f(); }

fn make_adder(delta: i32) -> impl Fn(i32) -> i32 {
    move |x| x + delta
}

fn spawn_thread() {
    let data = String::from("msg");
    std::thread::spawn(move || {
        println!("{}", data);
    }).join().unwrap();
}

fn main() {
    let x = 1;
    call_fn(|| { let _ = x; });

    let mut y = 0;
    call_fnmut(|| { y += 1; });
    assert_eq!(y, 1);

    let s = String::from("hi");
    call_fnonce(|| drop(s));

    let add5 = make_adder(5);
    assert_eq!(add5(3), 8);

    spawn_thread();
}


