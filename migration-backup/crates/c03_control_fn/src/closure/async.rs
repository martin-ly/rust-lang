// 定义一个异步函数，接受一个实现 FnOnce 的闭包
#[allow(unused)]
pub async fn async_fn_once<F>(f: F)
where
    F: FnOnce() -> i32,
{
    let result = f();
    println!("FnOnce result: {}", result);
}

// 定义一个异步函数，接受一个实现 FnMut 的闭包
#[allow(unused)]
pub async fn async_fn_mut<F>(mut f: F)
where
    F: FnMut() -> i32,
{
    let result = f();
    println!("FnMut result: {}", result);
}

// 定义一个异步函数，接受一个实现 Fn 的闭包
#[allow(unused)]
pub async fn async_fn<F>(f: F)
where
    F: Fn() -> i32,
{
    let result = f();
    println!("Fn result: {}", result);
}
