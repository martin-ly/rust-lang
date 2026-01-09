trait Accumulate<T> { fn accumulate(&self, input: &[T]) -> T; }

struct Sum;
impl Accumulate<i32> for Sum { fn accumulate(&self, input: &[i32]) -> i32 { input.iter().copied().sum() } }

fn static_dispatch<A>(acc: &A, data: &[i32]) -> i32
where
    A: Accumulate<i32>,
{
    acc.accumulate(data)
}

fn dynamic_dispatch(acc: &dyn Accumulate<i32>, data: &[i32]) -> i32 { acc.accumulate(data) }

fn main() {
    let data = [1, 2, 3, 4];
    let s = Sum;
    println!("static={}, dynamic={}", static_dispatch(&s, &data), dynamic_dispatch(&s, &data));
}
