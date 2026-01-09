const fn fib(n: usize) -> usize { if n < 2 { n } else { fib(n - 1) + fib(n - 2) } }

trait SizedInfo { const SIZE: usize; }

impl<T> SizedInfo for [T; 8] { const SIZE: usize = 8; }
impl<T> SizedInfo for [T; 16] { const SIZE: usize = 16; }

fn main() {
    const F10: usize = fib(10);
    println!("fib(10) = {}", F10);

    let _a: [i32; 8] = [0; 8];
    let _b: [i32; 16] = [0; 16];
    println!("SIZE a={}, b={}", <[i32; 8] as SizedInfo>::SIZE, <[i32; 16] as SizedInfo>::SIZE);
}
