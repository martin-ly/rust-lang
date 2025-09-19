const fn fib(n: usize) -> usize { if n < 2 { n } else { fib(n - 1) + fib(n - 2) } }

trait SizedInfo { const SIZE: usize; }

impl<T> SizedInfo for [T; 4] { const SIZE: usize = 4; }
impl<T> SizedInfo for [T; 8] { const SIZE: usize = 8; }

#[test]
fn test_fib_const() {
    const F6: usize = fib(6);
    assert_eq!(F6, 8);
}

#[test]
fn test_assoc_consts() {
    assert_eq!(<[i32; 4] as SizedInfo>::SIZE, 4);
    assert_eq!(<[i32; 8] as SizedInfo>::SIZE, 8);
}


