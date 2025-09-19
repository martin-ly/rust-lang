#[inline]
fn classify(x: i32) -> i32 {
    if x == 0 { return 0; }
    if x > 0 { 1 } else { -1 }
}

fn abs_i32(x: i32) -> i32 { if x >= 0 { x } else { -x } }

fn sum_iter_chain(v: &[i32]) -> i32 {
    v.iter().copied().filter(|x| *x > 0).map(|x| x * 2).sum()
}

fn sum_manual_loop(v: &[i32]) -> i32 {
    let mut acc = 0;
    for &x in v {
        if x > 0 { acc += x * 2; }
    }
    acc
}

fn main() {
    assert_eq!(classify(0), 0);
    assert_eq!(classify(3), 1);
    assert_eq!(classify(-3), -1);

    assert_eq!(abs_i32(-5), 5);

    let data = [1,-2,3,0,4];
    assert_eq!(sum_iter_chain(&data), 1*2 + 3*2 + 4*2);
    assert_eq!(sum_manual_loop(&data), 1*2 + 3*2 + 4*2);
}


