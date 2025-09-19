fn main() {
    let xs = vec![1, 2, 3, 4, 5];
    // 纯迭代器链：map + filter + sum
    let s: i32 = xs.iter().map(|x| x * 2).filter(|x| *x % 4 == 0).sum();
    println!("sum={}", s);

    // FromIterator: collect 到 Vec
    let ys: Vec<_> = xs.into_iter().map(|x| x + 1).collect();
    println!("ys={:?}", ys);
}


