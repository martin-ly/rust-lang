#[test]
fn test_iterator_chain_sum() {
    let xs = vec![1, 2, 3, 4, 5];
    let s: i32 = xs.iter().map(|x| x * 2).filter(|x| *x % 4 == 0).sum();
    assert_eq!(s, 12); // map*2: [2,4,6,8,10] -> filter%4==0: [4,8] -> sum=12
}

#[test]
fn test_collect_vec() {
    let xs = vec![1, 2, 3];
    let ys: Vec<_> = xs.into_iter().map(|x| x + 1).collect();
    assert_eq!(ys, vec![2, 3, 4]);
}


