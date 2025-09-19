fn search_2d(grid: &[Vec<i32>], target: i32) -> Option<(usize, usize)> {
    for (r, row) in grid.iter().enumerate() {
        for (c, &val) in row.iter().enumerate() {
            if val == target { return Some((r, c)); }
        }
    }
    None
}

fn first_positive(nums: &[i32]) -> Option<i32> {
    // 更直接且避免 break 目标歧义
    nums.iter().copied().find(|&n| n > 0)
}

fn sum_even_u32<I: IntoIterator<Item = u32>>(iter: I) -> Result<u64, &'static str> {
    iter.into_iter().try_fold(0u64, |acc, x| {
        if x % 2 == 0 { Ok(acc + x as u64) } else { Err("odd") }
    })
}

fn main() {
    let g = vec![vec![1,2], vec![3,4,5]];
    assert_eq!(search_2d(&g, 4), Some((1,1)));
    assert_eq!(search_2d(&g, 6), None);

    assert_eq!(first_positive(&[-3,-1,0,7]), Some(7));

    assert_eq!(sum_even_u32([2,4,6]), Ok(12));
    assert_eq!(sum_even_u32([2,3,4]).unwrap_err(), "odd");
}


