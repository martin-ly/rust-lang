use c08_algorithms::sorting::{sort_sync, sort_parallel, sort_async, SortingAlgo};
use c08_algorithms::searching::{binary_search_sync, parallel_search};
use c08_algorithms::graph::{bfs_shortest_path_sync, bfs_shortest_path_async};
use c08_algorithms::string_algorithms::{kmp_search_async, rabin_karp_search_async, ac_search_async};

#[tokio::main]
async fn main() {
    // 排序演示
    let mut v = vec![3, 1, 4, 1, 5, 9];
    sort_sync(&mut v, SortingAlgo::Merge);
    sort_parallel(&mut v, SortingAlgo::Quick);
    let v = sort_async(v, SortingAlgo::Heap).await.expect("sort_async failed");
    println!("sorted: {:?}", &v[..std::cmp::min(6, v.len())]);

    // 搜索演示
    let _ = binary_search_sync(&v, &5).expect("binary_search_sync failed");
    let _ = parallel_search(&v, &5);

    // 图演示
    use std::collections::HashMap;
    let mut g: HashMap<i32, Vec<i32>> = HashMap::new();
    g.insert(1, vec![2, 3]); g.insert(2, vec![4]); g.insert(3, vec![4]); g.insert(4, vec![]);
    let _ = bfs_shortest_path_sync(&g, &1, &4);
    let _ = bfs_shortest_path_async(g, 1, 4).await.expect("bfs_async failed");

    // 字符串算法演示
    let _k = kmp_search_async("ababcabcabababd".into(), "ababd".into()).await.expect("kmp");
    let _rk = rabin_karp_search_async("abracadabra".into(), "abra".into()).await.expect("rk");
    let _ac = ac_search_async("ahishers".into(), vec!["he".into(), "she".into(), "hers".into(), "his".into()])
        .await.expect("ac");

    println!("demo completed");
}

