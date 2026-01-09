use std::fs::File;
use std::io::Write;
use std::time::Instant;

#[derive(Clone, Copy)]
enum OutputFormat {
    Csv,
    Json,
}

struct Args {
    format: OutputFormat,
    output: Option<String>,
    select: Option<String>,
    preset: Option<String>,
    repeat: usize,
}

fn parse_args() -> Args {
    let mut format = OutputFormat::Csv;
    let mut output = None;
    let mut select = None;
    let mut preset = None;
    let mut repeat = 1usize;
    let mut iter = std::env::args().skip(1);
    while let Some(arg) = iter.next() {
        match arg.as_str() {
            "--format" => {
                if let Some(v) = iter.next() {
                    format = if v.eq_ignore_ascii_case("json") {
                        OutputFormat::Json
                    } else {
                        OutputFormat::Csv
                    };
                }
            }
            "--output" => {
                output = iter.next();
            }
            "--select" => {
                select = iter.next();
            }
            "--preset" => {
                preset = iter.next();
            }
            "--repeat" => {
                if let Some(v) = iter.next() {
                    repeat = v.parse().unwrap_or(1);
                }
            }
            _ => {}
        }
    }
    Args {
        format,
        output,
        select,
        preset,
        repeat,
    }
}

use c08_algorithms::backtracking::*;
use c08_algorithms::divide_and_conquer::*;
use c08_algorithms::dynamic_programming::*;
use c08_algorithms::graph::*;
use c08_algorithms::searching::*;
use c08_algorithms::sorting::*;
use c08_algorithms::string_algorithms::*;

fn time_it<F, R>(mut f: F) -> (R, u128)
where
    F: FnMut() -> R,
{
    let t0 = Instant::now();
    let r = f();
    (r, t0.elapsed().as_micros())
}

fn main() {
    let args = parse_args();
    let mut sink: Box<dyn Write> = if let Some(path) = &args.output {
        Box::new(File::create(path).expect("create output"))
    } else {
        Box::new(std::io::stdout())
    };

    if let OutputFormat::Csv = args.format {
        let _ = writeln!(sink, "category,algo,variant,param,size,unit,micros");
    }

    let mut json_items: Vec<serde_json::Value> = Vec::new();
    let mut write_row = |category: &str,
                         algo: &str,
                         variant: &str,
                         param: &str,
                         size: usize,
                         unit: &str,
                         micros: u128| {
        match args.format {
            OutputFormat::Csv => {
                let _ = writeln!(
                    sink,
                    "{category},{algo},{variant},{param},{size},{unit},{micros}"
                );
            }
            OutputFormat::Json => {
                json_items.push(serde_json::json!({
                    "category": category,
                    "algo": algo,
                    "variant": variant,
                    "param": param,
                    "size": size,
                    "unit": unit,
                    "micros": micros
                }));
            }
        }
    };

    // header already written for CSV above

    // 排序：不同 n
    let preset = args.preset.clone().unwrap_or_else(|| "default".to_string());
    let sizes_sort: Vec<usize> = match preset.as_str() {
        "quick" => vec![50_000, 200_000, 1_000_000],
        _ => vec![10_000, 50_000, 100_000],
    };

    if args.select.as_deref().unwrap_or("").contains("sorting") || args.select.is_none() {
        for &n in &sizes_sort {
            let mut v: Vec<i32> = (0..n as i32).rev().collect();
            let mut best = u128::MAX;
            for _ in 0..args.repeat {
                let (_r, us) = time_it(|| {
                    sort_sync(&mut v, SortingAlgo::Quick);

                });
                best = best.min(us);
            }
            write_row("sorting", "quick", "sync", "n", n, "items", best);

            let mut v: Vec<i32> = (0..n as i32).rev().collect();
            let mut best = u128::MAX;
            for _ in 0..args.repeat {
                let (_r, us) = time_it(|| {
                    sort_parallel(&mut v, SortingAlgo::Quick);

                });
                best = best.min(us);
            }
            write_row("sorting", "quick", "parallel", "n", n, "items", best);
        }
    }

    // 搜索：二分/并行线性
    if args.select.as_deref().unwrap_or("").contains("searching") || args.select.is_none() {
        for &n in &[100_000usize, 500_000] {
            let data: Vec<i32> = (0..n as i32).collect();
            let mut best = u128::MAX;
            for _ in 0..args.repeat {
                let (_r, us) = time_it(|| binary_search_sync(&data, &(n as i32 - 1)).unwrap());
                best = best.min(us);
            }
            write_row("searching", "binary", "sync", "n", n, "items", best);
            let mut best = u128::MAX;
            for _ in 0..args.repeat {
                let (_r, us) = time_it(|| parallel_search(&data, &42));
                best = best.min(us);
            }
            write_row("searching", "linear", "parallel", "n", n, "items", best);
        }
    }

    // 图：BFS/Dijkstra 简档
    let mut g: std::collections::HashMap<i32, Vec<i32>> = std::collections::HashMap::new();
    for i in 0..10_000 {
        g.insert(i, vec![i + 1]);
    }
    g.insert(10_000, vec![]);
    if args.select.as_deref().unwrap_or("").contains("graph") || args.select.is_none() {
        let mut best = u128::MAX;
        for _ in 0..args.repeat {
            let (_r, us) = time_it(|| bfs_shortest_path_sync(&g, &0, &10_000));
            best = best.min(us);
        }
        write_row("graph", "bfs", "sync", "n", 10_000, "nodes", best);

        let mut wg: std::collections::HashMap<i32, Vec<(i32, f64)>> =
            std::collections::HashMap::new();
        for i in 0..10_000 {
            wg.insert(i, vec![(i + 1, 1.0)]);
        }
        wg.insert(10_000, vec![]);
        let mut best = u128::MAX;
        for _ in 0..args.repeat {
            let (_r, us) = time_it(|| dijkstra_sync(&wg, &0));
            best = best.min(us);
        }
        write_row("graph", "dijkstra", "sync", "n", 10_000, "nodes", best);
    }

    // 分治/DP：代表性规模
    let nums: Vec<i64> = (0..200_000)
        .map(|i| if i % 10 == 0 { -5 } else { 3 })
        .collect();
    if args.select.as_deref().unwrap_or("").contains("dac") || args.select.is_none() {
        let mut best = u128::MAX;
        for _ in 0..args.repeat {
            let (_r, us) = time_it(|| max_subarray_sum_parallel(&nums));
            best = best.min(us);
        }
        write_row(
            "dac",
            "max_subarray",
            "parallel",
            "n",
            200_000,
            "items",
            best,
        );
    }

    let a = vec![b'A'; 2000];
    let b = vec![b'A'; 2000];
    if args.select.as_deref().unwrap_or("").contains("dp") || args.select.is_none() {
        let mut best = u128::MAX;
        for _ in 0..args.repeat {
            let (_r, us) = time_it(|| lcs_parallel(&a, &b));
            best = best.min(us);
        }
        write_row("dp", "lcs", "parallel", "n", 2000, "chars", best);
    }

    // 字符串：KMP/RK/AC
    if args.select.as_deref().unwrap_or("").contains("strings") || args.select.is_none() {
        for &n in &[10_000usize, 100_000] {
            let text: String = (0..n)
                .map(|i| char::from(((i * 131) % 26) as u8 + b'a'))
                .collect();
            let pattern = "abcab".to_string();
            let mut best = u128::MAX;
            for _ in 0..args.repeat {
                let (_r, us) = time_it(|| kmp_search(&text, &pattern));
                best = best.min(us);
            }
            write_row("strings", "kmp", "sync", "n", n, "chars", best);
            let mut best = u128::MAX;
            for _ in 0..args.repeat {
                let (_r, us) = time_it(|| rabin_karp_search(&text, &pattern));
                best = best.min(us);
            }
            write_row("strings", "rk", "sync", "n", n, "chars", best);
        }
        let text = "ahishers".to_string();
        let patterns = ["he".to_string(),
            "she".to_string(),
            "hers".to_string(),
            "his".to_string()];
        let mut best = u128::MAX;
        for _ in 0..args.repeat {
            let (_r, us) = time_it(|| {
                let pats: Vec<Vec<u8>> = patterns.iter().map(|s| s.as_bytes().to_vec()).collect();
                let trie = build_trie(&pats);
                trie.ac_search(text.as_bytes(), &pats)
            });
            best = best.min(us);
        }
        write_row("strings", "ac", "sync", "n", 8, "chars", best);
    }

    // 回溯：N 皇后计数
    if args
        .select
        .as_deref()
        .unwrap_or("")
        .contains("backtracking")
        || args.select.is_none()
    {
        for &n in &[10usize, 11] {
            let mut best = u128::MAX;
            for _ in 0..args.repeat {
                let (_r, us) = time_it(|| nqueens_count_parallel(n));
                best = best.min(us);
            }
            write_row("backtracking", "nqueens", "parallel", "n", n, "board", best);
        }
    }

    // flush stdout
    match args.format {
        OutputFormat::Csv => {
            let _ = sink.flush();
        }
        OutputFormat::Json => {
            let _ = writeln!(
                sink,
                "{}",
                serde_json::to_string_pretty(&json_items).unwrap()
            );
        }
    }
}
