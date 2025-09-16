use std::time::Instant;

// 模拟边缘侧采集、聚合与输出到本地（替代实际 InfluxDB/Telegraf）
fn main() {
    let start = Instant::now();
    let samples = vec![("temp", 21.5_f64), ("temp", 21.6), ("hum", 45.2)];
    let avg_temp: f64 = {
        let vals: Vec<f64> = samples
            .iter()
            .filter(|(k, _)| *k == "temp")
            .map(|(_, v)| *v)
            .collect();
        vals.iter().sum::<f64>() / (vals.len().max(1) as f64)
    };

    println!("edge avg temp = {:.2}", avg_temp);
    println!("elapsed_ms = {}", start.elapsed().as_millis());
}
