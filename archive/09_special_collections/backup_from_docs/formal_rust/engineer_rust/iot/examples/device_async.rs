// 物联网异步设备读取示例 IoT Async Device Read Example
trait Device {
    async fn read(&self) -> u32;
}

struct Sensor;

#[tokio::main]
async fn main() {
    let s = Sensor;
    let value = s.read().await;
    println!("Sensor value: {}", value);
}

impl Device for Sensor {
    async fn read(&self) -> u32 {
        123 // 模拟传感器数据
    }
} 