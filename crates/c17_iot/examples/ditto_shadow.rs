use serde::{Deserialize, Serialize};

// 模拟 Eclipse Ditto 兼容的设备孪生文档（极简）
#[derive(Debug, Serialize, Deserialize)]
struct ThingShadow {
    thing_id: String,
    desired: serde_json::Value,
    reported: serde_json::Value,
}

fn main() -> anyhow::Result<()> {
    let desired = serde_json::json!({"led": true, "threshold": 42});
    let reported = serde_json::json!({"led": false, "threshold": 40});
    let shadow = ThingShadow {
        thing_id: "c17-iot-1".into(),
        desired,
        reported,
    };

    let payload = serde_json::to_string_pretty(&shadow)?;
    println!("shadow document:\n{}", payload);

    // 计算需要下发的变更
    let desired_led = shadow.desired.get("led").and_then(|v| v.as_bool()).unwrap_or(false);
    let reported_led = shadow.reported.get("led").and_then(|v| v.as_bool()).unwrap_or(false);
    if desired_led != reported_led {
        println!("action: set led -> {}", desired_led);
    } else {
        println!("action: no-op");
    }
    Ok(())
}


