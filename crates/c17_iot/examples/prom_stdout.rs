fn export_metric(name: &str, value: f64, labels: &[(&str, &str)]) {
    let mut label_str = String::new();
    for (k, v) in labels {
        if !label_str.is_empty() { label_str.push(','); }
        label_str.push_str(&format!("{}={}", k, v));
    }
    println!("metric name={} value={} labels={}", name, value, label_str);
}

fn main() {
    // 打印几条“指标”到 stdout，实际可对接 prometheus_exporter
    export_metric("iot_temp_c", 21.6, &[("device", "d1"), ("room", "r1")]);
    export_metric("iot_hum_pct", 45.0, &[("device", "d1")]);
    export_metric("iot_packet_bytes", 128.0, &[]);
}


