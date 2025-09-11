use c17_iot::types::{Lwm2mInstance, Lwm2mObject, Lwm2mResource, Lwm2mValue};

fn main() {
    // 构建一个极简的 LwM2M 对象（Object 3303 温度传感器）
    let mut obj = Lwm2mObject {
        object_id: 3303,
        instances: vec![Lwm2mInstance {
            instance_id: 0,
            resources: vec![
                Lwm2mResource { // 5700: Sensor Value
                    id: 5700,
                    readable: true,
                    writable: false,
                    executable: false,
                    value: Some(Lwm2mValue::Float(21.5)),
                },
                Lwm2mResource { // 5601: Min Measured Value
                    id: 5601,
                    readable: true,
                    writable: false,
                    executable: false,
                    value: Some(Lwm2mValue::Float(20.0)),
                },
                Lwm2mResource { // 5602: Max Measured Value
                    id: 5602,
                    readable: true,
                    writable: false,
                    executable: false,
                    value: Some(Lwm2mValue::Float(25.0)),
                },
            ],
        }],
    };

    // 读取当前值
    if let Some(Lwm2mValue::Float(v)) = obj.read(0, 5700) {
        println!("temp value = {:.2}", v);
    }

    // 尝试写入只读资源（应失败）
    let ok = obj.write(0, 5700, Lwm2mValue::Float(22.0));
    println!("write readonly result = {}", ok);

    // 添加一个可写资源（应用配置）并写入
    if let Some(inst) = obj.instances.iter_mut().find(|i| i.instance_id == 0) {
        inst.resources.push(Lwm2mResource {
            id: 5900, // 自定义配置
            readable: true,
            writable: true,
            executable: false,
            value: Some(Lwm2mValue::String("default".into())),
        });
    }
    let ok2 = obj.write(0, 5900, Lwm2mValue::String("high-precision".into()));
    println!("write cfg result = {}", ok2);
}


