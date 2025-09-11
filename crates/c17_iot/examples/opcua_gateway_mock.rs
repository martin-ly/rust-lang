use c17_iot::types::{UaNodeId, UaObjectNode, UaVariableNode};

fn main() {
    // 构造一个 OPC UA 对象节点，聚合两个变量节点
    let mut obj = UaObjectNode {
        node_id: UaNodeId("ns=1;i=1001".into()),
        browse_name: "Gateway".into(),
        variables: vec![
            UaVariableNode {
                node_id: UaNodeId("ns=1;i=2001".into()),
                browse_name: "Temp".into(),
                value: serde_json::json!(21.7),
                writable: false,
            },
            UaVariableNode {
                node_id: UaNodeId("ns=1;i=2002".into()),
                browse_name: "Mode".into(),
                value: serde_json::json!("auto"),
                writable: true,
            },
        ],
    };

    let temp = obj.read("Temp").unwrap();
    println!("Temp={}", temp);

    let ok = obj.write("Mode", serde_json::json!("manual"));
    println!("write Mode -> {}", ok);
    println!("Mode={}", obj.read("Mode").unwrap());
}


