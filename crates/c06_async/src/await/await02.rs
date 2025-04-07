use reqwest::{Client, Error};

async fn fetch_data(url: &str, client: &Client) -> Result<String, Error> {
    // 异步获取数据
    let response = client.get(url).send().await?;
    let body = response.text().await?;
    Ok(body)
}

pub async fn process() {
    // 创建带有超时设置的 Client
    let client = Client::builder()
        .timeout(std::time::Duration::from_secs(1))
        .build()
        .unwrap();

    let client2 = Client::builder()
        .timeout(std::time::Duration::from_secs(2))
        .build()
        .unwrap();

    //let client3 = client.clone();
    // 并发获取多个数据源
    let results = futures::join!(
        fetch_data("https://example.com/api/1", &client),
        fetch_data("https://example.com/api/2", &client2)
    );

    // 处理结果
    match results {
        (Ok(data1), Ok(data2)) => {
            println!(
                "获取到两个数据源: {} 字节和 {} 字节",
                data1.len(),
                data2.len()
            );
            //println!("data1: {:?}", data1);
            //println!("data2: {:?}", data2);
        }
        (Err(e1), Err(e2)) => {
            println!("获取数据时出错: {:?}, {:?}", e1, e2);
        }
        (Err(e1), Ok(data2)) => {
            println!("获取数据时出错: {:?}", e1);
            println!("获取数据长度: {:?}", data2.len());
            //println!("获取数据: {:?}", data2);
        }
        (Ok(data1), Err(e2)) => {
            println!("获取数据时出错: {:?}", e2);
            println!("获取数据长度: {:?}", data1.len());
            //println!("获取数据: {:?}", data1);
        }
    }
}
