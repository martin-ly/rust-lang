// Async control flow example snippet
// This demonstrates basic async control flow patterns in Rust

/// Simple async function that returns a result
async fn fetch_data(id: u32) -> Result<String, &'static str> {
    if id == 0 {
        return Err("Invalid ID");
    }
    Ok(format!("Data for ID: {}", id))
}

/// Demonstrates async control flow with match
async fn process_with_match(id: u32) -> String {
    match fetch_data(id).await {
        Ok(data) => format!("Success: {}", data),
        Err(e) => format!("Error: {}", e),
    }
}

/// Demonstrates async control flow with if-let
async fn process_with_if_let(id: u32) -> String {
    if let Ok(data) = fetch_data(id).await {
        format!("Got data: {}", data)
    } else {
        "Failed to fetch data".to_string()
    }
}

/// Main run function that the test calls
pub async fn run() {
    // Test various async control flow patterns
    let result1 = process_with_match(1).await;
    println!("{}", result1);

    let result2 = process_with_if_let(2).await;
    println!("{}", result2);

    let result3 = process_with_match(0).await;
    println!("{}", result3);

    // Demonstrate async loop control flow
    for i in 1..=3 {
        let data = fetch_data(i).await;
        if let Ok(d) = data {
            println!("Iteration {}: {}", i, d);
        }
    }
}
