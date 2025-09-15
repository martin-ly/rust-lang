//! Minimal basic_ml example to satisfy workspace build.

use rand::{Rng, rngs::ThreadRng};

fn main() {
    // Simple linear model y = 2x + 1 with random x
    let mut rng = ThreadRng::default();
    let mut sum = 0.0f32;
    for _ in 0..10 {
        let x: f32 = rng.random_range(0.0..1.0);
        let y = 2.0 * x + 1.0;
        sum += y;
    }
    println!("basic_ml avg_y={:.3}", sum / 10.0);
}


