use c09_design_pattern::parallel::pipeline::define::make_pipeline_iter;

fn main() {
    let data = [1, 2, 3, 4, 5, 6];
    let v: Vec<i32> = make_pipeline_iter(&data).collect();
    println!("pipeline_iter_demo: {:?}", v);
}


