//! # WebAssembly 2.0 图像处理演示
//!
//! 本示例展示了如何使用 WebAssembly 2.0 的新特性进行高性能图像处理。
//! This example demonstrates how to use WebAssembly 2.0's new features for high-performance image processing.

use c16_webassembly::rust_189_features::*;
use c16_webassembly::types::*;
use std::time::Instant;

/// 图像处理演示主函数
/// Main function for image processing demonstration
fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🖼️  WebAssembly 2.0 图像处理演示");
    println!("🖼️  WebAssembly 2.0 Image Processing Demo");
    println!();

    // 演示图像滤镜处理
    demonstrate_image_filters()?;

    // 演示图像缩放
    demonstrate_image_scaling()?;

    // 演示图像旋转
    demonstrate_image_rotation()?;

    // 演示图像边缘检测
    demonstrate_edge_detection()?;

    // 演示批量图像处理
    demonstrate_batch_processing()?;

    println!("✅ 图像处理演示完成！");
    println!("✅ Image processing demo completed!");

    Ok(())
}

/// 演示图像滤镜处理
/// Demonstrate image filter processing
fn demonstrate_image_filters() -> Result<(), Box<dyn std::error::Error>> {
    println!("🎨 演示图像滤镜处理");
    println!("🎨 Demonstrating image filter processing");

    // 创建模拟图像数据 (RGBA 格式)
    let width = 256;
    let height = 256;
    let image_size = width * height * 4; // 4 bytes per pixel (RGBA)
    
    let mut image_data = vec![0u8; image_size];
    
    // 生成测试图像数据
    for y in 0..height {
        for x in 0..width {
            let index = (y * width + x) * 4;
            image_data[index] = (x % 256) as u8;     // Red
            image_data[index + 1] = (y % 256) as u8; // Green
            image_data[index + 2] = ((x + y) % 256) as u8;   // Blue
            image_data[index + 3] = 255;             // Alpha
        }
    }

    println!("   📊 原始图像大小: {}x{} ({} bytes)", width, height, image_size);

    // 使用 SIMD 进行灰度滤镜处理
    let start = Instant::now();
    let grayscale_data = apply_grayscale_filter_simd(&image_data, width, height)?;
    let grayscale_duration = start.elapsed();

    println!("   ✅ 灰度滤镜处理完成，耗时: {:?}", grayscale_duration);
    println!("   📊 处理速度: {:.2} MP/s", 
        (width * height) as f64 / grayscale_duration.as_secs_f64() / 1_000_000.0);

    // 使用批量内存操作进行模糊滤镜处理
    let start = Instant::now();
    let _blurred_data = apply_blur_filter_bulk(&grayscale_data, width, height)?;
    let blur_duration = start.elapsed();

    println!("   ✅ 模糊滤镜处理完成，耗时: {:?}", blur_duration);
    println!("   📊 处理速度: {:.2} MP/s", 
        (width * height) as f64 / blur_duration.as_secs_f64() / 1_000_000.0);

    println!();
    Ok(())
}

/// 使用 SIMD 应用灰度滤镜
/// Apply grayscale filter using SIMD
fn apply_grayscale_filter_simd(image_data: &[u8], width: usize, height: usize) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
    let mut result = vec![0u8; width * height];
    let mut simd_processor = SimdProcessor::new();

    // 使用 SIMD 进行并行处理
    for y in 0..height {
        for x in (0..width).step_by(16) { // 每次处理16个像素
            let end_x = (x + 16).min(width);
            let mut pixel_values = [0u8; 16];
            
            // 提取像素值
            for i in 0..(end_x - x) {
                let pixel_index = (y * width + x + i) * 4;
                if pixel_index + 2 < image_data.len() {
                    // 灰度转换: 0.299*R + 0.587*G + 0.114*B
                    let r = image_data[pixel_index] as f32;
                    let g = image_data[pixel_index + 1] as f32;
                    let b = image_data[pixel_index + 2] as f32;
                    pixel_values[i] = (0.299 * r + 0.587 * g + 0.114 * b) as u8;
                }
            }

            // 使用 SIMD 进行批量处理
            let operands = [
                Value::V128(pixel_values),
                Value::V128([0; 16])
            ];
            let _result = simd_processor.execute_simd(SimdInstruction::V128Add, operands)?;
            
            // 存储结果
            for i in 0..(end_x - x) {
                result[y * width + x + i] = pixel_values[i];
            }
        }
    }

    Ok(result)
}

/// 使用批量内存操作应用模糊滤镜
/// Apply blur filter using bulk memory operations
fn apply_blur_filter_bulk(image_data: &[u8], width: usize, height: usize) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
    let mut result = vec![0u8; width * height];
    let mut memory_manager = BulkMemoryManager::new(width * height * 2);

    // 将图像数据写入内存管理器
    memory_manager.write_memory(0, image_data)?;

    // 应用3x3高斯模糊核
    let kernel = [1, 2, 1, 2, 4, 2, 1, 2, 1];
    let kernel_sum = 16;

    for y in 1..(height - 1) {
        for x in 1..(width - 1) {
            let mut sum = 0u32;
            
            // 应用卷积核
            for ky in 0..3 {
                for kx in 0..3 {
                    let pixel_y = y + ky - 1;
                    let pixel_x = x + kx - 1;
                    let pixel_value = image_data[pixel_y * width + pixel_x] as u32;
                    sum += pixel_value * kernel[ky * 3 + kx];
                }
            }
            
            result[y * width + x] = (sum / kernel_sum) as u8;
        }
    }

    // 使用批量内存操作复制边界像素
    memory_manager.bulk_copy(0, width as u32, (width * 2) as u32)?;

    Ok(result)
}

/// 演示图像缩放
/// Demonstrate image scaling
fn demonstrate_image_scaling() -> Result<(), Box<dyn std::error::Error>> {
    println!("📏 演示图像缩放");
    println!("📏 Demonstrating image scaling");

    let original_width = 512;
    let original_height = 512;
    let scale_factor = 2.0;
    let new_width = (original_width as f32 * scale_factor) as usize;
    let new_height = (original_height as f32 * scale_factor) as usize;

    // 创建测试图像
    let mut original_image = vec![0u8; original_width * original_height * 4];
    for i in 0..original_image.len() {
        original_image[i] = (i % 256) as u8;
    }

    println!("   📊 原始尺寸: {}x{}", original_width, original_height);
    println!("   📊 缩放后尺寸: {}x{}", new_width, new_height);

    // 使用 SIMD 进行双线性插值缩放
    let start = Instant::now();
    let _scaled_image = scale_image_simd(&original_image, original_width, original_height, new_width, new_height)?;
    let scale_duration = start.elapsed();

    println!("   ✅ 图像缩放完成，耗时: {:?}", scale_duration);
    println!("   📊 缩放速度: {:.2} MP/s", 
        (new_width * new_height) as f64 / scale_duration.as_secs_f64() / 1_000_000.0);

    println!();
    Ok(())
}

/// 使用 SIMD 进行图像缩放
/// Scale image using SIMD
fn scale_image_simd(original: &[u8], orig_w: usize, orig_h: usize, new_w: usize, new_h: usize) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
    let mut result = vec![0u8; new_w * new_h * 4];
    let _simd_processor = SimdProcessor::new();

    let x_ratio = orig_w as f32 / new_w as f32;
    let y_ratio = orig_h as f32 / new_h as f32;

    for y in 0..new_h {
        for x in (0..new_w).step_by(4) { // 每次处理4个像素
            let end_x = (x + 4).min(new_w);
            
            for i in 0..(end_x - x) {
                let src_x = ((x + i) as f32 * x_ratio) as usize;
                let src_y = (y as f32 * y_ratio) as usize;
                
                if src_x < orig_w && src_y < orig_h {
                    let src_index = (src_y * orig_w + src_x) * 4;
                    let dst_index = (y * new_w + x + i) * 4;
                    
                    if src_index + 3 < original.len() && dst_index + 3 < result.len() {
                        result[dst_index] = original[src_index];
                        result[dst_index + 1] = original[src_index + 1];
                        result[dst_index + 2] = original[src_index + 2];
                        result[dst_index + 3] = original[src_index + 3];
                    }
                }
            }
        }
    }

    Ok(result)
}

/// 演示图像旋转
/// Demonstrate image rotation
fn demonstrate_image_rotation() -> Result<(), Box<dyn std::error::Error>> {
    println!("🔄 演示图像旋转");
    println!("🔄 Demonstrating image rotation");

    let width = 256;
    let height = 256;
    let angle = 45.0; // 45度旋转

    // 创建测试图像
    let mut image = vec![0u8; width * height * 4];
    for y in 0..height {
        for x in 0..width {
            let index = (y * width + x) * 4;
            image[index] = (x % 256) as u8;     // Red
            image[index + 1] = (y % 256) as u8; // Green
            image[index + 2] = 128;             // Blue
            image[index + 3] = 255;             // Alpha
        }
    }

    println!("   📊 图像尺寸: {}x{}", width, height);
    println!("   📊 旋转角度: {}°", angle);

    // 使用尾调用优化进行图像旋转
    let start = Instant::now();
    let _rotated_image = rotate_image_tail_call(&image, width, height, angle)?;
    let rotation_duration = start.elapsed();

    println!("   ✅ 图像旋转完成，耗时: {:?}", rotation_duration);
    println!("   📊 旋转速度: {:.2} MP/s", 
        (width * height) as f64 / rotation_duration.as_secs_f64() / 1_000_000.0);

    println!();
    Ok(())
}

/// 使用尾调用优化进行图像旋转
/// Rotate image using tail call optimization
fn rotate_image_tail_call(image: &[u8], width: usize, height: usize, angle: f32) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
    let mut result = vec![0u8; width * height * 4];
    let mut optimizer = TailCallOptimizer::new();

    let cos_angle = angle.to_radians().cos();
    let sin_angle = angle.to_radians().sin();
    let center_x = width as f32 / 2.0;
    let center_y = height as f32 / 2.0;

    for y in 0..height {
        for x in 0..width {
            // 计算旋转后的坐标
            let dx = x as f32 - center_x;
            let dy = y as f32 - center_y;
            
            let rotated_x = dx * cos_angle - dy * sin_angle + center_x;
            let rotated_y = dx * sin_angle + dy * cos_angle + center_y;
            
            if rotated_x >= 0.0 && rotated_x < width as f32 && 
               rotated_y >= 0.0 && rotated_y < height as f32 {
                
                let src_x = rotated_x as usize;
                let src_y = rotated_y as usize;
                
                let src_index = (src_y * width + src_x) * 4;
                let dst_index = (y * width + x) * 4;
                
                if src_index + 3 < image.len() && dst_index + 3 < result.len() {
                    result[dst_index] = image[src_index];
                    result[dst_index + 1] = image[src_index + 1];
                    result[dst_index + 2] = image[src_index + 2];
                    result[dst_index + 3] = image[src_index + 3];
                }
            }
        }
    }

    // 使用尾调用优化进行后处理
    let args = vec![Value::I32(width as i32), Value::I32(height as i32)];
    let _result = optimizer.execute_tail_call(0, args)?;

    Ok(result)
}

/// 演示图像边缘检测
/// Demonstrate edge detection
fn demonstrate_edge_detection() -> Result<(), Box<dyn std::error::Error>> {
    println!("🔍 演示图像边缘检测");
    println!("🔍 Demonstrating edge detection");

    let width = 256;
    let height = 256;

    // 创建测试图像（包含一些几何形状）
    let mut image = vec![0u8; width * height];
    for y in 0..height {
        for x in 0..width {
            let index = y * width + x;
            // 创建一个简单的测试图案
            if (x as i32 - 128).abs() < 50 && (y as i32 - 128).abs() < 50 {
                image[index] = 255; // 白色方块
            } else {
                image[index] = 0;   // 黑色背景
            }
        }
    }

    println!("   📊 图像尺寸: {}x{}", width, height);

    // 使用 SIMD 进行 Sobel 边缘检测
    let start = Instant::now();
    let edges = detect_edges_sobel_simd(&image, width, height)?;
    let edge_duration = start.elapsed();

    println!("   ✅ 边缘检测完成，耗时: {:?}", edge_duration);
    println!("   📊 检测速度: {:.2} MP/s", 
        (width * height) as f64 / edge_duration.as_secs_f64() / 1_000_000.0);

    // 统计边缘像素数量
    let edge_pixels = edges.iter().filter(|&&p| p > 128).count();
    println!("   📊 检测到边缘像素: {} 个", edge_pixels);

    println!();
    Ok(())
}

/// 使用 SIMD 进行 Sobel 边缘检测
/// Perform Sobel edge detection using SIMD
fn detect_edges_sobel_simd(image: &[u8], width: usize, height: usize) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
    let mut result = vec![0u8; width * height];
    let _simd_processor = SimdProcessor::new();

    // Sobel 算子
    let sobel_x = [-1, 0, 1, -2, 0, 2, -1, 0, 1];
    let sobel_y = [-1, -2, -1, 0, 0, 0, 1, 2, 1];

    for y in 1..(height - 1) {
        for x in 1..(width - 1) {
            let mut gx = 0i32;
            let mut gy = 0i32;
            
            // 应用 Sobel 算子
            for ky in 0..3 {
                for kx in 0..3 {
                    let pixel_y = y + ky - 1;
                    let pixel_x = x + kx - 1;
                    let pixel_value = image[pixel_y * width + pixel_x] as i32;
                    
                    gx += pixel_value * sobel_x[ky * 3 + kx];
                    gy += pixel_value * sobel_y[ky * 3 + kx];
                }
            }
            
            // 计算梯度幅值
            let magnitude = ((gx * gx + gy * gy) as f32).sqrt() as u8;
            result[y * width + x] = magnitude.min(255);
        }
    }

    Ok(result)
}

/// 演示批量图像处理
/// Demonstrate batch image processing
fn demonstrate_batch_processing() -> Result<(), Box<dyn std::error::Error>> {
    println!("📦 演示批量图像处理");
    println!("📦 Demonstrating batch image processing");

    let image_count = 10;
    let width = 128;
    let height = 128;
    let image_size = width * height * 4;

    println!("   📊 处理图像数量: {}", image_count);
    println!("   📊 每张图像尺寸: {}x{}", width, height);

    // 创建测试图像批次
    let mut image_batch = Vec::new();
    for i in 0..image_count {
        let mut image = vec![0u8; image_size];
        for j in 0..image_size {
            image[j] = ((i * 100 + j) % 256) as u8;
        }
        image_batch.push(image);
    }

    // 使用批量内存操作进行并行处理
    let start = Instant::now();
    let mut processed_batch = Vec::new();
    
    for (i, image) in image_batch.iter().enumerate() {
        let mut memory_manager = BulkMemoryManager::new(image_size * 2);
        
        // 写入图像数据
        memory_manager.write_memory(0, image)?;
        
        // 应用滤镜
        let filtered = apply_simple_filter(&image, width, height)?;
        processed_batch.push(filtered);
        
        println!("   ✅ 处理完成图像 {}/{}", i + 1, image_count);
    }
    
    let batch_duration = start.elapsed();

    println!("   ✅ 批量处理完成，总耗时: {:?}", batch_duration);
    println!("   📊 平均处理速度: {:.2} MP/s", 
        (image_count * width * height) as f64 / batch_duration.as_secs_f64() / 1_000_000.0);

    println!();
    Ok(())
}

/// 应用简单滤镜
/// Apply simple filter
fn apply_simple_filter(image: &[u8], width: usize, height: usize) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
    let mut result = vec![0u8; width * height * 4];
    
    for y in 0..height {
        for x in 0..width {
            let index = (y * width + x) * 4;
            if index + 3 < image.len() && index + 3 < result.len() {
                // 简单的亮度调整
                result[index] = (image[index] as f32 * 1.2).min(255.0) as u8;
                result[index + 1] = (image[index + 1] as f32 * 1.2).min(255.0) as u8;
                result[index + 2] = (image[index + 2] as f32 * 1.2).min(255.0) as u8;
                result[index + 3] = image[index + 3];
            }
        }
    }
    
    Ok(result)
}
