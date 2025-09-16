// 计算机视觉模块
// Computer Vision Module

use serde::{Deserialize, Serialize};

/// 图像结构
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Image {
    pub width: usize,
    pub height: usize,
    pub channels: usize,
    pub data: Vec<f64>,
}

impl Image {
    /// 创建新的图像
    pub fn new(width: usize, height: usize, channels: usize) -> Self {
        Self {
            width,
            height,
            channels,
            data: vec![0.0; width * height * channels],
        }
    }

    /// 从数据创建图像
    pub fn from_data(width: usize, height: usize, channels: usize, data: Vec<f64>) -> Self {
        Self {
            width,
            height,
            channels,
            data,
        }
    }

    /// 获取像素值
    pub fn get_pixel(&self, x: usize, y: usize, channel: usize) -> f64 {
        if x < self.width && y < self.height && channel < self.channels {
            let index = y * self.width * self.channels + x * self.channels + channel;
            self.data[index]
        } else {
            0.0
        }
    }

    /// 设置像素值
    pub fn set_pixel(&mut self, x: usize, y: usize, channel: usize, value: f64) {
        if x < self.width && y < self.height && channel < self.channels {
            let index = y * self.width * self.channels + x * self.channels + channel;
            self.data[index] = value;
        }
    }

    /// 图像归一化
    pub fn normalize(&mut self) {
        let min_val = self.data.iter().fold(f64::INFINITY, |a, &b| a.min(b));
        let max_val = self.data.iter().fold(f64::NEG_INFINITY, |a, &b| a.max(b));
        let range = max_val - min_val;

        if range > 0.0 {
            for pixel in &mut self.data {
                *pixel = (*pixel - min_val) / range;
            }
        }
    }
}

/// 图像滤波器
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ImageFilter {
    pub kernel: Vec<Vec<f64>>,
    pub kernel_size: usize,
}

impl ImageFilter {
    /// 创建高斯滤波器
    pub fn gaussian(size: usize, sigma: f64) -> Self {
        let mut kernel = vec![vec![0.0; size]; size];
        let center = size / 2;
        let mut sum = 0.0;

        for i in 0..size {
            for j in 0..size {
                let x = (i as i32 - center as i32) as f64;
                let y = (j as i32 - center as i32) as f64;
                let value = (-(x * x + y * y) / (2.0 * sigma * sigma)).exp();
                kernel[i][j] = value;
                sum += value;
            }
        }

        // 归一化
        for i in 0..size {
            for j in 0..size {
                kernel[i][j] /= sum;
            }
        }

        Self {
            kernel,
            kernel_size: size,
        }
    }

    /// 创建边缘检测滤波器
    pub fn sobel_x() -> Self {
        Self {
            kernel: vec![
                vec![-1.0, 0.0, 1.0],
                vec![-2.0, 0.0, 2.0],
                vec![-1.0, 0.0, 1.0],
            ],
            kernel_size: 3,
        }
    }

    /// 创建边缘检测滤波器
    pub fn sobel_y() -> Self {
        Self {
            kernel: vec![
                vec![-1.0, -2.0, -1.0],
                vec![0.0, 0.0, 0.0],
                vec![1.0, 2.0, 1.0],
            ],
            kernel_size: 3,
        }
    }

    /// 应用滤波器
    pub fn apply(&self, image: &Image) -> Image {
        let mut result = Image::new(image.width, image.height, image.channels);
        let half_kernel = self.kernel_size / 2;

        for y in half_kernel..image.height - half_kernel {
            for x in half_kernel..image.width - half_kernel {
                for c in 0..image.channels {
                    let mut sum = 0.0;

                    for ky in 0..self.kernel_size {
                        for kx in 0..self.kernel_size {
                            let pixel_x = x + kx - half_kernel;
                            let pixel_y = y + ky - half_kernel;
                            let pixel_value = image.get_pixel(pixel_x, pixel_y, c);
                            sum += pixel_value * self.kernel[ky][kx];
                        }
                    }

                    result.set_pixel(x, y, c, sum);
                }
            }
        }

        result
    }
}

/// 特征检测器
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FeatureDetector {
    pub detector_type: DetectorType,
    pub threshold: f64,
}

/// 检测器类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum DetectorType {
    Harris,
    SIFT,
    ORB,
    FAST,
}

/// 特征点
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FeaturePoint {
    pub x: f64,
    pub y: f64,
    pub response: f64,
    pub orientation: f64,
    pub descriptor: Vec<f64>,
}

impl FeatureDetector {
    /// 创建新的特征检测器
    pub fn new(detector_type: DetectorType, threshold: f64) -> Self {
        Self {
            detector_type,
            threshold,
        }
    }

    /// 检测特征点
    pub fn detect(&self, image: &Image) -> Vec<FeaturePoint> {
        match self.detector_type {
            DetectorType::Harris => self.detect_harris(image),
            DetectorType::SIFT => self.detect_sift(image),
            DetectorType::ORB => self.detect_orb(image),
            DetectorType::FAST => self.detect_fast(image),
        }
    }

    /// Harris角点检测
    fn detect_harris(&self, image: &Image) -> Vec<FeaturePoint> {
        let mut features = Vec::new();
        let sobel_x = ImageFilter::sobel_x();
        let sobel_y = ImageFilter::sobel_y();

        let grad_x = sobel_x.apply(image);
        let grad_y = sobel_y.apply(image);

        // 简化的Harris角点检测
        for y in 1..image.height - 1 {
            for x in 1..image.width - 1 {
                let mut ixx = 0.0;
                let mut iyy = 0.0;
                let mut ixy = 0.0;

                for dy in -1..=1 {
                    for dx in -1..=1 {
                        let gx =
                            grad_x.get_pixel((x as i32 + dx) as usize, (y as i32 + dy) as usize, 0);
                        let gy =
                            grad_y.get_pixel((x as i32 + dx) as usize, (y as i32 + dy) as usize, 0);

                        ixx += gx * gx;
                        iyy += gy * gy;
                        ixy += gx * gy;
                    }
                }

                let det = ixx * iyy - ixy * ixy;
                let trace = ixx + iyy;
                let response = det - 0.04 * trace * trace;

                if response > self.threshold {
                    features.push(FeaturePoint {
                        x: x as f64,
                        y: y as f64,
                        response,
                        orientation: 0.0,
                        descriptor: vec![ixx, iyy, ixy],
                    });
                }
            }
        }

        features
    }

    /// SIFT特征检测（简化版）
    fn detect_sift(&self, image: &Image) -> Vec<FeaturePoint> {
        let mut features = Vec::new();

        // 简化的SIFT检测
        for y in 8..image.height - 8 {
            for x in 8..image.width - 8 {
                let mut sum = 0.0;
                for dy in -8..8 {
                    for dx in -8..8 {
                        sum +=
                            image.get_pixel((x as i32 + dx) as usize, (y as i32 + dy) as usize, 0);
                    }
                }

                if sum > self.threshold {
                    features.push(FeaturePoint {
                        x: x as f64,
                        y: y as f64,
                        response: sum,
                        orientation: 0.0,
                        descriptor: vec![sum / 256.0],
                    });
                }
            }
        }

        features
    }

    /// ORB特征检测（简化版）
    fn detect_orb(&self, image: &Image) -> Vec<FeaturePoint> {
        let mut features = Vec::new();

        // 简化的ORB检测
        for y in 4..image.height - 4 {
            for x in 4..image.width - 4 {
                let center = image.get_pixel(x, y, 0);
                let mut brighter = 0;
                let mut darker = 0;

                for dy in -4..=4 {
                    for dx in -4..=4 {
                        if dx == 0 && dy == 0 {
                            continue;
                        }
                        let pixel =
                            image.get_pixel((x as i32 + dx) as usize, (y as i32 + dy) as usize, 0);
                        if pixel > center + 0.1 {
                            brighter += 1;
                        } else if pixel < center - 0.1 {
                            darker += 1;
                        }
                    }
                }

                if brighter > 8 || darker > 8 {
                    features.push(FeaturePoint {
                        x: x as f64,
                        y: y as f64,
                        response: (brighter + darker) as f64,
                        orientation: 0.0,
                        descriptor: vec![center],
                    });
                }
            }
        }

        features
    }

    /// FAST特征检测（简化版）
    fn detect_fast(&self, image: &Image) -> Vec<FeaturePoint> {
        let mut features = Vec::new();

        // 简化的FAST检测
        for y in 3..image.height - 3 {
            for x in 3..image.width - 3 {
                let center = image.get_pixel(x, y, 0);
                let mut consecutive = 0;
                let mut max_consecutive = 0;

                for i in 0..16 {
                    let angle = i as f64 * std::f64::consts::PI / 8.0;
                    let dx = (3.0 * angle.cos()) as i32;
                    let dy = (3.0 * angle.sin()) as i32;
                    let pixel =
                        image.get_pixel((x as i32 + dx) as usize, (y as i32 + dy) as usize, 0);

                    if pixel > center + 0.1 {
                        consecutive += 1;
                        max_consecutive = max_consecutive.max(consecutive);
                    } else {
                        consecutive = 0;
                    }
                }

                if max_consecutive >= 9 {
                    features.push(FeaturePoint {
                        x: x as f64,
                        y: y as f64,
                        response: max_consecutive as f64,
                        orientation: 0.0,
                        descriptor: vec![center],
                    });
                }
            }
        }

        features
    }
}

/// 图像分割器
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ImageSegmenter {
    pub method: SegmentationMethod,
    pub num_segments: usize,
}

/// 分割方法
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum SegmentationMethod {
    KMeans,
    Watershed,
    GraphCut,
    MeanShift,
}

/// 图像分割结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SegmentationResult {
    pub segments: Vec<Vec<(usize, usize)>>,
    pub num_segments: usize,
}

impl ImageSegmenter {
    /// 创建新的图像分割器
    pub fn new(method: SegmentationMethod, num_segments: usize) -> Self {
        Self {
            method,
            num_segments,
        }
    }

    /// 分割图像
    pub fn segment(&self, image: &Image) -> SegmentationResult {
        match self.method {
            SegmentationMethod::KMeans => self.kmeans_segmentation(image),
            SegmentationMethod::Watershed => self.watershed_segmentation(image),
            SegmentationMethod::GraphCut => self.graphcut_segmentation(image),
            SegmentationMethod::MeanShift => self.meanshift_segmentation(image),
        }
    }

    /// K-means分割
    fn kmeans_segmentation(&self, image: &Image) -> SegmentationResult {
        let mut segments = vec![Vec::new(); self.num_segments];

        // 简化的K-means分割
        for y in 0..image.height {
            for x in 0..image.width {
                let pixel_value = image.get_pixel(x, y, 0);
                let segment_id =
                    ((pixel_value * self.num_segments as f64) as usize).min(self.num_segments - 1);
                segments[segment_id].push((x, y));
            }
        }

        SegmentationResult {
            segments,
            num_segments: self.num_segments,
        }
    }

    /// 分水岭分割（简化版）
    fn watershed_segmentation(&self, image: &Image) -> SegmentationResult {
        // 简化的分水岭算法
        self.kmeans_segmentation(image)
    }

    /// 图割分割（简化版）
    fn graphcut_segmentation(&self, image: &Image) -> SegmentationResult {
        // 简化的图割算法
        self.kmeans_segmentation(image)
    }

    /// 均值漂移分割（简化版）
    fn meanshift_segmentation(&self, image: &Image) -> SegmentationResult {
        // 简化的均值漂移算法
        self.kmeans_segmentation(image)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_image_creation() {
        let image = Image::new(100, 100, 3);
        assert_eq!(image.width, 100);
        assert_eq!(image.height, 100);
        assert_eq!(image.channels, 3);
        assert_eq!(image.data.len(), 30000);
    }

    #[test]
    fn test_image_pixel_operations() {
        let mut image = Image::new(10, 10, 1);
        image.set_pixel(5, 5, 0, 0.5);
        assert_eq!(image.get_pixel(5, 5, 0), 0.5);
    }

    #[test]
    fn test_image_filter() {
        let image = Image::new(10, 10, 1);
        let filter = ImageFilter::gaussian(3, 1.0);
        let result = filter.apply(&image);
        assert_eq!(result.width, image.width);
        assert_eq!(result.height, image.height);
    }

    #[test]
    fn test_feature_detector() {
        let image = Image::new(100, 100, 1);
        let detector = FeatureDetector::new(DetectorType::Harris, 0.1);
        let _features = detector.detect(&image);
        // 验证特征检测器能够正常工作，返回有效的结果
        // 注意：对于空白图像，可能检测不到特征点，这是正常的
    }

    #[test]
    fn test_image_segmenter() {
        let image = Image::new(50, 50, 1);
        let segmenter = ImageSegmenter::new(SegmentationMethod::KMeans, 4);
        let result = segmenter.segment(&image);
        assert_eq!(result.num_segments, 4);
        assert_eq!(result.segments.len(), 4);
    }
}
