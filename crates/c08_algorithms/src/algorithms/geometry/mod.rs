//! # 几何算法模块
//! 
//! 本模块实现了各种几何算法。

use serde::{Serialize, Deserialize};

/// 点结构
#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
pub struct Point {
    pub x: f64,
    pub y: f64,
}

/// 几何算法实现
pub struct GeometryAlgorithms;

impl GeometryAlgorithms {
    /// 计算两点之间的距离
    pub fn distance(p1: Point, p2: Point) -> f64 {
        ((p1.x - p2.x).powi(2) + (p1.y - p2.y).powi(2)).sqrt()
    }

    /// 凸包算法 (Graham Scan)
    pub fn convex_hull(points: &mut [Point]) -> Vec<Point> {
        if points.len() < 3 {
            return points.to_vec();
        }
        
        // 找到最下方的点
        let mut min_y_idx = 0;
        for i in 1..points.len() {
            if points[i].y < points[min_y_idx].y || 
               (points[i].y == points[min_y_idx].y && points[i].x < points[min_y_idx].x) {
                min_y_idx = i;
            }
        }
        points.swap(0, min_y_idx);
        
        let start = points[0];
        
        // 按极角排序
        points[1..].sort_by(|a, b| {
            let cross = Self::cross_product(start, *a, start, *b);
            cross.partial_cmp(&0.0).unwrap_or(std::cmp::Ordering::Equal)
        });
        
        let mut hull = Vec::new();
        for &point in points.iter() {
            while hull.len() > 1 {
                let cross = Self::cross_product(hull[hull.len()-2], hull[hull.len()-1], hull[hull.len()-1], point);
                if cross <= 0.0 {
                    hull.pop();
                } else {
                    break;
                }
            }
            hull.push(point);
        }
        
        hull
    }
    
    /// 计算叉积
    fn cross_product(p1: Point, p2: Point, p3: Point, p4: Point) -> f64 {
        (p2.x - p1.x) * (p4.y - p3.y) - (p2.y - p1.y) * (p4.x - p3.x)
    }
}
