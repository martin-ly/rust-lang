//! 计算几何：凸包（Andrew）与旋转卡壳直径

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Pt {
    pub x: f64,
    pub y: f64,
}

fn cross(o: Pt, a: Pt, b: Pt) -> f64 {
    (a.x - o.x) * (b.y - o.y) - (a.y - o.y) * (b.x - o.x)
}
fn dist2(a: Pt, b: Pt) -> f64 {
    (a.x - b.x).powi(2) + (a.y - b.y).powi(2)
}

/// 凸包：返回按逆时针顺序的顶点（包含共线最外点）
pub fn convex_hull(mut pts: Vec<Pt>) -> Vec<Pt> {
    pts.sort_by(|p, q| {
        p.x.partial_cmp(&q.x)
            .unwrap()
            .then(p.y.partial_cmp(&q.y).unwrap())
    });
    let n = pts.len();
    if n <= 1 {
        return pts;
    }
    let mut lower: Vec<Pt> = Vec::new();
    for p in pts.iter().copied() {
        while lower.len() >= 2 && cross(lower[lower.len() - 2], lower[lower.len() - 1], p) <= 0.0 {
            lower.pop();
        }
        lower.push(p);
    }
    let mut upper: Vec<Pt> = Vec::new();
    for p in pts.into_iter().rev() {
        while upper.len() >= 2 && cross(upper[upper.len() - 2], upper[upper.len() - 1], p) <= 0.0 {
            upper.pop();
        }
        upper.push(p);
    }
    lower.pop();
    upper.pop();
    lower.extend(upper);
    lower
}

/// 旋转卡壳：求凸多边形直径（最大两点间距离平方）
pub fn rotating_calipers_diameter2(hull: &[Pt]) -> f64 {
    let m = hull.len();
    if m <= 1 {
        return 0.0;
    }
    if m == 2 {
        return dist2(hull[0], hull[1]);
    }
    let mut j = 1usize;
    let mut best = 0.0;
    for i in 0..m {
        loop {
            let ni = (i + 1) % m;
            let nj = (j + 1) % m;
            let area = cross(hull[i], hull[ni], hull[nj]).abs();
            let area_next = cross(hull[i], hull[ni], hull[j]).abs();
            if area > area_next {
                j = nj;
            } else {
                break;
            }
        }
        let d = dist2(hull[i], hull[j]);
        if d > best {
            best = d;
        }
    }
    best
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_convex_hull_and_diameter() {
        let pts = vec![
            Pt { x: 0.0, y: 0.0 },
            Pt { x: 1.0, y: 0.0 },
            Pt { x: 1.0, y: 1.0 },
            Pt { x: 0.0, y: 1.0 },
            Pt { x: 0.5, y: 0.5 },
        ];
        let hull = convex_hull(pts);
        assert!(hull.len() == 4);
        let d2 = rotating_calipers_diameter2(&hull);
        assert!((d2 - 2.0).abs() < 1e-9);
    }
}
