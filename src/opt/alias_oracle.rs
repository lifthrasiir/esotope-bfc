use crate::nodes::*;

pub fn seek_modulus(node: &Node) -> Option<i32> {
    if let Node::SeekMemory { stride, .. } = node {
        let abs_s = stride.abs();
        if abs_s >= 2 {
            Some(abs_s)
        } else {
            None
        }
    } else {
        None
    }
}

pub fn body_modulus(body: &[Node]) -> Option<i32> {
    if stride(body) == Some(0) {
        return None;
    }
    for node in body {
        if let Some(m) = seek_modulus(node) {
            return Some(m);
        }
        if let Node::While { children, .. } | Node::Repeat { children, .. } = node {
            if let Some(m) = body_modulus(children) {
                return Some(m);
            }
        }
    }
    None
}

pub fn cell_disjoint_from_seek(cell_offset: i32, stride_modulus: i32) -> bool {
    stride_modulus >= 2 && cell_offset.rem_euclid(stride_modulus) != 0
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::*;

    #[test]
    fn seek_modulus_stride3() {
        let n = Node::SeekMemory {
            target: 0,
            stride: 3,
            value: 0,
        };
        assert_eq!(seek_modulus(&n), Some(3));
    }

    #[test]
    fn seek_modulus_stride_neg3() {
        let n = Node::SeekMemory {
            target: 0,
            stride: -3,
            value: 0,
        };
        assert_eq!(seek_modulus(&n), Some(3));
    }

    #[test]
    fn seek_modulus_stride1_none() {
        let n = Node::SeekMemory {
            target: 0,
            stride: 1,
            value: 0,
        };
        assert_eq!(seek_modulus(&n), None);
    }

    #[test]
    fn seek_modulus_non_seek() {
        assert_eq!(seek_modulus(&Node::Nop), None);
    }

    #[test]
    fn cell_disjoint_lane1_from_stride3() {
        assert!(cell_disjoint_from_seek(1, 3));
        assert!(cell_disjoint_from_seek(2, 3));
        assert!(!cell_disjoint_from_seek(0, 3));
        assert!(!cell_disjoint_from_seek(3, 3));
        assert!(!cell_disjoint_from_seek(6, 3));
    }

    #[test]
    fn cell_disjoint_negative_offsets() {
        assert!(cell_disjoint_from_seek(-1, 3));
        assert!(!cell_disjoint_from_seek(-3, 3));
    }

    #[test]
    fn cell_disjoint_stride_1_never() {
        assert!(!cell_disjoint_from_seek(0, 1));
        assert!(!cell_disjoint_from_seek(1, 1));
    }

    #[test]
    fn body_modulus_with_seek() {
        let body = vec![
            Node::MovePointer { offset: 1 },
            Node::SeekMemory {
                target: 0,
                stride: 3,
                value: 0,
            },
        ];
        assert_eq!(body_modulus(&body), Some(3));
    }

    #[test]
    fn body_modulus_zero_stride_none() {
        let body = vec![Node::SetMemory {
            offset: 0,
            value: Expr::Int(5),
        }];
        assert_eq!(body_modulus(&body), None);
    }

    #[test]
    fn body_modulus_stride1_none() {
        let body = vec![Node::MovePointer { offset: 1 }];
        assert_eq!(body_modulus(&body), None);
    }
}
