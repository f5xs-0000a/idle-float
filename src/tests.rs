use std::cmp::Ordering;

use num::{
    Float,
    One,
    Zero,
};

use crate::IdleFloat;

#[test]
fn test_equality_same_base() {
    let a = IdleFloat::new(2.0, 3.0);
    let b = IdleFloat::new(2.0, 3.0);
    let c = IdleFloat::new(2.0, 4.0);

    assert_eq!(a, b);
    assert_ne!(a, c);
}

#[test]
fn test_equality_different_base() {
    let a = IdleFloat::new(2.0, 3.0);
    let b = IdleFloat::new(3.0, 3.0);

    // Different bases should not be equal even with same exponent
    assert_ne!(a, b);
}

#[test]
fn test_equality_zero() {
    let zero1: IdleFloat<f64> = IdleFloat::zero();
    let zero2: IdleFloat<f64> = IdleFloat::zero();
    let non_zero = IdleFloat::new(2.0, 1.0);

    assert_eq!(zero1, zero2);
    assert_ne!(zero1, non_zero);
}

#[test]
fn test_equality_one() {
    let one1: IdleFloat<f64> = IdleFloat::one();
    let one2: IdleFloat<f64> = IdleFloat::one();
    let non_one = IdleFloat::new(2.0, 1.0);

    assert_eq!(one1, one2);
    assert_ne!(one1, non_one);
}

#[test]
fn test_equality_nan() {
    let nan1: IdleFloat<f64> = IdleFloat::nan();
    let nan2: IdleFloat<f64> = IdleFloat::nan();
    let normal = IdleFloat::new(2.0, 1.0);

    // NaN should not equal anything, including itself
    assert_ne!(nan1, nan2);
    assert_ne!(nan1, normal);
}

#[test]
fn test_ordering_same_base() {
    let small = IdleFloat::new(2.0, 1.0);
    let large = IdleFloat::new(2.0, 3.0);

    assert!(small < large);
    assert!(large > small);
    assert_eq!(small.partial_cmp(&large), Some(Ordering::Less));
    assert_eq!(large.partial_cmp(&small), Some(Ordering::Greater));
}

#[test]
fn test_ordering_different_base() {
    // 2^3 = 8, 3^2 = 9, so 2^3 < 3^2
    let a = IdleFloat::new(2.0, 3.0);
    let b = IdleFloat::new(3.0, 2.0);

    assert!(a < b);
    assert_eq!(a.partial_cmp(&b), Some(Ordering::Less));
}

#[test]
fn test_ordering_with_zero() {
    let zero: IdleFloat<f64> = IdleFloat::zero();
    let positive = IdleFloat::new(2.0, 1.0);

    assert!(zero < positive);
    assert!(positive > zero);
    assert_eq!(zero.partial_cmp(&positive), Some(Ordering::Less));
}

#[test]
fn test_ordering_with_one() {
    let one: IdleFloat<f64> = IdleFloat::one();
    let small = IdleFloat::new(2.0, -1.0); // 2^(-1) = 0.5 < 1
    let large = IdleFloat::new(2.0, 2.0); // 2^2 = 4 > 1

    assert!(small < one);
    assert!(one < large);
    assert_eq!(small.partial_cmp(&one), Some(Ordering::Less));
    assert_eq!(large.partial_cmp(&one), Some(Ordering::Greater));
}

#[test]
fn test_ordering_infinite_exponents() {
    let pos_inf = IdleFloat::new(2.0, f64::INFINITY);
    let neg_inf = IdleFloat::new(2.0, f64::NEG_INFINITY);
    let finite = IdleFloat::new(2.0, 100.0);

    assert!(neg_inf < finite);
    assert!(finite < pos_inf);
    assert!(neg_inf < pos_inf);
}

#[test]
fn test_ordering_infinite_different_bases() {
    // Both have +inf exponent, larger base should win
    let small_base = IdleFloat::new(2.0, f64::INFINITY);
    let large_base = IdleFloat::new(3.0, f64::INFINITY);

    assert!(small_base < large_base);
    assert_eq!(small_base.partial_cmp(&large_base), Some(Ordering::Less));
}

#[test]
fn test_ordering_with_nan() {
    let nan: IdleFloat<f64> = IdleFloat::nan();
    let normal = IdleFloat::new(2.0, 1.0);

    // NaN should not compare to anything
    assert_eq!(nan.partial_cmp(&normal), None);
    assert_eq!(normal.partial_cmp(&nan), None);
    assert_eq!(nan.partial_cmp(&nan), None);
}

#[test]
fn test_mathematical_consistency() {
    // Test that 2^4 = 16 > 3^2 = 9
    let a = IdleFloat::new(2.0, 4.0);
    let b = IdleFloat::new(3.0, 2.0);

    assert!(a > b);

    // Test that 2^2 = 4 < 3^2 = 9
    let c = IdleFloat::new(2.0, 2.0);
    assert!(c < b);
}
