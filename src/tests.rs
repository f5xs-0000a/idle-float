use std::cmp::Ordering;

use num::{
    Float,
    Num,
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

#[test]
fn test_from_str_radix() {
    // Test parsing zero
    let zero: IdleFloat<f64> = IdleFloat::from_str_radix("0", 10).unwrap();
    assert!(zero.is_zero());

    // Test parsing one
    let one: IdleFloat<f64> = IdleFloat::from_str_radix("1", 10).unwrap();
    assert!(one.is_one());

    // Test parsing positive numbers
    let two: IdleFloat<f64> = IdleFloat::from_str_radix("2", 10).unwrap();
    let expected_two = IdleFloat::new(std::f64::consts::E, 2.0_f64.ln());
    assert_eq!(two, expected_two);

    let ten: IdleFloat<f64> = IdleFloat::from_str_radix("10", 10).unwrap();
    let expected_ten = IdleFloat::new(std::f64::consts::E, 10.0_f64.ln());
    assert_eq!(ten, expected_ten);

    // Test parsing with different radix
    let fifteen_hex: IdleFloat<f64> =
        IdleFloat::from_str_radix("F", 16).unwrap();
    let expected_fifteen = IdleFloat::new(std::f64::consts::E, 15.0_f64.ln());
    assert_eq!(fifteen_hex, expected_fifteen);

    // Test parsing negative numbers (should return NaN)
    let negative: IdleFloat<f64> = IdleFloat::from_str_radix("-5", 10).unwrap();
    assert!(negative.is_nan());

    // Test parsing invalid strings (should return error)
    let invalid = IdleFloat::<f64>::from_str_radix("abc", 10);
    assert!(invalid.is_err());

    // Test parsing fractional numbers
    let half: IdleFloat<f64> = IdleFloat::from_str_radix("0.5", 10).unwrap();
    let expected_half = IdleFloat::new(std::f64::consts::E, 0.5_f64.ln());
    assert_eq!(half, expected_half);
}

#[test]
fn test_is_zero_various_bases() {
    // Standard zero should be recognized regardless of how it's created
    let zero_standard: IdleFloat<f64> = IdleFloat::zero();
    assert!(zero_standard.is_zero());

    // Zero created with different bases should still be zero
    let zero_base2 = IdleFloat::new(2.0, f64::NEG_INFINITY);
    let zero_base3 = IdleFloat::new(3.0, f64::NEG_INFINITY);
    let zero_base10 = IdleFloat::new(10.0, f64::NEG_INFINITY);

    assert!(zero_base2.is_zero());
    assert!(zero_base3.is_zero());
    assert!(zero_base10.is_zero());

    // All zeros should be equal to each other
    assert_eq!(zero_standard, zero_base2);
    assert_eq!(zero_standard, zero_base3);
    assert_eq!(zero_standard, zero_base10);

    // Non-zero values should not be zero
    let non_zero = IdleFloat::new(2.0, 1.0);
    assert!(!non_zero.is_zero());

    // NaN should not be zero
    let nan: IdleFloat<f64> = IdleFloat::nan();
    assert!(!nan.is_zero());

    // Base = 1 (invalid) should not be zero
    let invalid_base = IdleFloat::new(1.0, f64::NEG_INFINITY);
    assert!(!invalid_base.is_zero());

    // Base < 1 should not be zero
    let small_base = IdleFloat::new(0.5, f64::NEG_INFINITY);
    assert!(!small_base.is_zero());
}

#[test]
fn test_is_one_various_bases() {
    // Standard one should be recognized
    let one_standard: IdleFloat<f64> = IdleFloat::one();
    assert!(one_standard.is_one());

    // Only e^0 should be recognized as one
    let one_base_e = IdleFloat::new(std::f64::consts::E, 0.0);
    assert!(one_base_e.is_one());

    // Different bases with exponent 0 should also be recognized as one
    // since mathematically any positive base^0 = 1
    let base2_exp0 = IdleFloat::new(2.0, 0.0); // 2^0 = 1 mathematically
    let base3_exp0 = IdleFloat::new(3.0, 0.0); // 3^0 = 1 mathematically  
    let base10_exp0 = IdleFloat::new(10.0, 0.0); // 10^0 = 1 mathematically

    assert!(base2_exp0.is_one());
    assert!(base3_exp0.is_one());
    assert!(base10_exp0.is_one());

    // Since all of these pass is_one() check, they should be equal due to the
    // special case in PartialEq: if self.is_one() && other.is_one() => true
    assert_eq!(one_standard, base2_exp0);
    assert_eq!(one_standard, base3_exp0);
    assert_eq!(one_standard, base10_exp0);

    // Base e with non-zero exponent should not be one
    let e_exp1 = IdleFloat::new(std::f64::consts::E, 1.0);
    assert!(!e_exp1.is_one());

    // NaN should not be one
    let nan: IdleFloat<f64> = IdleFloat::nan();
    assert!(!nan.is_one());

    // Zero should not be one
    let zero: IdleFloat<f64> = IdleFloat::zero();
    assert!(!zero.is_one());
}
