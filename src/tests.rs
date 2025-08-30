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

#[test]
fn test_sub_positive_values_close_to_one() {
    // Test subtraction with positive values close to 1
    // Using e as base for consistency (default base)
    let base = std::f64::consts::E;

    // Create values close to 1: e^0.1 ≈ 1.105 and e^0.05 ≈ 1.051
    let larger = IdleFloat::new(base, 0.1); // e^0.1
    let smaller = IdleFloat::new(base, 0.05); // e^0.05

    // Expected result: e^0.1 - e^0.05 ≈ 1.105 - 1.051 = 0.054
    // In IdleFloat form: e^ln(0.054) ≈ e^(-2.919)
    let result = larger - smaller;

    // Since we're dealing with floating point arithmetic, we need an epsilon for comparison
    let epsilon = 1e-10;

    // Convert both values to f64 for easier comparison
    // Expected: e^0.1 - e^0.05 = e^0.05 * (e^0.05 - 1) ≈ 1.051 * 0.051 ≈ 0.054
    let expected_value = base.powf(0.1) - base.powf(0.05);
    let expected = IdleFloat::new(base, expected_value.ln());

    // Check that the result is close to expected within epsilon
    // Since we can't directly compare IdleFloat values with epsilon,
    // we'll compare the actual mathematical values they represent
    let result_value = result.base.powf(result.exponent);
    let expected_mathematical_value = expected_value;

    assert!(
        (result_value - expected_mathematical_value).abs() < epsilon,
        "Subtraction result {:.10} should be close to expected {:.10} within \
         epsilon {:.10}",
        result_value,
        expected_mathematical_value,
        epsilon
    );

    // Also test that the result is positive and reasonable
    assert!(!result.is_zero(), "Result should not be zero");
    assert!(!result.is_nan(), "Result should not be NaN");
    assert!(result_value > 0.0, "Result should be positive");
    assert!(
        result_value < 1.0,
        "Result should be less than 1 (since we subtracted from a value > 1)"
    );
}

#[test]
fn test_sub_big_numbers() {
    // Test subtraction with large numbers: e^100 - e^99
    // This tests the LogSumExp implementation for large exponents
    let base = std::f64::consts::E;
    let epsilon = 1e-10;

    let big1 = IdleFloat::new(base, 100.0); // e^100
    let big2 = IdleFloat::new(base, 99.0); // e^99

    // Expected: e^100 - e^99 = e^99 * (e - 1) ≈ e^99 * 1.718
    // Result should be approximately e^(99 + ln(e-1)) = e^(99 + ln(1.718))
    let result = big1 - big2;

    // Mathematical verification: e^100 - e^99 = e^99 * (e - 1)
    let e_minus_1 = base - 1.0;
    let expected_exponent = 99.0 + e_minus_1.ln();
    let expected = IdleFloat::new(base, expected_exponent);

    // Compare the exponents since the numbers are too large for direct comparison
    let result_exp = result.exponent;
    let expected_exp = expected.exponent;

    assert!(
        (result_exp - expected_exp).abs() < epsilon,
        "Big number subtraction result exponent {:.10} should be close to \
         expected {:.10} within epsilon {:.10}",
        result_exp,
        expected_exp,
        epsilon
    );

    assert!(!result.is_zero(), "Result should not be zero");
    assert!(!result.is_nan(), "Result should not be NaN");
}

#[test]
fn test_sub_very_big_minus_very_small() {
    // Test: very big number - very small number ≈ very big number
    // e^1000 - e^(-10) should be approximately e^1000
    let base = std::f64::consts::E;
    let epsilon = 1e-10;

    let very_big = IdleFloat::new(base, 1000.0); // e^1000
    let very_small = IdleFloat::new(base, -10.0); // e^(-10)

    let result = very_big - very_small;

    // When subtracting a very small number from a very large number,
    // the result should be approximately the large number
    // Since e^1000 >> e^(-10), the result should be very close to e^1000

    // The LogSumExp algorithm should handle this gracefully
    // Expected: e^1000 * (1 - e^(-1010)) ≈ e^1000 (since e^(-1010) ≈ 0)
    let expected_exponent = 1000.0 + (1.0 - (-1010.0_f64).exp()).ln();

    // Since e^(-1010) is essentially 0, ln(1 - 0) = ln(1) = 0
    // So expected_exponent should be very close to 1000.0
    assert!(
        (result.exponent - 1000.0).abs() < epsilon,
        "Very big minus very small should be approximately the big number. \
         Got exponent {:.10}, expected ~1000.0",
        result.exponent
    );

    assert!(!result.is_zero(), "Result should not be zero");
    assert!(!result.is_nan(), "Result should not be NaN");
    assert!(result.exponent > 999.0, "Result should still be very large");
}

#[test]
fn test_sub_small_minus_big_gives_nan() {
    // Test: small number - big number should give NaN
    // Since IdleFloat represents only non-negative numbers, negative results are invalid
    // e^(-10) - e^100 should result in NaN
    let base = std::f64::consts::E;

    let small = IdleFloat::new(base, -10.0); // e^(-10) ≈ 0.000045
    let big = IdleFloat::new(base, 100.0); // e^100 (huge number)

    let result = small - big;

    // Since IdleFloat only represents non-negative numbers,
    // any subtraction that would result in a negative value should return NaN
    assert!(
        result.is_nan(),
        "Small minus big should result in NaN since IdleFloat cannot \
         represent negative numbers"
    );

    // Test with another case: e^5 - e^10
    let smaller = IdleFloat::new(base, 5.0); // e^5 ≈ 148
    let bigger = IdleFloat::new(base, 10.0); // e^10 ≈ 22026

    let result2 = smaller - bigger;
    assert!(
        result2.is_nan(),
        "Smaller minus bigger should result in NaN"
    );

    // Test edge case: same base, smaller exponent minus larger exponent
    let a = IdleFloat::new(base, 1.0); // e^1 ≈ 2.718
    let b = IdleFloat::new(base, 2.0); // e^2 ≈ 7.389

    let result3 = a - b;
    assert!(
        result3.is_nan(),
        "Any subtraction resulting in negative should be NaN"
    );
}

#[test]
fn test_add_positive_values_close_to_one() {
    // Test addition with positive values close to 1
    // Using e as base for consistency (default base)
    let base = std::f64::consts::E;

    // Create values close to 1: e^0.1 ≈ 1.105 and e^0.05 ≈ 1.051
    let val1 = IdleFloat::new(base, 0.1); // e^0.1
    let val2 = IdleFloat::new(base, 0.05); // e^0.05

    // Expected result: e^0.1 + e^0.05 ≈ 1.105 + 1.051 = 2.156
    // In IdleFloat form: e^ln(2.156) ≈ e^0.767
    let result = val1 + val2;

    // Since we're dealing with floating point arithmetic, we need an epsilon for comparison
    let epsilon = 1e-10;

    // Convert both values to f64 for easier comparison
    // Expected: e^0.1 + e^0.05 ≈ 1.105 + 1.051 = 2.156
    let expected_value = base.powf(0.1) + base.powf(0.05);
    let expected = IdleFloat::new(base, expected_value.ln());

    // Check that the result is close to expected within epsilon
    // Since we can't directly compare IdleFloat values with epsilon,
    // we'll compare the actual mathematical values they represent
    let result_value = result.base.powf(result.exponent);
    let expected_mathematical_value = expected_value;

    assert!(
        (result_value - expected_mathematical_value).abs() < epsilon,
        "Addition result {:.10} should be close to expected {:.10} within \
         epsilon {:.10}",
        result_value,
        expected_mathematical_value,
        epsilon
    );

    // Also test that the result is positive and reasonable
    assert!(!result.is_zero(), "Result should not be zero");
    assert!(!result.is_nan(), "Result should not be NaN");
    assert!(result_value > 0.0, "Result should be positive");
    assert!(
        result_value > 2.0,
        "Result should be greater than 2 (since we added two values > 1)"
    );
}

#[test]
fn test_add_big_numbers() {
    // Test addition with large numbers: e^100 + e^99
    // This tests the LogSumExp implementation for large exponents
    let base = std::f64::consts::E;
    let epsilon = 1e-10;

    let big1 = IdleFloat::new(base, 100.0); // e^100
    let big2 = IdleFloat::new(base, 99.0); // e^99

    // Expected: e^100 + e^99 = e^99 * (e + 1) ≈ e^99 * 3.718
    // Result should be approximately e^(99 + ln(e+1)) = e^(99 + ln(3.718))
    let result = big1 + big2;

    // Mathematical verification: e^100 + e^99 = e^99 * (e + 1)
    let e_plus_1 = base + 1.0;
    let expected_exponent = 99.0 + e_plus_1.ln();
    let expected = IdleFloat::new(base, expected_exponent);

    // Compare the exponents since the numbers are too large for direct comparison
    let result_exp = result.exponent;
    let expected_exp = expected.exponent;

    assert!(
        (result_exp - expected_exp).abs() < epsilon,
        "Big number addition result exponent {:.10} should be close to \
         expected {:.10} within epsilon {:.10}",
        result_exp,
        expected_exp,
        epsilon
    );

    assert!(!result.is_zero(), "Result should not be zero");
    assert!(!result.is_nan(), "Result should not be NaN");
}

#[test]
fn test_add_very_big_plus_very_small() {
    // Test: very big number + very small number ≈ very big number
    // e^1000 + e^(-10) should be approximately e^1000
    let base = std::f64::consts::E;
    let epsilon = 1e-10;

    let very_big = IdleFloat::new(base, 1000.0); // e^1000
    let very_small = IdleFloat::new(base, -10.0); // e^(-10)

    let result = very_big + very_small;

    // When adding a very small number to a very large number,
    // the result should be approximately the large number
    // Since e^1000 >> e^(-10), the result should be very close to e^1000

    // The LogSumExp algorithm should handle this gracefully
    // Expected: e^1000 * (1 + e^(-1010)) ≈ e^1000 (since e^(-1010) ≈ 0)
    let expected_exponent = 1000.0 + (1.0 + (-1010.0_f64).exp()).ln();

    // Since e^(-1010) is essentially 0, ln(1 + 0) = ln(1) = 0
    // So expected_exponent should be very close to 1000.0
    assert!(
        (result.exponent - 1000.0).abs() < epsilon,
        "Very big plus very small should be approximately the big number. Got \
         exponent {:.10}, expected ~1000.0",
        result.exponent
    );

    assert!(!result.is_zero(), "Result should not be zero");
    assert!(!result.is_nan(), "Result should not be NaN");
    assert!(result.exponent > 999.0, "Result should still be very large");
}

#[test]
fn test_add_zero() {
    // Test addition with zero
    let base = std::f64::consts::E;
    let zero: IdleFloat<f64> = IdleFloat::zero();
    let number = IdleFloat::new(base, 5.0); // e^5

    // Zero + number = number
    let result1 = zero + number;
    assert_eq!(result1, number, "Zero + number should equal number");

    // Number + zero = number
    let result2 = number + zero;
    assert_eq!(result2, number, "Number + zero should equal number");

    // Zero + zero = zero
    let result3 = zero + zero;
    assert_eq!(result3, zero, "Zero + zero should equal zero");
}

#[test]
fn test_add_one() {
    // Test addition with one
    let base = std::f64::consts::E;
    let one: IdleFloat<f64> = IdleFloat::one();
    let number = IdleFloat::new(base, 2.0); // e^2 ≈ 7.389
    let epsilon = 1e-10;

    // One + number should be approximately number + 1
    let result = one + number;

    // Expected: 1 + e^2 ≈ 1 + 7.389 = 8.389
    let expected_value = 1.0 + base.powf(2.0);
    let result_value = result.base.powf(result.exponent);

    assert!(
        (result_value - expected_value).abs() < epsilon,
        "One + number result {:.10} should be close to expected {:.10}",
        result_value,
        expected_value
    );

    assert!(!result.is_zero(), "Result should not be zero");
    assert!(!result.is_nan(), "Result should not be NaN");
}

#[test]
fn test_add_same_values() {
    // Test addition of identical values: x + x = 2x
    let base = std::f64::consts::E;
    let value = IdleFloat::new(base, 3.0); // e^3 ≈ 20.086
    let epsilon = 1e-10;

    let result = value + value;

    // Expected: e^3 + e^3 = 2 * e^3 = e^(ln(2) + 3)
    let expected_value = 2.0 * base.powf(3.0);
    let expected_exponent = 3.0 + 2.0_f64.ln();
    let result_value = result.base.powf(result.exponent);

    assert!(
        (result_value - expected_value).abs() < epsilon,
        "Same value + same value result {:.10} should be close to expected \
         {:.10}",
        result_value,
        expected_value
    );

    // Also check the exponent calculation
    assert!(
        (result.exponent - expected_exponent).abs() < epsilon,
        "Exponent should be close to ln(2) + original_exponent"
    );

    assert!(!result.is_zero(), "Result should not be zero");
    assert!(!result.is_nan(), "Result should not be NaN");
}
