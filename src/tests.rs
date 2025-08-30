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

#[test]
fn test_add_base_coercion() {
    // Test addition with different bases - should coerce to larger base
    let epsilon = 1e-10;

    // Test case 1: base 2 vs base 3 (3 > 2, so result should have base 3)
    let val_base2 = IdleFloat::new(2.0, 3.0); // 2^3 = 8
    let val_base3 = IdleFloat::new(3.0, 2.0); // 3^2 = 9

    let result = val_base2 + val_base3;

    // Result should have base 3 (the larger base)
    assert_eq!(result.base, 3.0, "Result should have the larger base (3.0)");

    // Expected: 8 + 9 = 17, which should be 3^ln_3(17)
    let expected_value = 8.0 + 9.0;
    let result_value = result.base.powf(result.exponent);

    assert!(
        (result_value - expected_value).abs() < epsilon,
        "Addition with base coercion: result {:.10} should be close to \
         expected {:.10}",
        result_value,
        expected_value
    );

    // Test case 2: base 10 vs base e (10 > e, so result should have base 10)
    let val_base_e = IdleFloat::new(std::f64::consts::E, 2.0); // e^2 ≈ 7.389
    let val_base_10 = IdleFloat::new(10.0, 1.0); // 10^1 = 10

    let result2 = val_base_e + val_base_10;

    // Result should have base 10 (the larger base)
    assert_eq!(
        result2.base, 10.0,
        "Result should have the larger base (10.0)"
    );

    // Expected: e^2 + 10 ≈ 7.389 + 10 = 17.389
    let expected_value2 = std::f64::consts::E.powf(2.0) + 10.0;
    let result_value2 = result2.base.powf(result2.exponent);

    assert!(
        (result_value2 - expected_value2).abs() < epsilon,
        "Addition with base coercion: result {:.10} should be close to \
         expected {:.10}",
        result_value2,
        expected_value2
    );

    // Test case 3: Verify commutativity with base coercion
    let result_commutative = val_base_10 + val_base_e;

    assert_eq!(
        result_commutative.base, 10.0,
        "Commutative result should also have base 10.0"
    );
    assert!(
        (result_commutative.exponent - result2.exponent).abs() < epsilon,
        "Commutative addition should give same exponent"
    );

    // Test case 4: Different bases with larger exponents
    let large_base2 = IdleFloat::new(2.0, 10.0); // 2^10 = 1024
    let large_base5 = IdleFloat::new(5.0, 5.0); // 5^5 = 3125

    let result3 = large_base2 + large_base5;

    // Result should have base 5 (the larger base)
    assert_eq!(
        result3.base, 5.0,
        "Result should have the larger base (5.0)"
    );

    // Expected: 1024 + 3125 = 4149
    let expected_value3 = 1024.0 + 3125.0;
    let result_value3 = result3.base.powf(result3.exponent);

    assert!(
        (result_value3 - expected_value3).abs() < epsilon,
        "Addition with base coercion for large numbers: result {:.10} should \
         be close to expected {:.10}",
        result_value3,
        expected_value3
    );
}

#[test]
fn test_sub_base_coercion() {
    // Test subtraction with different bases - should coerce to larger base
    let epsilon = 1e-10;

    // Test case 1: base 3 vs base 2 (3 > 2, so result should have base 3)
    let val_base3 = IdleFloat::new(3.0, 2.0); // 3^2 = 9
    let val_base2 = IdleFloat::new(2.0, 3.0); // 2^3 = 8

    let result = val_base3 - val_base2;

    // Result should have base 3 (the larger base)
    assert_eq!(result.base, 3.0, "Result should have the larger base (3.0)");

    // Expected: 9 - 8 = 1, which should be 3^0 = 1
    let expected_value = 9.0 - 8.0;
    let result_value = result.base.powf(result.exponent);

    assert!(
        (result_value - expected_value).abs() < epsilon,
        "Subtraction with base coercion: result {:.10} should be close to \
         expected {:.10}",
        result_value,
        expected_value
    );

    // Test case 2: base 10 vs base e (10 > e, so result should have base 10)
    let val_base_10 = IdleFloat::new(10.0, 1.5); // 10^1.5 ≈ 31.623
    let val_base_e = IdleFloat::new(std::f64::consts::E, 2.0); // e^2 ≈ 7.389

    let result2 = val_base_10 - val_base_e;

    // Result should have base 10 (the larger base)
    assert_eq!(
        result2.base, 10.0,
        "Result should have the larger base (10.0)"
    );

    // Expected: 10^1.5 - e^2 ≈ 31.623 - 7.389 = 24.234
    let expected_value2 = 10.0_f64.powf(1.5) - std::f64::consts::E.powf(2.0);
    let result_value2 = result2.base.powf(result2.exponent);

    assert!(
        (result_value2 - expected_value2).abs() < epsilon,
        "Subtraction with base coercion: result {:.10} should be close to \
         expected {:.10}",
        result_value2,
        expected_value2
    );

    // Test case 3: Different bases with larger exponents
    let large_base5 = IdleFloat::new(5.0, 5.0); // 5^5 = 3125
    let large_base2 = IdleFloat::new(2.0, 10.0); // 2^10 = 1024

    let result3 = large_base5 - large_base2;

    // Result should have base 5 (the larger base)
    assert_eq!(
        result3.base, 5.0,
        "Result should have the larger base (5.0)"
    );

    // Expected: 3125 - 1024 = 2101
    let expected_value3 = 3125.0 - 1024.0;
    let result_value3 = result3.base.powf(result3.exponent);

    assert!(
        (result_value3 - expected_value3).abs() < epsilon,
        "Subtraction with base coercion for large numbers: result {:.10} \
         should be close to expected {:.10}",
        result_value3,
        expected_value3
    );

    // Test case 4: Subtraction that would result in negative (should be NaN)
    let small_base5 = IdleFloat::new(5.0, 1.0); // 5^1 = 5
    let large_base2 = IdleFloat::new(2.0, 10.0); // 2^10 = 1024

    let result4 = small_base5 - large_base2;

    // Since 5 - 1024 < 0, and IdleFloat cannot represent negative numbers, result should be NaN
    assert!(
        result4.is_nan(),
        "Subtraction resulting in negative should be NaN"
    );
}

#[test]
fn test_mul_positive_values() {
    // Test multiplication with positive values
    // Using e as base for consistency (default base)
    let base = std::f64::consts::E;
    let epsilon = 1e-10;

    // Create values: e^2 ≈ 7.389 and e^1.5 ≈ 4.482
    let val1 = IdleFloat::new(base, 2.0); // e^2
    let val2 = IdleFloat::new(base, 1.5); // e^1.5

    // Expected result: e^2 * e^1.5 = e^(2+1.5) = e^3.5 ≈ 30.128
    let result = val1 * val2;

    // Check that the result has correct base and exponent
    assert_eq!(result.base, base, "Result should maintain base");
    assert!(
        (result.exponent - 3.5).abs() < epsilon,
        "Multiplication exponent should be sum: got {:.10}, expected 3.5",
        result.exponent
    );

    // Check the actual mathematical value
    let result_value = result.base.powf(result.exponent);
    let expected_value = base.powf(2.0) * base.powf(1.5);

    assert!(
        (result_value - expected_value).abs() < epsilon,
        "Multiplication result {:.10} should be close to expected {:.10}",
        result_value,
        expected_value
    );

    assert!(!result.is_zero(), "Result should not be zero");
    assert!(!result.is_nan(), "Result should not be NaN");
}

#[test]
fn test_mul_with_zero() {
    // Test multiplication with zero
    let base = std::f64::consts::E;
    let zero: IdleFloat<f64> = IdleFloat::zero();
    let number = IdleFloat::new(base, 5.0); // e^5

    // Zero * number = zero
    let result1 = zero * number;
    assert!(result1.is_zero(), "Zero * number should be zero");

    // Number * zero = zero
    let result2 = number * zero;
    assert!(result2.is_zero(), "Number * zero should be zero");

    // Zero * zero = zero
    let result3 = zero * zero;
    assert!(result3.is_zero(), "Zero * zero should be zero");
}

#[test]
fn test_mul_with_one() {
    // Test multiplication with one
    let base = std::f64::consts::E;
    let one: IdleFloat<f64> = IdleFloat::one();
    let number = IdleFloat::new(base, 3.0); // e^3

    // One * number = number
    let result1 = one * number;
    assert_eq!(result1, number, "One * number should equal number");

    // Number * one = number
    let result2 = number * one;
    assert_eq!(result2, number, "Number * one should equal number");

    // One * one = one
    let result3 = one * one;
    assert_eq!(result3, one, "One * one should equal one");
}

#[test]
fn test_mul_negative_exponents() {
    // Test multiplication with negative exponents (fractional values)
    let base = std::f64::consts::E;
    let epsilon = 1e-10;

    // e^(-2) ≈ 0.135 and e^(-1) ≈ 0.368
    let val1 = IdleFloat::new(base, -2.0); // e^(-2)
    let val2 = IdleFloat::new(base, -1.0); // e^(-1)

    // Expected: e^(-2) * e^(-1) = e^(-3) ≈ 0.0498
    let result = val1 * val2;

    assert_eq!(result.base, base, "Result should maintain base");
    assert!(
        (result.exponent - (-3.0)).abs() < epsilon,
        "Negative exponent multiplication: got {:.10}, expected -3.0",
        result.exponent
    );

    let result_value = result.base.powf(result.exponent);
    let expected_value = base.powf(-2.0) * base.powf(-1.0);

    assert!(
        (result_value - expected_value).abs() < epsilon,
        "Multiplication with negative exponents: result {:.10} should be \
         close to expected {:.10}",
        result_value,
        expected_value
    );
}

#[test]
fn test_mul_large_exponents() {
    // Test multiplication with large exponents
    let base = std::f64::consts::E;
    let epsilon = 1e-10;

    let big1 = IdleFloat::new(base, 100.0); // e^100
    let big2 = IdleFloat::new(base, 50.0); // e^50

    // Expected: e^100 * e^50 = e^150
    let result = big1 * big2;

    assert_eq!(result.base, base, "Result should maintain base");
    assert!(
        (result.exponent - 150.0).abs() < epsilon,
        "Large exponent multiplication: got {:.10}, expected 150.0",
        result.exponent
    );

    assert!(!result.is_zero(), "Result should not be zero");
    assert!(!result.is_nan(), "Result should not be NaN");
}

#[test]
fn test_mul_commutativity() {
    // Test that multiplication is commutative: a * b = b * a
    let base = std::f64::consts::E;
    let epsilon = 1e-10;

    let val_a = IdleFloat::new(base, 2.5);
    let val_b = IdleFloat::new(base, 1.8);

    let result1 = val_a * val_b;
    let result2 = val_b * val_a;

    assert_eq!(result1.base, result2.base, "Bases should be equal");
    assert!(
        (result1.exponent - result2.exponent).abs() < epsilon,
        "Multiplication should be commutative"
    );
}

#[test]
fn test_mul_with_nan() {
    // Test multiplication with NaN
    let base = std::f64::consts::E;
    let nan: IdleFloat<f64> = IdleFloat::nan();
    let number = IdleFloat::new(base, 2.0);

    // NaN * number = NaN
    let result1 = nan * number;
    assert!(result1.is_nan(), "NaN * number should be NaN");

    // Number * NaN = NaN
    let result2 = number * nan;
    assert!(result2.is_nan(), "Number * NaN should be NaN");

    // NaN * NaN = NaN
    let result3 = nan * nan;
    assert!(result3.is_nan(), "NaN * NaN should be NaN");
}

#[test]
fn test_div_positive_values() {
    // Test division with positive values
    // Using e as base for consistency (default base)
    let base = std::f64::consts::E;
    let epsilon = 1e-10;

    // Create values: e^6 ≈ 403.43 and e^2 ≈ 7.389
    let val1 = IdleFloat::new(base, 6.0); // e^6
    let val2 = IdleFloat::new(base, 2.0); // e^2

    // Expected result: e^6 / e^2 = e^(6-2) = e^4 ≈ 54.598
    let result = val1 / val2;

    // Check that the result has correct base and exponent
    assert_eq!(result.base, base, "Result should maintain base");
    assert!(
        (result.exponent - 4.0).abs() < epsilon,
        "Division exponent should be difference: got {:.10}, expected 4.0",
        result.exponent
    );

    // Check the actual mathematical value
    let result_value = result.base.powf(result.exponent);
    let expected_value = base.powf(6.0) / base.powf(2.0);

    assert!(
        (result_value - expected_value).abs() < epsilon,
        "Division result {:.10} should be close to expected {:.10}",
        result_value,
        expected_value
    );

    assert!(!result.is_zero(), "Result should not be zero");
    assert!(!result.is_nan(), "Result should not be NaN");
}

#[test]
fn test_div_by_zero() {
    // Test division by zero (should be NaN)
    let base = std::f64::consts::E;
    let zero: IdleFloat<f64> = IdleFloat::zero();
    let number = IdleFloat::new(base, 5.0); // e^5

    // Number / zero = NaN
    let result = number / zero;
    assert!(result.is_nan(), "Division by zero should be NaN");
}

#[test]
fn test_div_zero_by_number() {
    // Test zero divided by number (should be zero)
    let base = std::f64::consts::E;
    let zero: IdleFloat<f64> = IdleFloat::zero();
    let number = IdleFloat::new(base, 3.0); // e^3

    // Zero / number = zero
    let result = zero / number;
    assert!(result.is_zero(), "Zero divided by number should be zero");
}

#[test]
fn test_div_by_one() {
    // Test division by one (should return original value)
    let base = std::f64::consts::E;
    let one: IdleFloat<f64> = IdleFloat::one();
    let number = IdleFloat::new(base, 4.0); // e^4

    // Number / one = number
    let result = number / one;
    assert_eq!(result, number, "Number divided by one should equal number");
}

#[test]
fn test_div_negative_exponents() {
    // Test division with negative exponents
    let base = std::f64::consts::E;
    let epsilon = 1e-10;

    // e^(-1) ≈ 0.368 and e^(-3) ≈ 0.0498
    let val1 = IdleFloat::new(base, -1.0); // e^(-1)
    let val2 = IdleFloat::new(base, -3.0); // e^(-3)

    // Expected: e^(-1) / e^(-3) = e^(-1-(-3)) = e^2 ≈ 7.389
    let result = val1 / val2;

    assert_eq!(result.base, base, "Result should maintain base");
    assert!(
        (result.exponent - 2.0).abs() < epsilon,
        "Negative exponent division: got {:.10}, expected 2.0",
        result.exponent
    );

    let result_value = result.base.powf(result.exponent);
    let expected_value = base.powf(-1.0) / base.powf(-3.0);

    assert!(
        (result_value - expected_value).abs() < epsilon,
        "Division with negative exponents: result {:.10} should be close to \
         expected {:.10}",
        result_value,
        expected_value
    );
}

#[test]
fn test_div_large_exponents() {
    // Test division with large exponents
    let base = std::f64::consts::E;
    let epsilon = 1e-10;

    let big1 = IdleFloat::new(base, 200.0); // e^200
    let big2 = IdleFloat::new(base, 150.0); // e^150

    // Expected: e^200 / e^150 = e^50
    let result = big1 / big2;

    assert_eq!(result.base, base, "Result should maintain base");
    assert!(
        (result.exponent - 50.0).abs() < epsilon,
        "Large exponent division: got {:.10}, expected 50.0",
        result.exponent
    );

    assert!(!result.is_zero(), "Result should not be zero");
    assert!(!result.is_nan(), "Result should not be NaN");
}

#[test]
fn test_div_same_values() {
    // Test division of identical values: x / x = 1
    let base = std::f64::consts::E;
    let epsilon = 1e-10;

    let value = IdleFloat::new(base, 5.5); // e^5.5

    let result = value / value;

    // Result should be one (exponent = 0)
    assert_eq!(result.base, base, "Result should maintain base");
    assert!(
        result.exponent.abs() < epsilon,
        "Same value divided by itself should have exponent 0 (i.e., equal 1)"
    );

    // Should also pass the is_one() test
    assert!(result.is_one(), "x / x should equal one");
}

#[test]
fn test_div_resulting_in_fraction() {
    // Test division that results in a fraction (negative exponent)
    let base = std::f64::consts::E;
    let epsilon = 1e-10;

    // e^2 ≈ 7.389 and e^5 ≈ 148.41
    let smaller = IdleFloat::new(base, 2.0); // e^2
    let larger = IdleFloat::new(base, 5.0); // e^5

    // Expected: e^2 / e^5 = e^(2-5) = e^(-3) ≈ 0.0498
    let result = smaller / larger;

    assert_eq!(result.base, base, "Result should maintain base");
    assert!(
        (result.exponent - (-3.0)).abs() < epsilon,
        "Division resulting in fraction: got {:.10}, expected -3.0",
        result.exponent
    );

    let result_value = result.base.powf(result.exponent);
    let expected_value = base.powf(2.0) / base.powf(5.0);

    assert!(
        (result_value - expected_value).abs() < epsilon,
        "Division resulting in fraction: result {:.10} should be close to \
         expected {:.10}",
        result_value,
        expected_value
    );

    assert!(!result.is_zero(), "Result should not be zero");
    assert!(!result.is_nan(), "Result should not be NaN");
    assert!(result_value < 1.0, "Result should be less than 1");
}

#[test]
fn test_div_with_nan() {
    // Test division with NaN
    let base = std::f64::consts::E;
    let nan: IdleFloat<f64> = IdleFloat::nan();
    let number = IdleFloat::new(base, 2.0);

    // NaN / number = NaN
    let result1 = nan / number;
    assert!(result1.is_nan(), "NaN / number should be NaN");

    // Number / NaN = NaN
    let result2 = number / nan;
    assert!(result2.is_nan(), "Number / NaN should be NaN");

    // NaN / NaN = NaN
    let result3 = nan / nan;
    assert!(result3.is_nan(), "NaN / NaN should be NaN");
}

#[test]
fn test_mul_base_coercion() {
    // Test multiplication with different bases - should coerce to larger base
    let epsilon = 1e-10;

    // Test case 1: base 2 vs base 3 (3 > 2, so result should have base 3)
    let val_base2 = IdleFloat::new(2.0, 3.0); // 2^3 = 8
    let val_base3 = IdleFloat::new(3.0, 2.0); // 3^2 = 9

    let result = val_base2 * val_base3;

    // Result should have base 3 (the larger base)
    assert_eq!(result.base, 3.0, "Result should have the larger base (3.0)");

    // Expected: 8 * 9 = 72, which should be 3^log_3(72)
    let expected_value = 8.0 * 9.0;
    let result_value = result.base.powf(result.exponent);

    assert!(
        (result_value - expected_value).abs() < epsilon,
        "Multiplication with base coercion: result {:.10} should be close to \
         expected {:.10}",
        result_value,
        expected_value
    );

    // Test case 2: base 10 vs base e (10 > e, so result should have base 10)
    let val_base_e = IdleFloat::new(std::f64::consts::E, 2.0); // e^2 ≈ 7.389
    let val_base_10 = IdleFloat::new(10.0, 1.0); // 10^1 = 10

    let result2 = val_base_e * val_base_10;

    // Result should have base 10 (the larger base)
    assert_eq!(
        result2.base, 10.0,
        "Result should have the larger base (10.0)"
    );

    // Expected: e^2 * 10 ≈ 7.389 * 10 = 73.89
    let expected_value2 = std::f64::consts::E.powf(2.0) * 10.0;
    let result_value2 = result2.base.powf(result2.exponent);

    assert!(
        (result_value2 - expected_value2).abs() < epsilon,
        "Multiplication with base coercion: result {:.10} should be close to \
         expected {:.10}",
        result_value2,
        expected_value2
    );

    // Test case 3: Verify commutativity with base coercion
    let result_commutative = val_base_10 * val_base_e;

    assert_eq!(
        result_commutative.base, 10.0,
        "Commutative result should also have base 10.0"
    );
    assert!(
        (result_commutative.exponent - result2.exponent).abs() < epsilon,
        "Commutative multiplication should give same exponent"
    );

    // Test case 4: Different bases with larger exponents
    let large_base2 = IdleFloat::new(2.0, 10.0); // 2^10 = 1024
    let large_base5 = IdleFloat::new(5.0, 5.0); // 5^5 = 3125

    let result3 = large_base2 * large_base5;

    // Result should have base 5 (the larger base)
    assert_eq!(
        result3.base, 5.0,
        "Result should have the larger base (5.0)"
    );

    // Expected: 1024 * 3125 = 3,200,000
    let expected_value3 = 1024.0 * 3125.0;
    let result_value3 = result3.base.powf(result3.exponent);

    // Use larger epsilon for very large numbers due to floating point precision
    let large_epsilon = 1e-5;
    assert!(
        (result_value3 - expected_value3).abs() < large_epsilon,
        "Multiplication with base coercion for large numbers: result {:.10} \
         should be close to expected {:.10}",
        result_value3,
        expected_value3
    );
}

#[test]
fn test_div_base_coercion() {
    // Test division with different bases - should coerce to larger base
    let epsilon = 1e-10;

    // Test case 1: base 3 vs base 2 (3 > 2, so result should have base 3)
    let val_base3 = IdleFloat::new(3.0, 4.0); // 3^4 = 81
    let val_base2 = IdleFloat::new(2.0, 3.0); // 2^3 = 8

    let result = val_base3 / val_base2;

    // Result should have base 3 (the larger base)
    assert_eq!(result.base, 3.0, "Result should have the larger base (3.0)");

    // Expected: 81 / 8 = 10.125, which should be 3^log_3(10.125)
    let expected_value = 81.0 / 8.0;
    let result_value = result.base.powf(result.exponent);

    assert!(
        (result_value - expected_value).abs() < epsilon,
        "Division with base coercion: result {:.10} should be close to \
         expected {:.10}",
        result_value,
        expected_value
    );

    // Test case 2: base 10 vs base e (10 > e, so result should have base 10)
    let val_base_10 = IdleFloat::new(10.0, 2.0); // 10^2 = 100
    let val_base_e = IdleFloat::new(std::f64::consts::E, 3.0); // e^3 ≈ 20.086

    let result2 = val_base_10 / val_base_e;

    // Result should have base 10 (the larger base)
    assert_eq!(
        result2.base, 10.0,
        "Result should have the larger base (10.0)"
    );

    // Expected: 100 / e^3 ≈ 100 / 20.086 ≈ 4.978
    let expected_value2 = 100.0 / std::f64::consts::E.powf(3.0);
    let result_value2 = result2.base.powf(result2.exponent);

    assert!(
        (result_value2 - expected_value2).abs() < epsilon,
        "Division with base coercion: result {:.10} should be close to \
         expected {:.10}",
        result_value2,
        expected_value2
    );

    // Test case 3: Different bases with larger exponents
    let large_base5 = IdleFloat::new(5.0, 6.0); // 5^6 = 15,625
    let large_base2 = IdleFloat::new(2.0, 10.0); // 2^10 = 1024

    let result3 = large_base5 / large_base2;

    // Result should have base 5 (the larger base)
    assert_eq!(
        result3.base, 5.0,
        "Result should have the larger base (5.0)"
    );

    // Expected: 15,625 / 1024 ≈ 15.259
    let expected_value3 = 15625.0 / 1024.0;
    let result_value3 = result3.base.powf(result3.exponent);

    assert!(
        (result_value3 - expected_value3).abs() < epsilon,
        "Division with base coercion for large numbers: result {:.10} should \
         be close to expected {:.10}",
        result_value3,
        expected_value3
    );

    // Test case 4: Division that results in a fraction with base coercion
    let small_base5 = IdleFloat::new(5.0, 2.0); // 5^2 = 25
    let large_base2 = IdleFloat::new(2.0, 8.0); // 2^8 = 256

    let result4 = small_base5 / large_base2;

    // Result should have base 5 (the larger base)
    assert_eq!(
        result4.base, 5.0,
        "Result should have the larger base (5.0)"
    );

    // Expected: 25 / 256 ≈ 0.0977
    let expected_value4 = 25.0 / 256.0;
    let result_value4 = result4.base.powf(result4.exponent);

    assert!(
        (result_value4 - expected_value4).abs() < epsilon,
        "Division resulting in fraction with base coercion: result {:.10} \
         should be close to expected {:.10}",
        result_value4,
        expected_value4
    );

    // The result should be less than 1 (fractional)
    assert!(result_value4 < 1.0, "Result should be fractional (< 1)");
    assert!(!result4.is_zero(), "Result should not be zero");
    assert!(!result4.is_nan(), "Result should not be NaN");
}

#[test]
fn test_infinity() {
    // Test infinity creation and properties
    let inf: IdleFloat<f64> = IdleFloat::infinity();
    
    // Infinity should have base e and infinite exponent
    assert_eq!(inf.base, std::f64::consts::E, "Infinity should have base e");
    assert!(inf.exponent.is_infinite() && inf.exponent.is_sign_positive(), "Infinity should have positive infinite exponent");
    
    // Classification should be Infinite
    assert_eq!(inf.classify(), std::num::FpCategory::Infinite);
}

#[test]
fn test_min_positive_value() {
    // Test minimum positive value creation
    let min_pos: IdleFloat<f64> = IdleFloat::min_positive_value();
    
    // Should have base slightly greater than 1 and very negative exponent
    let expected_base = 1.0 + f64::MIN_POSITIVE;
    assert!((min_pos.base - expected_base).abs() < 1e-100, "Min positive should have base = 1 + MIN_POSITIVE");
    assert_eq!(min_pos.exponent, -f64::MAX, "Min positive should have most negative finite exponent");
    
    // Classification should be Normal
    assert_eq!(min_pos.classify(), std::num::FpCategory::Normal);
}

#[test]
fn test_max_value() {
    // Test maximum value creation
    let max_val: IdleFloat<f64> = IdleFloat::max_value();
    
    // Should have maximum finite values for both base and exponent
    assert_eq!(max_val.base, f64::MAX, "Max value should have max finite base");
    assert_eq!(max_val.exponent, f64::MAX, "Max value should have max finite exponent");
    
    // Classification should be Normal
    assert_eq!(max_val.classify(), std::num::FpCategory::Normal);
}

#[test]
fn test_classify() {
    // Test classification of various values
    let zero: IdleFloat<f64> = IdleFloat::zero();
    let one: IdleFloat<f64> = IdleFloat::one();
    let normal = IdleFloat::new(2.0, 3.0);
    let nan: IdleFloat<f64> = IdleFloat::nan();
    let inf: IdleFloat<f64> = IdleFloat::infinity();
    
    assert_eq!(zero.classify(), std::num::FpCategory::Zero);
    assert_eq!(one.classify(), std::num::FpCategory::Normal);
    assert_eq!(normal.classify(), std::num::FpCategory::Normal);
    assert_eq!(nan.classify(), std::num::FpCategory::Nan);
    assert_eq!(inf.classify(), std::num::FpCategory::Infinite);
}

#[test]
fn test_recip() {
    // Test reciprocal function
    let epsilon = 1e-10;
    let base = std::f64::consts::E;
    
    // Test reciprocal of a normal value: 1/(e^2) = e^(-2)
    let val = IdleFloat::new(base, 2.0);
    let recip_val = val.recip();
    
    assert_eq!(recip_val.base, base, "Reciprocal should maintain base");
    assert!((recip_val.exponent - (-2.0)).abs() < epsilon, "Reciprocal should negate exponent");
    
    // Test mathematical correctness: val * recip_val = 1
    let product = val * recip_val;
    assert!(product.is_one(), "Value times its reciprocal should equal one");
    
    // Test reciprocal of zero should be infinity
    let zero: IdleFloat<f64> = IdleFloat::zero();
    let recip_zero = zero.recip();
    assert_eq!(recip_zero.classify(), std::num::FpCategory::Infinite, "Reciprocal of zero should be infinity");
    
    // Test reciprocal of NaN should be NaN
    let nan: IdleFloat<f64> = IdleFloat::nan();
    let recip_nan = nan.recip();
    assert!(recip_nan.is_nan(), "Reciprocal of NaN should be NaN");
}

#[test]
fn test_sqrt() {
    // Test square root function
    let epsilon = 1e-10;
    let base = std::f64::consts::E;
    
    // Test sqrt of e^4 = e^2
    let val = IdleFloat::new(base, 4.0);
    let sqrt_val = val.sqrt();
    
    assert_eq!(sqrt_val.base, base, "Square root should maintain base");
    assert!((sqrt_val.exponent - 2.0).abs() < epsilon, "Square root should halve exponent");
    
    // Test mathematical correctness: sqrt_val^2 = val
    let squared = sqrt_val * sqrt_val;
    assert!((squared.exponent - val.exponent).abs() < epsilon, "Square of square root should equal original");
    
    // Test sqrt of zero should be zero
    let zero: IdleFloat<f64> = IdleFloat::zero();
    let sqrt_zero = zero.sqrt();
    assert!(sqrt_zero.is_zero(), "Square root of zero should be zero");
    
    // Test sqrt of NaN should be NaN
    let nan: IdleFloat<f64> = IdleFloat::nan();
    let sqrt_nan = nan.sqrt();
    assert!(sqrt_nan.is_nan(), "Square root of NaN should be NaN");
}

#[test]
fn test_exp() {
    // Test exponential function
    let epsilon = 1e-10;
    let base = std::f64::consts::E;
    
    // Test exp(0) = 1
    let zero: IdleFloat<f64> = IdleFloat::zero();
    let exp_zero = zero.exp();
    assert!(exp_zero.is_one(), "exp(0) should equal 1");
    
    // Test exp of a small value
    let small_val = IdleFloat::new(base, 1.0); // e^1 = e
    let exp_small = small_val.exp(); // e^e
    
    assert_eq!(exp_small.base, base, "exp result should have base e");
    assert!((exp_small.exponent - base).abs() < epsilon, "exp(e) should equal e^e");
    
    // Test exp of NaN should be NaN
    let nan: IdleFloat<f64> = IdleFloat::nan();
    let exp_nan = nan.exp();
    assert!(exp_nan.is_nan(), "exp(NaN) should be NaN");
}

#[test]
fn test_ln() {
    // Test natural logarithm function
    let epsilon = 1e-10;
    let base = std::f64::consts::E;
    
    // Test ln(1) = 0
    let one: IdleFloat<f64> = IdleFloat::one();
    let ln_one = one.ln();
    assert!(ln_one.is_zero(), "ln(1) should equal 0");
    
    // Test ln(e^2) = 2
    let val = IdleFloat::new(base, 2.0);
    let ln_val = val.ln();
    
    assert_eq!(ln_val.base, base, "ln result should have base e");
    assert!((ln_val.exponent - 2.0).abs() < epsilon, "ln(e^2) should equal 2");
    
    // Test ln with different base: ln(2^3) = 3 * ln(2)
    let val_base2 = IdleFloat::new(2.0, 3.0);
    let ln_val_base2 = val_base2.ln();
    let expected_exponent = 3.0 * 2.0_f64.ln();
    
    assert_eq!(ln_val_base2.base, base, "ln result should have base e");
    assert!((ln_val_base2.exponent - expected_exponent).abs() < epsilon, 
            "ln(2^3) should equal 3*ln(2)");
    
    // Test ln(0) should be NaN
    let zero: IdleFloat<f64> = IdleFloat::zero();
    let ln_zero = zero.ln();
    assert!(ln_zero.is_nan(), "ln(0) should be NaN");
    
    // Test ln(NaN) should be NaN
    let nan: IdleFloat<f64> = IdleFloat::nan();
    let ln_nan = nan.ln();
    assert!(ln_nan.is_nan(), "ln(NaN) should be NaN");
}

#[test]
fn test_log() {
    // Test logarithm with IdleFloat base
    let epsilon = 1e-10;
    
    // Let me try a simpler case first: log_2(4) = 2 (since 2^2 = 4)
    let val = IdleFloat::new(2.0, 2.0); // 2^2 = 4
    let base = IdleFloat::new(2.0, 1.0); // 2^1 = 2
    let log_result = val.log(base);
    
    let result_value = log_result.base.powf(log_result.exponent);
    assert!((result_value - 2.0).abs() < epsilon, 
            "log_2(4) should equal 2, got {}", result_value);
    
    // Test log_2(8) = 3 (since 2^3 = 8)
    let val8 = IdleFloat::new(2.0, 3.0); // 2^3 = 8
    let log_result8 = val8.log(base);
    let result_value8 = log_result8.base.powf(log_result8.exponent);
    assert!((result_value8 - 3.0).abs() < epsilon, 
            "log_2(8) should equal 3, got {}", result_value8);
    
    // Test log_10(100) = 2 (since 10^2 = 100)
    let val_100 = IdleFloat::new(10.0, 2.0); // 10^2 = 100
    let base_10 = IdleFloat::new(10.0, 1.0); // 10^1 = 10
    let log_100 = val_100.log(base_10);
    
    let result_value_100 = log_100.base.powf(log_100.exponent);
    assert!((result_value_100 - 2.0).abs() < epsilon, 
            "log_10(100) should equal 2");
}

#[test]
fn test_log_float() {
    // Test logarithm with Float base
    let epsilon = 1e-10;
    
    // Test log_2(8) = 3 using Float base
    let val = IdleFloat::new(2.0, 3.0); // 2^3 = 8
    let log_result = val.log_float(2.0);
    
    // Expected: log_2(8) = 3
    // Result should be e^ln(3) = 3
    let result_value = log_result.base.powf(log_result.exponent);
    assert!((result_value - 3.0).abs() < epsilon, 
            "log_float: log_2(8) should equal 3, got {}", result_value);
    
    // Test log_10(1000) = 3 using Float base
    let val_1000 = IdleFloat::new(10.0, 3.0); // 10^3 = 1000
    let log_1000 = val_1000.log_float(10.0);
    
    let result_value_1000 = log_1000.base.powf(log_1000.exponent);
    assert!((result_value_1000 - 3.0).abs() < epsilon, 
            "log_float: log_10(1000) should equal 3");
    
    // Test invalid base cases
    let val = IdleFloat::new(2.0, 2.0);
    
    // Base <= 0 should return NaN
    let log_neg = val.log_float(-2.0);
    assert!(log_neg.is_nan(), "log with negative base should be NaN");
    
    let log_zero_base = val.log_float(0.0);
    assert!(log_zero_base.is_nan(), "log with zero base should be NaN");
    
    // Base = 1 should return NaN
    let log_one_base = val.log_float(1.0);
    assert!(log_one_base.is_nan(), "log with base 1 should be NaN");
    
    // log of zero should be NaN
    let zero: IdleFloat<f64> = IdleFloat::zero();
    let log_of_zero = zero.log_float(10.0);
    assert!(log_of_zero.is_nan(), "log of zero should be NaN");
    
    // log_base(1) should be 0
    let one: IdleFloat<f64> = IdleFloat::one();
    let log_of_one = one.log_float(10.0);
    assert!(log_of_one.is_zero(), "log of one should be zero");
}

#[test]
fn test_max_min() {
    // Test max and min functions
    let val1 = IdleFloat::new(2.0, 3.0); // 2^3 = 8
    let val2 = IdleFloat::new(2.0, 2.0); // 2^2 = 4
    let val3 = IdleFloat::new(3.0, 2.0); // 3^2 = 9
    
    // Test max
    let max_result = val1.max(val2);
    assert_eq!(max_result, val1, "max(8, 4) should be 8");
    
    let max_result2 = val2.max(val3);
    assert_eq!(max_result2, val3, "max(4, 9) should be 9");
    
    // Test min
    let min_result = val1.min(val2);
    assert_eq!(min_result, val2, "min(8, 4) should be 4");
    
    let min_result2 = val2.min(val3);
    assert_eq!(min_result2, val2, "min(4, 9) should be 4");
    
    // Test with equal values
    let val_copy = IdleFloat::new(2.0, 3.0);
    let max_equal = val1.max(val_copy);
    let min_equal = val1.min(val_copy);
    assert_eq!(max_equal, val1, "max of equal values should return first value");
    assert_eq!(min_equal, val1, "min of equal values should return first value");
    
    // Test with NaN
    let nan: IdleFloat<f64> = IdleFloat::nan();
    let max_nan = val1.max(nan);
    let min_nan = val1.min(nan);
    assert!(max_nan.is_nan(), "max with NaN should be NaN");
    assert!(min_nan.is_nan(), "min with NaN should be NaN");
}
