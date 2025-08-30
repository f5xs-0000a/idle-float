#[cfg(test)]
mod tests;

use core::{
    cmp::Ordering::{
        self,
        *,
    },
    ops::{
        Add,
        Div,
        Mul,
        Sub,
    },
};

use num::{
    Float,
    One,
    Zero,
};

/// An implementation of a floating type number designed for incremental games.
///
/// # Representation
///
/// This crate is able to represent numbers from 0 up to `b^f64::max` where
/// `b` is any base you want. However, at the cost of this, while multiplication
/// and exponentiation are easier to represent, addition becomes much more
/// expensive to compute. This can be mitigated if the addition of numbers can
/// be done in a series, as provided using an implementation of `std::iter::Sum`
/// for this struct.
///
/// # Base Constraints
///
/// For optimal behavior in incremental games, bases should typically be greater
/// than 1. This ensures that larger exponents always represent larger values,
/// which aligns with the exponential growth expected in incremental games where
/// values explode towards infinity. While mathematically valid, bases between 0
/// and 1 would cause values to decrease as exponents increase, which is contrary
/// to the typical use case.
///
/// # Coercion
///
/// Numerical operations involving IdleFloats with different bases will result
/// into implicit coercion of the base into the larger base. That means
/// `f(a^b, c^d) = max(a, c)^F(b, d)`.
///
/// It is highly advised to avoid implicit base coercion at all costs by keeping
/// the base as consistent as possible.
///
/// By default, the base is set to `e`, as it is when evaluating `zero()` or
/// `one()`.
#[derive(Debug, Clone, Copy)]
pub struct IdleFloat<F: Float> {
    pub(crate) base: F,
    pub(crate) exponent: F,
}

impl<F: Float> Zero for IdleFloat<F> {
    /// Returns a representation of 0.
    fn zero() -> Self {
        IdleFloat {
            base: F::one().exp(),
            exponent: F::neg_infinity(),
        }
    }

    fn is_zero(&self) -> bool {
        !self.base.is_nan()
            && F::one() < self.base
            && self.exponent.is_infinite()
            && self.exponent.is_sign_negative()
    }
}

impl<F: Float> One for IdleFloat<F> {
    /// Returns a representation of 1.
    fn one() -> Self {
        IdleFloat {
            base: F::one().exp(),
            exponent: F::zero(),
        }
    }

    fn is_one(&self) -> bool {
        !self.base.is_nan()
            && F::zero() < self.base
            && self.exponent == F::zero()
    }
}

/// Checks if two `IdleFloat`s are equal in value.
///
/// If the bases are different, this method assumes both to be unequal.
impl<F: Float> PartialEq for IdleFloat<F> {
    fn eq(
        &self,
        other: &Self,
    ) -> bool {
        if self.is_nan() || other.is_nan() {
            return false;
        }

        if self.is_zero() && other.is_zero() {
            return true;
        }

        if self.is_one() && other.is_one() {
            return true;
        }

        self.base == other.base && self.exponent == other.exponent
    }
}

/// Checks for ordering between two `IdleFloat`s.
impl<F: Float> PartialOrd for IdleFloat<F> {
    fn partial_cmp(
        &self,
        other: &Self,
    ) -> Option<Ordering> {
        if self.is_nan() || other.is_nan() {
            return None;
        }

        let self_zero = self.is_zero();
        let other_zero = other.is_zero();

        match (self_zero, other_zero) {
            (true, true) => return Some(Equal),
            (true, false) => return Some(Less),
            (false, true) => return Some(Greater),
            _ => {},
        }

        if self.is_one() && other.is_one() {
            return Some(Equal);
        }

        // code usually returns here
        if self.base == other.base {
            return self.exponent.partial_cmp(&other.exponent);
        }

        // rare case when bases are different
        match (
            self.exponent.is_infinite() && self.exponent.is_sign_positive(),
            other.exponent.is_infinite() && self.exponent.is_sign_positive(),
        ) {
            // if both exponents are positive infinite, compare bases
            (true, true) => self.base.partial_cmp(&other.base),

            // if only one is infinite, that which is infinite is greater
            (true, false) => Some(Greater),
            (false, true) => Some(Less),

            // if neither are infinite, compute log values
            (false, false) => {
                let self_log_value = self.exponent * self.base.ln();
                let other_log_value = other.exponent * other.base.ln();
                self_log_value.partial_cmp(&other_log_value)
            },
        }
    }
}

impl<F: Float> std::ops::Neg for IdleFloat<F> {
    type Output = Self;

    /// Returns `NaN` since `IdleFloat`s do not represent negative numbers.
    fn neg(self) -> Self::Output {
        Self::nan()
    }
}

impl<F: Float> num::Num for IdleFloat<F> {
    type FromStrRadixErr = ();

    fn from_str_radix(
        str: &str,
        radix: u32,
    ) -> Result<Self, Self::FromStrRadixErr> {
        let parsed_float = F::from_str_radix(str, radix).map_err(|_| ())?;

        if parsed_float.is_nan() {
            return Ok(Self::nan());
        }

        if parsed_float.is_zero() {
            return Ok(Self::zero());
        }

        if parsed_float == F::one() {
            return Ok(Self::one());
        }

        // for positive numbers, represent as e^ln(number)
        if F::zero() < parsed_float {
            let ln_value = parsed_float.ln();

            if ln_value.is_finite() {
                return Ok(IdleFloat::new(F::one().exp(), ln_value));
            }
        }

        // for negative numbers or other invalid cases, return `NaN` since
        // `IdleFloat` represents only non-negative numbers
        Ok(Self::nan())
    }
}

impl<F: Float> Add<IdleFloat<F>> for IdleFloat<F> {
    type Output = IdleFloat<F>;

    fn add(
        self,
        rhs: IdleFloat<F>,
    ) -> Self::Output {
        // special case: 0 + 0 = 0
        if self.is_zero() && rhs.is_zero() {
            return IdleFloat {
                base: self.base.max(rhs.base),
                exponent: F::neg_infinity(),
            };
        }

        // coerce bases to equalize first
        match self.base.partial_cmp(&rhs.base) {
            Some(Equal) => {}, // pass-through,
            Some(Less) => return self.change_base(rhs.base).add(rhs),
            Some(Greater) => return self.add(rhs.change_base(self.base)),
            None => return Self::nan(),
        }

        // perform LogSumExp
        let base = self.base;
        let max = self.exponent.max(rhs.exponent);
        let self_exp_less = self.exponent - max;
        let rhs_exp_less = rhs.exponent - max;

        let se = base.powf(self_exp_less) + base.powf(rhs_exp_less);
        let lse = se.log(base);

        IdleFloat {
            base,
            exponent: lse + max,
        }
    }
}

impl<F: Float> Sub<IdleFloat<F>> for IdleFloat<F> {
    type Output = IdleFloat<F>;

    fn sub(
        self,
        rhs: IdleFloat<F>,
    ) -> Self::Output {
        // coerce bases to equalize first
        match self.base.partial_cmp(&rhs.base) {
            Some(Equal) => {}, // pass-through,
            Some(Less) => return self.change_base(rhs.base).sub(rhs),
            Some(Greater) => return self.sub(rhs.change_base(self.base)),
            None => return Self::nan(),
        }

        // perform LogSumExp
        let base = self.base;
        let max = self.exponent.max(rhs.exponent);
        let self_exp_less = self.exponent - max;
        let rhs_exp_less = rhs.exponent - max;

        let me = base.powf(self_exp_less) - base.powf(rhs_exp_less);
        let lme = me.log(base);

        IdleFloat {
            base,
            exponent: lme + max,
        }
    }
}

impl<F: Float> Mul<IdleFloat<F>> for IdleFloat<F> {
    type Output = IdleFloat<F>;

    fn mul(
        self,
        rhs: IdleFloat<F>,
    ) -> Self::Output {
        if self.is_nan() || rhs.is_nan() {
            return Self::nan();
        }

        // 0 * x = 0
        if self.is_zero() || rhs.is_zero() {
            return IdleFloat {
                base: self.base.max(rhs.base),
                exponent: F::neg_infinity(),
            };
        }

        // 1 * x = x, x * 1 = x
        if self.is_one() {
            return rhs;
        }

        if rhs.is_one() {
            return self;
        }

        // coerce bases to equalize first
        match self.base.partial_cmp(&rhs.base) {
            Some(Equal) => {}, // pass-through
            Some(Less) => return self.change_base(rhs.base).mul(rhs),
            Some(Greater) => return self.mul(rhs.change_base(self.base)),
            None => return Self::nan(),
        }

        // base^a * base^b = base^(a+b)
        IdleFloat {
            base: self.base,
            exponent: self.exponent + rhs.exponent,
        }
    }
}

impl<F: Float> Div<IdleFloat<F>> for IdleFloat<F> {
    type Output = IdleFloat<F>;

    fn div(
        self,
        rhs: IdleFloat<F>,
    ) -> Self::Output {
        if self.is_nan() || rhs.is_nan() {
            return Self::nan();
        }

        // x / 0 = NaN
        if rhs.is_zero() {
            return Self::nan();
        }

        // 0 / x = 0 where x != NaN
        if self.is_zero() {
            return IdleFloat {
                base: self.base.max(rhs.base),
                exponent: F::neg_infinity(),
            };
        }

        // x / 1 = x
        if rhs.is_one() {
            return self;
        }

        // coerce bases to equalize first
        match self.base.partial_cmp(&rhs.base) {
            Some(Equal) => {}, // pass-through
            Some(Less) => return self.change_base(rhs.base).div(rhs),
            Some(Greater) => return self.div(rhs.change_base(self.base)),
            None => return Self::nan(),
        }

        // base^a / base^b = base^(a-b)
        IdleFloat {
            base: self.base,
            exponent: self.exponent - rhs.exponent,
        }
    }
}

impl<F: Float> std::ops::Rem<IdleFloat<F>> for IdleFloat<F> {
    type Output = IdleFloat<F>;

    fn rem(
        self,
        _rhs: IdleFloat<F>,
    ) -> Self::Output {
        unimplemented!()
    }
}


impl<F: Float> IdleFloat<F> {
    /// Creates a new IdleFloat with the given base and exponent.
    ///
    /// TODO: Add validation for edge cases (negative bases, invalid values, etc.)
    pub const fn new(
        base: F,
        exponent: F,
    ) -> Self {
        IdleFloat {
            base,
            exponent,
        }
    }

    /// Returns `NaN`.
    pub fn nan() -> Self {
        IdleFloat {
            base: F::nan(),
            exponent: F::nan(),
        }
    }

    /// Returns positive infinity.
    pub fn infinity() -> Self {
        IdleFloat {
            base: F::one().exp(), // e
            exponent: F::infinity(),
        }
    }

    /// Checks if this `IdleFloat` is `NaN`.
    pub fn is_nan(self) -> bool {
        self.base.is_nan() || self.exponent.is_nan()
    }

    /// Returns the minimum positive value representable.
    pub fn min_positive_value() -> Self {
        IdleFloat {
            base: F::one() + F::min_positive_value(),
            exponent: -F::max_value(),
        }
    }

    /// Returns the maximum finite value representable.
    pub fn max_value() -> Self {
        IdleFloat {
            base: F::max_value(),
            exponent: F::max_value(),
        }
    }

    /// Classify this `IdleFloat` number.
    /// Note: There are no `Subnormal` values in `IdleFloat` representation.
    pub fn classify(self) -> std::num::FpCategory {
        if self.is_nan() {
            std::num::FpCategory::Nan
        }

        else if self.is_zero() {
            std::num::FpCategory::Zero
        }

        else if self.exponent.is_infinite() && self.exponent.is_sign_positive() {
            std::num::FpCategory::Infinite
        }

        else {
            std::num::FpCategory::Normal
        }
    }

    /// Returns the reciprocal of this `IdleFloat`.
    pub fn recip(self) -> Self {
        if self.is_zero() {
            return Self::infinity();
        }
        if self.is_nan() {
            return self;
        }

        IdleFloat {
            base: self.base,
            exponent: -self.exponent,
        }
    }

    /// Returns the square root of this `IdleFloat`.
    pub fn sqrt(self) -> Self {
        if self.is_zero() || self.is_nan() {
            return self;
        }

        IdleFloat {
            base: self.base,
            exponent: self.exponent / (F::one() + F::one()),
        }
    }

    /// Returns `e^x` where `x` is this `IdleFloat`.
    pub fn exp(self) -> Self {
        if self.is_nan() {
            return self;
        }

        if self.is_zero() {
            return Self::one();
        }

        let e_base = F::one().exp();
        let converted = self.change_base(e_base);

        IdleFloat {
            base: e_base,
            exponent: e_base.powf(converted.exponent),
        }
    }

    /// Returns the natural logarithm of this `IdleFloat`.
    pub fn ln(self) -> Self {
        if self.is_nan() || self.is_zero() {
            return Self::nan();
        }

        if self.is_one() {
            return Self::zero();
        }

        let ln_result = self.exponent * self.base.ln();
        
        IdleFloat {
            base: F::one().exp(), // e
            exponent: ln_result,
        }
    }

    /// Returns the logarithm of this `IdleFloat` with the specified base.
    pub fn log(self, base: Self) -> Self {
        if self.is_nan() || base.is_nan() {
            return Self::nan();
        }
        
        if self.is_zero() || base.is_zero() {
            return Self::nan();
        }
        
        if self.is_one() {
            return Self::zero();
        }
        
        if base.is_one() {
            return Self::nan();
        }

        let self_ln = self.exponent * self.base.ln();
        let base_ln = base.exponent * base.base.ln();
        let log_result = self_ln / base_ln;
        
        // Return IdleFloat representing the value log_result
        if log_result > F::zero() {
            IdleFloat {
                base: F::one().exp(), // e
                exponent: log_result.ln(), // ln(log_result)
            }
        } else {
            Self::nan()
        }
    }

    /// Returns the logarithm of this `IdleFloat` with the specified base as a
    /// `Float`.
    pub fn log_float(self, base: F) -> Self {
        if self.is_nan() || base.is_nan() || base <= F::zero() || base == F::one() {
            return Self::nan();
        }
        
        if self.is_zero() {
            return Self::nan();
        }
        
        if self.is_one() {
            return Self::zero();
        }

        let log_result = (self.exponent * self.base.ln()) / base.ln();
        
        // Return IdleFloat representing the value log_result
        if log_result > F::zero() {
            IdleFloat {
                base: F::one().exp(), // e
                exponent: log_result.ln(), // ln(log_result)
            }
        } else {
            Self::nan()
        }
    }

    /// Returns the maximum of two `IdleFloat` values.
    pub fn max(self, other: Self) -> Self {
        if self.is_nan() || other.is_nan() {
            return Self::nan();
        }

        match self.partial_cmp(&other) {
            Some(Greater) | Some(Equal) => self,
            Some(Less) => other,
            None => Self::nan(),
        }
    }

    /// Returns the minimum of two `IdleFloat` values.
    pub fn min(self, other: Self) -> Self {
        if self.is_nan() || other.is_nan() {
            return Self::nan();
        }

        match self.partial_cmp(&other) {
            Some(Less) | Some(Equal) => self,
            Some(Greater) => other,
            None => Self::nan(),
        }
    }

    /// Changes the base of this number.
    ///
    /// Converts from `old_base^old_exponent` to `new_base^new_exponent` while
    /// preserving the same mathematical value.
    ///
    /// # Special Cases
    ///
    /// - if the current value is zero, returns zero with the new base
    /// - if the current value is one, returns one with the new base
    /// - if the new base is invalid (≤ 0 or NaN), returns NaN
    /// - if conversion would result in invalid exponent, returns NaN
    ///
    /// Read the section about coercion for the warning about changing bases.
    pub fn change_base(
        &self,
        new_base: F,
    ) -> IdleFloat<F> {
        if self.is_nan() {
            return Self::nan();
        }

        if new_base.is_nan() || new_base <= F::zero() {
            return Self::nan();
        }

        if self.is_zero() {
            return IdleFloat {
                base: new_base,
                exponent: F::neg_infinity(),
            };
        }

        if self.is_one() {
            return IdleFloat {
                base: new_base,
                exponent: F::zero(),
            };
        }

        // ff bases are the same, no conversion needed
        if self.base == new_base {
            return *self;
        }

        // convert using the logarithmic law for changing bases
        let ln_old_base = self.base.ln();
        let ln_new_base = new_base.ln();

        // check for invalid logarithms
        if !ln_old_base.is_finite()
            || !ln_new_base.is_finite()
            || ln_new_base == F::zero()
        {
            return Self::nan();
        }

        let new_exponent = self.exponent * ln_old_base / ln_new_base;

        // check if the new exponent is valid
        if !new_exponent.is_finite() {
            return Self::nan();
        }

        IdleFloat {
            base: new_base,
            exponent: new_exponent,
        }
    }
}

/*
#[derive(Debug, Clone, Hash)]
pub enum DisplayFormat(
    Scientific,
    Exponential,
    Engineer,
);

pub struct DelayedFormat<'a> {
    num: &'a IdleFloat,
    format: DisplayFormat,
};
*/
