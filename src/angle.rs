use crate::{NearlyEqual, RangeWrappableMinMax};
use std::{
    f32::consts::PI,
    ops::{self, Add, AddAssign, Deref, DerefMut, Mul, MulAssign, Sub, SubAssign},
};

/// Represents degree angle.
#[derive(Debug, Copy, Clone, PartialEq, PartialOrd)]
pub struct Degree(pub f32);

impl Degree {
    /// Normalize degree angle value into `[-180, 180)` value.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Degree;
    ///
    /// assert_eq!(Degree(270f32).to_normalized(), Degree(-90f32));
    /// assert_eq!(Degree(180f32).to_normalized(), Degree(-180f32));
    /// assert_eq!(Degree(-180f32).to_normalized(), Degree(-180f32));
    /// ```
    pub fn to_normalized(self) -> Self { Self(self.0.to_wrap_min_max(-180f32, 180f32)) }
}

impl Deref for Degree {
    type Target = f32;
    fn deref(&self) -> &Self::Target { &self.0 }
}

impl DerefMut for Degree {
    fn deref_mut(&mut self) -> &mut Self::Target { &mut self.0 }
}

impl From<Radian> for Degree {
    fn from(radian: Radian) -> Self { Degree(*radian * 180f32 / PI) }
}

impl NearlyEqual for Degree {
    fn nearly_equal(&self, to: Self, tolerance: Self) -> bool {
        let off = *self - to;
        off.0.abs() <= tolerance.0
    }
}

op_angle_binary_impl!(Degree, Add, add, +);
op_angle_binary_impl!(Degree, Sub, sub, -);
op_angle_scalar_mul_impl!(Degree, Mul, mul, *, u8 u16 u32 u64 usize i8 i16 i32 i64 isize f32 f64);

op_angle_assign_impl!(Degree, AddAssign, add_assign, +=);
op_angle_assign_impl!(Degree, SubAssign, sub_assign, -=);
op_angle_assign_scalar_impl!(Degree, MulAssign, mul_assign, *=, u8 u16 u32 u64 usize i8 i16 i32 i64 isize f32 f64);

/// Represents radian angle.
#[derive(Debug, Copy, Clone, PartialEq, PartialOrd)]
pub struct Radian(pub f32);

impl Radian {
    /// Normalize degree angle value into `[-PI, PI)` value.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Radian;
    /// use std::f32::consts::PI;
    ///
    /// fn is_nearly_same(lhs: Radian, rhs: Radian) -> bool {
    ///     (lhs - rhs).0.abs() <= std::f32::EPSILON
    /// }
    ///
    /// //assert_eq!(is_nearly_same(Radian(PI * 1.5f32).to_normalized(), Radian(-PI * 0.5f32)), true);
    /// //assert_eq!(is_nearly_same(Radian(PI).to_normalized(), Radian(-PI)), true);
    /// assert_eq!(is_nearly_same(Radian(-PI).to_normalized(), Radian(-PI)), true);
    /// ```
    pub fn to_normalized(self) -> Self { Self(self.0.to_wrap_min_max(-PI, PI)) }
}

impl ops::Deref for Radian {
    type Target = f32;

    fn deref(&self) -> &Self::Target { &self.0 }
}

impl From<Degree> for Radian {
    fn from(degree: Degree) -> Self { Radian(*degree * PI / 180f32) }
}

impl NearlyEqual for Radian {
    fn nearly_equal(&self, to: Self, tolerance: Self) -> bool {
        let off = *self - to;
        off.0.abs() <= tolerance.0
    }
}

op_angle_binary_impl!(Radian, Add, add, +);
op_angle_binary_impl!(Radian, Sub, sub, -);
op_angle_scalar_mul_impl!(Radian, Mul, mul, *, u8 u16 u32 u64 usize i8 i16 i32 i64 isize f32 f64);

op_angle_assign_impl!(Radian, AddAssign, add_assign, +=);
op_angle_assign_impl!(Radian, SubAssign, sub_assign, -=);
op_angle_assign_scalar_impl!(Radian, MulAssign, mul_assign, *=, u8 u16 u32 u64 usize i8 i16 i32 i64 isize f32 f64);

#[cfg(test)]
mod test {
    use super::*;
    use std::f32::EPSILON;

    #[test]
    fn degree_test() {
        let value = Degree(30f32);
        assert_eq!(value + Degree(30f32), Degree(60f32));
    }

    fn is_nearly_same(lhs: Radian, rhs: Radian) -> bool { (lhs - rhs).0.abs() <= EPSILON }

    #[test]
    fn radian_test() {
        let value = Radian(PI);
        assert_eq!(value + Radian(PI), Radian(2f32 * PI));
        assert_eq!(value - Radian(PI), Radian(0f32));
        assert_eq!(is_nearly_same(Radian(-PI).to_normalized(), Radian(-PI)), true);
    }
}
