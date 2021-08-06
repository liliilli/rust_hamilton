use crate::{NearlyEqual, Vec2, Vec3};
use std::{
    fmt::{Debug, Display},
    iter,
    ops::{Add, AddAssign, Index, IndexMut, Mul, MulAssign, Sub, SubAssign},
};

/// Represent vector type which contains 4 elements.
///
/// # Examples
///
/// ```
/// use hamilton as math;
/// use math::Vec4;
///
/// let mut vec = Vec4::default();
/// assert_eq!(vec, Vec4::new(0f32, 0f32, 0f32, 0f32));
/// ```
#[derive(Copy, Clone, PartialEq)]
pub struct Vec4 {
    arr: [f32; 4],
}

impl Vec4 {
    /// Create new [Vec4] value.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Vec4;
    ///
    /// let vec = Vec4::new(6f32, 8f32, 10f32, 1f32);
    /// assert_eq!(vec * 0.5f32, Vec4::new(3f32, 4f32, 5f32, 0.5f32));
    /// ```
    #[inline]
    pub fn new(x: f32, y: f32, z: f32, w: f32) -> Self { Self { arr: [x, y, z, w] } }

    /// Create [Vec4] value filled with given scalar value `s`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Vec4;
    ///
    /// let vec = Vec4::from_scalar(17f32) * 0.5f32;
    /// assert_eq!(vec, Vec4::from_scalar(8.5f32));
    /// ```
    #[inline]
    pub fn from_scalar(s: f32) -> Self { Self { arr: [s, s, s, s] } }

    /// Create new [Vec4] value from array that has 4 elements.
    #[inline]
    pub fn from_array(arr: [f32; 4]) -> Self { Self { arr } }

    #[inline]
    pub fn x(&self) -> f32 { self[0] }
    #[inline]
    pub fn y(&self) -> f32 { self[1] }
    #[inline]
    pub fn z(&self) -> f32 { self[2] }
    #[inline]
    pub fn w(&self) -> f32 { self[3] }

    /// Do dot product operation with other `rhs` [Vec4] value.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Vec4;
    ///
    /// assert_eq!(Vec4::new(4f32, 3f32, 2f32, 1f32).dot(Vec4::new(2f32, 3f32, 4f32, 1f32)), 26f32);
    /// ```
    pub fn dot(&self, rhs: Self) -> f32 { (*self * rhs).arr.iter().sum() }
}

impl Default for Vec4 {
    /// Create zero vector.
    #[inline]
    fn default() -> Self { Self::new(0f32, 0f32, 0f32, 0f32) }
}

impl Debug for Vec4 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Vec4 {{x: {:.3}, y: {:.3}, z: {:.3}, w: {:.3}}}",
            self.arr[0], self.arr[1], self.arr[2], self.arr[3]
        )
    }
}

impl Display for Vec4 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Vec4 {{x: {:.3}, y: {:.3}, z: {:.3}, w: {:.3}}}",
            self.arr[0], self.arr[1], self.arr[2], self.arr[3]
        )
    }
}

impl Index<usize> for Vec4 {
    type Output = f32;
    #[inline]
    fn index(&self, index: usize) -> &Self::Output { &self.arr[index] }
}

impl IndexMut<usize> for Vec4 {
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut Self::Output { &mut self.arr[index] }
}

op_binary_impl!(Vec4, Add, add, +, 0 1 2 3);
op_binary_impl!(Vec4, Sub, sub, -, 0 1 2 3);
op_binary_impl!(Vec4, Mul, mul, *, 0 1 2 3);

op_scalar_impl!(Vec4, Add, add, +);
op_scalar_impl!(Vec4, Sub, sub, -);
op_scalar_impl!(Vec4, Mul, mul, *);

op_assign_impl!(Vec4, AddAssign, add_assign, +=, 0 1 2 3);
op_assign_impl!(Vec4, SubAssign, sub_assign, -=, 0 1 2 3);
op_assign_impl!(Vec4, MulAssign, mul_assign, *=, 0 1 2 3);

op_assign_scalar_impl!(Vec4, AddAssign, add_assign, +=);
op_assign_scalar_impl!(Vec4, SubAssign, sub_assign, -=);
op_assign_scalar_impl!(Vec4, MulAssign, mul_assign, *=);

impl iter::Sum for Vec4 {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self { iter.fold(Vec4::default(), |a, b| a + b) }
}

impl<'a> iter::Sum<&'a Vec4> for Vec4 {
    fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self { iter.fold(Vec4::default(), |a, b| a + b) }
}

impl NearlyEqual<f32> for Vec4 {
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Vec4, NearlyEqual};
    ///
    /// let lhs = Vec4::from_scalar(0.0);
    /// let rhs = Vec4::from_scalar(1e-4);
    /// assert_eq!(lhs.nearly_equal(rhs, 1e-4), true);
    /// assert_eq!(lhs.nearly_equal(rhs, 1e-5), false);
    /// ```
    fn nearly_equal(&self, to: Self, tolerance: f32) -> bool {
        let d = self - to;
        d.x().abs() <= tolerance && d.y().abs() <= tolerance && d.z().abs() <= tolerance && d.w().abs() <= tolerance
    }
}

// ----------------------------------------------------------------------------
//
// VEC4 SWIZZLINGS
//
// ----------------------------------------------------------------------------

impl Vec4 {
    #[inline]
    pub fn swizzle_00(&self) -> Vec2 { Vec2::new(0f32, 0f32) }
    #[inline]
    pub fn swizzle_0x(&self) -> Vec2 { Vec2::new(0f32, self.x()) }
    #[inline]
    pub fn swizzle_0y(&self) -> Vec2 { Vec2::new(0f32, self.y()) }
    #[inline]
    pub fn swizzle_0z(&self) -> Vec2 { Vec2::new(0f32, self.z()) }
    #[inline]
    pub fn swizzle_0w(&self) -> Vec2 { Vec2::new(0f32, self.w()) }

    #[inline]
    pub fn swizzle_x0(&self) -> Vec2 { Vec2::new(self.x(), 0f32) }
    #[inline]
    pub fn swizzle_xx(&self) -> Vec2 { Vec2::new(self.x(), self.x()) }
    #[inline]
    pub fn swizzle_xy(&self) -> Vec2 { Vec2::new(self.x(), self.y()) }
    #[inline]
    pub fn swizzle_xz(&self) -> Vec2 { Vec2::new(self.x(), self.z()) }
    #[inline]
    pub fn swizzle_xw(&self) -> Vec2 { Vec2::new(self.x(), self.w()) }

    #[inline]
    pub fn swizzle_y0(&self) -> Vec2 { Vec2::new(self.y(), 0f32) }
    #[inline]
    pub fn swizzle_yx(&self) -> Vec2 { Vec2::new(self.y(), self.x()) }
    #[inline]
    pub fn swizzle_yy(&self) -> Vec2 { Vec2::new(self.y(), self.y()) }
    #[inline]
    pub fn swizzle_yz(&self) -> Vec2 { Vec2::new(self.y(), self.z()) }
    #[inline]
    pub fn swizzle_yw(&self) -> Vec2 { Vec2::new(self.y(), self.w()) }

    #[inline]
    pub fn swizzle_z0(&self) -> Vec2 { Vec2::new(self.z(), 0f32) }
    #[inline]
    pub fn swizzle_zx(&self) -> Vec2 { Vec2::new(self.z(), self.x()) }
    #[inline]
    pub fn swizzle_zy(&self) -> Vec2 { Vec2::new(self.z(), self.y()) }
    #[inline]
    pub fn swizzle_zz(&self) -> Vec2 { Vec2::new(self.z(), self.z()) }
    #[inline]
    pub fn swizzle_zw(&self) -> Vec2 { Vec2::new(self.z(), self.w()) }

    #[inline]
    pub fn swizzle_w0(&self) -> Vec2 { Vec2::new(self.w(), 0f32) }
    #[inline]
    pub fn swizzle_wx(&self) -> Vec2 { Vec2::new(self.w(), self.x()) }
    #[inline]
    pub fn swizzle_wy(&self) -> Vec2 { Vec2::new(self.w(), self.y()) }
    #[inline]
    pub fn swizzle_wz(&self) -> Vec2 { Vec2::new(self.w(), self.z()) }
    #[inline]
    pub fn swizzle_ww(&self) -> Vec2 { Vec2::new(self.w(), self.w()) }
}

impl Vec4 {
    #[inline]
    pub fn swizzle_000(&self) -> Vec3 { Vec3::new(0f32, 0f32, 0f32) }
    #[inline]
    pub fn swizzle_00x(&self) -> Vec3 { Vec3::new(0f32, 0f32, self.x()) }
    #[inline]
    pub fn swizzle_00y(&self) -> Vec3 { Vec3::new(0f32, 0f32, self.y()) }
    #[inline]
    pub fn swizzle_00z(&self) -> Vec3 { Vec3::new(0f32, 0f32, self.z()) }
    #[inline]
    pub fn swizzle_00w(&self) -> Vec3 { Vec3::new(0f32, 0f32, self.w()) }
    #[inline]
    pub fn swizzle_0x0(&self) -> Vec3 { Vec3::new(0f32, self.x(), 0f32) }
    #[inline]
    pub fn swizzle_0xx(&self) -> Vec3 { Vec3::new(0f32, self.x(), self.x()) }
    #[inline]
    pub fn swizzle_0xy(&self) -> Vec3 { Vec3::new(0f32, self.x(), self.y()) }
    #[inline]
    pub fn swizzle_0xz(&self) -> Vec3 { Vec3::new(0f32, self.x(), self.z()) }
    #[inline]
    pub fn swizzle_0xw(&self) -> Vec3 { Vec3::new(0f32, self.x(), self.w()) }
    #[inline]
    pub fn swizzle_0y0(&self) -> Vec3 { Vec3::new(0f32, self.y(), 0f32) }
    #[inline]
    pub fn swizzle_0yx(&self) -> Vec3 { Vec3::new(0f32, self.y(), self.x()) }
    #[inline]
    pub fn swizzle_0yy(&self) -> Vec3 { Vec3::new(0f32, self.y(), self.y()) }
    #[inline]
    pub fn swizzle_0yz(&self) -> Vec3 { Vec3::new(0f32, self.y(), self.z()) }
    #[inline]
    pub fn swizzle_0yw(&self) -> Vec3 { Vec3::new(0f32, self.y(), self.w()) }
    #[inline]
    pub fn swizzle_0z0(&self) -> Vec3 { Vec3::new(0f32, self.z(), 0f32) }
    #[inline]
    pub fn swizzle_0zx(&self) -> Vec3 { Vec3::new(0f32, self.z(), self.x()) }
    #[inline]
    pub fn swizzle_0zy(&self) -> Vec3 { Vec3::new(0f32, self.z(), self.y()) }
    #[inline]
    pub fn swizzle_0zz(&self) -> Vec3 { Vec3::new(0f32, self.z(), self.z()) }
    #[inline]
    pub fn swizzle_0zw(&self) -> Vec3 { Vec3::new(0f32, self.z(), self.w()) }
    #[inline]
    pub fn swizzle_0w0(&self) -> Vec3 { Vec3::new(0f32, self.w(), 0f32) }
    #[inline]
    pub fn swizzle_0wx(&self) -> Vec3 { Vec3::new(0f32, self.w(), self.x()) }
    #[inline]
    pub fn swizzle_0wy(&self) -> Vec3 { Vec3::new(0f32, self.w(), self.y()) }
    #[inline]
    pub fn swizzle_0wz(&self) -> Vec3 { Vec3::new(0f32, self.w(), self.z()) }
    #[inline]
    pub fn swizzle_0ww(&self) -> Vec3 { Vec3::new(0f32, self.w(), self.w()) }

    #[inline]
    pub fn swizzle_x00(&self) -> Vec3 { Vec3::new(self.x(), 0f32, 0f32) }
    #[inline]
    pub fn swizzle_x0x(&self) -> Vec3 { Vec3::new(self.x(), 0f32, self.x()) }
    #[inline]
    pub fn swizzle_x0y(&self) -> Vec3 { Vec3::new(self.x(), 0f32, self.y()) }
    #[inline]
    pub fn swizzle_x0z(&self) -> Vec3 { Vec3::new(self.x(), 0f32, self.z()) }
    #[inline]
    pub fn swizzle_x0w(&self) -> Vec3 { Vec3::new(self.x(), 0f32, self.w()) }
    #[inline]
    pub fn swizzle_xx0(&self) -> Vec3 { Vec3::new(self.x(), self.x(), 0f32) }
    #[inline]
    pub fn swizzle_xxx(&self) -> Vec3 { Vec3::new(self.x(), self.x(), self.x()) }
    #[inline]
    pub fn swizzle_xxy(&self) -> Vec3 { Vec3::new(self.x(), self.x(), self.y()) }
    #[inline]
    pub fn swizzle_xxz(&self) -> Vec3 { Vec3::new(self.x(), self.x(), self.z()) }
    #[inline]
    pub fn swizzle_xxw(&self) -> Vec3 { Vec3::new(self.x(), self.x(), self.w()) }
    #[inline]
    pub fn swizzle_xy0(&self) -> Vec3 { Vec3::new(self.x(), self.y(), 0f32) }
    #[inline]
    pub fn swizzle_xyx(&self) -> Vec3 { Vec3::new(self.x(), self.y(), self.x()) }
    #[inline]
    pub fn swizzle_xyy(&self) -> Vec3 { Vec3::new(self.x(), self.y(), self.y()) }
    #[inline]
    pub fn swizzle_xyz(&self) -> Vec3 { Vec3::new(self.x(), self.y(), self.z()) }
    #[inline]
    pub fn swizzle_xyw(&self) -> Vec3 { Vec3::new(self.x(), self.y(), self.w()) }
    #[inline]
    pub fn swizzle_xz0(&self) -> Vec3 { Vec3::new(self.x(), self.z(), 0f32) }
    #[inline]
    pub fn swizzle_xzx(&self) -> Vec3 { Vec3::new(self.x(), self.z(), self.x()) }
    #[inline]
    pub fn swizzle_xzy(&self) -> Vec3 { Vec3::new(self.x(), self.z(), self.y()) }
    #[inline]
    pub fn swizzle_xzz(&self) -> Vec3 { Vec3::new(self.x(), self.z(), self.z()) }
    #[inline]
    pub fn swizzle_xzw(&self) -> Vec3 { Vec3::new(self.x(), self.z(), self.w()) }
    #[inline]
    pub fn swizzle_xw0(&self) -> Vec3 { Vec3::new(self.x(), self.w(), 0f32) }
    #[inline]
    pub fn swizzle_xwx(&self) -> Vec3 { Vec3::new(self.x(), self.w(), self.x()) }
    #[inline]
    pub fn swizzle_xwy(&self) -> Vec3 { Vec3::new(self.x(), self.w(), self.y()) }
    #[inline]
    pub fn swizzle_xwz(&self) -> Vec3 { Vec3::new(self.x(), self.w(), self.z()) }
    #[inline]
    pub fn swizzle_xww(&self) -> Vec3 { Vec3::new(self.x(), self.w(), self.w()) }

    #[inline]
    pub fn swizzle_y00(&self) -> Vec3 { Vec3::new(self.y(), 0f32, 0f32) }
    #[inline]
    pub fn swizzle_y0x(&self) -> Vec3 { Vec3::new(self.y(), 0f32, self.x()) }
    #[inline]
    pub fn swizzle_y0y(&self) -> Vec3 { Vec3::new(self.y(), 0f32, self.y()) }
    #[inline]
    pub fn swizzle_y0z(&self) -> Vec3 { Vec3::new(self.y(), 0f32, self.z()) }
    #[inline]
    pub fn swizzle_y0w(&self) -> Vec3 { Vec3::new(self.y(), 0f32, self.w()) }
    #[inline]
    pub fn swizzle_yx0(&self) -> Vec3 { Vec3::new(self.y(), self.x(), 0f32) }
    #[inline]
    pub fn swizzle_yxx(&self) -> Vec3 { Vec3::new(self.y(), self.x(), self.x()) }
    #[inline]
    pub fn swizzle_yxy(&self) -> Vec3 { Vec3::new(self.y(), self.x(), self.y()) }
    #[inline]
    pub fn swizzle_yxz(&self) -> Vec3 { Vec3::new(self.y(), self.x(), self.z()) }
    #[inline]
    pub fn swizzle_yxw(&self) -> Vec3 { Vec3::new(self.y(), self.x(), self.w()) }
    #[inline]
    pub fn swizzle_yy0(&self) -> Vec3 { Vec3::new(self.y(), self.y(), 0f32) }
    #[inline]
    pub fn swizzle_yyx(&self) -> Vec3 { Vec3::new(self.y(), self.y(), self.x()) }
    #[inline]
    pub fn swizzle_yyy(&self) -> Vec3 { Vec3::new(self.y(), self.y(), self.y()) }
    #[inline]
    pub fn swizzle_yyz(&self) -> Vec3 { Vec3::new(self.y(), self.y(), self.z()) }
    #[inline]
    pub fn swizzle_yyw(&self) -> Vec3 { Vec3::new(self.y(), self.y(), self.w()) }
    #[inline]
    pub fn swizzle_yz0(&self) -> Vec3 { Vec3::new(self.y(), self.z(), 0f32) }
    #[inline]
    pub fn swizzle_yzx(&self) -> Vec3 { Vec3::new(self.y(), self.z(), self.x()) }
    #[inline]
    pub fn swizzle_yzy(&self) -> Vec3 { Vec3::new(self.y(), self.z(), self.y()) }
    #[inline]
    pub fn swizzle_yzz(&self) -> Vec3 { Vec3::new(self.y(), self.z(), self.z()) }
    #[inline]
    pub fn swizzle_yzw(&self) -> Vec3 { Vec3::new(self.y(), self.z(), self.w()) }
    #[inline]
    pub fn swizzle_yw0(&self) -> Vec3 { Vec3::new(self.y(), self.w(), 0f32) }
    #[inline]
    pub fn swizzle_ywx(&self) -> Vec3 { Vec3::new(self.y(), self.w(), self.x()) }
    #[inline]
    pub fn swizzle_ywy(&self) -> Vec3 { Vec3::new(self.y(), self.w(), self.y()) }
    #[inline]
    pub fn swizzle_ywz(&self) -> Vec3 { Vec3::new(self.y(), self.w(), self.z()) }
    #[inline]
    pub fn swizzle_yww(&self) -> Vec3 { Vec3::new(self.y(), self.w(), self.w()) }

    #[inline]
    pub fn swizzle_z00(&self) -> Vec3 { Vec3::new(self.z(), 0f32, 0f32) }
    #[inline]
    pub fn swizzle_z0x(&self) -> Vec3 { Vec3::new(self.z(), 0f32, self.x()) }
    #[inline]
    pub fn swizzle_z0y(&self) -> Vec3 { Vec3::new(self.z(), 0f32, self.y()) }
    #[inline]
    pub fn swizzle_z0z(&self) -> Vec3 { Vec3::new(self.z(), 0f32, self.z()) }
    #[inline]
    pub fn swizzle_z0w(&self) -> Vec3 { Vec3::new(self.z(), 0f32, self.w()) }
    #[inline]
    pub fn swizzle_zx0(&self) -> Vec3 { Vec3::new(self.z(), self.x(), 0f32) }
    #[inline]
    pub fn swizzle_zxx(&self) -> Vec3 { Vec3::new(self.z(), self.x(), self.x()) }
    #[inline]
    pub fn swizzle_zxy(&self) -> Vec3 { Vec3::new(self.z(), self.x(), self.y()) }
    #[inline]
    pub fn swizzle_zxz(&self) -> Vec3 { Vec3::new(self.z(), self.x(), self.z()) }
    #[inline]
    pub fn swizzle_zxw(&self) -> Vec3 { Vec3::new(self.z(), self.x(), self.w()) }
    #[inline]
    pub fn swizzle_zy0(&self) -> Vec3 { Vec3::new(self.z(), self.y(), 0f32) }
    #[inline]
    pub fn swizzle_zyx(&self) -> Vec3 { Vec3::new(self.z(), self.y(), self.x()) }
    #[inline]
    pub fn swizzle_zyy(&self) -> Vec3 { Vec3::new(self.z(), self.y(), self.y()) }
    #[inline]
    pub fn swizzle_zyz(&self) -> Vec3 { Vec3::new(self.z(), self.y(), self.z()) }
    #[inline]
    pub fn swizzle_zyw(&self) -> Vec3 { Vec3::new(self.z(), self.y(), self.w()) }
    #[inline]
    pub fn swizzle_zz0(&self) -> Vec3 { Vec3::new(self.z(), self.z(), 0f32) }
    #[inline]
    pub fn swizzle_zzx(&self) -> Vec3 { Vec3::new(self.z(), self.z(), self.x()) }
    #[inline]
    pub fn swizzle_zzy(&self) -> Vec3 { Vec3::new(self.z(), self.z(), self.y()) }
    #[inline]
    pub fn swizzle_zzz(&self) -> Vec3 { Vec3::new(self.z(), self.z(), self.z()) }
    #[inline]
    pub fn swizzle_zzw(&self) -> Vec3 { Vec3::new(self.z(), self.z(), self.w()) }
    #[inline]
    pub fn swizzle_zw0(&self) -> Vec3 { Vec3::new(self.z(), self.w(), 0f32) }
    #[inline]
    pub fn swizzle_zwx(&self) -> Vec3 { Vec3::new(self.z(), self.w(), self.x()) }
    #[inline]
    pub fn swizzle_zwy(&self) -> Vec3 { Vec3::new(self.z(), self.w(), self.y()) }
    #[inline]
    pub fn swizzle_zwz(&self) -> Vec3 { Vec3::new(self.z(), self.w(), self.z()) }
    #[inline]
    pub fn swizzle_zww(&self) -> Vec3 { Vec3::new(self.z(), self.w(), self.w()) }

    #[inline]
    pub fn swizzle_w00(&self) -> Vec3 { Vec3::new(self.w(), 0f32, 0f32) }
    #[inline]
    pub fn swizzle_w0x(&self) -> Vec3 { Vec3::new(self.w(), 0f32, self.x()) }
    #[inline]
    pub fn swizzle_w0y(&self) -> Vec3 { Vec3::new(self.w(), 0f32, self.y()) }
    #[inline]
    pub fn swizzle_w0z(&self) -> Vec3 { Vec3::new(self.w(), 0f32, self.z()) }
    #[inline]
    pub fn swizzle_w0w(&self) -> Vec3 { Vec3::new(self.w(), 0f32, self.w()) }
    #[inline]
    pub fn swizzle_wx0(&self) -> Vec3 { Vec3::new(self.w(), self.x(), 0f32) }
    #[inline]
    pub fn swizzle_wxx(&self) -> Vec3 { Vec3::new(self.w(), self.x(), self.x()) }
    #[inline]
    pub fn swizzle_wxy(&self) -> Vec3 { Vec3::new(self.w(), self.x(), self.y()) }
    #[inline]
    pub fn swizzle_wxz(&self) -> Vec3 { Vec3::new(self.w(), self.x(), self.z()) }
    #[inline]
    pub fn swizzle_wxw(&self) -> Vec3 { Vec3::new(self.w(), self.x(), self.w()) }
    #[inline]
    pub fn swizzle_wy0(&self) -> Vec3 { Vec3::new(self.w(), self.y(), 0f32) }
    #[inline]
    pub fn swizzle_wyx(&self) -> Vec3 { Vec3::new(self.w(), self.y(), self.x()) }
    #[inline]
    pub fn swizzle_wyy(&self) -> Vec3 { Vec3::new(self.w(), self.y(), self.y()) }
    #[inline]
    pub fn swizzle_wyz(&self) -> Vec3 { Vec3::new(self.w(), self.y(), self.z()) }
    #[inline]
    pub fn swizzle_wyw(&self) -> Vec3 { Vec3::new(self.w(), self.y(), self.w()) }
    #[inline]
    pub fn swizzle_wz0(&self) -> Vec3 { Vec3::new(self.w(), self.z(), 0f32) }
    #[inline]
    pub fn swizzle_wzx(&self) -> Vec3 { Vec3::new(self.w(), self.z(), self.x()) }
    #[inline]
    pub fn swizzle_wzy(&self) -> Vec3 { Vec3::new(self.w(), self.z(), self.y()) }
    #[inline]
    pub fn swizzle_wzz(&self) -> Vec3 { Vec3::new(self.w(), self.z(), self.z()) }
    #[inline]
    pub fn swizzle_wzw(&self) -> Vec3 { Vec3::new(self.w(), self.z(), self.w()) }
    #[inline]
    pub fn swizzle_ww0(&self) -> Vec3 { Vec3::new(self.w(), self.w(), 0f32) }
    #[inline]
    pub fn swizzle_wwx(&self) -> Vec3 { Vec3::new(self.w(), self.w(), self.x()) }
    #[inline]
    pub fn swizzle_wwy(&self) -> Vec3 { Vec3::new(self.w(), self.w(), self.y()) }
    #[inline]
    pub fn swizzle_wwz(&self) -> Vec3 { Vec3::new(self.w(), self.w(), self.z()) }
    #[inline]
    pub fn swizzle_www(&self) -> Vec3 { Vec3::new(self.w(), self.w(), self.w()) }
}
