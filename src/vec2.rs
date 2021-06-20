use crate::{EError, NearlyEqual, Vec3, Vec4};
use std::{
    fmt::Debug,
    iter,
    ops::{Add, AddAssign, Index, IndexMut, Mul, MulAssign, Sub, SubAssign},
};

/// Represent vector type which contains 2 elements.
///
/// # Examples
///
/// ```
/// use hamilton as math;
/// use math::Vec2;
///
/// let mut vec = Vec2::default();
/// assert_eq!(vec, Vec2::new(0f32, 0f32));
/// ```
#[derive(Copy, Clone, PartialEq)]
pub struct Vec2 {
    arr: [f32; 2],
}

impl Vec2 {
    /// Create new [Vec2] value.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Vec2;
    ///
    /// let vec = Vec2::new(6f32, 8f32);
    /// assert_eq!(vec * 0.5f32, Vec2::new(3f32, 4f32));
    /// ```
    pub fn new(x: f32, y: f32) -> Self {
        Self { arr: [x, y] }
    }

    /// Create [Vec2] value filled with given scalar value `s`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Vec2;
    ///
    /// let vec = Vec2::from_scalar(17f32) * 0.5f32;
    /// assert_eq!(vec, Vec2::from_scalar(8.5f32));
    /// ```
    pub fn from_scalar(s: f32) -> Self {
        Self { arr: [s, s] }
    }

    /// Create new [Vec2] value from array that has 2 elements.
    pub fn from_array(arr: [f32; 2]) -> Self {
        Self {
            arr: [arr[0], arr[1]],
        }
    }

    /// Get squared length of this vector from `(0, 0)` origin.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Vec2;
    ///
    /// let vec = Vec2::new(3f32, 4f32);
    /// assert_eq!(vec.square_length(), 25f32);
    /// ```
    pub fn square_length(&self) -> f32 {
        self.arr.iter().fold(0f32, |sum, i| sum + i.powi(2))
    }

    /// Get length of this vector from `(0, 0)` origin.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Vec2;
    ///
    /// let vec = Vec2::new(3f32, 4f32);
    /// assert_eq!(vec.length(), 5f32);
    /// ```
    pub fn length(&self) -> f32 {
        self.square_length().sqrt()
    }

    /// Create normalized vector which length is projected to 1.
    ///
    /// If vector's length is not normal or 0, do nothing but just return `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Vec2;
    ///
    /// // If vector's length is normal, do normlization.
    /// let vec = Vec2::new(3f32, 4f32);
    /// assert_eq!(vec.x(), 3f32);
    /// assert_eq!(vec.y(), 4f32);
    /// assert_eq!(vec.to_normalized().unwrap(), Vec2::new(0.6f32, 0.8f32));
    ///
    /// // If not, do nothing but return `None`.
    /// let vec = Vec2::new(3.24e-76f32, 0.8e-54f32);
    /// assert_eq!(vec.to_normalized().is_err(), true);
    /// ```
    pub fn to_normalized(&self) -> Result<Self, EError> {
        let squared_length = self.square_length();
        if !squared_length.is_normal() {
            Err(EError::ZeroLengthVector)
        } else {
            let inv_squared = 1f32 / squared_length.sqrt();
            Ok(*self * inv_squared)
        }
    }

    pub fn x(&self) -> f32 {
        self[0]
    }
    pub fn y(&self) -> f32 {
        self[1]
    }

    /// Create x unit `(1, 0)` vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Vec2;
    ///
    /// assert_eq!(Vec2::new(1f32, 0f32), Vec2::unit_x());
    /// ```
    pub fn unit_x() -> Self {
        Self::new(1f32, 0f32)
    }

    /// Create y unit `(0, 1)` vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Vec2;
    ///
    /// assert_eq!(Vec2::new(0f32, 1f32), Vec2::unit_y());
    /// ```
    pub fn unit_y() -> Self {
        Self::new(0f32, 1f32)
    }

    /// Do dot product operation with other `rhs` [Vec2] value.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Vec2;
    ///
    /// assert_eq!(Vec2::new(4f32, 3f32).dot(Vec2::new(3f32, 4f32)), 24f32);
    /// ```
    pub fn dot(&self, rhs: Self) -> f32 {
        (*self * rhs).arr.iter().sum()
    }

    /// Project self [Vec2] onto given nonzero vector `nonzero_to`.
    /// `nonzero_to` should not be zeroed length.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Vec2;
    ///
    /// let a = Vec2::new(3f32, 4f32);
    /// let p = Vec2::new(2f32, 0f32);
    /// let a_on_p = a.uncheck_projected_on(p);
    /// assert_eq!(a_on_p, Vec2::new(3f32, 0f32));
    /// ```
    pub fn uncheck_projected_on(&self, nonzero_to: Vec2) -> Self {
        nonzero_to * (self.dot(nonzero_to) * nonzero_to.square_length().recip())
    }

    /// Project self [Vec2] onto given vector `rhs`.
    ///
    /// If given `rhs`'s length is zero or nearly zeroed, just return with error value.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Vec2;
    ///
    /// let a = Vec2::new(3f32, 4f32);
    /// let p = Vec2::new(2f32, 0f32);
    /// let a_on_p = a.projected_on(p).unwrap();
    /// assert_eq!(a_on_p, Vec2::new(3f32, 0f32));
    /// ```
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Vec2;
    ///
    /// let a = Vec2::new(3f32, 4f32);
    /// let p = Vec2::from_scalar(0f32);
    /// let should_err = a.projected_on(p).is_err();
    /// assert_eq!(should_err, true);
    /// ```
    pub fn projected_on(&self, rhs: Vec2) -> Result<Self, EError> {
        let recip = rhs.square_length().recip();
        if !recip.is_normal() {
            return Err(EError::ZeroLengthVector);
        } else {
            Ok(rhs * (self.dot(rhs) * recip))
        }
    }

    /// Caclulate orthogonal to `nonzero_to` but connected to `self`,
    /// and sum of projected vector on `nonzero_to` can be itself.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Vec2;
    ///
    /// let a = Vec2::new(3f32, 4f32);
    /// let p = Vec2::new(1f32, 0f32);
    /// let a_from_a_on_p = a.uncheck_rejected_from(p);
    /// assert_eq!(a_from_a_on_p, Vec2::new(0f32, 4f32));
    /// ```  
    pub fn uncheck_rejected_from(&self, nonzero_to: Vec2) -> Self {
        *self - self.uncheck_projected_on(nonzero_to)
    }

    /// Caclulate orthogonal to `rhs` but connected to `self`,
    ///
    /// If given `rhs`'s length is zero or nearly zeroed, just return with error value.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Vec2;
    ///
    /// let a = Vec2::new(3f32, 4f32);
    /// let p = Vec2::new(1f32, 0f32);
    /// let a_from_a_on_p = a.rejected_from(p).unwrap();
    /// assert_eq!(a_from_a_on_p, Vec2::new(0f32, 4f32));
    /// ```
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Vec2;
    ///
    /// let a = Vec2::new(3f32, 5f32);
    /// let p = Vec2::from_scalar(0f32);
    /// let should_err = a.rejected_from(p).is_err();
    /// assert_eq!(should_err, true);
    /// ```
    pub fn rejected_from(&self, rhs: Vec2) -> Result<Self, EError> {
        Ok(*self - self.projected_on(rhs)?)
    }

    /// Get reflected vector of `self` through non-zero vector [Vec2] `nonzero_vec`.
    ///
    /// `nonzero_vec` [Vec2] vector should not be zero length.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Vec2;
    ///
    /// let vec = Vec2::new(3f32, 4f32);
    /// let axis = Vec2::unit_x();
    /// let reflected = vec.uncheck_reflected_through(axis);
    /// assert_eq!(reflected, Vec2::new(-3f32, 4f32));
    /// ```
    pub fn uncheck_reflected_through(&self, nonzero_vec: Vec2) -> Self {
        self.uncheck_rejected_from(nonzero_vec) - self.uncheck_projected_on(nonzero_vec)
    }

    /// Get reflected vector of `self` through non-zero vector [Vec2] `rhs`.
    ///
    /// If given `rhs`'s length is zero or nearly zeroed, just return with error value.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Vec2;
    ///
    /// let vec = Vec2::new(3f32, 4f32);
    /// let axis = Vec2::unit_x();
    /// let reflected = vec.reflected_through(axis).unwrap();
    /// assert_eq!(reflected, Vec2::new(-3f32, 4f32));
    /// ```
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Vec2;
    ///
    /// let vec = Vec2::new(3f32, 4f32);
    /// let zeroed = Vec2::from_scalar(0f32);
    /// let should_err = vec.reflected_through(zeroed).is_err();
    /// assert_eq!(should_err, true);
    /// ```
    pub fn reflected_through(&self, rhs: Vec2) -> Result<Self, EError> {
        Ok(self.rejected_from(rhs)? - self.projected_on(rhs)?)
    }

    /// Get the involution of `self` [Vec2] through the vector `nonzero_vec`.
    ///
    /// `nonzero_vec` [Vec2] vector should not be zero length.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Vec2;
    ///
    /// let vec = Vec2::new(3f32, 4f32);
    /// let axis = Vec2::unit_x();
    /// let involuted = vec.uncheck_involuted_through(axis);
    /// assert_eq!(involuted, Vec2::new(3f32, -4f32));
    /// ```
    pub fn uncheck_involuted_through(&self, nonzero_vec: Vec2) -> Self {
        self.uncheck_projected_on(nonzero_vec) - self.uncheck_rejected_from(nonzero_vec)
    }

    /// Get the involution of `self` [Vec2] through the vector `rhs`.
    ///
    /// If given `rhs`'s length is zero or nearly zeroed, just return with error value.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Vec2;
    ///
    /// let vec = Vec2::new(3f32, 4f32);
    /// let axis = Vec2::unit_x();
    /// let involuted = vec.involuted_through(axis).unwrap();
    /// assert_eq!(involuted, Vec2::new(3f32, -4f32));
    /// ```
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Vec2;
    ///
    /// let vec = Vec2::new(3f32, 4f32);
    /// let zeroed = Vec2::from_scalar(0f32);
    /// let should_err = vec.involuted_through(zeroed).is_err();
    /// assert_eq!(should_err, true);
    /// ```
    pub fn involuted_through(&self, rhs: Vec2) -> Result<Self, EError> {
        Ok(self.projected_on(rhs)? - self.rejected_from(rhs)?)
    }

    /// Get new [Vec2] contains each minimum elements of `self` and given `points` [Vec2] list.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Vec2;
    ///
    /// let vec = Vec2::from_scalar(0f32);
    /// let new = vec.min_elements_with(&[
    ///     Vec2::new(0f32, -3f32),
    ///     Vec2::new(1f32, 2f32),
    ///     Vec2::new(-16f32, 8f32)]);
    /// assert_eq!(new, Vec2::new(-16f32, -3f32));
    ///
    /// let same = new.min_elements_with(&[]);
    /// assert_eq!(new, same);
    /// ```
    pub fn min_elements_with(&self, points: &[Self]) -> Self {
        points.iter().fold(*self, |prev, point| {
            Self::new(point[0].min(prev[0]), point[1].min(prev[1]))
        })
    }

    /// Get new [Vec2] contains each maximum elements of `self` and given `points` [Vec2] list.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Vec2;
    ///
    /// let vec = Vec2::from_scalar(0f32);
    /// let new = vec.max_elements_with(&[
    ///     Vec2::new(0f32, -3f32),
    ///     Vec2::new(1f32, 2f32),
    ///     Vec2::new(-16f32, 8f32)]);
    /// assert_eq!(new, Vec2::new(1f32, 8f32));
    ///
    /// let same = new.max_elements_with(&[]);
    /// assert_eq!(new, same);
    /// ```
    pub fn max_elements_with(&self, points: &[Self]) -> Self {
        points.iter().fold(*self, |prev, point| {
            Self::new(point[0].max(prev[0]), point[1].max(prev[1]))
        })
    }
}

impl Default for Vec2 {
    /// Create zero vector.
    fn default() -> Self {
        Self::from_scalar(0f32)
    }
}

impl Debug for Vec2 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Vec2 {{x: {:.3}, y: {:.3}}}", self.arr[0], self.arr[1],)
    }
}

impl Index<usize> for Vec2 {
    type Output = f32;
    fn index(&self, index: usize) -> &Self::Output {
        &self.arr[index]
    }
}

impl IndexMut<usize> for Vec2 {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.arr[index]
    }
}

op_binary_impl!(Vec2, Add, add, +, 0 1);
op_binary_impl!(Vec2, Sub, sub, -, 0 1);
op_binary_impl!(Vec2, Mul, mul, *, 0 1);

op_scalar_impl!(Vec2, Add, add, +);
op_scalar_impl!(Vec2, Sub, sub, -);
op_scalar_impl!(Vec2, Mul, mul, *);

op_assign_impl!(Vec2, AddAssign, add_assign, +=, 0 1);
op_assign_impl!(Vec2, SubAssign, sub_assign, -=, 0 1);
op_assign_impl!(Vec2, MulAssign, mul_assign, *=, 0 1);

op_assign_scalar_impl!(Vec2, AddAssign, add_assign, +=);
op_assign_scalar_impl!(Vec2, SubAssign, sub_assign, -=);
op_assign_scalar_impl!(Vec2, MulAssign, mul_assign, *=);

impl iter::Sum for Vec2 {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Vec2::default(), |a, b| a + b)
    }
}

impl<'a> iter::Sum<&'a Vec2> for Vec2 {
    fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(Vec2::default(), |a, b| a + b)
    }
}

impl NearlyEqual<f32> for Vec2 {
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Vec2, NearlyEqual};
    ///
    /// let lhs = Vec2::from_scalar(0.0);
    /// let rhs = Vec2::from_scalar(1e-4);
    /// assert_eq!(lhs.nearly_equal(rhs, 1e-4), true);
    /// assert_eq!(lhs.nearly_equal(rhs, 1e-5), false);
    /// ```
    fn nearly_equal(&self, to: Self, tolerance: f32) -> bool {
        let d = self - to;
        d.x().abs() <= tolerance && d.y().abs() <= tolerance
    }
}

// ----------------------------------------------------------------------------
//
// VEC2 SWIZZLINGS
//
// ----------------------------------------------------------------------------

impl Vec2 {
    pub fn swizzle_00(&self) -> Self {
        Self::new(0f32, 0f32)
    }
    pub fn swizzle_0x(&self) -> Self {
        Self::new(0f32, self.x())
    }
    pub fn swizzle_0y(&self) -> Self {
        Self::new(0f32, self.y())
    }
    pub fn swizzle_x0(&self) -> Self {
        Self::new(self.x(), 0f32)
    }
    pub fn swizzle_xx(&self) -> Self {
        Self::new(self.x(), self.x())
    }
    pub fn swizzle_xy(&self) -> Self {
        Self::new(self.x(), self.y())
    }
    pub fn swizzle_y0(&self) -> Self {
        Self::new(self.y(), 0f32)
    }
    pub fn swizzle_yx(&self) -> Self {
        Self::new(self.y(), self.x())
    }
    pub fn swizzle_yy(&self) -> Self {
        Self::new(self.y(), self.y())
    }
}

impl Vec2 {
    pub fn swizzle_000(&self) -> Vec3 {
        Vec3::from_scalar(0f32)
    }
    pub fn swizzle_00x(&self) -> Vec3 {
        Vec3::new(0f32, 0f32, self.x())
    }
    pub fn swizzle_00y(&self) -> Vec3 {
        Vec3::new(0f32, 0f32, self.y())
    }
    pub fn swizzle_0x0(&self) -> Vec3 {
        Vec3::new(0f32, self.x(), 0f32)
    }
    pub fn swizzle_0xx(&self) -> Vec3 {
        Vec3::new(0f32, self.x(), self.x())
    }
    pub fn swizzle_0xy(&self) -> Vec3 {
        Vec3::new(0f32, self.x(), self.y())
    }
    pub fn swizzle_0y0(&self) -> Vec3 {
        Vec3::new(0f32, self.y(), 0f32)
    }
    pub fn swizzle_0yx(&self) -> Vec3 {
        Vec3::new(0f32, self.y(), self.x())
    }
    pub fn swizzle_0yy(&self) -> Vec3 {
        Vec3::new(0f32, self.y(), self.y())
    }
    pub fn swizzle_x00(&self) -> Vec3 {
        Vec3::new(self.x(), 0f32, 0f32)
    }
    pub fn swizzle_x0x(&self) -> Vec3 {
        Vec3::new(self.x(), 0f32, self.x())
    }
    pub fn swizzle_x0y(&self) -> Vec3 {
        Vec3::new(self.x(), 0f32, self.y())
    }
    pub fn swizzle_xx0(&self) -> Vec3 {
        Vec3::new(self.x(), self.x(), 0f32)
    }
    pub fn swizzle_xxx(&self) -> Vec3 {
        Vec3::new(self.x(), self.x(), self.x())
    }
    pub fn swizzle_xxy(&self) -> Vec3 {
        Vec3::new(self.x(), self.x(), self.y())
    }
    pub fn swizzle_xy0(&self) -> Vec3 {
        Vec3::new(self.x(), self.y(), 0f32)
    }
    pub fn swizzle_xyx(&self) -> Vec3 {
        Vec3::new(self.x(), self.y(), self.x())
    }
    pub fn swizzle_xyy(&self) -> Vec3 {
        Vec3::new(self.x(), self.y(), self.y())
    }
    pub fn swizzle_y00(&self) -> Vec3 {
        Vec3::new(self.y(), 0f32, 0f32)
    }
    pub fn swizzle_y0x(&self) -> Vec3 {
        Vec3::new(self.y(), 0f32, self.x())
    }
    pub fn swizzle_y0y(&self) -> Vec3 {
        Vec3::new(self.y(), 0f32, self.y())
    }
    pub fn swizzle_yx0(&self) -> Vec3 {
        Vec3::new(self.y(), self.x(), 0f32)
    }
    pub fn swizzle_yxx(&self) -> Vec3 {
        Vec3::new(self.y(), self.x(), self.x())
    }
    pub fn swizzle_yxy(&self) -> Vec3 {
        Vec3::new(self.y(), self.x(), self.y())
    }
    pub fn swizzle_yy0(&self) -> Vec3 {
        Vec3::new(self.y(), self.y(), 0f32)
    }
    pub fn swizzle_yyx(&self) -> Vec3 {
        Vec3::new(self.y(), self.y(), self.x())
    }
    pub fn swizzle_yyy(&self) -> Vec3 {
        Vec3::new(self.y(), self.y(), self.y())
    }
}

impl Vec2 {
    pub fn swizzle_0000(&self) -> Vec4 {
        Vec4::from_scalar(0f32)
    }
    pub fn swizzle_000x(&self) -> Vec4 {
        Vec4::new(0f32, 0f32, 0f32, self.x())
    }
    pub fn swizzle_000y(&self) -> Vec4 {
        Vec4::new(0f32, 0f32, 0f32, self.y())
    }
    pub fn swizzle_00x0(&self) -> Vec4 {
        Vec4::new(0f32, 0f32, self.x(), 0f32)
    }
    pub fn swizzle_00xx(&self) -> Vec4 {
        Vec4::new(0f32, 0f32, self.x(), self.x())
    }
    pub fn swizzle_00xy(&self) -> Vec4 {
        Vec4::new(0f32, 0f32, self.x(), self.y())
    }
    pub fn swizzle_00y0(&self) -> Vec4 {
        Vec4::new(0f32, 0f32, self.y(), 0f32)
    }
    pub fn swizzle_00yx(&self) -> Vec4 {
        Vec4::new(0f32, 0f32, self.y(), self.x())
    }
    pub fn swizzle_00yy(&self) -> Vec4 {
        Vec4::new(0f32, 0f32, self.y(), self.y())
    }
    pub fn swizzle_0x00(&self) -> Vec4 {
        Vec4::new(0f32, self.x(), 0f32, 0f32)
    }
    pub fn swizzle_0x0x(&self) -> Vec4 {
        Vec4::new(0f32, self.x(), 0f32, self.x())
    }
    pub fn swizzle_0x0y(&self) -> Vec4 {
        Vec4::new(0f32, self.x(), 0f32, self.y())
    }
    pub fn swizzle_0xx0(&self) -> Vec4 {
        Vec4::new(0f32, self.x(), self.x(), 0f32)
    }
    pub fn swizzle_0xxx(&self) -> Vec4 {
        Vec4::new(0f32, self.x(), self.x(), self.x())
    }
    pub fn swizzle_0xxy(&self) -> Vec4 {
        Vec4::new(0f32, self.x(), self.x(), self.y())
    }
    pub fn swizzle_0xy0(&self) -> Vec4 {
        Vec4::new(0f32, self.x(), self.y(), 0f32)
    }
    pub fn swizzle_0xyx(&self) -> Vec4 {
        Vec4::new(0f32, self.x(), self.y(), self.x())
    }
    pub fn swizzle_0xyy(&self) -> Vec4 {
        Vec4::new(0f32, self.x(), self.y(), self.y())
    }
    pub fn swizzle_0y00(&self) -> Vec4 {
        Vec4::new(0f32, self.y(), 0f32, 0f32)
    }
    pub fn swizzle_0y0x(&self) -> Vec4 {
        Vec4::new(0f32, self.y(), 0f32, self.x())
    }
    pub fn swizzle_0y0y(&self) -> Vec4 {
        Vec4::new(0f32, self.y(), 0f32, self.y())
    }
    pub fn swizzle_0yx0(&self) -> Vec4 {
        Vec4::new(0f32, self.y(), self.x(), 0f32)
    }
    pub fn swizzle_0yxx(&self) -> Vec4 {
        Vec4::new(0f32, self.y(), self.x(), self.x())
    }
    pub fn swizzle_0yxy(&self) -> Vec4 {
        Vec4::new(0f32, self.y(), self.x(), self.y())
    }
    pub fn swizzle_0yy0(&self) -> Vec4 {
        Vec4::new(0f32, self.y(), self.y(), 0f32)
    }
    pub fn swizzle_0yyx(&self) -> Vec4 {
        Vec4::new(0f32, self.y(), self.y(), self.x())
    }
    pub fn swizzle_0yyy(&self) -> Vec4 {
        Vec4::new(0f32, self.y(), self.y(), self.y())
    }

    pub fn swizzle_x000(&self) -> Vec4 {
        Vec4::new(self.x(), 0f32, 0f32, 0f32)
    }
    pub fn swizzle_x00x(&self) -> Vec4 {
        Vec4::new(self.x(), 0f32, 0f32, self.x())
    }
    pub fn swizzle_x00y(&self) -> Vec4 {
        Vec4::new(self.x(), 0f32, 0f32, self.y())
    }
    pub fn swizzle_x0x0(&self) -> Vec4 {
        Vec4::new(self.x(), 0f32, self.x(), 0f32)
    }
    pub fn swizzle_x0xx(&self) -> Vec4 {
        Vec4::new(self.x(), 0f32, self.x(), self.x())
    }
    pub fn swizzle_x0xy(&self) -> Vec4 {
        Vec4::new(self.x(), 0f32, self.x(), self.y())
    }
    pub fn swizzle_x0y0(&self) -> Vec4 {
        Vec4::new(self.x(), 0f32, self.y(), 0f32)
    }
    pub fn swizzle_x0yx(&self) -> Vec4 {
        Vec4::new(self.x(), 0f32, self.y(), self.x())
    }
    pub fn swizzle_x0yy(&self) -> Vec4 {
        Vec4::new(self.x(), 0f32, self.y(), self.y())
    }
    pub fn swizzle_xx00(&self) -> Vec4 {
        Vec4::new(self.x(), self.x(), 0f32, 0f32)
    }
    pub fn swizzle_xx0x(&self) -> Vec4 {
        Vec4::new(self.x(), self.x(), 0f32, self.x())
    }
    pub fn swizzle_xx0y(&self) -> Vec4 {
        Vec4::new(self.x(), self.x(), 0f32, self.y())
    }
    pub fn swizzle_xxx0(&self) -> Vec4 {
        Vec4::new(self.x(), self.x(), self.x(), 0f32)
    }
    pub fn swizzle_xxxx(&self) -> Vec4 {
        Vec4::new(self.x(), self.x(), self.x(), self.x())
    }
    pub fn swizzle_xxxy(&self) -> Vec4 {
        Vec4::new(self.x(), self.x(), self.x(), self.y())
    }
    pub fn swizzle_xxy0(&self) -> Vec4 {
        Vec4::new(self.x(), self.x(), self.y(), 0f32)
    }
    pub fn swizzle_xxyx(&self) -> Vec4 {
        Vec4::new(self.x(), self.x(), self.y(), self.x())
    }
    pub fn swizzle_xxyy(&self) -> Vec4 {
        Vec4::new(self.x(), self.x(), self.y(), self.y())
    }
    pub fn swizzle_xy00(&self) -> Vec4 {
        Vec4::new(self.x(), self.y(), 0f32, 0f32)
    }
    pub fn swizzle_xy0x(&self) -> Vec4 {
        Vec4::new(self.x(), self.y(), 0f32, self.x())
    }
    pub fn swizzle_xy0y(&self) -> Vec4 {
        Vec4::new(self.x(), self.y(), 0f32, self.y())
    }
    pub fn swizzle_xyx0(&self) -> Vec4 {
        Vec4::new(self.x(), self.y(), self.x(), 0f32)
    }
    pub fn swizzle_xyxx(&self) -> Vec4 {
        Vec4::new(self.x(), self.y(), self.x(), self.x())
    }
    pub fn swizzle_xyxy(&self) -> Vec4 {
        Vec4::new(self.x(), self.y(), self.x(), self.y())
    }
    pub fn swizzle_xyy0(&self) -> Vec4 {
        Vec4::new(self.x(), self.y(), self.y(), 0f32)
    }
    pub fn swizzle_xyyx(&self) -> Vec4 {
        Vec4::new(self.x(), self.y(), self.y(), self.x())
    }
    pub fn swizzle_xyyy(&self) -> Vec4 {
        Vec4::new(self.x(), self.y(), self.y(), self.y())
    }

    pub fn swizzle_y000(&self) -> Vec4 {
        Vec4::new(self.y(), 0f32, 0f32, 0f32)
    }
    pub fn swizzle_y00x(&self) -> Vec4 {
        Vec4::new(self.y(), 0f32, 0f32, self.x())
    }
    pub fn swizzle_y00y(&self) -> Vec4 {
        Vec4::new(self.y(), 0f32, 0f32, self.y())
    }
    pub fn swizzle_y0x0(&self) -> Vec4 {
        Vec4::new(self.y(), 0f32, self.x(), 0f32)
    }
    pub fn swizzle_y0xx(&self) -> Vec4 {
        Vec4::new(self.y(), 0f32, self.x(), self.x())
    }
    pub fn swizzle_y0xy(&self) -> Vec4 {
        Vec4::new(self.y(), 0f32, self.x(), self.y())
    }
    pub fn swizzle_y0y0(&self) -> Vec4 {
        Vec4::new(self.y(), 0f32, self.y(), 0f32)
    }
    pub fn swizzle_y0yx(&self) -> Vec4 {
        Vec4::new(self.y(), 0f32, self.y(), self.x())
    }
    pub fn swizzle_y0yy(&self) -> Vec4 {
        Vec4::new(self.y(), 0f32, self.y(), self.y())
    }
    pub fn swizzle_yx00(&self) -> Vec4 {
        Vec4::new(self.y(), self.x(), 0f32, 0f32)
    }
    pub fn swizzle_yx0x(&self) -> Vec4 {
        Vec4::new(self.y(), self.x(), 0f32, self.x())
    }
    pub fn swizzle_yx0y(&self) -> Vec4 {
        Vec4::new(self.y(), self.x(), 0f32, self.y())
    }
    pub fn swizzle_yxx0(&self) -> Vec4 {
        Vec4::new(self.y(), self.x(), self.x(), 0f32)
    }
    pub fn swizzle_yxxx(&self) -> Vec4 {
        Vec4::new(self.y(), self.x(), self.x(), self.x())
    }
    pub fn swizzle_yxxy(&self) -> Vec4 {
        Vec4::new(self.y(), self.x(), self.x(), self.y())
    }
    pub fn swizzle_yxy0(&self) -> Vec4 {
        Vec4::new(self.y(), self.x(), self.y(), 0f32)
    }
    pub fn swizzle_yxyx(&self) -> Vec4 {
        Vec4::new(self.y(), self.x(), self.y(), self.x())
    }
    pub fn swizzle_yxyy(&self) -> Vec4 {
        Vec4::new(self.y(), self.x(), self.y(), self.y())
    }
    pub fn swizzle_yy00(&self) -> Vec4 {
        Vec4::new(self.y(), self.y(), 0f32, 0f32)
    }
    pub fn swizzle_yy0x(&self) -> Vec4 {
        Vec4::new(self.y(), self.y(), 0f32, self.x())
    }
    pub fn swizzle_yy0y(&self) -> Vec4 {
        Vec4::new(self.y(), self.y(), 0f32, self.y())
    }
    pub fn swizzle_yyx0(&self) -> Vec4 {
        Vec4::new(self.y(), self.y(), self.x(), 0f32)
    }
    pub fn swizzle_yyxx(&self) -> Vec4 {
        Vec4::new(self.y(), self.y(), self.x(), self.x())
    }
    pub fn swizzle_yyxy(&self) -> Vec4 {
        Vec4::new(self.y(), self.y(), self.x(), self.y())
    }
    pub fn swizzle_yyy0(&self) -> Vec4 {
        Vec4::new(self.y(), self.y(), self.y(), 0f32)
    }
    pub fn swizzle_yyyx(&self) -> Vec4 {
        Vec4::new(self.y(), self.y(), self.y(), self.x())
    }
    pub fn swizzle_yyyy(&self) -> Vec4 {
        Vec4::new(self.y(), self.y(), self.y(), self.y())
    }
}
