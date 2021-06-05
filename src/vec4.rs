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
    pub fn from_scalar(s: f32) -> Self { Self { arr: [s, s, s, s] } }

    /// Create new [Vec4] value from array that has 4 elements.
    pub fn from_array(arr: [f32; 4]) -> Self { Self { arr } }

    pub fn x(&self) -> f32 { self[0] }
    pub fn y(&self) -> f32 { self[1] }
    pub fn z(&self) -> f32 { self[2] }
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
    fn index(&self, index: usize) -> &Self::Output { &self.arr[index] }
}

impl IndexMut<usize> for Vec4 {
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
