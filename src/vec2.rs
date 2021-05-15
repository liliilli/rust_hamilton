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
    pub fn new(x: f32, y: f32) -> Self { Self { arr: [x, y] } }

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
    pub fn from_scalar(s: f32) -> Self { Self { arr: [s, s] } }

    /// Create new [Vec2] value from array that has 2 elements.
    pub fn from_array(arr: [f32; 2]) -> Self { Self { arr: [arr[0], arr[1]] } }

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
    pub fn square_length(&self) -> f32 { self.arr.iter().fold(0f32, |sum, i| sum + i.powi(2)) }

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
    pub fn length(&self) -> f32 { self.square_length().sqrt() }

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
    /// assert_eq!(vec.into_normalized(), Some(Vec2::new(0.6f32, 0.8f32)));
    ///
    /// // If not, do nothing but return `None`.
    /// let vec = Vec2::new(3.24e-76f32, 0.8e-54f32);
    /// assert_eq!(vec.into_normalized(), None);
    /// ```
    pub fn into_normalized(&self) -> Option<Self> {
        let squared_length = self.square_length();
        if !squared_length.is_normal() {
            None
        } else {
            let inv_squared = 1f32 / squared_length.sqrt();
            Some(*self * inv_squared)
        }
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
    pub fn unit_x() -> Self { Self::new(1f32, 0f32) }

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
    pub fn unit_y() -> Self { Self::new(0f32, 1f32) }

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
    pub fn dot(&self, rhs: Self) -> f32 { (*self * rhs).arr.iter().sum() }
}

impl Default for Vec2 {
    /// Create zero vector.
    fn default() -> Self { Self::from_scalar(0f32) }
}

impl Debug for Vec2 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Vec2 {{x: {:.3}, y: {:.3}}}", self.arr[0], self.arr[1],)
    }
}

impl Index<usize> for Vec2 {
    type Output = f32;
    fn index(&self, index: usize) -> &Self::Output { &self.arr[index] }
}

impl IndexMut<usize> for Vec2 {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output { &mut self.arr[index] }
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
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self { iter.fold(Vec2::default(), |a, b| a + b) }
}

impl<'a> iter::Sum<&'a Vec2> for Vec2 {
    fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self { iter.fold(Vec2::default(), |a, b| a + b) }
}
