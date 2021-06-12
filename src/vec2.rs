use crate::EError;
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
