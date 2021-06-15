use crate::IVec3;
use std::{
    fmt::Debug,
    iter,
    ops::{Add, AddAssign, Index, IndexMut, Mul, MulAssign, Sub, SubAssign},
};

/// Represent vector type which contains 2 integer elements.
///
/// # Examples
///
/// ```
/// use hamilton as math;
/// use math::IVec2;
///
/// let mut vec = IVec2::default();
/// assert_eq!(vec, IVec2::new(0, 0));
/// ```
#[derive(Copy, Clone, PartialEq)]
pub struct IVec2 {
    arr: [i32; 2],
}

impl IVec2 {
    /// Create new [IVec2] value.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::IVec2;
    ///
    /// let vec = IVec2::new(6, 8);
    /// assert_eq!(vec, IVec2::new(3, 4) * 2i32);
    /// ```
    pub fn new(x: i32, y: i32) -> Self {
        Self { arr: [x, y] }
    }

    /// Create [IVec2] value filled with given scalar value `s`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::IVec2;
    ///
    /// let vec = IVec2::from_scalar(17);
    /// assert_eq!(vec, IVec2::from_scalar(17));
    /// ```
    pub fn from_scalar(s: i32) -> Self {
        Self { arr: [s, s] }
    }

    /// Create new [IVec2] value from array that has 2 integer item.
    pub fn from_array(arr: [i32; 2]) -> Self {
        Self {
            arr: [arr[0], arr[1]],
        }
    }

    /// Get squared length of this integer vector from `(0, 0)` origin.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::IVec2;
    ///
    /// let vec = IVec2::new(3, 4);
    /// assert_eq!(vec.square_length(), 25);
    /// ```
    ///
    /// # Notes
    ///
    /// There is no `length()` method because rooted value would be floating point type.
    pub fn square_length(&self) -> usize {
        self.arr.iter().fold(0, |sum, i| sum + i.pow(2)) as usize
    }

    pub fn x(&self) -> i32 {
        self[0]
    }
    pub fn y(&self) -> i32 {
        self[1]
    }

    /// Create x unit `(1, 0)` integer vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::IVec2;
    ///
    /// assert_eq!(IVec2::new(1, 0), IVec2::unit_x());
    /// ```
    pub fn unit_x() -> Self {
        Self::new(1, 0)
    }

    /// Create y unit `(0, 1)` integer vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::IVec2;
    ///
    /// assert_eq!(IVec2::new(0, 1), IVec2::unit_y());
    /// ```
    pub fn unit_y() -> Self {
        Self::new(0, 1)
    }

    /// Get new [IVec2] contains each minimum elements of `self` and given `points` [IVec2] list.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::IVec2;
    ///
    /// let vec = IVec2::from_scalar(0);
    /// let new = vec.min_elements_with(&[
    ///     IVec2::new(0, -3),
    ///     IVec2::new(1, 2),
    ///     IVec2::new(-16, 8)]);
    /// assert_eq!(new, IVec2::new(-16, -3));
    ///
    /// let same = new.min_elements_with(&[]);
    /// assert_eq!(new, same);
    /// ```
    pub fn min_elements_with(&self, points: &[Self]) -> Self {
        points.iter().fold(*self, |prev, point| {
            Self::new(point[0].min(prev[0]), point[1].min(prev[1]))
        })
    }

    /// Get new [IVec2] contains each maximum elements of `self` and given `points` [IVec2] list.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::IVec2;
    ///
    /// let vec = IVec2::from_scalar(0);
    /// let new = vec.max_elements_with(&[
    ///     IVec2::new(0, -3),
    ///     IVec2::new(1, 2),
    ///     IVec2::new(-16, 8)]);
    /// assert_eq!(new, IVec2::new(1, 8));
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

impl Default for IVec2 {
    /// Create zero vector.
    fn default() -> Self {
        Self::from_scalar(0)
    }
}

impl Debug for IVec2 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "IVec2 {{x: {}, y: {}}}", self.arr[0], self.arr[1],)
    }
}

impl Index<usize> for IVec2 {
    type Output = i32;
    fn index(&self, index: usize) -> &Self::Output {
        &self.arr[index]
    }
}

impl IndexMut<usize> for IVec2 {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.arr[index]
    }
}

op_binary_impl!(IVec2, Add, add, +, 0 1);
op_binary_impl!(IVec2, Sub, sub, -, 0 1);
op_binary_impl!(IVec2, Mul, mul, *, 0 1);

op_scalar_impl!(IVec2, Add, add, +, i32);
op_scalar_impl!(IVec2, Sub, sub, -, i32);
op_scalar_impl!(IVec2, Mul, mul, *, i32);

op_assign_impl!(IVec2, AddAssign, add_assign, +=, 0 1);
op_assign_impl!(IVec2, SubAssign, sub_assign, -=, 0 1);
op_assign_impl!(IVec2, MulAssign, mul_assign, *=, 0 1);

op_assign_scalar_impl!(IVec2, AddAssign, add_assign, +=, i32);
op_assign_scalar_impl!(IVec2, SubAssign, sub_assign, -=, i32);
op_assign_scalar_impl!(IVec2, MulAssign, mul_assign, *=, i32);

impl iter::Sum for IVec2 {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(IVec2::default(), |a, b| a + b)
    }
}

impl<'a> iter::Sum<&'a IVec2> for IVec2 {
    fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(IVec2::default(), |a, b| a + b)
    }
}

// ----------------------------------------------------------------------------
//
// VEC2 SWIZZLINGS
//
// ----------------------------------------------------------------------------

impl IVec2 {
    pub fn swizzle_00(&self) -> Self {
        Self::new(0, 0)
    }
    pub fn swizzle_0x(&self) -> Self {
        Self::new(0, self.x())
    }
    pub fn swizzle_0y(&self) -> Self {
        Self::new(0, self.y())
    }
    pub fn swizzle_x0(&self) -> Self {
        Self::new(self.x(), 0)
    }
    pub fn swizzle_xx(&self) -> Self {
        Self::new(self.x(), self.x())
    }
    pub fn swizzle_xy(&self) -> Self {
        Self::new(self.x(), self.y())
    }
    pub fn swizzle_y0(&self) -> Self {
        Self::new(self.y(), 0)
    }
    pub fn swizzle_yx(&self) -> Self {
        Self::new(self.y(), self.x())
    }
    pub fn swizzle_yy(&self) -> Self {
        Self::new(self.y(), self.y())
    }
}

impl IVec2 {
    pub fn swizzle_000(&self) -> IVec3 {
        IVec3::from_scalar(0)
    }
    pub fn swizzle_00x(&self) -> IVec3 {
        IVec3::new(0, 0, self.x())
    }
    pub fn swizzle_00y(&self) -> IVec3 {
        IVec3::new(0, 0, self.y())
    }
    pub fn swizzle_0x0(&self) -> IVec3 {
        IVec3::new(0, self.x(), 0)
    }
    pub fn swizzle_0xx(&self) -> IVec3 {
        IVec3::new(0, self.x(), self.x())
    }
    pub fn swizzle_0xy(&self) -> IVec3 {
        IVec3::new(0, self.x(), self.y())
    }
    pub fn swizzle_0y0(&self) -> IVec3 {
        IVec3::new(0, self.y(), 0)
    }
    pub fn swizzle_0yx(&self) -> IVec3 {
        IVec3::new(0, self.y(), self.x())
    }
    pub fn swizzle_0yy(&self) -> IVec3 {
        IVec3::new(0, self.y(), self.y())
    }
    pub fn swizzle_x00(&self) -> IVec3 {
        IVec3::new(self.x(), 0, 0)
    }
    pub fn swizzle_x0x(&self) -> IVec3 {
        IVec3::new(self.x(), 0, self.x())
    }
    pub fn swizzle_x0y(&self) -> IVec3 {
        IVec3::new(self.x(), 0, self.y())
    }
    pub fn swizzle_xx0(&self) -> IVec3 {
        IVec3::new(self.x(), self.x(), 0)
    }
    pub fn swizzle_xxx(&self) -> IVec3 {
        IVec3::new(self.x(), self.x(), self.x())
    }
    pub fn swizzle_xxy(&self) -> IVec3 {
        IVec3::new(self.x(), self.x(), self.y())
    }
    pub fn swizzle_xy0(&self) -> IVec3 {
        IVec3::new(self.x(), self.y(), 0)
    }
    pub fn swizzle_xyx(&self) -> IVec3 {
        IVec3::new(self.x(), self.y(), self.x())
    }
    pub fn swizzle_xyy(&self) -> IVec3 {
        IVec3::new(self.x(), self.y(), self.y())
    }
    pub fn swizzle_y00(&self) -> IVec3 {
        IVec3::new(self.y(), 0, 0)
    }
    pub fn swizzle_y0x(&self) -> IVec3 {
        IVec3::new(self.y(), 0, self.x())
    }
    pub fn swizzle_y0y(&self) -> IVec3 {
        IVec3::new(self.y(), 0, self.y())
    }
    pub fn swizzle_yx0(&self) -> IVec3 {
        IVec3::new(self.y(), self.x(), 0)
    }
    pub fn swizzle_yxx(&self) -> IVec3 {
        IVec3::new(self.y(), self.x(), self.x())
    }
    pub fn swizzle_yxy(&self) -> IVec3 {
        IVec3::new(self.y(), self.x(), self.y())
    }
    pub fn swizzle_yy0(&self) -> IVec3 {
        IVec3::new(self.y(), self.y(), 0)
    }
    pub fn swizzle_yyx(&self) -> IVec3 {
        IVec3::new(self.y(), self.y(), self.x())
    }
    pub fn swizzle_yyy(&self) -> IVec3 {
        IVec3::new(self.y(), self.y(), self.y())
    }
}
