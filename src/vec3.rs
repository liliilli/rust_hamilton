use std::{
    convert::From,
    fmt::Debug,
    iter,
    ops::{Add, AddAssign, Index, IndexMut, Mul, MulAssign, Sub, SubAssign},
};

/// Represent vector type which contains 3 elements.
///
/// Actually, this type is implemented to have 4 elements
/// for utilizing SIMD and optimization, but last element is hidden.
///
/// To get a actual vector which have only 3 elements inside, convert it into struct [FitVec3].
///
/// # Examples
///
/// ```
/// use hamilton as math;
/// use math::Vec3;
///
/// let mut vec = Vec3::default();
/// assert_eq!(vec, Vec3::new(0f32, 0f32, 0f32));
/// ```
#[derive(Copy, Clone)]
pub struct Vec3 {
    arr: [f32; 4],
}

impl Vec3 {
    /// Create new [Vec3] value.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Vec3;
    ///
    /// let vec = Vec3::new(6f32, 8f32, 10f32);
    /// assert_eq!(vec * 0.5f32, Vec3::new(3f32, 4f32, 5f32));
    /// ```
    pub fn new(x: f32, y: f32, z: f32) -> Self { Self { arr: [x, y, z, 0f32] } }

    /// Create [Vec3] value filled with given scalar value `s`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Vec3;
    ///
    /// let vec = Vec3::from_scalar(17f32) * 0.5f32;
    /// assert_eq!(vec, Vec3::from_scalar(8.5f32));
    /// ```
    pub fn from_scalar(s: f32) -> Self { Self { arr: [s, s, s, 0f32] } }

    /// Create new `Vec3` value from array that has 3 elements.
    pub fn from_array(arr: [f32; 3]) -> Self {
        Self {
            arr: [arr[0], arr[1], arr[2], 0f32],
        }
    }

    /// Get squared length of this vector from `(0, 0, 0)` origin.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Vec3;
    ///
    /// let vec = Vec3::new(3f32, 4f32, 5f32);
    /// assert_eq!(vec.square_length(), 50f32);
    /// ```
    pub fn square_length(&self) -> f32 { self.arr.iter().fold(0f32, |sum, i| sum + i.powi(2)) }

    /// Get length of this vector from `(0, 0, 0)` origin.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Vec3;
    ///
    /// let vec = Vec3::new(3f32, 4f32, 5f32);
    /// assert_eq!(vec.length(), 50f32.sqrt());
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
    /// use math::Vec3;
    ///
    /// let vec = Vec3::new(3f32, 0f32, 4f32);
    /// assert_eq!(vec.into_normalized(), Some(Vec3::new(0.6f32, 0f32, 0.8f32)));
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

    pub fn x(&self) -> f32 { self[0] }
    pub fn y(&self) -> f32 { self[1] }
    pub fn z(&self) -> f32 { self[2] }

    /// Create x unit `(1, 0, 0)` vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Vec3;
    ///
    /// assert_eq!(Vec3::new(1f32, 0f32, 0f32), Vec3::unit_x());
    /// ```
    pub fn unit_x() -> Self { Self::new(1f32, 0f32, 0f32) }

    /// Create y unit `(0, 1, 0)` vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Vec3;
    ///
    /// assert_eq!(Vec3::new(0f32, 1f32, 0f32), Vec3::unit_y());
    /// ```
    pub fn unit_y() -> Self { Self::new(0f32, 1f32, 0f32) }

    /// Create z unit `(0, 0, 1)` vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Vec3;
    ///
    /// assert_eq!(Vec3::new(0f32, 0f32, 1f32), Vec3::unit_z());
    /// ```
    pub fn unit_z() -> Self { Self::new(0f32, 0f32, 1f32) }

    /// Do dot product operation with other `rhs` [Vec3] value.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Vec3;
    ///
    /// assert_eq!(Vec3::new(4f32, 3f32, 2f32).dot(Vec3::new(2f32, 3f32, 4f32)), 25f32);
    /// ```
    pub fn dot(&self, rhs: Self) -> f32 { (*self * rhs).arr.iter().sum() }
}

impl Default for Vec3 {
    /// Create zero vector.
    fn default() -> Self { Self::new(0f32, 0f32, 0f32) }
}

impl PartialEq for Vec3 {
    fn eq(&self, other: &Self) -> bool {
        self.arr[0] == other.arr[0] && self.arr[1] == other.arr[1] && self.arr[2] == other.arr[2]
    }
}

impl From<FitVec3> for Vec3 {
    fn from(vec: FitVec3) -> Self { Self::from_array(vec.arr) }
}

impl Debug for Vec3 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Vec3 {{x: {:.3}, y: {:.3}, z: {:.3}}}",
            self.arr[0], self.arr[1], self.arr[2]
        )
    }
}

impl Index<usize> for Vec3 {
    type Output = f32;
    fn index(&self, index: usize) -> &Self::Output { &self.arr[index] }
}

impl IndexMut<usize> for Vec3 {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output { &mut self.arr[index] }
}

op_binary_impl!(Vec3, Add, add, +, 0 1 2 3);
op_binary_impl!(Vec3, Sub, sub, +, 0 1 2 3);
op_binary_impl!(Vec3, Mul, mul, *, 0 1 2 3);

op_scalar_impl!(Vec3, Add, add, +);
op_scalar_impl!(Vec3, Sub, sub, -);
op_scalar_impl!(Vec3, Mul, mul, *);

op_assign_impl!(Vec3, AddAssign, add_assign, +=, 0 1 2 3);
op_assign_impl!(Vec3, SubAssign, sub_assign, -=, 0 1 2 3);
op_assign_impl!(Vec3, MulAssign, mul_assign, *=, 0 1 2 3);

op_assign_scalar_impl!(Vec3, AddAssign, add_assign, +=);
op_assign_scalar_impl!(Vec3, SubAssign, sub_assign, -=);
op_assign_scalar_impl!(Vec3, MulAssign, mul_assign, *=);

impl iter::Sum for Vec3 {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self { iter.fold(Vec3::default(), |a, b| a + b) }
}

impl<'a> iter::Sum<&'a Vec3> for Vec3 {
    fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self { iter.fold(Vec3::default(), |a, b| a + b) }
}

/// Represent vector type but actually have only 3 elments unlike `Vec3`.
///
///
#[derive(Copy, Clone, Debug)]
pub struct FitVec3 {
    arr: [f32; 3],
}

impl From<Vec3> for FitVec3 {
    fn from(vec: Vec3) -> Self {
        Self {
            arr: [vec.arr[0], vec.arr[1], vec.arr[2]],
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn vector3_test() {
        let vec3 = Vec3::new(13f32, 29f32, 53f32);
        let fitvec3: FitVec3 = vec3.into();
        let reconv_vec3: Vec3 = fitvec3.into();

        println!("{:?}", vec3);
        println!("{:?}", fitvec3);
        println!("{:?}", reconv_vec3);
    }
}
