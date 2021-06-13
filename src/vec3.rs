use crate::{EError, Quat, Radian, Ray, Vec2, Vec4};
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
    pub fn new(x: f32, y: f32, z: f32) -> Self {
        Self {
            arr: [x, y, z, 0f32],
        }
    }

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
    pub fn from_scalar(s: f32) -> Self {
        Self {
            arr: [s, s, s, 0f32],
        }
    }

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
    pub fn square_length(&self) -> f32 {
        self.arr.iter().fold(0f32, |sum, i| sum + i.powi(2))
    }

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
    /// use math::Vec3;
    ///
    /// let vec = Vec3::new(3f32, 0f32, 4f32);
    /// assert_eq!(vec.to_normalized().unwrap(), Vec3::new(0.6f32, 0f32, 0.8f32));
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
    pub fn z(&self) -> f32 {
        self[2]
    }

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
    pub fn unit_x() -> Self {
        Self::new(1f32, 0f32, 0f32)
    }

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
    pub fn unit_y() -> Self {
        Self::new(0f32, 1f32, 0f32)
    }

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
    pub fn unit_z() -> Self {
        Self::new(0f32, 0f32, 1f32)
    }

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
    pub fn dot(&self, rhs: Self) -> f32 {
        (*self * rhs).arr.iter().sum()
    }

    /// Do cross product operation with other `rhs` [Vec3] value.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Vec3;
    ///
    /// assert_eq!(
    ///     Vec3::new(-4f32, 3f32, -2f32).cross(
    ///     Vec3::new(2f32, -3f32, 4f32)
    /// ), Vec3::new(6f32, 12f32, 6f32));
    /// ```
    pub fn cross(&self, rhs: Self) -> Self {
        let x = (self.y() * rhs.z()) - (self.z() * rhs.y());
        let y = (self.z() * rhs.x()) - (self.x() * rhs.z());
        let z = (self.x() * rhs.y()) - (self.y() * rhs.x());
        Self::new(x, y, z)
    }

    /// Do triple product with given `b` and `c`.
    ///
    /// This function can be helpful to calculate `up` vector from `forward` and `side`.<br>
    /// Do not use that as a scalar triple product, scalar triple product is different to this.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Vec3;
    ///
    /// let forward = Vec3::new(1f32, 5f32, 4f32).to_normalized().unwrap();
    /// let world_up = Vec3::unit_y();
    /// let triple_product = forward.triple_product(forward, world_up) * -1f32;
    /// ```
    pub fn triple_product(&self, b: Self, c: Self) -> Self {
        (b * self.dot(c)) - (c * self.dot(b))
    }

    /// Project self [Vec3] onto given nonzero vector `nonzero_to`.
    /// `nonzero_to` should not be zeroed length.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Vec3;
    ///
    /// let a = Vec3::new(3f32, 5f32, 4f32);
    /// let p = Vec3::new(2f32, 0f32, 2f32);
    /// let a_on_p = a.uncheck_projected_on(p);
    /// assert_eq!(a_on_p, Vec3::new(3.5f32, 0f32, 3.5f32));
    /// ```
    pub fn uncheck_projected_on(&self, nonzero_to: Vec3) -> Self {
        nonzero_to * (self.dot(nonzero_to) * nonzero_to.square_length().recip())
    }

    /// Project self [Vec3] onto given vector `rhs`.
    ///
    /// If given `rhs`'s length is zero or nearly zeroed, just return with error value.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Vec3;
    ///
    /// let a = Vec3::new(3f32, 5f32, 4f32);
    /// let p = Vec3::new(2f32, 0f32, 2f32);
    /// let a_on_p = a.projected_on(p).unwrap();
    /// assert_eq!(a_on_p, Vec3::new(3.5f32, 0f32, 3.5f32));
    /// ```
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Vec3;
    ///
    /// let a = Vec3::new(3f32, 5f32, 4f32);
    /// let p = Vec3::from_scalar(0f32);
    /// let should_err = a.projected_on(p).is_err();
    /// assert_eq!(should_err, true);
    /// ```
    pub fn projected_on(&self, rhs: Vec3) -> Result<Self, EError> {
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
    /// use math::Vec3;
    ///
    /// let a = Vec3::new(3f32, 5f32, 4f32);
    /// let p = Vec3::new(1f32, 0f32, 0f32);
    /// let a_from_a_on_p = a.uncheck_rejected_from(p);
    /// assert_eq!(a_from_a_on_p, Vec3::new(0f32, 5f32, 4f32));
    /// ```  
    pub fn uncheck_rejected_from(&self, nonzero_to: Vec3) -> Self {
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
    /// use math::Vec3;
    ///
    /// let a = Vec3::new(3f32, 5f32, 4f32);
    /// let p = Vec3::new(1f32, 0f32, 0f32);
    /// let a_from_a_on_p = a.rejected_from(p).unwrap();
    /// assert_eq!(a_from_a_on_p, Vec3::new(0f32, 5f32, 4f32));
    /// ```
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Vec3;
    ///
    /// let a = Vec3::new(3f32, 5f32, 4f32);
    /// let p = Vec3::from_scalar(0f32);
    /// let should_err = a.rejected_from(p).is_err();
    /// assert_eq!(should_err, true);
    /// ```
    pub fn rejected_from(&self, rhs: Vec3) -> Result<Self, EError> {
        Ok(*self - self.projected_on(rhs)?)
    }

    /// rotate vector about given `axis` [Vec3] with angle [Radian].
    ///
    /// `axis` [Vec3] vector should not be zero length.
    ///
    /// # examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Vec3, Radian, Degree, NearlyEqual};
    ///
    /// let vec = Vec3::new(3f32, 5f32, 0f32);
    /// let axis = Vec3::unit_y();
    ///
    /// let rot90 = vec.uncheck_rotated_about_axis(axis, Degree(90f32).into());
    /// assert!(rot90.x().nearly_equal(0f32, 1e-4));
    /// assert!(rot90.y().nearly_equal(5f32, 1e-4));
    /// assert!(rot90.z().nearly_equal(-3f32, 1e-4));
    /// ```
    pub fn uncheck_rotated_about_axis(&self, axis: Vec3, angle: Radian) -> Self {
        let axis = axis.to_normalized().unwrap();
        let cos = angle.cos();
        let sin = angle.sin();
        (*self * cos) + (axis * (self.dot(axis) * (1f32 - cos))) - (self.cross(axis) * sin)
    }

    /// rotate vector about given `axis` [Vec3] with angle [Radian].
    ///
    /// If given `axis`'s length is zero or nearly zeroed, just return with error value.
    ///
    /// # examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Vec3, Radian, Degree, NearlyEqual};
    ///
    /// let vec = Vec3::new(3f32, 5f32, 0f32);
    /// let axis = Vec3::unit_y();
    ///
    /// let rot90 = vec.rotated_about_axis(axis, Degree(90f32).into()).unwrap();
    /// assert!(rot90.x().nearly_equal(0f32, 1e-4));
    /// assert!(rot90.y().nearly_equal(5f32, 1e-4));
    /// assert!(rot90.z().nearly_equal(-3f32, 1e-4));
    /// ```
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Vec3, Radian, Degree, NearlyEqual};
    ///
    /// let vec = Vec3::new(3f32, 5f32, 0f32);
    /// let zeroed = Vec3::from_scalar(0f32);
    ///
    /// let should_err = vec.rotated_about_axis(zeroed, Degree(90f32).into()).is_err();
    /// assert_eq!(should_err, true);
    /// ```
    pub fn rotated_about_axis(&self, axis: Vec3, angle: Radian) -> Result<Self, EError> {
        let axis = axis.to_normalized()?;
        let cos = angle.cos();
        let sin = angle.sin();
        Ok((*self * cos) + (axis * (self.dot(axis) * (1f32 - cos))) - (self.cross(axis) * sin))
    }

    /// Get reflected vector of `self` through non-zero vector [Vec3] `nonzero_vec`.
    ///
    /// `nonzero_vec` [Vec3] vector should not be zero length.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Vec3;
    ///
    /// let vec = Vec3::new(3f32, 4f32, 5f32);
    /// let axis = Vec3::unit_x();
    /// let reflected = vec.uncheck_reflected_through(axis);
    /// assert_eq!(reflected, Vec3::new(-3f32, 4f32, 5f32));
    /// ```
    pub fn uncheck_reflected_through(&self, nonzero_vec: Vec3) -> Self {
        self.uncheck_rejected_from(nonzero_vec) - self.uncheck_projected_on(nonzero_vec)
    }

    /// Get reflected vector of `self` through non-zero vector [Vec3] `rhs`.
    ///
    /// If given `rhs`'s length is zero or nearly zeroed, just return with error value.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Vec3;
    ///
    /// let vec = Vec3::new(3f32, 4f32, 5f32);
    /// let axis = Vec3::unit_x();
    /// let reflected = vec.reflected_through(axis).unwrap();
    /// assert_eq!(reflected, Vec3::new(-3f32, 4f32, 5f32));
    /// ```
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Vec3;
    ///
    /// let vec = Vec3::new(3f32, 4f32, 5f32);
    /// let zeroed = Vec3::from_scalar(0f32);
    /// let should_err = vec.reflected_through(zeroed).is_err();
    /// assert_eq!(should_err, true);
    /// ```
    pub fn reflected_through(&self, rhs: Vec3) -> Result<Self, EError> {
        Ok(self.rejected_from(rhs)? - self.projected_on(rhs)?)
    }

    /// Get the involution of `self` [Vec3] through the vector `nonzero_vec`.
    ///
    /// `nonzero_vec` [Vec3] vector should not be zero length.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Vec3;
    ///
    /// let vec = Vec3::new(3f32, 4f32, 5f32);
    /// let axis = Vec3::unit_x();
    /// let involuted = vec.uncheck_involuted_through(axis);
    /// assert_eq!(involuted, Vec3::new(3f32, -4f32, -5f32));
    /// ```
    pub fn uncheck_involuted_through(&self, nonzero_vec: Vec3) -> Self {
        self.uncheck_projected_on(nonzero_vec) - self.uncheck_rejected_from(nonzero_vec)
    }

    /// Get the involution of `self` [Vec3] through the vector `rhs`.
    ///
    /// If given `rhs`'s length is zero or nearly zeroed, just return with error value.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Vec3;
    ///
    /// let vec = Vec3::new(3f32, 4f32, 5f32);
    /// let axis = Vec3::unit_x();
    /// let involuted = vec.involuted_through(axis).unwrap();
    /// assert_eq!(involuted, Vec3::new(3f32, -4f32, -5f32));
    /// ```
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Vec3;
    ///
    /// let vec = Vec3::new(3f32, 4f32, 5f32);
    /// let zeroed = Vec3::from_scalar(0f32);
    /// let should_err = vec.involuted_through(zeroed).is_err();
    /// assert_eq!(should_err, true);
    /// ```
    pub fn involuted_through(&self, rhs: Vec3) -> Result<Self, EError> {
        Ok(self.projected_on(rhs)? - self.rejected_from(rhs)?)
    }

    /// Get the shortest distance from `self` [Vec3] to ray [Ray].
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Vec3, Ray};
    ///
    /// let vec = Vec3::new(3f32, 4f32, 5f32);
    /// let ray = Ray::new(Vec3::from_scalar(1f32), Vec3::new(0.5f32, 0f32, 0f32)).unwrap();
    /// let dist = vec.shortest_distance_to(ray);
    /// assert_eq!(dist, ((9 + 16) as f32).sqrt());
    /// ```
    pub fn shortest_distance_to(&self, ray: Ray) -> f32 {
        let u = *self - ray.origin;
        let squared = u.cross(ray.direction()).square_length(); // Supposed to be positive.
        squared.sqrt()
    }

    /// Convert into [Vec4] as a homogeneous coordinate.
    ///
    /// See <https://en.wikipedia.org/wiki/Homogeneous_coordinates>
    /// to know what homogeneous coordinate is.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Vec3, Vec4};
    ///
    /// let vec3 = Vec3::new(0f32, 2f32, 3f32);
    /// let homo = vec3.to_homogeneous();
    /// assert_eq!(homo, Vec4::new(0f32, 2f32, 3f32, 1f32));
    /// ```
    pub fn to_homogeneous(&self) -> Vec4 {
        Vec4::new(self.arr[0], self.arr[1], self.arr[2], 1f32)
    }

    /// Rotate this [Vec3] about [Quat] which has rotation data.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Vec3, Quat, Degree, NearlyEqual};
    ///
    /// let quat = Quat::from_degrees(Degree(0f32), Degree(45f32), Degree(0f32));
    /// let src = Vec3::new(0f32, 0f32, 2f32);
    /// let dst = src.rotated_about_quat(quat);
    ///
    /// assert!(dst.x().nearly_equal(2f32.sqrt(), 1e-3));
    /// assert!(dst.y().nearly_equal(0f32, 1e-3));
    /// assert!(dst.z().nearly_equal(2f32.sqrt(), 1e-3));
    /// ```
    pub fn rotated_about_quat(&self, quat: Quat) -> Self {
        let w = quat.w();
        let vecpart = Self::new(quat.x(), quat.y(), quat.z());
        let b2 = vecpart.square_length();

        // Result
        (self * ((w * w) - b2))
            + (vecpart * (self.dot(vecpart) * 2f32))
            + (vecpart.cross(*self) * (w * 2f32))
    }

    /// Get new [Vec3] contains each minimum elements of `self` and given `points` [Vec3] list.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Vec3;
    ///
    /// let vec = Vec3::from_scalar(0f32);
    /// let new = vec.min_elements_with(&[
    ///     Vec3::new(0f32, -3f32, 4f32),
    ///     Vec3::new(1f32, 2f32, 6f32),
    ///     Vec3::new(-16f32, 8f32, -7f32)]);
    /// assert_eq!(new, Vec3::new(-16f32, -3f32, -7f32));
    ///
    /// let same = new.min_elements_with(&[]);
    /// assert_eq!(new, same);
    /// ```
    pub fn min_elements_with(&self, points: &[Self]) -> Self {
        points.iter().fold(*self, |prev, point| {
            Self::new(
                point[0].min(prev[0]),
                point[1].min(prev[1]),
                point[2].min(prev[2]),
            )
        })
    }

    /// Get new [Vec3] contains each maximum elements of `self` and given `points` [Vec3] list.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Vec3;
    ///
    /// let vec = Vec3::from_scalar(0f32);
    /// let new = vec.max_elements_with(&[
    ///     Vec3::new(0f32, -3f32, 4f32),
    ///     Vec3::new(1f32, 2f32, 6f32),
    ///     Vec3::new(-16f32, 8f32, -7f32)]);
    /// assert_eq!(new, Vec3::new(1f32, 8f32, 6f32));
    ///
    /// let same = new.max_elements_with(&[]);
    /// assert_eq!(new, same);
    /// ```
    pub fn max_elements_with(&self, points: &[Self]) -> Self {
        points.iter().fold(*self, |prev, point| {
            Self::new(
                point[0].max(prev[0]),
                point[1].max(prev[1]),
                point[2].max(prev[2]),
            )
        })
    }
}

impl Default for Vec3 {
    /// Create zero vector.
    fn default() -> Self {
        Self::new(0f32, 0f32, 0f32)
    }
}

impl PartialEq for Vec3 {
    fn eq(&self, other: &Self) -> bool {
        self.arr[0] == other.arr[0] && self.arr[1] == other.arr[1] && self.arr[2] == other.arr[2]
    }
}

impl From<FitVec3> for Vec3 {
    fn from(vec: FitVec3) -> Self {
        Self::from_array(vec.arr)
    }
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
    fn index(&self, index: usize) -> &Self::Output {
        &self.arr[index]
    }
}

impl IndexMut<usize> for Vec3 {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.arr[index]
    }
}

op_binary_impl!(Vec3, Add, add, +, 0 1 2 3);
op_binary_impl!(Vec3, Sub, sub, -, 0 1 2 3);
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
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Vec3::default(), |a, b| a + b)
    }
}

impl<'a> iter::Sum<&'a Vec3> for Vec3 {
    fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(Vec3::default(), |a, b| a + b)
    }
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

// ----------------------------------------------------------------------------
//
// VEC3 SWIZZLINGS
//
// ----------------------------------------------------------------------------

impl Vec3 {
    pub fn swizzle_00(&self) -> Vec2 {
        Vec2::new(0f32, 0f32)
    }
    pub fn swizzle_0x(&self) -> Vec2 {
        Vec2::new(0f32, self.x())
    }
    pub fn swizzle_0y(&self) -> Vec2 {
        Vec2::new(0f32, self.y())
    }
    pub fn swizzle_0z(&self) -> Vec2 {
        Vec2::new(0f32, self.z())
    }

    pub fn swizzle_x0(&self) -> Vec2 {
        Vec2::new(self.x(), 0f32)
    }
    pub fn swizzle_xx(&self) -> Vec2 {
        Vec2::new(self.x(), self.x())
    }
    pub fn swizzle_xy(&self) -> Vec2 {
        Vec2::new(self.x(), self.y())
    }
    pub fn swizzle_xz(&self) -> Vec2 {
        Vec2::new(self.x(), self.z())
    }

    pub fn swizzle_y0(&self) -> Vec2 {
        Vec2::new(self.y(), 0f32)
    }
    pub fn swizzle_yx(&self) -> Vec2 {
        Vec2::new(self.y(), self.x())
    }
    pub fn swizzle_yy(&self) -> Vec2 {
        Vec2::new(self.y(), self.y())
    }
    pub fn swizzle_yz(&self) -> Vec2 {
        Vec2::new(self.y(), self.z())
    }

    pub fn swizzle_z0(&self) -> Vec2 {
        Vec2::new(self.z(), 0f32)
    }
    pub fn swizzle_zx(&self) -> Vec2 {
        Vec2::new(self.z(), self.x())
    }
    pub fn swizzle_zy(&self) -> Vec2 {
        Vec2::new(self.z(), self.y())
    }
    pub fn swizzle_zz(&self) -> Vec2 {
        Vec2::new(self.z(), self.z())
    }
}

impl Vec3 {
    pub fn swizzle_000(&self) -> Self {
        Self::new(0f32, 0f32, 0f32)
    }
    pub fn swizzle_00x(&self) -> Self {
        Self::new(0f32, 0f32, self.x())
    }
    pub fn swizzle_00y(&self) -> Self {
        Self::new(0f32, 0f32, self.y())
    }
    pub fn swizzle_00z(&self) -> Self {
        Self::new(0f32, 0f32, self.z())
    }

    pub fn swizzle_0x0(&self) -> Self {
        Self::new(0f32, self.x(), 0f32)
    }
    pub fn swizzle_0xx(&self) -> Self {
        Self::new(0f32, self.x(), self.x())
    }
    pub fn swizzle_0xy(&self) -> Self {
        Self::new(0f32, self.x(), self.y())
    }
    pub fn swizzle_0xz(&self) -> Self {
        Self::new(0f32, self.x(), self.z())
    }

    pub fn swizzle_0y0(&self) -> Self {
        Self::new(0f32, self.y(), 0f32)
    }
    pub fn swizzle_0yx(&self) -> Self {
        Self::new(0f32, self.y(), self.x())
    }
    pub fn swizzle_0yy(&self) -> Self {
        Self::new(0f32, self.y(), self.y())
    }
    pub fn swizzle_0yz(&self) -> Self {
        Self::new(0f32, self.y(), self.z())
    }

    pub fn swizzle_0z0(&self) -> Self {
        Self::new(0f32, self.z(), 0f32)
    }
    pub fn swizzle_0zx(&self) -> Self {
        Self::new(0f32, self.z(), self.x())
    }
    pub fn swizzle_0zy(&self) -> Self {
        Self::new(0f32, self.z(), self.y())
    }
    pub fn swizzle_0zz(&self) -> Self {
        Self::new(0f32, self.z(), self.z())
    }

    pub fn swizzle_x00(&self) -> Self {
        Self::new(self.x(), 0f32, 0f32)
    }
    pub fn swizzle_x0x(&self) -> Self {
        Self::new(self.x(), 0f32, self.x())
    }
    pub fn swizzle_x0y(&self) -> Self {
        Self::new(self.x(), 0f32, self.y())
    }
    pub fn swizzle_x0z(&self) -> Self {
        Self::new(self.x(), 0f32, self.z())
    }

    pub fn swizzle_xx0(&self) -> Self {
        Self::new(self.x(), self.x(), 0f32)
    }
    pub fn swizzle_xxx(&self) -> Self {
        Self::new(self.x(), self.x(), self.x())
    }
    pub fn swizzle_xxy(&self) -> Self {
        Self::new(self.x(), self.x(), self.y())
    }
    pub fn swizzle_xxz(&self) -> Self {
        Self::new(self.x(), self.x(), self.z())
    }

    pub fn swizzle_xy0(&self) -> Self {
        Self::new(self.x(), self.y(), 0f32)
    }
    pub fn swizzle_xyx(&self) -> Self {
        Self::new(self.x(), self.y(), self.x())
    }
    pub fn swizzle_xyy(&self) -> Self {
        Self::new(self.x(), self.y(), self.y())
    }
    pub fn swizzle_xyz(&self) -> Self {
        Self::new(self.x(), self.y(), self.z())
    }

    pub fn swizzle_xz0(&self) -> Self {
        Self::new(self.x(), self.z(), 0f32)
    }
    pub fn swizzle_xzx(&self) -> Self {
        Self::new(self.x(), self.z(), self.x())
    }
    pub fn swizzle_xzy(&self) -> Self {
        Self::new(self.x(), self.z(), self.y())
    }
    pub fn swizzle_xzz(&self) -> Self {
        Self::new(self.x(), self.z(), self.z())
    }

    pub fn swizzle_y00(&self) -> Self {
        Self::new(self.y(), 0f32, 0f32)
    }
    pub fn swizzle_y0x(&self) -> Self {
        Self::new(self.y(), 0f32, self.x())
    }
    pub fn swizzle_y0y(&self) -> Self {
        Self::new(self.y(), 0f32, self.y())
    }
    pub fn swizzle_y0z(&self) -> Self {
        Self::new(self.y(), 0f32, self.z())
    }

    pub fn swizzle_yx0(&self) -> Self {
        Self::new(self.y(), self.x(), 0f32)
    }
    pub fn swizzle_yxx(&self) -> Self {
        Self::new(self.y(), self.x(), self.x())
    }
    pub fn swizzle_yxy(&self) -> Self {
        Self::new(self.y(), self.x(), self.y())
    }
    pub fn swizzle_yxz(&self) -> Self {
        Self::new(self.y(), self.x(), self.z())
    }

    pub fn swizzle_yy0(&self) -> Self {
        Self::new(self.y(), self.y(), 0f32)
    }
    pub fn swizzle_yyx(&self) -> Self {
        Self::new(self.y(), self.y(), self.x())
    }
    pub fn swizzle_yyy(&self) -> Self {
        Self::new(self.y(), self.y(), self.y())
    }
    pub fn swizzle_yyz(&self) -> Self {
        Self::new(self.y(), self.y(), self.z())
    }

    pub fn swizzle_yz0(&self) -> Self {
        Self::new(self.y(), self.z(), 0f32)
    }
    pub fn swizzle_yzx(&self) -> Self {
        Self::new(self.y(), self.z(), self.x())
    }
    pub fn swizzle_yzy(&self) -> Self {
        Self::new(self.y(), self.z(), self.y())
    }
    pub fn swizzle_yzz(&self) -> Self {
        Self::new(self.y(), self.z(), self.z())
    }

    pub fn swizzle_z00(&self) -> Self {
        Self::new(self.z(), 0f32, 0f32)
    }
    pub fn swizzle_z0x(&self) -> Self {
        Self::new(self.z(), 0f32, self.x())
    }
    pub fn swizzle_z0y(&self) -> Self {
        Self::new(self.z(), 0f32, self.y())
    }
    pub fn swizzle_z0z(&self) -> Self {
        Self::new(self.z(), 0f32, self.z())
    }

    pub fn swizzle_zx0(&self) -> Self {
        Self::new(self.z(), self.x(), 0f32)
    }
    pub fn swizzle_zxx(&self) -> Self {
        Self::new(self.z(), self.x(), self.x())
    }
    pub fn swizzle_zxy(&self) -> Self {
        Self::new(self.z(), self.x(), self.y())
    }
    pub fn swizzle_zxz(&self) -> Self {
        Self::new(self.z(), self.x(), self.z())
    }

    pub fn swizzle_zy0(&self) -> Self {
        Self::new(self.z(), self.y(), 0f32)
    }
    pub fn swizzle_zyx(&self) -> Self {
        Self::new(self.z(), self.y(), self.x())
    }
    pub fn swizzle_zyy(&self) -> Self {
        Self::new(self.z(), self.y(), self.y())
    }
    pub fn swizzle_zyz(&self) -> Self {
        Self::new(self.z(), self.y(), self.z())
    }

    pub fn swizzle_zz0(&self) -> Self {
        Self::new(self.z(), self.z(), 0f32)
    }
    pub fn swizzle_zzx(&self) -> Self {
        Self::new(self.z(), self.z(), self.x())
    }
    pub fn swizzle_zzy(&self) -> Self {
        Self::new(self.z(), self.z(), self.y())
    }
    pub fn swizzle_zzz(&self) -> Self {
        Self::new(self.z(), self.z(), self.z())
    }
}

impl Vec3 {
    pub fn swizzle_0000(&self) -> Vec4 {
        Vec4::new(0f32, 0f32, 0f32, 0f32)
    }
    pub fn swizzle_000x(&self) -> Vec4 {
        Vec4::new(0f32, 0f32, 0f32, self.x())
    }
    pub fn swizzle_000y(&self) -> Vec4 {
        Vec4::new(0f32, 0f32, 0f32, self.y())
    }
    pub fn swizzle_000z(&self) -> Vec4 {
        Vec4::new(0f32, 0f32, 0f32, self.z())
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
    pub fn swizzle_00xz(&self) -> Vec4 {
        Vec4::new(0f32, 0f32, self.x(), self.z())
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
    pub fn swizzle_00yz(&self) -> Vec4 {
        Vec4::new(0f32, 0f32, self.y(), self.z())
    }

    pub fn swizzle_00z0(&self) -> Vec4 {
        Vec4::new(0f32, 0f32, self.z(), 0f32)
    }
    pub fn swizzle_00zx(&self) -> Vec4 {
        Vec4::new(0f32, 0f32, self.z(), self.x())
    }
    pub fn swizzle_00zy(&self) -> Vec4 {
        Vec4::new(0f32, 0f32, self.z(), self.y())
    }
    pub fn swizzle_00zz(&self) -> Vec4 {
        Vec4::new(0f32, 0f32, self.z(), self.z())
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
    pub fn swizzle_0x0z(&self) -> Vec4 {
        Vec4::new(0f32, self.x(), 0f32, self.z())
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
    pub fn swizzle_0xxz(&self) -> Vec4 {
        Vec4::new(0f32, self.x(), self.x(), self.z())
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
    pub fn swizzle_0xyz(&self) -> Vec4 {
        Vec4::new(0f32, self.x(), self.y(), self.z())
    }

    pub fn swizzle_0xz0(&self) -> Vec4 {
        Vec4::new(0f32, self.x(), self.z(), 0f32)
    }
    pub fn swizzle_0xzx(&self) -> Vec4 {
        Vec4::new(0f32, self.x(), self.z(), self.x())
    }
    pub fn swizzle_0xzy(&self) -> Vec4 {
        Vec4::new(0f32, self.x(), self.z(), self.y())
    }
    pub fn swizzle_0xzz(&self) -> Vec4 {
        Vec4::new(0f32, self.x(), self.z(), self.z())
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
    pub fn swizzle_0y0z(&self) -> Vec4 {
        Vec4::new(0f32, self.y(), 0f32, self.z())
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
    pub fn swizzle_0yxz(&self) -> Vec4 {
        Vec4::new(0f32, self.y(), self.x(), self.z())
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
    pub fn swizzle_0yyz(&self) -> Vec4 {
        Vec4::new(0f32, self.y(), self.y(), self.z())
    }

    pub fn swizzle_0yz0(&self) -> Vec4 {
        Vec4::new(0f32, self.y(), self.z(), 0f32)
    }
    pub fn swizzle_0yzx(&self) -> Vec4 {
        Vec4::new(0f32, self.y(), self.z(), self.x())
    }
    pub fn swizzle_0yzy(&self) -> Vec4 {
        Vec4::new(0f32, self.y(), self.z(), self.y())
    }
    pub fn swizzle_0yzz(&self) -> Vec4 {
        Vec4::new(0f32, self.y(), self.z(), self.z())
    }

    pub fn swizzle_0z00(&self) -> Vec4 {
        Vec4::new(0f32, self.z(), 0f32, 0f32)
    }
    pub fn swizzle_0z0x(&self) -> Vec4 {
        Vec4::new(0f32, self.z(), 0f32, self.x())
    }
    pub fn swizzle_0z0y(&self) -> Vec4 {
        Vec4::new(0f32, self.z(), 0f32, self.y())
    }
    pub fn swizzle_0z0z(&self) -> Vec4 {
        Vec4::new(0f32, self.z(), 0f32, self.z())
    }

    pub fn swizzle_0zx0(&self) -> Vec4 {
        Vec4::new(0f32, self.z(), self.x(), 0f32)
    }
    pub fn swizzle_0zxx(&self) -> Vec4 {
        Vec4::new(0f32, self.z(), self.x(), self.x())
    }
    pub fn swizzle_0zxy(&self) -> Vec4 {
        Vec4::new(0f32, self.z(), self.x(), self.y())
    }
    pub fn swizzle_0zxz(&self) -> Vec4 {
        Vec4::new(0f32, self.z(), self.x(), self.z())
    }

    pub fn swizzle_0zy0(&self) -> Vec4 {
        Vec4::new(0f32, self.z(), self.y(), 0f32)
    }
    pub fn swizzle_0zyx(&self) -> Vec4 {
        Vec4::new(0f32, self.z(), self.y(), self.x())
    }
    pub fn swizzle_0zyy(&self) -> Vec4 {
        Vec4::new(0f32, self.z(), self.y(), self.y())
    }
    pub fn swizzle_0zyz(&self) -> Vec4 {
        Vec4::new(0f32, self.z(), self.y(), self.z())
    }

    pub fn swizzle_0zz0(&self) -> Vec4 {
        Vec4::new(0f32, self.z(), self.z(), 0f32)
    }
    pub fn swizzle_0zzx(&self) -> Vec4 {
        Vec4::new(0f32, self.z(), self.z(), self.x())
    }
    pub fn swizzle_0zzy(&self) -> Vec4 {
        Vec4::new(0f32, self.z(), self.z(), self.y())
    }
    pub fn swizzle_0zzz(&self) -> Vec4 {
        Vec4::new(0f32, self.z(), self.z(), self.z())
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
    pub fn swizzle_x00z(&self) -> Vec4 {
        Vec4::new(self.x(), 0f32, 0f32, self.z())
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
    pub fn swizzle_x0xz(&self) -> Vec4 {
        Vec4::new(self.x(), 0f32, self.x(), self.z())
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
    pub fn swizzle_x0yz(&self) -> Vec4 {
        Vec4::new(self.x(), 0f32, self.y(), self.z())
    }

    pub fn swizzle_x0z0(&self) -> Vec4 {
        Vec4::new(self.x(), 0f32, self.z(), 0f32)
    }
    pub fn swizzle_x0zx(&self) -> Vec4 {
        Vec4::new(self.x(), 0f32, self.z(), self.x())
    }
    pub fn swizzle_x0zy(&self) -> Vec4 {
        Vec4::new(self.x(), 0f32, self.z(), self.y())
    }
    pub fn swizzle_x0zz(&self) -> Vec4 {
        Vec4::new(self.x(), 0f32, self.z(), self.z())
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
    pub fn swizzle_xx0z(&self) -> Vec4 {
        Vec4::new(self.x(), self.x(), 0f32, self.z())
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
    pub fn swizzle_xxxz(&self) -> Vec4 {
        Vec4::new(self.x(), self.x(), self.x(), self.z())
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
    pub fn swizzle_xxyz(&self) -> Vec4 {
        Vec4::new(self.x(), self.x(), self.y(), self.z())
    }

    pub fn swizzle_xxz0(&self) -> Vec4 {
        Vec4::new(self.x(), self.x(), self.z(), 0f32)
    }
    pub fn swizzle_xxzx(&self) -> Vec4 {
        Vec4::new(self.x(), self.x(), self.z(), self.x())
    }
    pub fn swizzle_xxzy(&self) -> Vec4 {
        Vec4::new(self.x(), self.x(), self.z(), self.y())
    }
    pub fn swizzle_xxzz(&self) -> Vec4 {
        Vec4::new(self.x(), self.x(), self.z(), self.z())
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
    pub fn swizzle_xy0z(&self) -> Vec4 {
        Vec4::new(self.x(), self.y(), 0f32, self.z())
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
    pub fn swizzle_xyxz(&self) -> Vec4 {
        Vec4::new(self.x(), self.y(), self.x(), self.z())
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
    pub fn swizzle_xyyz(&self) -> Vec4 {
        Vec4::new(self.x(), self.y(), self.y(), self.z())
    }

    pub fn swizzle_xyz0(&self) -> Vec4 {
        Vec4::new(self.x(), self.y(), self.z(), 0f32)
    }
    pub fn swizzle_xyzx(&self) -> Vec4 {
        Vec4::new(self.x(), self.y(), self.z(), self.x())
    }
    pub fn swizzle_xyzy(&self) -> Vec4 {
        Vec4::new(self.x(), self.y(), self.z(), self.y())
    }
    pub fn swizzle_xyzz(&self) -> Vec4 {
        Vec4::new(self.x(), self.y(), self.z(), self.z())
    }

    pub fn swizzle_xz00(&self) -> Vec4 {
        Vec4::new(self.x(), self.z(), 0f32, 0f32)
    }
    pub fn swizzle_xz0x(&self) -> Vec4 {
        Vec4::new(self.x(), self.z(), 0f32, self.x())
    }
    pub fn swizzle_xz0y(&self) -> Vec4 {
        Vec4::new(self.x(), self.z(), 0f32, self.y())
    }
    pub fn swizzle_xz0z(&self) -> Vec4 {
        Vec4::new(self.x(), self.z(), 0f32, self.z())
    }

    pub fn swizzle_xzx0(&self) -> Vec4 {
        Vec4::new(self.x(), self.z(), self.x(), 0f32)
    }
    pub fn swizzle_xzxx(&self) -> Vec4 {
        Vec4::new(self.x(), self.z(), self.x(), self.x())
    }
    pub fn swizzle_xzxy(&self) -> Vec4 {
        Vec4::new(self.x(), self.z(), self.x(), self.y())
    }
    pub fn swizzle_xzxz(&self) -> Vec4 {
        Vec4::new(self.x(), self.z(), self.x(), self.z())
    }

    pub fn swizzle_xzy0(&self) -> Vec4 {
        Vec4::new(self.x(), self.z(), self.y(), 0f32)
    }
    pub fn swizzle_xzyx(&self) -> Vec4 {
        Vec4::new(self.x(), self.z(), self.y(), self.x())
    }
    pub fn swizzle_xzyy(&self) -> Vec4 {
        Vec4::new(self.x(), self.z(), self.y(), self.y())
    }
    pub fn swizzle_xzyz(&self) -> Vec4 {
        Vec4::new(self.x(), self.z(), self.y(), self.z())
    }

    pub fn swizzle_xzz0(&self) -> Vec4 {
        Vec4::new(self.x(), self.z(), self.z(), 0f32)
    }
    pub fn swizzle_xzzx(&self) -> Vec4 {
        Vec4::new(self.x(), self.z(), self.z(), self.x())
    }
    pub fn swizzle_xzzy(&self) -> Vec4 {
        Vec4::new(self.x(), self.z(), self.z(), self.y())
    }
    pub fn swizzle_xzzz(&self) -> Vec4 {
        Vec4::new(self.x(), self.z(), self.z(), self.z())
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
    pub fn swizzle_y00z(&self) -> Vec4 {
        Vec4::new(self.y(), 0f32, 0f32, self.z())
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
    pub fn swizzle_y0xz(&self) -> Vec4 {
        Vec4::new(self.y(), 0f32, self.x(), self.z())
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
    pub fn swizzle_y0yz(&self) -> Vec4 {
        Vec4::new(self.y(), 0f32, self.y(), self.z())
    }

    pub fn swizzle_y0z0(&self) -> Vec4 {
        Vec4::new(self.y(), 0f32, self.z(), 0f32)
    }
    pub fn swizzle_y0zx(&self) -> Vec4 {
        Vec4::new(self.y(), 0f32, self.z(), self.x())
    }
    pub fn swizzle_y0zy(&self) -> Vec4 {
        Vec4::new(self.y(), 0f32, self.z(), self.y())
    }
    pub fn swizzle_y0zz(&self) -> Vec4 {
        Vec4::new(self.y(), 0f32, self.z(), self.z())
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
    pub fn swizzle_yx0z(&self) -> Vec4 {
        Vec4::new(self.y(), self.x(), 0f32, self.z())
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
    pub fn swizzle_yxxz(&self) -> Vec4 {
        Vec4::new(self.y(), self.x(), self.x(), self.z())
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
    pub fn swizzle_yxyz(&self) -> Vec4 {
        Vec4::new(self.y(), self.x(), self.y(), self.z())
    }

    pub fn swizzle_yxz0(&self) -> Vec4 {
        Vec4::new(self.y(), self.x(), self.z(), 0f32)
    }
    pub fn swizzle_yxzx(&self) -> Vec4 {
        Vec4::new(self.y(), self.x(), self.z(), self.x())
    }
    pub fn swizzle_yxzy(&self) -> Vec4 {
        Vec4::new(self.y(), self.x(), self.z(), self.y())
    }
    pub fn swizzle_yxzz(&self) -> Vec4 {
        Vec4::new(self.y(), self.x(), self.z(), self.z())
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
    pub fn swizzle_yy0z(&self) -> Vec4 {
        Vec4::new(self.y(), self.y(), 0f32, self.z())
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
    pub fn swizzle_yyxz(&self) -> Vec4 {
        Vec4::new(self.y(), self.y(), self.x(), self.z())
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
    pub fn swizzle_yyyz(&self) -> Vec4 {
        Vec4::new(self.y(), self.y(), self.y(), self.z())
    }

    pub fn swizzle_yyz0(&self) -> Vec4 {
        Vec4::new(self.y(), self.y(), self.z(), 0f32)
    }
    pub fn swizzle_yyzx(&self) -> Vec4 {
        Vec4::new(self.y(), self.y(), self.z(), self.x())
    }
    pub fn swizzle_yyzy(&self) -> Vec4 {
        Vec4::new(self.y(), self.y(), self.z(), self.y())
    }
    pub fn swizzle_yyzz(&self) -> Vec4 {
        Vec4::new(self.y(), self.y(), self.z(), self.z())
    }

    pub fn swizzle_yz00(&self) -> Vec4 {
        Vec4::new(self.y(), self.z(), 0f32, 0f32)
    }
    pub fn swizzle_yz0x(&self) -> Vec4 {
        Vec4::new(self.y(), self.z(), 0f32, self.x())
    }
    pub fn swizzle_yz0y(&self) -> Vec4 {
        Vec4::new(self.y(), self.z(), 0f32, self.y())
    }
    pub fn swizzle_yz0z(&self) -> Vec4 {
        Vec4::new(self.y(), self.z(), 0f32, self.z())
    }

    pub fn swizzle_yzx0(&self) -> Vec4 {
        Vec4::new(self.y(), self.z(), self.x(), 0f32)
    }
    pub fn swizzle_yzxx(&self) -> Vec4 {
        Vec4::new(self.y(), self.z(), self.x(), self.x())
    }
    pub fn swizzle_yzxy(&self) -> Vec4 {
        Vec4::new(self.y(), self.z(), self.x(), self.y())
    }
    pub fn swizzle_yzxz(&self) -> Vec4 {
        Vec4::new(self.y(), self.z(), self.x(), self.z())
    }

    pub fn swizzle_yzy0(&self) -> Vec4 {
        Vec4::new(self.y(), self.z(), self.y(), 0f32)
    }
    pub fn swizzle_yzyx(&self) -> Vec4 {
        Vec4::new(self.y(), self.z(), self.y(), self.x())
    }
    pub fn swizzle_yzyy(&self) -> Vec4 {
        Vec4::new(self.y(), self.z(), self.y(), self.y())
    }
    pub fn swizzle_yzyz(&self) -> Vec4 {
        Vec4::new(self.y(), self.z(), self.y(), self.z())
    }

    pub fn swizzle_yzz0(&self) -> Vec4 {
        Vec4::new(self.y(), self.z(), self.z(), 0f32)
    }
    pub fn swizzle_yzzx(&self) -> Vec4 {
        Vec4::new(self.y(), self.z(), self.z(), self.x())
    }
    pub fn swizzle_yzzy(&self) -> Vec4 {
        Vec4::new(self.y(), self.z(), self.z(), self.y())
    }
    pub fn swizzle_yzzz(&self) -> Vec4 {
        Vec4::new(self.y(), self.z(), self.z(), self.z())
    }

    pub fn swizzle_z000(&self) -> Vec4 {
        Vec4::new(self.z(), 0f32, 0f32, 0f32)
    }
    pub fn swizzle_z00x(&self) -> Vec4 {
        Vec4::new(self.z(), 0f32, 0f32, self.x())
    }
    pub fn swizzle_z00y(&self) -> Vec4 {
        Vec4::new(self.z(), 0f32, 0f32, self.y())
    }
    pub fn swizzle_z00z(&self) -> Vec4 {
        Vec4::new(self.z(), 0f32, 0f32, self.z())
    }

    pub fn swizzle_z0x0(&self) -> Vec4 {
        Vec4::new(self.z(), 0f32, self.x(), 0f32)
    }
    pub fn swizzle_z0xx(&self) -> Vec4 {
        Vec4::new(self.z(), 0f32, self.x(), self.x())
    }
    pub fn swizzle_z0xy(&self) -> Vec4 {
        Vec4::new(self.z(), 0f32, self.x(), self.y())
    }
    pub fn swizzle_z0xz(&self) -> Vec4 {
        Vec4::new(self.z(), 0f32, self.x(), self.z())
    }

    pub fn swizzle_z0y0(&self) -> Vec4 {
        Vec4::new(self.z(), 0f32, self.y(), 0f32)
    }
    pub fn swizzle_z0yx(&self) -> Vec4 {
        Vec4::new(self.z(), 0f32, self.y(), self.x())
    }
    pub fn swizzle_z0yy(&self) -> Vec4 {
        Vec4::new(self.z(), 0f32, self.y(), self.y())
    }
    pub fn swizzle_z0yz(&self) -> Vec4 {
        Vec4::new(self.z(), 0f32, self.y(), self.z())
    }

    pub fn swizzle_z0z0(&self) -> Vec4 {
        Vec4::new(self.z(), 0f32, self.z(), 0f32)
    }
    pub fn swizzle_z0zx(&self) -> Vec4 {
        Vec4::new(self.z(), 0f32, self.z(), self.x())
    }
    pub fn swizzle_z0zy(&self) -> Vec4 {
        Vec4::new(self.z(), 0f32, self.z(), self.y())
    }
    pub fn swizzle_z0zz(&self) -> Vec4 {
        Vec4::new(self.z(), 0f32, self.z(), self.z())
    }

    pub fn swizzle_zx00(&self) -> Vec4 {
        Vec4::new(self.z(), self.x(), 0f32, 0f32)
    }
    pub fn swizzle_zx0x(&self) -> Vec4 {
        Vec4::new(self.z(), self.x(), 0f32, self.x())
    }
    pub fn swizzle_zx0y(&self) -> Vec4 {
        Vec4::new(self.z(), self.x(), 0f32, self.y())
    }
    pub fn swizzle_zx0z(&self) -> Vec4 {
        Vec4::new(self.z(), self.x(), 0f32, self.z())
    }

    pub fn swizzle_zxx0(&self) -> Vec4 {
        Vec4::new(self.z(), self.x(), self.x(), 0f32)
    }
    pub fn swizzle_zxxx(&self) -> Vec4 {
        Vec4::new(self.z(), self.x(), self.x(), self.x())
    }
    pub fn swizzle_zxxy(&self) -> Vec4 {
        Vec4::new(self.z(), self.x(), self.x(), self.y())
    }
    pub fn swizzle_zxxz(&self) -> Vec4 {
        Vec4::new(self.z(), self.x(), self.x(), self.z())
    }

    pub fn swizzle_zxy0(&self) -> Vec4 {
        Vec4::new(self.z(), self.x(), self.y(), 0f32)
    }
    pub fn swizzle_zxyx(&self) -> Vec4 {
        Vec4::new(self.z(), self.x(), self.y(), self.x())
    }
    pub fn swizzle_zxyy(&self) -> Vec4 {
        Vec4::new(self.z(), self.x(), self.y(), self.y())
    }
    pub fn swizzle_zxyz(&self) -> Vec4 {
        Vec4::new(self.z(), self.x(), self.y(), self.z())
    }

    pub fn swizzle_zxz0(&self) -> Vec4 {
        Vec4::new(self.z(), self.x(), self.z(), 0f32)
    }
    pub fn swizzle_zxzx(&self) -> Vec4 {
        Vec4::new(self.z(), self.x(), self.z(), self.x())
    }
    pub fn swizzle_zxzy(&self) -> Vec4 {
        Vec4::new(self.z(), self.x(), self.z(), self.y())
    }
    pub fn swizzle_zxzz(&self) -> Vec4 {
        Vec4::new(self.z(), self.x(), self.z(), self.z())
    }

    pub fn swizzle_zy00(&self) -> Vec4 {
        Vec4::new(self.z(), self.y(), 0f32, 0f32)
    }
    pub fn swizzle_zy0x(&self) -> Vec4 {
        Vec4::new(self.z(), self.y(), 0f32, self.x())
    }
    pub fn swizzle_zy0y(&self) -> Vec4 {
        Vec4::new(self.z(), self.y(), 0f32, self.y())
    }
    pub fn swizzle_zy0z(&self) -> Vec4 {
        Vec4::new(self.z(), self.y(), 0f32, self.z())
    }

    pub fn swizzle_zyx0(&self) -> Vec4 {
        Vec4::new(self.z(), self.y(), self.x(), 0f32)
    }
    pub fn swizzle_zyxx(&self) -> Vec4 {
        Vec4::new(self.z(), self.y(), self.x(), self.x())
    }
    pub fn swizzle_zyxy(&self) -> Vec4 {
        Vec4::new(self.z(), self.y(), self.x(), self.y())
    }
    pub fn swizzle_zyxz(&self) -> Vec4 {
        Vec4::new(self.z(), self.y(), self.x(), self.z())
    }

    pub fn swizzle_zyy0(&self) -> Vec4 {
        Vec4::new(self.z(), self.y(), self.y(), 0f32)
    }
    pub fn swizzle_zyyx(&self) -> Vec4 {
        Vec4::new(self.z(), self.y(), self.y(), self.x())
    }
    pub fn swizzle_zyyy(&self) -> Vec4 {
        Vec4::new(self.z(), self.y(), self.y(), self.y())
    }
    pub fn swizzle_zyyz(&self) -> Vec4 {
        Vec4::new(self.z(), self.y(), self.y(), self.z())
    }

    pub fn swizzle_zyz0(&self) -> Vec4 {
        Vec4::new(self.z(), self.y(), self.z(), 0f32)
    }
    pub fn swizzle_zyzx(&self) -> Vec4 {
        Vec4::new(self.z(), self.y(), self.z(), self.x())
    }
    pub fn swizzle_zyzy(&self) -> Vec4 {
        Vec4::new(self.z(), self.y(), self.z(), self.y())
    }
    pub fn swizzle_zyzz(&self) -> Vec4 {
        Vec4::new(self.z(), self.y(), self.z(), self.z())
    }

    pub fn swizzle_zz00(&self) -> Vec4 {
        Vec4::new(self.z(), self.z(), 0f32, 0f32)
    }
    pub fn swizzle_zz0x(&self) -> Vec4 {
        Vec4::new(self.z(), self.z(), 0f32, self.x())
    }
    pub fn swizzle_zz0y(&self) -> Vec4 {
        Vec4::new(self.z(), self.z(), 0f32, self.y())
    }
    pub fn swizzle_zz0z(&self) -> Vec4 {
        Vec4::new(self.z(), self.z(), 0f32, self.z())
    }

    pub fn swizzle_zzx0(&self) -> Vec4 {
        Vec4::new(self.z(), self.z(), self.x(), 0f32)
    }
    pub fn swizzle_zzxx(&self) -> Vec4 {
        Vec4::new(self.z(), self.z(), self.x(), self.x())
    }
    pub fn swizzle_zzxy(&self) -> Vec4 {
        Vec4::new(self.z(), self.z(), self.x(), self.y())
    }
    pub fn swizzle_zzxz(&self) -> Vec4 {
        Vec4::new(self.z(), self.z(), self.x(), self.z())
    }

    pub fn swizzle_zzy0(&self) -> Vec4 {
        Vec4::new(self.z(), self.z(), self.y(), 0f32)
    }
    pub fn swizzle_zzyx(&self) -> Vec4 {
        Vec4::new(self.z(), self.z(), self.y(), self.x())
    }
    pub fn swizzle_zzyy(&self) -> Vec4 {
        Vec4::new(self.z(), self.z(), self.y(), self.y())
    }
    pub fn swizzle_zzyz(&self) -> Vec4 {
        Vec4::new(self.z(), self.z(), self.y(), self.z())
    }

    pub fn swizzle_zzz0(&self) -> Vec4 {
        Vec4::new(self.z(), self.z(), self.z(), 0f32)
    }
    pub fn swizzle_zzzx(&self) -> Vec4 {
        Vec4::new(self.z(), self.z(), self.z(), self.x())
    }
    pub fn swizzle_zzzy(&self) -> Vec4 {
        Vec4::new(self.z(), self.z(), self.z(), self.y())
    }
    pub fn swizzle_zzzz(&self) -> Vec4 {
        Vec4::new(self.z(), self.z(), self.z(), self.z())
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
