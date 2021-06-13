use crate::{EError, Quat, Radian, Ray, Vec4};
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
    /// See [https://en.wikipedia.org/wiki/Homogeneous_coordinates]
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
