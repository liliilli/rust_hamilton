use crate::IVec2;
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
/// To get a actual vector which have only 3 elements inside, convert it into struct [FitIVec3].
///
/// # Examples
///
/// ```
/// use hamilton as math;
/// use math::IVec3;
///
/// let mut vec = IVec3::default();
/// assert_eq!(vec, IVec3::from_scalar(0));
/// ```
#[derive(Copy, Clone)]
pub struct IVec3 {
    arr: [i32; 4],
}

impl IVec3 {
    /// Create new [IVec3] value.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::IVec3;
    ///
    /// let vec = IVec3::new(6, 8, 10);
    /// assert_eq!(vec, IVec3::new(3, 4, 5) * 2i32);
    /// ```
    pub fn new(x: i32, y: i32, z: i32) -> Self {
        Self {
            arr: [x, y, z, 0i32],
        }
    }

    /// Create [IVec3] value filled with given scalar value `s`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::IVec3;
    ///
    /// let vec = IVec3::from_scalar(16);
    /// assert_eq!(vec, IVec3::from_scalar(8) * 2);
    /// ```
    pub fn from_scalar(s: i32) -> Self {
        Self {
            arr: [s, s, s, 0i32],
        }
    }

    /// Create new `IVec3` value from array that has 3 elements.
    pub fn from_array(arr: [i32; 3]) -> Self {
        Self {
            arr: [arr[0], arr[1], arr[2], 0i32],
        }
    }

    /// Get squared length of this vector from `(0, 0, 0)` origin.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::IVec3;
    ///
    /// let vec = IVec3::new(3i32, 4i32, 5i32);
    /// assert_eq!(vec.square_length(), 50i32);
    /// ```
    pub fn square_length(&self) -> i32 {
        self.arr.iter().fold(0i32, |sum, i| sum + i.pow(2))
    }

    /// Create x unit `(1, 0, 0)` vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::IVec3;
    ///
    /// assert_eq!(IVec3::new(1i32, 0i32, 0i32), IVec3::unit_x());
    /// ```
    pub fn unit_x() -> Self {
        Self::new(1i32, 0i32, 0i32)
    }

    /// Create y unit `(0, 1, 0)` vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::IVec3;
    ///
    /// assert_eq!(IVec3::new(0i32, 1i32, 0i32), IVec3::unit_y());
    /// ```
    pub fn unit_y() -> Self {
        Self::new(0i32, 1i32, 0i32)
    }

    /// Create z unit `(0, 0, 1)` vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::IVec3;
    ///
    /// assert_eq!(IVec3::new(0i32, 0i32, 1i32), IVec3::unit_z());
    /// ```
    pub fn unit_z() -> Self {
        Self::new(0i32, 0i32, 1i32)
    }

    /// Do dot product operation with other `rhs` [IVec3] value.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::IVec3;
    ///
    /// assert_eq!(IVec3::new(4i32, 3i32, 2i32).dot(IVec3::new(2i32, 3i32, 4i32)), 25i32);
    /// ```
    pub fn dot(&self, rhs: Self) -> i32 {
        (*self * rhs).arr.iter().sum()
    }

    /// Get new [IVec3] contains each minimum elements of `self` and given `points` [IVec3] list.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::IVec3;
    ///
    /// let vec = IVec3::from_scalar(0i32);
    /// let new = vec.min_elements_with(&[
    ///     IVec3::new(0i32, -3i32, 4i32),
    ///     IVec3::new(1i32, 2i32, 6i32),
    ///     IVec3::new(-16i32, 8i32, -7i32)]);
    /// assert_eq!(new, IVec3::new(-16i32, -3i32, -7i32));
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

    /// Get new [IVec3] contains each maximum elements of `self` and given `points` [IVec3] list.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::IVec3;
    ///
    /// let vec = IVec3::from_scalar(0i32);
    /// let new = vec.max_elements_with(&[
    ///     IVec3::new(0i32, -3i32, 4i32),
    ///     IVec3::new(1i32, 2i32, 6i32),
    ///     IVec3::new(-16i32, 8i32, -7i32)]);
    /// assert_eq!(new, IVec3::new(1i32, 8i32, 6i32));
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

    pub fn x(&self) -> i32 {
        self[0]
    }
    pub fn y(&self) -> i32 {
        self[1]
    }
    pub fn z(&self) -> i32 {
        self[2]
    }
}

impl Default for IVec3 {
    /// Create zero vector.
    fn default() -> Self {
        Self::new(0i32, 0i32, 0i32)
    }
}

impl PartialEq for IVec3 {
    fn eq(&self, other: &Self) -> bool {
        self.arr[0] == other.arr[0] && self.arr[1] == other.arr[1] && self.arr[2] == other.arr[2]
    }
}

impl From<FitIVec3> for IVec3 {
    fn from(vec: FitIVec3) -> Self {
        Self::from_array(vec.arr)
    }
}

impl Debug for IVec3 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "IVec3 {{x: {}, y: {}, z: {}}}",
            self.arr[0], self.arr[1], self.arr[2]
        )
    }
}

impl Index<usize> for IVec3 {
    type Output = i32;
    fn index(&self, index: usize) -> &Self::Output {
        &self.arr[index]
    }
}

impl IndexMut<usize> for IVec3 {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.arr[index]
    }
}

op_binary_impl!(IVec3, Add, add, +, 0 1 2 3);
op_binary_impl!(IVec3, Sub, sub, -, 0 1 2 3);
op_binary_impl!(IVec3, Mul, mul, *, 0 1 2 3);

op_scalar_impl!(IVec3, Add, add, +, i32);
op_scalar_impl!(IVec3, Sub, sub, -, i32);
op_scalar_impl!(IVec3, Mul, mul, *, i32);

op_assign_impl!(IVec3, AddAssign, add_assign, +=, 0 1 2 3);
op_assign_impl!(IVec3, SubAssign, sub_assign, -=, 0 1 2 3);
op_assign_impl!(IVec3, MulAssign, mul_assign, *=, 0 1 2 3);

op_assign_scalar_impl!(IVec3, AddAssign, add_assign, +=, i32);
op_assign_scalar_impl!(IVec3, SubAssign, sub_assign, -=, i32);
op_assign_scalar_impl!(IVec3, MulAssign, mul_assign, *=, i32);

impl iter::Sum for IVec3 {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(IVec3::default(), |a, b| a + b)
    }
}

impl<'a> iter::Sum<&'a IVec3> for IVec3 {
    fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(IVec3::default(), |a, b| a + b)
    }
}

/// Represent vector type but actually have only 3 elments unlike `IVec3`.
///
///
#[derive(Copy, Clone, Debug)]
pub struct FitIVec3 {
    arr: [i32; 3],
}

impl From<IVec3> for FitIVec3 {
    fn from(vec: IVec3) -> Self {
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

impl IVec3 {
    pub fn swizzle_00(&self) -> IVec2 {
        IVec2::new(0i32, 0i32)
    }
    pub fn swizzle_0x(&self) -> IVec2 {
        IVec2::new(0i32, self.x())
    }
    pub fn swizzle_0y(&self) -> IVec2 {
        IVec2::new(0i32, self.y())
    }
    pub fn swizzle_0z(&self) -> IVec2 {
        IVec2::new(0i32, self.z())
    }

    pub fn swizzle_x0(&self) -> IVec2 {
        IVec2::new(self.x(), 0i32)
    }
    pub fn swizzle_xx(&self) -> IVec2 {
        IVec2::new(self.x(), self.x())
    }
    pub fn swizzle_xy(&self) -> IVec2 {
        IVec2::new(self.x(), self.y())
    }
    pub fn swizzle_xz(&self) -> IVec2 {
        IVec2::new(self.x(), self.z())
    }

    pub fn swizzle_y0(&self) -> IVec2 {
        IVec2::new(self.y(), 0i32)
    }
    pub fn swizzle_yx(&self) -> IVec2 {
        IVec2::new(self.y(), self.x())
    }
    pub fn swizzle_yy(&self) -> IVec2 {
        IVec2::new(self.y(), self.y())
    }
    pub fn swizzle_yz(&self) -> IVec2 {
        IVec2::new(self.y(), self.z())
    }

    pub fn swizzle_z0(&self) -> IVec2 {
        IVec2::new(self.z(), 0i32)
    }
    pub fn swizzle_zx(&self) -> IVec2 {
        IVec2::new(self.z(), self.x())
    }
    pub fn swizzle_zy(&self) -> IVec2 {
        IVec2::new(self.z(), self.y())
    }
    pub fn swizzle_zz(&self) -> IVec2 {
        IVec2::new(self.z(), self.z())
    }
}

impl IVec3 {
    pub fn swizzle_000(&self) -> Self {
        Self::new(0i32, 0i32, 0i32)
    }
    pub fn swizzle_00x(&self) -> Self {
        Self::new(0i32, 0i32, self.x())
    }
    pub fn swizzle_00y(&self) -> Self {
        Self::new(0i32, 0i32, self.y())
    }
    pub fn swizzle_00z(&self) -> Self {
        Self::new(0i32, 0i32, self.z())
    }

    pub fn swizzle_0x0(&self) -> Self {
        Self::new(0i32, self.x(), 0i32)
    }
    pub fn swizzle_0xx(&self) -> Self {
        Self::new(0i32, self.x(), self.x())
    }
    pub fn swizzle_0xy(&self) -> Self {
        Self::new(0i32, self.x(), self.y())
    }
    pub fn swizzle_0xz(&self) -> Self {
        Self::new(0i32, self.x(), self.z())
    }

    pub fn swizzle_0y0(&self) -> Self {
        Self::new(0i32, self.y(), 0i32)
    }
    pub fn swizzle_0yx(&self) -> Self {
        Self::new(0i32, self.y(), self.x())
    }
    pub fn swizzle_0yy(&self) -> Self {
        Self::new(0i32, self.y(), self.y())
    }
    pub fn swizzle_0yz(&self) -> Self {
        Self::new(0i32, self.y(), self.z())
    }

    pub fn swizzle_0z0(&self) -> Self {
        Self::new(0i32, self.z(), 0i32)
    }
    pub fn swizzle_0zx(&self) -> Self {
        Self::new(0i32, self.z(), self.x())
    }
    pub fn swizzle_0zy(&self) -> Self {
        Self::new(0i32, self.z(), self.y())
    }
    pub fn swizzle_0zz(&self) -> Self {
        Self::new(0i32, self.z(), self.z())
    }

    pub fn swizzle_x00(&self) -> Self {
        Self::new(self.x(), 0i32, 0i32)
    }
    pub fn swizzle_x0x(&self) -> Self {
        Self::new(self.x(), 0i32, self.x())
    }
    pub fn swizzle_x0y(&self) -> Self {
        Self::new(self.x(), 0i32, self.y())
    }
    pub fn swizzle_x0z(&self) -> Self {
        Self::new(self.x(), 0i32, self.z())
    }

    pub fn swizzle_xx0(&self) -> Self {
        Self::new(self.x(), self.x(), 0i32)
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
        Self::new(self.x(), self.y(), 0i32)
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
        Self::new(self.x(), self.z(), 0i32)
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
        Self::new(self.y(), 0i32, 0i32)
    }
    pub fn swizzle_y0x(&self) -> Self {
        Self::new(self.y(), 0i32, self.x())
    }
    pub fn swizzle_y0y(&self) -> Self {
        Self::new(self.y(), 0i32, self.y())
    }
    pub fn swizzle_y0z(&self) -> Self {
        Self::new(self.y(), 0i32, self.z())
    }

    pub fn swizzle_yx0(&self) -> Self {
        Self::new(self.y(), self.x(), 0i32)
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
        Self::new(self.y(), self.y(), 0i32)
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
        Self::new(self.y(), self.z(), 0i32)
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
        Self::new(self.z(), 0i32, 0i32)
    }
    pub fn swizzle_z0x(&self) -> Self {
        Self::new(self.z(), 0i32, self.x())
    }
    pub fn swizzle_z0y(&self) -> Self {
        Self::new(self.z(), 0i32, self.y())
    }
    pub fn swizzle_z0z(&self) -> Self {
        Self::new(self.z(), 0i32, self.z())
    }

    pub fn swizzle_zx0(&self) -> Self {
        Self::new(self.z(), self.x(), 0i32)
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
        Self::new(self.z(), self.y(), 0i32)
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
        Self::new(self.z(), self.z(), 0i32)
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
