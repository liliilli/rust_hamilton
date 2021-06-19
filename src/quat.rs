use crate::{Degree, Mat4, NearlyEqual, Radian, Vec3, Vec4};
use std::ops::{Add, AddAssign, Mul, MulAssign, Sub, SubAssign};

/// Represents 3D rotation information, roll, pitch and yaw.
///
/// There is a lot of definition about roll, pitch and yaw,
/// but we decided to uniformize these as below.
///
/// * Roll : x-axis rotation value.
/// * Yaw : y-axis rotation value.
/// * Pitch : z-axis rotation value.
///
/// # Examples
///
/// ```
/// use hamilton as math;
/// use math::{Degree, Rotation};
///
/// let rot = Rotation::from_degrees(Degree(30f32), Degree(60f32), Degree(45f32));
/// assert_eq!(rot.roll_degree(), Degree(30f32));
/// assert_eq!(rot.yaw_degree(), Degree(60f32));
/// assert_eq!(rot.pitch_degree(), Degree(45f32));
///
/// let rot = rot + Rotation::from_degrees(Degree(90f32), Degree(-60f32), Degree(-30f32));
/// assert_eq!(rot.roll_degree(), Degree(120f32));
/// assert_eq!(rot.yaw_degree(), Degree(0f32));
/// assert_eq!(rot.pitch_degree(), Degree(15f32));
/// ```
#[derive(Debug, PartialEq, Clone, Copy)]
pub struct Rotation {
    pub roll: Radian,
    pub yaw: Radian,
    pub pitch: Radian,
}

impl Rotation {
    /// Create rotation from [Degree] items.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Degree, Rotation};
    ///
    /// Rotation::from_degrees(Degree(30f32), Degree(60f32), Degree(45f32));
    /// ```
    pub fn from_degrees(roll: Degree, yaw: Degree, pitch: Degree) -> Self {
        Self {
            roll: roll.into(),
            yaw: yaw.into(),
            pitch: pitch.into(),
        }
    }

    /// Get roll value as [Degree] unit.
    pub fn roll_degree(&self) -> Degree {
        self.roll.into()
    }

    /// Get yaw value as [Degree] unit.
    pub fn yaw_degree(&self) -> Degree {
        self.yaw.into()
    }

    /// Get pitch value as [Degree] unit.
    pub fn pitch_degree(&self) -> Degree {
        self.pitch.into()
    }

    /// Normalize rotation values into `[-PI, PI)` in [Radian] unit.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Degree, Radian, Rotation, NearlyEqual};
    ///
    /// let mut rot = Rotation::from_degrees(Degree(30f32), Degree(60f32), Degree(45f32));
    /// rot += Rotation::from_degrees(Degree(180f32), Degree(360f32), Degree(180f32));
    /// rot = rot.to_normalized();
    ///
    /// let t = Degree(1e-3f32);
    /// assert!(rot.roll_degree().nearly_equal(Degree(-150f32), t));
    /// assert!(rot.yaw_degree().nearly_equal(Degree(60f32), t));
    /// assert!(rot.pitch_degree().nearly_equal(Degree(-135f32), t));
    /// ```
    pub fn to_normalized(&self) -> Self {
        Self {
            roll: self.roll.to_normalized(),
            yaw: self.yaw.to_normalized(),
            pitch: self.pitch.to_normalized(),
        }
    }

    /// Get trigonometric `sin` function applicated values.
    ///
    /// Returned each values represents `Roll`, `Yaw` and `Pitch`.
    pub fn sin(self) -> (f32, f32, f32) {
        (self.roll.sin(), self.yaw.sin(), self.pitch.sin())
    }

    /// Get trigonometric `cos` function applicated values.
    ///
    /// Returned each values represents `Roll`, `Yaw` and `Pitch`.
    pub fn cos(self) -> (f32, f32, f32) {
        (self.roll.cos(), self.yaw.cos(), self.pitch.cos())
    }

    /// Get trigonometric `tan` function applicated values.
    ///
    /// Returned each values represents `Roll`, `Yaw` and `Pitch`.
    pub fn tan(self) -> (f32, f32, f32) {
        (self.roll.tan(), self.yaw.tan(), self.pitch.tan())
    }
}

impl NearlyEqual for Rotation {
    type Tolerance = Self;

    fn nearly_equal(&self, to: Self, tolerance: Self) -> bool {
        let off = *self - to;
        (off.roll.0.abs() <= tolerance.roll.0)
            && (off.yaw.0.abs() <= tolerance.yaw.0)
            && (off.pitch.0.abs() <= tolerance.pitch.0)
    }
}

op_rotation_binary_impl!(Rotation, Add, add, +);
op_rotation_binary_impl!(Rotation, Sub, sub, -);
op_rotation_scalar_mul_impl!(Rotation, Mul, mul, *, u8 u16 u32 u64 i8 i16 i32 i64 usize isize f32 f64);

op_rotation_assign_impl!(Rotation, AddAssign, add_assign, +=);
op_rotation_assign_impl!(Rotation, SubAssign, sub_assign, -=);
op_rotation_assign_scalar_impl!(Rotation, MulAssign, mul_assign, *=, u8 u16 u32 u64 i8 i32 i64 usize isize f32 f64);

/// Quaternion type that stores rotation informtion avoiding gimbal lock problem.
///
/// All values in item are always normalized into 1.
///
/// # Examples
///
/// ```
/// use hamilton as math;
/// use math::{Degree, Rotation, Quat};
///
/// let lhs = Rotation::from_degrees(Degree(30f32), Degree(0f32), Degree(45f32));
/// let quat: Quat = lhs.into();
///
/// let rhs = Rotation::from_degrees(Degree(30f32), Degree(-45f32), Degree(15f32));
/// let quat = quat.mul(rhs.into());
/// ```
///
/// # Todos
///
/// * Add comments and test
/// * Add more functionality.
#[derive(Debug, PartialEq, Clone, Copy)]
pub struct Quat {
    x: f32,
    y: f32,
    z: f32,
    w: f32,
}

impl Quat {
    /// Create [Quat] from three [Degree] euler angle values.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Degree, Rotation, Quat};
    ///
    /// let quat = Quat::from_degrees(Degree(30f32), Degree(0f32), Degree(45f32));
    /// ```
    pub fn from_degrees(roll: Degree, yaw: Degree, pitch: Degree) -> Self {
        Rotation::from_degrees(roll, yaw, pitch).into()
    }

    /// Create [Quat] from three [Radian] euler angle values.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Degree, Radian, Rotation, Quat};
    ///
    /// let quat = Quat::from_radians(Degree(30f32).into(), Radian(0f32), Degree(45f32).into());
    /// ```
    pub fn from_radians(roll: Radian, yaw: Radian, pitch: Radian) -> Self {
        Rotation { roll, yaw, pitch }.into()
    }

    ///
    ///
    ///
    pub fn new(x: f32, y: f32, z: f32, w: f32) -> Self {
        let len = ((x * x) + (y * y) + (z * z) + (w * w)).sqrt();
        assert!(len.is_normal());

        Self {
            x: x / len,
            y: y / len,
            z: z / len,
            w: w / len,
        }
    }

    /// Return `x` value of quaternion.
    pub fn x(&self) -> f32 {
        self.x
    }
    /// Return `y` value of quaternion.
    pub fn y(&self) -> f32 {
        self.y
    }
    /// Return `z` value of quaternion.
    pub fn z(&self) -> f32 {
        self.z
    }
    /// Return `w` value of quaternion.
    pub fn w(&self) -> f32 {
        self.w
    }

    /// Multiplicate with another [Quat].
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Degree, Rotation, Quat};
    ///
    /// let lhs = Quat::from_degrees(Degree(30f32), Degree(0f32), Degree(45f32));
    /// let rhs = Quat::from_degrees(Degree(-30f32), Degree(45f32), Degree(-135f32));
    /// let multiplied = lhs.mul(rhs);
    ///
    /// let target = Quat::from_degrees(Degree(0f32), Degree(45f32), Degree(-90f32));
    /// assert_ne!(multiplied, target);
    /// ```
    pub fn mul(&self, rhs: Self) -> Self {
        Self {
            x: (self.x * rhs.w) + (self.w * rhs.x) + (self.y * rhs.z) - (self.z * rhs.y),
            y: (self.y * rhs.w) + (self.z * rhs.x) + (self.w * rhs.y) - (self.x * rhs.z),
            z: (self.z * rhs.w) + (self.w * rhs.z) + (self.x * rhs.y) - (self.y * rhs.x),
            w: (self.w * rhs.w) - (self.x * rhs.x) - (self.y * rhs.y) - (self.z * rhs.z),
        }
    }

    /// Multiplicate and transform given point [Vec4] which that `w` is 1.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Degree, Rotation, Quat, Vec3, Vec4};
    ///
    /// let quat = Quat::from_degrees(
    ///     Degree(0.0),
    ///     Degree(45.0),
    ///     Degree(-90.0)
    /// );
    /// let vec = quat.mul_point(Vec3::unit_z().to_homogeneous());
    /// ```
    pub fn mul_point(&self, point: Vec4) -> Vec4 {
        let bvec = Vec3::new(self.x(), self.y(), self.z());
        let b2 = bvec.square_length();
        let point = point.swizzle_xyz();

        ((point * (self.w * self.w - b2))
            + (bvec * (point.dot(bvec) * 2f32))
            + (bvec.cross(point) * (self.w * 2f32)))
            .to_homogeneous()
    }

    /// Invert [Quat].
    ///
    /// Inverted unit quaternion is same to conjugated quaternion.
    pub fn to_inverted(&self) -> Self {
        let original: Vec4 = self.into();
        let conjugated: Vec4 = original * Vec4::new(-1f32, -1f32, -1f32, 1f32);
        let invdot = 1f32 / original.dot(conjugated);

        Self {
            x: self.x * invdot,
            y: self.y * invdot,
            z: self.z * invdot,
            w: self.w * invdot,
        }
    }

    pub fn dot(&self, rhs: Quat) -> f32 {
        self.x * rhs.x + self.y * rhs.y + self.z * rhs.z + self.w * rhs.w
    }
}

impl Default for Quat {
    /// Create not rotated quaternion.
    fn default() -> Self {
        Self {
            x: 0f32,
            y: 0f32,
            z: 0f32,
            w: 1f32,
        }
    }
}

impl From<Rotation> for Quat {
    fn from(rot: Rotation) -> Self {
        let (cosx, cosy, cosz) = (rot * 0.5f32).cos();
        let (sinx, siny, sinz) = (rot * 0.5f32).sin();

        Self {
            x: (sinx * cosy * cosz) - (cosx * siny * sinz),
            y: (cosx * siny * cosz) + (sinx * cosy * sinz),
            z: (cosx * cosy * sinz) - (sinx * siny * cosz),
            w: (cosx * cosy * cosz) + (sinx * siny * sinz),
        }
    }
}

impl From<&Rotation> for Quat {
    fn from(rot: &Rotation) -> Self {
        let (cosx, cosy, cosz) = (rot * 0.5f32).cos();
        let (sinx, siny, sinz) = (rot * 0.5f32).sin();

        Self {
            x: (sinx * cosy * cosz) - (cosx * siny * sinz),
            y: (cosx * siny * cosz) + (sinx * cosy * sinz),
            z: (cosx * cosy * sinz) - (sinx * siny * cosz),
            w: (cosx * cosy * cosz) + (sinx * siny * sinz),
        }
    }
}

impl From<Quat> for Vec4 {
    fn from(quat: Quat) -> Self {
        Self::new(quat.x, quat.y, quat.z, quat.w)
    }
}

impl From<&Quat> for Vec4 {
    fn from(quat: &Quat) -> Self {
        Self::new(quat.x, quat.y, quat.z, quat.w)
    }
}
