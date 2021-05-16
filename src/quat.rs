use crate::{Degree, Radian, Vec4};
use std::ops::{Add, AddAssign, Mul, MulAssign, Sub, SubAssign};

/// Represents 3D rotation information, roll, pitch and yaw.
///
/// There is a lot of definition about roll, pitch and yaw,
/// but we decided to uniformize these as below.
///
/// * Roll : x-axis rotation value.
/// * Yaw : y-axis rotation value.
/// * Pitch : z-axis rotation value.
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
    /// let rot = Rotation::from_degrees(Degree(30f32), Degree(60f32), Degree(45f32));
    /// assert_eq!(rot.roll_degree(), Degree(30f32));
    /// assert_eq!(rot.yaw_degree(), Degree(60f32));
    /// assert_eq!(rot.pitch_degree(), Degree(45f32));
    /// ```
    pub fn from_degrees(roll: Degree, yaw: Degree, pitch: Degree) -> Self {
        Self {
            roll: roll.into(),
            yaw: yaw.into(),
            pitch: pitch.into(),
        }
    }

    /// Get roll value as [Degree] unit.
    pub fn roll_degree(&self) -> Degree { self.roll.into() }

    /// Get yaw value as [Degree] unit.
    pub fn yaw_degree(&self) -> Degree { self.yaw.into() }

    /// Get pitch value as [Degree] unit.
    pub fn pitch_degree(&self) -> Degree { self.pitch.into() }

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
#[derive(Debug, PartialEq, Clone, Copy)]
pub struct Quat {
    val: Vec4,
}

impl Quat {
    //pub fn from_rotation(
}

impl Default for Quat {
    /// Create not rotated quaternion.
    fn default() -> Self {
        Self {
            val: Vec4::new(0f32, 0f32, 0f32, 1f32),
        }
    }
}
