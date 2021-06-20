use std::ops::Mul;

use crate::{Mat4, Quat, Rotation, Vec3, Vec4};

/// This type guarantees that
/// this [Mat4] alternative matrix can be validly used as a [Transform].
///
/// This does not provide getting scale and euler rotation angles from the matrix.
///
/// # Examples
///
/// ```
/// use hamilton as math;
/// use math::{Vec3, Transform, Rotation, Degree, Quat};
///
/// let transform = Transform::builder()
///     .translation(Vec3::new(3.0, 4.0, 5.0))
///     .scale(Vec3::new(1.0, 0.5, 2.0))
///     .rotation(Quat::from_degrees(Degree(0.0), Degree(45.0), Degree(-90.0)))
///     .build();
/// assert_eq!(transform.translation(), Vec3::new(3.0, 4.0, 5.0));
///
/// let point = transform.mul_point(Vec3::unit_z().to_homogeneous());
/// ```
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Transform {
    /// Column-major matrix.
    transform: Mat4,
}

impl Transform {
    /// Make builder [TransformBuilder] instance for [Transform].
    pub fn builder() -> TransformBuilder {
        TransformBuilder::builder()
    }

    /// Create identity [Transform].
    /// Provides no translation, no rotation and default scale.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Vec3, Transform};
    ///
    /// let transform = Transform::from_identity();
    /// assert_eq!(transform.translation(), Vec3::from_scalar(0.0));
    /// ```
    pub fn from_identity() -> Self {
        Self {
            transform: Mat4::from_identity(),
        }
    }

    /// Create [Transform] which has given translation [Vec3].
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Vec3, Transform};
    ///
    /// let transform = Transform::from_translation(Vec3::new(3.0, 4.0, 5.0));
    /// assert_eq!(transform.translation(), Vec3::new(3.0, 4.0, 5.0));
    /// ```
    pub fn from_translation(translation: Vec3) -> Self {
        let mut v = Self::from_identity();
        v.transform[3] = translation.to_homogeneous();
        v
    }

    /// Create [Transform] which has given scale [Vec3].
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Vec3, Transform};
    ///
    /// let transform = Transform::from_scaling(Vec3::new(3.0, 4.0, 5.0));
    /// ```
    pub fn from_scaling(scaling: Vec3) -> Self {
        let mut v = Self::from_identity();
        let rv = &mut v.transform;
        rv[0][0] = scaling.x();
        rv[1][1] = scaling.y();
        rv[2][2] = scaling.z();
        v
    }

    /// Create [Transform] with given euler rotation [Rotation].
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Vec3, Transform, Rotation, Degree};
    ///
    /// let rotation = Rotation::from_degrees(
    ///     Degree(0.0),
    ///     Degree(45.0),
    ///     Degree(-90.0)
    /// );
    /// let transform = Transform::from_rotation(rotation);
    /// let vec = transform.mul_point(Vec3::unit_z().to_homogeneous());
    /// ```
    pub fn from_rotation(rotation: Rotation) -> Self {
        Self::from_quat(rotation.into())
    }

    /// Create [Transform] from quaternion [Quat] which stores rotation information.
    ///
    /// This is same to `from_rotation` method.
    pub fn from_quat(quat: Quat) -> Self {
        let x2 = quat.x() * quat.x();
        let y2 = quat.y() * quat.y();
        let z2 = quat.z() * quat.z();
        let xy = quat.x() * quat.y();
        let xz = quat.x() * quat.z();
        let yz = quat.y() * quat.z();
        let wx = quat.w() * quat.x();
        let wy = quat.w() * quat.y();
        let wz = quat.w() * quat.z();

        let transform = Mat4::from_column_arrays(
            [
                1.0 - (2.0 * (y2 + z2)),
                2.0 * (xy + wz),
                2.0 * (xz - wy),
                0.0,
            ],
            [
                2.0 * (xy - wz),
                1.0 - (2.0 * (x2 + z2)),
                2.0 * (yz + wx),
                0.0,
            ],
            [
                2.0 * (xz + wy),
                2.0 * (yz - wx),
                1.0 - (2.0 * (x2 + y2)),
                0.0,
            ],
            [0.0, 0.0, 0.0, 1.0],
        );
        Self { transform }
    }

    /// Create look-at [Transform].
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Vec3, Transform, Rotation, Degree};
    ///
    /// let lookat = Transform::from_lookat(
    ///     Vec3::new(1.0, -1.0, 2.0),  // Forward
    ///     Vec3::unit_y(),             // WorldUp
    ///     Vec3::new(3.0, 4.0, 5.0),   // Translation
    /// );
    /// ```
    pub fn from_lookat(forward: Vec3, world_up: Vec3, translation: Vec3) -> Self {
        let forward = forward.to_normalized().unwrap();
        let sidex = forward.cross(world_up.to_normalized().unwrap());
        let upy = sidex.cross(forward);
        let lookat_mat = Mat4::from_column_arrays(
            [sidex.x(), upy.x(), forward.x(), 0.0],
            [sidex.y(), upy.y(), forward.y(), 0.0],
            [sidex.z(), upy.z(), forward.z(), 0.0],
            [translation.x(), translation.y(), translation.z(), 1.0],
        );
        Self {
            transform: lookat_mat,
        }
    }

    /// Get translation of this [Transform].
    pub fn translation(&self) -> Vec3 {
        self.transform[3].swizzle_xyz()
    }

    /// Set new translation of this [Transform].
    pub fn set_translation(&mut self, translation: Vec3) {
        self.transform[3] = translation.to_homogeneous();
    }

    /// Multiply point [Vec4] which w is 1, and transform point.
    pub fn mul_point(&self, point: Vec4) -> Vec4 {
        self.transform.mul_vec4(point)
    }

    /// Multiply normal point [Vec3].
    /// All normal point must be transformed using this method, not `mul_point`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Vec3, Transform, Rotation, Degree, Quat, NearlyEqual};
    ///
    /// let transform = Transform::builder()
    ///     .translation(Vec3::new(3.0, 4.0, 5.0))
    ///     .scale(Vec3::new(1.0, 0.5, 2.0))
    ///     .rotation(Quat::from_degrees(Degree(0.0), Degree(45.0), Degree(-90.0)))
    ///     .build();
    /// let normal = Vec3::new(1.5, 2.4, -3.3).to_normalized().unwrap();
    /// assert!(normal.length().nearly_equal(1.0, 1e-4));
    /// let transformed_normal = transform.mul_normal(normal);

    /// let inv_t = transform.to_inverted();
    /// let inv_normal = inv_t.mul_normal(transformed_normal);
    /// assert!(inv_normal.x().nearly_equal(normal.x(), 1e-4));
    /// assert!(inv_normal.y().nearly_equal(normal.y(), 1e-4));
    /// assert!(inv_normal.z().nearly_equal(normal.z(), 1e-4));
    /// ```
    pub fn mul_normal(&self, normal: Vec3) -> Vec3 {
        self.to_inverted()
            .transform
            .to_transposed()
            .mul_vec4(normal.swizzle_xyz0())
            .swizzle_xyz()
            .to_normalized()
            .unwrap()
    }

    /// Multiply with another [Transform] and create new [Transform].
    pub fn mul(&self, other: Self) -> Self {
        Self {
            transform: self.transform.mul(other.transform),
        }
    }

    /// Get inverted transform.
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Vec3, Transform, Rotation, Degree, Quat, NearlyEqual};
    ///
    /// let transform = Transform::builder()
    ///     .translation(Vec3::new(3.0, 4.0, 5.0))
    ///     .scale(Vec3::new(1.0, 0.5, 2.0))
    ///     .rotation(Quat::from_degrees(Degree(0.0), Degree(45.0), Degree(-90.0)))
    ///     .build();
    /// let point = transform.mul_point(Vec3::unit_z().to_homogeneous());
    ///
    /// let inv_transform = transform.to_inverted();
    /// let inv_point = inv_transform.mul_point(point);
    /// assert!(inv_point.x().nearly_equal(0.0, 1e-4));
    /// assert!(inv_point.y().nearly_equal(0.0, 1e-4));
    /// assert!(inv_point.z().nearly_equal(1.0, 1e-4));
    /// assert!(inv_point.w().nearly_equal(1.0, 1e-4));
    /// ```
    pub fn to_inverted(&self) -> Self {
        let a = self.transform[0].swizzle_xyz();
        let b = self.transform[1].swizzle_xyz();
        let c = self.transform[2].swizzle_xyz();
        let d = self.transform[3].swizzle_xyz();

        let mut s = a.cross(b);
        let mut t = c.cross(d);
        let invdet = s.dot(c).recip();
        s *= invdet;
        t *= invdet;
        let v = c * invdet;
        let r0 = b.cross(v);
        let r1 = v.cross(a);

        let transform = Mat4::from_column_arrays(
            [r0.x(), r1.x(), s.x(), 0.0],
            [r0.y(), r1.y(), s.y(), 0.0],
            [r0.z(), r1.z(), s.z(), 0.0],
            [-(b.dot(t)), a.dot(t), -(d.dot(s)), 1.0],
        );
        Self { transform }
    }

    /// Check [Transform]'s handedness.
    ///
    /// Internally, handedness could be checked by checking determinant of first 3x3 submatrix.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Vec3, Transform, Degree, Quat, NearlyEqual};
    ///
    /// let righthanded = Transform::builder()
    ///     .translation(Vec3::new(3.0, 4.0, 5.0))
    ///     .scale(Vec3::new(1.0, 0.5, 2.0))
    ///     .rotation(Quat::from_degrees(Degree(0.0), Degree(45.0), Degree(-90.0)))
    ///     .build();
    /// assert_eq!(righthanded.is_right_handedness(), true);
    ///
    /// let lookat = Transform::from_lookat(
    ///     Vec3::new(1.0, -1.0, 2.0),  // Forward
    ///     Vec3::unit_y(),             // WorldUp
    ///     Vec3::new(3.0, 4.0, 5.0),   // Translation
    /// );
    /// assert_eq!(lookat.is_right_handedness(), false);
    /// ```
    pub fn is_right_handedness(&self) -> bool {
        let t = &self.transform;
        let d0 = t[0][0] * (t[1][1] * t[2][2] - t[1][2] * t[2][1]);
        let d1 = t[0][1] * (t[1][0] * t[2][2] - t[1][2] * t[2][0]);
        let d2 = t[0][2] * (t[1][0] * t[2][1] - t[1][1] * t[2][0]);
        let det = d0 - d1 + d2;
        det > 0.0
    }
}

/// Builder type for building [Transform].
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct TransformBuilder {
    translation: Vec3,
    scale: Vec3,
    rotation: Quat,
}

impl TransformBuilder {
    /// Make builder instance for [Transform].
    pub fn builder() -> Self {
        Self {
            translation: Vec3::default(),
            scale: Vec3::from_scalar(1.0),
            rotation: Quat::default(),
        }
    }

    /// Set translation of building [Transform] by [Vec3].
    pub fn translation(mut self, translation: Vec3) -> Self {
        self.translation = translation;
        self
    }

    /// Set scale of building [Transform] by [Vec3].
    pub fn scale(mut self, scale: Vec3) -> Self {
        self.scale = scale;
        self
    }

    /// Set rotation of building [Transform] by [Quat].
    pub fn rotation(mut self, rot: Quat) -> Self {
        self.rotation = rot;
        self
    }

    /// Build [Transform].
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Vec3, Transform, Rotation, Degree, Quat};
    ///
    /// let transform = Transform::builder()
    ///     .translation(Vec3::new(3.0, 4.0, 5.0))
    ///     .scale(Vec3::new(1.0, 0.5, 2.0))
    ///     .rotation(Quat::from_degrees(Degree(0.0), Degree(45.0), Degree(-90.0)))
    ///     .build();
    /// assert_eq!(transform.translation(), Vec3::new(3.0, 4.0, 5.0));
    ///
    /// let transformed_point = transform.mul_point(Vec3::unit_z().to_homogeneous());
    /// ```
    pub fn build(self) -> Transform {
        let mut transform = Transform::from_quat(self.rotation);
        transform.transform[0] *= self.scale.x();
        transform.transform[1] *= self.scale.y();
        transform.transform[2] *= self.scale.z();
        transform.transform[3] = self.translation.to_homogeneous();
        transform
    }
}
