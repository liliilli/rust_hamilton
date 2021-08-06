use crate::{Quat, Vec2, Vec3, Vec4};

pub trait Lerp<Rhs = Self> {
    type Output;

    /// Do linear interpolation.
    ///
    /// See <https://en.wikipedia.org/wiki/Linear_interpolation>.
    fn lerp(&self, rhs: &Rhs, t: f32) -> Self::Output;
}

// ----------------------------------------------------------------------------
//
// DEFAULT IMPLEMENTATIONS
//
// ----------------------------------------------------------------------------

impl Lerp for f32 {
    type Output = f32;

    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::lerp::Lerp;
    ///
    /// let src = 0.0f32;
    /// let dst = 10.0f32;
    /// let new = src.lerp(&dst, 0.5);
    /// assert_eq!(new, 0.5f32);
    /// ```
    fn lerp(&self, rhs: &Self, t: f32) -> Self::Output {
        let d = rhs - self;
        (d * t) + self
    }
}

impl Lerp for f64 {
    type Output = f64;

    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::lerp::Lerp;
    ///
    /// let src = 0.0f64;
    /// let dst = 10.0f64;
    /// let new = src.lerp(&dst, 0.5);
    /// assert_eq!(new, 0.5f64);
    /// ```
    fn lerp(&self, rhs: &Self, t: f32) -> Self::Output {
        let d = rhs - self;
        (d * (t as f64)) + self
    }
}

impl Lerp for Vec2 {
    type Output = Self;

    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Vec2, lerp::Lerp};
    ///
    /// let src = Vec2::from_scalar(0.0);
    /// let dst = Vec2::from_scalar(10.0);
    ///
    /// let new = src.lerp(&dst, 0.5);
    /// assert_eq!(new, Vec2::from_scalar(5.0));
    /// ```
    fn lerp(&self, rhs: &Self, t: f32) -> Self::Output {
        let d = rhs - self;
        (d * t) + self
    }
}

impl Lerp for Vec3 {
    type Output = Self;

    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Vec3, lerp::Lerp};
    ///
    /// let src = Vec3::from_scalar(0.0);
    /// let dst = Vec3::from_scalar(10.0);
    ///
    /// let new = src.lerp(&dst, 0.5);
    /// assert_eq!(new, Vec3::from_scalar(5.0));
    /// ```
    fn lerp(&self, rhs: &Self, t: f32) -> Self::Output {
        let d = rhs - self;
        (d * t) + self
    }
}

impl Lerp for Quat {
    type Output = Quat;

    /// Do spherical linear interpolation.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Degree, Vec3, Quat, lerp::Lerp, NearlyEqual};
    ///
    /// let p = Vec3::unit_z();
    /// let q0 = Quat::from_degrees(Degree(30.0), Degree(0.0), Degree(45.0));
    /// let p0 = q0.mul_point(p.to_homogeneous()).swizzle_xyz();
    /// assert!(p0.nearly_equal(Vec3::new(0.354, -0.354, 0.866), 1e-3));
    ///
    /// let q1 = Quat::from_degrees(Degree(60.0), Degree(-45.0), Degree(75.0));
    /// let p1 = q1.mul_point(p.to_homogeneous()).swizzle_xyz();
    /// assert!(p1.nearly_equal(Vec3::new(0.745, -0.566, 0.354), 1e-3));
    ///
    /// let qm = q0.lerp(&q1, 0.5);
    /// let pm = qm.mul_point(p.to_homogeneous()).swizzle_xyz();
    /// assert!(pm.nearly_equal(Vec3::new(0.563, -0.570, 0.599), 1e-3));
    /// ```
    fn lerp(&self, rhs: &Self, t: f32) -> Self::Output {
        let costheta = self.dot(*rhs);
        let theta = costheta.clamp(-1.0, 1.0).acos();
        let theta_p = theta * t;

        // Get normalized quaternion.
        let d0 = Vec4::new(self.x(), self.y(), self.z(), self.w());
        let d1 = Vec4::new(rhs.x(), rhs.y(), rhs.z(), rhs.w());
        let dd = {
            let d = d1 - (d0 * costheta);
            let dsqrt = (d.x() * d.x()) + (d.y() * d.y()) + (d.z() * d.z()) + (d.w() * d.w()).sqrt();
            d * dsqrt.recip()
        };
        let quat_v = (d0 * theta_p.cos()) + (dd * theta_p.sin());
        Quat::new(quat_v.x(), quat_v.y(), quat_v.z(), quat_v.w())
    }
}
