use crate::Vec3;

/// A `Ray` is semi-infinite line specified by its `origin` and `direction`.
///
/// # Examples
///
/// ```
/// use hamilton as math;
/// use math::{Ray, Vec3};
///
/// let ray = Ray::unsafe_new(Vec3::from_scalar(0f32), Vec3::new(1f32, 0f32, 0f32));
/// assert_eq!(ray.origin, Vec3::from_scalar(0f32));
/// assert_eq!(ray.to_proceeded(10f32).origin, Vec3::new(10f32, 0f32, 0f32));
/// ```
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Ray {
    pub origin: Vec3,
    dir: Vec3,
}

impl Ray {
    /// Create new [Ray] with `origin` and `direction`.
    ///
    /// # Warning
    ///
    ///	This function does not check given `direction` can be normalized.
    /// If input `direction` could not be normalized, this function will panic.
    ///
    /// ``` should_panic
    /// use hamilton as math;
    /// use math::{Ray, Vec3};
    ///
    /// // Below will be panicked.
    /// let ray = Ray::unsafe_new(Vec3::from_scalar(5f32), Vec3::new(0f32, 0f32, 0f32));
    /// ```
    pub fn unsafe_new(origin: Vec3, direction: Vec3) -> Self {
        Self {
            origin,
            dir: direction.to_normalized().unwrap(),
        }
    }

    /// Proceed ray along direction of the ray, and create new [Ray].
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Ray, Vec3, NearlyEqual};
    ///
    /// let ray = Ray::unsafe_new(Vec3::from_scalar(0f32), Vec3::new(3f32, 4f32, 5f32));
    /// let proceeded_origin = ray.to_proceeded(50f32.sqrt()).origin;
    /// assert!(proceeded_origin.x().nearly_equal(3f32, 1e-4));
    /// assert!(proceeded_origin.y().nearly_equal(4f32, 1e-4));
    /// assert!(proceeded_origin.z().nearly_equal(5f32, 1e-4));
    /// ```
    pub fn to_proceeded(&self, t: f32) -> Ray {
        Self {
            origin: self.origin + (self.dir * t),
            dir: self.dir,
        }
    }

    /// Get ray direction of the [Ray].
    ///
    /// Returned direction length is always or nearly equal to 1.
    pub fn direction(&self) -> Vec3 {
        self.dir
    }
}
