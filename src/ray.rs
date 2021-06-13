use crate::{EError, Vec3};

/// A `Ray` is semi-infinite line specified by its `origin` and `direction`.
///
/// # Examples
///
/// ```
/// use hamilton as math;
/// use math::{Ray, Vec3};
///
/// let ray = Ray::uncheck_new(Vec3::from_scalar(0f32), Vec3::new(1f32, 0f32, 0f32));
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
    /// let ray = Ray::uncheck_new(Vec3::from_scalar(5f32), Vec3::new(0f32, 0f32, 0f32));
    /// ```
    pub fn uncheck_new(origin: Vec3, direction: Vec3) -> Self {
        Self {
            origin,
            dir: direction.to_normalized().unwrap(),
        }
    }

    /// Create new [Ray] with `origin` and `direction`.
    ///
    /// If given `direction` is zero lengthed or almost zero lenghted vector,
    /// [Ray] could not be created and return error.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Ray, Vec3};
    ///
    /// let ray = Ray::new(Vec3::from_scalar(5f32), Vec3::new(0.5f32, 0f32, 0f32)).unwrap();
    /// assert_eq!(ray.direction(), Vec3::new(1f32, 0f32, 0f32));
    ///
    /// let should_err = Ray::new(Vec3::from_scalar(5f32), Vec3::from_scalar(0f32)).is_err();
    /// assert_eq!(should_err, true);
    /// ```
    pub fn new(origin: Vec3, direction: Vec3) -> Result<Self, EError> {
        Ok(Self {
            origin,
            dir: direction.to_normalized()?,
        })
    }

    /// Proceed ray along direction of the ray, and create new [Ray].
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Ray, Vec3, NearlyEqual};
    ///
    /// let ray = Ray::uncheck_new(Vec3::from_scalar(0f32), Vec3::new(3f32, 4f32, 5f32));
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

    /// Get shortest distance of two skewed or parallel [Ray] lines.
    ///
    /// If two lines are intersected in any point, returned value will be 0.
    pub fn shortest_distance_to(&self, ray: Ray) -> f32 {
        let dp = ray.origin - self.origin;
        let v1v2 = self.dir.dot(ray.dir);

        let det = (v1v2 * v1v2) - 1f32;
        // If the line is nearly parallel, or actually parallel.
        // If INF or NAN, rust will automatically halt.
        if !det.is_normal() {
            assert!(det.is_finite());
            dp.cross(self.dir).square_length().sqrt()
        } else {
            // We need to get t1 (self) and t2 (ray)
            let invdet = det.recip();
            let dpv1 = dp.dot(self.dir);
            let dpv2 = dp.dot(ray.dir);

            let t1 = ((-1f32 * dpv1) + (v1v2 * dpv2)) * invdet;
            let t2 = ((-v1v2 * dpv1) + (1f32 * dpv2)) * invdet;

            let shortest_t1vec = self.to_proceeded(t1).origin;
            let shortest_t2vec = ray.to_proceeded(t2).origin;

            (shortest_t2vec - shortest_t1vec).length()
        }
    }
}
