use crate::{Bounds3, EError, Plane, Vec3};

/// Represents sphere shape bounds.
///
///
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Sphere {
    center: Vec3,
    radius: f32,
}

impl Sphere {
    /// Create new [Sphere]. If length `d` is not positive, return error.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Sphere, Vec3};
    ///
    /// let sphere = Sphere::new(Vec3::new(1f32, 2f32, 3f32), 16f32).unwrap();
    /// assert_eq!(sphere.center(), Vec3::new(1f32, 2f32, 3f32));
    /// assert_eq!(sphere.radius(), 16f32);
    /// ```
    pub fn new(center: Vec3, radius: f32) -> Result<Self, EError> {
        if radius <= 0f32 {
            Err(EError::NegativeLength(radius))
        } else {
            Ok(Self { center, radius })
        }
    }

    /// Get the center point of [Sphere].
    pub fn center(&self) -> Vec3 {
        self.center
    }

    /// Get the radius of [Sphere].
    pub fn radius(&self) -> f32 {
        self.radius
    }

    // ------------------------------------------------------------------------
    //
    // PLANE SECTION
    //
    // ------------------------------------------------------------------------

    /// Check this [Sphere] is outside of given [Plane].
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Sphere, Vec3, Extent3, Plane};
    ///
    /// let outside_sphere = Sphere::new(
    ///     Vec3::new(1f32, 2f32, 3f32),
    ///     4f32).unwrap();
    /// let plane = Plane::new(
    ///     Vec3::new(0f32, 1f32, 0f32),
    ///     4f32).unwrap();
    /// assert_eq!(outside_sphere.is_outside_of_plane(&plane), true);
    ///
    /// let inside_sphere = Sphere::new(
    ///     Vec3::new(1f32, -10f32, 3f32),
    ///     4f32).unwrap();
    /// assert_eq!(inside_sphere.is_outside_of_plane(&plane), false);
    /// ```
    pub fn is_outside_of_plane(&self, plane: &Plane) -> bool {
        let sd = plane.dot(self.center()) + plane.d();
        (sd - self.radius()) > 0f32
    }

    /// Check this [Sphere] is inside of given [Plane].
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Sphere, Vec3, Extent3, Plane};
    ///
    /// let outside_sphere = Sphere::new(
    ///     Vec3::new(1f32, 2f32, 3f32),
    ///     4f32).unwrap();
    /// let plane = Plane::new(
    ///     Vec3::new(0f32, 1f32, 0f32),
    ///     4f32).unwrap();
    /// assert_eq!(outside_sphere.is_inside_of_plane(&plane), false);
    ///
    /// let inside_sphere = Sphere::new(
    ///     Vec3::new(1f32, -10f32, 3f32),
    ///     4f32).unwrap();
    /// assert_eq!(inside_sphere.is_inside_of_plane(&plane), true);
    /// ```
    pub fn is_inside_of_plane(&self, plane: &Plane) -> bool {
        let sd = plane.dot(self.center()) + plane.d();
        (sd - self.radius()) < 0f32
    }

    /// Check this [Sphere] is overlapped to given [Plane].
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Sphere, Vec3, Extent3, Plane};
    ///
    /// let sphere = Sphere::new(Vec3::new(1f32, 2f32, 3f32), 4f32).unwrap();
    ///
    /// let overlapped_plane = Plane::new(Vec3::new(0f32, 1f32, 0f32), 1f32).unwrap();
    /// assert_eq!(sphere.is_overlapped_plane(&overlapped_plane), true);
    ///
    /// let adjacent_plane = Plane::new(Vec3::new(0f32, 1f32, 0f32), 2f32).unwrap();
    /// assert_eq!(sphere.is_overlapped_plane(&adjacent_plane), false);
    /// ```
    pub fn is_overlapped_plane(&self, plane: &Plane) -> bool {
        let sd = (plane.dot(self.center()) + plane.d()).abs(); // signed distance.
        (sd - self.radius()) < 0f32
    }

    /// Check this [Sphere] is adjacent to given [Plane].
    pub fn is_adjacent_to_plane(&self, plane: &Plane) -> bool {
        let sd = (plane.dot(self.center()) + plane.d()).abs(); // signed distance.
        (sd - self.radius()) == 0f32
    }

    /// Check this [Sphere] is intersected to given [Plane].
    /// This function is same to `is_overlapped_plane` and `is_adjacent_to_plane`.
    pub fn is_intersected_to_plane(&self, plane: &Plane) -> bool {
        let sd = (plane.dot(self.center()) + plane.d()).abs(); // signed distance.
        (sd - self.radius()) <= 0f32
    }
}

impl From<Sphere> for Bounds3 {
    /// Convert [Sphere] into [Bounds3].
    fn from(sphere: Sphere) -> Bounds3 {
        let d = Vec3::from_scalar(sphere.radius());
        Self::from_points(&[sphere.center - d, sphere.center + d]).unwrap()
    }
}
