use crate::{EError, Ray, Vec3};

///
///
///
#[derive(Debug, Copy, Clone, PartialEq)]
pub struct Plane {
    normal: Vec3,
    d: f32,
}

impl Plane {
    /// Create [Plane] from three points.
    ///
    /// If normal vector of plane could not be calculated, return error.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Vec3, Plane};
    ///
    /// let plane = Plane::from_points(&[
    /// 	Vec3::default(),
    /// 	Vec3::new(1f32, 0f32, 0f32),
    ///		Vec3::new(0f32, 0f32, -1f32)
    ///	]).unwrap();
    /// assert_eq!(plane.normal(), Vec3::unit_y());
    /// ```
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Vec3, Plane};
    ///
    /// let should_err = Plane::from_points(&[
    /// 	Vec3::default(),
    /// 	Vec3::default(),
    /// 	Vec3::default(),
    ///	]).is_err();
    /// assert_eq!(should_err, true);
    /// ```
    pub fn from_points(triangle: &[Vec3; 3]) -> Result<Plane, EError> {
        let p21 = triangle[1] - triangle[0];
        let p31 = triangle[2] - triangle[0];
        let normal = p21.cross(p31).to_normalized()?;

        Ok(Self {
            normal,
            d: normal.dot(triangle[0]) * -1f32,
        })
    }

    /// Create [Plane] with valid normal vector and `d`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Vec3, Plane};
    ///
    /// let normal = Vec3::new(3f32, 4f32, 5f32);
    /// let plane = Plane::new(normal, 1f32).unwrap();
    /// assert_eq!(plane.normal(), normal.to_normalized().unwrap());
    /// ```
    pub fn new(normal: Vec3, d: f32) -> Result<Plane, EError> {
        Ok(Self {
            normal: normal.to_normalized()?,
            d,
        })
    }

    /// Get unit normal vector of this [Plane].
    pub fn normal(&self) -> Vec3 {
        self.normal
    }

    /// Get `d` value of this [Plane].
    pub fn d(&self) -> f32 {
        self.d
    }

    /// Do dot product given `v` [Vec3] into this [Plane].
    ///
    /// Doing dot product into normalized [Plane] is equalivalent to getting
    /// signed distance between `v` point, detecting whether the point is inside or outside.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Vec3, Plane};
    ///
    /// let plane = Plane::from_points(&[
    /// 	Vec3::default(),
    /// 	Vec3::new(1f32, 0f32, 0f32),
    ///		Vec3::new(0f32, 0f32, -1f32)
    ///	]).unwrap();
    /// assert_eq!(plane.normal(), Vec3::unit_y());
    /// assert!(plane.dot(Vec3::new(3f32, 4f32, 5f32)) > 0f32); // Outside.
    /// assert!(plane.dot(Vec3::new(-3f32, -4f32, -5f32)) < 0f32); // Inside.
    /// ```
    pub fn dot(&self, v: Vec3) -> f32 {
        self.normal.dot(v)
    }

    /// Check given vector point `v` is outside of this [Plane].
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Vec3, Plane};
    ///
    /// let plane = Plane::from_points(&[
    /// 	Vec3::default(),
    /// 	Vec3::new(1f32, 0f32, 0f32),
    ///		Vec3::new(0f32, 0f32, -1f32)
    ///	]).unwrap();
    /// assert_eq!(plane.normal(), Vec3::unit_y());
    /// assert_eq!(plane.check_outside(Vec3::new(3f32, 4f32, 5f32)), true);
    /// ```
    pub fn check_outside(&self, v: Vec3) -> bool {
        self.dot(v) > 0f32
    }

    /// Check given vector point `v` is inside of this [Plane].
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Vec3, Plane};
    ///
    /// let plane = Plane::from_points(&[
    /// 	Vec3::default(),
    /// 	Vec3::new(1f32, 0f32, 0f32),
    ///		Vec3::new(0f32, 0f32, -1f32)
    ///	]).unwrap();
    /// assert_eq!(plane.normal(), Vec3::unit_y());
    /// assert_eq!(plane.check_inside(Vec3::new(-3f32, -4f32, -5f32)), true);
    /// ```
    pub fn check_inside(&self, v: Vec3) -> bool {
        self.dot(v) < 0f32
    }

    /// Get intersected point from ray [Ray] into this [Plane].
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Vec3, Plane, Ray};
    ///
    /// let plane = Plane::from_points(&[
    /// 	Vec3::default(),
    /// 	Vec3::unit_x(),
    ///		Vec3::unit_z() * -1f32,
    ///	]).unwrap();
    /// let ray = Ray::new(Vec3::new(4f32, 5f32, 6f32), Vec3::from_scalar(-1f32)).unwrap();
    /// let intersected = plane.intersected_of_ray(ray).unwrap();
    /// assert_eq!(intersected, Vec3::new(-1f32, 0f32, 1f32));
    /// ```
    pub fn intersected_of_ray(&self, r: Ray) -> Result<Vec3, EError> {
        if !r.direction().dot(self.normal).is_normal() {
            Err(EError::ZeroLengthVector)
        } else {
            let recip = self.normal().dot(r.direction()).recip();
            let fdotp = self.normal().dot(r.origin) + self.d();
            Ok(r.origin - (r.direction() * (fdotp * recip)))
        }
    }
}

/// Try to get intersected point between three [Plane]s.
///
/// # Examples
///
/// ```
/// use hamilton as math;
/// use math::{Vec3, Plane, plane::intersected_with_planes};
///
/// let plane1 = Plane::new(Vec3::unit_x(), 6f32).unwrap();
/// let plane2 = Plane::new(Vec3::unit_y(), 5f32).unwrap();
/// let plane3 = Plane::new(Vec3::unit_z(), 4f32).unwrap();
/// let intersected = intersected_with_planes(&[plane1, plane2, plane3]).unwrap();
/// assert_eq!(intersected, Vec3::new(-6f32, -5f32, -4f32));
/// ```
pub fn intersected_with_planes(planes: &[Plane; 3]) -> Result<Vec3, EError> {
    let n1 = planes[0].normal();
    let n2 = planes[1].normal();
    let n3 = planes[2].normal();

    let n1cn2 = n1.cross(n2);
    let det = n1cn2.dot(n3);
    if !det.is_normal() {
        Err(EError::ZeroLengthVector)
    } else {
        let recip = det.recip();
        let v1 = planes[2].normal().cross(planes[1].normal()) * planes[0].d();
        let v2 = planes[0].normal().cross(planes[2].normal()) * planes[1].d();
        let v3 = planes[1].normal().cross(planes[0].normal()) * planes[2].d();

        Ok((v1 + v2 + v3) * recip)
    }
}

/// Try to get exist [Ray] which is intersecting two [Plane]s.
///
/// # Examples
///
/// ```
/// use hamilton as math;
/// use math::{Vec3, Ray, Plane, plane::intersected_ray_of};
///
/// let plane1 = Plane::new(Vec3::unit_x(), 6f32).unwrap();
/// let plane2 = Plane::new(Vec3::unit_y(), 5f32).unwrap();
/// let ray = intersected_ray_of(&[plane1, plane2]).unwrap();
/// assert_eq!(ray.origin, Vec3::new(-6f32, -5f32, 0f32));
/// assert_eq!(ray.direction(), Vec3::unit_z());
/// ```
pub fn intersected_ray_of(planes: &[Plane; 2]) -> Result<Ray, EError> {
    let n1 = planes[0].normal();
    let n2 = planes[1].normal();
    let v = n1.cross(n2);
    let det = v.dot(v);
    if !det.is_normal() {
        Err(EError::ZeroLengthVector)
    } else {
        let recip = det.recip();
        let v1 = (v.cross(planes[1].normal())) * planes[0].d();
        let v2 = (planes[0].normal().cross(v)) * planes[1].d();
        let p = (v1 + v2) * recip;

        Ok(Ray::new(p, v).unwrap())
    }
}
