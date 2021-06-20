#[macro_use]
mod internal_macro;

pub mod angle;
pub mod bounds;
pub mod error;
pub mod extent;
pub mod index;
pub mod ivec2;
pub mod ivec3;
pub mod lerp;
pub mod mat3;
pub mod mat4;
pub mod nearly_equal;
pub mod plane;
pub mod projection;
pub mod quat;
pub mod ray;
pub mod sphere;
pub mod spherical;
pub mod transform;
pub mod vec2;
pub mod vec3;
pub mod vec4;
pub mod wrappable;

pub use angle::{Degree, Radian};
pub use bounds::{Bounds2, Bounds3, IBounds2, IBounds3};
pub use error::EError;
pub use extent::{Extent2, Extent3, IExtent2, IExtent3};
pub use index::Index2;
pub use index::Offset2;
pub use ivec2::IVec2;
pub use ivec3::IVec3;
pub use mat3::Mat3;
pub use mat4::Mat4;
pub use nearly_equal::NearlyEqual;
pub use plane::Plane;
pub use quat::Quat;
pub use quat::Rotation;
pub use ray::Ray;
pub use sphere::Sphere;
pub use spherical::Spherical;
pub use transform::{Transform, TransformBuilder};
pub use vec2::Vec2;
pub use vec3::Vec3;
pub use vec4::Vec4;
pub use wrappable::RangeWrappable;
pub use wrappable::RangeWrappableMinMax;

trait SignedDistance<T> {
    ///
    fn signed_distance_of(&self, v: &T) -> f32;
}

/// Upper bound on the relative error of rounding in floating point arithmethic.
const MACHINE_EPSILON: f32 = f32::EPSILON * 0.5f32;

/// Used to let floating point value be stable,
/// providing additional conservative bound.
///
/// See <https://en.wikipedia.org/wiki/Error_analysis_(mathematics)>.
///
/// TODO : If floating point arithmetic function was `const`, let it be `const`.
pub fn gamma_bound(i: i32) -> f32 {
    ((i as f32) * MACHINE_EPSILON) / (1.0 - ((i as f32) * MACHINE_EPSILON))
}

/// Get y-aligned and x-scaled ratio value.
///
/// # Examples
///
/// ```
/// use hamilton as math;
/// use math::{NearlyEqual, get_xratio};
///
/// const WIDTH: u32 = 1600;
/// const HEIGHT: u32 = 900;
///
/// let xratio = get_xratio(WIDTH, HEIGHT).unwrap();
/// assert_eq!(xratio, 16.0 / 9.0);
/// ```
///
/// If `height` is 0 or not normal floating value,
/// function would be failed and return error.
///
/// ```
/// use hamilton as math;
/// use math::{NearlyEqual, get_xratio};
///
/// const WIDTH: u32 = 1600;
/// const HEIGHT: u32 = 0;
///
/// let should_err = get_xratio(WIDTH, HEIGHT).is_err();
/// assert_eq!(should_err, true);
/// ```
pub fn get_xratio(width: u32, height: u32) -> Result<f32, EError> {
    if !(height as f32).is_normal() {
        Err(EError::NotNormalFloatingValue(height as f32))
    } else {
        Ok((width as f32) / (height as f32))
    }
}
