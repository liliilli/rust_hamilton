#[macro_use]
mod internal_macro;

pub mod angle;
pub mod bounds;
pub mod error;
pub mod extent;
pub mod index;
pub mod mat3;
pub mod mat4;
pub mod nearly_equal;
pub mod quat;
pub mod ray;
pub mod spherical;
//pub mod transform;
pub mod vec2;
pub mod vec3;
pub mod vec4;
pub mod wrappable;

pub use angle::{Degree, Radian};
pub use bounds::Bounds2;
pub use error::EError;
pub use extent::{Extent2, Extent3, IExtent2, IExtent3};
pub use index::Index2;
pub use index::Offset2;
pub use mat3::Mat3;
pub use mat4::Mat4;
pub use nearly_equal::NearlyEqual;
pub use quat::Quat;
pub use quat::Rotation;
pub use ray::Ray;
pub use spherical::Spherical;
//pub use transform::Transform;
pub use vec2::Vec2;
pub use vec3::Vec3;
pub use vec4::Vec4;
pub use wrappable::RangeWrappable;
pub use wrappable::RangeWrappableMinMax;
