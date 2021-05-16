#[macro_use]
mod internal_macro;

pub mod angle;
pub mod mat3;
pub mod mat4;
pub mod nearly_equal;
pub mod quat;
pub mod spherical;
pub mod vec2;
pub mod vec3;
pub mod vec4;
pub mod wrappable;

pub use angle::Degree;
pub use angle::Radian;
pub use mat3::Mat3;
pub use mat4::Mat4;
pub use nearly_equal::NearlyEqual;
pub use quat::Quat;
pub use quat::Rotation;
pub use spherical::Spherical;
pub use vec2::Vec2;
pub use vec3::Vec3;
pub use vec4::Vec4;
pub use wrappable::RangeWrappable;
pub use wrappable::RangeWrappableMinMax;
