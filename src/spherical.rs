use super::Degree;
use super::Radian;
use super::Vec3;

/// Represents spherical coordinates, with phi (vertical) and theta (horizontal).
///
/// This type stores angles as `Radian`.
/// See <https://en.wikipedia.org/wiki/Spherical_coordinate_system>
/// to see what spherical coordinates is.
pub struct Spherical {
    phi: Radian,
    theta: Radian,
}

impl Spherical {
    /// Create `Spherical` from `Radian` values.
    ///
    /// Given `Radian` is not normalized.
    pub fn from_radians(phi: Radian, theta: Radian) -> Self { Self { phi, theta } }

    /// Create `Spherical` from `Degree` values.
    ///
    /// Given `Degree` is not normalized.
    pub fn from_degrees(phi: Degree, theta: Degree) -> Self {
        Self {
            phi: phi.into(),
            theta: theta.into(),
        }
    }

    /// Create rotated unit vector.
    pub fn into_unit_vector(&self) -> Vec3 {
        let x = (*self.phi).sin() * (*self.theta).sin();
        let y = (*self.phi).cos();
        let z = (*self.phi).sin() * (*self.theta).cos();
        Vec3::new(x, y, z)
    }
}

impl Default for Spherical {
    fn default() -> Self {
        Self {
            phi: Radian(0f32),
            theta: Radian(0f32),
        }
    }
}
