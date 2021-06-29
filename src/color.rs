use crate::Vec4;

/// Represents alpha enabled color.
///
/// This type is for `R32G32B32A32_FLOAT`,
/// and does not restrict each component's value into `[0, 1]` range.
///
/// # Example
///
/// ```
/// use hamilton as math;
/// use math::{ColorRgba};
///
/// let color = ColorRgba::new(1.0, 0.5, 0.3, 0.8);
/// assert_eq!(color.r(), 1.0);
/// assert_eq!(color.g(), 0.5);
/// assert_eq!(color.b(), 0.3);
/// assert_eq!(color.a(), 0.8);
/// ```
///
/// # Note
///
/// See <https://docs.microsoft.com/en-us/windows/win32/api/dxgiformat/ne-dxgiformat-dxgi_format>
///
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct ColorRgba {
    data: Vec4,
}

impl ColorRgba {
    /// Create new color [`ColorRgba`].
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{ColorRgba};
    ///
    /// let color = ColorRgba::new(1.5, 0.5, 0.3, 0.8);
    /// assert_eq!(color.r(), 1.5);
    /// assert_eq!(color.g(), 0.5);
    /// assert_eq!(color.b(), 0.3);
    /// assert_eq!(color.a(), 0.8);
    /// ```
    ///
    /// # Warning
    ///
    /// This function does not check given values are negative, or exceed `1.0`.
    /// Use [`ColorRgba::new_clamped`] method for clamping values into `[0, 1]`.
    pub fn new(r: f32, g: f32, b: f32, a: f32) -> Self {
        Self {
            data: Vec4::new(r, g, b, a),
        }
    }

    /// Create new color [`ColorRgba`], but also clamping every components into `[0, 1]`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{ColorRgba};
    ///
    /// let color = ColorRgba::new_clamped(1.5, 0.5, -0.3, 1.0);
    /// assert_eq!(color.r(), 1.0);
    /// assert_eq!(color.g(), 0.5);
    /// assert_eq!(color.b(), 0.0);
    /// assert_eq!(color.a(), 1.0);
    /// ```
    pub fn new_clamped(r: f32, g: f32, b: f32, a: f32) -> Self {
        Self {
            data: Vec4::new(
                r.clamp(0.0, 1.0),
                g.clamp(0.0, 1.0),
                b.clamp(0.0, 1.0),
                a.clamp(0.0, 1.0),
            ),
        }
    }

    /// Create new color but opaque (non-transparent).
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{ColorRgba};
    ///
    /// let color = ColorRgba::new_opaque_rgb(1.0, 0.5, 0.3);
    /// assert_eq!(color.r(), 1.0);
    /// assert_eq!(color.g(), 0.5);
    /// assert_eq!(color.b(), 0.3);
    /// assert_eq!(color.a(), 1.0);
    /// ```
    ///
    /// # Warning
    ///
    /// This function does not check given values are negative, or exceed `1.0`.
    /// Use [`ColorRgba::new_opaque_rgb_clamped`] method for clamping values into `[0, 1]`.
    pub fn new_opaque_rgb(r: f32, g: f32, b: f32) -> Self {
        Self {
            data: Vec4::new(r, g, b, 1.0f32),
        }
    }

    /// Create new color but opaque (non-transparent),
    /// but also clamping every components into `[0, 1]`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{ColorRgba};
    ///
    /// let color = ColorRgba::new_opaque_rgb_clamped(1.5, 0.5, -0.3);
    /// assert_eq!(color.r(), 1.0);
    /// assert_eq!(color.g(), 0.5);
    /// assert_eq!(color.b(), 0.0);
    /// assert_eq!(color.a(), 1.0);
    /// ```
    pub fn new_opaque_rgb_clamped(r: f32, g: f32, b: f32) -> Self {
        Self {
            data: Vec4::new(r.clamp(0.0, 1.0), g.clamp(0.0, 1.0), b.clamp(0.0, 1.0), 1.0),
        }
    }

    /// Create new color with 4 components array.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{ColorRgba};
    ///
    /// let color = ColorRgba::from_array([1.0, 0.8, 0.3, 0.5]);
    /// assert_eq!(color.r(), 1.0);
    /// assert_eq!(color.g(), 0.8);
    /// assert_eq!(color.b(), 0.3);
    /// assert_eq!(color.a(), 0.5);
    /// ```
    pub fn from_array(arr: [f32; 4]) -> Self {
        Self {
            data: Vec4::from_array(arr),
        }
    }

    /// Get red channel component color value.
    #[inline]
    pub fn r(&self) -> f32 {
        self.data.x()
    }

    /// Get green channel component color value.
    #[inline]
    pub fn g(&self) -> f32 {
        self.data.y()
    }

    /// Get blue channel component color value.
    #[inline]
    pub fn b(&self) -> f32 {
        self.data.z()
    }

    ///
    #[inline]
    pub fn a(&self) -> f32 {
        self.data.w()
    }

    /// Get `y` coefficient of XYZ color of this RGBA color.
    ///
    /// `y` coefficient is closely related to *luminance*, which measures the perceived
    /// brightness of a color.
    ///
    /// `Luminance` measures how bright a spectral power distribution (SPD)
    /// appears to a human observer.
    ///
    /// # Note
    ///
    /// * Calculated *luminance* does not calculate alpha value.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{ColorRgba};
    ///
    /// let color = ColorRgba::new_opaque_rgb(0.8, 0.75, 0.2);
    /// let luminance = color.y();
    /// ```
    pub fn y(&self) -> f32 {
        const WEIGHTS: [f32; 3] = [0.212671f32, 0.715160f32, 0.072169f32];
        self.r() * WEIGHTS[0] + self.g() * WEIGHTS[1] + self.b() * WEIGHTS[2]
    }

    // ------------------------------------------------------------------------
    //
    // COLOR PALETTES
    //
    // ------------------------------------------------------------------------

    /// Get `maroon` color as [`ColorRgba`].
    pub fn maroon() -> Self {
        Self::new_opaque_rgb(0.5, 0.0, 0.0)
    }

    /// Get `red` color as [`ColorRgba`].
    pub fn red() -> Self {
        Self::new_opaque_rgb(1.0, 0.0, 0.0)
    }

    /// Get `orange` color as [`ColorRgba`].
    pub fn orange() -> Self {
        Self::new_opaque_rgb(1.0, u8_to_f32(0xa5), 0.0)
    }

    /// Get `yellow` color as [`ColorRgba`].
    pub fn yellow() -> Self {
        Self::new_opaque_rgb(1.0, 1.0, 0.0)
    }

    /// Get `olive` color as [`ColorRgba`].
    pub fn olive() -> Self {
        Self::new_opaque_rgb(0.5, 0.5, 0.0)
    }

    /// Get `purple` color as [`ColorRgba`].
    pub fn purple() -> Self {
        Self::new_opaque_rgb(0.5, 0.0, 0.5)
    }

    /// Get `fuchsia` color as [`ColorRgba`].
    pub fn fuchsia() -> Self {
        Self::new_opaque_rgb(1.0, 0.0, 1.0)
    }

    /// Get `white` color as [`ColorRgba`].
    pub fn white() -> Self {
        Self::new_opaque_rgb(1.0, 1.0, 1.0)
    }

    /// Get `lime` color as [`ColorRgba`].
    pub fn lime() -> Self {
        Self::new_opaque_rgb(0.0, 1.0, 0.0)
    }

    /// Get `green` color as [`ColorRgba`].
    pub fn green() -> Self {
        Self::new_opaque_rgb(0.0, 0.5, 0.0)
    }

    /// Get `navy` color as [`ColorRgba`].
    pub fn navy() -> Self {
        Self::new_opaque_rgb(0.0, 0.0, 0.5)
    }

    /// Get `blue` color as [`ColorRgba`].
    pub fn blue() -> Self {
        Self::new_opaque_rgb(0.0, 0.0, 1.0)
    }

    /// Get `aqua` color as [`ColorRgba`].
    pub fn aqua() -> Self {
        Self::new_opaque_rgb(0.0, 1.0, 1.0)
    }

    /// Get `teal` color as [`ColorRgba`].
    pub fn teal() -> Self {
        Self::new_opaque_rgb(0.0, 0.5, 0.5)
    }

    /// Get `black` color as [`ColorRgba`].
    pub fn black() -> Self {
        Self::new_opaque_rgb(0.0, 0.0, 0.0)
    }

    /// Get `silver` color as [`ColorRgba`].
    pub fn silver() -> Self {
        let v = u8_to_f32(0xc0);
        Self::new_opaque_rgb(v, v, v)
    }

    /// Get `gray` color as [`ColorRgba`].
    pub fn gray() -> Self {
        Self::new_opaque_rgb(0.5, 0.5, 0.5)
    }
}

fn u8_to_f32(v: u8) -> f32 {
    ((v as f32) / 255.0).clamp(0.0, 1.0)
}
