use crate::Vec4;

/// Represents alpha enabled color but using u8 range, from 0 to 255.
///
/// # Note
///
/// * See [`ColorRgba`].
#[derive(Debug, Clone, Copy, Default, Eq, Hash, PartialEq)]
pub struct ColorRgbaU8([u8; 4]);

impl ColorRgbaU8 {
    /// Create new color [`ColorRgbaU8`].
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{ColorRgbaU8};
    ///
    /// let color = ColorRgbaU8::new(255, 128, 96, 32);
    /// assert_eq!(color.r(), 255);
    /// assert_eq!(color.g(), 128);
    /// assert_eq!(color.b(), 96);
    /// assert_eq!(color.a(), 32);
    /// ```
    #[inline(always)]
    pub const fn new(r: u8, g: u8, b: u8, a: u8) -> Self { Self([r, g, b, a]) }

    /// Create new color but opaque (non-transparent).
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{ColorRgbaU8};
    ///
    /// let color = ColorRgbaU8::new_opaque_rgb(255, 128, 64);
    /// assert_eq!(color.r(), 255);
    /// assert_eq!(color.g(), 128);
    /// assert_eq!(color.b(), 64);
    /// assert_eq!(color.a(), 255);
    /// ```
    #[inline(always)]
    pub const fn new_opaque_rgb(r: u8, g: u8, b: u8) -> Self { Self([r, g, b, 255]) }

    /// Get red channel component color value.
    #[inline(always)]
    pub const fn r(&self) -> u8 { self.0[0] }

    /// Get green channel component color value.
    #[inline(always)]
    pub const fn g(&self) -> u8 { self.0[1] }

    /// Get blue channel component color value.
    #[inline(always)]
    pub const fn b(&self) -> u8 { self.0[2] }

    /// Get alpha channel component color value.
    #[inline(always)]
    pub const fn a(&self) -> u8 { self.0[3] }

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
    /// use math::{ColorRgbaU8};
    ///
    /// let color = ColorRgbaU8::new_opaque_rgb(206, 177, 34);
    /// let luminance = color.y();
    /// ```
    pub fn y(&self) -> f32 {
        let v: ColorRgba = self.into();
        v.y()
    }

    // ------------------------------------------------------------------------
    //
    // COLOR PALETTES
    //
    // ------------------------------------------------------------------------

    /// Get `maroon` color as [`ColorRgba`].
    #[inline]
    pub const fn maroon() -> Self { Self::new_opaque_rgb(128, 0, 0) }

    /// Get `red` color as [`ColorRgba`].
    #[inline]
    pub const fn red() -> Self { Self::new_opaque_rgb(255, 0, 0) }

    /// Get `orange` color as [`ColorRgba`].
    #[inline]
    pub const fn orange() -> Self { Self::new_opaque_rgb(255, 0xa5, 0) }

    /// Get `yellow` color as [`ColorRgba`].
    #[inline]
    pub const fn yellow() -> Self { Self::new_opaque_rgb(255, 255, 0) }

    /// Get `olive` color as [`ColorRgba`].
    #[inline]
    pub const fn olive() -> Self { Self::new_opaque_rgb(128, 128, 0) }

    /// Get `purple` color as [`ColorRgba`].
    #[inline]
    pub const fn purple() -> Self { Self::new_opaque_rgb(128, 0, 128) }

    /// Get `fuchsia` color as [`ColorRgba`].
    #[inline]
    pub const fn fuchsia() -> Self { Self::new_opaque_rgb(255, 0, 255) }

    /// Get `white` color as [`ColorRgba`].
    #[inline]
    pub const fn white() -> Self { Self::new_opaque_rgb(255, 255, 255) }

    /// Get `lime` color as [`ColorRgba`].
    #[inline]
    pub const fn lime() -> Self { Self::new_opaque_rgb(0, 255, 0) }

    /// Get `green` color as [`ColorRgba`].
    #[inline]
    pub const fn green() -> Self { Self::new_opaque_rgb(0, 128, 0) }

    /// Get `navy` color as [`ColorRgba`].
    #[inline]
    pub const fn navy() -> Self { Self::new_opaque_rgb(0, 0, 128) }

    /// Get `blue` color as [`ColorRgba`].
    #[inline]
    pub const fn blue() -> Self { Self::new_opaque_rgb(0, 0, 255) }

    /// Get `aqua` color as [`ColorRgba`].
    #[inline]
    pub const fn aqua() -> Self { Self::new_opaque_rgb(0, 255, 255) }

    /// Get `teal` color as [`ColorRgba`].
    #[inline]
    pub const fn teal() -> Self { Self::new_opaque_rgb(0, 128, 128) }

    /// Get `black` color as [`ColorRgba`].
    #[inline]
    pub const fn black() -> Self { Self::new_opaque_rgb(0, 0, 0) }

    /// Get `silver` color as [`ColorRgba`].
    #[inline]
    pub const fn silver() -> Self { Self::new_opaque_rgb(0xc0, 0xc0, 0xc0) }

    /// Get `gray` color as [`ColorRgba`].
    #[inline]
    pub const fn gray() -> Self { Self::new_opaque_rgb(128, 128, 128) }
}

impl From<ColorRgba> for ColorRgbaU8 {
    fn from(v: ColorRgba) -> Self {
        Self::new(
            ((v.r().clamp(0f32, 1f32) * 255f32) as u16).clamp(0, 255) as u8,
            ((v.g().clamp(0f32, 1f32) * 255f32) as u16).clamp(0, 255) as u8,
            ((v.b().clamp(0f32, 1f32) * 255f32) as u16).clamp(0, 255) as u8,
            ((v.a().clamp(0f32, 1f32) * 255f32) as u16).clamp(0, 255) as u8,
        )
    }
}

impl From<&mut ColorRgba> for ColorRgbaU8 {
    fn from(v: &mut ColorRgba) -> Self {
        Self::new(
            ((v.r().clamp(0f32, 1f32) * 255f32) as u16).clamp(0, 255) as u8,
            ((v.g().clamp(0f32, 1f32) * 255f32) as u16).clamp(0, 255) as u8,
            ((v.b().clamp(0f32, 1f32) * 255f32) as u16).clamp(0, 255) as u8,
            ((v.a().clamp(0f32, 1f32) * 255f32) as u16).clamp(0, 255) as u8,
        )
    }
}

impl From<&ColorRgba> for ColorRgbaU8 {
    fn from(v: &ColorRgba) -> Self {
        Self::new(
            ((v.r().clamp(0f32, 1f32) * 255f32) as u16).clamp(0, 255) as u8,
            ((v.g().clamp(0f32, 1f32) * 255f32) as u16).clamp(0, 255) as u8,
            ((v.b().clamp(0f32, 1f32) * 255f32) as u16).clamp(0, 255) as u8,
            ((v.a().clamp(0f32, 1f32) * 255f32) as u16).clamp(0, 255) as u8,
        )
    }
}

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
/// * See <https://docs.microsoft.com/en-us/windows/win32/api/dxgiformat/ne-dxgiformat-dxgi_format>
/// * See [`ColorRgbaU8`].
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
    pub fn r(&self) -> f32 { self.data.x() }

    /// Get green channel component color value.
    #[inline]
    pub fn g(&self) -> f32 { self.data.y() }

    /// Get blue channel component color value.
    #[inline]
    pub fn b(&self) -> f32 { self.data.z() }

    ///
    #[inline]
    pub fn a(&self) -> f32 { self.data.w() }

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
    #[inline(always)]
    pub fn maroon() -> Self { Self::new_opaque_rgb(0.5, 0.0, 0.0) }

    /// Get `red` color as [`ColorRgba`].
    #[inline(always)]
    pub fn red() -> Self { Self::new_opaque_rgb(1.0, 0.0, 0.0) }

    /// Get `orange` color as [`ColorRgba`].
    #[inline(always)]
    pub fn orange() -> Self { Self::new_opaque_rgb(1.0, u8_to_f32(0xa5), 0.0) }

    /// Get `yellow` color as [`ColorRgba`].
    #[inline(always)]
    pub fn yellow() -> Self { Self::new_opaque_rgb(1.0, 1.0, 0.0) }

    /// Get `olive` color as [`ColorRgba`].
    #[inline(always)]
    pub fn olive() -> Self { Self::new_opaque_rgb(0.5, 0.5, 0.0) }

    /// Get `purple` color as [`ColorRgba`].
    #[inline(always)]
    pub fn purple() -> Self { Self::new_opaque_rgb(0.5, 0.0, 0.5) }

    /// Get `fuchsia` color as [`ColorRgba`].
    #[inline(always)]
    pub fn fuchsia() -> Self { Self::new_opaque_rgb(1.0, 0.0, 1.0) }

    /// Get `white` color as [`ColorRgba`].
    #[inline(always)]
    pub fn white() -> Self { Self::new_opaque_rgb(1.0, 1.0, 1.0) }

    /// Get `lime` color as [`ColorRgba`].
    #[inline(always)]
    pub fn lime() -> Self { Self::new_opaque_rgb(0.0, 1.0, 0.0) }

    /// Get `green` color as [`ColorRgba`].
    #[inline(always)]
    pub fn green() -> Self { Self::new_opaque_rgb(0.0, 0.5, 0.0) }

    /// Get `navy` color as [`ColorRgba`].
    #[inline(always)]
    pub fn navy() -> Self { Self::new_opaque_rgb(0.0, 0.0, 0.5) }

    /// Get `blue` color as [`ColorRgba`].
    #[inline(always)]
    pub fn blue() -> Self { Self::new_opaque_rgb(0.0, 0.0, 1.0) }

    /// Get `aqua` color as [`ColorRgba`].
    #[inline(always)]
    pub fn aqua() -> Self { Self::new_opaque_rgb(0.0, 1.0, 1.0) }

    /// Get `teal` color as [`ColorRgba`].
    #[inline(always)]
    pub fn teal() -> Self { Self::new_opaque_rgb(0.0, 0.5, 0.5) }

    /// Get `black` color as [`ColorRgba`].
    #[inline(always)]
    pub fn black() -> Self { Self::new_opaque_rgb(0.0, 0.0, 0.0) }

    /// Get `silver` color as [`ColorRgba`].
    #[inline(always)]
    pub fn silver() -> Self {
        let v = u8_to_f32(0xc0);
        Self::new_opaque_rgb(v, v, v)
    }

    /// Get `gray` color as [`ColorRgba`].
    #[inline(always)]
    pub fn gray() -> Self { Self::new_opaque_rgb(0.5, 0.5, 0.5) }
}

impl From<&mut ColorRgbaU8> for ColorRgba {
    fn from(v: &mut ColorRgbaU8) -> Self {
        let f = 255f32.recip();
        Self::new(
            (v.r() as f32) * f,
            (v.g() as f32) * f,
            (v.b() as f32) * f,
            (v.a() as f32) * f,
        )
    }
}

impl From<&ColorRgbaU8> for ColorRgba {
    fn from(v: &ColorRgbaU8) -> Self {
        let f = 255f32.recip();
        Self::new(
            (v.r() as f32) * f,
            (v.g() as f32) * f,
            (v.b() as f32) * f,
            (v.a() as f32) * f,
        )
    }
}

impl From<ColorRgbaU8> for ColorRgba {
    fn from(v: ColorRgbaU8) -> Self {
        let f = 255f32.recip();
        Self::new(
            (v.r() as f32) * f,
            (v.g() as f32) * f,
            (v.b() as f32) * f,
            (v.a() as f32) * f,
        )
    }
}

fn u8_to_f32(v: u8) -> f32 { ((v as f32) / 255.0).clamp(0.0, 1.0) }
