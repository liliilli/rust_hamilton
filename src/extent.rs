use crate::EError;

// ----------------------------------------------------------------------------
//
// EXTENT2
//
// ----------------------------------------------------------------------------

/// Represents extent with 2-axis (width, height).
///
/// Internal `width` and `height` always contain 0 or positive value.
#[derive(Debug, Copy, Clone, PartialEq)]
pub struct Extent2 {
    width: f32,
    height: f32,
}

impl Extent2 {
    /// Create new [Extent2] but not check given `width` and `height` is negative.
    /// If any value is negative, the application will be halted instantly.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Extent2;
    ///
    /// let extent = Extent2::uncheck_new(32f32, 17.6f32);
    /// assert_eq!(extent.width(), 32f32);
    /// assert_eq!(extent.height(), 17.6f32);
    /// ```
    ///
    /// ``` should_panic
    /// use hamilton as math;
    /// use math::Extent2;
    ///
    /// let _panicked = Extent2::uncheck_new(-1f32, 1f32);
    /// ```
    pub fn uncheck_new(width: f32, height: f32) -> Self {
        assert!(width >= 0f32 && height >= 0f32);
        Self { width, height }
    }

    /// Create new [Extent2] but check given `width` and `height` are positvie or 0.
    /// If any value is negative, return error value instead.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Extent2;
    ///
    /// let extent = Extent2::new(32f32, 17.6f32).unwrap();
    /// assert_eq!(extent.width(), 32f32);
    /// assert_eq!(extent.height(), 17.6f32);
    /// ```
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Extent2;
    ///
    /// let should_err = Extent2::new(-1f32, 1f32).is_err();
    /// assert_eq!(should_err, true);
    /// ```
    pub fn new(width: f32, height: f32) -> Result<Self, EError> {
        if width < 0f32 {
            Err(EError::NegativeLength(width))
        } else if height < 0f32 {
            Err(EError::NegativeLength(height))
        } else {
            Ok(Self::uncheck_new(width, height))
        }
    }

    /// Create new [Extent2] but not check whether given `length` is negative or not.
    /// If value is negative, the application will be halted instantly.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Extent2;
    ///
    /// let extent = Extent2::uncheck_from_scalar(32f32);
    /// assert_eq!(extent.width(), 32f32);
    /// assert_eq!(extent.height(), 32f32);
    /// ```
    ///
    /// ``` should_panic
    /// use hamilton as math;
    /// use math::Extent2;
    ///
    /// let _panicked = Extent2::uncheck_from_scalar(-1f32);
    /// ```
    pub fn uncheck_from_scalar(length: f32) -> Self {
        Self::uncheck_new(length, length)
    }

    /// Create new [Extent2] but check given `length` is positive or 0.
    /// If any value is negative, return error value instead.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Extent2;
    ///
    /// let extent = Extent2::from_scalar(32f32).unwrap();
    /// assert_eq!(extent.width(), 32f32);
    /// assert_eq!(extent.height(), 32f32);
    /// ```
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Extent2;
    ///
    /// let should_err = Extent2::from_scalar(-1f32).is_err();
    /// assert_eq!(should_err, true);
    /// ```
    pub fn from_scalar(length: f32) -> Result<Self, EError> {
        Self::new(length, length)
    }

    /// Return `width` value of the extent.
    pub fn width(&self) -> f32 {
        self.width
    }

    /// Return `height` value of the extent.
    pub fn height(&self) -> f32 {
        self.height
    }

    /// Return area value of this extent.
    pub fn area(&self) -> f32 {
        self.width * self.height
    }

    /// Convert into [IExtent2] but any fractional values are truncated.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Extent2, IExtent2};
    ///
    /// let iextent = Extent2::new(0.25f32, 11.5f32).unwrap().to_iextent2_floor_lossy();
    /// assert_eq!(iextent, IExtent2::new(0u32, 11u32));
    /// ```
    pub fn to_iextent2_floor_lossy(&self) -> IExtent2 {
        IExtent2::new(self.width.floor() as u32, self.height.floor() as u32)
    }

    /// Convert into [IExtent2] but any fractional values are ceiled into closest integer.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Extent2, IExtent2};
    ///
    /// let iextent = Extent2::new(0.25f32, 11.5f32).unwrap().to_iextent2_ceil_lossy();
    /// assert_eq!(iextent, IExtent2::new(1u32, 12u32));
    /// ```
    pub fn to_iextent2_ceil_lossy(&self) -> IExtent2 {
        IExtent2::new(self.width.ceil() as u32, self.height.ceil() as u32)
    }
}

/// Represents extent with 2-axis (width, height) but use [u32] instead of [f32].
///
/// `width` and `height` always contain 0 or positive value.
#[derive(Debug, Copy, Clone, PartialEq)]
pub struct IExtent2 {
    width: u32,
    height: u32,
}

impl IExtent2 {
    /// Create new [IExtent2].
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::IExtent2;
    ///
    /// let extent = IExtent2::new(32, 17);
    /// assert_eq!(extent.width(), 32);
    /// assert_eq!(extent.height(), 17);
    /// ```
    pub fn new(width: u32, height: u32) -> Self {
        Self { width, height }
    }

    /// Create new [IExtent2]
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::IExtent2;
    ///
    /// let extent = IExtent2::from_scalar(32);
    /// assert_eq!(extent.width(), 32);
    /// assert_eq!(extent.height(), 32);
    /// ```
    pub fn from_scalar(length: u32) -> Self {
        Self::new(length, length)
    }

    /// Return `width` value of the extent.
    pub fn width(&self) -> u32 {
        self.width
    }

    /// Return `height` value of the extent.
    pub fn height(&self) -> u32 {
        self.height
    }

    /// Get area of extent.
    pub fn area(&self) -> u64 {
        (self.width as u64) * (self.height as u64)
    }
}

impl From<IExtent2> for Extent2 {
    /// Convert [IExtent2] into [Extent2].
    fn from(extent: IExtent2) -> Extent2 {
        Self::uncheck_new(extent.width() as f32, extent.height() as f32)
    }
}

// ----------------------------------------------------------------------------
//
// EXTENT3
//
// ----------------------------------------------------------------------------

/// Represents extent with 3-axis (width, height).
///
/// Internal `width`, `height` and `depth` always contain 0 or positive value.
#[derive(Debug, Copy, Clone, PartialEq)]
pub struct Extent3 {
    width: f32,
    height: f32,
    depth: f32,
}

impl Extent3 {
    /// Create new [Extent3] but not check given `width`, `height`, and 'depth' is negative.
    /// If any value of these is negative, the application will be halted instantly.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Extent3;
    ///
    /// let extent = Extent3::uncheck_new(33f32, 17.6f32, 4.25f32);
    /// assert_eq!(extent.width(), 33f32);
    /// assert_eq!(extent.height(), 17.6f32);
    /// assert_eq!(extent.depth(), 4.25f32);
    /// ```
    ///
    /// ``` should_panic
    /// use hamilton as math;
    /// use math::Extent3;
    ///
    /// let _panicked = Extent3::uncheck_new(-1f32, 1f32, 6f32);
    /// ```
    pub fn uncheck_new(width: f32, height: f32, depth: f32) -> Self {
        assert!(width >= 0f32 && height >= 0f32 && depth >= 0f32);
        Self {
            width,
            height,
            depth,
        }
    }

    /// Create new [Extent3] but check given `width` and `height` are positvie or 0.
    /// If any value is negative, return error value instead.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Extent3;
    ///
    /// let extent = Extent3::new(33f32, 17.6f32, 4.25f32).unwrap();
    /// assert_eq!(extent.width(), 33f32);
    /// assert_eq!(extent.height(), 17.6f32);
    /// assert_eq!(extent.depth(), 4.25f32);
    /// ```
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Extent3;
    ///
    /// let should_err = Extent3::new(-1f32, 1f32, 6f32).is_err();
    /// assert_eq!(should_err, true);
    /// ```
    pub fn new(width: f32, height: f32, depth: f32) -> Result<Self, EError> {
        if width < 0f32 {
            Err(EError::NegativeLength(width))
        } else if height < 0f32 {
            Err(EError::NegativeLength(height))
        } else if depth < 0f32 {
            Err(EError::NegativeLength(depth))
        } else {
            Ok(Self::uncheck_new(width, height, depth))
        }
    }

    /// Create new [Extent3] but not check whether given `length` is negative or not.
    /// If value is negative, the application will be halted instantly.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Extent3;
    ///
    /// let extent = Extent3::uncheck_from_scalar(32f32);
    /// assert_eq!(extent.width(), 32f32);
    /// assert_eq!(extent.height(), 32f32);
    /// assert_eq!(extent.depth(), 32f32);
    /// ```
    ///
    /// ``` should_panic
    /// use hamilton as math;
    /// use math::Extent3;
    ///
    /// let _panicked = Extent3::uncheck_from_scalar(-1f32);
    /// ```
    pub fn uncheck_from_scalar(length: f32) -> Self {
        Self::uncheck_new(length, length, length)
    }

    /// Create new [Extent3] but check given `length` is positive or 0.
    /// If any value is negative, return error value instead.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Extent3;
    ///
    /// let extent = Extent3::from_scalar(32f32).unwrap();
    /// assert_eq!(extent.width(), 32f32);
    /// assert_eq!(extent.height(), 32f32);
    /// assert_eq!(extent.depth(), 32f32);
    /// ```
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Extent3;
    ///
    /// let should_err = Extent3::from_scalar(-1f32).is_err();
    /// assert_eq!(should_err, true);
    /// ```
    pub fn from_scalar(length: f32) -> Result<Self, EError> {
        Self::new(length, length, length)
    }

    /// Return `width` value of the extent.
    pub fn width(&self) -> f32 {
        self.width
    }

    /// Return `height` value of the extent.
    pub fn height(&self) -> f32 {
        self.height
    }

    /// Return `depth` value of the extent.
    pub fn depth(&self) -> f32 {
        self.depth
    }

    /// Get surface area of the extent.
    pub fn surface_area(&self) -> f32 {
        2f32 * ((self.width * self.height) + (self.height * self.depth) + (self.depth * self.width))
    }

    /// Get volume of the extent.
    pub fn volume(&self) -> f32 {
        self.width * self.height * self.depth
    }

    /// Convert into [IExtent3] but any fractional values are truncated.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Extent3, IExtent3};
    ///
    /// let iextent = Extent3::new(0.35f32, 11.5f32, 7.25f32).unwrap().to_iextent3_floor_lossy();
    /// assert_eq!(iextent, IExtent3::new(0u32, 11u32, 7u32));
    /// ```
    pub fn to_iextent3_floor_lossy(&self) -> IExtent3 {
        IExtent3::new(
            self.width.floor() as u32,
            self.height.floor() as u32,
            self.depth.floor() as u32,
        )
    }

    /// Convert into [IExtent3] but any fractional values are ceiled into closest integer.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Extent3, IExtent3};
    ///
    /// let iextent = Extent3::new(0.35f32, 11.5f32, 7.25f32).unwrap().to_iextent3_ceil_lossy();
    /// assert_eq!(iextent, IExtent3::new(1u32, 12u32, 8u32));
    /// ```
    pub fn to_iextent3_ceil_lossy(&self) -> IExtent3 {
        IExtent3::new(
            self.width.ceil() as u32,
            self.height.ceil() as u32,
            self.depth.ceil() as u32,
        )
    }
}

/// Represents extent with 3-axis (width, height, and depth) but use [u32] instead of [f32].
///
/// `width`, `height` and `depth` always contain 0 or positive value.
#[derive(Debug, Copy, Clone, PartialEq)]
pub struct IExtent3 {
    width: u32,
    height: u32,
    depth: u32,
}

impl IExtent3 {
    /// Create new [IExtent3].
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::IExtent3;
    ///
    /// let extent = IExtent3::new(33, 17, 0);
    /// assert_eq!(extent.width(), 33);
    /// assert_eq!(extent.height(), 17);
    /// assert_eq!(extent.depth(), 0);
    /// ```
    pub fn new(width: u32, height: u32, depth: u32) -> Self {
        Self {
            width,
            height,
            depth,
        }
    }

    /// Create new [IExtent3]
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::IExtent3;
    ///
    /// let extent = IExtent3::from_scalar(32);
    /// assert_eq!(extent.width(), 32);
    /// assert_eq!(extent.height(), 32);
    /// assert_eq!(extent.depth(), 32);
    /// ```
    pub fn from_scalar(length: u32) -> Self {
        Self::new(length, length, length)
    }

    /// Return `width` value of the extent.
    pub fn width(&self) -> u32 {
        self.width
    }

    /// Return `height` value of the extent.
    pub fn height(&self) -> u32 {
        self.height
    }

    /// Return `depth` value of the extent.
    pub fn depth(&self) -> u32 {
        self.depth
    }

    /// Get surface area of the extent.
    pub fn surface_area(&self) -> u64 {
        let width = self.width as u64;
        let height = self.height as u64;
        let depth = self.depth as u64;

        2u64 * ((width * height) + (height * depth) + (depth * width))
    }

    /// Get volume of extent.
    pub fn volume(&self) -> u64 {
        (self.width as u64) * (self.height as u64) * (self.depth as u64)
    }
}

impl From<IExtent3> for Extent3 {
    /// Convert [IExtent3] into [Extent3].
    fn from(extent: IExtent3) -> Extent3 {
        Self::uncheck_new(
            extent.width() as f32,
            extent.height() as f32,
            extent.depth() as f32,
        )
    }
}
