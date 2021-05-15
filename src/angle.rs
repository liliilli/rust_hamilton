use std::{f32::consts::PI, ops};

/// Wrap value into `max`.
///
pub fn wrap_max(val: f32, max: f32) -> f32 { (max + (val % max)) % max }

/// Wrap given value from `min` to `max`.
///
pub fn wrap_min_max(val: f32, min: f32, max: f32) -> f32 { min + wrap_max(val - min, max - min) }

/// Represents degree angle.
#[derive(Copy, Clone)]
pub struct Degree(pub f32);

impl Degree {
    /// Normalize degree angle value into `[-180, 180)` value.
    pub fn into_normalized(self) -> Self { Self(wrap_min_max(*self, -180f32, 180f32)) }
}

impl ops::Deref for Degree {
    type Target = f32;

    fn deref(&self) -> &Self::Target { &self.0 }
}

impl From<Radian> for Degree {
    fn from(radian: Radian) -> Self { Degree(*radian * 180f32 / PI) }
}

impl ops::Add for Degree {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output { Degree(*self + *rhs) }
}

impl ops::AddAssign for Degree {
    fn add_assign(&mut self, rhs: Self) { self.0 += *rhs; }
}

impl ops::Sub for Degree {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output { Degree(*self - *rhs) }
}

impl ops::SubAssign for Degree {
    fn sub_assign(&mut self, rhs: Self) { self.0 -= *rhs; }
}

impl ops::Mul<u8> for Degree {
    type Output = Self;

    fn mul(self, rhs: u8) -> Self::Output { Degree(*self * (rhs as f32)) }
}

impl ops::Mul<u16> for Degree {
    type Output = Self;

    fn mul(self, rhs: u16) -> Self::Output { Degree(*self * (rhs as f32)) }
}

impl ops::Mul<u32> for Degree {
    type Output = Self;

    fn mul(self, rhs: u32) -> Self::Output { Degree(*self * (rhs as f32)) }
}

impl ops::Mul<usize> for Degree {
    type Output = Self;

    fn mul(self, rhs: usize) -> Self::Output { Degree(*self * (rhs as f32)) }
}

impl ops::Mul<i8> for Degree {
    type Output = Self;

    fn mul(self, rhs: i8) -> Self::Output { Degree(*self * (rhs as f32)) }
}

impl ops::Mul<i16> for Degree {
    type Output = Self;

    fn mul(self, rhs: i16) -> Self::Output { Degree(*self * (rhs as f32)) }
}

impl ops::Mul<i32> for Degree {
    type Output = Self;

    fn mul(self, rhs: i32) -> Self::Output { Degree(*self * (rhs as f32)) }
}

impl ops::Mul<isize> for Degree {
    type Output = Self;

    fn mul(self, rhs: isize) -> Self::Output { Degree(*self * (rhs as f32)) }
}

impl ops::Mul<f32> for Degree {
    type Output = Self;

    fn mul(self, rhs: f32) -> Self::Output { Degree(*self * rhs) }
}

/// Represents radian angle.
#[derive(Copy, Clone)]
pub struct Radian(pub f32);

impl Radian {
    /// Normalize degree angle value into `[-PI, PI)` value.
    pub fn into_normalized(self) -> Self { Self(wrap_min_max(*self, -PI, PI)) }
}

impl ops::Deref for Radian {
    type Target = f32;

    fn deref(&self) -> &Self::Target { &self.0 }
}

impl From<Degree> for Radian {
    fn from(degree: Degree) -> Self { Radian(*degree * PI / 180f32) }
}

impl ops::Add for Radian {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output { Radian(*self + *rhs) }
}

impl ops::AddAssign for Radian {
    fn add_assign(&mut self, rhs: Self) { self.0 += *rhs; }
}

impl ops::Sub for Radian {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output { Radian(*self - *rhs) }
}

impl ops::SubAssign for Radian {
    fn sub_assign(&mut self, rhs: Self) { self.0 -= *rhs; }
}
