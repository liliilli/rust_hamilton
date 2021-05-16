use std::primitive::{f32, f64};

/// Provide equality feature like [PartialEq] or [Eq] but with tolerance value.
///
/// # Examples
///
/// ```
///
/// ```
pub trait NearlyEqual
where Self: Copy + Clone
{
    /// Check given value is nearly equal to given value `to` with `tolerance`.
    fn nearly_equal(&self, to: Self, tolerance: Self) -> bool;
}

/// Implement [NearlyEqual] to all floating point arithmetic types.
macro_rules! op_nearly_equal_impl {
    ($($t:ty),*) => {
        $(
            impl NearlyEqual for $t {
                fn nearly_equal(&self, to: $t, tolerance: $t) -> bool {
                    (self - to).abs() <= tolerance
                }
            }
        )*
    };
}

op_nearly_equal_impl!(f32, f64);
