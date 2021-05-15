use std::primitive::{f32, f64, i16, i32, i64, i8, isize, u16, u32, u64, u8, usize};

/// Trait for wrapping original value into new value which is in range `[Default, max)`.
///
/// Implementing struct must implement or derive of [Copy], and [Clone] trait.
///
/// # Examples
///
/// ```
/// use hamilton as math;
/// use math::RangeWrappable;
///
/// #[derive(Debug, Copy, Clone, PartialEq)]
/// struct Index2 {
///     x: u32,
///     y: u32,
/// }
///
/// impl RangeWrappable for Index2 {
///     fn to_wrap_max(&self, max: Index2) -> Self {
///         Self {
///             x: self.x.to_wrap_max(max.x),
///             y: self.y.to_wrap_max(max.y)
///         }
///     }
/// }
///
/// let index = Index2{x: 10, y: 8};
/// assert_eq!(index.to_wrap_max(Index2{x: 3, y: 6}), Index2{x: 1, y: 2});
/// ```
pub trait RangeWrappable
where Self: Clone + Copy
{
    fn to_wrap_max(&self, max: Self) -> Self;
}

/// Trait for wrapping original value into new value which is in range `[min, max)`.
///
/// Implementing struct must implement or derive of [Copy], [Clone] and [RangeWrappable] trait.
///
/// # Examples
///
/// ```
/// use hamilton as math;
/// use math::{RangeWrappable, RangeWrappableMinMax};
///
/// #[derive(Debug, Copy, Clone, PartialEq)]
/// struct Offset2 {
///     x: i32,
///     y: i32,
/// }
///
/// impl RangeWrappable for Offset2 {
///     fn to_wrap_max(&self, max: Self) -> Self {
///         Self {
///             x: self.x.to_wrap_max(max.x),
///             y: self.y.to_wrap_max(max.y)
///         }
///     }
/// }
///
/// impl RangeWrappableMinMax for Offset2 {
///     fn to_wrap_min_max(&self, min: Self, max: Self) -> Self {
///         Self {
///             x: self.x.to_wrap_min_max(min.x, max.x),
///             y: self.y.to_wrap_min_max(min.y, max.y)
///         }
///     }
/// }
///
/// let offset = Offset2{x: 10, y: 8};
/// assert_eq!(offset.to_wrap_min_max(Offset2{x: 5, y: 0}, Offset2{x: 10, y: 5}), Offset2{x: 5, y: 3});
/// ```
pub trait RangeWrappableMinMax: RangeWrappable
where Self: Clone + Copy
{
    fn to_wrap_min_max(&self, min: Self, max: Self) -> Self;
}

/// Implement [RangeWrappable] to all arithmetic types.
macro_rules! op_range_wrappable_impl {
    ($($t:ty),*) => {
        $(
            impl RangeWrappable for $t {
                fn to_wrap_max(&self, max: $t) -> $t { (max + (self % max)) % max }
            }
        )*
    };
}

/// Implement [RangeWrappableMinMax] to all arithmetic types.
macro_rules! op_range_wrappable_minmax_impl {
    ($($t:ty),*) => {
        $(
            impl RangeWrappableMinMax for $t {
                fn to_wrap_min_max(&self, min: $t, max: $t) -> $t {
                    assert!(min <= max);
                    min + (self - min).to_wrap_max(max - min)
                }
            }
        )*
    };
}

op_range_wrappable_impl!(u8, u16, u32, u64, i8, i16, i32, i64, usize, isize, f32, f64);
op_range_wrappable_minmax_impl!(i8, i16, i32, i64, isize, f32, f64);

#[cfg(test)]
mod test {
    use super::*;

    macro_rules! assert_float_eq {
        ($t:ty, $lhs:expr, $rhs:expr) => {
            assert!(($lhs - $rhs).abs() <= (1e-4 as $t));
        };
    }

    #[test]
    fn safe_wrappable_test() {
        macro_rules! test_safe_wrappable_for {
            (f64, $val:expr, $mod:expr, $res:expr) => {{
                assert_float_eq!(f64, ($val as f64).to_wrap_max($mod as f64), ($res as f64));
                let value = $val as f64;
                let ref_value = &value;
                assert_float_eq!(f64, ref_value.to_wrap_max($mod as f64), ($res as f64));
            }};
            (f32, $val:expr, $mod:expr, $res:expr) => {{
                assert_float_eq!(f32, ($val as f32).to_wrap_max($mod as f32), ($res as f32));
                let value = $val as f32;
                let ref_value = &value;
                assert_float_eq!(f32, ref_value.to_wrap_max($mod as f32), ($res as f32));
            }};
            ($t:ty, $val:expr, $mod:expr, $res:expr) => {{
                assert_eq!(($val as $t).to_wrap_max($mod as $t), $res as $t);
                let value = $val as $t;
                let ref_value = &value;
                assert_eq!(ref_value.to_wrap_max($mod as $t), $res as $t);
            }};
        }

        test_safe_wrappable_for!(u8, 13, 8, 5);
        test_safe_wrappable_for!(u16, 2_836, 137, 96);
        test_safe_wrappable_for!(u32, 132_972, 27_998, 20_980);
        test_safe_wrappable_for!(u64, 132_972, 27_998, 20_980);
        test_safe_wrappable_for!(usize, 132_972, 27_998, 20_980);

        test_safe_wrappable_for!(i8, 13, 8, 5);
        test_safe_wrappable_for!(i16, 2_836, 137, 96);
        test_safe_wrappable_for!(i32, 132_972, 27_998, 20_980);
        test_safe_wrappable_for!(i64, 132_972, 27_998, 20_980);
        test_safe_wrappable_for!(isize, 132_972, 27_998, 20_980);

        test_safe_wrappable_for!(f32, 20.2916, 8.223, 3.8456);
        test_safe_wrappable_for!(f64, 20.2916, 8.223, 3.8456);
    }

    #[test]
    fn safe_wrappable_minmax_test() {
        macro_rules! test_safe_wrappable_minmax_for {
            (f64, $val:expr, $min:expr, $max:expr, $res:expr) => {{
                assert_float_eq!(
                    f64,
                    ($val as f64).to_wrap_min_max($min as f64, $max as f64),
                    ($res as f64)
                );
                let value = $val as f64;
                let ref_value = &value;
                assert_float_eq!(
                    f64,
                    ref_value.to_wrap_min_max($min as f64, $max as f64),
                    ($res as f64)
                );
            }};
            (f32, $val:expr, $min:expr, $max:expr, $res:expr) => {{
                assert_float_eq!(
                    f32,
                    ($val as f32).to_wrap_min_max($min as f32, $max as f32),
                    ($res as f32)
                );
                let value = $val as f32;
                let ref_value = &value;
                assert_float_eq!(
                    f32,
                    ref_value.to_wrap_min_max($min as f32, $max as f32),
                    ($res as f32)
                );
            }};
            ($t:ty, $val:expr, $min:expr, $max:expr, $res:expr) => {{
                assert_eq!(($val as $t).to_wrap_min_max($min as $t, $max as $t), $res as $t);
                let value = $val as $t;
                let ref_value = &value;
                assert_eq!(ref_value.to_wrap_min_max($min as $t, $max as $t), $res as $t);
            }};
        }

        test_safe_wrappable_minmax_for!(i8, -6, 8, 13, 9);
        test_safe_wrappable_minmax_for!(i16, -16, 5, 27, 6);
        test_safe_wrappable_minmax_for!(i32, 281, 37, 64, 38);
        test_safe_wrappable_minmax_for!(i64, 28361, 7719, 8160, 8075);

        test_safe_wrappable_minmax_for!(f32, 180, -180, 180, -180);
        test_safe_wrappable_minmax_for!(f64, 180, -180, 180, -180);
    }
}
