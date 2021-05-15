///
macro_rules! forward_ref_binop {
    (impl $imp:ident, $method:ident for $t:ty, $u:ty) => {
        impl<'a> $imp<$u> for &'a $t {
            type Output = <$t as $imp<$u>>::Output;

            #[inline]
            fn $method(self, other: $u) -> <$t as $imp<$u>>::Output { $imp::$method(*self, other) }
        }

        impl $imp<&$u> for $t {
            type Output = <$t as $imp<$u>>::Output;

            #[inline]
            fn $method(self, other: &$u) -> <$t as $imp<$u>>::Output { $imp::$method(self, *other) }
        }

        impl $imp<&$u> for &$t {
            type Output = <$t as $imp<$u>>::Output;

            #[inline]
            fn $method(self, other: &$u) -> <$t as $imp<$u>>::Output { $imp::$method(*self, *other) }
        }
    };
}

/// Implements "T op= &U", based on "T op= U".
/// Where `U` is expected to be `Copy`able.
macro_rules! forward_ref_assign {
    (impl $imp:ident, $method:ident for $t:ty, $u:ty) => {
        impl $imp<&$u> for $t {
            #[inline]
            fn $method(&mut self, other: &$u) { $imp::$method(self, *other); }
        }
    };
}

///
macro_rules! op_binary_impl {
    ($t:ty, $imp:ident, $method:ident, $v: tt, $($i:expr)*) => {
        impl $imp for $t {
            type Output = $t;

            #[inline]
            fn $method(self, rhs: $t) -> Self {
                Self {
                    arr: [$(self.arr[$i] $v rhs.arr[$i]),*],
                }
            }
        }

        forward_ref_binop! { impl $imp, $method for $t, $t }
    };
}

///
macro_rules! op_scalar_impl_common {
    ($t:ty, $imp:ident, $method:ident, $v: tt) => {
        impl $imp<f32> for $t {
            type Output = $t;

            #[inline]
            fn $method(self, s: f32) -> Self::Output { self $v <$t>::from_scalar(s) }
        }

        impl<'a> $imp<f32> for &'a $t {
            type Output = <$t as $imp<f32>>::Output;

            #[inline]
            fn $method(self, s: f32) -> <$t as $imp<f32>>::Output { $imp::$method(*self, s) }
        }
    };
}

///
macro_rules! op_scalar_impl {
    ($t:ty, $imp:ident, $method:ident, $v: tt) => {
        op_scalar_impl_common! {$t, $imp, $method, $v}
    };
    ($t:ty, Mul, mul, *) => {
        op_scalar_impl_common! {$t, $imp, $method, *}
        forward_ref_binop! { impl Mul, mul for $t, f32 }
    };
}

///
macro_rules! op_assign_impl {
    ($t:ty, $imp:ident, $method:ident, $v: tt, $($i:expr)*) => {
        impl $imp for $t {
            #[inline]
            fn $method(&mut self, rhs: $t) {
                $(self.arr[$i] $v rhs.arr[$i]);*
            }
        }

        forward_ref_assign!{impl $imp, $method for $t, $t}
    };
}

macro_rules! op_assign_scalar_impl {
    ($t:ty, $imp:ident, $method:ident, $v: tt) => {
        impl $imp<f32> for $t {
            #[inline]
            fn $method(&mut self, s: f32) {
                 *self $v <$t>::from_scalar(s)
            }
        }

        impl $imp<&f32> for $t {
            #[inline]
            fn $method(&mut self, s: &f32) {
                 *self $v <$t>::from_scalar(*s)
            }
        }
    };
}
