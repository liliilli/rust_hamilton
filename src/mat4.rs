use crate::Vec4;
use std::{
    mem,
    ops::{Add, Index, IndexMut, Mul, Sub},
    slice,
};

/// Column major 4x4 size matrix type.
///
/// All arithmetic operations like [Add], [Sub], [Mul] are elementary operations.
/// Use explicit methods such as to do linear algebra operations.
#[derive(Debug, PartialEq, Copy, Clone)]
pub struct Mat4 {
    val: [Vec4; 4],
}

impl Mat4 {
    /// Create matrix which elements are all zeroed.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Mat4;
    /// use math::Vec4;
    ///
    /// let mat = Mat4::from_zeroed();
    /// for elems in mat.as_elements() {
    ///     assert_eq!(*elems, 0f32);
    /// }
    /// ```
    pub fn from_zeroed() -> Self {
        Self {
            val: [Vec4::default(); 4],
        }
    }

    /// Create identity matrix.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Vec4;
    /// use math::Mat4;
    ///
    /// let mat = Mat4::from_identity();
    /// for (i, col_vec) in mat.iter().enumerate() {
    ///     match i {
    ///     0 => assert_eq!(*col_vec, Vec4::new(1f32, 0f32, 0f32, 0f32)),
    ///     1 => assert_eq!(*col_vec, Vec4::new(0f32, 1f32, 0f32, 0f32)),
    ///     2 => assert_eq!(*col_vec, Vec4::new(0f32, 0f32, 1f32, 0f32)),
    ///     3 => assert_eq!(*col_vec, Vec4::new(0f32, 0f32, 0f32, 1f32)),
    ///     _ => (),
    ///     }
    /// }
    /// ```
    pub fn from_identity() -> Self {
        Self {
            val: [
                Vec4::new(1f32, 0f32, 0f32, 0f32), // Col1
                Vec4::new(0f32, 1f32, 0f32, 0f32), // Col2
                Vec4::new(0f32, 0f32, 1f32, 0f32), // Col3
                Vec4::new(0f32, 0f32, 0f32, 1f32), // Col4
            ],
        }
    }

    /// Create matrix from 16 elements arrays. Input elements are regarded as a column aligned.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Vec4, Mat4};
    ///
    /// macro_rules! f32_arr { ($($e:expr),*) => { [ $($e as f32),* ] }; }
    ///
    /// let mat = Mat4::from_elements_array(f32_arr!(1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 2, 3, 4, 1));
    /// for (i, col_vec) in mat.iter().enumerate() {
    ///     match i {
    ///     0 => assert_eq!(*col_vec, Vec4::new(1f32, 0f32, 0f32, 0f32)),
    ///     1 => assert_eq!(*col_vec, Vec4::new(0f32, 1f32, 0f32, 0f32)),
    ///     2 => assert_eq!(*col_vec, Vec4::new(0f32, 0f32, 1f32, 0f32)),
    ///     3 => assert_eq!(*col_vec, Vec4::new(2f32, 3f32, 4f32, 1f32)),
    ///     _ => (),
    ///     }
    /// }
    /// ```
    pub fn from_elements_array(elements: [f32; 16]) -> Self {
        let e = &elements;
        Self {
            val: [
                Vec4::new(e[0], e[1], e[2], e[3]),
                Vec4::new(e[4], e[5], e[6], e[7]),
                Vec4::new(e[8], e[9], e[10], e[11]),
                Vec4::new(e[12], e[13], e[14], e[15]),
            ],
        }
    }

    /// Create matrix from 4 column arrays.
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Vec4, Mat4};
    ///
    /// macro_rules! f32_arr { ($($e:expr),*) => { [ $($e as f32),* ] }; }
    ///
    /// let mat = Mat4::from_column_arrays(
    ///     f32_arr!(1, 0, 0, 0),
    ///     f32_arr!(0, 1, 0, 0),
    ///     f32_arr!(0, 0, 1, 0),
    ///     f32_arr!(2, 3, 4, 1)
    /// );
    /// for (i, col_vec) in mat.iter().enumerate() {
    ///     match i {
    ///     0 => assert_eq!(*col_vec, Vec4::new(1f32, 0f32, 0f32, 0f32)),
    ///     1 => assert_eq!(*col_vec, Vec4::new(0f32, 1f32, 0f32, 0f32)),
    ///     2 => assert_eq!(*col_vec, Vec4::new(0f32, 0f32, 1f32, 0f32)),
    ///     3 => assert_eq!(*col_vec, Vec4::new(2f32, 3f32, 4f32, 1f32)),
    ///     _ => (),
    ///     }
    /// }
    /// ```
    pub fn from_column_arrays(col0: [f32; 4], col1: [f32; 4], col2: [f32; 4], col3: [f32; 4]) -> Self {
        Self {
            val: [
                Vec4::from_array(col0),
                Vec4::from_array(col1),
                Vec4::from_array(col2),
                Vec4::from_array(col3),
            ],
        }
    }

    /// Create matrix from 4 column vec4s.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Vec4, Mat4};
    ///
    /// let mat = Mat4::from_column_vec4s(
    ///     Vec4::new(1f32, 0f32, 0f32, 0f32),
    ///     Vec4::new(0f32, 1f32, 0f32, 0f32),
    ///     Vec4::new(0f32, 0f32, 1f32, 0f32),
    ///     Vec4::new(2f32, 3f32, 4f32, 1f32),
    /// );
    /// for (i, col_vec) in mat.iter().enumerate() {
    ///     match i {
    ///     0 => assert_eq!(*col_vec, Vec4::new(1f32, 0f32, 0f32, 0f32)),
    ///     1 => assert_eq!(*col_vec, Vec4::new(0f32, 1f32, 0f32, 0f32)),
    ///     2 => assert_eq!(*col_vec, Vec4::new(0f32, 0f32, 1f32, 0f32)),
    ///     3 => assert_eq!(*col_vec, Vec4::new(2f32, 3f32, 4f32, 1f32)),
    ///     _ => (),
    ///     }
    /// }
    /// ```
    pub fn from_column_vec4s(col0: Vec4, col1: Vec4, col2: Vec4, col3: Vec4) -> Self {
        Self {
            val: [col0, col1, col2, col3],
        }
    }

    /// Create new transposed matrix.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Vec4, Mat4};
    ///
    /// macro_rules! f32_arr { ($($e:expr),*) => { [ $($e as f32),* ] }; }
    ///
    /// let mat = Mat4::from_elements_array(
    ///     f32_arr!(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15)
    /// );
    /// let tmat = mat.to_transposed();
    /// for (i, col_vec) in tmat.iter().enumerate() {
    ///     match i {
    ///     0 => assert_eq!(*col_vec, Vec4::new(0f32, 4f32, 8f32, 12f32)),
    ///     1 => assert_eq!(*col_vec, Vec4::new(1f32, 5f32, 9f32, 13f32)),
    ///     2 => assert_eq!(*col_vec, Vec4::new(2f32, 6f32, 10f32, 14f32)),
    ///     3 => assert_eq!(*col_vec, Vec4::new(3f32, 7f32, 11f32, 15f32)),
    ///     _ => (),
    ///     }
    /// }
    /// ```
    ///
    /// # Todos
    ///
    /// * Support SSE _MM_TRANSPOSE4_PS for the fast transpose.
    pub fn to_transposed(&self) -> Self {
        let elems = self.as_elements();
        Self::from_elements_array([
            elems[0], elems[4], elems[8], elems[12], elems[1], elems[5], elems[9], elems[13], elems[2], elems[6],
            elems[10], elems[14], elems[3], elems[7], elems[11], elems[15],
        ])
    }

    /// Get determinant of full matrix.
    ///
    /// This method does not regard matrix as homogeneous coordinate transform,
    /// so maybe slower than transform version.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Vec4, Mat4};
    ///
    /// macro_rules! f32_arr { ($($e:expr),*) => { [ $($e as f32),* ] }; }
    ///
    /// let mat = Mat4::from_elements_array(
    ///     f32_arr!(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15)
    /// );
    /// assert_eq!(mat.determinant(), 0f32);
    /// assert_eq!(mat.to_transposed().determinant(), 0f32);
    ///
    /// assert_eq!(Mat4::from_identity().determinant(), 1f32);
    ///
    /// let mat = Mat4::from_elements_array(
    ///     f32_arr!(3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 1)
    /// );
    /// assert_eq!(mat.determinant(), 27f32);
    /// ```
    ///
    /// # Todos
    ///
    /// * Support SIMD for the fast operation.
    pub fn determinant(&self) -> f32 {
        let f0 = self[2][2] * self[3][3] - self[3][2] * self[2][3];
        let f1 = self[2][1] * self[3][3] - self[3][1] * self[2][3];
        let f2 = self[2][1] * self[3][2] - self[3][1] * self[2][2];
        let f3 = self[2][0] * self[3][3] - self[3][0] * self[2][3];
        let f4 = self[2][0] * self[3][2] - self[3][0] * self[2][2];
        let f5 = self[2][0] * self[3][1] - self[3][0] * self[2][1];

        let coefficient = Vec4::from_array([
            (self[1][1] * f0 - self[1][2] * f1 + self[1][3] * f2),
            (self[1][0] * f0 - self[1][2] * f3 + self[1][3] * f4) * -1f32,
            (self[1][0] * f1 - self[1][1] * f3 + self[1][3] * f5),
            (self[1][0] * f2 - self[1][1] * f4 + self[1][2] * f5) * -1f32,
        ]);

        self[0].dot(coefficient)
    }

    /// Get fully inversed matrix if matrix can be inverted.
    ///
    /// This method does not regard matrix as homogeneous coordinates transform,
    /// so maybe slower than transform version.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Vec4, Mat4};
    ///
    /// macro_rules! f32_arr { ($($e:expr),*) => { [ $($e as f32),* ] }; }
    ///
    /// let mat = Mat4::from_elements_array(
    ///     f32_arr!(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15)
    /// );
    /// assert_eq!(mat.to_inversed(), None);
    /// assert_eq!(mat.to_transposed().to_inversed(), None);
    ///
    /// let mat = Mat4::from_column_vec4s(
    ///     Vec4::new(0.707f32, 0f32, 0.707f32, 0f32),
    ///     Vec4::new(0f32, 1f32, 0f32, 0f32),
    ///     Vec4::new(-0.707f32, 0f32, 0.707f32, 0f32),
    ///     Vec4::new(4f32, -3f32, 1f32, 1f32),
    /// );
    /// assert_ne!(mat.to_inversed(), None);
    ///
    /// let mat = Mat4::from_elements_array(
    ///     f32_arr!(4, 0, 0, 0, 0, 4, 0, 0, 0, 0, 4, 0, 0, 0, 0, 1)
    /// );
    /// assert_eq!(mat.determinant(), 64f32);
    /// assert_eq!(
    ///     mat.to_inversed(),
    ///     Some(Mat4::from_elements_array(
    ///         f32_arr!(0.25, 0, 0, 0, 0, 0.25, 0, 0, 0, 0, 0.25, 0, 0, 0, 0, 1)
    ///     ))
    /// );
    ///
    /// assert_eq!(Mat4::from_identity().to_inversed(), Some(Mat4::from_identity()));
    /// ```
    ///
    /// # Todos
    ///
    /// * Support SIMD for the fast operation.
    pub fn to_inversed(&self) -> Option<Mat4> {
        let c00 = (self[2][2] * self[3][3]) - (self[3][2] * self[2][3]);
        let c02 = (self[1][2] * self[3][3]) - (self[3][2] * self[1][3]);
        let c03 = (self[1][2] * self[2][3]) - (self[2][2] * self[1][3]);

        let c04 = (self[2][1] * self[3][3]) - (self[3][1] * self[2][3]);
        let c06 = (self[1][1] * self[3][3]) - (self[3][1] * self[1][3]);
        let c07 = (self[1][1] * self[2][3]) - (self[2][1] * self[1][3]);

        let c08 = (self[2][1] * self[3][2]) - (self[3][1] * self[2][2]);
        let c10 = (self[1][1] * self[3][2]) - (self[3][1] * self[1][2]);
        let c11 = (self[1][1] * self[2][2]) - (self[2][1] * self[1][2]);

        let c12 = (self[2][0] * self[3][3]) - (self[3][0] * self[2][3]);
        let c14 = (self[1][0] * self[3][3]) - (self[3][0] * self[1][3]);
        let c15 = (self[1][0] * self[2][3]) - (self[2][0] * self[1][3]);

        let c16 = (self[2][0] * self[3][2]) - (self[3][0] * self[2][2]);
        let c18 = (self[1][0] * self[3][2]) - (self[3][0] * self[1][2]);
        let c19 = (self[1][0] * self[2][2]) - (self[2][0] * self[1][2]);

        let c20 = (self[2][0] * self[3][1]) - (self[3][0] * self[2][1]);
        let c22 = (self[1][0] * self[3][1]) - (self[3][0] * self[1][1]);
        let c23 = (self[1][0] * self[2][1]) - (self[2][0] * self[1][1]);

        let fac0 = Vec4::new(c00, c00, c02, c03);
        let fac1 = Vec4::new(c04, c04, c06, c07);
        let fac2 = Vec4::new(c08, c08, c10, c11);
        let fac3 = Vec4::new(c12, c12, c14, c15);
        let fac4 = Vec4::new(c16, c16, c18, c19);
        let fac5 = Vec4::new(c20, c20, c22, c23);

        let vec0 = Vec4::new(self[1][0], self[0][0], self[0][0], self[0][0]);
        let vec1 = Vec4::new(self[1][1], self[0][1], self[0][1], self[0][1]);
        let vec2 = Vec4::new(self[1][2], self[0][2], self[0][2], self[0][2]);
        let vec3 = Vec4::new(self[1][3], self[0][3], self[0][3], self[0][3]);

        let inv0 = (vec1 * fac0) - (vec2 * fac1) + (vec3 * fac2);
        let inv1 = (vec0 * fac0) - (vec2 * fac3) + (vec3 * fac4);
        let inv2 = (vec0 * fac1) - (vec1 * fac3) + (vec3 * fac5);
        let inv3 = (vec0 * fac2) - (vec1 * fac4) + (vec2 * fac5);

        let sign_a = Vec4::new(1f32, -1f32, 1f32, -1f32);
        let sign_b = sign_a * -1f32;
        let row0 = Vec4::new(inv0[0], inv1[0], inv2[0], inv3[0]) * sign_a;
        let det = row0.dot(self[0]);

        if !det.is_normal() {
            None
        } else {
            let invdet = 1f32 / det;
            Some(Self::from_column_vec4s(
                inv0 * sign_a * invdet,
                inv1 * sign_b * invdet,
                inv2 * sign_a * invdet,
                inv3 * sign_b * invdet,
            ))
        }
    }

    /// Multiply to other matrix.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Vec4, Mat4};
    ///
    /// macro_rules! f32_arr { ($($e:expr),*) => { [ $($e as f32),* ] }; }
    ///
    /// let lhs = Mat4::from_elements_array(
    ///     f32_arr!(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15)
    /// );
    /// let rhs = lhs * -1f32;
    /// let mat = lhs.mul(rhs);
    /// for (i, col_vec) in mat.iter().enumerate() {
    ///     match i {
    ///     0 => assert_eq!(*col_vec, Vec4::from_array(f32_arr!(-56, -62, -68, -74))),
    ///     1 => assert_eq!(*col_vec, Vec4::from_array(f32_arr!(-152, -174, -196, -218))),
    ///     2 => assert_eq!(*col_vec, Vec4::from_array(f32_arr!(-248, -286, -324, -362))),
    ///     3 => assert_eq!(*col_vec, Vec4::from_array(f32_arr!(-344, -398, -452, -506))),
    ///     _ => (),
    ///     }
    /// }
    /// ```
    pub fn mul(&self, rhs: Self) -> Self {
        let lhs = self.to_transposed();
        Self::from_elements_array([
            rhs[0].dot(lhs[0]),
            rhs[0].dot(lhs[1]),
            rhs[0].dot(lhs[2]),
            rhs[0].dot(lhs[3]),
            rhs[1].dot(lhs[0]),
            rhs[1].dot(lhs[1]),
            rhs[1].dot(lhs[2]),
            rhs[1].dot(lhs[3]),
            rhs[2].dot(lhs[0]),
            rhs[2].dot(lhs[1]),
            rhs[2].dot(lhs[2]),
            rhs[2].dot(lhs[3]),
            rhs[3].dot(lhs[0]),
            rhs[3].dot(lhs[1]),
            rhs[3].dot(lhs[2]),
            rhs[3].dot(lhs[3]),
        ])
    }

    /// Multiply to [Vec4] and return [Vec4].
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Vec4, Mat4};
    ///
    /// macro_rules! f32_arr { ($($e:expr),*) => { [ $($e as f32),* ] }; }
    ///
    /// let lhs = Mat4::from_elements_array(
    ///     f32_arr!(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15)
    /// );
    /// let rhs = Vec4::new(3f32, 6f32, 9f32, 1f32);
    /// let vec = lhs.mul_vec4(rhs);
    /// assert_eq!(vec, Vec4::new(108f32, 127f32, 146f32, 165f32));
    /// ```
    pub fn mul_vec4(&self, rhs: Vec4) -> Vec4 {
        let lhs = self.to_transposed();
        Vec4::new(lhs[0].dot(rhs), lhs[1].dot(rhs), lhs[2].dot(rhs), lhs[3].dot(rhs))
    }

    /// Return slice that traverses each elements of matrix with column order.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Mat4;
    ///
    /// macro_rules! f32_arr { ($($e:expr),*) => { [ $($e as f32),* ] }; }
    ///
    /// let mat = Mat4::from_elements_array(
    ///     f32_arr!(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15)
    /// );
    /// mat.as_elements()
    ///     .iter()
    ///     .enumerate()
    ///     .for_each(|(i, &v)| assert_eq!(v, i as f32));
    /// ```
    pub fn as_elements(&self) -> &[f32] {
        let v: &[f32; 16] = unsafe { mem::transmute(&self.val[0]) };
        &v[..16]
    }

    /// Return iterator that can traverse 4 columns as [Vec4].
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Mat4;
    ///
    /// macro_rules! f32_arr { ($($e:expr),*) => { [ $($e as f32),* ] }; }
    ///
    /// let mat = Mat4::from_elements_array(
    ///     f32_arr!(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15)
    /// );
    ///
    /// // Outputs will be
    /// // "Col 0 : (0, 1, 2, 3)"
    /// // "Col 1 : (4, 5, 6, 7)"
    /// // "Col 2 : (8, 9,10,11)"
    /// // "Col 3 :(12,13,14,15)"
    /// mat.iter()
    ///     .enumerate()
    ///     .for_each(|(i, c)| { println!("Col {} : {:?}", i, c); });
    /// ```
    pub fn iter(&self) -> slice::Iter<'_, Vec4> { self.val.iter() }
}

impl Default for Mat4 {
    /// Create identity matrix.
    fn default() -> Self { Self::from_identity() }
}

impl Index<usize> for Mat4 {
    type Output = Vec4;

    /// Perform indexing but as column major order.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Mat4;
    ///
    /// macro_rules! f32_arr { ($($e:expr),*) => { [ $($e as f32),* ] }; }
    ///
    /// let mat = Mat4::from_elements_array(
    ///     f32_arr!(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15)
    /// );
    ///
    /// assert_eq!(mat[0][0], 0f32);
    /// assert_eq!(mat[0][3], 3f32);
    /// assert_eq!(mat[1][0], 4f32);
    /// assert_eq!(mat[1][3], 7f32);
    /// assert_eq!(mat[2][0], 8f32);
    /// assert_eq!(mat[2][3], 11f32);
    /// assert_eq!(mat[3][0], 12f32);
    /// assert_eq!(mat[3][3], 15f32);
    /// ```
    fn index(&self, index: usize) -> &Self::Output { &self.val[index] }
}

impl IndexMut<usize> for Mat4 {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output { &mut self.val[index] }
}

op_matrix_binary_impl!(Mat4, Add, add, +, 0 1 2 3);
op_matrix_binary_impl!(Mat4, Sub, sub, -, 0 1 2 3);
op_matrix_binary_impl!(Mat4, Mul, mul, *, 0 1 2 3);
op_matrix_scalar_mul_impl!(Mat4, Mul, mul, *, 0 1 2 3, u8);
op_matrix_scalar_mul_impl!(Mat4, Mul, mul, *, 0 1 2 3, u16);
op_matrix_scalar_mul_impl!(Mat4, Mul, mul, *, 0 1 2 3, u32);
op_matrix_scalar_mul_impl!(Mat4, Mul, mul, *, 0 1 2 3, u64);
op_matrix_scalar_mul_impl!(Mat4, Mul, mul, *, 0 1 2 3, usize);
op_matrix_scalar_mul_impl!(Mat4, Mul, mul, *, 0 1 2 3, i8);
op_matrix_scalar_mul_impl!(Mat4, Mul, mul, *, 0 1 2 3, i16);
op_matrix_scalar_mul_impl!(Mat4, Mul, mul, *, 0 1 2 3, i32);
op_matrix_scalar_mul_impl!(Mat4, Mul, mul, *, 0 1 2 3, i64);
op_matrix_scalar_mul_impl!(Mat4, Mul, mul, *, 0 1 2 3, isize);
op_matrix_scalar_mul_impl!(Mat4, Mul, mul, *, 0 1 2 3, f32);
op_matrix_scalar_mul_impl!(Mat4, Mul, mul, *, 0 1 2 3, f64);

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn invert_test() {
        macro_rules! f32_arr { ($($e:expr),*) => { [ $($e as f32),* ] }; }

        let mat = Mat4::from_elements_array(f32_arr!(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15));
        assert_eq!(mat.to_inversed(), None);
        assert_eq!(mat.to_transposed().to_inversed(), None);

        let mat = Mat4::from_column_vec4s(
            Vec4::new(0.707f32, 0f32, 0.707f32, 0f32),
            Vec4::new(0f32, 1f32, 0f32, 0f32),
            Vec4::new(-0.707f32, 0f32, 0.707f32, 0f32),
            Vec4::new(4f32, -3f32, 1f32, 1f32),
        );
        assert_ne!(mat.to_inversed(), None);

        assert_eq!(Mat4::from_identity().to_inversed(), Some(Mat4::from_identity()));

        let mat = Mat4::from_elements_array(f32_arr!(4, 0, 0, 0, 0, 4, 0, 0, 0, 0, 4, 0, 0, 0, 0, 1));
        assert_eq!(mat.determinant(), 64f32);
        assert_eq!(
            mat.to_inversed(),
            Some(Mat4::from_elements_array(f32_arr!(
                0.25, 0, 0, 0, 0, 0.25, 0, 0, 0, 0, 0.25, 0, 0, 0, 0, 1
            )))
        );
    }
}
