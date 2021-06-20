use crate::{gamma_bound, get_xratio, Degree, EError, Mat4, NearlyEqual, Radian};

/// Create perspective projection matrix.
///
/// Given input values must satisfy below conditions.
/// * `height` must be normal floating point value.
/// * `fov_angle` degree angle value must be ranged in `(0, 180)` closed range.
/// * `view_near` must be more near than `view_far`.
/// * `view_far` must not be 0.
///
/// See <https://en.wikipedia.org/wiki/3D_projection>
pub fn perspective_matrix(
    width: u32,
    height: u32,
    fov_angle: Radian,
    view_near: f32,
    view_far: f32,
    ndc_near: f32,
    ndc_far: f32,
    y_inverted: bool,
) -> Result<Mat4, EError> {
    // If fov angle is 0 or nearly 90 degrees, do not calculation.
    let half_fov_angle = fov_angle * 0.5f32;
    if half_fov_angle.nearly_equal(Degree(90.0).into(), 1e-3f32) || !half_fov_angle.is_normal() {
        return Err(EError::InvalidRadian(fov_angle));
    }

    // If view near and view far is same or not satisfied condition,
    // `view_near < view_far`, do not calculation.
    if view_near >= view_far || !view_far.is_normal() {
        return Err(EError::InvalidNearFar(view_near, view_far));
    }

    // Get value to be used calculation checking failure errors.
    // Make perspective projection matrix.
    let xr = get_xratio(width, height)?;
    let pd = half_fov_angle.tan();

    // Calculate matrix element items. following 2d indices follows row-major.
    let i00 = pd / xr;
    let i11 = pd * if y_inverted { -1.0 } else { 1.0 };
    let (i22_a, i23_b) = {
        let view_nmf = view_near - view_far;
        let nnmff = (ndc_near * view_near) - (ndc_far * view_far);
        let a = nnmff / view_nmf;
        let b = (ndc_far - a) * view_far;
        (a, b)
    };

    Ok(Mat4::from_column_arrays(
        [i00, 0.0, 0.0, 0.0],
        [0.0, i11, 0.0, 0.0],
        [0.0, 0.0, i22_a, 1.0],
        [0.0, 0.0, i23_b, 0.0],
    ))
}

/// Create depth-infinite perspective projection matrix.
///
/// Given input values must satisfy below conditions.
/// * `height` must be normal floating point value.
/// * `fov_angle` degree angle value must be ranged in `(0, 180)` closed range.
/// * `view_near` must be more near than `view_far`.
///
/// See <https://en.wikipedia.org/wiki/3D_projection>
pub fn infinite_far_perspective_matrix(
    width: u32,
    height: u32,
    fov_angle: Radian,
    view_near: f32,
    ndc_near: f32,
    ndc_far: f32,
    y_inverted: bool,
) -> Result<Mat4, EError> {
    // If fov angle is 0 or nearly 90 degrees, do not calculation.
    let half_fov_angle = fov_angle * 0.5f32;
    if half_fov_angle.nearly_equal(Degree(90.0).into(), 1e-3f32) || !half_fov_angle.is_normal() {
        return Err(EError::InvalidRadian(fov_angle));
    }

    // Get value to be used calculation checking failure errors.
    // Make perspective projection matrix.
    let xr = get_xratio(width, height)?;
    let pd = half_fov_angle.tan();

    // Calculate matrix element items. following 2d indices follows row-major.
    let i00 = pd / xr;
    let i11 = pd * if y_inverted { -1.0 } else { 1.0 };
    let i22_a = ndc_near * (1.0 + 2.0 * gamma_bound(1));
    let i23_b = (ndc_far - i22_a) * view_near;

    Ok(Mat4::from_column_arrays(
        [i00, 0.0, 0.0, 0.0],
        [0.0, i11, 0.0, 0.0],
        [0.0, 0.0, i22_a, 1.0],
        [0.0, 0.0, i23_b, 0.0],
    ))
}

/// Create orthographic projection matrix.
///
/// Given input values must satisfy below conditions.
/// * `height` must be normal floating point value.
/// * `fov_angle` degree angle value must be ranged in `(0, 180)` closed range.
/// * `view_near` must be more near than `view_far`.
/// * `view_far` must not be 0.
///
/// See <https://en.wikipedia.org/wiki/Orthographic_projection>
pub fn orthographic_matrix(
    width: u32,
    height: u32,
    fov_angle: Radian,
    view_near: f32,
    view_far: f32,
    ndc_near: f32,
    ndc_far: f32,
    y_inverted: bool,
) -> Result<Mat4, EError> {
    // Check `width` and `height` can be halved.
    let half_width = width >> 1;
    let half_height = height >> 1;
    if half_width == 0u32 || half_height == 0u32 {
        return Err(EError::InvalidArgument);
    }

    // If fov angle is 0 or nearly 90 degrees, do not calculation.
    let half_fov_angle = fov_angle * 0.5f32;
    if half_fov_angle.nearly_equal(Degree(90.0).into(), 1e-3f32) || !half_fov_angle.is_normal() {
        return Err(EError::InvalidRadian(fov_angle));
    }

    // If view near and view far is same or not satisfied condition,
    // `view_near < view_far`, do not calculation.
    if view_near >= view_far || !view_far.is_normal() {
        return Err(EError::InvalidNearFar(view_near, view_far));
    }

    // Get value to be used calculation checking failure errors.
    // Make perspective projection matrix.
    let xr = get_xratio(width, height)?;
    let i11 = if y_inverted { -1.0f32 } else { 1.0f32 };
    let i22_a = ndc_far * (view_far - view_near).recip();
    let i23_b = (-1.0 * ndc_far * view_near * (view_far - view_near).recip()) + ndc_near;

    // Make orthographic matrix.
    Ok(Mat4::from_column_arrays(
        [xr.recip(), 0.0, 0.0, 0.0],
        [0.0, i11, 0.0, 0.0],
        [0.0, 0.0, i22_a, 0.0],
        [0.0, 0.0, i23_b, 1.0],
    ))
}
