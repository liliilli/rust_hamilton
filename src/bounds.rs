use crate::{Extent2, Extent3, IExtent2, IExtent3, IVec2, Vec2, Vec3};

// ----------------------------------------------------------------------------
//
// BOUNDS2
//
// ----------------------------------------------------------------------------

/// Represents 2D bounds which is consist of `start` and `length`.
///
/// This [Bounds2] is half-closed range such as `[start, start + size)`.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Bounds2 {
    start: Vec2,
    size: Extent2,
}

impl Bounds2 {
    /// Create [Bounds2] from given `points` [Vec2] list.
    ///
    /// If `points` list is empty, do not create [Bounds2] but just return `None` value.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Vec2, Bounds2, Extent2};
    ///
    /// let bounds = Bounds2::from_points(&[
    ///     Vec2::new(0f32, -3f32),
    ///     Vec2::new(1f32, 2f32),
    ///     Vec2::new(-16f32, 8f32)]).unwrap();
    /// assert_eq!(bounds.start(), Vec2::new(-16f32, -3f32));
    /// assert_eq!(bounds.size(), Extent2::new(17f32, 11f32).unwrap());
    /// ```
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Bounds2;
    ///
    /// let should_none = Bounds2::from_points(&[]).is_none();
    /// assert_eq!(should_none, true);
    /// ```
    pub fn from_points(points: &[Vec2]) -> Option<Self> {
        if points.is_empty() {
            None
        } else {
            let min = Vec2::from_scalar(f32::MAX).min_elements_with(points);
            let max = Vec2::from_scalar(f32::MIN).max_elements_with(points);
            let length = max - min;

            Some(Self {
                start: min,
                // We need to clamp to 0 when length is minus,
                // because IEEE-754 arithmetic calculation error may occur slight negative values.
                size: Extent2::uncheck_new(length.x().max(0f32), length.y().max(0f32)),
            })
        }
    }

    /// Create [Bounds2] with `start` position and `size` 2D-axis length.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Vec2, Bounds2, Extent2};
    ///
    /// let bounds = Bounds2::new(Vec2::new(0f32, -1f32), Extent2::new(2f32, 3f32).unwrap());
    /// assert_eq!(bounds.start(), Vec2::new(0f32, -1f32));
    /// assert_eq!(bounds.size(), Extent2::new(2f32, 3f32).unwrap());
    /// ```
    pub fn new(start: Vec2, size: Extent2) -> Self {
        Self { start, size }
    }

    /// Get `start` position of [Bounds2].
    pub fn start(&self) -> Vec2 {
        self.start
    }

    /// Get `end` position which is not inclusive in this [Bounds2].
    pub fn exclusive_end(&self) -> Vec2 {
        self.start + self.diagonal()
    }

    /// Get `size` [Extent2] of [Bounds2].
    pub fn size(&self) -> Extent2 {
        self.size
    }

    /// Get diagonal vector [Vec2] of [Bounds2].
    ///
    /// Diagonal vector values are same to [Extent2]'s `width` and `height` from `Self::size` method.
    pub fn diagonal(&self) -> Vec2 {
        let size = self.size();
        Vec2::new(size.width(), size.height())
    }

    /// Get area value of this [Bounds2].
    pub fn area(&self) -> f32 {
        self.size.area()
    }

    /// Get corner positions of this [Bounds2].
    /// Each position is located with counter-clockwised order.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Vec2, Bounds2, Extent2};
    ///
    /// let bounds = Bounds2::from_points(&[
    ///     Vec2::new(0f32, -3f32),
    ///     Vec2::new(1f32, 2f32),
    ///     Vec2::new(-16f32, 8f32)]).unwrap();
    /// let corners = bounds.corners();
    /// assert_eq!(corners[0], bounds.start());
    /// assert_eq!(corners[1], Vec2::new(1f32, -3f32));
    /// assert_eq!(corners[2], bounds.exclusive_end());
    /// assert_eq!(corners[3], Vec2::new(-16f32, 8f32));
    /// ```
    pub fn corners(&self) -> [Vec2; 4] {
        let diagonal = self.diagonal();
        [
            self.start,
            self.start + diagonal.swizzle_x0(),
            self.start + diagonal,
            self.start + diagonal.swizzle_0y(),
        ]
    }

    /// Get unionized (combined) [Bounds2] with `self` and given input `bounds`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Vec2, Bounds2, Extent2};
    ///
    /// let old = Bounds2::new(Vec2::new(0f32, -1f32), Extent2::new(2f32, 3f32).unwrap());
    /// let new = old.union_with_bounds(&[
    /// 	Bounds2::new(Vec2::new(3f32, 4f32), Extent2::new(4f32, 2f32).unwrap()),
    /// 	Bounds2::new(Vec2::new(1f32, -3f32), Extent2::new(3f32, 6f32).unwrap()),
    /// ]);
    /// assert_eq!(new.start(), Vec2::new(0f32, -3f32));
    /// assert_eq!(new.size(), Extent2::new(7f32, 9f32).unwrap());
    /// ```
    pub fn union_with_bounds(&self, bounds: &[Bounds2]) -> Self {
        let init = (self.start, self.exclusive_end());
        let new = bounds.iter().fold(init, |(min, max), bounds| {
            let rhs_min = bounds.start();
            let rhs_max = bounds.exclusive_end();
            (
                min.min_elements_with(&[rhs_min]),
                max.max_elements_with(&[rhs_max]),
            )
        });
        let size = (new.1 - new.0).max_elements_with(&[Vec2::from_scalar(0f32)]);
        Self {
            start: new.0,
            size: Extent2::new(size.x(), size.y()).unwrap(),
        }
    }

    /// Get total intersection [Bounds2] of `self` and given `bounds` list.
    ///
    /// If there is no shared intersection of list, return `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Vec2, Bounds2, Extent2};
    ///
    /// let item0 = Bounds2::new(
    /// 	Vec2::from_scalar(-3f32),
    /// 	Extent2::from_scalar(6f32).unwrap()
    /// );
    /// let intersection = item0.intersection_with_bounds(&[
    /// 	Bounds2::new(Vec2::from_scalar(1.5f32), Extent2::from_scalar(1f32).unwrap()),
    /// 	Bounds2::new(Vec2::new(1f32, -3f32), Extent2::new(3f32, 6f32).unwrap()),
    /// ]).unwrap();
    /// assert_eq!(intersection.start(), Vec2::from_scalar(1.5f32));
    /// assert_eq!(intersection.exclusive_end(), Vec2::from_scalar(2.5f32));
    ///
    /// let extent = Extent2::from_scalar(3f32).unwrap();
    /// let should_none = item0.intersection_with_bounds(&[
    /// 	Bounds2::new(Vec2::from_scalar(0f32), extent),
    /// 	Bounds2::new(Vec2::new(0f32, -3f32), extent),
    /// 	Bounds2::new(Vec2::from_scalar(-3f32), extent),
    /// 	Bounds2::new(Vec2::new(-3f32, 0f32), extent),
    /// ]).is_none();
    /// assert_eq!(should_none, true);
    /// ```
    pub fn intersection_with_bounds(&self, bounds: &[Bounds2]) -> Option<Self> {
        // If no bound is exist except for `self`, return `None`.
        if bounds.is_empty() {
            return None;
        }

        let mut int_s = self.start;
        let mut int_e = self.exclusive_end();
        for bound in bounds {
            int_s = int_s.max_elements_with(&[bound.start()]);
            int_e = int_e.min_elements_with(&[bound.exclusive_end()]);

            // If there is no more intersection, just return with failure.
            if (int_s.x() >= int_e.x()) || (int_s.y() >= int_e.y()) {
                return None;
            }
        }

        Self::from_points(&[int_s, int_e])
    }

    /// Check two [Bounds2] `this` and `rhs` is overlapped with each other.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Vec2, Bounds2, Extent2};
    ///
    /// let lhs = Bounds2::new(Vec2::new(-1f32, -1f32), Extent2::new(2f32, 2f32).unwrap());
    /// assert_eq!(lhs.is_overlapped_with(&lhs), true);
    ///
    /// let overlapped = Bounds2::new(Vec2::new(0f32, 0f32), Extent2::new(2f32, 2f32).unwrap());
    /// assert_eq!(lhs.is_overlapped_with(&overlapped), true);
    ///
    /// let not_overlapped = Bounds2::new(Vec2::new(-1f32, 1f32), Extent2::new(1f32, 1f32).unwrap());
    /// assert_eq!(lhs.is_overlapped_with(&not_overlapped), false);
    /// ```
    pub fn is_overlapped_with(&self, rhs: &Bounds2) -> bool {
        let lhs_s = self.start();
        let lhs_e = self.exclusive_end();
        let rhs_s = rhs.start();
        let rhs_e = rhs.exclusive_end();

        let overlap_x = (lhs_s.x() < rhs_e.x()) && (rhs_s.x() < lhs_e.x());
        let overlap_y = (lhs_s.y() < rhs_e.y()) && (rhs_s.y() < lhs_e.y());
        overlap_x && overlap_y
    }

    /// Check that this `self` [Bounds2] is inside of `rhs` [Bounds2].
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Vec2, Bounds2, Extent2};
    ///
    /// let item = Bounds2::new(Vec2::from_scalar(-1f32), Extent2::new(2f32, 2f32).unwrap());
    /// let moved = Bounds2::new(Vec2::from_scalar(0f32), Extent2::new(2f32, 2f32).unwrap());
    /// assert_eq!(item.is_inside_of(&item), true);
    /// assert_eq!(item.is_inside_of(&moved), false);
    ///
    /// let bigger = Bounds2::new(Vec2::new(-1f32, -2f32), Extent2::new(2f32, 4f32).unwrap());
    /// assert_eq!(item.is_inside_of(&bigger), true);
    ///
    /// let smaller = Bounds2::new(Vec2::from_scalar(-0.5f32), Extent2::new(1f32, 1f32).unwrap());
    /// assert_eq!(item.is_inside_of(&smaller), false);
    /// assert_eq!(smaller.is_inside_of(&item), true);
    /// ```
    pub fn is_inside_of(&self, rhs: &Bounds2) -> bool {
        let lhs_s = self.start();
        let lhs_e = self.exclusive_end();
        let rhs_s = rhs.start();
        let rhs_e = rhs.exclusive_end();

        let inside_x = (rhs_s.x() <= lhs_s.x()) && (lhs_e.x() <= rhs_e.x());
        let inside_y = (rhs_s.y() <= lhs_s.y()) && (lhs_e.y() <= rhs_e.y());
        inside_x && inside_y
    }

    /// Check that `self` and given `rhs` [Bounds2] are adjacent to each other.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Vec2, Bounds2, Extent2};
    ///
    /// let item = Bounds2::new(
    ///		Vec2::from_scalar(-1f32),
    /// 	Extent2::new(2f32, 2f32).unwrap()
    /// );
    /// let adj_x = Bounds2::new(
    /// 	Vec2::new(1f32, 0f32),
    /// 	Extent2::new(1f32, 1f32).unwrap()
    /// );
    /// assert_eq!(item.is_adjacent_to(&adj_x), true);
    ///
    /// let adj_y = Bounds2::new(
    /// 	Vec2::new(-2f32, -2f32),
    /// 	Extent2::new(2f32, 1f32).unwrap()
    /// );
    /// assert_eq!(item.is_adjacent_to(&adj_y), true);
    ///
    /// let not = Bounds2::new(
    /// 	Vec2::new(-2f32, -1f32),
    /// 	Extent2::new(2f32, 2f32).unwrap()
    /// );
    /// assert_eq!(item.is_adjacent_to(&not), false);
    /// ```
    pub fn is_adjacent_to(&self, rhs: &Bounds2) -> bool {
        let lhs_s = self.start();
        let lhs_e = self.exclusive_end();
        let rhs_s = rhs.start();
        let rhs_e = rhs.exclusive_end();

        let overlap_x = (lhs_s.x() < rhs_e.x()) && (rhs_s.x() < lhs_e.x());
        let adjacent_y = (lhs_s.y() == rhs_e.y()) || (lhs_e.y() == rhs_s.y());

        let overlap_y = (lhs_s.y() < rhs_e.y()) && (rhs_s.y() < lhs_e.y());
        let adjacent_x = (lhs_s.x() == rhs_e.x()) || (lhs_e.x() == rhs_s.x());

        (overlap_x && adjacent_y) || (overlap_y && adjacent_x)
    }
}

// ----------------------------------------------------------------------------
//
// IBOUNDS2
//
// ----------------------------------------------------------------------------

/// Represents 2D bounds which is consist of `start` and `length`.
/// But each elements are consisted of integer types unlike [Bounds2].
///
/// This [IBounds2] is half-closed range such as `[start, start + size)`.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct IBounds2 {
    start: IVec2,
    size: IExtent2,
}

impl IBounds2 {
    /// Create [IBounds2] from given `points` [IVec2] list.
    ///
    /// If `points` list is empty, do not create [IBounds2] but just return `None` value.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{IBounds2, IExtent2, IVec2};
    ///
    /// let bounds = IBounds2::from_ivec2s(&[
    ///     IVec2::new(0, -3),
    ///     IVec2::new(1, 2),
    ///     IVec2::new(16, 8)]
    /// ).unwrap();
    /// assert_eq!(bounds.start(), IVec2::new(0, -3));
    /// assert_eq!(bounds.size(), IExtent2::new(16, 11));
    /// ```
    ///
    /// ```
    /// use hamilton as math;
    /// use math::IBounds2;
    ///
    /// let should_none = IBounds2::from_ivec2s(&[]).is_none();
    /// assert_eq!(should_none, true);
    /// ```
    pub fn from_ivec2s(points: &[IVec2]) -> Option<Self> {
        if points.is_empty() {
            None
        } else {
            let min = IVec2::from_scalar(i32::MAX).min_elements_with(points);
            let max = IVec2::from_scalar(i32::MIN).max_elements_with(points);
            let length = max - min;

            Some(Self {
                start: min,
                size: IExtent2::new(length.x() as u32, length.y() as u32),
            })
        }
    }

    /// Create [IBounds2] with `start` position and `size` 2D-axis length.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{IBounds2, IExtent2, IVec2};
    ///
    /// let bounds = IBounds2::new(
    ///     IVec2::new(0, -1),
    ///     IExtent2::new(2, 3),
    /// );
    /// assert_eq!(bounds.start(), IVec2::new(0, -1));
    /// assert_eq!(bounds.size(), IExtent2::new(2, 3));
    /// ```
    pub fn new(start: IVec2, size: IExtent2) -> Self {
        Self { start, size }
    }

    /// Get `start` position of [IBounds2].
    pub fn start(&self) -> IVec2 {
        self.start
    }

    /// Get `end` position which is not inclusive in this [IBounds2].
    pub fn exclusive_end(&self) -> IVec2 {
        let diagonal = self.diagonal();
        self.start() + diagonal
    }

    /// Get `size` [IExtent2] of [IBounds2].
    pub fn size(&self) -> IExtent2 {
        self.size
    }

    /// Get diagonal length pair of [IBounds2].
    ///
    /// Diagonal vector values are same to [IExtent2]'s `width` and `height` from `Self::size` method.
    pub fn diagonal(&self) -> IVec2 {
        IVec2::new(self.size.width() as i32, self.size.height() as i32)
    }

    /// Get area value of this [IBounds2].
    pub fn area(&self) -> u64 {
        self.size.area()
    }

    /// Get corner positions of this [IBounds2].
    /// Each position is located with counter-clockwised order.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{IVec2, IBounds2};
    ///
    /// let bounds = IBounds2::from_ivec2s(&[
    ///     IVec2::new(0, -3),
    ///     IVec2::new(1, 2),
    ///     IVec2::new(-16, 8)]
    /// ).unwrap();
    /// let corners = bounds.corners();
    /// assert_eq!(corners[0], bounds.start());
    /// assert_eq!(corners[1], IVec2::new(1, -3));
    /// assert_eq!(corners[2], bounds.exclusive_end());
    /// assert_eq!(corners[3], IVec2::new(-16, 8));
    /// ```
    pub fn corners(&self) -> [IVec2; 4] {
        let diagonal = self.diagonal();
        [
            self.start,
            self.start + diagonal.swizzle_x0(),
            self.start + diagonal,
            self.start + diagonal.swizzle_0y(),
        ]
    }

    /// Get unionized (combined) [IBounds2] with `self` and given input `bounds`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{IVec2, IBounds2, IExtent2};
    ///
    /// let old = IBounds2::new(
    ///     IVec2::new(0, -1),
    ///     IExtent2::new(2, 3),
    /// );
    /// let new = old.union_with_bounds(&[
    /// 	IBounds2::new(IVec2::new(3, 4), IExtent2::new(4, 2)),
    /// 	IBounds2::new(IVec2::new(1, -3), IExtent2::new(3, 6)),
    /// ]);
    /// assert_eq!(new.start(), IVec2::new(0, -3));
    /// assert_eq!(new.size(), IExtent2::new(7, 9));
    /// ```
    pub fn union_with_bounds(&self, bounds: &[IBounds2]) -> Self {
        let init = (self.start, self.exclusive_end());
        let new = bounds.iter().fold(init, |(min, max), bounds| {
            let rhs_min = bounds.start();
            let rhs_max = bounds.exclusive_end();
            (
                min.min_elements_with(&[rhs_min]),
                max.max_elements_with(&[rhs_max]),
            )
        });
        let size = (new.1 - new.0).max_elements_with(&[IVec2::from_scalar(0)]);
        Self {
            start: new.0,
            size: IExtent2::new(size.x() as u32, size.y() as u32),
        }
    }

    /// Get total intersection [IBounds2] of `self` and given `bounds` list.
    ///
    /// If there is no shared intersection of list, return `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{IVec2, IBounds2, IExtent2};
    ///
    /// let item0 = IBounds2::new(
    /// 	IVec2::from_scalar(-3),
    /// 	IExtent2::from_scalar(6)
    /// );
    /// let intersection = item0.intersection_with_bounds(&[
    /// 	IBounds2::new(IVec2::from_scalar(2), IExtent2::from_scalar(1)),
    /// 	IBounds2::new(IVec2::new(1, -3), IExtent2::new(3, 6)),
    /// ]).unwrap();
    /// assert_eq!(intersection.start(), IVec2::from_scalar(2));
    /// assert_eq!(intersection.exclusive_end(), IVec2::from_scalar(3));
    ///
    /// let extent = IExtent2::from_scalar(3);
    /// let should_none = item0.intersection_with_bounds(&[
    /// 	IBounds2::new(IVec2::from_scalar(0), extent),
    /// 	IBounds2::new(IVec2::new(0, -3), extent),
    /// 	IBounds2::new(IVec2::from_scalar(-3), extent),
    /// 	IBounds2::new(IVec2::new(-3, 0), extent),
    /// ]).is_none();
    /// assert_eq!(should_none, true);
    /// ```
    pub fn intersection_with_bounds(&self, bounds: &[IBounds2]) -> Option<Self> {
        // If no bound is exist except for `self`, return `None`.
        if bounds.is_empty() {
            return None;
        }

        let mut int_s = self.start;
        let mut int_e = self.exclusive_end();
        for bound in bounds {
            int_s = int_s.max_elements_with(&[bound.start()]);
            int_e = int_e.min_elements_with(&[bound.exclusive_end()]);

            // If there is no more intersection, just return with failure.
            if (int_s.x() >= int_e.x()) || (int_s.y() >= int_e.y()) {
                return None;
            }
        }

        Self::from_ivec2s(&[int_s, int_e])
    }

    /// Check two [IBounds2] `this` and `rhs` is overlapped with each other.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{IVec2, IBounds2, IExtent2};
    ///
    /// let lhs = IBounds2::new(
    ///     IVec2::new(-1, -1),
    ///     IExtent2::new(2, 2)
    /// );
    /// assert_eq!(lhs.is_overlapped_with(&lhs), true);
    ///
    /// let overlapped = IBounds2::new(
    ///     IVec2::new(0, 0),
    ///     IExtent2::new(2, 2)
    /// );
    /// assert_eq!(lhs.is_overlapped_with(&overlapped), true);
    ///
    /// let not_overlapped = IBounds2::new(
    ///     IVec2::new(-1, 1),
    ///     IExtent2::new(1, 1)
    /// );
    /// assert_eq!(lhs.is_overlapped_with(&not_overlapped), false);
    /// ```
    pub fn is_overlapped_with(&self, rhs: &IBounds2) -> bool {
        let lhs_s = self.start();
        let lhs_e = self.exclusive_end();
        let rhs_s = rhs.start();
        let rhs_e = rhs.exclusive_end();

        let overlap_x = (lhs_s.x() < rhs_e.x()) && (rhs_s.x() < lhs_e.x());
        let overlap_y = (lhs_s.y() < rhs_e.y()) && (rhs_s.y() < lhs_e.y());
        overlap_x && overlap_y
    }

    /// Check that this `self` [IBounds2] is inside of `rhs` [IBounds2].
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{IVec2, IBounds2, IExtent2};
    ///
    /// let item = IBounds2::new(IVec2::from_scalar(-1), IExtent2::new(2, 2));
    /// let moved = IBounds2::new(IVec2::from_scalar(0), IExtent2::new(2, 2));
    /// assert_eq!(item.is_inside_of(&item), true);
    /// assert_eq!(item.is_inside_of(&moved), false);
    ///
    /// let bigger = IBounds2::new(IVec2::new(-1, -2), IExtent2::new(2, 4));
    /// assert_eq!(item.is_inside_of(&bigger), true);
    ///
    /// let smaller = IBounds2::new(IVec2::from_scalar(0), IExtent2::new(1, 1));
    /// assert_eq!(item.is_inside_of(&smaller), false);
    /// assert_eq!(smaller.is_inside_of(&item), true);
    /// ```
    pub fn is_inside_of(&self, rhs: &IBounds2) -> bool {
        let lhs_s = self.start();
        let lhs_e = self.exclusive_end();
        let rhs_s = rhs.start();
        let rhs_e = rhs.exclusive_end();

        let inside_x = (rhs_s.x() <= lhs_s.x()) && (lhs_e.x() <= rhs_e.x());
        let inside_y = (rhs_s.y() <= lhs_s.y()) && (lhs_e.y() <= rhs_e.y());
        inside_x && inside_y
    }

    /// Check that `self` and given `rhs` [IBounds2] are adjacent to each other.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{IVec2, IBounds2, IExtent2};
    ///
    /// let item = IBounds2::new(
    ///		IVec2::from_scalar(-1),
    /// 	IExtent2::new(2, 2)
    /// );
    /// let adj_x = IBounds2::new(
    /// 	IVec2::new(1, 0),
    /// 	IExtent2::new(1, 1)
    /// );
    /// assert_eq!(item.is_adjacent_to(&adj_x), true);
    ///
    /// let adj_y = IBounds2::new(
    /// 	IVec2::new(-2, -2),
    /// 	IExtent2::new(2, 1)
    /// );
    /// assert_eq!(item.is_adjacent_to(&adj_y), true);
    ///
    /// let not = IBounds2::new(
    /// 	IVec2::new(-2, -1),
    /// 	IExtent2::new(2, 2)
    /// );
    /// assert_eq!(item.is_adjacent_to(&not), false);
    /// ```
    pub fn is_adjacent_to(&self, rhs: &IBounds2) -> bool {
        let lhs_s = self.start();
        let lhs_e = self.exclusive_end();
        let rhs_s = rhs.start();
        let rhs_e = rhs.exclusive_end();

        let overlap_x = (lhs_s.x() < rhs_e.x()) && (rhs_s.x() < lhs_e.x());
        let adjacent_y = (lhs_s.y() == rhs_e.y()) || (lhs_e.y() == rhs_s.y());

        let overlap_y = (lhs_s.y() < rhs_e.y()) && (rhs_s.y() < lhs_e.y());
        let adjacent_x = (lhs_s.x() == rhs_e.x()) || (lhs_e.x() == rhs_s.x());

        (overlap_x && adjacent_y) || (overlap_y && adjacent_x)
    }
}

// ----------------------------------------------------------------------------
//
// BOUNDS3
//
// ----------------------------------------------------------------------------

/// Represents 3D bounds which is consist of `start` and `length`.
///
/// This [Bounds3] is half-closed range such as `[start, start + size)`.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Bounds3 {
    start: Vec3,
    size: Extent3,
}

impl Bounds3 {
    /// Create [Bounds3] from given `points` [Vec3] list.
    ///
    /// If `points` list is empty, do not create [Bounds3] but just return `None` value.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Vec3, Bounds3, Extent3};
    ///
    /// let bounds = Bounds3::from_points(&[
    ///     Vec3::new(0f32, -3f32, -1f32),
    ///     Vec3::new(1f32, 2f32, 5f32),
    ///     Vec3::new(-16f32, 8f32, 4f32)]).unwrap();
    /// assert_eq!(bounds.start(), Vec3::new(-16f32, -3f32, -1f32));
    /// assert_eq!(bounds.size(), Extent3::new(17f32, 11f32, 6f32).unwrap());
    /// ```
    ///
    /// ```
    /// use hamilton as math;
    /// use math::Bounds3;
    ///
    /// let should_none = Bounds3::from_points(&[]).is_none();
    /// assert_eq!(should_none, true);
    /// ```
    pub fn from_points(points: &[Vec3]) -> Option<Self> {
        if points.is_empty() {
            None
        } else {
            let min = Vec3::from_scalar(f32::MAX).min_elements_with(points);
            let max = Vec3::from_scalar(f32::MIN).max_elements_with(points);
            let length = max - min;

            Some(Self {
                start: min,
                // We need to clamp to 0 when length is minus,
                // because IEEE-754 arithmetic calculation error may occur slight negative values.
                size: Extent3::uncheck_new(
                    length.x().max(0f32),
                    length.y().max(0f32),
                    length.z().max(0f32),
                ),
            })
        }
    }

    /// Create [Bounds3] with `start` position and `size` 2D-axis length.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Vec3, Bounds3, Extent3};
    ///
    /// let bounds = Bounds3::new(
    ///     Vec3::new(0f32, -1f32, -5f32),
    ///     Extent3::new(2f32, 3f32, 20f32).unwrap());
    /// assert_eq!(bounds.start(), Vec3::new(0f32, -1f32, -5f32));
    /// assert_eq!(bounds.size(), Extent3::new(2f32, 3f32, 20f32).unwrap());
    /// ```
    pub fn new(start: Vec3, size: Extent3) -> Self {
        Self { start, size }
    }

    /// Get `start` position of [Bounds3].
    pub fn start(&self) -> Vec3 {
        self.start
    }

    /// Get `end` position which is not inclusive in this [Bounds3].
    pub fn exclusive_end(&self) -> Vec3 {
        self.start + self.diagonal()
    }

    /// Get `size` [Extent3] of [Bounds3].
    pub fn size(&self) -> Extent3 {
        self.size
    }

    /// Get diagonal vector [Vec3] of [Bounds3].
    ///
    /// Diagonal vector values are same to [Extent3]'s `width`, `height` and `depth` from `Self::size` method.
    pub fn diagonal(&self) -> Vec3 {
        let size = self.size();
        Vec3::new(size.width(), size.height(), size.depth())
    }

    /// Get surface area value of this [Bounds3].
    pub fn surface_area(&self) -> f32 {
        self.size.surface_area()
    }

    /// Get the volume of this [Bounds3].
    pub fn volume(&self) -> f32 {
        self.size.volume()
    }

    /// Get corner positions of this [Bounds3].
    /// Each position is located with counter-clockwised order.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Vec3, Bounds3, Extent3};
    ///
    /// let bounds = Bounds3::from_points(&[
    ///     Vec3::new(0f32, -3f32, -1f32),
    ///     Vec3::new(1f32, 2f32, 0f32),
    ///     Vec3::new(-16f32, 8f32, 5f32)]).unwrap();
    /// let corners = bounds.corners();
    /// assert_eq!(corners[0], bounds.start());
    /// assert_eq!(corners[1], Vec3::new(-16f32, -3f32, 5f32));
    /// assert_eq!(corners[2], Vec3::new(1f32, -3f32, 5f32));
    /// assert_eq!(corners[3], Vec3::new(1f32, -3f32, -1f32));
    /// assert_eq!(corners[4], Vec3::new(-16f32, 8f32, -1f32));
    /// assert_eq!(corners[5], Vec3::new(-16f32, 8f32, 5f32));
    /// assert_eq!(corners[6], bounds.exclusive_end());
    /// assert_eq!(corners[7], Vec3::new(1f32, 8f32, -1f32));
    /// ```
    pub fn corners(&self) -> [Vec3; 8] {
        let diagonal = self.diagonal();
        let upy = self.start + diagonal.swizzle_0y0();
        [
            self.start,
            self.start + diagonal.swizzle_00z(),
            self.start + diagonal.swizzle_x0z(),
            self.start + diagonal.swizzle_x00(),
            upy,
            upy + diagonal.swizzle_00z(),
            upy + diagonal.swizzle_x0z(),
            upy + diagonal.swizzle_x00(),
        ]
    }

    /// Get unionized (combined) [Bounds3] with `self` and given input `bounds`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Vec3, Bounds3, Extent3};
    ///
    /// let old = Bounds3::new(
    ///     Vec3::new(0f32, -1f32, -2f32),
    ///     Extent3::new(2f32, 3f32, 5f32).unwrap()
    /// );
    /// let new = old.union_with_bounds(&[
    /// 	Bounds3::new(
    ///         Vec3::new(3f32, 4f32, 3f32),
    ///         Extent3::new(4f32, 2f32, 6f32).unwrap()),
    /// 	Bounds3::new(
    ///         Vec3::new(1f32, -3f32, -4f32),
    ///         Extent3::new(3f32, 6f32, 1f32).unwrap()),
    /// ]);
    /// assert_eq!(new.start(), Vec3::new(0f32, -3f32, -4f32));
    /// assert_eq!(new.size(), Extent3::new(7f32, 9f32, 13f32).unwrap());
    /// ```
    pub fn union_with_bounds(&self, bounds: &[Bounds3]) -> Self {
        let init = (self.start, self.exclusive_end());
        let new = bounds.iter().fold(init, |(min, max), bounds| {
            let rhs_min = bounds.start();
            let rhs_max = bounds.exclusive_end();
            (
                min.min_elements_with(&[rhs_min]),
                max.max_elements_with(&[rhs_max]),
            )
        });
        let size = (new.1 - new.0).max_elements_with(&[Vec3::from_scalar(0f32)]);
        Self {
            start: new.0,
            size: Extent3::new(size.x(), size.y(), size.z()).unwrap(),
        }
    }

    /// Get total intersection [Bounds3] of `self` and given `bounds` list.
    ///
    /// If there is no shared intersection of list, return `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Vec3, Bounds3, Extent3};
    ///
    /// let item = Bounds3::new(
    /// 	Vec3::from_scalar(-3f32),
    /// 	Extent3::from_scalar(6f32).unwrap()
    /// );
    /// let intersection = item.intersection_with_bounds(&[
    /// 	Bounds3::new(
    ///         Vec3::from_scalar(1.5f32),
    ///         Extent3::from_scalar(1f32).unwrap()),
    /// 	Bounds3::new(
    ///         Vec3::new(1f32, -3f32, -6f32),
    ///         Extent3::new(3f32, 6f32, 10f32).unwrap()),
    /// ]).unwrap();
    /// assert_eq!(intersection.start(), Vec3::from_scalar(1.5f32));
    /// assert_eq!(intersection.exclusive_end(), Vec3::from_scalar(2.5f32));
    /// ```
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Vec3, Bounds3, Extent3};
    ///
    /// let item0 = Bounds3::new(
    /// 	Vec3::from_scalar(-3f32),
    /// 	Extent3::from_scalar(6f32).unwrap()
    /// );
    /// let extent = Extent3::from_scalar(3f32).unwrap();
    /// let should_none = item0.intersection_with_bounds(&[
    /// 	Bounds3::new(Vec3::from_scalar(-3f32), extent),
    /// 	Bounds3::new(Vec3::new(-3f32, -3f32, 0f32), extent),
    /// 	Bounds3::new(Vec3::new(0f32, -3f32, 0f32), extent),
    /// 	Bounds3::new(Vec3::new(0f32, -3f32, -3f32), extent),
    /// 	Bounds3::new(Vec3::new(-3f32, 0f32, -3f32), extent),
    /// 	Bounds3::new(Vec3::new(-3f32, 0f32, 0f32), extent),
    /// 	Bounds3::new(Vec3::from_scalar(0f32), extent),
    /// 	Bounds3::new(Vec3::new(0f32, 0f32, -3f32), extent),
    /// ]).is_none();
    /// assert_eq!(should_none, true);
    /// ```
    pub fn intersection_with_bounds(&self, bounds: &[Bounds3]) -> Option<Self> {
        // If no bound is exist except for `self`, return `None`.
        if bounds.is_empty() {
            return None;
        }

        let mut int_s = self.start;
        let mut int_e = self.exclusive_end();
        for bound in bounds {
            int_s = int_s.max_elements_with(&[bound.start()]);
            int_e = int_e.min_elements_with(&[bound.exclusive_end()]);

            // If there is no more intersection, just return with failure.
            if (int_s.x() >= int_e.x()) || (int_s.y() >= int_e.y()) || (int_s.z() >= int_e.z()) {
                return None;
            }
        }

        Self::from_points(&[int_s, int_e])
    }

    /// Check two [Bounds3] `this` and `rhs` is overlapped with each other.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Vec3, Bounds3, Extent3};
    ///
    /// let lhs = Bounds3::new(
    ///     Vec3::from_scalar(-1f32),
    ///     Extent3::from_scalar(2f32).unwrap());
    /// assert_eq!(lhs.is_overlapped_with(&lhs), true);
    ///
    /// let overlapped = Bounds3::new(
    ///     Vec3::from_scalar(0f32),
    ///     Extent3::from_scalar(2f32).unwrap());
    /// assert_eq!(lhs.is_overlapped_with(&overlapped), true);
    ///
    /// let not_overlapped = Bounds3::new(
    ///     Vec3::new(-1f32, 1f32, -0.5f32),
    ///     Extent3::new(2f32, 1f32, 2f32).unwrap());
    /// assert_eq!(lhs.is_overlapped_with(&not_overlapped), false);
    /// ```
    pub fn is_overlapped_with(&self, rhs: &Bounds3) -> bool {
        let lhs_s = self.start();
        let lhs_e = self.exclusive_end();
        let rhs_s = rhs.start();
        let rhs_e = rhs.exclusive_end();

        let overlap_x = (lhs_s.x() < rhs_e.x()) && (rhs_s.x() < lhs_e.x());
        let overlap_y = (lhs_s.y() < rhs_e.y()) && (rhs_s.y() < lhs_e.y());
        let overlap_z = (lhs_s.z() < rhs_e.z()) && (rhs_s.z() < lhs_e.z());
        overlap_x && overlap_y && overlap_z
    }

    /// Check that this `self` [Bounds3] is inside of `rhs` [Bounds3].
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Vec3, Bounds3, Extent3};
    ///
    /// let item = Bounds3::new(
    ///     Vec3::from_scalar(-1f32),
    ///     Extent3::from_scalar(2f32).unwrap());
    /// let moved = Bounds3::new(
    ///     Vec3::from_scalar(0f32),
    ///     Extent3::from_scalar(2f32).unwrap());
    /// assert_eq!(item.is_inside_of(&item), true);
    /// assert_eq!(item.is_inside_of(&moved), false);
    ///
    /// let bigger = Bounds3::new(
    ///     Vec3::new(-1f32, -2f32, -3f32),
    ///     Extent3::new(2f32, 4f32, 6f32).unwrap());
    /// assert_eq!(item.is_inside_of(&bigger), true);
    ///
    /// let smaller = Bounds3::new(
    ///     Vec3::from_scalar(-0.5f32),
    ///     Extent3::new(1f32, 1.5f32, 1f32).unwrap());
    /// assert_eq!(item.is_inside_of(&smaller), false);
    /// assert_eq!(smaller.is_inside_of(&item), true);
    /// ```
    pub fn is_inside_of(&self, rhs: &Bounds3) -> bool {
        let lhs_s = self.start();
        let lhs_e = self.exclusive_end();
        let rhs_s = rhs.start();
        let rhs_e = rhs.exclusive_end();

        let inside_x = (rhs_s.x() <= lhs_s.x()) && (lhs_e.x() <= rhs_e.x());
        let inside_y = (rhs_s.y() <= lhs_s.y()) && (lhs_e.y() <= rhs_e.y());
        let inside_z = (rhs_s.z() <= lhs_s.z()) && (lhs_e.z() <= rhs_e.z());
        inside_x && inside_y && inside_z
    }

    /// Check that `self` and given `rhs` [Bounds3] are adjacent to each other.
    ///
    /// # Examples
    ///
    /// ```
    /// use hamilton as math;
    /// use math::{Vec3, Bounds3, Extent3};
    ///
    /// let item = Bounds3::new(
    ///		Vec3::from_scalar(-1f32),
    /// 	Extent3::from_scalar(2f32).unwrap()
    /// );
    /// let adj_x = Bounds3::new(
    /// 	Vec3::new(1f32, 0f32, -1f32),
    /// 	Extent3::from_scalar(2f32).unwrap()
    /// );
    /// assert_eq!(item.is_adjacent_to(&adj_x), true);
    ///
    /// let adj_y = Bounds3::new(
    /// 	Vec3::from_scalar(-2f32),
    /// 	Extent3::new(2f32, 1f32, 4f32).unwrap()
    /// );
    /// assert_eq!(item.is_adjacent_to(&adj_y), true);
    ///
    /// let not = Bounds3::new(
    /// 	Vec3::new(-2f32, -1f32, 0f32),
    /// 	Extent3::from_scalar(2f32).unwrap()
    /// );
    /// assert_eq!(item.is_adjacent_to(&not), false);
    /// ```
    pub fn is_adjacent_to(&self, rhs: &Bounds3) -> bool {
        let lhs_s = self.start();
        let lhs_e = self.exclusive_end();
        let rhs_s = rhs.start();
        let rhs_e = rhs.exclusive_end();

        let overlap_x = (lhs_s.x() < rhs_e.x()) && (rhs_s.x() < lhs_e.x());
        let overlap_y = (lhs_s.y() < rhs_e.y()) && (rhs_s.y() < lhs_e.y());
        let overlap_z = (lhs_s.z() < rhs_e.z()) && (rhs_s.z() < lhs_e.z());

        let adjacent_x = (lhs_s.x() == rhs_e.x()) || (lhs_e.x() == rhs_s.x());
        let adjacent_y = (lhs_s.y() == rhs_e.y()) || (lhs_e.y() == rhs_s.y());
        let adjacent_z = (lhs_s.z() == rhs_e.z()) || (lhs_e.z() == rhs_s.z());

        (adjacent_x && overlap_y && overlap_z)
            || (adjacent_y && overlap_x && overlap_z)
            || (adjacent_z && overlap_x && overlap_y)
    }
}
