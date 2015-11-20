//! Data structures for tracking cell/value possibilities.

/// Cell value index.
///
/// Represents a possible value of a cell, typically 1-9.
#[derive(Clone, Copy, Debug)]
pub struct ValueId(usize);

/// Cell position index.
///
/// This is used to address a particular cell on a grid.
#[derive(Clone, Copy, Debug)]
pub struct CellId(usize);

/// Cell/value combination index.
///
/// This is used to address the possibility that a particular cell is a particular value.
#[derive(Clone, Copy, Debug)]
pub struct CaseId(usize);

/// Marker trait to indicate grid-size-dependent conversions.
///
/// Very similar to the `std::convert::From` trait, except that conversions also need to know an
/// appropriate grid size. Generally used by the `IndexConverter` trait.
pub trait FromIndex<T> {
    /// Converts `other` to `Self`
    ///
    /// Note that the conversion is made under the assumption the puzzle is `size` cells wide.
    fn convert(other: T, size: usize) -> Self;
}

impl<T> FromIndex<T> for T {
    fn convert(t: T, _: usize) -> Self { t }
}

/// Convert between `usize` and `ValueId`
///
/// A `usize` of at least `1` and at most the size of the puzzle grid may be converted to/from a
/// `ValueId`.
///
/// # Panics
///
/// In debug builds, this will panic if `value` is outside of `1..size+1`.
impl FromIndex<usize> for ValueId {
    fn convert(value: usize, size: usize) -> Self {
        debug_assert!(0 < value && value <= size, "value in 1..size+1");
        ValueId(value - 1)
    }
}

impl FromIndex<ValueId> for usize {
    fn convert(ValueId(value_id): ValueId, _: usize) -> Self {
        value_id + 1
    }
}

/// Convert between `(usize, usize)` and `CellId`
///
/// A `(usize, usize)` representing an (x,y) coordinate (with each element being in the range
/// `0..size`) may be converted to/from a `CellId`.
///
/// # Panics
///
/// In debug builds, this will panic if `x` or `y` is outside of `0..size`.
impl FromIndex<(usize, usize)> for CellId {
    fn convert((x, y): (usize, usize), size: usize) -> Self {
        debug_assert!(x < size, "x in 0..size");
        debug_assert!(y < size, "y in 0..size");
        CellId(size*y + x)
    }
}

impl FromIndex<CellId> for (usize, usize) {
    fn convert(CellId(cell_id): CellId, size: usize) -> Self {
        (cell_id % size, cell_id / size)
    }
}

/// Convert between `(CellId, ValueId)` and `CaseId`
impl FromIndex<(CellId, ValueId)> for CaseId {
    fn convert((CellId(cell_id), ValueId(value_id)): (CellId, ValueId), size: usize) -> Self {
        CaseId(size*cell_id + value_id)
    }
}

/// Convert between `(ValueId, CellId)` and `CaseId`
impl FromIndex<(ValueId, CellId)> for CaseId {
    fn convert((ValueId(value_id), CellId(cell_id)): (ValueId, CellId), size: usize) -> Self {
        CaseId(size*cell_id + value_id)
    }
}

impl FromIndex<CaseId> for (CellId, ValueId) {
    fn convert(CaseId(cell_id): CaseId, size: usize) -> Self {
        (CellId(cell_id / size), ValueId(cell_id % size))
    }
}

impl FromIndex<CaseId> for (ValueId, CellId) {
    fn convert(CaseId(cell_id): CaseId, size: usize) -> Self {
        (ValueId(cell_id % size), CellId(cell_id / size))
    }
}

/// Indicates ability to perform size-dependent index conversion.
///
/// This trait indicates that something has a particular puzzle size, allowing it to perform
/// conversions between types such as `ValueId`, `CellId` and `CaseId`.
///
/// # Examples
///
/// ```rust
/// # use rusudoku::grid::*;
/// let c = SimpleConverter(9);
/// let cell_id: CellId = c.convert((4, 5));
/// let value_id: ValueId = c.convert(6);
/// let case_id: CaseId = c.convert((cell_id, value_id));
/// let (value_id, cell_id): (ValueId, CellId) = c.convert(case_id);
/// let (x, y): (usize, usize) = c.convert(cell_id);
/// let value: usize = c.convert(value_id);
/// assert_eq!((x, y, value), (4, 5, 6))
/// ```
pub trait IndexConverter {
    /// Returns puzzle width (in cells) that conversions assume.
    fn conversion_size(&self) -> usize;
    /// Convert `T` into `U`, for a puzzle `conversion_size()` cells wide.
    fn convert<T, U>(&self, t: T) -> U
        where U: FromIndex<T> {
        U::convert(t, self.conversion_size())
    }
}

/// Simple light-weight index converter.
///
/// Allows for converting between `ValueId`, `CellId` and `CaseId` without needing to store
/// a full puzzle `Grid`. The contained `usize` represents the puzzle size (width in cells).
#[derive(Clone, Copy, Debug)]
pub struct SimpleConverter(pub usize);

impl IndexConverter for SimpleConverter {
    fn conversion_size(&self) -> usize { self.0 }
}

/// Not yet implemented.
pub struct Grid;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_value_id_conversions() {
        let c = SimpleConverter(9);
        let cases = vec![(1, 0), (5,4), (9, 8)];
        for (initial, expected_internal) in cases {
            let ValueId(value_id) = c.convert(initial);
            assert_eq!(value_id, expected_internal);
            let value: usize = c.convert(ValueId(value_id));
            assert_eq!(value, initial);
        }
    }

    #[test]
    #[should_panic]
    #[cfg(debug_assertions)]
    fn test_value_id_cannot_be_zero() {
        let c = SimpleConverter(9);
        let _: ValueId = c.convert(0);
    }

    #[test]
    #[should_panic]
    #[cfg(debug_assertions)]
    fn test_value_id_cannot_be_too_large() {
        let c = SimpleConverter(9);
        let _: ValueId = c.convert(10);
    }

    #[test]
    fn test_cell_id_conversions() {
        let c = SimpleConverter(9);
        let cases = vec![(0, 0,  0), (5, 0,  5), (8, 0,  8),
                         (0, 1,  9), (2, 3, 29), (8, 4, 44),
                         (0, 8, 72), (4, 8, 76), (8, 8, 80)];
        for (initial_x, initial_y, expected_internal) in cases {
            let CellId(cell_id) = c.convert((initial_x, initial_y));
            assert_eq!(cell_id, expected_internal);
            let coords: (usize, usize) = c.convert(CellId(cell_id));
            assert_eq!(coords, (initial_x, initial_y));
        }
    }

    #[test]
    #[should_panic]
    #[cfg(debug_assertions)]
    fn test_cell_id_x_cannot_be_too_large() {
        let c = SimpleConverter(9);
        let _: CellId = c.convert((9,0));
    }

    #[test]
    #[should_panic]
    #[cfg(debug_assertions)]
    fn test_cell_id_y_cannot_be_too_large() {
        let c = SimpleConverter(9);
        let _: CellId = c.convert((0,9));
    }

    #[test]
    fn test_case_id_conversions() {
        let c = SimpleConverter(9);
        let cases = vec![( 0, 0,   0), ( 0, 4,   4), ( 0, 8,   8),
                         ( 1, 0,   9), ( 2, 3,  21), ( 8, 4,  76),
                         (79, 8, 719), (80, 0, 720), (80, 8, 728)];
        for (initial_cell_id, initial_value_id, expected_internal) in cases {
            let cell = CellId(initial_cell_id);
            let value = ValueId(initial_value_id);
            let CaseId(case_id) = c.convert((cell, value));
            assert_eq!(case_id, expected_internal);
            let CaseId(case_id) = c.convert((value, cell));
            assert_eq!(case_id, expected_internal);
            let (CellId(cell_id), ValueId(value_id)) = c.convert(CaseId(case_id));
            assert_eq!((cell_id, value_id), (initial_cell_id, initial_value_id));
            let (ValueId(value_id), CellId(cell_id)) = c.convert(CaseId(case_id));
            assert_eq!((value_id, cell_id), (initial_value_id, initial_cell_id));
        }
    }

    #[test]
    fn test_alternate_size_conversions() {
        let c = SimpleConverter(16);
        let CellId(cell_id) = c.convert((5,12));
        assert_eq!(cell_id, 197);
        let ValueId(value_id) = c.convert(9);
        assert_eq!(value_id, 8);
        let CaseId(case_id) = c.convert((CellId(cell_id), ValueId(value_id)));
        assert_eq!(case_id, 3160);
    }
}
