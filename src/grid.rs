//! Data structures for tracking cell/value possibilities.

use std::fmt;
use std::io::Result as IOResult;
use std::iter;
use std::ops;
use std::slice;

/// Input/output for grids
pub mod io {
    pub use super::super::io::*;
}

/// Cell value index.
///
/// Represents a possible value of a cell, typically 1-9.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ValueId(pub usize);

/// Cell position index.
///
/// This is used to address a particular cell on a grid.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct CellId(pub usize);

/// Cell/value combination index.
///
/// This is used to address the possibility that a particular cell is a particular value.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct CaseId(pub usize);

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

/// Stores the possible values for each cell of a puzzle.
///
/// A grid contains cells arranged in a square (with `size` cells per side). Each cell
/// has `size` different `bool`s, each one indicating whether the cell may be a particular
/// value.
pub struct Grid {
    size: usize,
    cases: Vec<bool>, // TODO: Memory-efficient implementation?
}

impl Grid {
    /// Creates a new `Grid` for a puzzle that is `size` cells wide.
    pub fn new(size: usize) -> Grid {
        Grid {
            size: size,
            cases: vec![true; size * size * size]
        }
    }

    /// Reads new `Grid` from lines iterator.
    pub fn read<I>(lines: &mut I) -> Result<Grid, io::Error>
        where I: Iterator<Item=IOResult<String>> {
        io::GridReader::new().read(lines)
    }

    /// Returns the width of the grid in cells.
    pub fn size(&self) -> usize { self.size }

    /// Returns iterator over all cell positions/values.
    ///
    /// Iterates over all cells in row-major order, yielding items of type `(CellId, &[bool])`,
    /// representing a cell's position, whether it can be each value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rusudoku::grid::*;
    /// let grid = Grid::new(9);
    /// let (cell, values) = grid.cells().nth(5).unwrap();
    /// assert_eq!(cell, grid.convert((5, 0)));
    /// assert!(values[0]); // The cell could be the value 1.
    /// ```
    pub fn cells(&self) -> CellsIter {
        let cell_id: fn(_) -> _ = CellId;
        (0..).map(cell_id).zip(self.cases.chunks(self.size))
    }

    /// Returns mutable iterator over all cell positions/values.
    ///
    /// Identical to `cells()`, except that the boolean array references are mutable.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rusudoku::grid::*;
    /// let mut grid = Grid::new(9);
    /// let (cell, values) = grid.cells_mut().nth(5).unwrap();
    /// values[0] = false; // Prevent the cell from being the value 1.
    /// ```
    pub fn cells_mut(&mut self) -> CellsIterMut {
        let cell_id: fn(_) -> _ = CellId;
        (0..).map(cell_id).zip(self.cases.chunks_mut(self.size))
    }

    fn cell_range(&self, cell_id: CellId) -> ops::Range<usize> {
        let size = self.size;
        cell_id.0 * size .. cell_id.0 * size + size
    }

    /// Returns iterator over cases/values of a cell.
    ///
    /// Given a CellId (or something that can be converted to one), returns an iterator over the
    /// cases that make up a particular cell, yielding items of type `(CaseId, &bool)`,
    /// representing a particular case (i.e. position and value) and whether or not that case is
    /// possible.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rusudoku::grid::*;
    /// let mut grid = Grid::new(9);
    /// let (case, value) = grid.cell((5, 0)).nth(3).unwrap();
    /// assert!(*value); // The cell at 5,0 could be the value 4.
    /// ```
    pub fn cell<T>(&self, cell_id: T) -> CasesIter
        where CellId: FromIndex<T> {
        let case_id: fn(_) -> _ = CaseId;
        let range = self.cell_range(self.convert(cell_id));
        range.clone().map(case_id).zip(self.cases[range].iter())
    }

    /// Returns mutable iterator over cases/values of a cell.
    ///
    /// Identical to `cell(...)`, except that the boolean references are mutable.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rusudoku::grid::*;
    /// let mut grid = Grid::new(9);
    /// let (case, value) = grid.cell_mut((5, 0)).nth(3).unwrap();
    /// *value = false; // Prevent the cell at 5,0 from being the value 4.
    /// ```
    pub fn cell_mut<T>(&mut self, cell_id: T) -> CasesIterMut
        where CellId: FromIndex<T> {
        let case_id: fn(_) -> _ = CaseId;
        let range = self.cell_range(self.convert(cell_id));
        range.clone().map(case_id).zip(self.cases[range].iter_mut())
    }

    /// Returns iterator over all cases/values.
    ///
    /// Iterates over the cases of the puzzle, yielding items of type `(CaseId, &bool)`,
    /// representing a particular case (i.e. position and value) and whether or not that
    /// case is possible.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rusudoku::grid::*;
    /// let mut grid = Grid::new(9);
    /// let (case, value) = grid.cases().nth(100).unwrap();
    /// assert!(*value); // The cell at 2,1 could be the value 2.
    /// ```
    pub fn cases(&self) -> CasesIter {
        let case_id: fn(_) -> _ = CaseId;
        (0..self.cases.len()).map(case_id).zip(self.cases.iter())
    }

    /// Returns mutable iterator over all cases/values.
    ///
    /// Identical to `cases()`, except that the boolean references are mutable.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rusudoku::grid::*;
    /// let mut grid = Grid::new(9);
    /// let (case, value) = grid.cases_mut().nth(100).unwrap();
    /// *value = false; // Prevent the cell at 2,1 from being the value 2.
    /// ```
    pub fn cases_mut(&mut self) -> CasesIterMut {
        let case_id: fn(_) -> _ = CaseId;
        (0..self.cases.len()).map(case_id).zip(self.cases.iter_mut())
    }
}

pub type CellsIter<'a>    = iter::Zip<iter::Map<ops::RangeFrom<usize>, fn(usize) -> CellId>, slice::Chunks<'a, bool>>;
pub type CellsIterMut<'a> = iter::Zip<iter::Map<ops::RangeFrom<usize>, fn(usize) -> CellId>, slice::ChunksMut<'a, bool>>;
pub type CasesIter<'a>    = iter::Zip<iter::Map<ops::Range<usize>,     fn(usize) -> CaseId>, slice::Iter<'a, bool>>;
pub type CasesIterMut<'a> = iter::Zip<iter::Map<ops::Range<usize>,     fn(usize) -> CaseId>, slice::IterMut<'a, bool>>;

impl IndexConverter for Grid {
    fn conversion_size(&self) -> usize { self.size }
}

impl ops::Index<CellId> for Grid {
    type Output = [bool];
    fn index(&self, cell_id: CellId) -> &[bool] {
        let range = self.cell_range(cell_id);
        &self.cases[range]
    }
}

impl ops::IndexMut<CellId> for Grid {
    fn index_mut(&mut self, cell_id: CellId) -> &mut [bool] {
        let range = self.cell_range(cell_id);
        &mut self.cases[range]
    }
}

impl ops::Index<CaseId> for Grid {
    type Output = bool;
    fn index(&self, CaseId(case_id): CaseId) -> &bool {
        &self.cases[case_id]
    }
}

impl ops::IndexMut<CaseId> for Grid {
    fn index_mut(&mut self, CaseId(case_id): CaseId) -> &mut bool {
        &mut self.cases[case_id]
    }
}

impl fmt::Display for Grid {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        try!(io::GridWriter::new().write(f, &self));
        Ok(())
    }
}

// Wish I could figure out how to get Index<FromIndex<T>> to work...

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

    #[test]
    fn test_new_grid() {
        let grid = Grid::new(9);
        assert_eq!(grid.size(), 9);
        assert_eq!(grid.cases.len(), 729);
    }

    #[test]
    fn test_grid_cells_iter() {
        let mut grid = Grid::new(9);
        for i in vec![9,10,12,13,14,16,17] {
            grid.cases[i] = false;
        }
        assert_eq!(grid.cells().count(), 81);
        let cells: Vec<_> = grid.cells().take(3).collect();
        assert_eq!(cells[0].0, grid.convert((0,0)));
        assert_eq!(cells[1].0, grid.convert((1,0)));
        assert_eq!(cells[2].0, grid.convert((2,0)));
        assert_eq!(cells[0].1, [true; 9]);
        assert_eq!(cells[1].1, [false, false, true, false, false, false, true, false, false]);
        assert_eq!(cells[2].1, [true; 9]);
    }

    #[test]
    fn test_grid_cells_mut_iter() {
        let mut grid = Grid::new(9);
        let cell = {
            let (cell, possibilities) = grid.cells_mut().nth(3).unwrap();
            possibilities[0] = false;
            possibilities[3] = false;
            possibilities[8] = false;
            cell
        };
        assert_eq!((3,0), grid.convert(cell));
        assert!(grid.cases[27..36] == [false, true, true, false, true, true, true, true, false]);
    }

    #[test]
    fn test_grid_cell_iter() {
        let mut grid = Grid::new(9);
        for i in vec![9,10,12,13,14,16,17] {
            grid.cases[i] = false;
        }
        let (cases, possibilities): (Vec<_>, Vec<_>) = grid.cell((1,0)).map(|(case, &ok)| (case, ok)).unzip();
        assert_eq!(possibilities, [false, false, true, false, false, false, true, false, false]);
        let (cells, values): (Vec<_>, Vec<_>) = cases.iter()
                                                     .map(|&case| grid.convert::<_, (CellId, ValueId)>(case))
                                                     .unzip();
        assert!(cells.iter().all(|&cell| cell == grid.convert((1,0))));
        assert_eq!(values[0], grid.convert(1));
        assert_eq!(values[8], grid.convert(9));
    }

    #[test]
    fn test_grid_cell_mut_iter() {
        let mut grid = Grid::new(9);
        let c = SimpleConverter(9);
        for (i, (case, possibility)) in grid.cell_mut((1,0)).enumerate() {
            let (cell, value): (CellId, ValueId) = c.convert(case);
            assert_eq!((1,0), c.convert(cell));
            assert_eq!(i+1, c.convert(value));
            assert!(*possibility);
            *possibility = false;
        }
        assert!(grid.cases[9..18] == [false; 9]);
    }

    #[test]
    fn test_grid_cases_iter() {
        let mut grid = Grid::new(9);
        grid.cases[8] = false;
        grid.cases[9] = false;
        let cases: Vec<_> = grid.cases().skip(7).take(4).collect();
        assert_eq!(cases[0].0, CaseId(7));
        assert_eq!(cases[1].0, CaseId(8));
        assert_eq!(cases[2].0, CaseId(9));
        assert_eq!(cases[3].0, CaseId(10));
        assert!(cases[0].1);
        assert!(!cases[1].1);
        assert!(!cases[2].1);
        assert!(cases[3].1);
    }

    #[test]
    fn test_grid_cases_mut_iter() {
        let mut grid = Grid::new(9);
        {
            let (case, possibility) = grid.cases_mut().nth(10).unwrap();
            *possibility = false;
            assert_eq!(case, CaseId(10));
        }
        assert!(grid.cases[9]);
        assert!(!grid.cases[10]);
        assert!(grid.cases[11]);
    }

    #[test]
    fn test_grid_index_by_cell() {
        let mut grid = Grid::new(9);
        for i in vec![0,1,3,4,5,7,8] {
            grid[CellId(4)][i] = false;
        }
        assert!(grid[CellId(3)] == [true; 9]);
        assert!(grid[CellId(4)] == [false, false, true, false, false, false, true, false, false]);
        assert!(grid[CellId(5)] == [true; 9]);
    }

    #[test]
    fn test_grid_index_by_case() {
        let mut grid = Grid::new(9);
        for i in vec![0,1,5,20,50,80] {
            assert!(grid[CaseId(i)]);
            grid[CaseId(i)] = false;
            assert!(!grid[CaseId(i)]);
        }
        assert!(grid[CaseId(2)]);
        assert!(grid[CaseId(6)]);
        assert!(grid[CaseId(25)]);
        assert!(grid[CaseId(40)]);
        assert!(grid[CaseId(79)]);
    }
}
