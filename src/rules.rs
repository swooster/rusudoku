//! Data strutures for storing the rules of sudoku

use std::fmt;
use std::error;
use std::iter;
use std::ops;
use std::slice;

use grid::CellId;

/// Clique index.
///
/// This is used to address a particular clique.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CliqueId(pub usize);

/// Rules for which cells must have distinct values.
///
/// A `Rules` object is used to determine which cells must be different from each other.
/// It is essentially a list of cliques, where a clique is a set of cells that must each
/// have different values from one another. For example, in a classic sudoku problem
/// each row, column and zone is a clique.
///
/// # Examples
///
/// ```rust
/// # use rusudoku::rules::*;
/// let classic_rules = Rules::new_standard(9).expect("Classic sudoku rules are possible.");
/// let six_by_six_rules = Rules::new(RegularCliquesIterator::new(3, 2));
/// ```
#[derive(Debug)]
pub struct Rules {
    size: usize,
    clique_cells: Vec<Vec<CellId>>,
    cell_cliques: Vec<Vec<CliqueId>>,
}

impl Rules {
    /// Creates new set of arbitrary rules.
    ///
    /// This is the most general way to construct a `Rules`. You must pass an iterator
    /// of cliques (each clique being represented as an iterator of `CellId`s).
    /// The size of the sudoku grid is inferred from the size of the cliques.
    ///
    /// # Panics
    ///
    /// This will panic unless there is at least one clique, and all cliques have the
    /// same (non-zero) size.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rusudoku::rules::*;
    /// use rusudoku::grid::CellId;
    ///
    /// let cliques = [
    ///     [0, 1, 2, 3],
    ///     [0, 4, 8, 12],
    ///     [3, 5, 7, 11],
    /// ];
    /// let cliques = cliques.iter().map(|clique| {
    ///     clique.iter().cloned().map(CellId)
    /// });
    /// let rules = Rules::new(cliques);
    /// ```
    pub fn new<I, C>(cliques: I) -> Rules
        where I: Iterator<Item=C>, C: Iterator<Item=CellId> {

        fn unique_vec<T, U>(iter: T) -> Vec<U>
            where T: Iterator<Item=U>, U: Ord {
            let mut vec: Vec<_> = iter.collect();
            vec.sort();
            vec.dedup();
            vec.shrink_to_fit();
            vec
        }

        let clique_cells = unique_vec(cliques.map(unique_vec));
        assert!(clique_cells.len() > 0);
        let size = clique_cells[0].len();
        assert!(size > 0);
        assert!(clique_cells.iter().all(|clique| clique.len() == size));
        let mut cell_cliques: Vec<Vec<CliqueId>> = vec![Vec::new(); size*size];
        for (clique_id, clique) in clique_cells.iter().enumerate() {
            let clique_id = CliqueId(clique_id);
            for &CellId(cell_id) in clique.iter() {
                cell_cliques[cell_id].push(clique_id);
            }
        }
        for cliques in cell_cliques.iter_mut() {
            cliques.shrink_to_fit();
        }
        cell_cliques.shrink_to_fit();
        Rules {
            size: size,
            clique_cells: clique_cells,
            cell_cliques: cell_cliques,
        }
    }

    /// Creates a new set of standard sudoku rules.
    ///
    /// Given a grid `size` that has an integer square root, this creates a set of standard
    /// sudoku rules (two cells must differ if they share a row, column or zone), with each
    /// zone being a square. For example classic sudoku rules can be created with
    /// `Rules::new_standard(9)`. However, if classic sudoku rules cannot be created for a
    /// grid of the given `size` (due to lacking an integer square root), an
    /// `Err(NonSquareError {...})` is returned instead of an `Ok(Rules {...})`.
    pub fn new_standard(size: usize) -> Result<Rules, NonSquareError> {
        // This makes me a little uncomfortable, but at least
        // it shouldn't be a problem for reasonable sizes.
        let zone_size = (size as f64).sqrt().ceil() as usize;
        if zone_size * zone_size == size {
            Ok(Self::new(RegularCliquesIterator::new(zone_size, zone_size)))
        } else {
            Err(NonSquareError{ size: size })
        }
    }

    /// Returns the grid size the rules are for.
    pub fn size(&self) -> usize {
        self.size
    }

    /// Returns the cliques that contain a particular cell.
    pub fn cliques(&self, CellId(cell_id): CellId) -> CliquesIter {
        self.cell_cliques[cell_id].iter()
    }

    /// Returns the cells contained by a particular clique.
    pub fn cells(&self, CliqueId(clique_id): CliqueId) -> CellsIter {
        self.clique_cells[clique_id].iter()
    }

    /// Returns all clique ids that are valid for this set of rules.
    pub fn clique_ids(&self) -> CliqueIdsIter {
        (0..self.clique_cells.len()).map(CliqueId)
    }
}

pub type CliquesIter<'a> = slice::Iter<'a, CliqueId>;
pub type CellsIter<'a> = slice::Iter<'a, CellId>;
pub type CliqueIdsIter = iter::Map<ops::Range<usize>, fn(usize) -> CliqueId>;

impl ops::Index<CellId> for Rules {
    type Output = [CliqueId];
    fn index(&self, CellId(cell_id): CellId) -> &[CliqueId] {
        &self.cell_cliques[cell_id]
    }
}

impl ops::Index<CliqueId> for Rules {
    type Output = [CellId];
    fn index(&self, CliqueId(clique_id): CliqueId) -> &[CellId] {
        &self.clique_cells[clique_id]
    }
}

/// Iterator of cliques for rules with rectangular zones.
///
/// This provides an iterator of cliques for sudoku puzzles where each row, column and zone is a
/// clique, and zones are disjoint rectangles that all have the same dimensions.
pub struct RegularCliquesIterator {
    zone_width: usize,
    zone_height: usize,
    clique: usize,
}

impl RegularCliquesIterator {
    /// Creates a `RegularCliquesIterator`.
    ///
    /// This creates a `RegularCliquesIterator` with zones of the given dimensions.
    /// The grid size is inferred from the number of cells in a zone.
    pub fn new(zone_width: usize, zone_height: usize) -> RegularCliquesIterator {
        RegularCliquesIterator {
            zone_width: zone_width,
            zone_height: zone_height,
            clique: 0,
        }
    }
}

impl Iterator for RegularCliquesIterator {
    type Item = iter::Map<RectIndexIter, fn(usize) -> CellId>;

    fn next(&mut self) -> Option<iter::Map<RectIndexIter, fn(usize) -> CellId>> {
        let cell_id: fn(_) -> _ = CellId;
        let size = self.zone_width * self.zone_height;
        let (clique_type, clique_id) = (self.clique / size, self.clique % size);
        let result = match clique_type {
            0 => Some(RectIndexIter::new(size, 0..size, clique_id..clique_id+1).map(cell_id)),
            1 => Some(RectIndexIter::new(size, clique_id..clique_id+1, 0..size).map(cell_id)),
            2 => {
                let (width, height) = (self.zone_width, self.zone_height);
                // Note: There are zone_height (yes, height!) zones per row of zones.
                let (zone_y, zone_x) = (clique_id / height, clique_id % height);
                let x_range = zone_x*width..zone_x*width + width;
                let y_range = zone_y*height..zone_y*height + height;
                Some(RectIndexIter::new(size, x_range, y_range).map(cell_id))
            },
            _ => None,
        };
        if result.is_some() {
            self.clique += 1;
        }
        return result;
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = 3 * self.zone_width * self.zone_height - self.clique;
        (remaining, Some(remaining))
    }
}

/// Iterator of indexes of a subrect inside a 2D array.
///
/// Allows iterating over indexes of a sub-rectangle of a 2D array stored in row-major order.
///
/// # Examples
///
/// ```rust
/// # use rusudoku::rules::*;
/// let rect = [
///     1, 1, 1, 1, 1, 1,
///     1, 1, 2, 2, 2, 1,
///     1, 1, 2, 2, 2, 1,
///     1, 3, 6, 2, 2, 1,
///     1, 3, 6, 2, 2, 1,
///     1, 3, 3, 1, 1, 1,
///     1, 1, 1, 1, 1, 1,
/// ];
///
/// let mut subrect = RectIndexIter::new(6, 2..5, 1..5);
/// assert!(subrect.all(|i| rect[i] % 2 == 0));
///
/// let mut subrect = RectIndexIter::new(6, 1..3, 3..6);
/// assert!(subrect.all(|i| rect[i] % 3 == 0));
/// ```
pub struct RectIndexIter {
    index: usize,
    row_len: usize,
    non_row_len: usize,
    row_end: usize,
    end: usize,
}

impl RectIndexIter {
    /// Creates new `RectIndexIter`.
    ///
    /// This requires `outer_row_len` (the length of rows of an outer 2D array that's stored in
    /// row-major order), and x/y ranges that describe a sub-rectangle (the ranges are assumed
    /// to be right-open, as usual). Note that empty sub-rectangles are not currently supported.
    pub fn new(outer_row_len: usize, x_range: ops::Range<usize>, y_range: ops::Range<usize>) -> RectIndexIter {
        RectIndexIter {
            index: outer_row_len * y_range.start + x_range.start,
            row_len: x_range.end - x_range.start,
            non_row_len: outer_row_len - (x_range.end - x_range.start),
            row_end: outer_row_len * y_range.start + x_range.end,
            end: outer_row_len * y_range.end + x_range.start,
        }
    }
}

impl Iterator for RectIndexIter {
    type Item = usize;

    fn next(&mut self) -> Option<usize> {
        if self.index < self.end {
            let current = self.index;
            self.index += 1;
            if self.index == self.row_end {
                self.index += self.non_row_len;
                self.row_end = self.index + self.row_len;
            }
            Some(current)
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let rows_left = (self.end - self.index) / (self.row_len + self.non_row_len);
        // Modulus prevents double-counting remainder when on the first index of the row.
        let row_remainder = (self.row_end - self.index) % self.row_len;
        let remaining = self.row_len * rows_left + row_remainder;
        (remaining, Some(remaining))
    }
}

/// Indicates that a size has no integer square root
///
/// This is returned when standad rules cannot be created because their
/// zones cannot be arranged as squares.
#[derive(Debug)]
pub struct NonSquareError {
    size: usize,
}

impl NonSquareError {
    pub fn size(&self) -> usize { self.size }
}

impl fmt::Display for NonSquareError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} has no integer square root", self.size)
    }
}

impl error::Error for NonSquareError {
    fn description(&self) -> &str {
        "size's has no integer square root"
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::super::grid::CellId;

    #[test]
    fn test_rules_sanity() {
        let rules = toy_rules();
        assert_eq!(rules.size(), 4);
        assert_eq!(rules.clique_ids().count(), 3);
        assert_eq!(rules.cliques(CellId(0)).count(), 3);
        assert_eq!(rules.cliques(CellId(1)).count(), 2);
        assert_eq!(rules.cliques(CellId(2)).count(), 1);
        assert_eq!(rules.cliques(CellId(4)).count(), 2);
        assert_eq!(rules.cliques(CellId(6)).count(), 0); // Presumably wouldn't happen with real rules.
    }

    #[test]
    fn test_rules_consistency() {
        let various_rules = [
            toy_rules(),
            Rules::new(RegularCliquesIterator::new(2, 3)),
            Rules::new(RegularCliquesIterator::new(5, 4)),
            Rules::new_standard(4).unwrap(),
            Rules::new_standard(9).unwrap(),
            Rules::new_standard(16).unwrap(),
        ];

        for rules in &various_rules {
            for clique_id in rules.clique_ids() {
                assert_eq!(rules.cells(clique_id).count(), rules.size());
                assert_eq!(rules.cells(clique_id).cloned().collect::<Vec<_>>(), &rules[clique_id]);
                for &cell_id in &rules[clique_id] {
                    assert!(rules[cell_id].binary_search(&clique_id).is_ok());
                }
            }
            for cell_id in 0..rules.size() * rules.size() {
                let cell_id = CellId(cell_id);
                assert_eq!(rules.cliques(cell_id).cloned().collect::<Vec<_>>(), &rules[cell_id]);
                for &clique_id in &rules[cell_id] {
                    assert!(rules[clique_id].binary_search(&cell_id).is_ok());
                }
            }
        }
    }

    fn toy_rules() -> Rules {
        let cliques = [
            [ 0,  1,  2,  3],
            [ 0,  4,  8, 12],
            [ 0,  1,  4,  5],
        ];
        let cliques = cliques.iter().map(|clique| clique.iter().cloned().map(CellId));
        Rules::new(cliques)
    }

    #[test]
    fn test_rules_deduplication() {
        let cliques = [
            [ 0,  1,  2,  3],
            [ 0,  1,  2,  4],
            [ 3,  1,  0,  2],
        ];
        let cliques = cliques.iter().map(|clique| clique.iter().cloned().map(CellId));
        let rules = Rules::new(cliques);
        assert_eq!(rules.clique_ids().count(), 2);
    }

    #[test]
    fn test_rules_standard() {
        let standard_works = [false, true, false, false, true, false, false, false, false, true, false];
        for (size, &expected) in standard_works.iter().enumerate().skip(1) {
            assert_eq!(Rules::new_standard(size).is_ok(), expected);
        }
    }

    #[test]
    fn test_rules_standard_error() {
        let err = Rules::new_standard(12).unwrap_err();
        assert_eq!(err.size(), 12);
    }

    #[test]
    fn test_regular_cliques_values() {
        fn to_vecs<T, U>(cliques_iter: T) -> Vec<Vec<usize>>
            where T: Iterator<Item=U>, U: Iterator<Item=CellId> {
            cliques_iter.map(|clique_iter| {
                clique_iter.map(|CellId(cell_id)| cell_id).collect()
            }).collect()
        }

        let cliques = to_vecs(RegularCliquesIterator::new(2, 2));
        let expected = [
            [ 0,  1,  2,  3],
            [ 4,  5,  6,  7],
            [ 8,  9, 10, 11],
            [12, 13, 14, 15],

            [ 0,  4,  8, 12],
            [ 1,  5,  9, 13],
            [ 2,  6, 10, 14],
            [ 3,  7, 11, 15],

            [ 0,  1,  4,  5],
            [ 2,  3,  6,  7],
            [ 8,  9, 12, 13],
            [10, 11, 14, 15],
        ];
        assert_eq!(cliques, expected);

        let cliques = to_vecs(RegularCliquesIterator::new(3, 2));
        let expected = [
            [ 0,  1,  2,  3,  4,  5],
            [ 6,  7,  8,  9, 10, 11],
            [12, 13, 14, 15, 16, 17],
            [18, 19, 20, 21, 22, 23],
            [24, 25, 26, 27, 28, 29],
            [30, 31, 32, 33, 34, 35],

            [ 0,  6, 12, 18, 24, 30],
            [ 1,  7, 13, 19, 25, 31],
            [ 2,  8, 14, 20, 26, 32],
            [ 3,  9, 15, 21, 27, 33],
            [ 4, 10, 16, 22, 28, 34],
            [ 5, 11, 17, 23, 29, 35],

            [ 0,  1,  2,  6,  7,  8],
            [ 3,  4,  5,  9, 10, 11],
            [12, 13, 14, 18, 19, 20],
            [15, 16, 17, 21, 22, 23],
            [24, 25, 26, 30, 31, 32],
            [27, 28, 29, 33, 34, 35],
        ];
        assert_eq!(cliques, expected);

        let cliques = to_vecs(RegularCliquesIterator::new(3, 3));
        assert_eq!(cliques[0],  [ 0,  1,  2,  3,  4,  5,  6,  7,  8]);
        assert_eq!(cliques[8],  [72, 73, 74, 75, 76, 77, 78, 79, 80]);
        assert_eq!(cliques[9],  [ 0,  9, 18, 27, 36, 45, 54, 63, 72]);
        assert_eq!(cliques[17], [ 8, 17, 26, 35, 44, 53, 62, 71, 80]);
        assert_eq!(cliques[18], [ 0,  1,  2,  9, 10, 11, 18, 19, 20]);
        assert_eq!(cliques[22], [30, 31, 32, 39, 40, 41, 48, 49, 50]);
        assert_eq!(cliques[26], [60, 61, 62, 69, 70, 71, 78, 79, 80]);
    }

    #[test]
    fn test_regular_cliques_size_hints() {
        test_size_hint(12, RegularCliquesIterator::new(2, 2));
        test_size_hint(18, RegularCliquesIterator::new(3, 2));
        test_size_hint(27, RegularCliquesIterator::new(3, 3));
        test_size_hint(48, RegularCliquesIterator::new(4, 4));
    }

    #[test]
    fn test_rect_index_values() {
        let values: Vec<_> = RectIndexIter::new(4, 1..3, 1..3).collect();
        assert_eq!(values, [5, 6, 9, 10]);

        let values: Vec<_> = RectIndexIter::new(8, 3..5, 4..7).collect();
        assert_eq!(values, [35, 36, 43, 44, 51, 52]);

        let values: Vec<_> = RectIndexIter::new(3, 0..3, 0..4).collect();
        assert_eq!(values, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]);
    }

    #[test]
    fn test_rect_index_size_hints() {
        test_size_hint(4, RectIndexIter::new(4, 1..3, 1..3));
        test_size_hint(6, RectIndexIter::new(8, 3..5, 4..7));
        test_size_hint(12, RectIndexIter::new(3, 0..3, 0..4));
    }

    fn test_size_hint<T: Iterator>(mut expected: usize, mut iter: T) {
        while expected > 0 {
            assert_eq!(iter.size_hint(), (expected, Some(expected)));
            assert!(iter.next().is_some());
            expected -= 1;
        }
        assert_eq!(iter.size_hint(), (0, Some(0)));
        assert!(iter.next().is_none());
        assert_eq!(iter.size_hint(), (0, Some(0)));
    }
}
