//! Structures useful for solving sudoku problems

use std::collections;
use std::hash::Hash;
use std::iter::{Rev, Take, Zip};
use std::mem;
use std::ops::Deref;
use std::rc::Rc;
use std::slice::{ChunksMut, IterMut};

use super::grid::{CaseId, CellId, FromIndex, Grid, HasGridSize, ValueId};
use super::rules::{CliqueId, Rules};

/// Solves a `Grid`
///
/// This is a simple wrapper for `SolutionsIter` that uses sane defaults.
pub fn solve(grid: Grid, rules: Rules) -> Solution {
    assert_eq!(grid.size(), rules.size());
    let rules = Rc::new(rules);
    let partitioner = Partitioner::new(rules);
    let strategies = vec![Box::new(partitioner) as Box<Strategy>];
    let mut iter = SolutionsIter::new(grid, strategies);
    match (iter.next(), iter.next()) {
        (Some(grid), Some(_)) => Solution::NonUnique(grid),
        (Some(grid), None)    => Solution::Unique(grid),
        (None, _)             => Solution::Unsolvable,
    }
}

/// Solution to a sudoku puzzle.
pub enum Solution {
    /// The puzzle was solved.
    Unique(Grid),
    /// The puzzle was solved, but was improper (other solutions exist).
    NonUnique(Grid),
    /// The puzzle was unsolvable (a contradiction was found).
    Unsolvable,
}

impl Solution {
    /// Unwraps the `Grid` that contains the results of the `Solution`.
    pub fn grid(self) -> Option<Grid> {
        match self {
            Solution::Unique(grid)    => Some(grid),
            Solution::NonUnique(grid) => Some(grid),
            Solution::Unsolvable      => None,
        }
    }
}

/// Iterates over all solutions to a sudoku puzzle
///
/// Given a grid of initial conditions and a vector of (usually non-recursive) `Strategy`s, this iterates
/// over all solutions to the puzzle. It attempts to solve the puzzle by feeding newly discovered inferences
/// back into all `Strategy`s. If the puzzle cannot be resolved via `Strategy`s (or it has multiple solutions)
/// this falls back to guessing and recursion as necessary (but it shouldn't exhaust the stack).
pub struct SolutionsIter {
    grids: Vec<Grid>,
    strategies_per_grid: usize,
    strategies: Vec<Box<Strategy>>,
}

impl SolutionsIter {
    /// Constructs a `SolutionsIter` from initial conditions and a set of strategies.
    pub fn new(mut grid: Grid, mut strategies: Vec<Box<Strategy>>) -> SolutionsIter {
        let vetoes = grid.vetoes().collect();
        SolutionsIter::deduce(&mut grid, &mut strategies, vetoes);
        SolutionsIter {
            grids: vec![grid],
            strategies_per_grid: strategies.len(),
            strategies: strategies,
        }
    }

    // Incorporate vetos, taking as much as possible into account without guessing.
    fn deduce(grid: &mut Grid, strategies: &mut [Box<Strategy>], mut vetoes: Vec<CaseId>) {
        while vetoes.len() > 0 {
            let mut inferences: Vec<CaseId> = vec![];
            for strategy in strategies.iter_mut() {
                debug_assert_eq!(strategy.inferences().len(), 0);
                // This is a minimal-copy way of collecting new inferences into `inferences`.
                mem::swap(&mut inferences, strategy.inferences());
                strategy.veto(&vetoes[..]);
                mem::swap(&mut inferences, strategy.inferences());
            }
            grid.veto(inferences.iter().cloned());
            vetoes = inferences;
        }
    }

    // Try to find a good cell to guess values for, returning it and the number possible values it might have.
    // If any cells lack possibilities, return that. (no point guessing if a puzzle can't be solved)
    // Else, if any cells have at least two possibilies, choose one with the a minimal number of possibilities
    // Else, the puzzle is solved and it doesn't matter which cell we return.
    fn find_least_underconstrained_cell(grid: &Grid) -> (CellId, usize) {
        fn count_true(values: &[bool]) -> usize {
            values.iter().filter(|&&b| b).count()
        }
        let (choices, cell) = grid.cells()
                                  // We swap order so min sorts correctly
                                  .map(|(cell_id, values)| (count_true(values), cell_id))
                                  .filter(|&(choices, _)| choices != 1)
                                  .min()
                                  .unwrap_or((1, CellId(0)));
        (cell, choices)
    }

    // Pops a (Grid, [Box<Strategy>]) pair off the top of the stack,
    // and pushes `n` duplicates of it back onto the stack.
    fn duplicate_last_grid_n_times(&mut self, n: usize) {
        let grid = self.grids.pop().expect("SolutionsIter bug: duplicate_last_n_grids called on empty iter");
        let split_index = self.strategies.len() - self.strategies_per_grid;
        let strategies = self.strategies.split_off(split_index);
        for _ in 1..n {
            self.grids.push(grid.clone());
            self.strategies.extend(strategies.iter().map(|s| s.boxed_clone()));
        }
        self.grids.push(grid);
        self.strategies.extend(strategies.into_iter());
    }

    // Returns `n` pairs of (Grid, [Box<Strategy>]) from the top of the stack.
    fn last_n_grids(&mut self, n: usize) -> Take<Rev<Zip<IterMut<Grid>, ChunksMut<Box<Strategy>>>>> {
        self.grids.iter_mut()
            .zip(self.strategies.chunks_mut(self.strategies_per_grid))
            .rev()
            .take(n)
    }
}

impl Iterator for SolutionsIter {
    type Item = Grid;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(grid) = self.grids.pop() {
            let (cell, number_of_choices) = SolutionsIter::find_least_underconstrained_cell(&grid);
            let new_strategies_len = self.strategies.len() - self.strategies_per_grid;
            if number_of_choices == 0 {
                self.strategies.truncate(new_strategies_len);
                continue;
            }
            if number_of_choices == 1 {
                self.strategies.truncate(new_strategies_len);
                return Some(grid);
            }

            // Hookay, looks like we'll have to guess. :(
            // Start by prepping grids and strategies... wish I could figure out how to do this with one fewer allocations.
            self.grids.push(grid);
            self.duplicate_last_grid_n_times(number_of_choices);
            for (n, (mut grid, mut strategies)) in self.last_n_grids(number_of_choices).enumerate() {
                let mut vetoes: Vec<CaseId> = grid.cell(cell)
                                              .filter(|&(_, &possible)| possible)
                                              .map(|(case_id, _)| case_id)
                                              .collect();
                vetoes.swap_remove(n);
                SolutionsIter::deduce(&mut grid, &mut strategies, vetoes);
            }
        }
        None
    }
}

/// Common interface for sudoku strategies
///
/// A `Strategy` is something that can narrow down the possible solutions of a puzzle, but which
/// may not be able to solve a puzzle by itself. The idea is that a solver could combine multiple
/// strategies to minimize the need for guessing.
///
/// Note that a `Strategy` is NOT required to incorporate its own inferences, so for best results
/// a `Strategy`'s own inferences should be fed back into it.
pub trait Strategy {
    /// Marks `CaseId`s as impossible.
    ///
    /// This is used to inform the `Strategy` of cell/value combinations that are known
    /// to be impossible. The `Strategy` must ignore any vetoes it's already aware of.
    fn veto(&mut self, vetoes: &[CaseId]);

    /// Returns a mutable reference to a Vec of `CaseId`s inferred to be impossible.
    ///
    /// As `CaseId`s are vetoed, new inferences will be pushed onto the `Vec` returned by
    /// `inferences()`. It's fine to mess with the `Vec` however you want, such as clearing
    /// it after reading it.
    ///
    /// Note that `inferences()` is allowed to return `CaseId`s that have already been marked
    /// as impossible.
    fn inferences(&mut self) -> &mut Vec<CaseId>;

    /// Returns a boxed clone of the `Strategy`.
    ///
    /// This allows the `Strategy` to be copied without knowledge of its type.
    fn boxed_clone(&self) -> Box<Strategy>;
}

/// Infers solution constraints by partitioning possibilities
///
/// Given the constraints of a sudoku puzzle, a `Partitioner` can infer additional constraints,
/// whittling down the possibities, potentially even solving a puzzle by itself. It figures out
/// constraints by detecting when possible values/positions can be split into disjoint partitions.
/// For example, if two cells in the same clique are both limited to having the values 5 or 8,
/// then no other cells in the clique can be 5 or 8. Similarly, if the values 3 and 4 can only be
/// in two possible cells, then those cells cannot be anything other than a 3 or 4. The
/// partitioner applies that idea with partitions of any size, not just two values/cells. In
/// particular, handling partitions of size 1 is equivalent to simple sudoku strategies like
/// eliminating values already used by cells in the same clique. A major limitation of
/// `Partitioner` is that it can only detect explicit partitions, not implicit ones: Although
/// it can detect a partition where three cells are each restricted to the values 4, 5 and 6, it
/// can't detect a partition where a cell is 4 or 5, another is 5 or 6 and a final cell is 4 or 6.
///
/// Once a `Partitioner` is constructed, `veto()` is used to inform it of any `CaseId`s that
/// cannot be true. As cases are vetoed, the `Partitioner` accumulates `inferences`. Note that
/// currently `Partitioner` doesn't automatically use the inferences it generates. This has the
/// advantage that calls to `veto()` should complete in time proportional to the number of
/// `CaseId`s vetoed, but has the disadvantage that you must feed the `Partitioner`'s `inferences`
/// back into itself to get the most `inferences` out of it.
///
/// # Examples
///
/// ```rust
/// use std::fmt::Write;
/// use std::mem;
///
/// use rusudoku::grid::Grid;
/// use rusudoku::rules::Rules;
/// use rusudoku::solver::Partitioner;
///
/// let puzzle = "1 _ _ _\n\
///               _ 2 _ _\n\
///               3 _ _ _\n\
///               _ _ 4 _\n";
/// let mut lines = puzzle.lines().map(|line| Ok(line.to_string()));
/// let mut grid = Grid::read(&mut lines).unwrap();
/// let rules = Rules::new_standard(grid.size()).unwrap();
/// let mut partitioner = Partitioner::new(&rules);
/// let mut vetoes: Vec<_> = grid.vetoes().collect();
/// while vetoes.len() > 0 {
///     partitioner.veto(vetoes.iter().cloned());
///     grid.veto(vetoes.iter().cloned());
///     vetoes = mem::replace(&mut partitioner.inferences, vec![]);
/// }
/// let mut output = String::new();
/// write!(&mut output, "{}", grid);
/// assert_eq!(output, "1 3 2 4\n\
///                     4 2 3 1\n\
///                     3 4 1 2\n\
///                     2 1 4 3\n");
/// ```
#[derive(Clone)]
pub struct Partitioner<R> {
    rules: R,
    grid: Grid,
    lookups: LookupPair,
    /// The list of `CaseId`s inferred to be impossible.
    ///
    /// As `CaseId`s are vetoed, new inferences will be pushed onto this `Vec`. It's fine
    /// to mess with `inferences` however you want, such as clearing it after reading it.
    pub inferences: Vec<CaseId>,
}

// Pair of mappings from possibilities to referrers (see below)
#[derive(Clone)]
struct LookupPair {
    valueset_cells: Lookup<ValueId, CellId>,
    cellset_values: Lookup<CellId, ValueId>,
}

type Lookup<K, V> = collections::HashMap<(CliqueId, Vec<K>), Vec<V>>;

impl<'a> From<&'a mut LookupPair> for &'a mut Lookup<ValueId, CellId> {
    fn from(other: &'a mut LookupPair) -> Self { &mut other.valueset_cells }
}

impl<'a> From<&'a mut LookupPair> for &'a mut Lookup<CellId, ValueId> {
    fn from(other: &'a mut LookupPair) -> Self { &mut other.cellset_values }
}

// The way this works is: It thinks of each clique as having a binary relation between
// values and the clique's cells. It knows it has found a partition when N cells all have
// the same N values. When that happens it knows all other cells cannot have those N values.
// Symmetrically, when N values all have the same N cells, then other values cannot have
// those N cells.
//
// In order to efficiently detect this, each clique uses a pair of mappings. To detect
// when N cells have the same N values, it has a mapping from "possibilities" (sets of
// values) to the list of "referrers" (cells that have those possibilities). When updating
// these bookkeeping structures, it checks if number possibilities is the same as the number
// of referrers; if so it subtracts the possibilities from non-referrers.
//
// Likewise, it has symmetric data structures for finding when N values have the same N
// cells. In this case, the "possibilities" are a set of cells, and the "referrers" are
// sets of values.
//
// In order to avoid having nested mappings (and the associated extra allocations), all
// cliques share a pair of mappings (self.lookups) from possibilities to referrers. Each
// clique's possibilities are kept separate from one another by including the clique's id
// in the mapping's key.
//
// Additionally, in order to aid with comparison (and finding elements) without requiring
// too many allocations, possibilities and referrers are stored as sorted Vecs.
//
// One final note about terminology used by this code... An "axis" is the set of all
// elements that could potentially be in a set of "possibilities", and a "cross-axis"
// is the set of all elements that could potentially be in a set of "referrers".
// The terms "axis" and "cross-axis" come from thinking of a clique's relation between
// cells and values as 2D grid. In generic type parameters, the axis's type is A and
// the cross-axis's type is C.
impl<'a, R> Partitioner<R>
    where R: Deref<Target=Rules> + Clone + 'a {

    /// Creates a new `Partitioner`
    ///
    /// This requires a reference to a set of `Rules` so the `Partitioner` knows what cells
    /// must be different from eachother.
    pub fn new(rules: R) -> Partitioner<R> {
        let grid = Grid::new(rules.size());
        let mut valueset_cells = collections::HashMap::new();
        let mut cellset_values = collections::HashMap::new();
        let values: Vec<_> = grid.range_iter::<ValueId>().collect();
        for clique_id in rules.clique_ids() {
            let cells = &rules[clique_id];
            valueset_cells.insert((clique_id, values.clone()), cells.to_vec());
            cellset_values.insert((clique_id, cells.to_vec()), values.clone());
        }
        Partitioner {
            grid: grid,
            rules: rules,
            lookups: LookupPair {
                valueset_cells: valueset_cells,
                cellset_values: cellset_values,
            },
            inferences: vec![],
        }
    }

    /// Marks `CaseId`s as impossible.
    ///
    /// This is used to inform the `Partitioner` of cell/value combinations that are known
    /// to be impossible.
    pub fn veto<I>(&mut self, vetoes: I)
        where I: Iterator<Item=CaseId> {
        let rules = &mut self.rules.clone();
        for veto in vetoes {
            if !self.grid[veto] {
                continue;
            }
            let (veto_cell, veto_value): (CellId, ValueId) = self.grid.convert(veto);
            let all_values: Vec<_> = self.grid.range_iter::<ValueId>().collect();
            for &clique_id in rules.cliques(veto_cell) {
                let cells = &rules[clique_id];
                self.remove_possibility(clique_id,
                                        (&all_values[..], cells),
                                        (veto_value, veto_cell));
                self.remove_possibility(clique_id,
                                        (cells, &all_values[..]),
                                        (veto_cell, veto_value));
            }
            self.grid[veto] = false;
        }
    }

    // The core idea of what this does, is it marks `cross_axis_item` as
    // no longer referring to a set of possibilities that includes `axis_item`,
    // updating the bookkeeping as appropriate
    fn remove_possibility<A, C>(&'a mut self, clique_id: CliqueId,
                                (axis, cross_axis): (&[A], &[C]),
                                (axis_item, cross_axis_item): (A, C))
        where A: Copy + Eq + Hash + Ord + 'a,
              C: Copy + Ord + 'a,
              CaseId: FromIndex<(A,C)>,
              &'a mut Lookup<A, C>: From<&'a mut LookupPair> {

        let grid = &self.grid;
        let referrers_lookup: &mut Lookup<A, C> = (&mut self.lookups).into();
        let possibilities: Vec<_> =
            axis.iter()
                .cloned()
                .filter(|&axis_id| {
                    let case_id: CaseId = grid.convert((axis_id, cross_axis_item));
                    grid[case_id]
                }).collect();
        let mut key = (clique_id, possibilities);

        // Here we remove `cross_axis_item` from the list of `referrers` of `possibilities`,
        // and check if we've found a partition.
        let referrers_len = {
            let referrers = referrers_lookup.get_mut(&key)
                                            .expect("Partitioner bug: \
                                                     No referrers for possibilities");
            Self::remove(referrers, &cross_axis_item);
            Self::check_for_partition(&key.1,
                                      referrers,
                                      cross_axis,
                                      grid,
                                      &mut self.inferences);
            referrers.len()
        };
        if referrers_len == 0 {
            referrers_lookup.remove(&key);
        }

        // `cross_axis_item`s new `possibilties` are (possibilities - axis_item)
        // It's easiest/fastest to just tweak `possibilities` to remove the `axis_item`.
        Self::remove(&mut key.1, &axis_item);

        // Here we add `cross_axis_item` to the list of `referrers` of the the new
        // `possibilities` and check if we've found a partition.
        if !referrers_lookup.contains_key(&key) { // avoiding entry() because it'd consume key
            referrers_lookup.insert(key.clone(), vec![]);
        }
        let referrers = referrers_lookup.get_mut(&key)
                                        .expect("Partitioner bug: \
                                                 No referrers for new possibilities.");
        Self::insert(referrers, cross_axis_item);
        Self::check_for_partition(&key.1,
                                  referrers,
                                  cross_axis,
                                  grid,
                                  &mut self.inferences);
    }

    fn check_for_partition<A, C>(possibilities: &Vec<A>,
                        referrers:  &[C],
                        cross_axis: &[C],
                        grid: &Grid,
                        inferences: &mut Vec<CaseId>)
        where A: Copy,
              C: Copy + Ord,
              CaseId: FromIndex<(A,C)> {
        if possibilities.len() == referrers.len() {
            // This is really saying "veto the cartesian product of non-referrers and
            // possibilities".
            for &cross_element in cross_axis {
                if referrers.binary_search(&cross_element).is_err() {
                    for &element in possibilities {
                        let case_id: CaseId = grid.convert((element, cross_element));
                        inferences.push(case_id);
                    }
                }
            }
        }
    }

    // Removes element `e` from an ordered Vec `v`, or else panics
    // This is just to simplify remove_possibility() slightly.
    fn remove<T: Ord>(v: &mut Vec<T>, e: &T) {
        let i = v.binary_search(e)
                 .expect("Partitioner bug: Bookkeeping missing expected element");
        v.remove(i);
    }

    // Inserts element `e` into an ordered Vec `v`, or else panics
    // This is just to simplify remove_possibility() slightly.
    fn insert<T: Ord>(v: &mut Vec<T>, e: T) {
        let i = v.binary_search(&e)
                 .err().expect("Partitioner bug: Bookkeeping already had element.");
        v.insert(i, e);
    }
}

impl<R> Strategy for Partitioner<R>
    where R: Deref<Target=Rules> + Clone + 'static {

    fn veto(&mut self, vetoes: &[CaseId]) {
        self.veto(vetoes.iter().cloned());
    }

    fn inferences(&mut self) -> &mut Vec<CaseId> {
        &mut self.inferences
    }

    fn boxed_clone(&self) -> Box<Strategy> {
        Box::new(self.clone())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::fmt::Write;
    use std::mem;
    use std::rc::Rc;

    use super::super::grid::{CaseId, Grid};
    use super::super::rules::Rules;

    #[test]
    fn test_value_exclusion() {
        // Restrict upper-left cell to be a 1.
        let vetoes = [1, 2, 3];
        assert_eq!(infer_from_vetoes(4, &vetoes), [
            // The rest of the row is restricted from being 1,
            4, 8, 12,
            // as is the rest of the zone,
            16, 20,
            // and the rest of the column.
            32, 48,
        ]);
    }

    #[test]
    fn test_cell_exclusion() {
        // Veto the right 3 cells of the top row from being 1.
        let vetoes = [4, 8, 12];
        assert_eq!(infer_from_vetoes(4, &vetoes), [
            // The top left cell is required to be 1.
            1, 2, 3,
        ]);
    }

    #[test]
    fn test_multicell_partitioning() {
        // Restrict the left 2 cells of the top row to be a 1 or 2.
        let vetoes = [2, 3, 6, 7];
        assert_eq!(infer_from_vetoes(4, &vetoes), [
            // The rest of the row is restricted from being 1 or 2,
            8, 9, 12, 13,
            // as is the rest of the zone.
            16, 17, 20, 21,
        ]);
    }

    fn infer_from_vetoes(size: usize, vetoes: &[usize]) -> Vec<usize> {
        let rules = Rules::new_standard(size).unwrap();
        let mut partitioner = Partitioner::new(&rules);
        partitioner.veto(vetoes.iter().cloned().map(CaseId));
        partitioner.inferences.sort();
        partitioner.inferences.dedup();
        partitioner.inferences.into_iter()
                              .map(|CaseId(case_id)| case_id)
                              .collect()
    }

    #[test]
    fn test_solve_basic4() {
        let solution = fully_partition("1 _ _ _\n\
                                        _ 2 _ _\n\
                                        3 _ _ _\n\
                                        _ _ 4 _\n");

        assert_eq!(solution, "1 3 2 4\n\
                              4 2 3 1\n\
                              3 4 1 2\n\
                              2 1 4 3\n");
    }

    #[test]
    fn test_solve_classic9() {
        let solution = fully_partition("5 3 _ _ 7 _ _ _ _\n\
                                        6 _ _ 1 9 5 _ _ _\n\
                                        _ 9 8 _ _ _ _ 6 _\n\
                                        8 _ _ _ 6 _ _ _ 3\n\
                                        4 _ _ 8 _ 3 _ _ 1\n\
                                        7 _ _ _ 2 _ _ _ 6\n\
                                        _ 6 _ _ _ _ 2 8 _\n\
                                        _ _ _ 4 1 9 _ _ 5\n\
                                        _ _ _ _ 8 _ _ 7 9\n");

        assert_eq!(solution, "5 3 4 6 7 8 9 1 2\n\
                              6 7 2 1 9 5 3 4 8\n\
                              1 9 8 3 4 2 5 6 7\n\
                              8 5 9 7 6 1 4 2 3\n\
                              4 2 6 8 5 3 7 9 1\n\
                              7 1 3 9 2 4 8 5 6\n\
                              9 6 1 5 3 7 2 8 4\n\
                              2 8 7 4 1 9 6 3 5\n\
                              3 4 5 2 8 6 1 7 9\n");
    }

    fn fully_partition(input: &str) -> String {
        let (mut grid, rules) = read_grid(input);
        let mut partitioner = Partitioner::new(&rules);
        let mut vetoes: Vec<_> = grid.vetoes().collect();
        while vetoes.len() > 0 {
            partitioner.veto(vetoes.iter().cloned());
            grid.veto(vetoes.iter().cloned());
            vetoes = mem::replace(&mut partitioner.inferences, vec![]);
        }
        let mut output = String::new();
        let _ = write!(&mut output, "{}", grid);
        output
    }

    #[test]
    fn test_partitioner_as_strategy() {
        let rules = Rules::new_standard(4).unwrap();
        let p = &mut Partitioner::new(Rc::new(rules)) as &mut Strategy;
        let vetoes = vec![CaseId(1), CaseId(2), CaseId(3)];
        p.veto(&vetoes);
        let mut p2 = p.boxed_clone();
        assert_eq!(p2.inferences(), p.inferences());
        assert!(p2.inferences().len() > 0);
    }

    #[test]
    fn test_solve_classic9_evil() {
        let solution = solve_str("_ _ _ _ _ _ _ _ _\n\
                                  _ _ _ _ _ _ 3 _ 8\n\
                                  _ _ _ _ _ 2 5 6 _\n\
                                  _ _ 9 _ 6 _ _ _ _\n\
                                  _ _ 6 _ _ 3 7 _ _\n\
                                  _ _ _ _ 2 _ 8 5 _\n\
                                  _ 6 _ _ 3 7 _ _ 4\n\
                                  _ 8 _ _ 1 9 _ _ _\n\
                                  _ 4 5 _ _ _ _ 7 9\n");

        assert_eq!(solution, "Unique\n\
                              5 3 4 6 7 8 9 1 2\n\
                              6 7 2 1 9 5 3 4 8\n\
                              1 9 8 3 4 2 5 6 7\n\
                              8 5 9 7 6 1 4 2 3\n\
                              4 2 6 8 5 3 7 9 1\n\
                              7 1 3 9 2 4 8 5 6\n\
                              9 6 1 5 3 7 2 8 4\n\
                              2 8 7 4 1 9 6 3 5\n\
                              3 4 5 2 8 6 1 7 9\n");
    }

    #[test]
    fn test_unsolvable() {
        let (grid, rules) = read_grid("_ _ 1 _\n\
                                       _ 2 _ _\n\
                                       3 _ _ _\n\
                                       4 _ _ _\n");
        assert!( solve(grid, rules).grid().is_none() );
    }

    #[test]
    fn test_multuple_solutions() {
        let solution = solve_str("1 2 3 4\n\
                                  4 3 _ _\n\
                                  3 4 _ _\n\
                                  2 1 4 3\n");
        assert!(
            solution == "NonUnique\n\
                         1 2 3 4\n\
                         4 3 1 2\n\
                         3 4 2 1\n\
                         2 1 4 3\n" ||
            solution == "NonUnique\n\
                         1 2 3 4\n\
                         4 3 2 1\n\
                         3 4 1 2\n\
                         2 1 4 3\n"
        );
    }

    fn solve_str(input: &str) -> String {
        let (grid, rules) = read_grid(input);
        let solution = solve(grid, rules);
        let mut output = String::new();
        let _ = match solution {
            Solution::Unique(grid)    => write!(&mut output, "Unique\n{}",    grid),
            Solution::NonUnique(grid) => write!(&mut output, "NonUnique\n{}", grid),
            Solution::Unsolvable      => write!(&mut output, "Unsolvable\n"),
        };
        output
    }

    fn read_grid(input: &str) -> (Grid, Rules) {
        let mut lines = input.lines().map(|line| Ok(line.to_string()));
        let grid = Grid::read(&mut lines).unwrap();
        let rules = Rules::new_standard(grid.size()).unwrap();
        (grid, rules)
    }
}
