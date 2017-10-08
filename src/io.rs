use std::error::Error as StdError;
use std::fmt;
use std::io;
use std::ops::{Range, RangeTo};

use super::grid::Grid;

/// Function capable of parsing cells, given a `&str`.
pub type CellParserFn = Fn(&str) -> Result<Option<usize>, Box<StdError>>;

/// Reads iterator of lines to construct a `Grid`.
///
/// # Examples
///
/// ```rust
/// # use std::error;
/// # use std::io;
/// use rusudoku::grid::io::{CellParserFn, GridReader};
///
/// fn hex_cell(token: &str) -> Result<Option<usize>, Box<std::error::Error>> {
///     let chars = "_123456789ABCDEF0";
///     if token.len() == 1 {
///         if let Some(i) = chars.find(token) {
///             return Ok(if i > 0 { Some(i) } else { None })
///         }
///     }
///     Err(Box::new("".parse::<usize>().unwrap_err()))
/// }
///
/// let mut reader = GridReader::new();
/// reader.set_size_range(16);
/// reader.set_cell_parser(Box::new(hex_cell) as Box<CellParserFn>);
/// let input = "whatever";
/// let mut lines = input.lines().map(|line| Ok(line.to_string()));
/// let grid_or_err = reader.read(&mut lines);
/// ```
pub struct GridReader {
    size_range: Range<usize>,
    cell_parser: Box<CellParserFn>,
}

impl GridReader {
    /// Returns a new `GridReader` with reasonable defaults.
    ///
    /// The `GridReader` will accept grids with a size of up to 1024, and expects filled cells
    /// be represented as decimal numbers, while empty cells are represented as underscores,
    /// question marks, or a few other characters.
    pub fn new() -> GridReader {
        fn cell_parser(token: &str) -> Result<Option<usize>, Box<StdError>> {
            match token {
                "?" | "_" | "-" | "." | "*" | "X" => Ok(None),
                _ => token.parse::<usize>().map(Some)
                                           .map_err(|err| Box::new(err) as Box<StdError>),
            }
        }
        GridReader {
            size_range: SizeRange::from(1..1025).0,
            cell_parser: Box::new(cell_parser),
        }
    }

    /// Sets what grid sizes may be parsed.
    ///
    /// `range` may be one of several types:
    ///
    /// * `usize`: Indicates the only size accepted.
    /// * `Range<usize>` or `RangeTo<usize>`: Indicates a range of accepted sizes. Note that the
    ///   upper bound is excluded, indicating lowest size rejected.
    pub fn set_size_range<T>(&mut self, range: T)
        where SizeRange: From<T> {
        self.size_range = SizeRange::from(range).0;
    }

    fn is_allowed_size(&self, size: usize) -> bool { self.size_range.start <= size && size < self.size_range.end }

    /// Controls how cells are parsed.
    ///
    /// `cell_parser` should be a closure taking a `&str` token (guaranteed to have no whitespace)
    /// and returning a `Result` containing either an `Option<size>` (indicated a successful
    /// parse of a numbered or empty cell), or a `Box<std::error::Error>` (indicating an
    /// arbitrary parse error).
    pub fn set_cell_parser(&mut self, cell_parser: Box<CellParserFn>) {
        self.cell_parser = cell_parser;
    }

    /// Constructs a `Grid` from an iterator of lines.
    ///
    /// Consumes lines from the given iterator until it encounters one consisting of whitespace,
    /// where each line is interpreted as a row, with each cell separated by whitespace.
    /// The rows must form a square (with an allowed size determined by `set_size_filter(...)`).
    /// Any errors encountered will halt consumption of lines mid-way.
    pub fn read<I>(&self, lines: &mut I) -> Result<Grid, Error>
        where I: Iterator<Item=io::Result<String>> {
        let rows = try!(self.parse_rows(lines));
        Ok(GridReader::rows_to_grid(rows))
    }

    fn parse_rows<I>(&self, lines: &mut I) -> Result<Vec<Vec<Option<usize>>>, Error>
        where I: Iterator<Item=io::Result<String>> {
        let mut rows = vec!();
        for (y, line) in (0..self.size_range.end+1).zip(lines) {
            let line = try!(line);
            let cells = line.split_whitespace()
                            .map(|token| (*self.cell_parser)(token))
                            .zip(0..self.size_range.end+1)
                            .map(|(result, x)| result.map_err(|e|
                                Error::CellParse{ x: x, y: y, cause: e }
                            ));
            let cells: Vec<_> = try!(self.coerce_oversized_errors(cells.collect()));
            if cells.len() == 0 {
                break;
            }
            rows.push(cells)
        }
        if !self.is_allowed_size(rows.len()) {
            return Err(Error::GridSize{size: rows.len(), expected: self.size_range.clone()});
        }
        for (y, row) in rows.iter().enumerate() {
            if row.len() != rows.len() {
                return Err(Error::RowLength { y: y, size: row.len(), expected: rows.len() });
            }
        }
        try!(GridReader::check_cell_values(&rows));
        Ok(rows)
    }

    // It might be confusing for parse_rows() to return ParseCell errors for cells that
    // fall outside of allowed sizes, so we convert such errors into GridSize or RowLength
    // errors. The advantage of using RowLength errors is that it can convey information
    // about WHICH row was too long.
    fn coerce_oversized_errors<T>(&self, result: Result<T, Error>) -> Result<T, Error> {
        let max_size = self.size_range.end - 1;
        match result {
            Err(Error::CellParse{y, ..}) if y == max_size =>
                Err(Error::GridSize{
                    size: max_size + 1, expected: self.size_range.clone()
                }),
            Err(Error::CellParse{x, y, ..}) if x == max_size =>
                Err(Error::RowLength {
                    y: y, size: max_size + 1, expected: max_size
                }),
            _ => result,
        }
    }

    fn check_cell_values(rows: &Vec<Vec<Option<usize>>>) -> Result<(), Error> {
        let max = rows.len();
        for (y, row) in rows.iter().enumerate() {
            for (x, &cell) in row.iter().enumerate() {
                if let Some(value) = cell {
                    if value < 1 || max < value {
                        return Err(Error::CellValue{ x: x, y: y, value: value, expected: 1..max+1 });
                    }
                }
            }
        }
        Ok(())
    }

    fn rows_to_grid(rows: Vec<Vec<Option<usize>>>) -> Grid {
        let mut grid = Grid::new(rows.len());
        for (src_cell, (_, dst_cell)) in rows.into_iter()
                                             .flat_map(|row| row.into_iter())
                                             .zip(grid.cells_mut()) {
            if let Some(value) = src_cell {
                for possibility in dst_cell.iter_mut() {
                    *possibility = false;
                }
                dst_cell[value-1] = true;
            }
        }
        grid
    }
}

/// A helper type for representing a range of grid-sizes that can be parsed.
///
/// This exists to simulate overloading `GridReader.set_size_range()`
pub struct SizeRange(Range<usize>);

impl From<RangeTo<usize>> for SizeRange {
    fn from(range: RangeTo<usize>) -> Self { SizeRange(1..range.end) }
}

impl From<Range<usize>> for SizeRange {
    fn from(range: Range<usize>) -> Self { SizeRange(range) }
}

impl From<usize> for SizeRange {
    fn from(size: usize) -> Self { SizeRange(size..size+1) }
}

/// A function capable of writing cells, given a buffer, a width, and a cell.
pub type CellWriterFn = Fn(&mut fmt::Write, usize, Option<usize>) -> fmt::Result;

/// Writes a `Grid` to a `std::fmt::Write`
///
/// # Examples
///
/// ```rust
/// # use std::fmt;
/// # use rusudoku::grid::Grid;
/// use rusudoku::grid::io::{CellWriterFn, GridWriter};
///
/// fn hex_cell(w: &mut std::fmt::Write, width: usize, cell: Option<usize>) -> std::fmt::Result {
///     let chars: Vec<_> = "_123456789ABCDEF0".chars().collect();
///     write!(w, "{:>1$}", chars[cell.unwrap_or(0)], width)
/// }
///
/// let grid = Grid::new(16);
/// // add_constraints(grid);
/// let mut writer = GridWriter::new();
/// writer.set_cell_writer(Box::new(hex_cell) as Box<CellWriterFn>);
/// let mut output = String::new();
/// writer.write(&mut output, &grid).unwrap();
/// ```
pub struct GridWriter {
    cell_writer: Box<CellWriterFn>,
}

impl GridWriter {
    /// Returns a new `GridWriter` with reasonable defaults.
    ///
    /// In particular, cells are written as right-align decimal numbers with empty cells
    /// displayed as underscores.
    pub fn new() -> GridWriter {
        GridWriter {
            cell_writer: CellWriter::from("_").0,
        }
    }

    /// Controls how cells are written.
    ///
    /// `writer` may be one of two types:
    ///
    /// * `&str`: When a cell has a value, it's printed as a right-aligned decimal number.
    ///   Empty cells are depicted with the given `&str`, right aligned.
    /// * `Box<Fn(&mut std::fmt::Write, usize, Option<usize>) -> std::fmt::Result>`: Allows
    ///   full control over cell formatting. The given function is passed a `&mut Write`, the
    ///   desired cell width in characters, and the value of the cell. It's expected to `write!`
    ///   the cell's contents to the `Write` and return a `std::fmt::Result`.
    pub fn set_cell_writer<T>(&mut self, writer: T)
        where CellWriter: From<T> {
        self.cell_writer = CellWriter::from(writer).0;
    }

    /// Prints a `Grid` to a `std::fmt::Formatter`.
    ///
    /// The Grid is printed as multiple lines of text, each representing a row. Each
    /// row is a whitespace-separated sequence of cells, with empty cells printed
    /// according to `set_empty_cell(...)`.
    pub fn write(&self, w: &mut fmt::Write, grid: &Grid) -> fmt::Result {
        // Buggy, but only for stuff too large to fit on the screen.
        // Maybe calculate this via formatting instead?
        let num_width = (grid.size() as f64).log(10.0).floor() as usize + 1;

        let whitespace = (0..grid.size()).rev().cycle().map(|x| if x == 0 {"\n"} else {" "});

        // Iterator of Option<usize>, where Some(x) indicates sole possibility for that cell
        let cells = grid.cells().map(|(_, possibilities)| {
            let mut possibilities = possibilities.iter();
            let number = possibilities.by_ref().position(|&possible| possible).map(|n| n + 1);
            if possibilities.any(|&b| b) {None} else {number} // Return None if >1 possibilities
        });

        for (cell, ws) in cells.zip(whitespace) {
            try!((*self.cell_writer)(w, num_width, cell));
            try!(write!(w, "{}", ws));
        }

        Ok(())
    }
}

/// A helper type for representing ways of writing a cell.
///
/// This exists to simulate overloading `GridWritier.set_cell_writer()`
pub struct CellWriter(Box<CellWriterFn>);

impl From<Box<CellWriterFn>> for CellWriter {
    fn from(closure: Box<CellWriterFn>) -> Self {
        CellWriter(closure)
    }
}

impl<'a> From<&'a str> for CellWriter {
    fn from(empty: &str) -> Self {
        let empty = empty.to_string();
        CellWriter(Box::new(move |w: &mut fmt::Write, width, cell| {
            match cell {
                Some(x) => write!(w, "{:>1$}",     x, width),
                None    => write!(w, "{:>1$}", empty, width),
            }
        }))
    }
}

/// Grid read error.
///
/// Indicates a problem with reading a `Grid`.
#[derive(Debug)]
pub enum Error {
    /// Wraps any `std::io::Error` that occurs during reading.
    IO(io::Error),
    /// Indicates that a cell could not be parsed.
    CellParse {
        /// Column of error, counting from 0.
        x: usize,
        /// Row of error, counting from 0.
        y: usize,
        /// The particular parsing problem that caused the error.
        cause: Box<StdError>,
    },
    CellValue {
        /// Column of error, counting from 0.
        x: usize,
        /// Row of error, counting from 0.
        y: usize,
        /// The value found.
        value: usize,
        /// The range of values that would be ok.
        expected: Range<usize>,
    },
    /// Indicates that a particular row of a `Grid` was the wrong length.
    RowLength {
        /// Row of error, counting from 0.
        y: usize,
        /// The actual length of the row.
        size: usize,
        /// The length the row should have been.
        expected: usize,
    },
    /// Indicates attempt to read a `Grid` of an unacceptable size.
    GridSize {
        /// The attempted size of the grid.
        size: usize,
        /// The range of grid sizes that can be read.
        expected: Range<usize>,
    },
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Error::IO(ref err) => write!(f, "{}", err.description()),
            Error::CellParse{x, y, ref cause} =>
                write!(f, "grid parse failed at {}/{} ({})", x, y, cause.description()),
            Error::CellValue{x, y, value, ref expected} =>
                write!(f, "cell value at {}/{} was {}, but should be from {} to {}",
                       x, y, value, expected.start, expected.end - 1),
            Error::RowLength{y, size, expected} =>
                write!(f, "grid row {} has length of {}, but {} was expected", y, size, expected),
            Error::GridSize{size, ref expected} => 
                write!(f, "grid size was {}, but should be from {} to {}",
                       size, expected.start, expected.end - 1),
        }
    }
}

impl StdError for Error {
    fn description(&self) -> &str {
        match *self {
            Error::IO(ref err) => err.description(),
            Error::CellParse{..} => "failed to parse cell",
            Error::CellValue{..} => "cell contained bad value",
            Error::RowLength{..} => "grid row length wrong",
            Error::GridSize{..} => "grid had unacceptable size",
        }
    }

    fn cause<'a>(&'a self) -> Option<&'a StdError> {
        match *self {
            Error::IO(ref err) => Some(err),
            Error::CellParse{cause: ref err, ..} => Some(&**err),
            _ => None,
        }
    }
}

impl From<io::Error> for Error {
    fn from(err: io::Error) -> Error { Error::IO(err) }
}

#[cfg(test)]
mod tests {
    use std::error;
    use std::fmt;
    use std::num;

    use super::*;

    fn roundtrip(input: &str) -> Result<String, Error> {
        let mut lines = input.lines().map(|line| Ok(line.to_string()));
        let mut output = String::new();
        let reader = GridReader::new();
        let writer = GridWriter::new();
        let grid = try!(reader.read(&mut lines));
        writer.write(&mut output, &grid).unwrap();
        Ok(output)
    }

    #[test]
    fn test_classic9_roundtrip() {
        let puzzle = "5 3 _ _ 7 _ _ _ _\n\
                      6 _ _ 1 9 5 _ _ _\n\
                      _ 9 8 _ _ _ _ 6 _\n\
                      8 _ _ _ 6 _ _ _ 3\n\
                      4 _ _ 8 _ 3 _ _ 1\n\
                      7 _ _ _ 2 _ _ _ 6\n\
                      _ 6 _ _ _ _ 2 8 _\n\
                      _ _ _ 4 1 9 _ _ 5\n\
                      _ _ _ _ 8 _ _ 7 9\n";
        assert_eq!(roundtrip(puzzle).unwrap(), puzzle);
    }

    #[test]
    fn test_partial16_roundtrip() {
        let puzzle = " 1  2  3  4  5  6  7  8  9 10 11 12 13 14 15 16\n \
                       _  3  _  _  _  _  _  _  _  _  _  _  _  _  _  _\n \
                       _  _  4  _  _  _  _  _  _  _  _  _  _  _  _  _\n \
                       _  _  _  5  _  _  _  _  _  _  _  _  _  _  _  _\n \
                       _  _  _  _  6  _  _  _  _  _  _  _  _  _  _  _\n \
                       _  _  _  _  _  7  _  _  _  _  _  _  _  _  _  _\n \
                       _  _  _  _  _  _  8  _  _  _  _  _  _  _  _  _\n \
                       _  _  _  _  _  _  _  9  _  _  _  _  _  _  _  _\n \
                       _  _  _  _  _  _  _  _ 10  _  _  _  _  _  _  _\n \
                       _  _  _  _  _  _  _  _  _ 11  _  _  _  _  _  _\n \
                       _  _  _  _  _  _  _  _  _  _ 12  _  _  _  _  _\n \
                       _  _  _  _  _  _  _  _  _  _  _ 13  _  _  _  _\n \
                       _  _  _  _  _  _  _  _  _  _  _  _ 14  _  _  _\n \
                       _  _  _  _  _  _  _  _  _  _  _  _  _ 15  _  _\n \
                       _  _  _  _  _  _  _  _  _  _  _  _  _  _ 16  _\n \
                       _  _  _  _  _  _  _  _  _  _  _  _  _  _  _  1\n";
        assert_eq!(roundtrip(puzzle).unwrap(), puzzle);
    }

    #[test]
    fn test_empty_cell_normalization() {
        let puzzle   = "? _ -\n\
                        . * X\n\
                        1 2 3\n";
        let expected = "_ _ _\n\
                        _ _ _\n\
                        1 2 3\n";
        assert_eq!(roundtrip(puzzle).unwrap(), expected);
    }

    #[test]
    fn test_whitespace_normalization() {
        let puzzle   = " _  _   \n\t_\t_\t\n";
        let expected = "_ _\n_ _\n";
        assert_eq!(roundtrip(puzzle).unwrap(), expected);
    }

    #[test]
    fn test_set_size_range() {
        let mut reader = GridReader::new();
        reader.set_size_range(5);
        assert_eq!(reader.size_range, 5..6);
        reader.set_size_range(9..26);
        assert_eq!(reader.size_range, 9..26);
        reader.set_size_range(..256);
        assert_eq!(reader.size_range, 1..256);
    }

    #[test]
    fn test_handles_conflicted_puzzles() {
        let puzzle = "1 1\n1 1\n";
        assert_eq!(roundtrip(puzzle).unwrap(), puzzle);
    }

    #[test]
    fn test_cell_parse_error() {
        let puzzle = "1   2   3   4\n\
                      2   3 WTF   1\n\
                      3   4   1   2\n\
                      4   1   2   3\n";
        match roundtrip(puzzle).unwrap_err() {
            Error::CellParse{x, y, ref cause} => {
                assert_eq!((x, y), (2, 1));
                cause.downcast_ref::<num::ParseIntError>().expect("Cause wasn't parse error");
            },
            err => panic!("Wrong error: {}", err),
        }
    }

    #[test]
    fn test_cell_value_too_low() {
        let puzzle = "1 2 3 4\n\
                      2 3 4 0\n\
                      3 4 1 2\n\
                      4 1 2 3\n";
        match roundtrip(puzzle).unwrap_err() {
            Error::CellValue{x, y, value, expected} => {
                assert_eq!((x, y), (3, 1));
                assert_eq!(value, 0);
                assert_eq!(expected, 1..5);
            },
            err => panic!("Wrong error: {}", err),
        }
    }

    #[test]
    fn test_cell_value_too_high() {
        let puzzle = "1 2 3 4\n\
                      2 3 4 1\n\
                      3 5 1 2\n\
                      4 1 2 3\n";
        match roundtrip(puzzle).unwrap_err() {
            Error::CellValue{x, y, value, expected} => {
                assert_eq!((x, y), (1, 2));
                assert_eq!(value, 5);
                assert_eq!(expected, 1..5);
            },
            err => panic!("Wrong error: {}", err),
        }
    }

    #[test]
    fn test_too_few_rows() {
        let puzzle = "1 2 3 4\n\
                      2 3 4 1\n\
                      3 4 1 2\n";
        let mut lines = puzzle.lines().map(|line| Ok(line.to_string()));
        let mut reader = GridReader::new();
        reader.set_size_range(4);
        match reader.read(&mut lines) {
            Err(Error::GridSize{size, expected}) => {
                assert_eq!(size, 3);
                assert_eq!(expected, 4..5);
            },
            _ => panic!("Wrong result"),
        }
    }

    #[test]
    fn test_too_many_rows() {
        let puzzle = "1 2 3 4\n\
                      2 3 4 1\n\
                      3 4 1 2\n\
                      4 1 2 3\n\
                      1 2 3 4\n";
        let mut lines = puzzle.lines().map(|line| Ok(line.to_string()));
        let mut reader = GridReader::new();
        reader.set_size_range(4);
        match reader.read(&mut lines) {
            Err(Error::GridSize{size, expected}) => {
                assert_eq!(size, 5);
                assert_eq!(expected, 4..5);
            },
            _ => panic!("Wrong result"),
        }
    }

    #[test]
    fn test_row_too_short() {
        let puzzle = "1 2 3 4\n\
                      2 3 4 1\n\
                      3 4   2\n\
                      4 1 2 3\n";
        let mut lines = puzzle.lines().map(|line| Ok(line.to_string()));
        let mut reader = GridReader::new();
        reader.set_size_range(4);
        match reader.read(&mut lines) {
            Err(Error::RowLength{y, size, expected}) => {
                assert_eq!(y, 2);
                assert_eq!(size, 3);
                assert_eq!(expected, 4);
            },
            _ => panic!("Wrong result"),
        }
    }

    #[test]
    fn test_row_too_long() {
        let puzzle = "1 2 3 4\n\
                      2 3 4 1 2\n\
                      3 4 1 2\n\
                      4 1 2 3\n";
        let mut lines = puzzle.lines().map(|line| Ok(line.to_string()));
        let mut reader = GridReader::new();
        reader.set_size_range(4);
        match reader.read(&mut lines) {
            Err(Error::RowLength{y, size, expected}) => {
                assert_eq!(y, 1);
                assert_eq!(size, 5);
                assert_eq!(expected, 4);
            },
            _ => panic!("Wrong result"),
        }
    }

    #[test]
    fn test_grid_size_vs_cell_parse_errors() {
        let puzzle = "1 2 3 4\n\
                      2 3 4 1\n\
                      3 4 1 2\n\
                      4 1 2 3\n\
                      WTF\n";
        let mut lines = puzzle.lines().map(|line| Ok(line.to_string()));
        let mut reader = GridReader::new();
        reader.set_size_range(4);
        match reader.read(&mut lines) {
            Err(Error::GridSize{size, expected}) => {
                assert_eq!(size, 5);
                assert_eq!(expected, 4..5);
            },
            Err(err) => panic!("Wrong error: {:?}", err),
            _ => panic!("Failed to error out"),
        }
    }

    #[test]
    fn test_row_length_vs_cell_parse_errors() {
        let puzzle = "1 2 3 4\n\
                      2 3 4 1 WTF\n\
                      3 4 1 2\n\
                      4 1 2 3\n";
        let mut lines = puzzle.lines().map(|line| Ok(line.to_string()));
        let mut reader = GridReader::new();
        reader.set_size_range(4);
        match reader.read(&mut lines) {
            Err(Error::RowLength{y, size, expected}) => {
                assert_eq!(y, 1);
                assert_eq!(size, 5);
                assert_eq!(expected, 4);
            },
            Err(err) => panic!("Wrong error: {:?}", err),
            _ => panic!("Failed to error out"),
        }
    }

    #[test]
    fn test_custom_parsing_and_formatting() {
        let puzzle = "A    B    C    D   \n\
                      B    None None A   \n\
                      None D    A    None\n\
                      D    A    B    C   \n";

        fn parse_cell(token: &str) -> Result<Option<usize>, Box<error::Error>> {
            Ok(Some(match token {
                "A" => 1, "B" => 2, "C" => 3, "D" => 4,
                "None" => return Ok(None),
                _ => return Err(Box::new("".parse::<usize>().unwrap_err())),
            }))
        }

        fn write_cell(w: &mut fmt::Write, _width: usize, cell: Option<usize>) -> fmt::Result {
            let descriptions = ["None", "A", "B", "C", "D"];
            let i = match cell {
                Some(x) => x,
                None    => 0,
            };
            write!(w, "{:<4}", descriptions[i])
        }

        let mut lines = puzzle.lines().map(|line| Ok(line.to_string()));
        let mut output = String::new();
        let mut reader = GridReader::new();
        let mut writer = GridWriter::new();
        reader.set_cell_parser(Box::new(parse_cell));
        writer.set_cell_writer(Box::new(write_cell) as Box<CellWriterFn>);
        let grid = reader.read(&mut lines).unwrap();
        writer.write(&mut output, &grid).unwrap();
        assert_eq!(output, puzzle);
    }

}
