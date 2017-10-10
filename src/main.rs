extern crate rusudoku;

use std::io;
use std::io::BufRead;

// I'm under the impression user-errors shouldn't be handled via panics, and main() was
// getting a bit cluttered from error-handling... Hopefully this'll help with readability.
// This is like .expect(), except it takes format strings and exits the process instead of
// panicking.
macro_rules! expect {
    ($result:expr, $err:ident => $($err_msg:expr),+) => {
        match $result {
            Ok(value) => value,
            Err($err) => {
                use std::io::{stderr, Write};
                use std::process;
                let _ = writeln!(&mut stderr(), $($err_msg),*);
                process::exit(1);
            }
        }
    }
}

fn main() {
    let mut lines = io::BufReader::new(io::stdin()).lines();

    let grid = rusudoku::grid::Grid::read(&mut lines);
    let grid = expect!(grid, err => "Couldn't read puzzle: {}", err);

    let rules = rusudoku::rules::Rules::new_standard(grid.size());
    let rules = expect!(rules, err => "Couldn't create rules for sudoku problem {} cells wide.",
                                      err.size());

    match rusudoku::solver::solve(grid, rules) {
        rusudoku::solver::Solution::Unique(grid)    => print!("Unique:\n{}", grid),
        rusudoku::solver::Solution::NonUnique(grid) => print!("Non-unique:\n{}", grid),
        rusudoku::solver::Solution::Unsolvable      => print!("Unsolvable:\n"),
    }
}
