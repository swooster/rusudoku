extern crate rusudoku;

use std::io;
use std::io::BufRead;

fn main() {
    let mut lines = io::BufReader::new(io::stdin()).lines();
    let grid = rusudoku::grid::Grid::read(&mut lines);
    let grid = match grid {
        Ok(grid) => grid,
        Err(err) => {
            println!("Couldn't read puzzle: {}", err);
            return;
        },
    };
    print!("{}", grid);
}
