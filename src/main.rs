extern crate rusudoku;

use std::io;
use std::io::BufRead;
use std::mem;

fn main() {
    let mut lines = io::BufReader::new(io::stdin()).lines();
    let grid = rusudoku::grid::Grid::read(&mut lines);
    let mut grid = match grid {
        Ok(grid) => grid,
        Err(err) => {
            println!("Couldn't read puzzle: {}", err);
            return;
        },
    };

    let rules = rusudoku::rules::Rules::new_standard(grid.size());
    let rules = match rules {
        Some(rules) => rules,
        None => {
            println!("Couldn't create rules for sudoku problem {} cells wide.", grid.size());
            return;
        },
    };

    let mut partitioner = rusudoku::solver::Partitioner::new(&rules);
    let mut vetoes: Vec<_> = grid.vetoes().collect();
    while vetoes.len() > 0 {
        partitioner.veto(vetoes.iter().cloned());
        grid.veto(vetoes.iter().cloned());
        vetoes = mem::replace(&mut partitioner.inferences, vec![]);
    }

    print!("{}", grid);
}
