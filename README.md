# rusudoku

This is a sudoku solver written to learn Rust. It consists of a crate (called `rusudoku`) and an
executable. The executable reads a single puzzle from stdin and prints its solution to stdout.
Puzzles formatted like so:

```
5 3 _ _ 7 _ _ _ _
6 _ _ 1 9 5 _ _ _
_ 9 8 _ _ _ _ 6 _
8 _ _ _ 6 _ _ _ 3
4 _ _ 8 _ 3 _ _ 1
7 _ _ _ 2 _ _ _ 6
_ 6 _ _ _ _ 2 8 _
_ _ _ 4 1 9 _ _ 5
_ _ _ _ 8 _ _ 7 9
```

`rusudoku` doesn't yet fall back on guessing, so there are puzzles it can't solve. This should
hopefully be fixed soon.
