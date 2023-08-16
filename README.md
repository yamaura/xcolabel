# xcolabel

Convert between column label to 0-based number.

**xcolabel** converts between 0-based numbers and column labels of spreadsheet software.
For example, "A" becomes 0. "AA" becomes 26.
It also converts tuples of the form (row, column) into strings like "C2".

# Status
**xcolabel** is a pure Rust library.
Everything except TryFromCellStr has been implemented.

# Examples
```
use xcolabel::ToCellString;

assert_eq!((4, 2).to_cell_string(), "C5"); // value is 0-based (row, column)
```

