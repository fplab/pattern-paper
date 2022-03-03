# A Solver-based implementation `Incon`

# Dependencies

This implementation is very lightweight and only use one package `Z3` from `opam`. Any recent opam version should work. At the time of development, we use opam version 4.12.0.

Assume you have `opam` installed on your machine, simply run `make` would install `Z3` and build the project.

# File Structure

* `constraint.ml` defines the constraint language along with three operations on constraints, `dual`, `truify`, and `falsify`. They are all described in the main paper.

* `solver.ml` offers a dozen of helper function and an interface for satisfiability checking.

* `incon.ml` gives an equivalent decision procedure to check inconsistency of constraint, dubbed "incon" judgment in the paper. 
Function `incon` is the entry point to the decision procedure. It first transforms the constraint into a logical formula (via function `trans`) and return the negation of the result checking the satisfiability of the formula.
