# A Solver-based implementation of `Incon`

A simple solver-based inconsistency checker for constraint language described in the paper.

# Setup

Assuming you have `opam` installed, the `build` script create a new opam switch, install necessary dependencies, and build the project.

```shell
./build
```

# File Structure in `src`

* `constraint.ml` defines the constraint language along with three operations on constraints, `dual`, `truify`, and `falsify`. They are all described in the main paper.

* `solver.ml` offers a dozen of helper function and an interface for satisfiability checking in `Z3`.

* `incon.ml` describes a decision procedure to check inconsistency of
constraints, equivalent to `incon` judgment in the paper.  Function
`trans` turns a constraint (that encodes exhaustiveness checking or
redundancy checking) into a logical formula.  As a result, checking satisfiability of the formula is equivalent to checking the consistency of the constrain.

# Try it yourself!

Launch ocaml top-level.
```bash
dune utop src
```

Within the top-level, bring the functions into scope with `open Incon;;`, and you may check exhaustiveness and redundancy as follows.

```ocaml
is_exhaustive (disjunct [ Inl Truth; Inr Unknown ]);;
```

```ocaml
is_redundant (disjunct [ Num 2; Unknown ]) (disjunct [ Num 2; Num 3 ]);;
```
