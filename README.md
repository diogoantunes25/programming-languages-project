# Programming Languages - Project

## Group

 - Carlos Vaz, 99188, carlosvaz@tecnico.ulisboa.pt
 - Diogo Melita, 99202, diogo.melita@tecnico.ulisboa.pt
 - Diogo Antunes, 99210, diogo.santiago@tecnico.ulisboa.pt

## Implemented Features

All mandatory tasks implemented. 

Features implemented include:

- `com` extended with `!!` (non-deterministic choice) and `->` (conditional guard) operators
- appropriate updates to step-indexed evaluator
- implemented `ceval` relation to support version of Imp language
- parser extended as appropriate to support new constructs

Proofs completed include:

- `p1_equals_p2`
- `ceval_step_more`
- all `ceval_example_*` proofs
- Idempotence
- Commutativity
- Associativity
- Distributivity (left)
- Congruence

Moreover, examples `p1` and `p2` were added to the `Imp.v` file and 3 new `.lpro` programs were added to the `examples` folder, `ex3.lpro`, `ex4.lpro` and `ex5.lpro`.

## Extras

The step-indexed evaluator was restructured into continuation passing style (CPS),
aligning the language's behavior with typical expectations of an imperative language.
This modification effectively resolved numerous peculiarities present in the original implementation.
It its implemented in the `CPS` module in `Interpreter.v`. This module includes:

- **Continuation Passing Style Implementation:** Instead of using functions to represent continuations, our implementation employs lists of commands. This method not only simplifies the proofs but also highlights scenarios where traditional function-based implementations may fail to hold true for more general lemmas.
  
- **Adjusted Examples:** We've modified our examples to better represent differences in gas expenditures.

- **Proofs:** Two adjusted versions of the existing theorems are proven. Furthermore, we two additional general lemmas are also proven.

> Note: In the `ceval_invariant` proof, we used an `admit` to facilitate the use of strong induction — a technique not directly supported by Coq without manual derivation.
