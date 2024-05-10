# Programming Languages - Project

## Group

 - Carlos Vaz, 99188, carlosvaz@tecnico.ulisboa.pt
 - Diogo Melita, 99202, diogo.melita@tecnico.ulisboa.pt
 - Diogo Antunes, 99210, diogo.santiago@tecnico.ulisboa.pt

## Implemented Features

All mandatory tasks implemented. 

Features implemented include:

- `com` extended with `!!` (non-deterministic choice) and `->` (conditional guard) operators.
- appropriate updates to step-indexed evaluator.
- implemented `ceval` relation to support version of Imp language
- Parser extended as appropriate to support new constructs.

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

We extended our work with more features. We implemented the following features:

- The step-indexed evaluator was restructured into continuation passing style (CPS),
aligning the language's behavior with typical expectations of an imperative language.
This modification effectively resolved numerous peculiarities present in the original implementation.

// TODO: mention that gas is different

- The step-indexed evaluator was modified to return the appropriate error messages and the number of "steps" taken when successful.
