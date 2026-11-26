# option — optional values

An optional value is either absent (`none`) or present (`some a`). The
chapter mints the type through the datatype door, which carves
`option(A)` out of the recursive-type universe `recspace(A)` and
derives the four principles a datatype comes with:

- **Induction** — a property that holds at `none` and at every
  `some a` holds of every optional value. There is no recursive
  constructor, so this is a case analysis dressed as an induction. The
  `induction` tactic dispatches on it under the library name
  `option_induction`.
- **Recursion** — a function on optional values is determined by its
  value at `none` and its values at the `some a`. The define door's
  equation compiler instantiates it under `option_recursion`.
- **SomeInjective** and **NoneNotSome** — `some a = some b` exactly
  when `a = b`, and `none` is not a `some`.

Between them, the four are the whole of what the datatype door promises
about the type. The chapter adds one consequence, **Cases** — every
optional value is `none` or some `some a` — the plain case analysis a
deduction reads when it decomposes an unknown optional value, as
`list.Cases` and `peano.Cases` are for lists and numbers. No operation
on optional values is defined here. The universe's own theory is the
sibling chapter `datatype_universe`, which the door's derivations read.

The framework mechanics (typed cites, recorded deps, the shared family CNF blob,
replay) are the standard ones — see
`library/chapter_constitution.md` and `library/registry/`.
