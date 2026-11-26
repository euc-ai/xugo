# relations/closure — the transitive and reflexive–transitive closures

`transitive_closure(R)` is the least transitive relation containing
`R`: two rules say so, and everything here is read off them.

    R(x, y)                                        ⇒ transitive_closure(R, x, y)
    transitive_closure(R, x, y) ∧ transitive_closure(R, y, z)
                                                   ⇒ transitive_closure(R, x, z)

A definition by rules comes with its theorems: the rules themselves,
rule induction along the closure, that induction strengthened so a step
knows the two halves it composes are themselves steps, and the case
analysis. The chapter spends the first three. The case analysis it
publishes without using — the two members below that take a closure
step apart say something sharper than it does — because a consumer
outside the chapter may still want the plain one. The closure form
the constant is minted with is not a proof surface: `Unfold` refuses
it, so **no member unfolds `transitive_closure`**.

## Taking it apart

Two members say what a step of the closure IS, and they are a mirror
pair: every such step has a first move and a last one, and either can
be peeled off.

- **CasesLeft** — split at the LAST move: a step of the closure is a
  single step of `R`, or a step of the closure followed by a single
  step of `R`.
- **CasesRight** — split at the FIRST move: a single step of `R`, or a
  single step of `R` into a point that reaches the far end in the
  closure. The reflection of the one above, proved the same way.

Both run the strengthened induction on the statement's own right-hand
side, and each needs the strengthening on the stretch the other does
not: `CasesLeft` prefixes a stretch and keeps the last move, so it is
handed the first stretch as a closure fact; `CasesRight` appends one
and keeps the first move, so it is handed the second.

## Inducting a step at a time

The induction the definition comes with composes two ARBITRARY
stretches. An argument that walks a path wants to extend by one move,
and these two are that principle, one for each end — a second mirror
pair, each proved by strengthening the property to a CARRIER that moves
one of `P`'s arguments along a stretch, and each finished by the
cases law that peels off the end it does not travel.

- **InductLeft** — the step extends on the RIGHT; the carrier moves
  `P`'s second argument forward, and `CasesRight` peels the first move.
- **InductRight** — the step extends on the LEFT; the carrier moves
  `P`'s first argument back, and `CasesLeft` peels the last move.

## The operator's own laws

- **Monotone** — a relation contained in another has its closure
  contained in the other's closure. Rule induction along the smaller
  relation's closure, whose two obligations are the larger relation's
  own rules.
- **Closed** — the one fixed point of the construction:
  `transitive_closure(R) = R` exactly when `R` is transitive. Read as
  an equation between relations, spent pointwise; the induction runs at
  `R` itself, so one of its two obligations is a tautology, closed as it
  stands, and the other is transitivity.
- **Idempotent** — closing twice closes once. `Closed` read at the
  closure itself, which then asks only that the closure be transitive,
  and that is its second rule.

## The reflexive–transitive closure

`reflexive_transitive_closure(R, x, y)` adds equality to the transitive
closure: x reaches y in zero or more steps of `R`
(`ReflexiveTransitiveClosureDef`). It is transitive
(`ReflexiveTransitiveClosureTransitive`) and grows with the relation
(`ReflexiveTransitiveClosureMonotone`), and a property that every step
of `R` carries forward holds at the end of a walk when it holds at the
start (`ReflexiveTransitiveClosurePreserves`).

Restrict a relation symmetric on a carrier (`symmetric_on`) to that
carrier and take its reflexive–transitive closure: the result is an
equivalence on the carrier (`ReflexiveTransitiveClosureEquivalenceOn`). Rule
induction reverses a walk by reversing its steps and composing them in
reverse order.

The framework mechanics (typed cites, recorded deps, the shared family CNF blob,
replay) are the standard ones — see
`library/chapter_constitution.md` and `library/registry/`.
