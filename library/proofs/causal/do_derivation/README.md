# do_derivation — causal expressions and the derivation relation of the do-calculus

A causal expression is a term over node sets (`DoExprData`): the atom
`do_prob(Y, X, W)`, read P(v_Y | do(v_X), v_W), the sum `do_sum(Z, e)`
over the values of Z, and products and quotients. Arguments are node
sets, never values: the environment of an expression assigns each
observed node one value, the atom reads its groups' values from it, and
a sum binds the values of its group by overriding the environment
there, so shadowing needs no renaming. The joint probability is
`do_prob(Y, ∅, ∅)` and the constant 1 is `do_prob(∅, ∅, ∅)`.

The derivation relation `do_derivable(E, O, e₁, e₂)` is the least
relation the rules generate, and it connects only well-formed
expressions: equivalence and congruence; the three causal rules, each
under its separation condition in a graph with edges deleted; the
probability rules of conditioning, marginalisation and the empty event;
and the algebraic rules of products, quotients and sums. Every
disjointness the rules need is written in them: well-formedness does
not give it. The table is accepted by its consumers and claims no
completeness. The back-door and front-door adjustments derive in it
when the treatment, outcome and third node set are pairwise disjoint
subsets of the observed nodes. Both open with the law of total
probability under the intervention, which conditions the effect on the
third set and sums over it (`TotalProbabilityDerivable`); the back-door
criterion then removes the intervention from each factor, and the
front-door derivation applies the back-door one to its inner factor.

The language carries the product, quotient and sum calculus of one
interventional query P(y | do(x), w), and no more. It has no sum or
difference of expressions: a contrast of two queries, such as an
average effect P(y | do(x₁)) − P(y | do(x₀)), is two expressions read at
two environments. Each node has one value in scope at a time, so the
front-door formula's inner sum over X cannot be moved out past the
factor P(z | x) that reads the outer x: Σ_{x'} P(x') Σ_z P(z | x) P(y | z,
x') needs both values of X at once and is not an expression here.

This chapter reads only the graph chapters. The meaning of expressions
in a model and the soundness of derivation are
`causal/do_semantics`.

| Member | Statement |
|---|---|
| `DoExprData` | the datatype `do_expr(I)`: `do_prob(Y, X, W)`, `do_sum(Z, e)`, `do_mul(a, b)`, `do_div(a, b)` |
| `FreeDef` | `do_expr_free(e)`: an atom's groups; a sum's body without its group; the union of both sides |
| `WellFormedDef` | `do_expr_wf(O, e)`: each atom's groups pairwise disjoint and observed, each summed group observed |
| `ObservationalDef` | `do_expr_observational(e)`: no atom intervenes |
| `DoDerivableRules` | the derivation relation `do_derivable(E, O, e₁, e₂)` and its twenty rules |
| `UnitWellFormed` | the unit `do_prob(∅, ∅, ∅)` is well formed over any observed nodes |
| `DerivableWellFormed` | a derivation connects well-formed expressions |
| `TotalProbabilityDerivable` | the law of total probability under intervention: P(Y \| do(X)) derives to Σ_Z P(Y \| do(X), Z) P(Z \| do(X)) |
| `BackdoorDerivable` | under the back-door criterion `do_prob(Y, X, ∅)` derives to Σ_Z P(Y \| X, Z) P(Z) |
| `FrontdoorDerivable` | under the front-door criterion `do_prob(Y, X, ∅)` derives to Σ_Z P(Z \| X) Σ_X P(Y \| Z, X) P(X) |

The framework mechanics are the standard ones — see
`library/chapter_constitution.md`.
