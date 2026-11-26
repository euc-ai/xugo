# do_semantics — the meaning of causal expressions and the soundness of derivation

An expression is read in a model at an environment, a configuration of
the observed nodes, by structural recursion (`EvalDef`): the atom
`do_prob(Y, X, W)` is the conditional probability, under the model
intervened at X with the environment's values, that the Y-coordinates
take the environment's values given that the W-coordinates do; a sum
overrides the environment on its group with each configuration of the
group's finite carriers and adds; products and quotients are pointwise,
with the total real division. The environment ranges over observed
configurations, not over configurations of all nodes: two
observationally equivalent models may have different latent spaces and
still share it.

In the positive class every well-formed expression is positive, so the
total division never meets a zero denominator; derivable expressions
agree in every model of the class at every environment; and a query
derived to an observational expression is identifiable. That last
theorem states the query of `causal/identifiability`'s back-door and
front-door theorems, P_x(V_Y = v_Y) with v legal on X, so a derivation
in the syntax and an adjustment formula in the semantics reach the same
statement; `BackdoorDerivable` with `DerivationIdentifies` is a second
route to `BackdoorIdentifiable`, which cannot cite it, this chapter
standing above that one.

| Member | Statement |
|---|---|
| `EvalDef` | `do_expr_eval(M, v, e)`, by recursion on e |
| `EvalCoincidence` | the value depends on the environment only at the free nodes — card |
| `EvalPositive` | in the positive class a well-formed expression is positive at every observed configuration — card |
| `ObservationalEvalAgrees` | an observational expression has the same value in two models with the same observed masses — card |
| `DoDerivationSound` | derivable expressions have the same value in every model of the positive class — card |
| `DerivationIdentifies` | an interventional probability derived to an observational expression is identifiable on the positive class — card |

The framework mechanics are the standard ones — see
`library/chapter_constitution.md`.
