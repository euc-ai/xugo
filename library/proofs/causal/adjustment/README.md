# adjustment — the back-door and front-door adjustment formulas

A set Z satisfying the back-door criterion for (X, Y) identifies the
effect of X on Y by adjusting for Z: P_x(E) = Σ_z P(E | x, z) P(z) for
any event E of the outcome's coordinates, from Rule 3 for P_x(z) =
P(z), Rule 2 for P(E | x, z) and the law of total probability. A
mediator set Z satisfying the front-door criterion identifies it
through Z even with a hidden common cause of X and Y: P_x(E) = Σ_z
P(z | x) Σ_{x'} P(E | z, x') P(x'), where the inner sum is the
back-door adjustment for the effect of Z on Y. The sums run over the
configurations of the summed nodes, whose state carriers are finite;
the other nodes are unrestricted, and the outcome may be continuous.
The support conditions are stated with each formula: a conditional
probability the observations do not reach is not identified by a
convention on zero denominators. For continuous treatments and
adjustment sets the formula is `causal/kernel_do_calculus`'s.

A concrete graph meeting the front-door criterion, with its
identification, is an example of `causal/identifiability`.

| Member | Statement |
|---|---|
| `BackdoorAdjustment` | under the back-door criterion, P_x(E) = Σ_z P(E \| x, z) P(z) wherever P(z) > 0 gives P(x, z) > 0 — card |
| `FrontdoorAdjustment` | under the front-door criterion, P_x(E) = Σ_z P(z \| x) Σ_{x'} P(E \| z, x') P(x') under its support conditions — card |

The framework mechanics are the standard ones — see
`library/chapter_constitution.md`.
