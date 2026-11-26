# sensitivity — the degree bound by squared sensitivity

`SensitivityTheorem` states $\deg(f)\le s(f)^2$ on any finite coordinate
set $U$. Degree and sensitivity both use the input $X\subseteq U$ to mean
that exactly the coordinates in $X$ have value one.

For positive degree $k$, `boolean_degree.MajorityFace` supplies $S\subseteq U$
of size $k$. On the face $X\subseteq S$, one parity class $H$ occupies
strictly more than half the inputs. Every edge of $H$ changes $f$.
`hypercube.Huang` gives a vertex $X\in H$ of degree $d$ with $k\le d^2$.
Each of its neighbours comes from a sensitive coordinate in $U$, so
`DegreeLeLocalSensitivity` gives $d\le s(f,X)\le s(f)$. Degree zero
satisfies the inequality directly.
