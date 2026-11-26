# hypercube — the finite cube graph and its induced degrees

For any finite coordinate set $S$, the vertices of its cube are the subsets
of $S$. Two vertices are adjacent when one is obtained from the other by
toggling a member of $S$. On a vertex family $H$, `graph_degree(H,
cube_adjacent(S), X)` counts exactly the neighbours of $X$ retained in $H$.

`Huang` gives a vertex of induced degree $d$ with $d^2\ge \lvert S\rvert$ whenever
$2\lvert H\rvert>2^{\lvert S\rvert}$. `HuangDegreeSquare` states the bound with the usual
threshold $\lvert H\rvert>2^{n-1}$ for $n=\lvert S\rvert$, a threshold no family meets in
dimension zero; the strict-majority form also covers the singleton cube there.
[Hao Huang, *Induced subgraphs of hypercubes and a proof of the Sensitivity Conjecture*](https://annals.math.princeton.edu/2019/190-3/p06).

`SignedCube` constructs an edge signing $M$ with $M^2=\lvert S\rvert I$. For
$K=\mathcal{P}(S)\setminus H$, the rectangular block with rows in $K$
and columns in $H$ has more columns than rows. `module_dimension.MajorityKernelVector`
therefore supplies a vector $v$ that is nonzero at some vertex of $H$.
Both $v$ and $Mv$ vanish on $K$, the support hypotheses of `SupportedDegreeBound`.
If $d$ is the maximum degree in $H$, each row sum on these vectors is
bounded by $d$ times the largest input coordinate in absolute value.
Applying that bound twice gives $\lvert S\rvert\max \lvert v\rvert\le d^2\max \lvert v\rvert$.
