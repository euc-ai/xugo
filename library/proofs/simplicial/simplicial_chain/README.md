# simplicial_chain — the alternating face map complex of a simplicial set, its boundary squaring to zero, and the chain map a simplicial map induces

The n-chains of a simplicial set `X` over a commutative ring
`R`, its carrier `c = R.carrier`, are the free module on the
n-simplices `X.simplices(n)`, `simplicial_chains(c, n)`
(`finite_supp`, the functions of finite support valued in `c`). The
boundary of the generator at an n-simplex `x` is the alternating sum
of the generators at its faces, `face_sum(n, x) = Σ_{i ≤ n} (−1)^i
δ(X.d(n, i, x))`, and `simplicial_boundary(n)` is that map of the
generators extended linearly (`free_lift`). The sign `(−1)^i` is
comm_ring's `alternating_sign(i)`, one at 0 and negated at each step, so that the
step `alternating_sign(j) = −alternating_sign(j − 1)` is the
definition's own clause.

Two boundaries in a row are zero. On a generator the composite is the
double sum $\sum_j \sum_i (-1)^{i+j} \delta(d_i d_j x)$ over `i ≤ n + 1`,
`j ≤ n + 2`; the pairs `(j, i)` with `j ≤ i` are carried onto those
with `i < j` by `(j, i) ↦ (i + 1, j)`, with no subtraction, the face
identity $d_i d_j = d_{j-1} d_i$ makes the two simplices one, and the
signs are opposite, so the two halves cancel. The sum laws this uses — a sum over a
disjoint union, over the image of an injection, over a product of
index sets, and the negative of a sum — are the module chapter's. The
boundary is a homomorphism of the free modules, so the chains form a
chain complex of the homological algebra chapters, `chain_complex`,
and its homology is `simplicial_homology`. A simplicial map sends
generators to generators and induces a chain map.

## The boundary and the complex

| member | statement |
|---|---|
| `FaceSumDef` | `face_sum(n, x) = Σ_{i ≤ n} alternating_sign(i) • delta_at(d(n, i, x))` |
| `SimplicialChainsDef`, `SimplicialBoundaryDef` | `simplicial_chains(zero, X, c, n) = finite_supp(zero, c, X.simplices(n))`; `simplicial_boundary(n) = free_lift(λx. face_sum(n, x))` |
| `ChainsModule` | the n-chains of any record `X`, simplicial or not, are a module over the ring at every dimension, `module_on(R, mk_module(fun_add, fun_zero, fun_neg, fun_smul, simplicial_chains(R.carrier, n)))`: by definition the free module on `X.simplices(n)`, `FreeModuleOn` at `R` with the record's parts read off |
| `FaceSumIn` | the face sum of an (n+1)-simplex is an n-chain: each term scales the generator at a face, an n-simplex, by a sign in `c`, and the free module on `X.simplices(n)` holds the finite sum |
| `BoundaryHom` | the boundary is a homomorphism of the free modules: the face sum, which carries `X.simplices(n + 1)` into the n-chains, extended linearly from the generators |
| `BoundaryDelta` | on a generator the boundary is the face sum: the face sum carries `X.simplices(n + 1)` into the n-chains, a module, so its linear extension takes the face sum's value at each generator |
| `FaceSumCancel` | $\sum_{j \le n+2} \sum_{i \le n+1} (-1)^{i+j} \delta(d_i d_j x) = 0$: the pairs with `j ≤ i` go one-to-one onto those with `i < j` by `(j, i) ↦ (i + 1, j)`, where the face identity makes the simplices one and the signs opposite |
| `BoundaryFaceSum` | `∂(face_sum(x)) = 0` for an (n+2)-simplex `x`: the boundary is linear, so it passes through the signed sum of the generators at the faces and through each sign, and on each generator gives that face's own face sum; the outer sign carried inside leaves the double sum of `FaceSumCancel` |
| `BoundaryTwice` | `∂ ∘ ∂ = 0` on every chain: the composite boundary and the zero map are homomorphisms that agree on generators (`BoundaryDelta`, `BoundaryFaceSum`), hence on all chains (`FreeLiftUnique`) |
| `ChainComplex` | the alternating face map complex is a chain complex: each term, the free module on the simplices of its dimension, is a module (`ChainsModule`); each boundary is a homomorphism one dimension down (`BoundaryHom`); and two boundaries in a row vanish (`BoundaryTwice`) |

## The chain map of a simplicial map, and homology

| member | statement |
|---|---|
| `SimplicialChainMapDef` | `simplicial_chain_map(F, n) = free_lift(λx. delta_at(F(n, x)))` |
| `ChainMapOfSimplicialMap` | a simplicial map induces a chain map of the two complexes: each induced map extends the generators' images linearly, so it is a homomorphism (`FreeLiftHom`); the two ways round the square are homomorphisms out of the free module on `X.simplices(n + 1)` that agree on its generators — both give `Σ_i (−1)^i δ(Y.d(n + 1, i, F(n + 1, x)))` by `BoundaryDelta`, `FreeLiftDelta` and `MapFace` — so they agree on every chain (`FreeLiftUnique`) |
| `SimplicialHomologyDef` | `simplicial_homology(c, n)` is degree-n homology of the complex record containing the pointwise operations, `simplicial_chains(c)` and `simplicial_boundary` |

The conventions every proof here follows are `library/proofs/README.md`;
the rules are `library/chapter_constitution.md`.

The chain complex is packaged as a `complex_ops` record containing
pointwise operations, degree carriers and the boundary. `BoundaryHom`
and `ChainMapOfSimplicialMap` use self-contained homomorphisms, so their
claims include the source and target free-module laws.
