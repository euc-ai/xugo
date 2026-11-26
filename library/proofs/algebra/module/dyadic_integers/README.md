# dyadic_integers — the dyadic integers ℤ₂: compatible residues modulo powers of two, their topology, the embedding of ℤ, the 2-adic series map, and the derived limit of the tower of doubling

The worked example of [derived_limit](../derived_limit/README.md): lim¹ of the tower of the integers under doubling is ℤ₂/ℤ, and so has at least continuum many elements.

The 2-adic integers are built from residues alone. A point of `dyadic_integer_group` is a sequence whose k-th term is a residue modulo 2^k, each term reducing modulo 2^k to the one before, and the group adds residuewise. Its topology is the one the product of the discrete coordinates induces, and the compatible sequences are compact in it. An integer enters through its residues modulo each power of two: the integers are dense and not closed, and their discrete parametrization makes them a Polish cover of the group (`DyadicIntegerPolishCover`).

A sequence of integers a has the 2-adic series ∑ 2^i a_i, read at stage k as the residue of its first k terms modulo 2^k, so each stage reads finitely many coordinates. For the tower of the integers under doubling, id − shift sends a to the sequence $a_k - 2a_{k+1}$, whose series is the integer a_0, and binary digits make the series map onto. So the series map identifies the Polish cover of lim¹, the sequence group over the image of id − shift, with ℤ₂ over ℤ, and since ℤ is not closed in ℤ₂, borel_subgroup's dichotomy gives the continuum (`DyadicDerivedLimit`).

Both theorem members are cards. To read their exact statements and dependencies, run `xugo query family algebra/module/dyadic_integers`.

## Members

| Member | Status | Statement and purpose |
|---|---|---|
| `DyadicIntegerGroupDef` | definition | Compatible residues modulo 2^k, with residuewise addition: an independent model of the additive 2-adic integers. |
| `DyadicIntegerTopologyDef` | definition | The closed inverse-limit topology of the residue groups. |
| `dyadicIntegerEmbeddingDef` | definition | An integer read modulo each power of two. |
| `dyadicSeriesDef` | definition | The compatible residues of the convergent 2-adic series sum 2^i a_i; each output uses only finitely many coordinates. |
| `DyadicIntegerPolishCover` | card | The compatible residues are a closed subgroup of the product of finite cyclic groups. — card |
| `DyadicDerivedLimit` | card | The series map is continuous and onto by binary digits. — card |
