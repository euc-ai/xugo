# linear_independence — independent sets and bases of a module on a set, and the replacement theorem over a field

A subset `S` of a module on a set over a ring on a set is independent
when only the zero combination of its members vanishes:
`module_independent(R, M, S)` says `S ⊆ M.carrier` and, for every
finite part `T` of `S` and coefficients `a(x)` in `R.carrier`,
`Σ_{x∈T} a(x) • x = M.zero` forces every `a(x)` on `T` to be `R.zero`.
A basis is an independent set whose span is the carrier,
`module_basis(R, M, S)`. The set indexes its own combinations: there is
no index type and no family of vectors between a set and its
independence, so a basis is a set of vectors like any other, and two
bases of one module are two subsets of one type.

The span of a set — the submodule chapter's least submodule holding it,
whose order laws (`SpanMono`, `SpanOfSubmodule`) are that chapter's and
need no module law — is, over any ring, the set of its finite
combinations (`SpanCombinations`). Over a field — the scalars
`ring_subfield(R, inv, R.carrier)`, the module's own ring a field on its
carrier with an inverse beside it — a member with a nonzero coefficient
in a combination that lies in a submodule, beside members that lie in it,
lies in it too (`SolveForMember`), and the chapter's second half rests
on that move, dividing by a nonzero scalar: a vector joins
an independent set exactly when it lies outside its span
(`IndependentInsertIff`, whose ⇒ holds over any ring with one ≠ zero,
`IndependentInsertOutsideSpan`), the exchange lemma, an independent set
inside a spanning set extends to a basis inside it by Zorn's lemma
(`BasisBetween`), so every independent set lies in a basis
(`BasisExtends`) and every spanning set holds one
(`BasisWithinSpanning`), and the replacement theorem: an independent set inside the span of a
finite set is finite and no larger (`Steinitz`). The dimension chapter
(`module_dimension`) reads its consequences.

The ring `R` and the module `M` are each one value of its record
(module_record). A law that needs the module's axioms is read under
`module_on(R, M)`; one that needs none — the two readings of
independence, `IndependentSubset`, `IndependentRestrict`,
`IndependentEmpty`, `IndependentChainUnion` — binds the two records
alone; and the laws under a homomorphism are read under
`module_homomorphism(R, M, N, f)`, which carries both modules.

## The definitions

| member | statement |
|---|---|
| `ModuleIndependentDef` | `module_independent(R, M, S)` ⇔ `S ⊆ M.carrier` and every vanishing combination over a finite `T ⊆ S` with coefficients in `R.carrier` has every coefficient `R.zero` |
| `ModuleBasisDef` | `module_basis(R, M, S)` ⇔ `module_independent(R, M, S) ∧ module_span(R, M, S) = M.carrier` |
| `IndependentInCarrier` | an independent set lies in `M.carrier`: the first conjunct |
| `BasisInCarrier` | a basis lies in `M.carrier`: it is independent, and an independent set lies there (`IndependentInCarrier`) |
| `IndependentVanishingCombination` | a vanishing combination over a finite part of an independent set has every coefficient `R.zero`: the second conjunct |

## The span, over any ring

| member | statement |
|---|---|
| `CombinationExtendByZero` | `finite(U) ∧ T ⊆ U ⊆ M.carrier ⇒` the combination over `U` of the coefficients on `T` extended by `R.zero` is the combination over `T` |
| `CombinationAdd` | over a finite `T ⊆ M.carrier`, `Σ_{x∈T} a(x) • x + Σ_{x∈T} b(x) • x = Σ_{x∈T} (a(x) + b(x)) • x` |
| `CombinationScale` | over a finite `T ⊆ M.carrier`, `c • Σ_{x∈T} a(x) • x = Σ_{x∈T} (c * a(x)) • x` |
| `CombinationPair` | for distinct `u, v` in `M.carrier` and scalars `a(u)`, `a(v)`, `Σ_{x∈{u, v}} a(x) • x = a(u) • u + a(v) • v` |
| `SpanCombinations` | `S ⊆ M.carrier ⇒ module_span(R, M, S)` = the finite combinations of `S` |
| `SpanMembership` | `S ⊆ M.carrier ⇒ (v ∈ module_span(R, M, S) ⇔` `v` is a combination over a finite `T ⊆ S` with coefficients in `R.carrier`) |
| `SpanRestrict` | for `S ⊆ N` a submodule, the span of `S` in `restrict_module(M, N)` is its span in `M` |
| `SpanningRestrict` | for a submodule `N`, `module_span(R, restrict_module(M, N), E) = N ⇔ E ⊆ N ∧ module_span(R, M, E) = N` |

## Independence, over any ring

| member | statement |
|---|---|
| `IndependentSubset` | a subset of an independent set is independent |
| `IndependentRestrict` | for `N ⊆ M.carrier`, `E` is independent in `restrict_module(M, N)` exactly when `E ⊆ N` and `E` is independent in `M` |
| `BasisRestrict` | for a submodule `N`, `module_basis(R, restrict_module(M, N), E) ⇔ module_independent(R, M, E) ∧ module_span(R, M, E) = N` |
| `IndependentEmpty` | `module_independent(R, M, ∅)` |
| `IndependentPair` | distinct `u, v` in `M.carrier` are independent exactly when `c • u + d • v = M.zero` with `c, d` in `R.carrier` forces `c = d = R.zero` |
| `RegularModuleBasis` | a commutative ring is free of rank one over itself: `{one}` is a basis of the ring as a module over itself |
| `IndependentZeroNotIn` | `R.one ≠ R.zero ∧ module_independent(R, M, S) ⇒ M.zero ∉ S` |
| `IndependentUniqueCoefficients` | two combinations of an independent set over one finite part that agree have equal coefficients |
| `IndependentChainUnion` | the union of a chain of independent sets is independent |
| `IndependentUnion` | two independent sets whose spans meet only in zero have an independent union |
| `IndependentSpansMeet` | the spans of two disjoint parts of an independent set meet only in zero |
| `IndependentInsertOutsideSpan` | `R.one ≠ R.zero`, `insert(v, S)` independent and `v ∉ S` ⇒ `v` lies outside `module_span(R, M, S)` |
| `IndependentInsertNoMultiple` | a vector of `M.carrier` that only `R.zero` scales into `module_span(R, M, S)` joins the independent `S` independently |
| `IndependentPartSpansMultiple` | over an integral domain, a finite `G ⊆ M.carrier` has an independent part `S` and a nonzero `a` with `a • g ∈ module_span(R, M, S)` for every `g` of `G` |

## Under a homomorphism, over any ring

| member | statement |
|---|---|
| `HomSpan` | a homomorphism carries `module_span(R, M, S)`, for `S ⊆ M.carrier`, onto `module_span(R, N, image(f, S))` |
| `HomSpanInSubmodule` | a homomorphism sends `module_span(R, M, S)`, for `S ⊆ M.carrier`, into every submodule `P` of `N` holding `image(f, S)` |
| `HomAgreeOnSpan` | homomorphisms agreeing on `S ⊆ M.carrier` agree on `module_span(R, M, S)` |
| `SpanInsertKernel` | a linear functional that is `R.one` at `e` and `R.zero` on `S ⊆ M.carrier` kills a vector of `module_span(R, M, insert(e, S))` only inside `module_span(R, M, S)` |
| `IndependentImage` | a one-to-one homomorphism carries an independent set to an independent set |
| `InjectiveImageBasis` | a one-to-one homomorphism carries a finite basis to a finite basis of its image module, of the same size |
| `IndependentImageKernel` | a homomorphism is one-to-one on an independent `S` whose span meets the kernel only in zero, and carries `S` to an independent set |
| `IndependentFromImage` | a set a homomorphism carries one-to-one onto an independent set is independent, and its span meets the kernel only in zero |
| `BasisPullback` | along a homomorphism one-to-one on `M.carrier`, a basis `E` of the image pulls back to the basis `preimage_on(M.carrier, f, E)` of `M` |

## Over a field

| member | statement |
|---|---|
| `SolveForMember` | a member `w` of a combination lying in a submodule `N`, with a nonzero coefficient and the other members in `N`, lies in `N` |
| `IndependentInsertIff` | `v ∈ M.carrier ∖ S ⇒ (module_independent(R, M, insert(v, S)) ⇔ module_independent(R, M, S) ∧ v ∉ module_span(R, M, S))` |
| `Exchange` | `v ∈ module_span(R, M, insert(w, S)) ∖ module_span(R, M, S) ⇒ w ∈ module_span(R, M, insert(v, S))` |
| `MaximalIndependentBasis` | an independent set is a basis when every vector of `M.carrier` that joins it independently already lies in it |
| `BasisBetween` | an independent `S` inside a spanning `U` extends to a basis `E` with `S ⊆ E ⊆ U` |
| `BasisExtends` | every independent set lies in a basis |
| `BasisExists` | `∃E. module_basis(R, M, E)` |
| `BasisWithinSpanning` | a spanning set holds a basis |
| `ReplacementStep` | a member `v` of an independent `I ⊆ span(S)` outside `S` replaces some `w ∈ S ∖ I`: `I` lies in the span of `insert(v, S ∖ {w})` |
| `Steinitz` | `finite(S) ∧ S ⊆ M.carrier ∧ module_independent(R, M, I) ∧ I ⊆ module_span(R, M, S) ⇒ finite(I) ∧ card(I) ≤ card(S)` |

Zorn's lemma enters once, at `BasisBetween`, at inclusion over the
independent sets between an independent `S` and a spanning `U`; that
family holds `S`, so it is never empty and no statement asks the module
to be nonzero. `BasisExtends` reads it at `U = M.carrier`,
`BasisWithinSpanning` at `S = ∅`.

## Additional interfaces

| Member | Statement |
|---|---|
| `IndexedModuleBasisDef` | `indexed_module_basis`: ring_ops(A) → module_ops(A, B) → num → (num → B) → bool |
| `IndexedBasisImage` | the vectors `{e(i) \| i < n}` of an indexed basis form a finite basis of n members, indexed one-to-one by `{i \| i < n}` |
| `IndexedBasisInCarrier` | each vector `e(i)`, `i < n`, of an indexed basis lies in `M.carrier` |
| `FiniteBasisIndexed` | a finite basis `E` is the vector set of an indexed basis of `card(E)` vectors |
| `IndependentImageCriterion` | a family `e` into `M`, one-to-one on `X`, has an independent image once its combinations over the finite parts of `X` vanish only with zero coefficients |
| `CharactersIndependent` | finitely many maps into an integral domain, keeping one and the product on `G` and differing pairwise on `G`, have only the zero combination vanishing on `G` |
