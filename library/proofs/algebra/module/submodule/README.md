# submodule — submodules, spans and quotient modules of a module on a set

A submodule of a module `M` over a ring `R`, both record values
(module_record), is a subgroup of `M.carrier` under the vector addition
that is closed under scaling by `R.carrier`, `submodule(R, M, N)`; with
M's operations it is a module in its own right,
`module_on(R, restrict_module(M, N))`, and the submodules of `M` meet and
add to submodules. The span of a set is the least submodule holding it,
the meet of all of them. The quotient of `M` by a submodule `N` is the
quotient group of cosets, added as sets, and scaled without choosing a
representative: `quotient_smul(M.add, M.smul, N, c, s)` is the set
`c • s + N`, which for the coset `u + N` is the coset `c • u + N`; the
record `quotient_module(M, N)` packs those operations with the cosets.
A submodule of a submodule is the same notion one level down, at
`restrict_module(M, N)`; the facts that need no module law — a
submodule's two conjuncts and the inclusion and closures read off them,
meets, restriction, the span's order properties — bind the two records
and no module.

## Submodules

| member | statement |
|---|---|
| `SubmoduleDef` | `submodule(R, M, N)` ⇔ `subgroup(module_additive_group(M), N)` and `c ∈ R.carrier ∧ u ∈ N ⇒ c • u ∈ N` |
| `SubmoduleSubgroup` | a submodule is a subgroup of `M.carrier` under `M.add`: the first conjunct |
| `SubmoduleSmul`, `SubmoduleSubset`, `SubmoduleZero`, `SubmoduleAdd`, `SubmoduleNeg`, `SubmoduleSub` | a submodule holds `c • u` for `c ∈ R.carrier` (the second conjunct), lies in `M.carrier`, and holds `M.zero`, `u + v`, `-u` and `u − v` for `u, v` in it |
| `SubmoduleCriterion` | `N ⊆ M.carrier`, `M.zero ∈ N`, N closed under + and under scaling ⇒ `submodule(R, M, N)` |
| `SubmoduleModuleOn` | a submodule is a module over `R`, `module_on(R, restrict_module(M, N))` |
| `SubmoduleModuleSum` | `submodule(R, M, N)`, `finite(s)`, `F(x) ∈ N` on s ⇒ `module_sum(M.add, M.zero, s, F) ∈ N` |
| `CarrierSubmodule`, `ZeroSubmodule` | `M.carrier` and `{M.zero}` |
| `SubmoduleInter` | `N ∩ N'` |
| `SubmoduleSum` | `N + N'` |
| `SumLeast` | a submodule holding X and Y holds X + Y |
| `SumContainsLeft`, `SumContainsRight` | N ⊆ N + N' and N' ⊆ N + N' |
| `SubmoduleTrans` | `submodule(R, M, N) ∧ submodule(R, restrict_module(M, N), K) ⇒ submodule(R, M, K)`: a submodule of a submodule |
| `SubmoduleRestrict` | `submodule(R, M, K) ∧ K ⊆ N ⇒ submodule(R, restrict_module(M, N), K)`: a submodule lying in a set N is one of M restricted to N |
| `SubmoduleRestrictScalars` | `R'.carrier ⊆ R.carrier` ⇒ `submodule(R', M, N)`: a submodule for R's scalars is one for any ring whose scalars lie among R's |
| `IdealIffRegularSubmodule` | in a commutative ring `R`, `ring_ideal(R, I) ⇔ submodule(R, regular_module(R), I)` |

## Spans

| member | statement |
|---|---|
| `ModuleSpanDef` | `module_span(R, M, S) = ⋂{N \| submodule(R, M, N) ∧ S ⊆ N}` |
| `SpanSubmodule` | a submodule, when `S ⊆ M.carrier` |
| `SubsetSpan` | holding `S` |
| `SpanLeast` | inside every submodule holding `S` |
| `SpanMono` | `S ⊆ T ⇒ module_span(R, M, S) ⊆ module_span(R, M, T)` |
| `SpanEmpty` | `module_span(R, M, ∅) = {M.zero}` |
| `SpanInsert` | `module_span(R, M, insert(v, S)) = {c • v + w \| c ∈ R.carrier ∧ w ∈ module_span(R, M, S)}`, for `S ⊆ M.carrier` and `v ∈ M.carrier` |
| `SpanOfSubmodule` | `submodule(R, M, N) ⇒ module_span(R, M, N) = N` |
| `SpanClosureOperator` | span is a closure operator on `{S \| S ⊆ M.carrier}`, by `relations/order.ClosureFromLeast` |
| `SpanOfSubringSpan` | the R-span of the R₀-span of X is the R-span of X |
| `RegularSpanIsIdealSpan` | `X ⊆ R.carrier` in a commutative ring ⇒ `module_span(R, regular_module(R), X) = ideal_span(R, X)` |
| `SpanFamilyCombinations` | in a commutative ring, the ideal finitely many elements P(0), …, P(r − 1) generate is their combinations Σ P(j)·G(j) |
| `SpanFiniteSums` | `S ⊆ M.carrier` closed under scaling ⇒ `module_span(R, M, S)` is the set of finite sums `Σ_{i<n} F(i)` with every `F(i) ∈ S` |

## The quotient module

| member | statement |
|---|---|
| `QuotientSmulDef` | `quotient_smul(add, smul, N, c, s) = image(smul(c), s) + N` |
| `QuotientSmulCoset` | `quotient_smul(M.add, M.smul, N, c, u + N) = c • u + N` |
| `SubmoduleCosetEq` | for `x`, `y` in `M.carrier` and `S` a submodule, `x + S = y + S ⇔ x + -y ∈ S` |
| `SubmoduleNormal` | a submodule is a normal subgroup of `M.carrier` under `M.add` |
| `QuotientModuleDef` | `quotient_module(M, N)`: the cosets of `N` in `M.carrier`, added as sets, with `N` as the zero, and scaled by `quotient_smul` |
| `QuotientModuleOn` | `module_on(R, quotient_module(M, N))` for a submodule `N` |

## The annihilator of a vector of a simple module

| member | statement |
|---|---|
| `AnnihilatorOfSimpleMaximal` | every submodule is `{M.zero}` or `M.carrier`, `a ∈ M.carrier`, `a ≠ M.zero` ⇒ `{r ∈ R.carrier \| r • a = M.zero}` is a maximal ideal |
