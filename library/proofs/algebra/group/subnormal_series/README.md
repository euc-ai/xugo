# subnormal_series — subnormal and composition series, Schreier's refinement theorem and the Jordan–Hölder theorem

For `G:group_ops(A)`, a subnormal series is a map `s : num → set(A)`
read with a length `n`: `s(0)` is the carrier, each term is a normal
subgroup of the one before, and every term from the `n`-th on is the
trivial group. Its factors are the quotient groups `s(i)/s(i+1)`,
groups on sets. Two series are equivalent when their proper factors
correspond one to one, corresponding factors isomorphic; a composition
series is one whose terms are maximal proper normal subgroups of their
predecessors, so that every factor is proper and has no proper
nontrivial normal subgroup — the maximality said of the terms. Schreier's
theorem refines two series of one group into equivalent series, and
the refinements are written out: between `s(i)` and `s(i+1)` go the
groups `s(i+1)·(s(i) ∩ t(j))`, the butterfly lemma matches the factor
at `(i, j)` with the other refinement's factor at `(j, i)`, and the
swap of the double index — `div` and `rem` by the lengths — is the
correspondence. Jordan–Hölder follows: a refinement of a composition
series can only repeat its terms, so it is equivalent to the series,
and the two series meet through their refinements. Nothing here is
chosen but the inverse of a correspondence and the index a factor of a
refinement comes from, and nothing is finite but a length.

## Series

| member | statement |
|---|---|
| `SubnormalSeriesDef` | `subnormal_series(G, s, n)` ⇔ `s(0) = G.carrier`, `s(i) = {G.one}` for `n ≤ i`, each term normal in the one before |
| `SeriesStart`, `SeriesTail`, `SeriesNormal` | the three conjuncts |
| `SeriesSubgroup`, `SeriesGroup`, `SeriesChain` | every term a subgroup of `G.carrier` and a group on a set; the terms descend — card |
| `TrivialCarrierSeries` | a series of `{G.one}` is `{G.one}` throughout — card |
| `FactorGroup` | `group_on(quotient_group(restrict_group(G, s(i)), s(i+1)))` — card |
| `FactorTrivialIff` | a factor is one point ⇔ its terms agree — card |
| `FactorsIsomorphicDef` | `factors_isomorphic(G, s, i, t, j)` ⇔ the two factor groups are isomorphic |
| `FactorsIsomorphicProper` | isomorphic factors are proper together — card |
| `FactorsIsomorphicRefl`, `FactorsIsomorphicSym`, `FactorsIsomorphicTrans` | an equivalence — card |
| `SeriesEquivalentDef` | `series_equivalent(G, s, n, t, m)` ⇔ the proper factors correspond, isomorphic |
| `EquivalentSym`, `EquivalentTrans` | symmetric and transitive — card |
| `SeriesRefinementDef` | `series_refinement(t, m, s, n)` ⇔ every term of `s` is a term of `t` |

## Schreier's theorem

| member | statement |
|---|---|
| `SchreierRefinementDef` | `schreier_refinement(G.mul, s, t, m)(k) = s(i+1)·(s(i) ∩ t(j))` at `i = div(k, m)`, `j = rem(k, m)` |
| `DoubleIndexSwapBelow`, `DoubleIndexSwapInverse` | the swap `k ↦ rem(k, m)·n + div(k, m)` is a bijection below `n·m` — card |
| `SchreierRefinementTerm` | the term at `i·m + j` for `j ≤ m` — card |
| `SchreierRefinementSeries` | the refinement is a subnormal series of length `n·m` — card |
| `SchreierRefinementRefines` | it refines `s` — card |
| `SchreierRefinementFactor` | its factor at `(i, j)` ≅ the other's at `(j, i)` — card |
| `Schreier` | the two refinements are equivalent — card |

## The Jordan–Hölder theorem

| member | statement |
|---|---|
| `CompositionSeriesDef` | `composition_series(G, s, n)` ⇔ subnormal, each term a maximal proper normal subgroup of the one before |
| `CompositionSubnormal`, `CompositionMaximal` | the two conjuncts |
| `CompositionSeriesInjective` | the terms up to the length are distinct — card |
| `CompositionRefinementStep` | after a term equal to `s(i)`, a refinement has `s(i)` or `s(i+1)` — card |
| `CompositionRefinementTerm` | every term of a refinement is a term of the series — card |
| `CompositionRefinementProperFactor` | a proper factor of a refinement is a factor of the series — card |
| `CompositionRefinementOnto` | every factor of the series is a proper factor of a refinement — card |
| `RefinementOfComposition` | a refinement of a composition series is equivalent to it — card |
| `JordanHolder` | two composition series are equivalent — card |
| `JordanHolderLength` | and have one length — card |
