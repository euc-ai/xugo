# group_isomorphism — the isomorphism theorems and the butterfly lemma for groups on sets

Two records `G:group_ops(A)` and `H:group_ops(B)` are isomorphic when some map is an isomorphism
between them, `group_isomorphic(G, H)`. The chapter states the second
and third isomorphism theorems with their maps written out — a coset
goes to a coset by a set operation, `s ↦ s·n` and `S ↦ ⋃S`, and the
theorems' maps choose nothing — and Zassenhaus's butterfly lemma, which is the second
isomorphism theorem read twice, inside a subgroup each time, with
Dedekind's modular law computing the kernels. Every statement is about
groups on sets, so a subgroup of a subgroup, a quotient of a subgroup
and a quotient of a quotient are the same notions one level down;
nothing here mentions a type. A fact that needs no group law — a meet
of subgroups, normality carried into a subgroup, the symmetry and
transitivity of being isomorphic — binds the group record without assuming its group laws.

The lemma's setting, spelled once: `a` and `b` are subgroups of the
group on `G.carrier`, `a'` is normal in `a` and `b'` in `b`. Then
`a'(a ∩ b)/a'(a ∩ b')` and `b'(a ∩ b)/b'(a' ∩ b)` are isomorphic, each
being isomorphic to `(a ∩ b)/((a' ∩ b)(a ∩ b'))`. The Jordan–Hölder
chapter reads the lemma at the double series of two subnormal series.

## Subgroups of a group on a set

| member | statement |
|---|---|
| `SubgroupInter` | `subgroup(G, h) ∧ subgroup(G, k) ⇒ subgroup(G, h ∩ k)` |
| `SubgroupTrans` | `subgroup(G, h) ∧ subgroup(restrict_group(G, h), k) ⇒ subgroup(G, k)` |
| `SubgroupRestrict` | `subgroup(G, k) ∧ k ⊆ h ⇒ subgroup(restrict_group(G, h), k)` |
| `PSubgroupRestrict` | `p_subgroup(G, p, P) ∧ P ⊆ K ⇒ p_subgroup(restrict_group(G, K), p, P)`: a p-subgroup inside a set K is a p-subgroup of G restricted to K |
| `SetMulSubgroup` | `h` normalizes `k` ⇒ `subgroup(G, hk)` |
| `SetMulNormal` | `subgroup(G, h) ∧ normal_subgroup(G, n) ⇒ subgroup(G, hn)` |
| `SetMulNormalSwap` | `h ⊆ G.carrier ∧ normal_subgroup(G, n) ⇒ hn = nh` |
| `SetMulAbsorb` | `subgroup(G, h) ∧ k ⊆ h ∧ G.one ∈ k ⇒ hk = h` — card |
| `SubsetSetMulLeft` | `h ⊆ hk` |
| `SubsetSetMulRight` | `k ⊆ hk` — card |
| `NormalRestrict` | a normal subgroup inside a subgroup `h` is normal in `h` |
| `NormalInter` | `normal_subgroup(restrict_group(G, h), h ∩ n)` — card |
| `NormalInSetMul` | `normal_subgroup(restrict_group(G, hn), n)` — card |
| `DedekindModular` | `subgroup(G, k) ∧ h ⊆ k ∧ n ⊆ G.carrier ⇒ k ∩ hn = h(k ∩ n)` |

## The isomorphism theorems

| member | statement |
|---|---|
| `SecondIsomorphism` | `s ↦ s·n` is an isomorphism of `h/(h ∩ n)` onto `hn/n` — card |
| `ThirdIsomorphismNormal` | `n ⊆ m` normal ⇒ `m/n` is normal in `G/n` |
| `ThirdIsomorphism` | `S ↦ ⋃S` is an isomorphism of `(G/n)/(m/n)` onto `G/m` |

## Isomorphism as a relation, and the butterfly lemma

| member | statement |
|---|---|
| `GroupIsomorphicDef` | `group_isomorphic(G, H)` ⇔ some `f` is an isomorphism |
| `IsomorphismInverse` | `inverse_on(G.carrier, f)` is a group isomorphism in the reverse direction |
| `IsomorphismCompose` | the composite of isomorphisms is an isomorphism — card |
| `IsomorphismFiniteCard` | an isomorphism's carriers are finite together, and then of equal card |
| `IsomorphicRefl`, `IsomorphicSym`, `IsomorphicTrans` | an equivalence — card |
| `IsomorphicTrivial` | isomorphic groups are trivial together — card |
| `ZassenhausSubgroup` | `subgroup(restrict_group(G, a), a'(a ∩ b))` (no `b'` needed) — card |
| `ZassenhausNormal` | `normal_subgroup(restrict_group(G, a'(a ∩ b)), a'(a ∩ b'))` — card |
| `ZassenhausProduct` | `(a ∩ b) · a'(a ∩ b') = a'(a ∩ b)` — card |
| `ZassenhausMeet` | `(a ∩ b) ∩ a'(a ∩ b') = (a' ∩ b)(a ∩ b')` — card |
| `ZassenhausLeft`, `ZassenhausRight` | each quotient is isomorphic to the middle one — card |
| `Zassenhaus` | the two quotients are isomorphic — card |
