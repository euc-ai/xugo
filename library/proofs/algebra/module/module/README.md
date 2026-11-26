# module — a module over a commutative ring, on a carrier set

A module is an abelian group of vectors on which the ring's scalars act.
The ring and the module are each one value of a record type
(module_record): `R : ring_ops(A)` holds the ring's six operations and
the set of scalars, `M : module_ops(A, B)` the vector addition, zero,
negation, the scaling and the set of vectors. `module_on(R, M)` says the
vectors of `M` are a module over the commutative ring `R`:
`comm_ring_on(R)`; `M.carrier` is a group on a set
under `M.add`, which commutes there; `M.carrier` is closed under the
scaling `c • u` by a scalar of `R.carrier`; and scaling distributes over
both additions, associates with the ring's product, and fixes a vector
at `R.one`. The scalars and the vectors live in two types, and the two
additions share the symbol `+`, each read at its own operands; the
scaling carries `•`, read at a scalar and a vector.

Both carriers are parts of the records because a module's submodules
and quotients are modules on sets and a ring's localizations and
quotients are rings on sets, and every law is proved once for a module
on a set over a ring on a set (constitution §Structures, "One proof per
law"). An instance is a packed value: the n-vectors over a ring are
`mk_module(vec_add, vec_zero, vec_neg, vec_scalar_mul, {u | vec⟨n⟩(u)})`
over `restrict_ring(R, 𝕌)` (`vec_space.ModuleOn`), and a law read there
states the packed parts once the record's projections read them off.

## The structure and its axioms

The ring and the additive group are the definition's first two
conjuncts, so the laws of the ring chapter's carrier form apply at a
module through `RingOn`, the laws of the group chapter's carrier form
through `AddGroupOn`, written additively, and those of the abelian group
chapter through `AddAbelianGroupOn`, the group and its commutativity
together, and those of the commutative monoid chapter through
`AddMonoidOn`, the addition and its zero.

| member | statement |
|---|---|
| `ModuleOn` | `module_on(R, M)` ⇔ `R` a commutative ring on its carrier, `M.carrier` a group on a set under `+` that commutes, closed under `•` by scalars of `R.carrier`, and the four scaling laws for scalars of `R.carrier` and members of `M.carrier` |
| `RingOn` | `comm_ring_on(R)` |
| `AddGroupOn` | `group_on(module_additive_group(M))` |
| `AddComm` | `u ∈ M.carrier ∧ v ∈ M.carrier ⇒ u + v = v + u` |
| `AddAbelianGroupOn` | `abelian_group_on(module_additive_group(M))`: `AddGroupOn` and `AddComm` together |
| `AddMonoidOn` | `comm_monoid_on(M.carrier, M.add, M.zero)`: the abelian group's own monoid (`abelian_group.MonoidOn` read at `AddAbelianGroupOn`) |
| `SmulIn` | `c ∈ R.carrier ∧ u ∈ M.carrier ⇒ c • u ∈ M.carrier` |
| `SmulAddLeft` | `c • (u + v) = c • u + c • v` for a scalar and two vectors |
| `SmulAddRight` | `(c + d) • u = c • u + d • u` for two scalars and a vector |
| `SmulMul` | `(c * d) • u = c • (d • u)` for two scalars and a vector |
| `SmulOne` | `u ∈ M.carrier ⇒ R.one • u = u` |

## The zero laws

Each zero is the one element of the additive group that is its own
double. `R.zero • u` is `(R.zero + R.zero) • u`, which distributes to
`R.zero • u + R.zero • u`; `c • M.zero` is `c • (M.zero + M.zero)` the
same way. The group chapter's `IdempotentIsOneOn`, read at the vectors
with `+` for its operation, then names the element the vectors' zero.

| member | statement |
|---|---|
| `ZeroSmul` | `u ∈ M.carrier ⇒ R.zero • u = M.zero` |
| `SmulZero` | `c ∈ R.carrier ⇒ c • M.zero = M.zero` |
| `SmulNeg` | `c • (−u) = −(c • u)` for a scalar and a vector |
| `NegSmul` | `(−c) • u = −(c • u)` for a scalar and a vector: `(−c) • u + c • u = (−c + c) • u = R.zero • u = M.zero` (`SmulAddRight`, `ZeroSmul`), so `(−c) • u` is the inverse of `c • u` (`InvUniqueOn` at `AddGroupOn`) |
| `NegOneSmul` | `u ∈ M.carrier ⇒ (−R.one) • u = −u`: `NegSmul` at `R.one`, and `SmulOne` |
| `RegularModuleOn` | `comm_ring_on(R) ⇒ module_on(R, regular_module(R))`, a commutative ring a module over itself: each module axiom is a ring axiom — the additive group and its commutativity, `MulIn`, the two distributive laws, and the associativity and left identity of the multiplicative monoid |
| `RegularModuleOverSubring` | a commutative ring is a module over each of its subrings |
| `ModuleRestrictScalars` | `S` a subring of `R.carrier` ⇒ `module_on(restrict_ring(R, S), M)`: a module over R is one over each subring, its scalars restricted |

## Finite sums

A sum over a finite index set is the fold of the family under an
addition from a zero, the step reading the family on the index set
only: `module_sum(add, zero, s, F)`, a module's sum
`module_sum(M.add, M.zero, s, F)` and a ring's
`module_sum(R.add, R.zero, s, F)`. The definition, the empty sum and the
congruence hold for any addition and zero; the other laws hold for
families valued in `M.carrier` on the index set, through cardinality's
fold laws within a set.

| member | statement |
|---|---|
| `ModuleSumDef` | `module_sum(add, zero, s, F) = set_fold(λx a. COND(x ∈ s, add(F(x), a), a), s, zero)` |
| `ModuleSumEmpty` | the empty sum is the zero: no index lies in ∅, so the step is the identity |
| `ModuleSumCongruence` | a sum reads its family on `s` only: the two steps are one function — on `s` the families agree, off `s` both return the accumulator |

## The fold of a commutative monoid on a set

The insert and delete laws, membership, reindexing along an injective map,
the termwise combination and the fold of the identity read only a
commutative monoid on a set, `comm_monoid_on(c, op, e)`. They are proved
there once; a module's `ModuleSumInsert`, `ModuleSumIn`, `ModuleSumImage`,
`ModuleSumAdd` and `ModuleSumZero` are those laws read at `AddMonoidOn`, and
a ring's finite product `module_sum(R.mul, R.one, s, F)` reads them at
`comm_monoid_on(R.carrier, R.mul, R.one)`. The empty fold and the congruence
ask nothing of the operation. A commutative monoid on the whole type, which
has the fold mechanism's `iterated_op` beside this one, folds the same value
either way (`ModuleSumIteratedOp`).

| member | statement |
|---|---|
| `ModuleSumInsertMonoid` | `finite(s)`, `x ∉ s`, `F` in `c` on `insert(x, s)` ⇒ `module_sum(op, e, insert(x, s), F) = op(F(x), module_sum(op, e, s, F))`: the step of an index set on which `F` lies in `c` keeps `c` and left-commutes there (`LeftCommOn`), so the fold over `insert(x, s)` applies the step at `x` last, and over `s` it agrees with the step of `s` |
| `ModuleSumDeleteMonoid` | `finite(s)`, `x ∈ s`, `F` in `c` on `s` ⇒ `module_sum(op, e, s, F) = op(F(x), module_sum(op, e, delete(s, x), F))`: a ring's finite product singles out one factor by it, read at `comm_ring.MulMonoidOn` |
| `ModuleSumInMonoid` | a fold of members of `c` over a finite set lies in `c`: by induction on the index set (`FiniteInductFreshOn`), the empty fold is `e`, and a new index combines two members of `c` (`OpIn`) |
| `ModuleSumImageMonoid` | `g` injective on `s` ⇒ the fold over `image(g, s)` of `F` is the fold over `s` of `F ∘ g`: by induction on the index set, `g(x)` is new to the image of the rest by injectivity, so `F(g(x))` peels off both sides (`ModuleSumInsertMonoid` twice) |
| `ModuleSumReindex` | `σ` maps the indices below n injectively into themselves, `G` in `c` below n ⇒ `module_sum(op, e, {a \| a < n}, λa. G(σ(a))) = module_sum(op, e, {a \| a < n}, G)`: an injective self-map of the indices below n is onto them, and `ModuleSumImageMonoid` reindexes |
| `ModuleSumMonoidHomomorphism` | `h(e) = e₂` and `h(op(u, v)) = op₂(h(u), h(v))` on `c` ⇒ `h` of the fold is the fold of the images under `op₂` from `e₂`; a ring map's multiplicative part is such an `h` |
| `ModuleSumConstantMonoid` | `finite(s)`, `a ∈ c` ⇒ `module_sum(op, e, s, λx. a) = a ^ card(s)`: a fold of one constant is its power by the size of the index set |
| `ModuleSumIdentityMonoid` | `finite(s)`, `F = e` on `s` ⇒ `module_sum(op, e, s, F) = e`: a fold of the identity is the identity |
| `ModuleSumAddMonoid` | `finite(s)`, `F` and `G` in `c` on `s` ⇒ `module_sum(op, e, s, λx. op(F(x), G(x))) = op(module_sum(op, e, s, F), module_sum(op, e, s, G))`: the fold of a termwise combination combines the folds |
| `ModuleSumIteratedOp` | `comm_monoid(op, e)`, `finite(s)` ⇒ `module_sum(op, e, s, F) = iterated_op(op, s, F)`: by induction on the index set, both empty folds are the identity, the operation's neutral element (`comm_monoid.Neutral`), and a new index combines its term with the fold before it on both sides (`ModuleSumInsertMonoid`, `monoidal.OneTurn`) |

## A module's sums

| member | statement |
|---|---|
| `ModuleSumInsert` | one more index adds its term: `ModuleSumInsertMonoid` read at the vectors' commutative monoid (`AddMonoidOn`) |
| `ModuleSumBelowClauses` | the sum below 0 is `M.zero`, and with the terms below suc(k) in M, the sum below suc(k) is the sum below k plus F(k) |
| `GeometricSum` | `w ∈ R.carrier` ⇒ `(w - R.one) * module_sum(R.add, R.zero, {a \| a < n}, λa. monoid_pow(R.mul, R.one, w, a)) = monoid_pow(R.mul, R.one, w, n) - R.one`: the geometric sum in a commutative ring, by induction on n through `ModuleSumBelowClauses` at `RegularModuleOn` |
| `ModuleSumDelete` | `finite(s)`, `x ∈ s`, `F` in `M.carrier` on `s` ⇒ `module_sum(M.add, M.zero, s, F) = F(x) + module_sum(M.add, M.zero, delete(s, x), F)`: `s` is `insert(x, delete(s, x))` with `x` new there (`InsertDelete`, `InDelete`), and `ModuleSumInsert` peels `F(x)` |
| `ModuleSumIn` | a sum of vectors is a vector: `ModuleSumInMonoid` read at `AddMonoidOn` |
| `ModuleSumImage` | a sum over the image of a map injective on the index set is the sum of the composite: `ModuleSumImageMonoid` read at `AddMonoidOn` |
| `ModuleSumConstant` | `finite(s)`, `v ∈ M.carrier` ⇒ `module_sum(M.add, M.zero, s, λi. v) = monoid_pow(R.add, R.zero, R.one, card(s)) • v`: `v` is `R.one • v`, the sum of these scales `v` by the sum of the ones (`ModuleSumSmulRight`), and that sum is `ModuleSumConstantMonoid` read at the scalars' additive monoid |
| `ModuleSumZero` | `finite(s)`, `F = M.zero` on `s` ⇒ `module_sum(M.add, M.zero, s, F) = M.zero`: a sum of zeros is `M.zero`, `ModuleSumIdentityMonoid` read at `AddMonoidOn` |
| `ModuleSumAdd` | `finite(s)`, `F` and `G` in `M.carrier` on `s` ⇒ `module_sum(M.add, M.zero, s, λx. F(x) + G(x)) = module_sum(M.add, M.zero, s, F) + module_sum(M.add, M.zero, s, G)`: the sum of two families is the sum of their sums, `ModuleSumAddMonoid` read at `AddMonoidOn` |
| `ModuleSumSmul` | a scalar passes through a sum: by induction on the finite index set, `c • M.zero = M.zero`, and `c • (F(x) + rest) = c • F(x) + c • rest`, the claim carried to the indices before `x` scaling the rest |
| `ModuleSumSmulRight` | a sum of scalars scales to a sum: by induction on the finite index set, the ring's sum read as the fold of the scalars' additive monoid (`comm_ring.AddMonoidOn` at `RingOn`), each scalar distributed through `SmulAddRight` |
| `ModuleSumSupport` | a sum over a superset of the support is the sum over the support: `s` is `t ∪ (s ∖ t)`, two disjoint finite sets, so the sum over `s` is the sum over `t` plus the sum over `s ∖ t` (`ModuleSumDisjointUnion`), and the second is `M.zero` (`ModuleSumZero`) |
| `ModuleSumSingle` | a sum whose terms vanish on `s` off one index `x ∈ s` is `F(x)`: `ModuleSumSupport` shrinks it to `{x}`, which is `insert(x, ∅)` (`ModuleSumInsert`), and the empty sum is `M.zero` (`ModuleSumEmpty`) |
| `ModuleSumSwap` | two sums interchange: each double sum is a sum over a product of the index sets (`ModuleSumCross` twice), and `s × t` is the image of `t × s` under the swap of pairs (`CrossSwap`), one to one there, so `ModuleSumImage` carries one sum to the other |
| `ModuleSumFibres` | `finite(S)`, `F` in `M.carrier` on `S` ⇒ `module_sum(M.add, M.zero, S, F) = module_sum(M.add, M.zero, image(f, S), λz. module_sum(M.add, M.zero, {i \| i ∈ S ∧ f(i) = z}, F))`: a sum is the sum of its sums over the fibres of `f`: the mask, `F(i)` where `f(i) = z` and `M.zero` elsewhere, sums over the image to `F(i)` (`ModuleSumSingle`) and over `S` to the fibre sum (`ModuleSumSupport`), and its two sums interchange (`ModuleSumSwap`) |
| `ModuleSumTriangleSwap` | a sum over the triangle `i ≤ k ≤ n` grouped by `k` is the sum grouped by `i` with `k = i + j`, `j ≤ n − i`: padded by `M.zero` off the triangle, `G` fills the square, where the two sums interchange (`ModuleSumSwap`); each padded row is its row and each padded column the column read from the diagonal (`ModuleSumSupport`, `ModuleSumImage`) |
| `PowNatSum` | `x ∈ c`, `finite(s)` ⇒ in a commutative monoid `x ^ nat_sum(s, m) = module_sum(op, e, s, λi. x ^ m(i))` |
| `NatSumNumeral` | `finite(s)` ⇒ the numeral of `nat_sum(s, m)` is `module_sum(R.add, R.zero, s, λi. monoid_pow(R.add, R.zero, R.one, m(i)))` |
| `ModuleSumDisjointUnion` | a sum over a disjoint union is the sum of the two sums: by induction on the second index set, the union with `∅` is the first and the empty sum is `M.zero`; an index `x` added to `t` lies outside `s` by disjointness, so `x` is new to `s ∪ t` as to `t`, and `F(x)` peels off both sides, regrouped by associativity and commutativity |
| `ModuleSumNeg` | the sum of the negatives is the negative of the sum: by induction on the finite index set, `−M.zero = M.zero`, and `−F(x) + −rest = −(F(x) + rest)`, `NegAddOn` read at `AddAbelianGroupOn` |
| `ModuleSumCross` | a double sum is the sum over the product of the index sets: by induction on the first index set, a new index `x` adds its row on the left and, on the right, the pairs `(x, y)` for `y` in `t`, disjoint from the pairs over the rest; `y ↦ (x, y)` is injective and the projections undo the pairing, so their sum is the row of `x` |
| `ModuleSumSupportMonoid` | A fold over a finite set does not see the indices where its term is the identity |
| `ModuleSumSingleMonoid` | A fold over a part of {x} is the term at x, when that term is the identity should x lie off the part |
| `SupportSumAdditive` | A sum over the support of a divisor, each point reading its coefficient through a map that carries the coefficients' addition to the monoid's operation, is additive in the divisor |
