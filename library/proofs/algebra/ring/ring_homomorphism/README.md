# ring_homomorphism — maps between rings on sets that keep the sum, the product and the one

A ring homomorphism carries a ring `R` into a ring `S`, keeping the
sum, the product and the one: `ring_homomorphism(R, S, f)`, the two
rings given as records. Both rings are the definition's first two conjuncts, as
both groups are a group homomorphism's. Keeping the sum makes the map a
homomorphism of the two additive groups (`AdditiveHomomorphism`), and
so it keeps zero and the negation. An isomorphism is a homomorphism
that is one-to-one on `R.carrier` and reaches every member of
`S.carrier`. Its carrier inverse `inverse_on(R.carrier, f)` is an
isomorphism in the reverse direction.

Conversely, a map that carries a commutative ring's carrier onto the
carrier of a ring record, and its six operations to the record's, makes
that record a commutative ring: the homomorphic image of a commutative
ring is one. Its additive group is the image of the source's abelian
additive group (`group_homomorphism.ImageAbelianGroupOn`) and its
multiplicative monoid the image of the source's
(`comm_monoid.ImageCommMonoidOn`); the two laws joining the operations
are pulled back along the map. The quotient by an ideal
and a ring carried along an injection are its instances.

| member | statement |
|---|---|
| `RingHomomorphism` | `ring_homomorphism(R, S, f)` ⇔ both rings, `f` maps `R.carrier` into `S.carrier`, keeps `+`, `*` and the one |
| `Source`, `Target` | the two rings |
| `MapIn`, `MapAdd`, `MapMul`, `MapOne` | the four conditions |
| `MapUnit` | `φ` carries a unit `ring_unit(R, x)` of the source to a unit `ring_unit(S, φ(x))` of the target |
| `AdditiveHomomorphism` | `group_homomorphism(additive_group(R), additive_group(S), f)`: `f` is a homomorphism of the additive groups, so it keeps the negation (`group_homomorphism.MapInv`, read at it) |
| `MapZero` | `f(R.zero) = S.zero` |
| `ZeroIffImageZero` | `injective_on(R.carrier, f)` and `x ∈ R.carrier` ⇒ (`x = R.zero ⇔ f(x) = S.zero`): a homomorphism one-to-one on its source sends exactly zero to zero |
| `MapNeg` | `x ∈ R.carrier ⇒ f(-x) = -f(x)` |
| `MapSub` | `x, y ∈ R.carrier ⇒ f(x - y) = f(x) - f(y)` |
| `RingMapNumeral` | `f(monoid_pow(R.add, R.zero, R.one, n)) = monoid_pow(S.add, S.zero, S.one, n)`: `f` keeps the numerals |
| `RingKernelDef` | `ring_kernel(zero', c, f)` = the members of `c` that `f` sends to `zero'` |
| `KernelIdeal` | the kernel is an ideal of the source |
| `RestrictionImageKernel` | A map cut down to S keeps its image on S, and its kernel is the old kernel met with S |
| `IdealSpanInKernel` | `E ⊆ R.carrier` and `f` zero on `E` ⇒ `ideal_span(R, E) ⊆ ring_kernel(S.zero, R.carrier, f)`: a ring map that kills a set kills the ideal it spans |
| `ImageCommRingOn` | `comm_ring_on(S)` for a ring record `S` with `image(f, R.carrier) = S.carrier`, when `f` carries the sum, zero, negation, product, one and difference of a commutative ring `R` to `S`'s |
| `ImageSubfield` | for fields `F` and `G`, `ring_homomorphism(field_ring(F), field_ring(G), f) ⇒ subfield(G, image(f, F.carrier))` |
| `FieldHomomorphismInjective` | for fields `F` and `G`, `ring_homomorphism(field_ring(F), field_ring(G), f) ⇒ injective_on(F.carrier, f)` |
| `SubfieldHomomorphismEmbedding` | for fields `M` and `L`, `subfield(M, k)` and `ring_homomorphism(restrict_ring(field_ring(M), k), field_ring(L), σ)` ⇒ `subfield(L, image(σ, k)) ∧ injective_on(k, σ)`: a ring map out of a subfield embeds it |
| `RingHomIdentity` | the identity of a ring is a ring homomorphism to itself |
| `PreimageIdeal` | the preimage `preimage_on(R.carrier, φ, I)` of an ideal `I` of the target is an ideal of the source |
| `IdealSpanImage` | a ring isomorphism takes the ideal a set spans to the ideal its image spans |
| `RingHomCompose` | the composite of two ring homomorphisms is one |
| `RingHomCongruence` | `ring_homomorphism(R, S, u)` and `v(x) = u(x)` on `R.carrier` ⇒ `ring_homomorphism(R, S, v)` |
| `RingHomRestrictSource` | `ring_homomorphism(R, S, f)` and `subring(R, T)` ⇒ `ring_homomorphism(restrict_ring(R, T), S, f)`: a ring map restricts to a subring of its source |
| `SubringInclusionHom` | `subring(R, T) ⇒ ring_homomorphism(restrict_ring(R, T), R, λa:A. a)`: a subring includes into its ring |
| `RingHomCorestrict` | `ring_homomorphism(R, S, f)`, `subring(S, T)` and `f` carrying `R.carrier` into `T` ⇒ `ring_homomorphism(R, restrict_ring(S, T), f)` |
| `RingHomExtendTarget` | `ring_homomorphism(R, restrict_ring(S, T), f)`, `comm_ring_on(S)` and `T ⊆ S.carrier` ⇒ `ring_homomorphism(R, S, f)` |
| `RingIsomorphismDef` | `ring_isomorphism(R, S, f)` ⇔ a homomorphism, one-to-one on `R.carrier`, onto `S.carrier` |
| `IsomorphismInverse` | `inverse_on(R.carrier, f)` is an isomorphism from the target ring back to the source |
| `ImageSubring` | The image of a ring map is a subring of the target |
| `RingMapEqualizerSubring` | The elements where two ring maps agree form a subring |
| `RingMapPreimageSubring` | The elements a ring map sends into a subring of its target form a subring |
| `FactorsThroughOnto` | A homomorphism killing what a surjection kills factors through it |
| `KernelFactorization` | A ring map killing the kernel of another factors through its image |
| `RingMapPower` | A ring homomorphism keeps the powers of a member of its source |
| `RingMapProductSum` | A ring homomorphism takes a finite sum of triple products term by term |
