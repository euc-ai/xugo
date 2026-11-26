# group_homomorphism — maps between groups on sets

A homomorphism is stated as `group_homomorphism(G, H, f)`, with
`G:group_ops(A)` and `H:group_ops(B)`. It includes the group laws for
both records, requires `f` to carry `G.carrier` into `H.carrier`, and
requires it to preserve the product on source carrier points. Under a
law, `x * y` uses `G.mul`, while `f(x) * f(y)` uses `H.mul`.

`Source` and `Target` project the two group facts, so their carrier laws
are read at these projections. The records may describe abelian groups
or arbitrary groups. A whole-type instance has carrier `𝕌` in each
record.

## The structure and its axioms

| member | statement under `group_homomorphism(G, H, f)` |
|---|---|
| `GroupHomomorphism` | the two group facts, carrying and product preservation |
| `Source` | `group_on(G)` |
| `Target` | `group_on(H)` |
| `MapIn` | `x ∈ G.carrier ⇒ f(x) ∈ H.carrier` |
| `MapMul` | `x ∈ G.carrier ∧ y ∈ G.carrier ⇒ f(x * y) = f(x) * f(y)` |
| `MapOne` | `f(G.one) = H.one` |
| `MapInv` | `x ∈ G.carrier ⇒ f(G.inv(x)) = H.inv(f(x))` |
| `MapPow` | `x ∈ G.carrier ⇒ f(monoid_pow(G.mul, G.one, x, n)) = monoid_pow(H.mul, H.one, f(x), n)` |

The identity is preserved because its image is an idempotent in the
target group, hence the target identity. The inverse is preserved
because its image is a left inverse of the image point, and that inverse
is unique in the target carrier.

## Kernel and image

The low-level set `group_kernel(one, c, f)` uses a distinguished target
point and a source set. For a homomorphism its arguments are
`group_kernel(H.one, G.carrier, f)`. It is a normal subgroup of `G`.
The image `image(f, G.carrier)` is a subgroup of `H`. Conversely, a map
that carries a group's carrier onto the carrier of a group record, and
its product, identity and inverse to the record's, makes that record a
group: the homomorphic image of a group is a group, and the quotient
group is an instance of it.

| member | statement |
|---|---|
| `GroupKernelDef` | `group_kernel(one, c, f) = {x \| x ∈ c ∧ f(x) = one}` |
| `InKernel` | its membership reading |
| `KernelSubgroup` | `subgroup(G, group_kernel(H.one, G.carrier, f))` |
| `KernelNormal` | `normal_subgroup(G, group_kernel(H.one, G.carrier, f))` |
| `EqIffInKernel` | source carrier points have equal images exactly when their inverse difference lies in the kernel |
| `EqIffInLeftCoset` | they have equal images exactly when they lie in one left coset of the kernel |
| `KernelTrivialIffInjective` | `group_kernel(H.one, G.carrier, f) = {G.one} ⇔ injective_on(G.carrier, f)` |
| `ImageSubgroup` | `subgroup(H, image(f, G.carrier))` |
| `ImageGroupOn` | `group_on(H)` for a record `H` with `image(f, G.carrier) = H.carrier`, when `f` carries `G`'s product, identity and inverse to `H`'s |
| `ImageAbelianGroupOn` | `abelian_group_on(H)` under the same hypotheses, when `G` is abelian |
| `SubgroupImage` | The image of a subgroup is a subgroup |

Kernel closure follows from preservation of product and inverse, and
normality follows by mapping a conjugate. The image's conditions, as a
subgroup (`ImageSubgroup`) and as a group (`ImageGroupOn`), quantify
over image points: each pulls back along `f` to the same condition at
their preimages, where the source's law holds and the map's laws carry
it across. `ImageAbelianGroupOn` pulls commutativity back the same way.

## Identity, composition and isomorphisms

| member | statement |
|---|---|
| `IdentityHom` | `group_on(G) ⇒ group_homomorphism(G, G, identity_map)` |
| `ComposeHom` | `group_homomorphism(G, H, f) ∧ group_homomorphism(H, K, g) ⇒ group_homomorphism(G, K, g ∘ f)` |
| `GroupIsomorphismDef` | `group_isomorphism(G, H, f)` is a homomorphism injective on `G.carrier` and onto `H.carrier` |
| `IsomorphismHomomorphism`, `IsomorphismInjective`, `IsomorphismSurjective` | its three conditions |
| `InnerAutomorphism` | `group_on(G) ∧ g ∈ G.carrier ⇒ group_isomorphism(G, G, λx:A. g * x * G.inv(g))` |

Conjugation by a point of the carrier is an automorphism: g⁻¹g cancels
between two conjugates, so it respects products; it is one-to-one by
cancellation, and each point x is the conjugate of g⁻¹xg.

The first isomorphism theorem in `quotient_group` identifies the quotient
by the kernel with the image, using these same record-based predicates.
