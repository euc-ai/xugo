# biaffine_deformation — the deformations of a curve held by two affine charts, glued from deformations of the charts by an isomorphism of their localizations, with the obstruction in two levels

A curve held by two charts (`scheme/lattice_pair`) is a ring A₀₁, the
overlap, with two subrings A₀ and A₁ and t ∈ A₀, s ∈ A₁ inverse to each
other, A₀₁ = A₀[1/t] = A₁[1/s]; its coefficients are a lattice pair, an
A₀-module M₀ and an A₁-module M₁ inside one module V over A₀₁, spanning
the same overlap module M₀₁. An extension of the curve by M is then two
extensions of the charts and a gluing: E₀ of A₀ by M₀ and E₁ of A₁ by M₁,
over a base ring P, and an isomorphism φ from E₀ with a lift of t
inverted onto E₁ with a lift of s inverted. Both localizations are
extensions of A₀₁ by M₀₁, read in place, so φ is an isomorphism of
extensions of one ring by one module. A deformation of the curve over a
square-zero thickening R → R₀ is the same thing over R whose two chart
extensions are deformations of the charts (`algebra/cotangent/algebra_deformation`):
a deformation of a curve held by two charts is two chart deformations and
an isomorphism of their localizations on the overlap.

The extensions are classified in two steps. Each has a pair of chart
classes, in D¹ of A₀ and of A₁, and the gluing forces them to agree on the
overlap, where a class of a chart is read through the restriction —
the coefficient map into M₀₁ followed by the inverse of the right map of
P → A_i → A₀₁, D¹ being contravariant in the algebra. Every agreeing pair
is reached, and the extensions with one pair of chart classes are the
regluings of one of them, its gluing φ moved by the shear of a
derivation d of the overlap. Two regluings are isomorphic exactly when
the derivations differ by a derivation of A₀ into M₀ plus one of A₁ into
M₁. Those two modules form the derivation pair 𝒟⁰, a lattice pair inside
the derivations of the overlap when the charts are finitely generated, so
the fibre is H¹(𝒟⁰); the extensions that split on both charts are the
split extensions glued by shears, H¹(𝒟⁰) itself. That is the sequence
0 → H¹(𝒟⁰) → extensions → compatible classes → 0, with each fibre an
H¹(𝒟⁰)-torsor; the automorphisms of an extension are H⁰(𝒟⁰), the
derivations of the curve.

The obstruction to a deformation comes in two levels. The local one is
the pair of the charts' obstructions, ∂¹ of the thickening class in
D²(A₀/R₀, M₀) and in D²(A₁/R₀, M₁): it vanishes exactly when each chart
deforms, and says nothing of the overlap. Once it does, two chart
deformations localize to deformations of the overlap, whose classes have
the same image in D¹(R₀/R, M₀₁); their difference is the image of
exactly one δ in D¹(A₀₁/R₀, M₀₁), and the class of δ modulo the
restrictions of the charts' D¹ is the gluing obstruction. It does not
depend on the chart deformations chosen, and it vanishes exactly when
they can be chosen to glue, that is when the curve deforms. The
deformations, when there are any, move in the same two layers as the
extensions: their chart classes by the compatible pairs of classes over
R₀, and each fibre by regluing modulo 𝒟₀ + 𝒟₁. When both charts are
smooth over R₀ the charts' D¹ and D² vanish, and with them D¹ of the
overlap, both obstructions and the compatible classes: a smooth curve
deforms, and its deformations are an H¹(𝒟⁰)-torsor.

The isomorphism classes of deformations are a torsor under the group of
extensions of the curve over R₀. Its group law is the Baer sum of
square-zero extensions (algebra/ring/square_zero_extension), taken chart
by chart and glued by the sum of the two gluings on the Baer sum of the
localizations. The group `biaffine_exal` is the set of isomorphism
classes of the extensions realized on `set(prod(U, D))`, each class a set
of 5-tuples, with the class of a Baer sum for the sum; it is abelian and
sits in the exact sequence 0 → H¹(𝒟⁰) → Exal → compatible classes → 0,
H¹(𝒟⁰) read as all the derivations of the overlap modulo
fst(𝒟⁰) + snd(𝒟⁰), which is `lattice_pair_h1` when both charts are
finitely generated. The deformations are the Baer sums of one deformation
with the extensions over R₀ read over R, two of them isomorphic exactly
when the extensions are (`BiaffineDeformationsTorsor`); read in the
sequence's two layers, the chart classes move by the compatible pairs and
each fibre by regluing (`BiaffineDeformationsTorsorLayers`).

The framework in one line: the charts, the chart modules and the overlap
module sit in place inside A₀₁ and V, one ring map from the base into A₀₁
landing in both charts is the structure map of all three, an extension
carries its lift of t or s as data, and a class lives on the host type U.

## Members

### The definitions

| Member | Statement |
|---|---|
| `biaffineOverlapDerivationsDef` | `biaffine_overlap_derivations(P, h, A₀₁, V, M)`: the derivations of A₀₁ over P into M₀₁, zero off A₀₁, a module over A₀₁ |
| `biaffineDerivationPairDef` | `biaffine_derivation_pair(P, h, A₀₁, A₀, A₁, V, M)`, 𝒟⁰: the derivations of the overlap carrying A₀ into M₀, and those carrying A₁ into M₁ |
| `BiaffineExtensionDef` | `biaffine_extension(P, h, A₀₁, A₀, A₁, t, s, V, M, E₀, t₀, E₁, t₁, φ)`: chart extensions over P with lifts of t and s, φ an isomorphism of their localizations |
| `BiaffineIsomorphismDef` | `biaffine_isomorphism(P, A₀₁, V, M, E, E', ψ₀, ψ₁)`: isomorphisms of the chart extensions whose maps of localizations carry φ to φ' |
| `biaffineShearGluingDef` | `biaffine_shear_gluing(A₀₁, A₁, s, V, M, d, X)`: the split extensions' localizations read in A₀₁ ⋉ M₀₁, sheared by d, read back on chart 1 |
| `biaffineRegluingDef` | `biaffine_regluing(A₀₁, V, M, E₀, t₀, φ, d, x)`: φ after x ↦ x − i(d(p(x))) on E₀ localized |
| `biaffineLocalClassDef` | `biaffine_local_class(P, h, A₀₁, A₀, A₁, V, M, E₀, E₁)`: the pair of the classes of the chart extensions |
| `biaffineCompatibleClassesDef` | `biaffine_compatible_classes(P, h, A₀₁, A₀, A₁, V, M)`: the pairs of chart classes with one restriction to the overlap |
| `biaffineGluingCokernelDef` | `biaffine_gluing_cokernel(P, h, A₀₁, A₀, A₁, V, M)`: D¹(A₀₁/P, M₀₁) modulo the restrictions of the charts' D¹ |
| `BiaffineDeformationDef` | `biaffine_deformation(R, R₀, f, g, A₀₁, A₀, A₁, t, s, V, M, ι, E₀, t₀, E₁, t₁, φ)`: a biaffine extension over R whose chart extensions are deformations with coefficients (M_i, ι) |
| `biaffineLocalObstructionDef` | `biaffine_local_obstruction(R, R₀, f, g, A₀₁, A₀, A₁, V, M, ι)`: the pair of the charts' obstructions ∂¹(ξ) |
| `biaffineGluingObstructionDef` | `biaffine_gluing_obstruction(R, R₀, f, g, A₀₁, A₀, A₁, V, M, ζ₀, ζ₁)`: the class in the gluing cokernel of the δ whose left-map image is res(ζ₀) − res(ζ₁) |
| `biaffineBaerGluingDef` | `biaffine_baer_gluing(A₀₁, V, M, E₀, t₀, E₁, t₁, φ, E₀', t₀', E₁', t₁', φ')`: the gluing of the Baer sum — each localized chart sum read as the Baer sum of the localizations, `φ ⊕ φ'`, read back on chart 1 |
| `biaffineExalClassDef` | `biaffine_exal_class(P, h, A₀₁, A₀, A₁, t, s, V, M, E₀, t₀, E₁, t₁, φ)`: the biaffine extensions on `set(prod(U, D))` isomorphic to the given one |
| `biaffineExalDef` | `biaffine_exal(P, h, A₀₁, A₀, A₁, t, s, V, M)`, Exal: the classes of the biaffine extensions over `P` |
| `biaffineExalSumDef` | `biaffine_exal_sum(…, X, Y)`: the union of the classes of the Baer sums of members of `X` and `Y` |
| `biaffineExalNegDef` | `biaffine_exal_neg(…, X)`: the union of the classes of the members with both inclusions negated |

### The derivation pair

| Member | Statement |
|---|---|
| `DerivationPairIsLattice` | both charts finitely generated over the base ⇒ 𝒟⁰ is a lattice pair in the derivations of the overlap, its ambient all of them — card |
| `ChartDerivationsExtend` | a derivation of a chart extends by the quotient rule to exactly one member of its chart of 𝒟⁰, and every member restricts to one: 𝒟⁰ = (Der(A₀, M₀), Der(A₁, M₁)) — card |

### Extensions glued from the charts

| Member | Statement |
|---|---|
| `GluedTrivialIsExtension` | the split extensions with lifts (t, 0), (s, 0), glued by the shear of a derivation d of the overlap, are a biaffine extension — card |
| `GluedTrivialIsoIffCoboundary` | the split extensions glued by d and by d' are isomorphic ⇔ d − d' ∈ fst(𝒟⁰) + snd(𝒟⁰); for d = d' + d₀ + d₁ the shears by d₀ and −d₁ are an isomorphism — card |
| `LocallyTrivialIsH1D0` | the split extensions have chart classes zero, and every extension with chart classes zero is isomorphic to the split extensions glued by some shear — card |
| `LocalClassLandsInKernel` | the chart classes of a biaffine extension are a compatible pair — card |
| `LocalClassOnto` | chart extensions with lifts whose classes agree on the overlap have a gluing — card |
| `ExalSequence` | every compatible pair is the chart classes of an extension; a reglued extension is one; two with one pair of chart classes differ by a regluing; two regluings are isomorphic ⇔ the derivations differ by fst(𝒟⁰) + snd(𝒟⁰) — card |
| `BiaffineAutomorphisms` | the automorphisms of a biaffine extension are the pairs of shears by a member of H⁰(𝒟⁰), which they determine, composing by the sum — card |
| `ClassModulesOverSubring` | over a subring of both charts the restrictions are linear, the compatible classes a submodule of the product, and they and the gluing cokernel modules — card |

### The group of extensions

| Member | Statement |
|---|---|
| `BiaffineBaerSumIsExtension` | the chartwise Baer sum with the paired lifts and `biaffine_baer_gluing` is a biaffine extension, and so is an extension with both inclusions negated — card |
| `BiaffineExalClassEqIff` | the class of a biaffine extension on any types lies in Exal; two have one class ⇔ they are isomorphic — card |
| `BiaffineExalSumClass` | the sum of the classes of two biaffine extensions is the class of their Baer sum — card |
| `BiaffineExalNegClass` | the negative of a class is the class of the negated extension — card |
| `BiaffineExalGroupOn` | Exal is a group under the sum of classes, unit the class of the split extensions glued by the zero derivation — card |
| `BiaffineExalAbelian` | Exal is an abelian group — card |
| `ExalSequenceExact` | `H¹(𝒟⁰) → Exal`, `d ↦` the class of the shear gluing, is a one-to-one homomorphism; the chart classes map Exal onto the compatible classes; the image of the first is the kernel of the second — card |

### Deformations and the obstruction in two levels

| Member | Statement |
|---|---|
| `ThickeningDerivationsAgree` | f onto ⇒ the derivations of the overlap and 𝒟⁰ over R through g ∘ f are those over R₀ through g — card |
| `LocalDeformationsExistIff` | each chart has a deformation ⇔ the local obstruction is zero; a chart deformation kills its component — card |
| `LocalizedLiftsSameImage` | the restrictions of two chart deformation classes have one image in D¹(R₀/R, M₀₁), and their difference is the left-map image of exactly one δ — card |
| `GluingObstructionWellDefined` | the gluing obstruction is a class of the gluing cokernel and does not depend on the chart deformation classes — card |
| `GluingObstructionZeroIffLift` | the gluing obstruction vanishes ⇔ some chart deformation classes agree on the overlap ⇔ the curve has a deformation — card |
| `BiaffineDeformationTheorem` | a deformation kills both obstructions; with the local one zero, chart deformation classes exist, and a vanishing gluing obstruction gives a deformation — card |
| `CokernelZeroLocalObstructionSuffices` | gluing cokernel zero and local obstruction zero ⇒ the curve has a deformation — card |
| `BiaffineDeformationsTorsor` | the deformations are the Baer sums of one deformation `D` with the biaffine extensions over `R₀` read over `R`; `D ⊕ E' ≅ D ⊕ E''` ⇔ `E' ≅ E''` — card |
| `BiaffineDeformationsTorsorLayers` | the chart classes of the deformations move by exactly one compatible pair over R₀, every pair is reached; each fibre is the regluings of one deformation, two isomorphic ⇔ the derivations differ by fst(𝒟⁰) + snd(𝒟⁰) — card |
| `SmoothChartsUnobstructed` | both charts with no D¹ and D² over R₀ ⇒ both obstructions, the compatible classes and the cokernel vanish, a deformation exists, and the deformations are an H¹(𝒟⁰)-torsor under regluing — card |

### The projective line and the Weierstrass cubic

| Member | Statement |
|---|---|
| `LineChartsSmooth` | t transcendental over k ⇒ the charts k[t] and k[1/t] in the field have Dⁿ = 0 over k for every n ≥ 1 and every coefficient module — card |
| `LineChartsFinitelyGenerated` | k[t] is generated over k by t and k[1/t] by 1/t, as DerivationPairIsLattice asks — card |
| `LineDerivationPair` | on the line, d(1/t) = −t⁻²·d(t), 𝒟⁰ is a lattice pair, and d ↦ d(t) is an isomorphism of lattice pairs from 𝒟⁰ onto O(2) — card |
| `ProjectiveLineRigid` | every extension of the line by O over k is isomorphic to the trivial gluing; over a square-zero thickening of k the line has a deformation, unique up to isomorphism — card |
| `ChartsSmoothOnImage` | 2 ≠ 0 and 4a³ + 27b² ≠ 0 ⇒ both Weierstrass charts in the field have Dⁿ = 0 over k for every n ≥ 1 and every coefficient module — card |
| `WeierstrassChartsFinitelyGenerated` | chart 0 is generated over k by x and y, chart 1 by 1/x and y/x² — card |
| `WeierstrassDerivationPair` | smooth cubic ⇒ the vector field θ (θ(x) = 2y, θ(y) = 3x² + a) lies in H⁰(𝒟⁰), every derivation is $\frac{d(x)}{2y} \cdot \theta$, and $d \mapsto \frac{d(x)}{2y}$ is an isomorphism of lattice pairs from 𝒟⁰ onto O — card |
| `EllipticDeformationsDimOne` | smooth cubic ⇒ the extensions by O are the trivial ones glued by d, isomorphic ⇔ d − d′ ∈ fst(𝒟⁰) + snd(𝒟⁰), dim_k H¹(𝒟⁰) = 1; over a thickening a deformation exists and the deformations are an H¹(𝒟⁰)-torsor under regluing — card |
