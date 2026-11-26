// definitions.go — the chapter's definitional layer. Over a biaffine
// datum (A₀₁, A₀, A₁, t, s) with a lattice pair (V, M) of coefficients:
// the derivations of the overlap into M₀₁ and the derivation pair 𝒟⁰
// inside them; a biaffine extension, two chart extensions with lifts of t
// and s and an isomorphism of their localizations, and the isomorphisms
// between two of them; the split extensions glued by the shear of a
// derivation, and a gluing moved by one; the pair of chart classes, the
// compatible pairs and the cokernel of the restrictions to the overlap.
// Over a thickening R → R₀ with a map ι from its kernel into H⁰(M): the
// biaffine deformations, and their obstruction in two levels.
//
// Everything sits in place. The charts are subsets of the overlap ring
// A₀₁ and the chart modules subsets of the container V, so a chart ring
// is restrict_ring(A₀₁, A₀), a chart module restrict_module(V, fst(M)),
// and the overlap module M₀₁ is V restricted to the ambient of M. A chart
// extension localized at its lift is square_zero_localization with the
// overlap ring and M₀₁ for the localizations and the identities for
// their maps, so the two charts' localizations are extensions of one
// ring by one module. One ring map h from the base P into A₀₁, landing
// in A₀ ∩ A₁, is the structure map of both charts and of the overlap at
// once: the inclusions are then maps of algebras with nothing to check.

package biaffine_deformation

import (
	"github.com/euc-ai/xugo/library/registry"
)

// The chart rings, the chart modules and the overlap module M₀₁, all read
// in place inside A₀₁ and V.
const (
	wg3Chart0  = "restrict_ring(A₀₁, A₀)"
	wg3Chart1  = "restrict_ring(A₀₁, A₁)"
	wg3Module0 = "restrict_module(V, fst(M))"
	wg3Module1 = "restrict_module(V, snd(M))"
	wg3Overlap = "restrict_module(V, lattice_pair_ambient(A₀₁, V, M))"
)

// wg3Localized is the chart extension E, an extension by the chart
// module, with the powers of its lift inverted and read on the overlap in
// place.
func wg3Localized(module, E, lift string) string {
	return "square_zero_localization(" + module + ", A₀₁, λc:C. c, " + wg3Overlap + ", λv:D. v, " + E + ", " + lift + ")"
}

// wg3Fraction is the class of e over v among the fractions of E's ring at
// the powers of the lift.
func wg3Fraction(E, lift, e, v string) string {
	return "fraction_class(" + E + ".ring.mul, " + E + ".ring.carrier, monoid_powers(" + E + ".ring.mul, " + E + ".ring.one, " + lift + "), " + e + ", " + v + ")"
}

// wg3LocalizedMap applies to x the map of localizations that ψ, from a
// chart extension with ring type src to E' with ring type tgt, induces:
// a class with representative (e, v) goes to the quotient ψ(e)/1 by
// ψ(v)/1 in E' localized at its own lift, ψ(v) being a lift of a power of
// t and so a unit there.
func wg3LocalizedMap(ψ, E, lift, module, src, tgt, x string) string {
	L := wg3Localized(module, E, lift)
	return "induced_map(λz:prod(" + src + ", " + src + "). inverse_on(" + L + ".ring.carrier, λy:set(prod(" + tgt + ", " + tgt + ")). " +
		L + ".ring.mul(y, " + wg3Fraction(
		E,
		lift,
		ψ+"(snd(z))",
		E+".ring.one") + "), " + wg3Fraction(E, lift, ψ+"(fst(z))", E+".ring.one") + "), " + x + ")"
}

// wg3ChartClasses are D^1 of each chart over the base P through h, and
// of the overlap; wg3Restriction0 and wg3Restriction1 restrict a class
// of a chart to the overlap, its coefficients carried into M₀₁ by the
// identity.
const (
	wg3ChartClasses0 = "cotangent_cohomology(P, restrict_ring(A₀₁, A₀), " +
		"h, restrict_ring(A₀₁, A₀), λc:C. c, restrict_module(V, fst(M)), 1)"
	wg3ChartClasses1 = "cotangent_cohomology(P, restrict_ring(A₀₁, A₁), " +
		"h, restrict_ring(A₀₁, A₁), λc:C. c, restrict_module(V, snd(M)), 1)"
	wg3OverlapClasses = "cotangent_cohomology(P, A₀₁, h, A₀₁, λc:C. c, " + wg3Overlap + ", 1)"
)

func wg3Restriction0(x string) string {
	return "cotangent_cohomology_restriction(P, restrict_ring(A₀₁, A₀), h, A₀₁, λc:C. c, " + wg3Overlap + ", λv:D. v, 1, " + x + ")"
}

func wg3Restriction1(x string) string {
	return "cotangent_cohomology_restriction(P, restrict_ring(A₀₁, A₁), h, A₀₁, λc:C. c, " + wg3Overlap + ", λv:D. v, 1, " + x + ")"
}

// ---------------------------------------------------------------------------
// The derivation pair
// ---------------------------------------------------------------------------

// biaffineOverlapDerivationsDef — `biaffine_overlap_derivations(P, h,
// A₀₁, V, M)`: the derivations of the overlap ring over P through h into
// M₀₁, zero off the overlap's carrier, as a module over A₀₁ under the
// pointwise operations — the container of the derivation pair.
var biaffineOverlapDerivationsDef = biaffineOverlapDerivationsDefThm{family.Define(registry.DefEntry{
	Name:  "biaffineOverlapDerivationsDef",
	Key:   "prop_e8061ea3a870f2fe",
	Const: "biaffine_overlap_derivations",
	Type: "ring_ops(A) → " +
		"(A → C) → " +
		"ring_ops(C) → " +
		"module_ops(C, D) → " +
		"prod(set(D), set(D)) → " +
		"module_ops(C, C → D)",
	Equations: []string{
		"∀P:ring_ops(A). ∀h:(A → C). ∀A₀₁:ring_ops(C). ∀V:module_ops(C, D). ∀M:prod(set(D), set(D)). biaffine_overlap_derivations(P, h, A₀₁, V, M) = " +
			"mk_module(fun_add⟨D:C⟩(V.add), fun_zero⟨D:C⟩(V.zero), fun_neg⟨D:C⟩(V.neg), fun_smul⟨D:C⟩(V.smul), " +
			"{d:C → D | derivation_on(P, A₀₁, h, " + wg3Overlap + ", d) ∧ (∀y:C. y ∉ A₀₁.carrier ⇒ d(y) = V.zero)})",
	},
	Reading: "Zero off the carrier is what makes a derivation one member and not a " +
		"family of them: derivation_on reads only the carrier, so without it H⁰ of the " +
		"pair would hold every function equal to a derivation there. It is a module over " +
		"A₀₁ when V is one and M₀₁ is a submodule, a multiple a • d keeping the Leibniz " +
		"rule by commutativity. For the deformations P is R₀ through g, or R through g ∘ " +
		"f, which give the same derivations when f is onto (ThickeningDerivationsAgree).",
})}

// biaffineDerivationPairDef — `biaffine_derivation_pair(P, h, A₀₁, A₀,
// A₁, V, M)`, written 𝒟⁰: the derivations of the overlap carrying A₀
// into fst(M), and those carrying A₁ into snd(M) — each chart's
// derivations into its module, read by restriction inside the
// derivations of the overlap.
var biaffineDerivationPairDef = biaffineDerivationPairDefThm{family.Define(registry.DefEntry{
	Name:  "biaffineDerivationPairDef",
	Key:   "prop_b516bf5524024375",
	Const: "biaffine_derivation_pair",
	Type: "ring_ops(A) → " +
		"(A → C) → " +
		"ring_ops(C) → " +
		"set(C) → " +
		"set(C) → " +
		"module_ops(C, D) → " +
		"prod(set(D), set(D)) → " +
		"prod(set(C → D), set(C → D))",
	Equations: []string{
		"∀P:ring_ops(A). " +
			"∀h:(A → C). " +
			"∀A₀₁:ring_ops(C). " +
			"∀A₀ A₁:set(C). " +
			"∀V:module_ops(C, D). " +
			"∀M:prod(set(D), set(D)). " +
			"    biaffine_derivation_pair(P, h, A₀₁, A₀, A₁, V, M) = " +
			"    ({d:C → D | " +
			"            d ∈ biaffine_overlap_derivations(P, h, A₀₁, V, M).carrier ∧ image(d, A₀) ⊆ fst(M)}, " +
			"        {d:C → D | " +
			"            d ∈ biaffine_overlap_derivations(P, h, A₀₁, V, M).carrier ∧ image(d, A₁) ⊆ snd(M)})",
	},
	Reading: "The pair is read by restriction from the overlap, and is (Der(A₀, M₀), Der(A₁, M₁)) " +
		"through the quotient-rule extension, a chart derivation extending to exactly one derivation of " +
		"the overlap (ChartDerivationsExtend). It is a lattice pair in the container when both charts " +
		"are finitely generated (DerivationPairIsLattice); its H⁰ is the derivations of the curve into " +
		"M, its H¹ classifies the extensions that split on each chart (LocallyTrivialIsH1D0).",
	Deps: []registry.EntryLike{biaffineOverlapDerivationsDef},
})}

// ---------------------------------------------------------------------------
// Biaffine extensions and their isomorphisms
// ---------------------------------------------------------------------------

// BiaffineExtensionDef — `biaffine_extension(P, h, A₀₁, A₀, A₁, t, s, V,
// M, E₀, t₀, E₁, t₁, φ)`: E₀ is a square-zero extension of chart 0 by
// fst(M) and E₁ one of chart 1 by snd(M), both over P through h; t₀ in E₀
// lifts t and t₁ in E₁ lifts s; and φ is an isomorphism of extensions
// from E₀ localized at t₀ onto E₁ localized at t₁, both extensions of
// the overlap by M₀₁ over P.
var BiaffineExtensionDef = biaffineExtensionDefThm{family.Define(registry.DefEntry{
	Name:  "BiaffineExtensionDef",
	Key:   "prop_dd32d93353d13387",
	Const: "biaffine_extension",
	Type: "ring_ops(A) → " +
		"(A → C) → " +
		"ring_ops(C) → " +
		"set(C) → " +
		"set(C) → " +
		"C → " +
		"C → " +
		"module_ops(C, D) → " +
		"prod(set(D), set(D)) → " +
		"square_zero_ops(A, C, I, D) → " +
		"I → " +
		"square_zero_ops(A, C, H, D) → " +
		"H → " +
		"(set(prod(I, I)) → set(prod(H, H))) → " +
		"bool",
	Equations: []string{
		"∀P:ring_ops(A). ∀h:(A → C). ∀A₀₁:ring_ops(C). ∀A₀ A₁:set(C). ∀t s:C. ∀V:module_ops(C, D). ∀M:prod(set(D), set(D)). " +
			"∀E₀:square_zero_ops(A, C, I, D). ∀t₀:I. ∀E₁:square_zero_ops(A, C, H, D). ∀t₁:H. ∀φ:(set(prod(I, I)) → set(prod(H, H))). " +
			"biaffine_extension(P, h, A₀₁, A₀, A₁, t, s, V, M, E₀, t₀, E₁, t₁, φ) ⇔ " +
			"biaffine(A₀₁, A₀, A₁, t, s) ∧ lattice_pair(A₀₁, A₀, A₁, V, M) ∧ " +
			"square_zero_extension(P, " + wg3Chart0 + ", h, " + wg3Module0 + ", E₀) ∧ t₀ ∈ E₀.ring.carrier ∧ E₀.projection(t₀) = t ∧ " +
			"square_zero_extension(P, " + wg3Chart1 + ", h, " + wg3Module1 + ", E₁) ∧ t₁ ∈ E₁.ring.carrier ∧ E₁.projection(t₁) = s ∧ " +
			"square_zero_isomorphism(P, " + wg3Overlap + ", " + wg3Localized(
			wg3Module0, "E₀", "t₀") + ", " + wg3Localized(wg3Module1, "E₁", "t₁") + ", φ)",
	},
	Reading: "The lifts are part of the datum because the localization of an extension is " +
		"taken at one element of its ring; another lift gives an isomorphic localization " +
		"(SquareZeroLocalizationIndependent), and biaffine_isomorphism lets the lifts change. " +
		"Both localizations are extensions of A₀₁ by M₀₁ over P because A₀₁ = A₀[1/t] = A₁[1/s] " +
		"in place and M₀₁ is the span of either chart module (BiaffineChartLocalization, " +
		"SpanIsModuleLocalization). A base P whose map h leaves A₀ ∩ A₁ admits no biaffine " +
		"extension: the projection after the structure map is h on P, inside each chart.",
})}

// BiaffineIsomorphismDef — `biaffine_isomorphism(P, A₀₁, V, M, E₀, t₀,
// E₁, t₁, φ, E₀', t₀', E₁', t₁', φ', ψ₀, ψ₁)`: ψ₀ and ψ₁ are isomorphisms
// of the chart extensions over P, E₀ ≅ E₀' and E₁ ≅ E₁', whose maps of
// localizations carry the gluing φ to the gluing φ': φ' ∘ loc(ψ₀) =
// loc(ψ₁) ∘ φ on the localization of E₀.
var BiaffineIsomorphismDef = biaffineIsomorphismDefThm{family.Define(registry.DefEntry{
	Name:  "BiaffineIsomorphismDef",
	Key:   "prop_c4466ca30a283d3e",
	Const: "biaffine_isomorphism",
	Type: "ring_ops(A) → " +
		"ring_ops(C) → " +
		"module_ops(C, D) → " +
		"prod(set(D), set(D)) → " +
		"square_zero_ops(A, C, I, D) → " +
		"I → " +
		"square_zero_ops(A, C, H, D) → " +
		"H → " +
		"(set(prod(I, I)) → set(prod(H, H))) → " +
		"square_zero_ops(A, C, G, D) → " +
		"G → " +
		"square_zero_ops(A, C, F, D) → " +
		"F → " +
		"(set(prod(G, G)) → set(prod(F, F))) → " +
		"(I → G) → " +
		"(H → F) → " +
		"bool",
	Equations: []string{
		"∀P:ring_ops(A). ∀A₀₁:ring_ops(C). ∀V:module_ops(C, D). ∀M:prod(set(D), set(D)). " +
			"∀E₀:square_zero_ops(A, C, I, D). ∀t₀:I. ∀E₁:square_zero_ops(A, C, H, D). ∀t₁:H. ∀φ:(set(prod(I, I)) → set(prod(H, H))). " +
			"∀E₀':square_zero_ops(A, C, G, D). ∀t₀':G. ∀E₁':square_zero_ops(A, C, F, D). ∀t₁':F. ∀φ':(set(prod(G, G)) → set(prod(F, F))). ∀ψ₀:(I → G). ∀ψ₁:(H → F). " +
			"biaffine_isomorphism(P, A₀₁, V, M, E₀, t₀, E₁, t₁, φ, E₀', t₀', E₁', t₁', φ', ψ₀, ψ₁) ⇔ " +
			"square_zero_isomorphism(P, " + wg3Module0 + ", E₀, E₀', ψ₀) ∧ square_zero_isomorphism(P, " + wg3Module1 + ", E₁, E₁', ψ₁) ∧ " +
			"(∀x:set(prod(I, I)). x ∈ " + wg3Localized(wg3Module0, "E₀", "t₀") + ".ring.carrier ⇒ " +
			"φ'(" + wg3LocalizedMap("ψ₀", "E₀'", "t₀'", wg3Module0, "I", "G", "x") + ") = " +
			wg3LocalizedMap("ψ₁", "E₁'", "t₁'", wg3Module1, "H", "F", "φ(x)") + ")",
	},
	Reading: "The lifts may change: ψ₀(t₀) need not be t₀', so the map of localizations divides " +
		"by ψ₀(v)/1 in the localization at t₀', where it is a unit, ψ₀(t₀) − t₀' lying in the " +
		"square-zero kernel. Read on a class e/v it is ψ(e)/1 times the inverse of ψ(v)/1, whatever " +
		"representative induced_map picks, since related representatives stay related under ψ. The " +
		"first extension's lift t₁ is not read: φ(x) is already a class at the powers of t₁, and the " +
		"map of localizations reads it through a representative. ψ₀(t₀) = t₀' + i(n) is a unit at t₀' " +
		"by UnitPlusSquareZeroIsUnit, which is what makes the map of localizations a ring map.",
})}

// ---------------------------------------------------------------------------
// The split extensions glued by a shear, and a gluing moved by one
// ---------------------------------------------------------------------------

// biaffineShearGluingDef — `biaffine_shear_gluing(A₀₁, A₁, s, V, M, d,
// X)`: the gluing of the split extensions A₀ ⋉ M₀ and A₁ ⋉ M₁, localized
// at (t, 0) and (s, 0), by the shear of the derivation d of the overlap —
// a class X of fractions read in A₀₁ ⋉ M₀₁, sheared, (u, n) ↦ (u, n −
// d(u)), and read back among chart 1's fractions.
var biaffineShearGluingDef = biaffineShearGluingDefThm{family.Define(registry.DefEntry{
	Name:  "biaffineShearGluingDef",
	Key:   "prop_aa2a1776e1e8b870",
	Const: "biaffine_shear_gluing",
	Type: "ring_ops(C) → " +
		"set(C) → " +
		"C → " +
		"module_ops(C, D) → " +
		"prod(set(D), set(D)) → " +
		"(C → D) → " +
		"set(prod(prod(C, D), prod(C, D))) → " +
		"set(prod(prod(C, D), prod(C, D)))",
	Equations: []string{
		"∀A₀₁:ring_ops(C). " +
			"∀A₁:set(C). " +
			"∀s:C. " +
			"∀V:module_ops(C, D). " +
			"∀M:prod(set(D), set(D)). " +
			"∀d:(C → D). " +
			"∀X:set(prod(prod(C, D), prod(C, D))). " +
			"    biaffine_shear_gluing(A₀₁, A₁, s, V, M, d, X) = " +
			"    inverse_on(ring_localization( " +
			"            split_square_zero(restrict_ring(A₀₁, A₁), λy:C. y, restrict_module(V, snd(M))).mul, " +
			"            split_square_zero(restrict_ring(A₀₁, A₁), " +
			"                λy:C. y, " +
			"                restrict_module(V, snd(M))).carrier, " +
			"            monoid_powers(split_square_zero(restrict_ring(A₀₁, A₁), " +
			"                    λy:C. y, " +
			"                    restrict_module(V, snd(M))).mul, " +
			"                split_square_zero(restrict_ring(A₀₁, A₁), " +
			"                    λy:C. y, " +
			"                    restrict_module(V, snd(M))).one, " +
			"                (s, V.zero))), " +
			"        λY:set(prod(prod(C, D), prod(C, D))). " +
			"            induced_map(λz:prod(prod(C, D), prod(C, D)).( " +
			"                    inverse_on(A₀₁.carrier, λy:C. A₀₁.mul(y, fst(snd(z))), fst(fst(z))), " +
			"                    inverse_on(lattice_pair_ambient(A₀₁, V, M), " +
			"                        λm:D. V.smul(fst(snd(z)), m), " +
			"                        snd(fst(z)))), " +
			"                Y), " +
			"        derivation_shear(restrict_module(V, lattice_pair_ambient(A₀₁, V, M)), " +
			"            d, " +
			"            induced_map(λz:prod(prod(C, D), prod(C, D)).( " +
			"                    inverse_on(A₀₁.carrier, λy:C. A₀₁.mul(y, fst(snd(z))), fst(fst(z))), " +
			"                    inverse_on(lattice_pair_ambient(A₀₁, V, M), " +
			"                        λm:D. V.smul(fst(snd(z)), m), " +
			"                        snd(fst(z)))), " +
			"                X)))",
	},
	Reading: "The reading of a class in A₀₁ ⋉ M₀₁ is the isomorphism of " +
		"SplitSquareZeroLocalization, the same formula at either chart; chart 0 enters only through X, " +
		"which is why its data are not arguments. At d = 0 it is the trivial gluing, the identification " +
		"of both localized split extensions with A₀₁ ⋉ M₀₁; for d a derivation of the overlap over the " +
		"base the shear fixes the structure map and M₀₁, so the gluing is an isomorphism of extensions " +
		"(GluedTrivialIsExtension). Off the localization of chart 0 the value is never read.",
})}

// biaffineRegluingDef — `biaffine_regluing(A₀₁, V, M, E₀, t₀, φ, d, x)`:
// the gluing φ moved by the derivation d of the overlap — φ after the
// automorphism x ↦ x − i(d(p(x))) of E₀ localized at t₀.
var biaffineRegluingDef = biaffineRegluingDefThm{family.Define(registry.DefEntry{
	Name:  "biaffineRegluingDef",
	Key:   "prop_adbf7ace229074b7",
	Const: "biaffine_regluing",
	Type: "ring_ops(C) → " +
		"module_ops(C, D) → " +
		"prod(set(D), set(D)) → " +
		"square_zero_ops(A, C, I, D) → " +
		"I → " +
		"(set(prod(I, I)) → set(prod(H, H))) → " +
		"(C → D) → " +
		"set(prod(I, I)) → " +
		"set(prod(H, H))",
	Equations: []string{
		"∀A₀₁:ring_ops(C). ∀V:module_ops(C, D). ∀M:prod(set(D), set(D)). ∀E₀:square_zero_ops(A, C, I, D). ∀t₀:I. ∀φ:(set(prod(I, I)) → set(prod(H, H))). ∀d:(C → D). ∀x:set(prod(I, I)). " +
			"biaffine_regluing(A₀₁, V, M, E₀, t₀, φ, d, x) = φ(" + wg3Localized(
			wg3Module0, "E₀", "t₀") + ".ring.sub(x, " + wg3Localized(wg3Module0, "E₀", "t₀") + ".inclusion(d(" +
			wg3Localized(wg3Module0, "E₀", "t₀") + ".projection(x)))))",
	},
	Reading: "The sign is the shear's, (u, n) ↦ (u, n − d(u)), so the split extensions " +
		"glued by biaffine_shear_gluing at d are those glued at zero moved by d. For d a " +
		"derivation of the overlap over the base the automorphism is over the base, the identity " +
		"on M₀₁ and over A₀₁, so a moved gluing is again a gluing (ExalSequence); an isomorphism " +
		"of extensions commutes with it, which is why the side it is applied on does not matter.",
})}

// ---------------------------------------------------------------------------
// The chart classes
// ---------------------------------------------------------------------------

// biaffineLocalClassDef — `biaffine_local_class(P, h, A₀₁, A₀, A₁, V, M,
// E₀, E₁)`: the pair of the classes of the chart extensions, in D^1 of
// chart 0 over P with coefficients fst(M) and in D^1 of chart 1 with
// coefficients snd(M).
var biaffineLocalClassDef = biaffineLocalClassDefThm{family.Define(registry.DefEntry{
	Name:  "biaffineLocalClassDef",
	Key:   "prop_d6271b11341704f5",
	Const: "biaffine_local_class",
	Type: "ring_ops(A) → " +
		"(A → C) → " +
		"ring_ops(C) → " +
		"set(C) → " +
		"set(C) → " +
		"module_ops(C, D) → " +
		"prod(set(D), set(D)) → " +
		"square_zero_ops(A, C, I, D) → " +
		"square_zero_ops(A, C, H, D) → " +
		"prod(set(U → D), set(U → D))",
	Equations: []string{
		"∀P:ring_ops(A). ∀h:(A → C). ∀A₀₁:ring_ops(C). ∀A₀ A₁:set(C). ∀V:module_ops(C, D). ∀M:prod(set(D), set(D)). ∀E₀:square_zero_ops(A, C, I, D). ∀E₁:square_zero_ops(A, C, H, D). " +
			"biaffine_local_class(P, h, A₀₁, A₀, A₁, V, M, E₀, E₁) = (square_zero_class(P, " + wg3Chart0 + ", h, " + wg3Module0 + ", E₀), square_zero_class(P, " + wg3Chart1 + ", h, " + wg3Module1 + ", E₁))",
	},
	Reading: "Neither the lifts nor the gluing is read: the pair is what the extension " +
		"is on each chart, and the gluing is what the pair forgets (ExalSequence). The letter " +
		"U is the host's, fixed by the universe hypotheses of the statements that read it.",
})}

// biaffineCompatibleClassesDef — `biaffine_compatible_classes(P, h,
// A₀₁, A₀, A₁, V, M)`: the pairs of a class of chart 0 and a class of
// chart 1 with one restriction to the overlap — the kernel of res₀ − res₁
// from D^1(A₀/P, M₀) × D^1(A₁/P, M₁) to D^1(A₀₁/P, M₀₁), with the
// componentwise operations.
var biaffineCompatibleClassesDef = biaffineCompatibleClassesDefThm{family.Define(registry.DefEntry{
	Name:  "biaffineCompatibleClassesDef",
	Key:   "prop_9e2b8b6bcaa64fc3",
	Const: "biaffine_compatible_classes",
	Type: "ring_ops(A) → " +
		"(A → C) → " +
		"ring_ops(C) → " +
		"set(C) → " +
		"set(C) → " +
		"module_ops(C, D) → " +
		"prod(set(D), set(D)) → " +
		"module_ops(C, prod(set(U → D), set(U → D)))",
	Equations: []string{
		"∀P:ring_ops(A). ∀h:(A → C). ∀A₀₁:ring_ops(C). ∀A₀ A₁:set(C). ∀V:module_ops(C, D). ∀M:prod(set(D), set(D)). " +
			"biaffine_compatible_classes(P, h, A₀₁, A₀, A₁, V, M) = restrict_module(product_module(" + wg3ChartClasses0 + ", " + wg3ChartClasses1 + "), " +
			"{z:prod(set(U → D), set(U → D)) | fst(z) ∈ " + wg3ChartClasses0 + ".carrier ∧ snd(z) ∈ " + wg3ChartClasses1 + ".carrier ∧ " +
			wg3Restriction0("fst(z)") + " = " + wg3Restriction1("snd(z)") + "})",
	},
	Reading: "H⁰ of the local D¹: the chart classes that agree on the overlap, where every " +
		"biaffine extension's pair of classes lies (LocalClassLandsInKernel) and which every such " +
		"pair reaches (ExalSequence). The restriction is cotangent_cohomology_restriction, the " +
		"coefficient map into M₀₁ followed by the inverse of the right map of P → A_i → A₀₁: D¹ " +
		"is contravariant in the algebra, so no map runs from a chart to the overlap otherwise. " +
		"It is a module over any subring of both charts (ClassModulesOverSubring), not over A₀₁.",
})}

// biaffineGluingCokernelDef — `biaffine_gluing_cokernel(P, h, A₀₁, A₀,
// A₁, V, M)`: D^1(A₀₁/P, M₀₁) modulo the sum of the restrictions of the
// classes of the two charts — the cokernel of res₀ − res₁, where the
// gluing obstruction lives.
var biaffineGluingCokernelDef = biaffineGluingCokernelDefThm{family.Define(registry.DefEntry{
	Name:  "biaffineGluingCokernelDef",
	Key:   "prop_5a91d40fa4bd6e09",
	Const: "biaffine_gluing_cokernel",
	Type: "ring_ops(A) → " +
		"(A → C) → " +
		"ring_ops(C) → " +
		"set(C) → " +
		"set(C) → " +
		"module_ops(C, D) → " +
		"prod(set(D), set(D)) → " +
		"module_ops(C, set(set(U → D)))",
	Equations: []string{
		"∀P:ring_ops(A). ∀h:(A → C). ∀A₀₁:ring_ops(C). ∀A₀ A₁:set(C). ∀V:module_ops(C, D). ∀M:prod(set(D), set(D)). " +
			"biaffine_gluing_cokernel(P, h, A₀₁, A₀, A₁, V, M) = quotient_module(" + wg3OverlapClasses + ", set_mul(" + wg3OverlapClasses + ".add, " +
			"image(λx:set(U → D). " + wg3Restriction0(
			"x") + ", " + wg3ChartClasses0 + ".carrier), image(λx:set(U → D). " + wg3Restriction1(
			"x") + ", " + wg3ChartClasses1 + ".carrier)))",
	},
	Reading: "H¹ of the local D¹, as the lattice pair's H¹ is its ambient modulo M₀ + M₁. Its " +
		"zero is the sum of the two images itself, the zero of a quotient module. It vanishes when " +
		"D¹(A₀₁/P, M₀₁) does, which a chart smooth over P forces (SmoothChartsUnobstructed); then a " +
		"deformation exists as soon as each chart has one (CokernelZeroLocalObstructionSuffices).",
})}

// ---------------------------------------------------------------------------
// Deformations and their obstruction
// ---------------------------------------------------------------------------

// BiaffineDeformationDef — `biaffine_deformation(R, R₀, f, g, A₀₁, A₀,
// A₁, t, s, V, M, ι, E₀, t₀, E₁, t₁, φ)`: a deformation of the biaffine
// curve over R₀ to the thickening R — a biaffine extension over R through
// g ∘ f whose chart extensions are deformations of the charts with
// coefficients the chart modules and the map ι from the kernel of f.
var BiaffineDeformationDef = biaffineDeformationDefThm{family.Define(registry.DefEntry{
	Name:  "BiaffineDeformationDef",
	Key:   "prop_83212ab8223e2a51",
	Const: "biaffine_deformation",
	Type: "ring_ops(A) → " +
		"ring_ops(B) → " +
		"(A → B) → " +
		"(B → C) → " +
		"ring_ops(C) → " +
		"set(C) → " +
		"set(C) → " +
		"C → " +
		"C → " +
		"module_ops(C, D) → " +
		"prod(set(D), set(D)) → " +
		"(A → D) → " +
		"square_zero_ops(A, C, I, D) → " +
		"I → " +
		"square_zero_ops(A, C, H, D) → " +
		"H → " +
		"(set(prod(I, I)) → set(prod(H, H))) → " +
		"bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀R₀:ring_ops(B). ∀f:(A → B). ∀g:(B → C). ∀A₀₁:ring_ops(C). ∀A₀ A₁:set(C). ∀t s:C. ∀V:module_ops(C, D). ∀M:prod(set(D), set(D)). ∀ι:(A → D). " +
			"∀E₀:square_zero_ops(A, C, I, D). ∀t₀:I. ∀E₁:square_zero_ops(A, C, H, D). ∀t₁:H. ∀φ:(set(prod(I, I)) → set(prod(H, H))). " +
			"biaffine_deformation(R, R₀, f, g, A₀₁, A₀, A₁, t, s, V, M, ι, E₀, t₀, E₁, t₁, φ) ⇔ " +
			"biaffine_extension(R, λa:A. g(f(a)), A₀₁, A₀, A₁, t, s, V, M, E₀, t₀, E₁, t₁, φ) ∧ " +
			"algebra_deformation(R, R₀, f, " + wg3Chart0 + ", g, " + wg3Module0 + ", ι, E₀) ∧ algebra_deformation(R, R₀, f, " + wg3Chart1 + ", g, " + wg3Module1 + ", ι, E₁)",
	},
	Reading: "The gluing is an isomorphism over R of the localized chart deformations, and asks " +
		"nothing more of the kernel J: each localization is a deformation of A₀₁ with coefficients " +
		"(M₀₁, ι) (DeformationLocalizes), and an isomorphism over R carries E₀.structure(j)/1 = " +
		"i(ι(j)) to the same equation on the other side. ι is one map for both charts, from J into " +
		"H⁰(M) = M₀ ∩ M₁ in the statements; with M the pair J ⊗_{R₀} (A₀, A₁) and ι(j) = j ⊗ 1, and " +
		"both charts flat over R₀, a deformation is a flat curve over R lifting the curve over R₀.",
	Deps: []registry.EntryLike{BiaffineExtensionDef},
})}

// biaffineLocalObstructionDef — `biaffine_local_obstruction(R, R₀, f,
// g, A₀₁, A₀, A₁, V, M, ι)`: the pair of the obstructions ∂¹(ξ) to
// deforming each chart, in D^2(A₀/R₀, M₀) and D^2(A₁/R₀, M₁).
var biaffineLocalObstructionDef = biaffineLocalObstructionDefThm{family.Define(registry.DefEntry{
	Name:  "biaffineLocalObstructionDef",
	Key:   "prop_344453c7317a44e2",
	Const: "biaffine_local_obstruction",
	Type: "ring_ops(A) → " +
		"ring_ops(B) → " +
		"(A → B) → " +
		"(B → C) → " +
		"ring_ops(C) → " +
		"set(C) → " +
		"set(C) → " +
		"module_ops(C, D) → " +
		"prod(set(D), set(D)) → " +
		"(A → D) → " +
		"prod(set(U → D), set(U → D))",
	Equations: []string{
		"∀R:ring_ops(A). ∀R₀:ring_ops(B). ∀f:(A → B). ∀g:(B → C). ∀A₀₁:ring_ops(C). ∀A₀ A₁:set(C). ∀V:module_ops(C, D). ∀M:prod(set(D), set(D)). ∀ι:(A → D). " +
			"biaffine_local_obstruction(R, R₀, f, g, A₀₁, A₀, A₁, V, M, ι) = (algebra_deformation_obstruction(R, R₀, f, " + wg3Chart0 + ", g, " + wg3Module0 + ", ι), " +
			"algebra_deformation_obstruction(R, R₀, f, " + wg3Chart1 + ", g, " + wg3Module1 + ", ι))",
	},
	Reading: "The first level of the obstruction, one class in D² of each chart over R₀; " +
		"it vanishes exactly when each chart has a deformation (LocalDeformationsExistIff), " +
		"whatever the overlap does. Each component is the connecting map of the chart's tower " +
		"R → R₀ → A_i at the thickening class, and lies in D² of the chart over R₀.",
})}

// biaffineGluingObstructionDef — `biaffine_gluing_obstruction(R, R₀, f,
// g, A₀₁, A₀, A₁, V, M, ζ₀, ζ₁)`: for classes ζ₀ and ζ₁ of deformations
// of the two charts, the class in the gluing cokernel over R₀ of the δ in
// D^1(A₀₁/R₀, M₀₁) whose image in D^1(A₀₁/R, M₀₁) is res(ζ₀) − res(ζ₁).
var biaffineGluingObstructionDef = biaffineGluingObstructionDefThm{family.Define(registry.DefEntry{
	Name:  "biaffineGluingObstructionDef",
	Key:   "prop_567debf187651add",
	Const: "biaffine_gluing_obstruction",
	Type: "ring_ops(A) → " +
		"ring_ops(B) → " +
		"(A → B) → " +
		"(B → C) → " +
		"ring_ops(C) → " +
		"set(C) → " +
		"set(C) → " +
		"module_ops(C, D) → " +
		"prod(set(D), set(D)) → " +
		"set(U → D) → " +
		"set(U → D) → " +
		"set(set(U → D))",
	Equations: []string{
		"∀R:ring_ops(A). ∀R₀:ring_ops(B). ∀f:(A → B). ∀g:(B → C). ∀A₀₁:ring_ops(C). ∀A₀ A₁:set(C). ∀V:module_ops(C, D). ∀M:prod(set(D), set(D)). ∀ζ₀ ζ₁:set(U → D). " +
			"biaffine_gluing_obstruction(R, R₀, f, g, A₀₁, A₀, A₁, V, M, ζ₀, ζ₁) = left_coset(" + wg3OverlapOverReduced + ".add, " +
			"inverse_on(" + wg3OverlapOverReduced + ".carrier, co_transitivity_left_map(R, R₀, f, A₀₁, g, " + wg3Overlap + ", 1), " +
			wg3OverlapOverThickening + ".add(" + wg3ThickeningRestriction0(
			"ζ₀") + ", " + wg3OverlapOverThickening + ".neg(" + wg3ThickeningRestriction1("ζ₁") + "))), " +
			"biaffine_gluing_cokernel(R₀, g, A₀₁, A₀, A₁, V, M).zero)",
	},
	Reading: "The second level. Deformations of the charts localize to deformations of " +
		"the overlap, whose classes have one image ξ in D¹(R₀/R, M₀₁), so their difference is " +
		"the left map's image of exactly one δ (LocalizedLiftsSameImage), the left map being " +
		"injective as f is onto. Choosing other chart deformations moves δ by res₀(η₀) − " +
		"res₁(η₁), so the class does not move (GluingObstructionWellDefined). The arguments " +
		"are classes, not extensions, so that a statement can quantify over them on the host " +
		"type. On classes that are not deformation classes the value is a choice nothing reads.",
	Deps: []registry.EntryLike{biaffineGluingCokernelDef},
})}

// The overlap's D^1 over R₀ through g and over R through g ∘ f, with
// coefficients M₀₁, and the restrictions over R of a class of each chart.
const (
	wg3OverlapOverReduced    = "cotangent_cohomology(R₀, A₀₁, g, A₀₁, λc:C. c, " + wg3Overlap + ", 1)"
	wg3OverlapOverThickening = "cotangent_cohomology(R, A₀₁, λa:A. g(f(a)), A₀₁, λc:C. c, " + wg3Overlap + ", 1)"
)

func wg3ThickeningRestriction0(x string) string {
	return "cotangent_cohomology_restriction(R, restrict_ring(A₀₁, A₀), λa:A. g(f(a)), A₀₁, λc:C. c, " + wg3Overlap + ", λv:D. v, 1, " + x + ")"
}

func wg3ThickeningRestriction1(x string) string {
	return "cotangent_cohomology_restriction(R, restrict_ring(A₀₁, A₁), λa:A. g(f(a)), A₀₁, λc:C. c, " + wg3Overlap + ", λv:D. v, 1, " + x + ")"
}
