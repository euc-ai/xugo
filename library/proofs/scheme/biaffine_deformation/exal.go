// exal.go — the group of extensions of a curve held by two charts. Two
// biaffine extensions are added chart by chart by the Baer sum, the lifts
// paired, and glued by the two gluings read through the localization of
// a Baer sum; a biaffine extension is negated by negating both
// inclusions. The isomorphism classes, each a set of biaffine extensions
// on the realizations' type, are an abelian group under the sum of
// classes, its unit the class of the split extensions glued by the zero
// derivation. Its group form of the exact sequence: H¹(𝒟⁰), the
// derivations of the overlap modulo those of the two charts, embeds by
// the shear gluings, and the chart classes map onto the compatible pairs
// with that image as kernel.

package biaffine_deformation

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/algebra_deformation"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/square_zero_classification"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_localization"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/square_zero_extension"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The spelling of the Baer sum of two biaffine extensions
// ---------------------------------------------------------------------------

// baerAntidiagonal spells the pairs (i(m), −i'(m)) for m in N's carrier
// that the Baer sum of X and Y divides their fiber product by; baerClass
// is the class of the pair z in that Baer sum.
func baerAntidiagonal(N, X, Y string) string {
	return "image(λm:D. (" + X + ".inclusion(m), " + Y + ".ring.neg(" + Y + ".inclusion(m))), " + N + ".carrier)"
}

func baerClass(N, X, Y, z string) string {
	return "ideal_quotient_projection(square_zero_fiber_product(" + X + ", " + Y + "), " + baerAntidiagonal(
		N, X, Y) + ", " + z + ")"
}

// baerFraction is the class of e over the k-th power of the lift u among
// the fractions of X's ring at the powers of u.
func baerFraction(X, u, e, k string) string {
	return "fraction_class(" + X + ".ring.mul, " + X + ".ring.carrier, monoid_powers(" + X + ".ring.mul, " + X + ".ring.one, " + u + "), " + e + ", " +
		"monoid_pow(" + X + ".ring.mul, " + X + ".ring.one, " + u + ", " + k + "))"
}

// baerLocalizedReading reads the class W of fractions of the Baer sum of
// the chart extensions X and Y by module, at the powers of the lift
// [(u, v)], in the Baer sum of their localizations on the overlap: the
// map of BaerSumLocalizes in place: the union of the classes of
// (e/uᵏ, e'/vᵏ) over the representations ([(e, e')], [(u, v)]ᵏ) of W
// with e and e' in their rings' carriers. src and src2 are the types of
// X's and Y's rings.
func baerLocalizedReading(module, X, u, Y, v, src, src2, W string) string {
	sum := "square_zero_baer_sum(" + module + ", " + X + ", " + Y + ")"
	lift := baerClass(module, X, Y, "("+u+", "+v+")")
	return "⋃{" + baerClass(
		wg3Overlap,
		wg3Localized(module, X, u),
		wg3Localized(module, Y, v),
		"("+baerFraction(X, u, "e", "k")+", "+baerFraction(Y, v, "e'", "k")+")") +
		" | e:" + src + ", e':" + src2 + ", k:num | e ∈ " + X + ".ring.carrier ∧ e' ∈ " + Y + ".ring.carrier ∧ " +
		"(" + baerClass(
		module,
		X,
		Y,
		"(e, e')") + ", monoid_pow(" + sum + ".ring.mul, " + sum + ".ring.one, " + lift + ", k)) ∈ " + W + "}"
}

// baerGlued spells the Baer sum of the biaffine extensions with parts a
// and b, each (E₀, t₀, E₁, t₁, φ), as its five parts: the Baer sums of the
// charts, the classes of the paired lifts, and biaffine_baer_gluing.
func baerGlued(a, b [5]string) string {
	return "square_zero_baer_sum(" + wg3Module0 + ", " + a[0] + ", " + b[0] + "), " + baerClass(
		wg3Module0, a[0], b[0], "("+a[1]+", "+b[1]+")") + ", " +
		"square_zero_baer_sum(" + wg3Module1 + ", " + a[2] + ", " + b[2] + "), " + baerClass(
		wg3Module1, a[2], b[2], "("+a[3]+", "+b[3]+")") + ", " +
		"biaffine_baer_gluing(A₀₁, V, M, " + a[0] + ", " + a[1] + ", " + a[2] + ", " + a[3] + ", " + a[4] + ", " + b[0] + ", " + b[1] + ", " + b[2] + ", " + b[3] + ", " + b[4] + ")"
}

// baerNegated is the chart extension X with its inclusion negated;
// baerNegatedGlued negates both chart extensions of a, keeping the lifts
// and the gluing.
func baerNegated(X string) string {
	return "mk_square_zero(" + X + ".ring, " + X + ".structure, λn:D. " + X + ".ring.neg(" + X + ".inclusion(n)), " + X + ".projection)"
}

func baerNegatedGlued(a [5]string) string {
	return baerNegated(a[0]) + ", " + a[1] + ", " + baerNegated(a[2]) + ", " + a[3] + ", " + a[4]
}

// The parts of the first and the second biaffine extension, as wg3First
// and wg3Second spell them.
var (
	baerFirst  = [5]string{"E₀", "t₀", "E₁", "t₁", "φ"}
	baerSecond = [5]string{"E₀'", "t₀'", "E₁'", "t₁'", "φ'"}
)

// ---------------------------------------------------------------------------
// The spelling of the classes
// ---------------------------------------------------------------------------

// The realizations' type set(prod(U, D)) as a chart ring, the ring of a
// localization of such a chart, the extension record there, and a
// biaffine extension there: the five parts, nested to the right.
const (
	baerHost      = "set(prod(U, D))"
	baerHostLocal = "set(prod(set(prod(U, D)), set(prod(U, D))))"
	baerHostChart = "square_zero_ops(A, C, set(prod(U, D)), D)"
	baerTuple     = "prod(" + baerHostChart + ", prod(" + baerHost + ", prod(" + baerHostChart + ", prod(" + baerHost + ", (" + baerHostLocal + " → " + baerHostLocal + ")))))"
)

// baerHostParts binds the five parts of a biaffine extension on the
// realizations' type under the names a, in a comprehension's binder list.
func baerHostParts(a [5]string) string {
	return a[0] + ":" + baerHostChart + ", " + a[1] + ":" + baerHost + ", " + a[2] + ":" + baerHostChart + ", " + a[3] + ":" + baerHost + ", " +
		a[4] + ":(" + baerHostLocal + " → " + baerHostLocal + ")"
}

func baerTupleOf(a [5]string) string {
	return "(" + a[0] + ", " + a[1] + ", " + a[2] + ", " + a[3] + ", " + a[4] + ")"
}

func baerPartsOf(a [5]string) string {
	return a[0] + ", " + a[1] + ", " + a[2] + ", " + a[3] + ", " + a[4]
}

// The members of two classes in a comprehension.
var (
	baerMemberX = [5]string{"X₀", "u₀", "X₁", "u₁", "χ"}
	baerMemberY = [5]string{"Y₀", "v₀", "Y₁", "v₁", "ω"}
)

// baerExalClass is the class of the biaffine extension glued over the
// base P through h, its members on set(prod(U, D)); baerExal is the set
// of classes over P.
func baerExalClass(P, h, glued string) string {
	return "biaffine_exal_class⟨U:U⟩(" + P + ", " + h + ", A₀₁, A₀, A₁, t, s, V, M, " + glued + ")"
}

func baerExal(P, h string) string {
	return "biaffine_exal(" + P + ", " + h + ", A₀₁, A₀, A₁, t, s, V, M)"
}

// ---------------------------------------------------------------------------
// The Baer sum of biaffine extensions and the classes
// ---------------------------------------------------------------------------

// biaffineBaerGluingDef — `biaffine_baer_gluing(A₀₁, V, M, E₀, t₀, E₁,
// t₁, φ, E₀', t₀', E₁', t₁', φ', x)`: the gluing of the Baer sum of two
// biaffine extensions — a class x of fractions of the chart-0 Baer sum at
// the lift [(t₀, t₀')] read in the Baer sum of the localizations, sent by
// φ and φ' componentwise, and read back among the fractions of the
// chart-1 Baer sum at [(t₁, t₁')].
var biaffineBaerGluingDef = biaffineBaerGluingDefThm{family.Define(registry.DefEntry{
	Name:  "biaffineBaerGluingDef",
	Key:   "prop_b28509df62e812e1",
	Const: "biaffine_baer_gluing",
	Type: "ring_ops(C) → " +
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
		"set(prod(set(prod(I, G)), set(prod(I, G)))) → " +
		"set(prod(set(prod(H, F)), set(prod(H, F))))",
	Equations: []string{
		"∀A₀₁:ring_ops(C). ∀V:module_ops(C, D). ∀M:prod(set(D), set(D)). " + wg3Glued + wg3GluedOther + "∀x:set(prod(set(prod(I, G)), set(prod(I, G)))). " +
			"biaffine_baer_gluing(A₀₁, V, M, " + wg3First + ", " + wg3Second + ", x) = inverse_on(" +
			wg3Localized(
				wg3Module1,
				"square_zero_baer_sum("+wg3Module1+", E₁, E₁')",
				baerClass(wg3Module1, "E₁", "E₁'", "(t₁, t₁')")) + ".ring.carrier, " +
			"λW:set(prod(set(prod(H, F)), set(prod(H, F)))). " + baerLocalizedReading(
			wg3Module1, "E₁", "t₁", "E₁'", "t₁'", "H", "F", "W") + ", " +
			"induced_map(λz:prod(set(prod(I, I)), set(prod(G, G))). " +
			baerClass(
				wg3Overlap,
				wg3Localized(wg3Module1, "E₁", "t₁"),
				wg3Localized(wg3Module1, "E₁'", "t₁'"),
				"(φ(fst(z)), φ'(snd(z)))") + ", " +
			baerLocalizedReading(wg3Module0, "E₀", "t₀", "E₀'", "t₀'", "I", "G", "x") + "))",
	},
	Reading: "Each localized Baer sum is read as the Baer sum of the localizations by the " +
		"isomorphism of BaerSumLocalizes in place, the overlap A₀₁ and M₀₁ for the localizations " +
		"and the identities for their maps; the two gluings then act componentwise, the " +
		"isomorphism BaerSumIsomorphism writes, and the reading on chart 1 is undone by " +
		"inverse_on. Off the localization of the chart-0 sum the value is a choice nothing " +
		"reads. The lifts of the sum are the classes [(t₀, t₀')] and [(t₁, t₁')], over t and s.",
})}

// biaffineExalClassDef — `biaffine_exal_class(P, h, A₀₁, A₀, A₁, t, s,
// V, M, E₀, t₀, E₁, t₁, φ)`: the class of a biaffine extension — the
// biaffine extensions on the realizations' type set(prod(U, D)) that are
// isomorphic to it.
var biaffineExalClassDef = biaffineExalClassDefThm{family.Define(registry.DefEntry{
	Name:  "biaffineExalClassDef",
	Key:   "prop_c02e2dbb7389c886",
	Const: "biaffine_exal_class",
	Type: "ring_ops(A) → (A → C) → ring_ops(C) → set(C) → set(C) → C → C → module_ops(C, D) → prod(set(D), set(D)) → " +
		"square_zero_ops(A, C, I, D) → I → square_zero_ops(A, C, H, D) → H → (set(prod(I, I)) → set(prod(H, H))) → set(" + baerTuple + ")",
	Equations: []string{
		"∀P:ring_ops(A). ∀h:(A → C). ∀A₀₁:ring_ops(C). ∀A₀ A₁:set(C). ∀t s:C. ∀V:module_ops(C, D). ∀M:prod(set(D), set(D)). " + wg3Glued +
			"biaffine_exal_class(P, h, A₀₁, A₀, A₁, t, s, V, M, " + wg3First + ") = {" + baerTupleOf(
			baerMemberX) + ":" + baerTuple + " | " + baerHostParts(baerMemberX) + " | " +
			wg3Extension(
				"P",
				"h",
				baerPartsOf(baerMemberX)) + " ∧ (∃ψ₀:(I → " + baerHost + "). ∃ψ₁:(H → " + baerHost + "). " +
			wg3Isomorphism("P", wg3First, baerPartsOf(baerMemberX), "ψ₀", "ψ₁") + ")}",
	},
	Reading: "A class is a set of 5-tuples on one type, as curve_pair_class is a set " +
		"of pairs: the extension it is the class of may sit on any types, its members on " +
		"set(prod(U, D)). It is never empty for a biaffine extension once U is a universe " +
		"for the base, the charts and the overlap (BiaffineExalClassEqIff): every extension " +
		"is isomorphic to a regluing of the realizations of its chart classes. For a small U " +
		"it may be empty, which is why the statements that read a class carry the universes.",
	Deps: []registry.EntryLike{BiaffineExtensionDef, BiaffineIsomorphismDef},
})}

// biaffineExalDef — `biaffine_exal(P, h, A₀₁, A₀, A₁, t, s, V, M)`,
// written Exal: the classes of the biaffine extensions over P.
var biaffineExalDef = biaffineExalDefThm{family.Define(registry.DefEntry{
	Name:  "biaffineExalDef",
	Key:   "prop_53c1950d7e69dede",
	Const: "biaffine_exal",
	Type:  "ring_ops(A) → (A → C) → ring_ops(C) → set(C) → set(C) → C → C → module_ops(C, D) → prod(set(D), set(D)) → set(set(" + baerTuple + "))",
	Equations: []string{
		"∀P:ring_ops(A). ∀h:(A → C). ∀A₀₁:ring_ops(C). ∀A₀ A₁:set(C). ∀t s:C. ∀V:module_ops(C, D). ∀M:prod(set(D), set(D)). " + baerExal(
			"P", "h") + " = " +
			"{" + baerExalClass(
			"P",
			"h",
			baerPartsOf(baerMemberX)) + ":set(" + baerTuple + ") | " + baerHostParts(
			baerMemberX) + " | " + wg3Extension("P", "h", baerPartsOf(baerMemberX)) + "}",
	},
	Reading: "The classes are listed through their members on the realizations' type; " +
		"the class of an extension on any other type is one of them under the universes " +
		"(BiaffineExalClassEqIff). Its group law is the Baer sum (BiaffineExalGroupOn), and " +
		"it sits between H¹(𝒟⁰) and the compatible classes (ExalSequenceExact).",
	Deps: []registry.EntryLike{biaffineExalClassDef, BiaffineExtensionDef},
})}

// biaffineExalSumDef — `biaffine_exal_sum(P, h, A₀₁, A₀, A₁, t, s, V, M,
// X, Y)`: the sum of two classes — the classes of the Baer sums of a
// member of X and a member of Y, united.
var biaffineExalSumDef = biaffineExalSumDefThm{family.Define(registry.DefEntry{
	Name:  "biaffineExalSumDef",
	Key:   "prop_a0efc7a06d70099c",
	Const: "biaffine_exal_sum",
	Type: "ring_ops(A) → (A → C) → ring_ops(C) → set(C) → set(C) → C → C → module_ops(C, D) → prod(set(D), set(D)) → " +
		"set(" + baerTuple + ") → set(" + baerTuple + ") → set(" + baerTuple + ")",
	Equations: []string{
		"∀P:ring_ops(A). ∀h:(A → C). ∀A₀₁:ring_ops(C). ∀A₀ A₁:set(C). ∀t s:C. ∀V:module_ops(C, D). ∀M:prod(set(D), set(D)). ∀X Y:set(" + baerTuple + "). " +
			"biaffine_exal_sum(P, h, A₀₁, A₀, A₁, t, s, V, M, X, Y) = ⋃{" + baerExalClass(
			"P", "h", baerGlued(baerMemberX, baerMemberY)) + " | " +
			baerHostParts(baerMemberX) + ", " + baerHostParts(
			baerMemberY) + " | " + baerTupleOf(baerMemberX) + " ∈ X ∧ " + baerTupleOf(baerMemberY) + " ∈ Y}",
	},
	Reading: "On two classes this is a class: isomorphic summands have isomorphic " +
		"Baer sums, so every pair of members gives the class of the sum of any two " +
		"(BiaffineExalSumClass). The Baer sum of two members sits on a larger type than " +
		"the realizations', which is why the sum is the class of it and not the sum itself.",
	Deps: []registry.EntryLike{biaffineExalClassDef, biaffineBaerGluingDef},
})}

// biaffineExalNegDef — `biaffine_exal_neg(P, h, A₀₁, A₀, A₁, t, s, V, M,
// X)`: the negative of a class — the classes of its members with both
// inclusions negated, united.
var biaffineExalNegDef = biaffineExalNegDefThm{family.Define(registry.DefEntry{
	Name:  "biaffineExalNegDef",
	Key:   "prop_6686c54962259bd2",
	Const: "biaffine_exal_neg",
	Type: "ring_ops(A) → (A → C) → ring_ops(C) → set(C) → set(C) → C → C → module_ops(C, D) → prod(set(D), set(D)) → " +
		"set(" + baerTuple + ") → set(" + baerTuple + ")",
	Equations: []string{
		"∀P:ring_ops(A). ∀h:(A → C). ∀A₀₁:ring_ops(C). ∀A₀ A₁:set(C). ∀t s:C. ∀V:module_ops(C, D). ∀M:prod(set(D), set(D)). ∀X:set(" + baerTuple + "). " +
			"biaffine_exal_neg(P, h, A₀₁, A₀, A₁, t, s, V, M, X) = ⋃{" + baerExalClass(
			"P", "h", baerNegatedGlued(baerMemberX)) + " | " + baerHostParts(baerMemberX) + " | " +
			baerTupleOf(baerMemberX) + " ∈ X}",
	},
	Reading: "Negating an inclusion keeps the ring, the structure map and the projection, " +
		"and the localization of the negated extension is the localization of the extension with " +
		"its inclusion negated, so the gluing φ glues the negations too. The negations of the " +
		"members of one class are isomorphic, and their classes are one (BiaffineExalNegClass).",
	Deps: []registry.EntryLike{biaffineExalClassDef},
})}

// BiaffineBaerSumIsExtension — the Baer sum of two biaffine extensions,
// chart by chart with the lifts paired and glued by biaffine_baer_gluing,
// is a biaffine extension, and so is a biaffine extension with both
// inclusions negated.
var BiaffineBaerSumIsExtension = biaffineBaerSumIsExtensionThm{family.Add(registry.ProofEntry{
	Name: "BiaffineBaerSumIsExtension",
	Key:  "prop_da83c6472efaea76",
	Reading: "No universe is read. [(t₀, t₀')] lies over t in the chart-0 sum and [(t₁, t₁')] over " +
		"s in the chart-1 sum. The gluing is an isomorphism of extensions of A₀₁ by M₀₁ because each of " +
		"its three steps is one: the readings of BaerSumLocalizes in place, A₀₁ being the localization " +
		"of each chart and M₀₁ of each chart module, and the map BaerSumIsomorphism gives from φ and " +
		"φ'. The negated extension keeps its lifts and its gluing: the localization of a negated chart " +
		"extension is the localization with its inclusion negated, and φ commutes with negation.",
	Deps: []registry.EntryLike{
		BiaffineExtensionDef,
		biaffineBaerGluingDef,
		square_zero_extension.BaerSumIsExtension,
		square_zero_extension.BaerSumLocalizes,
		square_zero_extension.BaerSumIsomorphism,
		square_zero_extension.BaerSumInverse,
		square_zero_extension.SquareZeroLocalizationDef,
		square_zero_extension.SquareZeroIsomorphismDef,
		square_zero_extension.SpanIsModuleLocalization,
		lattice_pair.BiaffineChartLocalization,
		lattice_pair.LatticePairDef,
		ring_localization.FractionNegClass,
		functions.InverseOnLeft,
		functions.InverseOnRight,
		functions.InverseOnIn,
	},
	Build: family.Card(Statement{
		Binders: "∀P:ring_ops(A). " +
			"∀h:(A → C). " +
			"∀A₀₁:ring_ops(C). " +
			"∀A₀ A₁:set(C). " +
			"∀t s:C. " +
			"∀V:module_ops(C, D). " +
			"∀M:prod(set(D), set(D)). " +
			"∀E₀:square_zero_ops(A, C, I, D). " +
			"∀t₀:I. " +
			"∀E₁:square_zero_ops(A, C, H, D). " +
			"∀t₁:H. " +
			"∀φ:(set(prod(I, I)) → set(prod(H, H))). " +
			"∀E_0':square_zero_ops(A, C, G, D). " +
			"∀t_0':G. " +
			"∀E_1':square_zero_ops(A, C, F, D). " +
			"∀t_1':F. " +
			"∀φ':(set(prod(G, G)) → set(prod(F, F))).",
		Hypotheses: []string{
			"biaffine_extension(P, h, A₀₁, A₀, A₁, t, s, V, M, E₀, t₀, E₁, t₁, φ)",
			"biaffine_extension(P, h, A₀₁, A₀, A₁, t, s, V, M, E_0', t_0', E_1', t_1', φ')",
		},
		Conclusion: "biaffine_extension(P, " +
			"    h, " +
			"    A₀₁, " +
			"    A₀, " +
			"    A₁, " +
			"    t, " +
			"    s, " +
			"    V, " +
			"    M, " +
			"    square_zero_baer_sum(«wg3Module0», E₀, E_0'), " +
			"    ideal_quotient_projection(square_zero_fiber_product(E₀, E_0'), " +
			"        image(λm:D. (E₀.inclusion(m), E_0'.ring.neg(E_0'.inclusion(m))), «wg3Module0».carrier), " +
			"        (t₀, t_0')), " +
			"    square_zero_baer_sum(«wg3Module1», E₁, E_1'), " +
			"    ideal_quotient_projection(square_zero_fiber_product(E₁, E_1'), " +
			"        image(λm:D. (E₁.inclusion(m), E_1'.ring.neg(E_1'.inclusion(m))), «wg3Module1».carrier), " +
			"        (t₁, t_1')), " +
			"    biaffine_baer_gluing(A₀₁, V, M, E₀, t₀, E₁, t₁, φ, E_0', t_0', E_1', t_1', φ')) ∧ " +
			"biaffine_extension(P, " +
			"    h, " +
			"    A₀₁, " +
			"    A₀, " +
			"    A₁, " +
			"    t, " +
			"    s, " +
			"    V, " +
			"    M, " +
			"    mk_square_zero(E₀.ring, E₀.structure, λn:D. E₀.ring.neg(E₀.inclusion(n)), E₀.projection), " +
			"    t₀, " +
			"    mk_square_zero(E₁.ring, E₁.structure, λn:D. E₁.ring.neg(E₁.inclusion(n)), E₁.projection), " +
			"    t₁, " +
			"    φ)",
	},
		"chart by chart the Baer sums are extensions of the charts by their modules over P "+
			"(BaerSumIsExtension), and the classes of the paired lifts lie over t and s. A₀₁ is the "+
			"localization of each chart at the powers of its element in place and M₀₁ of each chart module "+
			"(BiaffineChartLocalization, SpanIsModuleLocalization, LatticePairDef), so BaerSumLocalizes "+
			"reads each localized sum as the Baer sum of the localizations; φ and φ' give an isomorphism of "+
			"those Baer sums (BaerSumIsomorphism), and the reading on chart 1 is inverted by inverse_on "+
			"(InverseOnLeft, InverseOnRight, InverseOnIn): the composite, biaffine_baer_gluing, is an "+
			"isomorphism of extensions (biaffineBaerGluingDef, SquareZeroIsomorphismDef), which is "+
			"BiaffineExtensionDef. Negation: each negated chart extension is one (BaerSumInverse's first "+
			"conjunct); its localization has the same ring, structure map and projection, and the inclusion "+
			"negated, the representation of m chosen alike (SquareZeroLocalizationDef, FractionNegClass), "+
			"so φ, a ring map that is the identity on M₀₁, is an isomorphism of the negations"),
})}

// BiaffineExalClassEqIff — in a universe for the base, the charts and the
// overlap, the class of a biaffine extension on any types is a member of
// Exal, and two biaffine extensions have one class exactly when they are
// isomorphic.
var BiaffineExalClassEqIff = biaffineExalClassEqIffThm{family.Add(registry.ProofEntry{
	Name: "BiaffineExalClassEqIff",
	Key:  "prop_28d1dad5dde13252",
	Reading: "The universes are load-bearing for the membership: they make the class " +
		"nonempty, ExalSequence realizing the chart classes on set(prod(U, D)) and reaching every " +
		"extension there by a regluing. ⇐ needs no universe, isomorphisms of biaffine extensions " +
		"composing and inverting. With an empty class ⇒ would fail, which the membership excludes.",
	Deps: []registry.EntryLike{
		biaffineExalClassDef,
		biaffineExalDef,
		BiaffineIsomorphismDef,
		ExalSequence,
		LocalClassLandsInKernel,
		square_zero_extension.SquareZeroIsomorphismDef,
		ring_localization.LocalizationHomomorphismExtensional,
		functions.InverseOnLeft,
		functions.InverseOnRight,
	},
	Build: family.Card(Statement{
		Binders: "∀P:ring_ops(A). " +
			"∀h:(A → C). " +
			"∀A₀₁:ring_ops(C). " +
			"∀A₀ A₁:set(C). " +
			"∀t s:C. " +
			"∀V:module_ops(C, D). " +
			"∀M:prod(set(D), set(D)). " +
			"∀E₀:square_zero_ops(A, C, I, D). " +
			"∀t₀:I. " +
			"∀E₁:square_zero_ops(A, C, H, D). " +
			"∀t₁:H. " +
			"∀φ:(set(prod(I, I)) → set(prod(H, H))). " +
			"∀E_0':square_zero_ops(A, C, G, D). " +
			"∀t_0':G. " +
			"∀E_1':square_zero_ops(A, C, F, D). " +
			"∀t_1':F. " +
			"∀φ':(set(prod(G, G)) → set(prod(F, F))).",
		Hypotheses: []string{
			"cotangent_universe(P, 𝕌⟨A:U⟩)",
			"cotangent_universe(restrict_ring(A₀₁, A₀), 𝕌⟨A:U⟩)",
			"cotangent_universe(restrict_ring(A₀₁, A₁), 𝕌⟨A:U⟩)",
			"cotangent_universe(A₀₁, 𝕌⟨A:U⟩)",
			"biaffine(A₀₁, A₀, A₁, t, s)",
			"lattice_pair(A₀₁, A₀, A₁, V, M)",
			"ring_homomorphism(P, A₀₁, h)",
			"image(h, P.carrier) ⊆ A₀ ∩ A₁",
			"biaffine_extension(P, h, A₀₁, A₀, A₁, t, s, V, M, E₀, t₀, E₁, t₁, φ)",
			"biaffine_extension(P, h, A₀₁, A₀, A₁, t, s, V, M, E_0', t_0', E_1', t_1', φ')",
		},
		Conclusion: "biaffine_exal_class⟨U:U⟩(P, h, A₀₁, A₀, A₁, t, s, V, M, E₀, t₀, E₁, t₁, φ) ∈ " +
			"biaffine_exal(P, h, A₀₁, A₀, A₁, t, s, V, M) ∧ " +
			"(biaffine_exal_class⟨U:U⟩(P, h, A₀₁, A₀, A₁, t, s, V, M, E₀, t₀, E₁, t₁, φ) = " +
			"    biaffine_exal_class⟨U:U⟩(P, h, A₀₁, A₀, A₁, t, s, V, M, E_0', t_0', E_1', t_1', φ') ⇔ " +
			"    ∃ψ₀:(I → G). ∃ψ₁:(H → F). " +
			"        biaffine_isomorphism(P, " +
			"            A₀₁, " +
			"            V, " +
			"            M, " +
			"            E₀, " +
			"            t₀, " +
			"            E₁, " +
			"            t₁, " +
			"            φ, " +
			"            E_0', " +
			"            t_0', " +
			"            E_1', " +
			"            t_1', " +
			"            φ', " +
			"            ψ₀, " +
			"            ψ₁))",
	},
		"the chart classes of the first extension are a compatible pair (LocalClassLandsInKernel); "+
			"ExalSequence's first conjunct gives a biaffine extension on set(prod(U, D)) with those chart "+
			"classes, its third an isomorphism from a regluing of it, again on that type (its second "+
			"conjunct), to the first extension, so the class holds a member and is the class of that "+
			"member (biaffineExalClassDef, biaffineExalDef). Biaffine isomorphisms compose and invert: "+
			"the chart isomorphisms compose and invert as ring isomorphisms (SquareZeroIsomorphismDef, "+
			"InverseOnLeft, InverseOnRight), and their maps of localizations compose, both sides ring "+
			"maps agreeing on the classes e/1 (LocalizationHomomorphismExtensional, "+
			"BiaffineIsomorphismDef). So isomorphic extensions have one class, and two with one class are "+
			"isomorphic to one member of it, hence to each other"),
})}

// BiaffineExalSumClass — in a universe for the base, the charts and the
// overlap, the sum of the classes of two biaffine extensions is the class
// of their Baer sum.
var BiaffineExalSumClass = biaffineExalSumClassThm{family.Add(registry.ProofEntry{
	Name: "BiaffineExalSumClass",
	Key:  "prop_c1df5e6cf1b9672e",
	Reading: "The Baer sum respects isomorphisms of biaffine extensions: chart " +
		"by chart (BaerSumIsomorphism), and the gluing of the sum is carried to the " +
		"gluing of the sum because each step of biaffine_baer_gluing is natural in " +
		"the chart isomorphisms. So every pair of members of the two classes has a " +
		"Baer sum in one class, and the classes are not empty under the universes.",
	Deps: []registry.EntryLike{
		biaffineExalSumDef,
		biaffineExalClassDef,
		BiaffineExalClassEqIff,
		BiaffineBaerSumIsExtension,
		biaffineBaerGluingDef,
		BiaffineIsomorphismDef,
		square_zero_extension.BaerSumIsomorphism,
		square_zero_extension.BaerSumLocalizes,
		ring_localization.LocalizationHomomorphismExtensional,
	},
	Build: family.Card(Statement{
		Binders: "∀P:ring_ops(A). " +
			"∀h:(A → C). " +
			"∀A₀₁:ring_ops(C). " +
			"∀A₀ A₁:set(C). " +
			"∀t s:C. " +
			"∀V:module_ops(C, D). " +
			"∀M:prod(set(D), set(D)). " +
			"∀E₀:square_zero_ops(A, C, I, D). " +
			"∀t₀:I. " +
			"∀E₁:square_zero_ops(A, C, H, D). " +
			"∀t₁:H. " +
			"∀φ:(set(prod(I, I)) → set(prod(H, H))). " +
			"∀E_0':square_zero_ops(A, C, G, D). " +
			"∀t_0':G. " +
			"∀E_1':square_zero_ops(A, C, F, D). " +
			"∀t_1':F. " +
			"∀φ':(set(prod(G, G)) → set(prod(F, F))).",
		Hypotheses: []string{
			"cotangent_universe⟨A:A, U:U⟩(P, 𝕌)",
			"cotangent_universe⟨A:C, U:U⟩(restrict_ring(A₀₁, A₀), 𝕌)",
			"cotangent_universe⟨A:C, U:U⟩(restrict_ring(A₀₁, A₁), 𝕌)",
			"cotangent_universe⟨A:C, U:U⟩(A₀₁, 𝕌)",
			"biaffine(A₀₁, A₀, A₁, t, s)",
			"lattice_pair(A₀₁, A₀, A₁, V, M)",
			"ring_homomorphism(P, A₀₁, h)",
			"image(h, P.carrier) ⊆ A₀ ∩ A₁",
			"biaffine_extension(P, h, A₀₁, A₀, A₁, t, s, V, M, E₀, t₀, E₁, t₁, φ)",
			"biaffine_extension(P, h, A₀₁, A₀, A₁, t, s, V, M, E_0', t_0', E_1', t_1', φ')",
		},
		Conclusion: "biaffine_exal_sum⟨A:A, C:C, D:D, U:U⟩(P, " +
			"    h, " +
			"    A₀₁, " +
			"    A₀, " +
			"    A₁, " +
			"    t, " +
			"    s, " +
			"    V, " +
			"    M, " +
			"    biaffine_exal_class(P, h, A₀₁, A₀, A₁, t, s, V, M, E₀, t₀, E₁, t₁, φ), " +
			"    biaffine_exal_class(P, h, A₀₁, A₀, A₁, t, s, V, M, E_0', t_0', E_1', t_1', φ')) = " +
			"biaffine_exal_class(P, " +
			"    h, " +
			"    A₀₁, " +
			"    A₀, " +
			"    A₁, " +
			"    t, " +
			"    s, " +
			"    V, " +
			"    M, " +
			"    square_zero_baer_sum(«wg3Module0», E₀, E_0'), " +
			"    ideal_quotient_projection(square_zero_fiber_product(E₀, E_0'), " +
			"        image(λm:D. (E₀.inclusion(m), E_0'.ring.neg(E_0'.inclusion(m))), «wg3Module0».carrier), " +
			"        (t₀, t_0')), " +
			"    square_zero_baer_sum(«wg3Module1», E₁, E_1'), " +
			"    ideal_quotient_projection(square_zero_fiber_product(E₁, E_1'), " +
			"        image(λm:D. (E₁.inclusion(m), E_1'.ring.neg(E_1'.inclusion(m))), «wg3Module1».carrier), " +
			"        (t₁, t_1')), " +
			"    biaffine_baer_gluing(A₀₁, V, M, E₀, t₀, E₁, t₁, φ, E_0', t_0', E_1', t_1', φ'))",
	},
		"unfold biaffine_exal_sum (biaffineExalSumDef). Members x of the first class and y of the "+
			"second are isomorphic to the two extensions (biaffineExalClassDef); the chart isomorphisms "+
			"give isomorphisms of the chart Baer sums (BaerSumIsomorphism), and their maps of "+
			"localizations carry one gluing of the sum to the other: read through BaerSumLocalizes they "+
			"are the componentwise maps of localizations, which commute with φ and φ' by "+
			"BiaffineIsomorphismDef, checked on the classes e/1 (LocalizationHomomorphismExtensional). "+
			"So the Baer sum of x and y is isomorphic to that of the two extensions, a biaffine "+
			"extension (BiaffineBaerSumIsExtension), and its class is the same (BiaffineExalClassEqIff). "+
			"Both classes have members (BiaffineExalClassEqIff), so the union is that one class"),
})}

// BiaffineExalNegClass — in a universe for the base, the charts and the
// overlap, the negative of the class of a biaffine extension is the class
// of the extension with both inclusions negated.
var BiaffineExalNegClass = biaffineExalNegClassThm{family.Add(registry.ProofEntry{
	Name: "BiaffineExalNegClass",
	Key:  "prop_91ddc0cd5376be90",
	Reading: "An isomorphism of chart extensions is one of their negations, " +
		"the same map: it commutes with negation, being additive. So the negations " +
		"of the members of a class are isomorphic to the negation of the extension.",
	Deps: []registry.EntryLike{
		biaffineExalNegDef,
		biaffineExalClassDef,
		BiaffineExalClassEqIff,
		BiaffineBaerSumIsExtension,
		BiaffineIsomorphismDef,
		square_zero_extension.SquareZeroIsomorphismDef,
		square_zero_extension.SquareZeroLocalizationDef,
		ring_localization.FractionNegClass,
	},
	Build: family.Card(Statement{
		Binders: "∀P:ring_ops(A). " +
			"∀h:(A → C). " +
			"∀A₀₁:ring_ops(C). " +
			"∀A₀ A₁:set(C). " +
			"∀t s:C. " +
			"∀V:module_ops(C, D). " +
			"∀M:prod(set(D), set(D)). " +
			"∀E₀:square_zero_ops(A, C, I, D). " +
			"∀t₀:I. " +
			"∀E₁:square_zero_ops(A, C, H, D). " +
			"∀t₁:H. " +
			"∀φ:(set(prod(I, I)) → set(prod(H, H))).",
		Hypotheses: []string{
			"cotangent_universe⟨A:A, U:U⟩(P, 𝕌)",
			"cotangent_universe⟨A:C, U:U⟩(restrict_ring(A₀₁, A₀), 𝕌)",
			"cotangent_universe⟨A:C, U:U⟩(restrict_ring(A₀₁, A₁), 𝕌)",
			"cotangent_universe⟨A:C, U:U⟩(A₀₁, 𝕌)",
			"biaffine(A₀₁, A₀, A₁, t, s)",
			"lattice_pair(A₀₁, A₀, A₁, V, M)",
			"ring_homomorphism(P, A₀₁, h)",
			"image(h, P.carrier) ⊆ A₀ ∩ A₁",
			"biaffine_extension(P, h, A₀₁, A₀, A₁, t, s, V, M, E₀, t₀, E₁, t₁, φ)",
		},
		Conclusion: "biaffine_exal_neg⟨A:A, C:C, D:D, U:U⟩(P, " +
			"    h, " +
			"    A₀₁, " +
			"    A₀, " +
			"    A₁, " +
			"    t, " +
			"    s, " +
			"    V, " +
			"    M, " +
			"    biaffine_exal_class(P, h, A₀₁, A₀, A₁, t, s, V, M, E₀, t₀, E₁, t₁, φ)) = " +
			"biaffine_exal_class(P, " +
			"    h, " +
			"    A₀₁, " +
			"    A₀, " +
			"    A₁, " +
			"    t, " +
			"    s, " +
			"    V, " +
			"    M, " +
			"    mk_square_zero(E₀.ring, E₀.structure, λn:D. E₀.ring.neg(E₀.inclusion(n)), E₀.projection), " +
			"    t₀, " +
			"    mk_square_zero(E₁.ring, E₁.structure, λn:D. E₁.ring.neg(E₁.inclusion(n)), E₁.projection), " +
			"    t₁, " +
			"    φ)",
	},
		"unfold biaffine_exal_neg (biaffineExalNegDef). A member x of the class is isomorphic "+
			"to the extension (biaffineExalClassDef); the same chart isomorphisms are isomorphisms "+
			"of the negations, additive ring maps commuting with the negated inclusions "+
			"(SquareZeroIsomorphismDef), and the same maps of localizations, the localization of a "+
			"negation being the localization with its inclusion negated (SquareZeroLocalizationDef, "+
			"FractionNegClass), so the square of BiaffineIsomorphismDef is unchanged. The negations "+
			"are biaffine extensions (BiaffineBaerSumIsExtension), so their classes agree "+
			"(BiaffineExalClassEqIff), and the class has members, so the union is that one class"),
})}

// BiaffineExalGroupOn — in a universe for the base, the charts and the
// overlap, Exal is a group under the sum of classes, with the class of
// the split extensions glued by the zero derivation as unit and the class
// of the negated extension as inverse.
var BiaffineExalGroupOn = biaffineExalGroupOnThm{family.Add(registry.ProofEntry{
	Name: "BiaffineExalGroupOn",
	Key:  "prop_f88a996efba136ae",
	Reading: "Every member of Exal is the class of a biaffine extension, and the operations on " +
		"classes are the operations on extensions (BiaffineExalSumClass, BiaffineExalNegClass): " +
		"the group axioms are the Baer sum's up to isomorphism, chart by chart, with the gluings " +
		"matched through the readings of BaerSumLocalizes. The unit is the trivial gluing: the " +
		"split extensions with the lifts (t, 0) and (s, 0), glued by the shear of the zero " +
		"derivation (GluedTrivialIsExtension). No smoothness and no finiteness is asked.",
	Deps: []registry.EntryLike{
		biaffineExalDef,
		BiaffineExalSumClass,
		BiaffineExalNegClass,
		BiaffineExalClassEqIff,
		BiaffineBaerSumIsExtension,
		GluedTrivialIsExtension,
		biaffineShearGluingDef,
		square_zero_extension.BaerSumAssoc,
		square_zero_extension.BaerSumSplitUnit,
		square_zero_extension.BaerSumComm,
		square_zero_extension.BaerSumInverse,
		square_zero_extension.BaerSumLocalizes,
		square_zero_extension.SplitSquareZeroLocalization,
		ring_localization.LocalizationHomomorphismExtensional,
		group.GroupOn,
	},
	Build: family.Card(Statement{
		Binders: "∀P:ring_ops(A). " +
			"∀h:(A → C). " +
			"∀A₀₁:ring_ops(C). " +
			"∀A₀ A₁:set(C). " +
			"∀t s:C. " +
			"∀V:module_ops(C, D). " +
			"∀M:prod(set(D), set(D)).",
		Hypotheses: []string{
			"cotangent_universe(P, 𝕌⟨A:U⟩)",
			"cotangent_universe(restrict_ring(A₀₁, A₀), 𝕌⟨A:U⟩)",
			"cotangent_universe(restrict_ring(A₀₁, A₁), 𝕌⟨A:U⟩)",
			"cotangent_universe(A₀₁, 𝕌⟨A:U⟩)",
			"biaffine(A₀₁, A₀, A₁, t, s)",
			"lattice_pair(A₀₁, A₀, A₁, V, M)",
			"ring_homomorphism(P, A₀₁, h)",
			"image(h, P.carrier) ⊆ A₀ ∩ A₁",
		},
		Conclusion: "group_on(mk_group(λX:set(prod(square_zero_ops(A, C, set(prod(U, D)), D), " +
			"                    prod(set(prod(U, D)), " +
			"                        prod(square_zero_ops(A, C, set(prod(U, D)), D), " +
			"                            prod(set(prod(U, D)), " +
			"                                set(prod(set(prod(U, D)), set(prod(U, D)))) → " +
			"                                set(prod(set(prod(U, D)), set(prod(U, D))))))))). " +
			"        λY:set(prod(square_zero_ops(A, C, set(prod(U, D)), D), " +
			"                    prod(set(prod(U, D)), " +
			"                        prod(square_zero_ops(A, C, set(prod(U, D)), D), " +
			"                            prod(set(prod(U, D)), " +
			"                                set(prod(set(prod(U, D)), set(prod(U, D)))) → " +
			"                                set(prod(set(prod(U, D)), set(prod(U, D))))))))). " +
			"            biaffine_exal_sum(P, h, A₀₁, A₀, A₁, t, s, V, M, X, Y), " +
			"        biaffine_exal_class⟨U:U⟩(P, " +
			"            h, " +
			"            A₀₁, " +
			"            A₀, " +
			"            A₁, " +
			"            t, " +
			"            s, " +
			"            V, " +
			"            M, " +
			"            mk_square_zero( " +
			"                split_square_zero(restrict_ring(A₀₁, A₀), λy:C. y, restrict_module(V, fst(M))), " +
			"                λa:A. (h(a), V.zero), " +
			"                λn:D. (A₀₁.zero, n), " +
			"                λz:prod(C, D). fst(z)), " +
			"            (t, V.zero), " +
			"            mk_square_zero( " +
			"                split_square_zero(restrict_ring(A₀₁, A₁), λy:C. y, restrict_module(V, snd(M))), " +
			"                λa:A. (h(a), V.zero), " +
			"                λn:D. (A₀₁.zero, n), " +
			"                λz:prod(C, D). fst(z)), " +
			"            (s, V.zero), " +
			"            biaffine_shear_gluing(A₀₁, " +
			"                A₁, " +
			"                s, " +
			"                V, " +
			"                M, " +
			"                biaffine_overlap_derivations(P, h, A₀₁, V, M).zero)), " +
			"        λX:set(prod(square_zero_ops(A, C, set(prod(U, D)), D), " +
			"                    prod(set(prod(U, D)), " +
			"                        prod(square_zero_ops(A, C, set(prod(U, D)), D), " +
			"                            prod(set(prod(U, D)), " +
			"                                set(prod(set(prod(U, D)), set(prod(U, D)))) → " +
			"                                set(prod(set(prod(U, D)), set(prod(U, D))))))))). " +
			"            biaffine_exal_neg(P, h, A₀₁, A₀, A₁, t, s, V, M, X), " +
			"        biaffine_exal(P, h, A₀₁, A₀, A₁, t, s, V, M)))",
	},
		"unfold group_on (GroupOn) and biaffine_exal: the members are the classes of biaffine "+
			"extensions on the realizations' type (biaffineExalDef). The unit is a member: the trivial "+
			"gluing is a biaffine extension (GluedTrivialIsExtension at the zero derivation) and its class "+
			"is in Exal (BiaffineExalClassEqIff). Closure: the sum and the negative of classes are the "+
			"classes of the Baer sum and of the negation (BiaffineExalSumClass, BiaffineExalNegClass), "+
			"biaffine extensions (BiaffineBaerSumIsExtension). Associativity, the unit and the inverse law "+
			"hold of representatives up to isomorphism: chart by chart by BaerSumAssoc, BaerSumSplitUnit "+
			"with BaerSumComm, and BaerSumInverse with BaerSumComm, each isomorphism carrying one gluing "+
			"to the other when both are read through BaerSumLocalizes and SplitSquareZeroLocalization, "+
			"checked on the classes e/1 (LocalizationHomomorphismExtensional); isomorphic extensions have "+
			"one class (BiaffineExalClassEqIff)"),
})}

// BiaffineExalAbelian — in a universe for the base, the charts and the
// overlap, Exal is an abelian group.
var BiaffineExalAbelian = biaffineExalAbelianThm{family.Add(registry.ProofEntry{
	Name: "BiaffineExalAbelian",
	Key:  "prop_5d5f91021367ab63",
	Deps: []registry.EntryLike{
		BiaffineExalGroupOn,
		BiaffineExalSumClass,
		BiaffineExalClassEqIff,
		square_zero_extension.BaerSumComm,
		square_zero_extension.BaerSumLocalizes,
		ring_localization.LocalizationHomomorphismExtensional,
		abelian_group.AbelianGroupOn,
	},
	Build: family.Card(Statement{
		Binders: "∀P:ring_ops(A). " +
			"∀h:(A → C). " +
			"∀A₀₁:ring_ops(C). " +
			"∀A₀ A₁:set(C). " +
			"∀t s:C. " +
			"∀V:module_ops(C, D). " +
			"∀M:prod(set(D), set(D)).",
		Hypotheses: []string{
			"cotangent_universe(P, 𝕌⟨A:U⟩)",
			"cotangent_universe(restrict_ring(A₀₁, A₀), 𝕌⟨A:U⟩)",
			"cotangent_universe(restrict_ring(A₀₁, A₁), 𝕌⟨A:U⟩)",
			"cotangent_universe(A₀₁, 𝕌⟨A:U⟩)",
			"biaffine(A₀₁, A₀, A₁, t, s)",
			"lattice_pair(A₀₁, A₀, A₁, V, M)",
			"ring_homomorphism(P, A₀₁, h)",
			"image(h, P.carrier) ⊆ A₀ ∩ A₁",
		},
		Conclusion: "abelian_group_on(mk_group(λX:set(prod(square_zero_ops(A, C, set(prod(U, D)), D), " +
			"                    prod(set(prod(U, D)), " +
			"                        prod(square_zero_ops(A, C, set(prod(U, D)), D), " +
			"                            prod(set(prod(U, D)), " +
			"                                set(prod(set(prod(U, D)), set(prod(U, D)))) → " +
			"                                set(prod(set(prod(U, D)), set(prod(U, D))))))))). " +
			"        λY:set(prod(square_zero_ops(A, C, set(prod(U, D)), D), " +
			"                    prod(set(prod(U, D)), " +
			"                        prod(square_zero_ops(A, C, set(prod(U, D)), D), " +
			"                            prod(set(prod(U, D)), " +
			"                                set(prod(set(prod(U, D)), set(prod(U, D)))) → " +
			"                                set(prod(set(prod(U, D)), set(prod(U, D))))))))). " +
			"            biaffine_exal_sum(P, h, A₀₁, A₀, A₁, t, s, V, M, X, Y), " +
			"        biaffine_exal_class⟨U:U⟩(P, " +
			"            h, " +
			"            A₀₁, " +
			"            A₀, " +
			"            A₁, " +
			"            t, " +
			"            s, " +
			"            V, " +
			"            M, " +
			"            mk_square_zero( " +
			"                split_square_zero(restrict_ring(A₀₁, A₀), λy:C. y, restrict_module(V, fst(M))), " +
			"                λa:A. (h(a), V.zero), " +
			"                λn:D. (A₀₁.zero, n), " +
			"                λz:prod(C, D). fst(z)), " +
			"            (t, V.zero), " +
			"            mk_square_zero( " +
			"                split_square_zero(restrict_ring(A₀₁, A₁), λy:C. y, restrict_module(V, snd(M))), " +
			"                λa:A. (h(a), V.zero), " +
			"                λn:D. (A₀₁.zero, n), " +
			"                λz:prod(C, D). fst(z)), " +
			"            (s, V.zero), " +
			"            biaffine_shear_gluing(A₀₁, " +
			"                A₁, " +
			"                s, " +
			"                V, " +
			"                M, " +
			"                biaffine_overlap_derivations(P, h, A₀₁, V, M).zero)), " +
			"        λX:set(prod(square_zero_ops(A, C, set(prod(U, D)), D), " +
			"                    prod(set(prod(U, D)), " +
			"                        prod(square_zero_ops(A, C, set(prod(U, D)), D), " +
			"                            prod(set(prod(U, D)), " +
			"                                set(prod(set(prod(U, D)), set(prod(U, D)))) → " +
			"                                set(prod(set(prod(U, D)), set(prod(U, D))))))))). " +
			"            biaffine_exal_neg(P, h, A₀₁, A₀, A₁, t, s, V, M, X), " +
			"        biaffine_exal(P, h, A₀₁, A₀, A₁, t, s, V, M)))",
	},
		"unfold abelian_group_on (AbelianGroupOn): the group is BiaffineExalGroupOn, and "+
			"the Baer sums of x and y and of y and x are isomorphic biaffine extensions, "+
			"BaerSumComm chart by chart carrying one gluing to the other through the "+
			"readings of BaerSumLocalizes (LocalizationHomomorphismExtensional), so their "+
			"classes agree (BiaffineExalSumClass, BiaffineExalClassEqIff)"),
})}

// ---------------------------------------------------------------------------
// The exact sequence of groups
// ---------------------------------------------------------------------------

// ExalSequenceExact — in a universe for the base, the charts and the
// overlap, the group form of ExalSequence: d ↦ the class of the split
// extensions glued by the shear of d is a one-to-one homomorphism from
// H¹(𝒟⁰) into Exal, the chart classes are a homomorphism from Exal onto
// the compatible classes, and the image of the first is the kernel of
// the second.
var ExalSequenceExact = exalSequenceExactThm{family.Add(registry.ProofEntry{
	Name: "ExalSequenceExact",
	Key:  "prop_40cb8416c599dea1",
	Reading: "0 → H¹(𝒟⁰) → Exal → compatible classes → 0. H¹(𝒟⁰) is read in the container, " +
		"every derivation of the overlap modulo fst(𝒟⁰) + snd(𝒟⁰), a group whatever the charts; " +
		"it is lattice_pair_h1 of the derivation pair when both charts are finitely generated, " +
		"its ambient then being every derivation (DerivationPairIsLattice). Both maps read a " +
		"representative: the first is well defined by GluedTrivialIsoIffCoboundary, the second " +
		"because isomorphic extensions have one pair of chart classes. ExalSequence is the same " +
		"sequence at the level of sets, with the regluings named.",
	Deps: []registry.EntryLike{
		ExalSequence,
		GluedTrivialIsExtension,
		GluedTrivialIsoIffCoboundary,
		LocallyTrivialIsH1D0,
		LocalClassLandsInKernel,
		BiaffineExalGroupOn,
		BiaffineExalSumClass,
		BiaffineExalClassEqIff,
		biaffineLocalClassDef,
		biaffineCompatibleClassesDef,
		algebra_deformation.BaerSumClass,
		square_zero_classification.ExtensionClassWellDefined,
		square_zero_extension.BaerSumSplitUnit,
		square_zero_extension.SplitSquareZeroLocalization,
		group_homomorphism.GroupHomomorphism,
		quotient_group.QuotientGroupOn,
		ClassModulesOverSubring,
		module_homomorphism.ExactAtDef,
		group_homomorphism.GroupKernelDef,
		submodule.QuotientModuleDef,
		functions.InjectiveOnDef,
	},
	Build: family.Card(Statement{
		Binders: "∀P:ring_ops(A). " +
			"∀h:(A → C). " +
			"∀A₀₁:ring_ops(C). " +
			"∀A₀ A₁:set(C). " +
			"∀t s:C. " +
			"∀V:module_ops(C, D). " +
			"∀M:prod(set(D), set(D)).",
		Hypotheses: []string{
			"cotangent_universe(P, 𝕌⟨A:U⟩)",
			"cotangent_universe(restrict_ring(A₀₁, A₀), 𝕌⟨A:U⟩)",
			"cotangent_universe(restrict_ring(A₀₁, A₁), 𝕌⟨A:U⟩)",
			"cotangent_universe(A₀₁, 𝕌⟨A:U⟩)",
			"biaffine(A₀₁, A₀, A₁, t, s)",
			"lattice_pair(A₀₁, A₀, A₁, V, M)",
			"ring_homomorphism(P, A₀₁, h)",
			"image(h, P.carrier) ⊆ A₀ ∩ A₁",
		},
		Conclusion: "group_homomorphism(mk_group(quotient_module( " +
			"            biaffine_overlap_derivations(P, h, A₀₁, V, M), " +
			"            set_mul(biaffine_overlap_derivations(P, h, A₀₁, V, M).add, " +
			"                fst(biaffine_derivation_pair(P, h, A₀₁, A₀, A₁, V, M)), " +
			"                snd(biaffine_derivation_pair(P, h, A₀₁, A₀, A₁, V, M)))).add, " +
			"        quotient_module(biaffine_overlap_derivations(P, h, A₀₁, V, M), " +
			"            set_mul(biaffine_overlap_derivations(P, h, A₀₁, V, M).add, " +
			"                fst(biaffine_derivation_pair(P, h, A₀₁, A₀, A₁, V, M)), " +
			"                snd(biaffine_derivation_pair(P, h, A₀₁, A₀, A₁, V, M)))).zero, " +
			"        quotient_module(biaffine_overlap_derivations(P, h, A₀₁, V, M), " +
			"            set_mul(biaffine_overlap_derivations(P, h, A₀₁, V, M).add, " +
			"                fst(biaffine_derivation_pair(P, h, A₀₁, A₀, A₁, V, M)), " +
			"                snd(biaffine_derivation_pair(P, h, A₀₁, A₀, A₁, V, M)))).neg, " +
			"        quotient_module(biaffine_overlap_derivations(P, h, A₀₁, V, M), " +
			"            set_mul(biaffine_overlap_derivations(P, h, A₀₁, V, M).add, " +
			"                fst(biaffine_derivation_pair(P, h, A₀₁, A₀, A₁, V, M)), " +
			"                snd(biaffine_derivation_pair(P, h, A₀₁, A₀, A₁, V, M)))).carrier), " +
			"    mk_group(λX:set(prod(square_zero_ops(A, C, set(prod(U, D)), D), " +
			"                    prod(set(prod(U, D)), " +
			"                        prod(square_zero_ops(A, C, set(prod(U, D)), D), " +
			"                            prod(set(prod(U, D)), " +
			"                                set(prod(set(prod(U, D)), set(prod(U, D)))) → " +
			"                                set(prod(set(prod(U, D)), set(prod(U, D))))))))). " +
			"        λY:set(prod(square_zero_ops(A, C, set(prod(U, D)), D), " +
			"                    prod(set(prod(U, D)), " +
			"                        prod(square_zero_ops(A, C, set(prod(U, D)), D), " +
			"                            prod(set(prod(U, D)), " +
			"                                set(prod(set(prod(U, D)), set(prod(U, D)))) → " +
			"                                set(prod(set(prod(U, D)), set(prod(U, D))))))))). " +
			"            biaffine_exal_sum(P, h, A₀₁, A₀, A₁, t, s, V, M, X, Y), " +
			"        biaffine_exal_class⟨U:U⟩(P, " +
			"            h, " +
			"            A₀₁, " +
			"            A₀, " +
			"            A₁, " +
			"            t, " +
			"            s, " +
			"            V, " +
			"            M, " +
			"            mk_square_zero( " +
			"                split_square_zero(restrict_ring(A₀₁, A₀), λy:C. y, restrict_module(V, fst(M))), " +
			"                λa:A. (h(a), V.zero), " +
			"                λn:D. (A₀₁.zero, n), " +
			"                λz:prod(C, D). fst(z)), " +
			"            (t, V.zero), " +
			"            mk_square_zero( " +
			"                split_square_zero(restrict_ring(A₀₁, A₁), λy:C. y, restrict_module(V, snd(M))), " +
			"                λa:A. (h(a), V.zero), " +
			"                λn:D. (A₀₁.zero, n), " +
			"                λz:prod(C, D). fst(z)), " +
			"            (s, V.zero), " +
			"            biaffine_shear_gluing(A₀₁, " +
			"                A₁, " +
			"                s, " +
			"                V, " +
			"                M, " +
			"                biaffine_overlap_derivations(P, h, A₀₁, V, M).zero)), " +
			"        λX:set(prod(square_zero_ops(A, C, set(prod(U, D)), D), " +
			"                    prod(set(prod(U, D)), " +
			"                        prod(square_zero_ops(A, C, set(prod(U, D)), D), " +
			"                            prod(set(prod(U, D)), " +
			"                                set(prod(set(prod(U, D)), set(prod(U, D)))) → " +
			"                                set(prod(set(prod(U, D)), set(prod(U, D))))))))). " +
			"            biaffine_exal_neg(P, h, A₀₁, A₀, A₁, t, s, V, M, X), " +
			"        biaffine_exal(P, h, A₀₁, A₀, A₁, t, s, V, M)), " +
			"    induced_map(λd:(C → D). " +
			"            biaffine_exal_class⟨U:U⟩(P, " +
			"                h, " +
			"                A₀₁, " +
			"                A₀, " +
			"                A₁, " +
			"                t, " +
			"                s, " +
			"                V, " +
			"                M, " +
			"                mk_square_zero(split_square_zero(restrict_ring(A₀₁, A₀), " +
			"                        λy:C. y, " +
			"                        restrict_module(V, fst(M))), " +
			"                    λa:A. (h(a), V.zero), " +
			"                    λn:D. (A₀₁.zero, n), " +
			"                    λz:prod(C, D). fst(z)), " +
			"                (t, V.zero), " +
			"                mk_square_zero(split_square_zero(restrict_ring(A₀₁, A₁), " +
			"                        λy:C. y, " +
			"                        restrict_module(V, snd(M))), " +
			"                    λa:A. (h(a), V.zero), " +
			"                    λn:D. (A₀₁.zero, n), " +
			"                    λz:prod(C, D). fst(z)), " +
			"                (s, V.zero), " +
			"                biaffine_shear_gluing(A₀₁, A₁, s, V, M, d)))) ∧ " +
			"injective_on(quotient_module(biaffine_overlap_derivations(P, h, A₀₁, V, M), " +
			"        set_mul(biaffine_overlap_derivations(P, h, A₀₁, V, M).add, " +
			"            fst(biaffine_derivation_pair(P, h, A₀₁, A₀, A₁, V, M)), " +
			"            snd(biaffine_derivation_pair(P, h, A₀₁, A₀, A₁, V, M)))).carrier, " +
			"    induced_map(λd:(C → D). " +
			"            biaffine_exal_class⟨U:U⟩(P, " +
			"                h, " +
			"                A₀₁, " +
			"                A₀, " +
			"                A₁, " +
			"                t, " +
			"                s, " +
			"                V, " +
			"                M, " +
			"                mk_square_zero(split_square_zero(restrict_ring(A₀₁, A₀), " +
			"                        λy:C. y, " +
			"                        restrict_module(V, fst(M))), " +
			"                    λa:A. (h(a), V.zero), " +
			"                    λn:D. (A₀₁.zero, n), " +
			"                    λz:prod(C, D). fst(z)), " +
			"                (t, V.zero), " +
			"                mk_square_zero(split_square_zero(restrict_ring(A₀₁, A₁), " +
			"                        λy:C. y, " +
			"                        restrict_module(V, snd(M))), " +
			"                    λa:A. (h(a), V.zero), " +
			"                    λn:D. (A₀₁.zero, n), " +
			"                    λz:prod(C, D). fst(z)), " +
			"                (s, V.zero), " +
			"                biaffine_shear_gluing(A₀₁, A₁, s, V, M, d)))) ∧ " +
			"group_homomorphism(mk_group(λX:set(prod(square_zero_ops(A, C, set(prod(U, D)), D), " +
			"                    prod(set(prod(U, D)), " +
			"                        prod(square_zero_ops(A, C, set(prod(U, D)), D), " +
			"                            prod(set(prod(U, D)), " +
			"                                set(prod(set(prod(U, D)), set(prod(U, D)))) → " +
			"                                set(prod(set(prod(U, D)), set(prod(U, D))))))))). " +
			"        λY:set(prod(square_zero_ops(A, C, set(prod(U, D)), D), " +
			"                    prod(set(prod(U, D)), " +
			"                        prod(square_zero_ops(A, C, set(prod(U, D)), D), " +
			"                            prod(set(prod(U, D)), " +
			"                                set(prod(set(prod(U, D)), set(prod(U, D)))) → " +
			"                                set(prod(set(prod(U, D)), set(prod(U, D))))))))). " +
			"            biaffine_exal_sum(P, h, A₀₁, A₀, A₁, t, s, V, M, X, Y), " +
			"        biaffine_exal_class⟨U:U⟩(P, " +
			"            h, " +
			"            A₀₁, " +
			"            A₀, " +
			"            A₁, " +
			"            t, " +
			"            s, " +
			"            V, " +
			"            M, " +
			"            mk_square_zero( " +
			"                split_square_zero(restrict_ring(A₀₁, A₀), λy:C. y, restrict_module(V, fst(M))), " +
			"                λa:A. (h(a), V.zero), " +
			"                λn:D. (A₀₁.zero, n), " +
			"                λz:prod(C, D). fst(z)), " +
			"            (t, V.zero), " +
			"            mk_square_zero( " +
			"                split_square_zero(restrict_ring(A₀₁, A₁), λy:C. y, restrict_module(V, snd(M))), " +
			"                λa:A. (h(a), V.zero), " +
			"                λn:D. (A₀₁.zero, n), " +
			"                λz:prod(C, D). fst(z)), " +
			"            (s, V.zero), " +
			"            biaffine_shear_gluing(A₀₁, " +
			"                A₁, " +
			"                s, " +
			"                V, " +
			"                M, " +
			"                biaffine_overlap_derivations(P, h, A₀₁, V, M).zero)), " +
			"        λX:set(prod(square_zero_ops(A, C, set(prod(U, D)), D), " +
			"                    prod(set(prod(U, D)), " +
			"                        prod(square_zero_ops(A, C, set(prod(U, D)), D), " +
			"                            prod(set(prod(U, D)), " +
			"                                set(prod(set(prod(U, D)), set(prod(U, D)))) → " +
			"                                set(prod(set(prod(U, D)), set(prod(U, D))))))))). " +
			"            biaffine_exal_neg(P, h, A₀₁, A₀, A₁, t, s, V, M, X), " +
			"        biaffine_exal(P, h, A₀₁, A₀, A₁, t, s, V, M)), " +
			"    mk_group(biaffine_compatible_classes⟨U:U⟩(P, h, A₀₁, A₀, A₁, V, M).add, " +
			"        biaffine_compatible_classes⟨U:U⟩(P, h, A₀₁, A₀, A₁, V, M).zero, " +
			"        biaffine_compatible_classes⟨U:U⟩(P, h, A₀₁, A₀, A₁, V, M).neg, " +
			"        biaffine_compatible_classes⟨U:U⟩(P, h, A₀₁, A₀, A₁, V, M).carrier), " +
			"    induced_map(λx:prod(square_zero_ops(A, C, set(prod(U, D)), D), " +
			"                prod(set(prod(U, D)), " +
			"                    prod(square_zero_ops(A, C, set(prod(U, D)), D), " +
			"                        prod(set(prod(U, D)), " +
			"                            set(prod(set(prod(U, D)), set(prod(U, D)))) → " +
			"                            set(prod(set(prod(U, D)), set(prod(U, D)))))))). " +
			"            biaffine_local_class⟨U:U⟩(P, h, A₀₁, A₀, A₁, V, M, fst(x), fst(snd(snd(x)))))) ∧ " +
			"image(induced_map(λx:prod(square_zero_ops(A, C, set(prod(U, D)), D), " +
			"                prod(set(prod(U, D)), " +
			"                    prod(square_zero_ops(A, C, set(prod(U, D)), D), " +
			"                        prod(set(prod(U, D)), " +
			"                            set(prod(set(prod(U, D)), set(prod(U, D)))) → " +
			"                            set(prod(set(prod(U, D)), set(prod(U, D)))))))). " +
			"            biaffine_local_class⟨U:U⟩(P, h, A₀₁, A₀, A₁, V, M, fst(x), fst(snd(snd(x))))), " +
			"    biaffine_exal(P, h, A₀₁, A₀, A₁, t, s, V, M)) = " +
			"biaffine_compatible_classes⟨U:U⟩(P, h, A₀₁, A₀, A₁, V, M).carrier ∧ " +
			"exact_at(biaffine_compatible_classes⟨U:U⟩(P, h, A₀₁, A₀, A₁, V, M).zero, " +
			"    quotient_module(biaffine_overlap_derivations(P, h, A₀₁, V, M), " +
			"        set_mul(biaffine_overlap_derivations(P, h, A₀₁, V, M).add, " +
			"            fst(biaffine_derivation_pair(P, h, A₀₁, A₀, A₁, V, M)), " +
			"            snd(biaffine_derivation_pair(P, h, A₀₁, A₀, A₁, V, M)))).carrier, " +
			"    biaffine_exal(P, h, A₀₁, A₀, A₁, t, s, V, M), " +
			"    induced_map(λd:(C → D). " +
			"            biaffine_exal_class⟨U:U⟩(P, " +
			"                h, " +
			"                A₀₁, " +
			"                A₀, " +
			"                A₁, " +
			"                t, " +
			"                s, " +
			"                V, " +
			"                M, " +
			"                mk_square_zero(split_square_zero(restrict_ring(A₀₁, A₀), " +
			"                        λy:C. y, " +
			"                        restrict_module(V, fst(M))), " +
			"                    λa:A. (h(a), V.zero), " +
			"                    λn:D. (A₀₁.zero, n), " +
			"                    λz:prod(C, D). fst(z)), " +
			"                (t, V.zero), " +
			"                mk_square_zero(split_square_zero(restrict_ring(A₀₁, A₁), " +
			"                        λy:C. y, " +
			"                        restrict_module(V, snd(M))), " +
			"                    λa:A. (h(a), V.zero), " +
			"                    λn:D. (A₀₁.zero, n), " +
			"                    λz:prod(C, D). fst(z)), " +
			"                (s, V.zero), " +
			"                biaffine_shear_gluing(A₀₁, A₁, s, V, M, d))), " +
			"    induced_map(λx:prod(square_zero_ops(A, C, set(prod(U, D)), D), " +
			"                prod(set(prod(U, D)), " +
			"                    prod(square_zero_ops(A, C, set(prod(U, D)), D), " +
			"                        prod(set(prod(U, D)), " +
			"                            set(prod(set(prod(U, D)), set(prod(U, D)))) → " +
			"                            set(prod(set(prod(U, D)), set(prod(U, D)))))))). " +
			"            biaffine_local_class⟨U:U⟩(P, h, A₀₁, A₀, A₁, V, M, fst(x), fst(snd(snd(x))))))",
	},
		"the first map: the shear gluing of a derivation is a biaffine extension "+
			"(GluedTrivialIsExtension) whose class lies in Exal (BiaffineExalClassEqIff); two members of one "+
			"coset glue isomorphic extensions (GluedTrivialIsoIffCoboundary), so the class does not depend "+
			"on the representative, and two cosets with one image are one, which is the injectivity "+
			"(QuotientModuleDef, InjectiveOnDef). It is a homomorphism: the Baer sum of the split extensions "+
			"glued by d and d' is isomorphic to the split extensions glued by d + d', chart by chart by "+
			"BaerSumSplitUnit at the split extension, the gluings read in A₀₁ ⋉ M₀₁ through "+
			"SplitSquareZeroLocalization, where the shears compose by the sum (BiaffineExalSumClass, "+
			"BiaffineExalClassEqIff). The second map is well defined, isomorphic extensions having one pair "+
			"of chart classes (ExtensionClassWellDefined through biaffineLocalClassDef), lands in the "+
			"compatible classes (LocalClassLandsInKernel), is a homomorphism, the chart classes of a Baer "+
			"sum being the sums (BaerSumClass at each chart, biaffineCompatibleClassesDef), and is onto "+
			"(ExalSequence's first conjunct). Exactness (ExactAtDef, GroupKernelDef): the split extensions "+
			"have chart classes zero, and every class with chart classes zero is the class of a shear gluing "+
			"(LocallyTrivialIsH1D0). Exal is a group (BiaffineExalGroupOn); H¹(𝒟⁰) is one as the quotient of "+
			"the derivations' additive group by fst(𝒟⁰) + snd(𝒟⁰), a subgroup of an abelian group and so "+
			"normal (QuotientGroupOn), and the compatible classes are one as a submodule of the product "+
			"(ClassModulesOverSubring); the two maps are homomorphisms of these groups (GroupHomomorphism)"),
})}
