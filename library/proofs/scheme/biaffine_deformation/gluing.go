// gluing.go — the extensions of a curve held by two charts. The
// derivation pair is a lattice pair in the derivations of the overlap,
// its charts the derivations of the two charts extended by the quotient
// rule. The split extensions glued by the shear of a derivation d are
// biaffine extensions that split on each chart, two of them isomorphic
// exactly when d − d' ∈ Der(A₀, M₀) + Der(A₁, M₁), and every extension
// that splits on both charts is one of them: those extensions are
// H¹(𝒟⁰). The pair of chart classes of a biaffine extension agrees on
// the overlap, every agreeing pair is reached, and the extensions with
// one pair of chart classes are the regluings of one by the derivations
// of the overlap, two regluings isomorphic exactly when the derivations
// differ by Der(A₀, M₀) + Der(A₁, M₁): the sequence 0 → H¹(𝒟⁰) → biaffine
// extensions → compatible classes → 0 with its fibres H¹(𝒟⁰)-torsors.
// The automorphisms of a biaffine extension are H⁰(𝒟⁰).

package biaffine_deformation

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/algebra_deformation"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/cotangent_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/cotangent_examples"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/square_zero_classification"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/partial_derivative"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_localization"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/square_zero_extension"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The spelling of the statements over a base P
// ---------------------------------------------------------------------------

// wg3Glued binds a biaffine extension (E₀, t₀, E₁, t₁, φ), its chart
// rings on the types I and H, and wg3GluedOther a second one on G and F;
// wg3First and wg3Second spell them as arguments.
const (
	wg3Glued = "∀E₀:square_zero_ops(A, C, I, D). ∀t₀:I. ∀E₁:square_zero_ops(A, " +
		"C, H, D). ∀t₁:H. ∀φ:(set(prod(I, I)) → set(prod(H, H))). "
	wg3GluedOther = "∀E₀':square_zero_ops(A, C, G, D). ∀t₀':G. " +
		"∀E₁':square_zero_ops(A, C, F, D). ∀t₁':F. ∀φ':(set(prod(G, G)) → set(prod(F, F))). "
	wg3First  = "E₀, t₀, E₁, t₁, φ"
	wg3Second = "E₀', t₀', E₁', t₁', φ'"
)

// wg3Extension says the five parts glued are a biaffine extension over
// the base P through h; wg3Isomorphism that ψ₀ and ψ₁ are an isomorphism
// of biaffine extensions over P from src to tgt.
func wg3Extension(P, h, glued string) string {
	return "biaffine_extension(" + P + ", " + h + ", A₀₁, A₀, A₁, t, s, V, M, " + glued + ")"
}

func wg3Isomorphism(P, src, tgt, ψ0, ψ1 string) string {
	return "biaffine_isomorphism(" + P + ", A₀₁, V, M, " + src + ", " + tgt + ", " + ψ0 + ", " + ψ1 + ")"
}

// ---------------------------------------------------------------------------
// The derivation pair
// ---------------------------------------------------------------------------

// DerivationPairIsLattice — when both charts are finitely generated over
// the base, the derivation pair is a lattice pair in the derivations of
// the overlap, and its ambient is all of them.
var DerivationPairIsLattice = derivationPairIsLatticeThm{family.Add(registry.ProofEntry{
	Name: "DerivationPairIsLattice",
	Key:  "prop_cbc95f2a2401c650",
	Reading: "Finite generation is load-bearing for the ambient: a derivation d of the " +
		"overlap takes the finitely many generators of A₀ into M₀₁, one power tⁿ brings all " +
		"their values into M₀, and the Leibniz rule carries that power to the ring they generate " +
		"with the image of P, so tⁿ · d lies in chart 0 and d = sⁿ · (tⁿ · d) in its span. " +
		"Without it a chart need not be brought into M₀ by one power. Each chart is a submodule " +
		"over its own ring because a • d carries A₀ into a • M₀ ⊆ M₀ for a in A₀. The generators " +
		"generate A₀ only together with h(P), so d killing h(P) is load-bearing too. The ambient " +
		"is the whole carrier of the derivations only because its members are V.zero off A₀₁.",
	Deps: []registry.EntryLike{
		biaffineOverlapDerivationsDef,
		biaffineDerivationPairDef,
		lattice_pair.LatticePairDef,
		lattice_pair.LatticePairAmbientDef,
		lattice_pair.LatticePairByPowers,
		lattice_pair.ChartSpanAway,
		lattice_pair.BiaffineSwap,
		lattice_pair.AmbientContains,
		lattice_pair.BiaffineDef,
		partial_derivative.DerivationOn,
		module.ModuleOn,
		submodule.SubmoduleDef,
		submodule.SpanLeast,
		submodule.SubsetSpan,
		submodule.SpanSubmodule,
		comm_ring.CommRingOn,
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
			"biaffine(A₀₁, A₀, A₁, t, s)",
			"lattice_pair(A₀₁, A₀, A₁, V, M)",
			"ring_homomorphism(P, A₀₁, h)",
			"image(h, P.carrier) ⊆ A₀ ∩ A₁",
			"∃K:set(C). " +
				"    finite(K) ∧ " +
				"    K ⊆ A₀ ∧ " +
				"    (∀Q:set(C). comm_ring_on(restrict_ring(A₀₁, Q)) ∧ image(h, P.carrier) ⊆ Q ∧ K ⊆ Q ⇒ A₀ ⊆ Q)",
			"∃K:set(C). " +
				"    finite(K) ∧ " +
				"    K ⊆ A₁ ∧ " +
				"    (∀Q:set(C). comm_ring_on(restrict_ring(A₀₁, Q)) ∧ image(h, P.carrier) ⊆ Q ∧ K ⊆ Q ⇒ A₁ ⊆ Q)",
		},
		Conclusion: "lattice_pair(A₀₁, A₀, A₁, «wg3Derivations», «wg3Pair») ∧ " +
			"lattice_pair_ambient(A₀₁, «wg3Derivations», «wg3Pair») = «wg3Derivations».carrier",
	},
		"the derivations zero off A₀₁ are a module over A₀₁ under the pointwise operations, V "+
			"being one and M₀₁ a submodule (AmbientContains, DerivationOn, ModuleOn); each chart of "+
			"𝒟⁰ is a submodule over its chart ring (SubmoduleDef, the chart modules closed under A₀ "+
			"and A₁). For a derivation d of the overlap, ChartSpanAway at each of the finitely many "+
			"generators gives one n with tⁿ · d(k) in M₀ for every generator k; the members a of A₀ "+
			"with tⁿ · d(a) in M₀ are a subring holding h(P) (d kills it) and the generators, by "+
			"the Leibniz rule with coefficients in A₀, so all of A₀, and tⁿ · d lies in fst(𝒟⁰). "+
			"Then d = sⁿ · (tⁿ · d) lies in its span (SubsetSpan, SpanSubmodule), the same at chart "+
			"1 through BiaffineSwap: both spans are every derivation (SpanLeast), which is the "+
			"lattice-pair condition and the ambient (LatticePairDef, LatticePairAmbientDef)"),
})}

// ChartDerivationsExtend — the derivation pair is the pair of the charts'
// derivations: a derivation of a chart into its module extends by the
// quotient rule to exactly one member of that chart of 𝒟⁰ agreeing with
// it on the chart, and every member of the chart of 𝒟⁰ restricts to a
// derivation of the chart.
var ChartDerivationsExtend = chartDerivationsExtendThm{family.Add(registry.ProofEntry{
	Name: "ChartDerivationsExtend",
	Key:  "prop_cfea3a7d2305cabb",
	Reading: "This is the identification 𝒟⁰ = (Der(A₀, M₀), Der(A₁, M₁)) the chapter reads by " +
		"restriction: restriction and the quotient-rule extension are inverse between Der_P(A₀, " +
		"M₀) and fst(𝒟⁰). The overlap is the localization of each chart in place " +
		"(BiaffineChartLocalization), which is all DerivationExtendsUniquely asks; no finite " +
		"generation enters. So H⁰(𝒟⁰) is the derivations of the overlap restricting to derivations " +
		"of both charts, the derivations of the curve. The quotient rule accepts any denominator " +
		"in A₀ that is a unit of A₀₁, and is well defined because units act injectively on M₀₁.",
	Deps: []registry.EntryLike{
		biaffineDerivationPairDef,
		biaffineOverlapDerivationsDef,
		partial_derivative.DerivationExtendsUniquely,
		partial_derivative.DerivationOn,
		lattice_pair.BiaffineChartLocalization,
		lattice_pair.BiaffineSwap,
		lattice_pair.AmbientContains,
		lattice_pair.LatticePairDef,
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
			"biaffine(A₀₁, A₀, A₁, t, s)",
			"lattice_pair(A₀₁, A₀, A₁, V, M)",
			"ring_homomorphism(P, A₀₁, h)",
			"image(h, P.carrier) ⊆ A₀ ∩ A₁",
		},
		Conclusion: "(∀d:(C → D). " +
			"    derivation_on(P, restrict_ring(A₀₁, A₀), h, «wg3Module0», d) ⇒ " +
			"    (λy:C. " +
			"        COND(y ∈ A₀₁.carrier, " +
			"            derivation_localization(restrict_ring(A₀₁, A₀), A₀₁, λc:C. c, «wg3Overlap», d, y), " +
			"            V.zero)) ∈ " +
			"    fst(«wg3Pair») ∧ " +
			"    (∀a:C. " +
			"        a ∈ A₀ ⇒ " +
			"        derivation_localization(restrict_ring(A₀₁, A₀), A₀₁, λc:C. c, «wg3Overlap», d, a) = " +
			"        d(a)) ∧ " +
			"    (∀e:(C → D). " +
			"        e ∈ fst(«wg3Pair») ∧ (∀a:C. a ∈ A₀ ⇒ e(a) = d(a)) ⇒ " +
			"        e = " +
			"        λy:C. " +
			"            COND(y ∈ A₀₁.carrier, " +
			"                derivation_localization(restrict_ring(A₀₁, A₀), " +
			"                    A₀₁, " +
			"                    λc:C. c, " +
			"                    «wg3Overlap», " +
			"                    d, " +
			"                    y), " +
			"                V.zero))) ∧ " +
			"(∀e:(C → D). " +
			"    e ∈ fst(«wg3Pair») ⇒ derivation_on(P, restrict_ring(A₀₁, A₀), h, «wg3Module0», e)) ∧ " +
			"(∀d:(C → D). " +
			"    derivation_on(P, restrict_ring(A₀₁, A₁), h, «wg3Module1», d) ⇒ " +
			"    (λy:C. " +
			"        COND(y ∈ A₀₁.carrier, " +
			"            derivation_localization(restrict_ring(A₀₁, A₁), A₀₁, λc:C. c, «wg3Overlap», d, y), " +
			"            V.zero)) ∈ " +
			"    snd(«wg3Pair») ∧ " +
			"    (∀a:C. " +
			"        a ∈ A₁ ⇒ " +
			"        derivation_localization(restrict_ring(A₀₁, A₁), A₀₁, λc:C. c, «wg3Overlap», d, a) = " +
			"        d(a)) ∧ " +
			"    (∀e:(C → D). " +
			"        e ∈ snd(«wg3Pair») ∧ (∀a:C. a ∈ A₁ ⇒ e(a) = d(a)) ⇒ " +
			"        e = " +
			"        λy:C. " +
			"            COND(y ∈ A₀₁.carrier, " +
			"                derivation_localization(restrict_ring(A₀₁, A₁), " +
			"                    A₀₁, " +
			"                    λc:C. c, " +
			"                    «wg3Overlap», " +
			"                    d, " +
			"                    y), " +
			"                V.zero))) ∧ " +
			"(∀e:(C → D). e ∈ snd(«wg3Pair») ⇒ derivation_on(P, restrict_ring(A₀₁, A₁), h, «wg3Module1», e))",
	},
		"A₀₁ is the localization of each chart at the powers of its element in place "+
			"(BiaffineChartLocalization), and M₀₁ a module over it holding both chart modules "+
			"(AmbientContains); a derivation of A₀ into M₀ is one into M₀₁ read over A₀. "+
			"DerivationExtendsUniquely gives its extension, a derivation of the overlap agreeing "+
			"with it on A₀ and the only one there; the COND makes it zero off A₀₁, so it is a "+
			"member of the derivations (biaffineOverlapDerivationsDef) carrying A₀ into M₀ "+
			"(biaffineDerivationPairDef), and two members agreeing on A₀ are equal off A₀₁ too. A "+
			"member of fst(𝒟⁰) restricted to A₀ keeps the Leibniz rule and kills h(P) ⊆ A₀, its "+
			"values in M₀ (DerivationOn). Chart 1 is the same at the exchanged datum (BiaffineSwap)"),
})}

// ---------------------------------------------------------------------------
// The split extensions glued by a shear
// ---------------------------------------------------------------------------

// GluedTrivialIsExtension — for a derivation d of the overlap over the
// base, the split extensions of the two charts with the lifts (t, 0) and
// (s, 0), glued by the shear of d, are a biaffine extension.
var GluedTrivialIsExtension = gluedTrivialIsExtensionThm{family.Add(registry.ProofEntry{
	Name: "GluedTrivialIsExtension",
	Key:  "prop_2fae68b5d1cf66a",
	Reading: "d is a derivation over the base: the shear fixes the structure map (h(a), 0) exactly " +
		"because d kills h(P). At d = 0 this is the trivial biaffine extension, the base point of the " +
		"classification. (t, 0) lies in A₀ ⋉ M₀ over t, so it is a lift, and the localizations at (t, " +
		"0) and (s, 0) are both A₀₁ ⋉ M₀₁ through the reading of SplitSquareZeroLocalization.",
	Deps: []registry.EntryLike{
		BiaffineExtensionDef,
		biaffineShearGluingDef,
		biaffineOverlapDerivationsDef,
		square_zero_extension.SplitSquareZeroLocalization,
		square_zero_extension.DerivationShearAutomorphism,
		square_zero_extension.SplitSquareZeroRing,
		square_zero_extension.SquareZeroIsomorphismDef,
		square_zero_extension.SpanIsModuleLocalization,
		algebra_deformation.SplitExtensionClassZero,
		lattice_pair.BiaffineChartLocalization,
		lattice_pair.LatticePairDef,
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
			"∀d:(C → D).",
		Hypotheses: []string{
			"biaffine(A₀₁, A₀, A₁, t, s)",
			"lattice_pair(A₀₁, A₀, A₁, V, M)",
			"ring_homomorphism(P, A₀₁, h)",
			"image(h, P.carrier) ⊆ A₀ ∩ A₁",
			"d ∈ biaffine_overlap_derivations(P, h, A₀₁, V, M).carrier",
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
			"    mk_square_zero( " +
			"        split_square_zero(restrict_ring(A₀₁, A₀), λy:C. y, restrict_module(V, fst(M))), " +
			"        λa:A. (h(a), V.zero), " +
			"        λn:D. (A₀₁.zero, n), " +
			"        λz:prod(C, D). fst(z)), " +
			"    (t, V.zero), " +
			"    mk_square_zero( " +
			"        split_square_zero(restrict_ring(A₀₁, A₁), λy:C. y, restrict_module(V, snd(M))), " +
			"        λa:A. (h(a), V.zero), " +
			"        λn:D. (A₀₁.zero, n), " +
			"        λz:prod(C, D). fst(z)), " +
			"    (s, V.zero), " +
			"    biaffine_shear_gluing(A₀₁, A₁, s, V, M, d))",
	},
		"the split extensions are extensions of the charts by their modules over P "+
			"(SplitExtensionClassZero's first conjunct, SplitSquareZeroRing), and (t, 0), (s, 0) lift t "+
			"and s. The reading ι of a class of fractions in A₀₁ ⋉ M₀₁ is an isomorphism of extensions "+
			"from each localization (SplitSquareZeroLocalization at the chart rings, A₀₁ a localization of "+
			"each by BiaffineChartLocalization and M₀₁ of each chart module by SpanIsModuleLocalization); "+
			"the shear by d is an automorphism of A₀₁ ⋉ M₀₁ over P fixing (0, n) and the first component "+
			"(DerivationShearAutomorphism). So ι₁⁻¹ ∘ shear ∘ ι₀, the inverse taken by inverse_on "+
			"(InverseOnLeft, InverseOnRight, InverseOnIn), is an isomorphism of extensions "+
			"(SquareZeroIsomorphismDef), and that is biaffine_shear_gluing (biaffineShearGluingDef)"),
})}

// GluedTrivialIsoIffCoboundary — the split extensions glued by the shears
// of d and of d' are isomorphic biaffine extensions exactly when d − d'
// lies in fst(𝒟⁰) + snd(𝒟⁰); when d = d' + d₀ + d₁ the shears of the two
// charts by d₀ and by −d₁ are an isomorphism.
var GluedTrivialIsoIffCoboundary = gluedTrivialIsoIffCoboundaryThm{family.Add(registry.ProofEntry{
	Name: "GluedTrivialIsoIffCoboundary",
	Key:  "prop_fe335c4b110fbc0c",
	Reading: "This is injectivity of H¹(𝒟⁰) → biaffine extensions: the classes of d and d' in " +
		"H¹(𝒟⁰), ambient modulo fst(𝒟⁰) + snd(𝒟⁰), agree exactly when the glued extensions are " +
		"isomorphic. The automorphisms of a split chart extension are the shears by the chart's " +
		"derivations (DeformationAutomorphisms), which localize to the shears by their extensions, " +
		"members of 𝒟⁰ (ChartDerivationsExtend); shears compose by the sum, so φ_{d'} ∘ loc(shear " +
		"d₀) = loc(shear d₁') ∘ φ_d says d' + d₀ = d + d₁'. The sign is load-bearing: ψ₁ is the " +
		"shear by −d₁, and the square reads σ_{d'+d₀} = σ_{d−d₁}, which is d = d' + d₀ + d₁.",
	Deps: []registry.EntryLike{
		GluedTrivialIsExtension,
		ChartDerivationsExtend,
		BiaffineIsomorphismDef,
		biaffineShearGluingDef,
		square_zero_extension.DerivationShearAutomorphism,
		square_zero_extension.SplitSquareZeroLocalization,
		algebra_deformation.DeformationAutomorphisms,
		ring_localization.LocalizationHomomorphismExtensional,
		module_extension.DerivationShearDef,
	},
	Build: family.Card(Statement{
		Binders: "∀P:ring_ops(A). " +
			"∀h:(A → C). " +
			"∀A₀₁:ring_ops(C). " +
			"∀A₀ A₁:set(C). " +
			"∀t s:C. " +
			"∀V:module_ops(C, D). " +
			"∀M:prod(set(D), set(D)). " +
			"∀d d':(C → D).",
		Hypotheses: []string{
			"biaffine(A₀₁, A₀, A₁, t, s)",
			"lattice_pair(A₀₁, A₀, A₁, V, M)",
			"ring_homomorphism(P, A₀₁, h)",
			"image(h, P.carrier) ⊆ A₀ ∩ A₁",
			"d ∈ biaffine_overlap_derivations(P, h, A₀₁, V, M).carrier",
			"d' ∈ biaffine_overlap_derivations(P, h, A₀₁, V, M).carrier",
		},
		Conclusion: "((∃ψ₀ ψ₁:(prod(C, D) → prod(C, D)). " +
			"        biaffine_isomorphism(P, " +
			"            A₀₁, " +
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
			"            biaffine_shear_gluing(A₀₁, A₁, s, V, M, d), " +
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
			"            biaffine_shear_gluing(A₀₁, A₁, s, V, M, d'), " +
			"            ψ₀, " +
			"            ψ₁)) ⇔ " +
			"    biaffine_overlap_derivations(P, h, A₀₁, V, M).add(d, " +
			"        biaffine_overlap_derivations(P, h, A₀₁, V, M).neg(d')) ∈ " +
			"    set_mul(biaffine_overlap_derivations(P, h, A₀₁, V, M).add, " +
			"        fst(biaffine_derivation_pair(P, h, A₀₁, A₀, A₁, V, M)), " +
			"        snd(biaffine_derivation_pair(P, h, A₀₁, A₀, A₁, V, M)))) ∧ " +
			"(∀d₀ d₁:(C → D). " +
			"    d₀ ∈ fst(biaffine_derivation_pair(P, h, A₀₁, A₀, A₁, V, M)) ∧ " +
			"    d₁ ∈ snd(biaffine_derivation_pair(P, h, A₀₁, A₀, A₁, V, M)) ∧ " +
			"    d = " +
			"    biaffine_overlap_derivations(P, h, A₀₁, V, M).add(d', " +
			"        biaffine_overlap_derivations(P, h, A₀₁, V, M).add(d₀, d₁)) ⇒ " +
			"    biaffine_isomorphism(P, " +
			"        A₀₁, " +
			"        V, " +
			"        M, " +
			"        mk_square_zero( " +
			"            split_square_zero(restrict_ring(A₀₁, A₀), λy:C. y, restrict_module(V, fst(M))), " +
			"            λa:A. (h(a), V.zero), " +
			"            λn:D. (A₀₁.zero, n), " +
			"            λz:prod(C, D). fst(z)), " +
			"        (t, V.zero), " +
			"        mk_square_zero( " +
			"            split_square_zero(restrict_ring(A₀₁, A₁), λy:C. y, restrict_module(V, snd(M))), " +
			"            λa:A. (h(a), V.zero), " +
			"            λn:D. (A₀₁.zero, n), " +
			"            λz:prod(C, D). fst(z)), " +
			"        (s, V.zero), " +
			"        biaffine_shear_gluing(A₀₁, A₁, s, V, M, d), " +
			"        mk_square_zero( " +
			"            split_square_zero(restrict_ring(A₀₁, A₀), λy:C. y, restrict_module(V, fst(M))), " +
			"            λa:A. (h(a), V.zero), " +
			"            λn:D. (A₀₁.zero, n), " +
			"            λz:prod(C, D). fst(z)), " +
			"        (t, V.zero), " +
			"        mk_square_zero( " +
			"            split_square_zero(restrict_ring(A₀₁, A₁), λy:C. y, restrict_module(V, snd(M))), " +
			"            λa:A. (h(a), V.zero), " +
			"            λn:D. (A₀₁.zero, n), " +
			"            λz:prod(C, D). fst(z)), " +
			"        (s, V.zero), " +
			"        biaffine_shear_gluing(A₀₁, A₁, s, V, M, d'), " +
			"        λz:prod(C, D). derivation_shear(restrict_module(V, fst(M)), d₀, z), " +
			"        λz:prod(C, D). derivation_shear(restrict_module(V, snd(M)), λu:C. V.neg(d₁(u)), z)))",
	},
		"⇐ is the second conjunct: d₀ restricted to A₀ is a derivation of the chart "+
			"(ChartDerivationsExtend), so its shear is an automorphism of A₀ ⋉ M₀ over P, the identity "+
			"on M₀ and over A₀ (DerivationShearAutomorphism), and so is the shear of A₁ ⋉ M₁ by −d₁. "+
			"Their maps of localizations read, through the readings of SplitSquareZeroLocalization, as "+
			"the shears of A₀₁ ⋉ M₀₁ by d₀ and by −d₁, two ring maps out of a localization agreeing on "+
			"the classes e/1 (LocalizationHomomorphismExtensional); shears compose by the sum "+
			"(DerivationShearDef), and d' + d₀ = d − d₁ is the hypothesis, so the square of "+
			"BiaffineIsomorphismDef commutes. ⇒: an isomorphism's chart maps are automorphisms of the "+
			"split extensions, so shears by chart derivations e₀, e₁ (DeformationAutomorphisms with "+
			"the identity thickening), and the square gives d − d' = e₀ − e₁ on A₀₁, both sides zero "+
			"off it, with e₀ in fst(𝒟⁰) and −e₁ in snd(𝒟⁰) after extension (ChartDerivationsExtend)"),
})}

// LocallyTrivialIsH1D0 — the extensions split on each chart are H¹(𝒟⁰):
// the split extensions have chart classes zero, and every biaffine
// extension whose chart classes are zero is isomorphic to the split
// extensions glued by the shear of some derivation of the overlap.
var LocallyTrivialIsH1D0 = locallyTrivialIsH1D0Thm{family.Add(registry.ProofEntry{
	Name: "LocallyTrivialIsH1D0",
	Key:  "prop_e740887278bedfe6",
	Reading: "With GluedTrivialIsoIffCoboundary this is the bijection H¹(𝒟⁰) → {biaffine extensions " +
		"with zero chart classes} / ≅, the class of d going to the split extensions glued by the shear " +
		"of d: the kernel of the chart-class map, the first map of ExalSequence. The universes are those " +
		"the chart classes read. An isomorphism of chart extensions changes nothing the gluing sees, so " +
		"the gluing of an extension that splits on both charts is an automorphism of A₀₁ ⋉ M₀₁, a shear. " +
		"No universe for the overlap is needed, the gluing being read directly as that shear.",
	Deps: []registry.EntryLike{
		GluedTrivialIsExtension,
		biaffineLocalClassDef,
		BiaffineIsomorphismDef,
		algebra_deformation.SplitExtensionClassZero,
		algebra_deformation.DeformationAutomorphisms,
		square_zero_extension.SplitSquareZeroLocalization,
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
			"∀M:prod(set(D), set(D)).",
		Hypotheses: []string{
			"cotangent_universe(P, 𝕌⟨A:U⟩)",
			"cotangent_universe(restrict_ring(A₀₁, A₀), 𝕌⟨A:U⟩)",
			"cotangent_universe(restrict_ring(A₀₁, A₁), 𝕌⟨A:U⟩)",
			"biaffine(A₀₁, A₀, A₁, t, s)",
			"lattice_pair(A₀₁, A₀, A₁, V, M)",
			"ring_homomorphism(P, A₀₁, h)",
			"image(h, P.carrier) ⊆ A₀ ∩ A₁",
		},
		Conclusion: "biaffine_local_class⟨U:U⟩(P, " +
			"    h, " +
			"    A₀₁, " +
			"    A₀, " +
			"    A₁, " +
			"    V, " +
			"    M, " +
			"    mk_square_zero( " +
			"        split_square_zero(restrict_ring(A₀₁, A₀), λy:C. y, restrict_module(V, fst(M))), " +
			"        λa:A. (h(a), V.zero), " +
			"        λn:D. (A₀₁.zero, n), " +
			"        λz:prod(C, D). fst(z)), " +
			"    mk_square_zero( " +
			"        split_square_zero(restrict_ring(A₀₁, A₁), λy:C. y, restrict_module(V, snd(M))), " +
			"        λa:A. (h(a), V.zero), " +
			"        λn:D. (A₀₁.zero, n), " +
			"        λz:prod(C, D). fst(z))) = " +
			"(cotangent_cohomology(P, " +
			"        restrict_ring(A₀₁, A₀), " +
			"        h, " +
			"        restrict_ring(A₀₁, A₀), " +
			"        λc:C. c, " +
			"        restrict_module(V, fst(M)), " +
			"        1).zero, " +
			"    cotangent_cohomology(P, " +
			"        restrict_ring(A₀₁, A₁), " +
			"        h, " +
			"        restrict_ring(A₀₁, A₁), " +
			"        λc:C. c, " +
			"        restrict_module(V, snd(M)), " +
			"        1).zero) ∧ " +
			"(∀E₀:square_zero_ops(A, C, I, D). " +
			"∀t₀:I. " +
			"∀E₁:square_zero_ops(A, C, H, D). " +
			"∀t₁:H. " +
			"∀φ:(set(prod(I, I)) → set(prod(H, H))). " +
			"    biaffine_extension(P, h, A₀₁, A₀, A₁, t, s, V, M, E₀, t₀, E₁, t₁, φ) ∧ " +
			"    biaffine_local_class⟨U:U⟩(P, h, A₀₁, A₀, A₁, V, M, E₀, E₁) = " +
			"    (cotangent_cohomology(P, " +
			"            restrict_ring(A₀₁, A₀), " +
			"            h, " +
			"            restrict_ring(A₀₁, A₀), " +
			"            λc:C. c, " +
			"            restrict_module(V, fst(M)), " +
			"            1).zero, " +
			"        cotangent_cohomology(P, " +
			"            restrict_ring(A₀₁, A₁), " +
			"            h, " +
			"            restrict_ring(A₀₁, A₁), " +
			"            λc:C. c, " +
			"            restrict_module(V, snd(M)), " +
			"            1).zero) ⇒ " +
			"    ∃d:(C → D). " +
			"        d ∈ biaffine_overlap_derivations(P, h, A₀₁, V, M).carrier ∧ " +
			"        (∃ψ₀:(prod(C, D) → I). ∃ψ₁:(prod(C, D) → H). " +
			"            biaffine_isomorphism(P, " +
			"                A₀₁, " +
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
			"                biaffine_shear_gluing(A₀₁, A₁, s, V, M, d), " +
			"                E₀, " +
			"                t₀, " +
			"                E₁, " +
			"                t₁, " +
			"                φ, " +
			"                ψ₀, " +
			"                ψ₁)))",
	},
		"a split extension has a section, so class zero (SplitExtensionClassZero). Conversely class "+
			"zero gives isomorphisms χ₀, χ₁ from the split extensions onto E₀ and E₁ "+
			"(SplitExtensionClassZero's last clause). Read through the readings ι₀, ι₁ of "+
			"SplitSquareZeroLocalization, loc(χ₁)⁻¹ ∘ φ ∘ loc(χ₀) is an automorphism of A₀₁ ⋉ M₀₁ over P, "+
			"the identity on M₀₁ and over A₀₁, so the shear by a derivation d of the overlap over P "+
			"(DeformationAutomorphisms with the identity thickening), made zero off A₀₁; then (χ₀, χ₁) is "+
			"an isomorphism from the split extensions glued by the shear of d to E, the square checked on "+
			"the classes e/1 (LocalizationHomomorphismExtensional, InverseOnLeft, InverseOnRight)"),
})}

// ---------------------------------------------------------------------------
// The chart classes and the exact sequence
// ---------------------------------------------------------------------------

// LocalClassLandsInKernel — the pair of chart classes of a biaffine
// extension agrees on the overlap: it lies in the compatible classes.
var LocalClassLandsInKernel = localClassLandsInKernelThm{family.Add(registry.ProofEntry{
	Name: "LocalClassLandsInKernel",
	Key:  "prop_950fd3c32df179e9",
	Reading: "The class of a localization is the restriction of the class " +
		"(SquareZeroLocalizationClass), whatever lift it was taken at, and the gluing makes the two " +
		"localizations isomorphic, so of one class. The second map of ExalSequence is well defined " +
		"by this; the overlap's universe is asked because the restrictions are classes of the overlap.",
	Deps: []registry.EntryLike{
		BiaffineExtensionDef,
		biaffineLocalClassDef,
		biaffineCompatibleClassesDef,
		algebra_deformation.SquareZeroLocalizationClass,
		square_zero_classification.ExtensionClassWellDefined,
		square_zero_extension.SquareZeroLocalizationIsExtension,
		lattice_pair.BiaffineChartLocalization,
		square_zero_extension.SpanIsModuleLocalization,
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
			"cotangent_universe(P, 𝕌⟨A:U⟩)",
			"cotangent_universe(restrict_ring(A₀₁, A₀), 𝕌⟨A:U⟩)",
			"cotangent_universe(restrict_ring(A₀₁, A₁), 𝕌⟨A:U⟩)",
			"cotangent_universe(A₀₁, 𝕌⟨A:U⟩)",
			"biaffine_extension(P, h, A₀₁, A₀, A₁, t, s, V, M, E₀, t₀, E₁, t₁, φ)",
		},
		Conclusion: "«wg3LocalClass»(E₀, E₁) ∈ " +
			"biaffine_compatible_classes(P, h, A₀₁, A₀, A₁, V, M).carrier",
	},
		"each chart class lies in its D¹ (ExtensionClassWellDefined). A₀₁ is the localization of "+
			"each chart and M₀₁ of each chart module in place (BiaffineChartLocalization, "+
			"SpanIsModuleLocalization), so SquareZeroLocalizationClass makes the class of E₀ "+
			"localized at t₀ the restriction of E₀'s class, and the same at chart 1; φ is an "+
			"isomorphism of the two localizations, extensions of A₀₁ by M₀₁ over P "+
			"(SquareZeroLocalizationIsExtension), so their classes agree (ExtensionClassWellDefined), "+
			"and the pair satisfies the condition of biaffineCompatibleClassesDef"),
})}

// LocalClassOnto — two chart extensions whose classes agree on the
// overlap, with lifts of t and s, glue: some isomorphism of their
// localizations makes them a biaffine extension.
var LocalClassOnto = localClassOntoThm{family.Add(registry.ProofEntry{
	Name: "LocalClassOnto",
	Key:  "prop_5b45696a35be65b7",
	Reading: "The gluing exists but is not unique: any other differs from it by " +
		"an automorphism of the localization, a shear by a derivation of the overlap " +
		"(ExalSequence). The extensions may sit on any types; with the realizations " +
		"of a compatible pair of classes this is the surjectivity in ExalSequence.",
	Deps: []registry.EntryLike{
		BiaffineExtensionDef,
		algebra_deformation.SquareZeroLocalizationClass,
		square_zero_classification.ExtensionIsoIffSameClass,
		square_zero_extension.SquareZeroLocalizationIsExtension,
		lattice_pair.BiaffineChartLocalization,
		square_zero_extension.SpanIsModuleLocalization,
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
			"∀t₁:H.",
		Hypotheses: []string{
			"cotangent_universe(P, 𝕌⟨A:U⟩)",
			"cotangent_universe(restrict_ring(A₀₁, A₀), 𝕌⟨A:U⟩)",
			"cotangent_universe(restrict_ring(A₀₁, A₁), 𝕌⟨A:U⟩)",
			"cotangent_universe(A₀₁, 𝕌⟨A:U⟩)",
			"biaffine(A₀₁, A₀, A₁, t, s)",
			"lattice_pair(A₀₁, A₀, A₁, V, M)",
			"ring_homomorphism(P, A₀₁, h)",
			"image(h, P.carrier) ⊆ A₀ ∩ A₁",
			"square_zero_extension(P, restrict_ring(A₀₁, A₀), h, «wg3Module0», E₀)",
			"t₀ ∈ E₀.ring.carrier",
			"E₀.projection(t₀) = t",
			"square_zero_extension(P, restrict_ring(A₀₁, A₁), h, «wg3Module1», E₁)",
			"t₁ ∈ E₁.ring.carrier",
			"E₁.projection(t₁) = s",
			"«wg3Restriction0»(square_zero_class⟨U:U⟩(P, restrict_ring(A₀₁, A₀), h, «wg3Module0», E₀)) = " +
				"«wg3Restriction1»(square_zero_class(P, restrict_ring(A₀₁, A₁), h, «wg3Module1», E₁))",
		},
		Conclusion: "∃φ:(set(prod(I, I)) → set(prod(H, H))). " +
			"    biaffine_extension(P, h, A₀₁, A₀, A₁, t, s, V, M, E₀, t₀, E₁, t₁, φ)",
	},
		"the localizations of E₀ at t₀ and of E₁ at t₁ are extensions of A₀₁ by M₀₁ over P "+
			"(SquareZeroLocalizationIsExtension, in place by BiaffineChartLocalization and "+
			"SpanIsModuleLocalization), their classes the restrictions of the chart classes "+
			"(SquareZeroLocalizationClass), equal by hypothesis; ExtensionIsoIffSameClass gives "+
			"an isomorphism φ between them, which with the hypotheses is BiaffineExtensionDef"),
})}

// ExalSequence — the extensions of the curve over P: every compatible
// pair of chart classes is the pair of some biaffine extension; a
// gluing moved by a derivation of the overlap is again one; two biaffine
// extensions with one pair of chart classes are, up to isomorphism, one
// regluing of the other; and two regluings of one are isomorphic exactly
// when the derivations differ by fst(𝒟⁰) + snd(𝒟⁰).
var ExalSequence = exalSequenceThm{family.Add(registry.ProofEntry{
	Name: "ExalSequence",
	Key:  "prop_cfb86ddc92739550",
	Reading: "The sequence 0 → H¹(𝒟⁰) → biaffine extensions / ≅ → compatible classes → 0 at " +
		"the level of sets, with every map and action named: the chart classes " +
		"(LocalClassLandsInKernel) onto the compatible pairs (first conjunct), each fibre an " +
		"H¹(𝒟⁰)-torsor under regluing (the last three), the fibre over zero the split extensions " +
		"glued by shears (LocallyTrivialIsH1D0, GluedTrivialIsoIffCoboundary). Its group form, " +
		"the Baer sum making the isomorphism classes a group, is ExalSequenceExact. The " +
		"extension the first conjunct asks for exists at the realizations' type set(prod(U, D)).",
	Deps: []registry.EntryLike{
		LocalClassOnto,
		LocalClassLandsInKernel,
		LocallyTrivialIsH1D0,
		GluedTrivialIsoIffCoboundary,
		ChartDerivationsExtend,
		biaffineRegluingDef,
		BiaffineIsomorphismDef,
		square_zero_classification.ExtensionRealizeClass,
		square_zero_classification.ExtensionIsoIffSameClass,
		algebra_deformation.DeformationAutomorphisms,
		square_zero_extension.SquareZeroLocalizationIsExtension,
		square_zero_extension.SquareZeroIsomorphismDef,
		ring_localization.LocalizationHomomorphismExtensional,
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
		Conclusion: "(∀z:prod(set(U → D), set(U → D)). " +
			"    z ∈ biaffine_compatible_classes(P, h, A₀₁, A₀, A₁, V, M).carrier ⇒ " +
			"    ∃E₀:square_zero_ops(A, C, set(prod(U, D)), D). " +
			"    ∃t₀:set(prod(U, D)). " +
			"    ∃E₁:square_zero_ops(A, C, set(prod(U, D)), D). " +
			"    ∃t₁:set(prod(U, D)). " +
			"    ∃φ:(set(prod(set(prod(U, D)), set(prod(U, D)))) → " +
			"            set(prod(set(prod(U, D)), set(prod(U, D))))). " +
			"        biaffine_extension(P, h, A₀₁, A₀, A₁, t, s, V, M, E₀, t₀, E₁, t₁, φ) ∧ " +
			"        biaffine_local_class(P, h, A₀₁, A₀, A₁, V, M, E₀, E₁) = z) ∧ " +
			"(∀E₀:square_zero_ops(A, C, I, D). " +
			"∀t₀:I. " +
			"∀E₁:square_zero_ops(A, C, H, D). " +
			"∀t₁:H. " +
			"∀φ:(set(prod(I, I)) → set(prod(H, H))). " +
			"∀d:(C → D). " +
			"    biaffine_extension(P, h, A₀₁, A₀, A₁, t, s, V, M, E₀, t₀, E₁, t₁, φ) ∧ " +
			"    d ∈ «wg3Derivations».carrier ⇒ " +
			"    biaffine_extension(P, " +
			"        h, " +
			"        A₀₁, " +
			"        A₀, " +
			"        A₁, " +
			"        t, " +
			"        s, " +
			"        V, " +
			"        M, " +
			"        E₀, " +
			"        t₀, " +
			"        E₁, " +
			"        t₁, " +
			"        biaffine_regluing(A₀₁, V, M, E₀, t₀, φ, d))) ∧ " +
			"(∀E₀:square_zero_ops(A, C, I, D). " +
			"∀t₀:I. " +
			"∀E₁:square_zero_ops(A, C, H, D). " +
			"∀t₁:H. " +
			"∀φ:(set(prod(I, I)) → set(prod(H, H))). " +
			"∀E_0':square_zero_ops(A, C, G, D). " +
			"∀t_0':G. " +
			"∀E_1':square_zero_ops(A, C, F, D). " +
			"∀t_1':F. " +
			"∀φ':(set(prod(G, G)) → set(prod(F, F))). " +
			"    biaffine_extension(P, h, A₀₁, A₀, A₁, t, s, V, M, E₀, t₀, E₁, t₁, φ) ∧ " +
			"    biaffine_extension(P, h, A₀₁, A₀, A₁, t, s, V, M, E_0', t_0', E_1', t_1', φ') ∧ " +
			"    «wg3LocalClass»(E₀, E₁) = biaffine_local_class(P, h, A₀₁, A₀, A₁, V, M, E_0', E_1') ⇒ " +
			"    ∃d:(C → D). " +
			"        d ∈ «wg3Derivations».carrier ∧ " +
			"        (∃ψ₀:(I → G). ∃ψ₁:(H → F). " +
			"            biaffine_isomorphism(P, " +
			"                A₀₁, " +
			"                V, " +
			"                M, " +
			"                E₀, " +
			"                t₀, " +
			"                E₁, " +
			"                t₁, " +
			"                biaffine_regluing(A₀₁, V, M, E₀, t₀, φ, d), " +
			"                E_0', " +
			"                t_0', " +
			"                E_1', " +
			"                t_1', " +
			"                φ', " +
			"                ψ₀, " +
			"                ψ₁))) ∧ " +
			"(∀E₀:square_zero_ops(A, C, I, D). " +
			"∀t₀:I. " +
			"∀E₁:square_zero_ops(A, C, H, D). " +
			"∀t₁:H. " +
			"∀φ:(set(prod(I, I)) → set(prod(H, H))). " +
			"∀d d':(C → D). " +
			"    biaffine_extension(P, h, A₀₁, A₀, A₁, t, s, V, M, E₀, t₀, E₁, t₁, φ) ∧ " +
			"    d ∈ «wg3Derivations».carrier ∧ " +
			"    d' ∈ «wg3Derivations».carrier ⇒ " +
			"    ((∃ψ₀:(I → I). ∃ψ₁:(H → H). " +
			"            biaffine_isomorphism(P, " +
			"                A₀₁, " +
			"                V, " +
			"                M, " +
			"                E₀, " +
			"                t₀, " +
			"                E₁, " +
			"                t₁, " +
			"                biaffine_regluing(A₀₁, V, M, E₀, t₀, φ, d), " +
			"                E₀, " +
			"                t₀, " +
			"                E₁, " +
			"                t₁, " +
			"                biaffine_regluing(A₀₁, V, M, E₀, t₀, φ, d'), " +
			"                ψ₀, " +
			"                ψ₁)) ⇔ " +
			"        «wg3Derivations».add(d, «wg3Derivations».neg(d')) ∈ " +
			"        set_mul(«wg3Derivations».add, fst(«wg3Pair»), snd(«wg3Pair»))))",
	},
		"onto: the realizations of a compatible pair are chart extensions with those classes "+
			"(ExtensionRealizeClass), each with a lift of t or s (its projection onto), and LocalClassOnto "+
			"glues them. Regluing: x ↦ x − i(d(p(x))) is an automorphism of the localization of E₀ over P, "+
			"the identity on M₀₁ and over A₀₁, d killing h(P) (DeformationAutomorphisms with the identity "+
			"thickening), so φ after it is an isomorphism (SquareZeroIsomorphismDef). Fibres: equal chart "+
			"classes give isomorphisms ψ₀, ψ₁ of the chart extensions (ExtensionIsoIffSameClass); φ⁻¹ ∘ "+
			"loc(ψ₁)⁻¹ ∘ φ' ∘ loc(ψ₀) is an automorphism of the localization of E₀, a shear by some d, "+
			"which is the isomorphism's square for the regluing by d. Freeness: an isomorphism between two "+
			"regluings of E is a pair of automorphisms of E₀ and E₁, shears by chart derivations whose "+
			"localizations are the shears by their extensions in 𝒟⁰ (ChartDerivationsExtend, checked on "+
			"the classes e/1 by LocalizationHomomorphismExtensional); φ commutes with shears and shears "+
			"compose by the sum, so the square says d − d' = e₀ − e₁"),
})}

// BiaffineAutomorphisms — the automorphisms of a biaffine extension are
// H⁰(𝒟⁰): a derivation of the overlap carrying both charts into their
// modules shears both chart extensions compatibly, every automorphism is
// such a pair of shears, the derivation is determined by it, and the
// shears compose by the sum.
var BiaffineAutomorphisms = biaffineAutomorphismsThm{family.Add(registry.ProofEntry{
	Name: "BiaffineAutomorphisms",
	Key:  "prop_277be560f83392",
	Reading: "No smoothness and no universe: an automorphism of a chart extension over P, the " +
		"identity on the module and over the chart, is a shear by a derivation of the chart, and " +
		"the gluing asks the two derivations to agree on the overlap, where each extends uniquely. " +
		"For a deformation over a thickening R → R₀ with f onto, the derivations over R through g " +
		"∘ f are those over R₀ through g (ThickeningDerivationsAgree), so the automorphisms of a " +
		"deformation are H⁰ of the derivation pair over R₀. The derivation is fixed by its shear " +
		"on A₀ through the injective inclusion and the projection onto A₀, on A₀₁ by the " +
		"uniqueness of the quotient-rule extension, and off A₀₁ because it is zero off the carrier.",
	Deps: []registry.EntryLike{
		BiaffineIsomorphismDef,
		BiaffineExtensionDef,
		ChartDerivationsExtend,
		algebra_deformation.DeformationAutomorphisms,
		square_zero_extension.SquareZeroLocalizationIsExtension,
		square_zero_extension.SquareZeroIsomorphismDef,
		ring_localization.LocalizationHomomorphismExtensional,
		lattice_pair.LatticePairH0Def,
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
			"biaffine_extension(P, h, A₀₁, A₀, A₁, t, s, V, M, E₀, t₀, E₁, t₁, φ)",
		},
		Conclusion: "(∀d:(C → D). " +
			"    d ∈ lattice_pair_h0(«wg3Derivations», «wg3Pair»).carrier ⇒ " +
			"    biaffine_isomorphism(P, " +
			"        A₀₁, " +
			"        V, " +
			"        M, " +
			"        E₀, " +
			"        t₀, " +
			"        E₁, " +
			"        t₁, " +
			"        φ, " +
			"        E₀, " +
			"        t₀, " +
			"        E₁, " +
			"        t₁, " +
			"        φ, " +
			"        λe:I. E₀.ring.sub(e, E₀.inclusion(d(E₀.projection(e)))), " +
			"        λe:H. E₁.ring.sub(e, E₁.inclusion(d(E₁.projection(e)))))) ∧ " +
			"(∀ψ₀:(I → I). ∀ψ₁:(H → H). " +
			"    biaffine_isomorphism(P, A₀₁, V, M, E₀, t₀, E₁, t₁, φ, E₀, t₀, E₁, t₁, φ, ψ₀, ψ₁) ⇒ " +
			"    ∃d:(C → D). " +
			"        d ∈ lattice_pair_h0(«wg3Derivations», «wg3Pair»).carrier ∧ " +
			"        (∀e:I. " +
			"            e ∈ E₀.ring.carrier ⇒ ψ₀(e) = E₀.ring.sub(e, E₀.inclusion(d(E₀.projection(e))))) ∧ " +
			"        (∀e:H. " +
			"            e ∈ E₁.ring.carrier ⇒ ψ₁(e) = E₁.ring.sub(e, E₁.inclusion(d(E₁.projection(e)))))) ∧ " +
			"(∀d d':(C → D). " +
			"    d ∈ lattice_pair_h0(«wg3Derivations», «wg3Pair»).carrier ∧ " +
			"    d' ∈ lattice_pair_h0(«wg3Derivations», «wg3Pair»).carrier ∧ " +
			"    (∀e:I. " +
			"        e ∈ E₀.ring.carrier ⇒ " +
			"        E₀.ring.sub(e, E₀.inclusion(d(E₀.projection(e)))) = " +
			"        E₀.ring.sub(e, E₀.inclusion(d'(E₀.projection(e))))) ⇒ " +
			"    d = d') ∧ " +
			"(∀d d':(C → D). " +
			"    d ∈ lattice_pair_h0(«wg3Derivations», «wg3Pair»).carrier ∧ " +
			"    d' ∈ lattice_pair_h0(«wg3Derivations», «wg3Pair»).carrier ⇒ " +
			"    ∀e:I. " +
			"        e ∈ E₀.ring.carrier ⇒ " +
			"        E₀.ring.sub(E₀.ring.sub(e, E₀.inclusion(d'(E₀.projection(e)))), " +
			"            E₀.inclusion( " +
			"                d(E₀.projection(E₀.ring.sub(e, E₀.inclusion(d'(E₀.projection(e)))))))) = " +
			"        E₀.ring.sub(e, E₀.inclusion(«wg3Derivations».add(d, d')(E₀.projection(e)))))",
	},
		"a member d of fst(𝒟⁰) ∩ snd(𝒟⁰) restricts to derivations of both charts "+
			"(ChartDerivationsExtend), whose shears are automorphisms of E₀ and E₁ over P "+
			"(DeformationAutomorphisms with the identity thickening); their maps of localizations "+
			"are both the shear by d, two ring maps out of a localization agreeing on the classes "+
			"e/1 (SquareZeroLocalizationIsExtension's last conjunct, "+
			"LocalizationHomomorphismExtensional), and φ, an isomorphism of extensions of A₀₁ by "+
			"M₀₁, commutes with that shear (SquareZeroIsomorphismDef). Conversely the chart maps "+
			"of an automorphism are shears by chart derivations e₀, e₁, and the square gives the "+
			"extensions of e₀ and e₁ equal, the d asked for. d is determined on A₀ by its shear, "+
			"the inclusion being injective and the projection onto A₀, and on A₀₁ by its "+
			"restriction (ChartDerivationsExtend); the composite is the sum, the inclusion additive"),
})}

// ClassModulesOverSubring — over a subring S of both charts the
// restrictions to the overlap are linear, the compatible classes are a
// submodule of the product of the charts' D^1, and the compatible
// classes and the gluing cokernel are modules over S.
var ClassModulesOverSubring = classModulesOverSubringThm{family.Add(registry.ProofEntry{
	Name: "ClassModulesOverSubring",
	Key:  "prop_dc51e71a9d04ba12",
	Reading: "Each restriction is linear over its own chart only " +
		"(CotangentCohomologyRestrictionHom), so the difference of the two is linear over the rings " +
		"inside both: over k, for a curve over a field, the compatible classes and the cokernel are " +
		"vector spaces, which is what their dimensions are read in. They are not modules over A₀₁.",
	Deps: []registry.EntryLike{
		biaffineCompatibleClassesDef,
		biaffineGluingCokernelDef,
		cotangent_examples.CotangentCohomologyRestrictionHom,
		cotangent_complex.CotangentCohomologyModuleOn,
		lattice_pair.BiaffineChartLocalization,
		module_homomorphism.ProductModuleOn,
		submodule.SubmoduleDef,
		submodule.SubmoduleModuleOn,
		submodule.QuotientModuleOn,
		submodule.SubmoduleSum,
		module_homomorphism.HomDiff,
		module_homomorphism.KernelSubmodule,
		module_homomorphism.ImageSubmodule,
	},
	Build: family.Card(Statement{
		Binders: "∀P:ring_ops(A). " +
			"∀h:(A → C). " +
			"∀A₀₁:ring_ops(C). " +
			"∀A₀ A₁:set(C). " +
			"∀t s:C. " +
			"∀V:module_ops(C, D). " +
			"∀M:prod(set(D), set(D)). " +
			"∀S:set(C).",
		Hypotheses: []string{
			"cotangent_universe(P, 𝕌⟨A:U⟩)",
			"cotangent_universe(restrict_ring(A₀₁, A₀), 𝕌⟨A:U⟩)",
			"cotangent_universe(restrict_ring(A₀₁, A₁), 𝕌⟨A:U⟩)",
			"cotangent_universe(A₀₁, 𝕌⟨A:U⟩)",
			"biaffine(A₀₁, A₀, A₁, t, s)",
			"lattice_pair(A₀₁, A₀, A₁, V, M)",
			"ring_homomorphism(P, A₀₁, h)",
			"image(h, P.carrier) ⊆ A₀ ∩ A₁",
			"subring(A₀₁, S)",
			"S ⊆ A₀",
			"S ⊆ A₁",
		},
		Conclusion: "module_homomorphism(restrict_ring(A₀₁, S), " +
			"    cotangent_cohomology⟨U:U⟩(P, " +
			"        restrict_ring(A₀₁, A₀), " +
			"        h, " +
			"        restrict_ring(A₀₁, A₀), " +
			"        λc:C. c, " +
			"        «wg3Module0», " +
			"        1), " +
			"    «wg3OverlapClasses», " +
			"    λx:set(U → D). «wg3Restriction0»(x)) ∧ " +
			"module_homomorphism(restrict_ring(A₀₁, S), " +
			"    cotangent_cohomology⟨U:U⟩(P, " +
			"        restrict_ring(A₀₁, A₁), " +
			"        h, " +
			"        restrict_ring(A₀₁, A₁), " +
			"        λc:C. c, " +
			"        «wg3Module1», " +
			"        1), " +
			"    «wg3OverlapClasses», " +
			"    λx:set(U → D). «wg3Restriction1»(x)) ∧ " +
			"submodule(restrict_ring(A₀₁, S), " +
			"    product_module(cotangent_cohomology⟨U:U⟩(P, " +
			"            restrict_ring(A₀₁, A₀), " +
			"            h, " +
			"            restrict_ring(A₀₁, A₀), " +
			"            λc:C. c, " +
			"            «wg3Module0», " +
			"            1), " +
			"        «wg3ChartClasses1»), " +
			"    biaffine_compatible_classes(P, h, A₀₁, A₀, A₁, V, M).carrier) ∧ " +
			"module_on(restrict_ring(A₀₁, S), biaffine_compatible_classes⟨U:U⟩(P, h, A₀₁, A₀, A₁, V, M)) ∧ " +
			"module_on(restrict_ring(A₀₁, S), biaffine_gluing_cokernel⟨U:U⟩(P, h, A₀₁, A₀, A₁, V, M))",
		Abbrev: Abbrev{
			{Name: "wg3ChartClasses1", Text: "cotangent_cohomology(P, " +
				"    restrict_ring(A₀₁, A₁), " +
				"    h, " +
				"    restrict_ring(A₀₁, A₁), " +
				"    λc:C. c, " +
				"    restrict_module(V, snd(M)), " +
				"    1)"},
			{Name: "wg3OverlapClasses", Text: "cotangent_cohomology(P, A₀₁, h, A₀₁, λc:C. c, «wg3Overlap», 1)"},
		},
	},
		"each chart's D¹ is a module over the chart ring (CotangentCohomologyModuleOn), so over S "+
			"⊆ it, and the restriction is linear over the chart ring into D¹(A₀₁/P, M₀₁) read over it "+
			"(CotangentCohomologyRestrictionHom at the localization of BiaffineChartLocalization, ν "+
			"the inclusion of the chart module, linear over the chart), so over S. The compatible "+
			"classes are the kernel of the difference of the two on the product (ProductModuleOn, "+
			"HomDiff, KernelSubmodule), a submodule and so a module (SubmoduleModuleOn); the two "+
			"images are submodules over S (ImageSubmodule) and their sum is one (SubmoduleSum), so the "+
			"quotient of the overlap's D¹, a module over A₀₁ ⊇ S, is a module over S (QuotientModuleOn)"),
})}
