// long_exact.go — the long exact sequence of André–Quillen homology of a
// tower R → S → T with coefficients in a module N over T. The triangle's
// totals form a short exact sequence of complexes, whose homology is
// long exact; the left total computes D_n(S/R, N), the middle one
// D_n(T/R, N) through the double complex with constant rows, the right
// one D_n(T/S, N). The three maps of the sequence are carried across
// those homology isomorphisms, inverted on their carriers; each spot of
// the sequence is then exact because the carried sequence is. The left
// map is the one induced by g on cotangent complexes and the right map
// the one induced by changing the base from R to S; the cone of the
// inclusion of totals computes the cotangent complex of T over S.

package transitivity

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/cotangent_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/resolution_comparison"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/simplicial_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/standard_resolution"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/chain_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/partial_derivative"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_module"
	"github.com/euc-ai/xugo/library/registry"
)

// The three edge maps: the left total onto the cotangent complex of S
// over R, the total with constant rows onto the cotangent complex of T
// over R, the right total onto the cotangent complex of T over S.
const (
	leftEdge     = "double_edge(triangle_left_eps⟨U:U⟩)"
	constantEdge = "λm:num. λu:(num → U → D). u(0)"
	rightEdge    = "λm:num. λu:(num → U → D). triangle_right_eps(R, S, f, T, N, m, u(0))"
)

const middleComparisonTotal = "double_total_map(triangle_middle_comparison(R, S, f, T, g, N))"

// ---------------------------------------------------------------------------
// The maps of the long exact sequence
// ---------------------------------------------------------------------------

// TransitivityLeftMapDef — `transitivity_left_map(R, S, f, T, g, N, n,
// c)`: the map D_n(S/R, N) → D_n(T/R, N) of the long exact sequence, the
// inclusion of totals carried across the homology isomorphisms — c
// lifted to the left total, included in the middle total, brought back
// to the total with constant rows and read in its column 0.
var TransitivityLeftMapDef = transitivityLeftMapDefThm{family.Define(registry.DefEntry{
	Name:  "TransitivityLeftMapDef",
	Key:   "prop_ebc9bb378ae27892",
	Const: "transitivity_left_map",
	Type:  towerType + "num → set(U → D) → set(U → D)",
	Equations: []string{
		towerBinders + "∀n:num. ∀c:set(U → D). transitivity_left_map(R, S, f, T, g, N, n, c) = " +
			"homology_map(" + cotangentTR + ", " + constantEdge + ", n, " +
			"inverse_on(homology(" + constantTotal + ", n), homology_map(" + middleTotal + ", " + middleComparisonTotal + ", n), " +
			"homology_map(" + middleTotal + ", double_total_map(triangle_inclusion), n, " +
			"inverse_on(homology(" + leftTotal + ", n), homology_map(" + cotangentSR + ", " + leftEdge + ", n), c))))",
	},
	Reading: "Each inverse is the preimage inverse_on chooses in the homology of the source of a " +
		"quasi-isomorphism the hypotheses provide — the left edge and the column comparison — a " +
		"genuine inverse there; so on D_n(S/R, N) the map is a homomorphism over T and it is the map " +
		"induced by g on cotangent complexes, read on homology. Off the classes the value is never read.",
	Deps: []registry.EntryLike{
		TriangleLeftTotalDef,
		TriangleMiddleTotalDef,
		constantCotangentTotalDef,
		triangleMiddleComparisonDef,
		TriangleInclusionDef,
		TriangleLeftEpsDef,
	},
})}

// TransitivityRightMapDef — `transitivity_right_map(R, S, f, T, g, N, n,
// c)`: the map D_n(T/R, N) → D_n(T/S, N) of the long exact sequence, the
// projection of totals carried across the homology isomorphisms — c
// lifted to the total with constant rows, mapped into the middle total,
// projected to the right total and read through the rows' augmentation.
var TransitivityRightMapDef = transitivityRightMapDefThm{family.Define(registry.DefEntry{
	Name:  "TransitivityRightMapDef",
	Key:   "prop_307278d23ca0a048",
	Const: "transitivity_right_map",
	Type:  towerType + "num → set(U → D) → set(U → D)",
	Equations: []string{
		towerBinders + "∀n:num. ∀c:set(U → D). transitivity_right_map(R, S, f, T, g, N, n, c) = " +
			"homology_map(" + cotangentTS + ", " + rightEdge + ", n, " +
			"homology_map(" + rightTotal + ", double_total_map(triangle_projection), n, " +
			"homology_map(" + middleTotal + ", " + middleComparisonTotal + ", n, " +
			"inverse_on(homology(" + constantTotal + ", n), homology_map(" + cotangentTR + ", " + constantEdge + ", n), c))))",
	},
	Reading: "One inverse only, the edge of the total with constant rows; on " +
		"D_n(T/R, N) the map is a homomorphism over T, and it is the map induced by the " +
		"change of base along f on cotangent complexes, read on homology. Each inverse_on " +
		"is taken on the homology of the source of a quasi-isomorphism the hypotheses " +
		"provide, a genuine inverse there; off the classes the value is never read.",
	Deps: []registry.EntryLike{
		TriangleRightTotalDef,
		TriangleMiddleTotalDef,
		constantCotangentTotalDef,
		triangleMiddleComparisonDef,
		TriangleProjectionDef,
		TriangleRightEpsDef,
	},
})}

// TransitivityConnectingDef — `transitivity_connecting(R, S, f, T, g, N,
// n, c)`: the connecting map D_{n+1}(T/S, N) → D_n(S/R, N) of the long
// exact sequence, the connecting map of the short exact sequence of
// totals carried across the homology isomorphisms of the right and the
// left total.
var TransitivityConnectingDef = transitivityConnectingDefThm{family.Define(registry.DefEntry{
	Name:  "TransitivityConnectingDef",
	Key:   "prop_dc798fd433def0b2",
	Const: "transitivity_connecting",
	Type:  towerType + "num → set(U → D) → set(U → D)",
	Equations: []string{
		towerBinders + "∀n:num. ∀c:set(U → D). transitivity_connecting(R, S, f, T, g, N, n, c) = " +
			"homology_map(" + cotangentSR + ", " + leftEdge + ", n, " +
			"connecting_hom(" + leftTotal + ", " + middleTotal + ", double_total_map(triangle_inclusion), double_total_map(triangle_projection), n, " +
			"inverse_on(homology(" + rightTotal + ", n + 1), homology_map(" + cotangentTS + ", " + rightEdge + ", n + 1), c)))",
	},
	Reading: "Indexed as connecting_hom is, by the target degree: it lowers the degree by " +
		"one. The class c is lifted to the right total, the connecting map of the totals' short " +
		"exact sequence takes it to the left total, and the edge map reads it on D_n(S/R, N). " +
		"Each inverse_on is taken on the homology of the source of a quasi-isomorphism the " +
		"hypotheses provide, a genuine inverse there; off the classes the value is never read.",
	Deps: []registry.EntryLike{
		TriangleLeftTotalDef,
		TriangleMiddleTotalDef,
		TriangleRightTotalDef,
		TriangleInclusionDef,
		TriangleProjectionDef,
		TriangleLeftEpsDef,
		TriangleRightEpsDef,
	},
})}

// transport lists what every exactness statement reads: the totals' short
// exact sequence, the three homology isomorphisms and the inverses that
// carry the maps.
var transport = []registry.EntryLike{
	TriangleTotalShortExact,
	LeftTotalQuasiIsomorphism,
	MiddleTotalQuasiIsomorphism,
	ConstantRowsTotal,
	RightTotalQuasiIsomorphism,
	TransitivityLeftMapDef,
	TransitivityRightMapDef,
	TransitivityConnectingDef,
	module_homomorphism.ExactAtIsomorphism,
	module_homomorphism.IsomorphismInverse,
	module_homomorphism.ModuleIsomorphismDef,
	functions.InverseOnLeft,
	chain_complex.QuasiIsomorphismDef,
	chain_complex.HomologyMapHom,
	chain_complex.ConnectingHom,
	chain_complex.HomologyModuleDef,
	chain_complex.HomologyDef,
	cotangent_complex.CotangentHomologyDef,
}

const transportNote = "ExactAtIsomorphism at the totals' long exact sequence " +
	"(TriangleTotalShortExact), the vertical isomorphisms the homology maps of the left " +
	"edge (LeftTotalQuasiIsomorphism), of the middle zigzag — the constant rows' edge after " +
	"the inverse of the column comparison (ConstantRowsTotal, MiddleTotalQuasiIsomorphism, " +
	"IsomorphismInverse) — and of the right edge (RightTotalQuasiIsomorphism). The squares " +
	"commute by the definitions of the carried maps, each inverse cancelling its map on the " +
	"homology of its source (InverseOnLeft); the maps are homomorphisms (HomologyMapHom, " +
	"ConnectingHom) and a homology module's carrier and zero are the classes and the " +
	"boundaries (HomologyModuleDef, CotangentHomologyDef)"

// ---------------------------------------------------------------------------
// The long exact sequence
// ---------------------------------------------------------------------------

// TransitivityExactAtMiddle — the sequence D_n(S/R, N) → D_n(T/R, N) →
// D_n(T/S, N) is exact at the middle.
var TransitivityExactAtMiddle = transitivityExactAtMiddleThm{family.Add(registry.ProofEntry{
	Name: "TransitivityExactAtMiddle",
	Key:  "prop_bc42aee0c362b358",
	Reading: "The vertical isomorphisms are the left edge, the middle zigzag and the right " +
		"edge; the zigzag's square needs the comparison of totals onto (IsomorphismInverse), not " +
		"InverseOnLeft alone. At S = R, f the identity, the card says the right map is injective.",
	Deps: append([]registry.EntryLike{chain_complex.LongExactMiddle}, transport...),
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D). " +
			"∀n:num.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"module_on(T, N)",
		},
		Conclusion: "exact_at(cotangent_homology⟨U:U⟩(S, T, g, T, λc:C. c, N, n).zero, " +
			"    cotangent_homology(R, S, f, T, g, N, n).carrier, " +
			"    cotangent_homology(R, T, λa:A. g(f(a)), T, λc:C. c, N, n).carrier, " +
			"    transitivity_left_map(R, S, f, T, g, N, n), " +
			"    transitivity_right_map(R, S, f, T, g, N, n))",
	}, transportNote+", at LongExactMiddle"),
})}

// TransitivityExactAtRight — the sequence D_{n+1}(T/R, N) → D_{n+1}(T/S,
// N) → D_n(S/R, N) is exact at D_{n+1}(T/S, N).
var TransitivityExactAtRight = transitivityExactAtRightThm{family.Add(registry.ProofEntry{
	Name: "TransitivityExactAtRight",
	Key:  "prop_315bc15036bee7ae",
	Reading: "The right map is read at n + 1 and the connecting map at n; " +
		"connecting_hom's ε is well defined on classes because the inclusion " +
		"of totals is injective in every degree (TriangleTotalShortExact).",
	Deps: append([]registry.EntryLike{chain_complex.LongExactQuotient}, transport...),
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D). " +
			"∀n:num.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"module_on(T, N)",
		},
		Conclusion: "exact_at(cotangent_homology(R, S, f, T, g, N, n).zero, " +
			"    cotangent_homology(R, T, λa:A. g(f(a)), T, λc:C. c, N, n + 1).carrier, " +
			"    cotangent_homology⟨U:U⟩(S, T, g, T, λc:C. c, N, n + 1).carrier, " +
			"    transitivity_right_map(R, S, f, T, g, N, n + 1), " +
			"    transitivity_connecting(R, S, f, T, g, N, n))",
	}, transportNote+", at LongExactQuotient"),
})}

// TransitivityExactAtLeft — the sequence D_{n+1}(T/S, N) → D_n(S/R, N) →
// D_n(T/R, N) is exact at D_n(S/R, N).
var TransitivityExactAtLeft = transitivityExactAtLeftThm{family.Add(registry.ProofEntry{
	Name: "TransitivityExactAtLeft",
	Key:  "prop_a5580b62d5c24748",
	Reading: "With T = S and g the identity, D_*(S/S, N) = 0: this card makes the left map " +
		"injective and ExactAtMiddle makes it onto, consistent with TransitivityLeftMapNatural " +
		"since standard_map(R, S, S, λb. b) is the identity on the standard terms.",
	Deps: append([]registry.EntryLike{chain_complex.LongExactSub}, transport...),
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D). " +
			"∀n:num.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"module_on(T, N)",
		},
		Conclusion: "exact_at(cotangent_homology(R, T, λa:A. g(f(a)), T, λc:C. c, N, n).zero, " +
			"    cotangent_homology⟨U:U⟩(S, T, g, T, λc:C. c, N, n + 1).carrier, " +
			"    cotangent_homology(R, S, f, T, g, N, n).carrier, " +
			"    transitivity_connecting(R, S, f, T, g, N, n), " +
			"    transitivity_left_map(R, S, f, T, g, N, n))",
	}, transportNote+", at LongExactSub"),
})}

// TransitivityEnd — the sequence ends in D_0(T/R, N) → D_0(T/S, N) → 0:
// the right map in degree 0 is onto.
var TransitivityEnd = transitivityEndThm{family.Add(registry.ProofEntry{
	Name: "TransitivityEnd",
	Key:  "prop_5f77e8ec8995e4ad",
	Reading: "Load-bearing is cycles(P, 0) = P.terms(0), so the degreewise " +
		"surjection of totals passes to H_0: Ω_{T/R} ⊗ N → Ω_{T/S} ⊗ N is onto.",
	Deps: append(
		[]registry.EntryLike{
			chain_complex.ExactComplexesDef,
			chain_complex.ShortExactComplexes,
			chain_complex.CyclesDef,
			chain_complex.HomologyMapCoset,
		},
		transport...),
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"module_on(T, N)",
		},
		Conclusion: "image(transitivity_right_map(R, S, f, T, g, N, 0), " +
			"    cotangent_homology(R, T, λa:A. g(f(a)), T, λc:C. c, N, 0).carrier) = " +
			"cotangent_homology⟨U:U⟩(S, T, g, T, λc:C. c, N, 0).carrier",
	},
		"in degree 0 every member of a total is a cycle (CyclesDef) and the projection of totals is "+
			"onto in every degree (TriangleTotalShortExact, ShortExactComplexes, ExactComplexesDef), so "+
			"its homology map in degree 0 is onto (HomologyMapCoset); carried across the isomorphisms "+
			"of the middle and the right total, which are bijections of the carriers, it stays onto"),
})}

// ---------------------------------------------------------------------------
// The maps of the sequence are the natural ones
// ---------------------------------------------------------------------------

// TransitivityLeftMapNatural — the left map of the long exact sequence is
// the map induced by g on cotangent complexes, read on homology.
var TransitivityLeftMapNatural = transitivityLeftMapNaturalThm{family.Add(registry.ProofEntry{
	Name: "TransitivityLeftMapNatural",
	Key:  "prop_d51e4bf55503f417",
	Reading: "The right side is CotangentFunctorialMap's chain map at S' = T, f' = λa:A. g(f(a)), " +
		"φ = g and the identity of T as coefficient map, read on homology: the map L_{S/R} ⊗_S N → " +
		"L_{T/R} ⊗_T N. Its domain complex there is cotangent_complex(R, S, f, T, λy:B. g(y), N), the " +
		"left complex up to η. The content is that a class in bidegree (n, 0) of the middle total " +
		"equals one in bidegree (0, n); at n = 0 the difference is the vertical boundary of the " +
		"second-tag variable of var(tag₀ x) in Q(0, 1), whose two faces are var(tag₀ x) and var(tag₁ " +
		"tag(g s)). Through the diagonal the identity is exact on classes: [AW(J(F) z)] is the " +
		"inclusion of the left edge's preimage of c, and [AW(J(G) z)] the comparison of the constant " +
		"edge's preimage of [J(standard_map g) z], the constant edge after AW being the identity on " +
		"chains. No sign enters: AW is unsigned and the three totals share alternating_sign.",
	Deps: append([]registry.EntryLike{
		cotangent_complex.CotangentFunctorialMap,
		cotangent_complex.CotangentChainComplex,
		cotangent_complex.DifferentialHomotopyChainHomotopy,
		cotangent_complex.DifferentialMapChainMap,
		cotangent_complex.DifferentialMapCompose,
		cotangent_complex.DifferentialComplexChain,
		simplicial_ring.AugmentedAlongRingMap,
		resolution_comparison.ComparisonHomotopyExists,
		resolution_comparison.SimplicialAlgebraMapCompose,
		standard_resolution.StandardPolynomialAlgebra,
		standard_resolution.StandardMapAlgebraMap,
		standard_resolution.StandardMapAugmentation,
		standard_resolution.RelativeDiagonalResolution,
		standard_resolution.RelativeDiagonalBaseInclusion,
		standard_resolution.RelativeDiagonalFromAbsolute,
		simplicial_module.AlexanderWhitneyChainMap,
		simplicial_module.AlexanderWhitneyNatural,
		simplicial_module.AlexanderWhitneyConstantVertical,
		simplicial_module.AlexanderWhitneyConstantHorizontal,
		TriangleMiddleBisimplicial,
		TriangleLeftBisimplicial,
		ConstantCotangentBisimplicial,
		MiddleComparisonBisimplicialMap,
		MiddleDiagonalDifferential,
		MiddleComparisonDoubleMap,
		LeftColumnsConstant,
		LeftTotalAugmented,
		TriangleLeftEpsDef,
		simplicial_ring.TagInjective,
		partial_derivative.JacobianDelta,
		partial_derivative.PartialVar,
		chain_complex.HomotopicSameHomologyMap,
		chain_complex.HomologyMapCoset,
		chain_complex.ChainMapCycles,
		chain_complex.CyclesDef,
		chain_complex.BoundariesDef,
		chain_complex.DoubleEdgeDef,
	}, transport...),
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D). " +
			"∀n:num. " +
			"∀c:set(U → D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"module_on(T, N)",
			"c ∈ cotangent_homology(R, S, f, T, g, N, n).carrier",
		},
		Conclusion: "transitivity_left_map(R, S, f, T, g, N, n)(c) = " +
			"homology_map(cotangent_complex(R, T, λa:A. g(f(a)), T, λc:C. c, N), " +
			"    differential_map(R, " +
			"        standard_names(R, S), " +
			"        standard_names(R, T), " +
			"        standard_face(R, T, λa:A. g(f(a))), " +
			"        λu:U. standard_eps(R, T, λa:A. g(f(a)), u), " +
			"        standard_map(R, S, T, g), " +
			"        N), " +
			"    n, " +
			"    c)",
	},
		"compare on the diagonal of Q and come back by the Alexander–Whitney map AW. Let z be a "+
			"cycle of L_{S/R} ⊗ N in the class c. The first tag F and G = relative_from_absolute ∘ "+
			"standard_map(R, S, T, g) are simplicial algebra maps from P into the diagonal of Q "+
			"(RelativeDiagonalBaseInclusion; RelativeDiagonalFromAbsolute with StandardMapAlgebraMap, "+
			"SimplicialAlgebraMapCompose), a polynomial resolution of T (RelativeDiagonalResolution), "+
			"and both cover g (StandardMapAugmentation), so ComparisonHomotopyExists joins them and "+
			"their Jacobians, chain maps into the differential complex of the diagonal "+
			"(DifferentialMapChainMap, AugmentedAlongRingMap at StandardPolynomialAlgebra), are chain "+
			"homotopic (DifferentialHomotopyChainHomotopy): J(F)(z) and J(G)(z) have one class there "+
			"(HomotopicSameHomologyMap, DifferentialComplexChain, CotangentChainComplex). On its terms "+
			"that complex is the face complex of the diagonal of the middle bisimplicial module "+
			"(MiddleDiagonalDifferential, TriangleMiddleBisimplicial), which AW carries by a chain map "+
			"to the middle total (AlexanderWhitneyChainMap), so AW(J(F)(z)) and AW(J(G)(z)) have one "+
			"class in the middle total (HomologyMapCoset, ChainMapCycles). Left: J(F)(z) is z under "+
			"the first tag (JacobianDelta, PartialVar), a member of the diagonal of the left "+
			"bisimplicial module (TriangleLeftBisimplicial), whose vertical faces are identities "+
			"(LeftColumnsConstant); so AW(J(F)(z)) is a cycle of the left total "+
			"(AlexanderWhitneyChainMap at TriangleLeftBisimplicial, the left and middle modules "+
			"sharing their maps), whose corner (n, 0) is J(F)(z) (AlexanderWhitneyConstantVertical) "+
			"and whose edge is z (DoubleEdgeDef, TriangleLeftEpsDef, TagInjective): its class is the "+
			"preimage of c under the left edge (LeftTotalAugmented, LeftTotalQuasiIsomorphism), and "+
			"the inclusion of totals moves nothing. Right: J(G) is the comparison read on the diagonal "+
			"after CotangentFunctorialMap's chain map (DifferentialMapCompose, "+
			"MiddleDiagonalDifferential), and AW after the diagonal comparison is the total comparison "+
			"after AW of the constant rows (AlexanderWhitneyNatural at MiddleComparisonBisimplicialMap "+
			"and ConstantCotangentBisimplicial, linear by MiddleComparisonDoubleMap), whose coordinate "+
			"0 is its argument (AlexanderWhitneyConstantHorizontal): AW of the constant rows, a chain "+
			"map from the cotangent complex of T over R, the face complex of their diagonal, to their "+
			"total (AlexanderWhitneyChainMap at ConstantCotangentBisimplicial), inverts their edge on "+
			"homology (ConstantRowsTotal). So the inclusion after the inverse left edge is the total "+
			"comparison after the inverse constant edge after CotangentFunctorialMap's homology map, "+
			"and inverting the comparison (MiddleTotalQuasiIsomorphism) and applying the constant edge "+
			"gives the card (TransitivityLeftMapDef)"),
})}

// TransitivityRightMapNatural — the right map of the long exact sequence
// is the map induced on homology by standard_base_change(R, S, f), the
// change of coefficients of the standard resolution of T from R to S.
var TransitivityRightMapNatural = transitivityRightMapNaturalThm{family.Add(registry.ProofEntry{
	Name: "TransitivityRightMapNatural",
	Key:  "prop_dcdaf08a1b5a2369",
	Reading: "The map is standard_base_change(R, S, f), the change of coefficients from R to S " +
		"keeping the names, which meets CotangentBaseChangeMap's hypotheses (StandardBaseChangeMap, " +
		"StandardBaseChangeAugmentation). It is the composite λq u. relative_horizontal_eps(R, S, f, " +
		"q, relative_from_absolute(R, q, u)) on the standard resolution of T over R, so the equality " +
		"holds on the nose, with no homotopy; another map meeting those hypotheses would need a " +
		"comparison homotopy across the change of coefficients, which the corpus does not state. It " +
		"holds on chains, not only on classes: for a cycle x of L_{T/R}, triangle_right_eps(n, " +
		"projection(comparison₀ x)) and the Jacobian of standard_base_change(n) at x are both the " +
		"pushforward along standard_base_change(n − 1), along the identity at n = 0, because " +
		"triangle_row_augmentation(R, S, f, 0, q + 1) = relative_horizontal_eps(R, S, f, q).",
	Deps: append([]registry.EntryLike{
		cotangent_complex.CotangentBaseChangeMap,
		standard_resolution.StandardBaseChangeMap,
		standard_resolution.StandardBaseChangeAugmentation,
		standard_resolution.StandardBaseChangeDef,
		standard_resolution.RelativeFromAbsoluteMap,
		standard_resolution.RelativeHorizontalEpsHom,
		standard_resolution.RelativeHorizontalEpsVertical,
		standard_resolution.RelativeHorizontalEpsDef,
		standard_resolution.RelativeFromAbsoluteDef,
		partial_derivative.JacobianCompose,
		partial_derivative.JacobianCongruence,
		chain_complex.HomologyMapCoset,
		triangleMiddleComparisonDef,
		TriangleRightEpsDef,
	}, transport...),
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D). " +
			"∀n:num. " +
			"∀c:set(U → D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"module_on(T, N)",
			"c ∈ cotangent_homology(R, T, λa:A. g(f(a)), T, λc:C. c, N, n).carrier",
		},
		Conclusion: "transitivity_right_map(R, S, f, T, g, N, n)(c) = " +
			"homology_map(cotangent_complex(S, T, g, T, λc:C. c, N), " +
			"    λm:num. " +
			"        free_algebra_jacobian(universe_embedding(R), " +
			"            universe_embedding(S), " +
			"            R, " +
			"            S, " +
			"            standard_names(R, T, m), " +
			"            standard_names(S, T, m), " +
			"            standard_base_change(R, S, f, m), " +
			"            standard_to_base(S, T, g, m), " +
			"            N), " +
			"    n, " +
			"    c)",
	},
		"lift c through the constant rows' edge (ConstantRowsTotal): on the coordinate 0 the "+
			"comparison, the projection and the right augmentation compose to the Jacobian of "+
			"relative_horizontal_eps after relative_from_absolute (triangleMiddleComparisonDef, "+
			"TriangleRightEpsDef, JacobianCompose, JacobianCongruence, RelativeFromAbsoluteMap, "+
			"RelativeHorizontalEpsVertical); that composite is standard_base_change(R, S, f, q) on "+
			"the standard terms of T over R, by induction on q — degree 0 both are the map of "+
			"coefficients along f on the tags of T's elements, degree q + 1 both are the map along f "+
			"induced by the one below (RelativeHorizontalEpsDef, RelativeFromAbsoluteDef, "+
			"StandardBaseChangeDef, FreeAlgebraMapCompose) — so the two chain maps agree on terms and "+
			"the classes agree (HomologyMapCoset); CotangentBaseChangeMap with StandardBaseChangeMap "+
			"and StandardBaseChangeAugmentation makes the right side a homomorphism of the homologies"),
})}

// ---------------------------------------------------------------------------
// The triangle
// ---------------------------------------------------------------------------

// TransitivityTriangle — the cone of the inclusion of the left total in
// the middle total maps quasi-isomorphically onto the cotangent complex
// of T over S: the cofibre of L_{S/R} ⊗ N → L_{T/R} ⊗ N is L_{T/S} ⊗ N.
var TransitivityTriangle = transitivityTriangleThm{family.Add(registry.ProofEntry{
	Name: "TransitivityTriangle",
	Key:  "prop_3a4e78c9d84053c8",
	Reading: "The two totals are the models of L_{S/R} ⊗_S N and L_{T/R} ⊗_T N in one host, " +
		"quasi-isomorphic to them (LeftTotalQuasiIsomorphism, MiddleTotalQuasiIsomorphism with " +
		"ConstantRowsTotal), and the inclusion between them is, on homology, the map induced by " +
		"g (TransitivityLeftMapNatural). The map from the cone discards its first component, " +
		"the shifted left total, and reads coordinate 0 of the projected middle component " +
		"through the right edge: DegreewiseSplitThirdTermCone after RightTotalQuasiIsomorphism, " +
		"the section on totals being triangle_section in every coordinate.",
	Deps: []registry.EntryLike{
		TriangleTotalShortExact,
		TriangleDegreewiseShortExact,
		RightTotalQuasiIsomorphism,
		TriangleSectionDef,
		chain_complex.DegreewiseSplitThirdTermCone,
		chain_complex.ChainConeDef,
		chain_complex.QuasiIsomorphismCompose,
		chain_complex.DoubleTotalTermsDef,
		chain_complex.DoubleTotalMapDef,
		chain_complex.DoubleTotalDef,
		chain_complex.ConeChainComplex,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"module_on(T, N)",
		},
		Conclusion: "quasi_isomorphism(T, " +
			"    chain_cone(triangle_left_total(R, S, f, T, g, N), " +
			"        triangle_middle_total(R, S, f, T, g, N), " +
			"        double_total_map(triangle_inclusion)), " +
			"    cotangent_complex(S, T, g, T, λc:C. c, N), " +
			"    λn:num. λz:prod(num → U → D, num → U → D). " +
			"        triangle_right_eps(R, S, f, T, N, n, triangle_projection(0, n, snd(z)(0))))",
	},
		"the sequence of totals is short exact (TriangleTotalShortExact) and split in every degree, by "+
			"the section on every coordinate of a diagonal (TriangleDegreewiseShortExact, "+
			"TriangleSectionDef, DoubleTotalTermsDef), so DegreewiseSplitThirdTermCone makes the projection "+
			"of the second component a quasi-isomorphism from the cone onto the right total; compose with "+
			"the right edge (RightTotalQuasiIsomorphism, QuasiIsomorphismCompose), the coordinate 0 of the "+
			"projected diagonal being triangle_projection(0, n, ·) of the coordinate 0 (DoubleTotalMapDef)"),
})}
