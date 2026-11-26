// cohomology.go — the long exact sequence of André–Quillen cohomology of a
// tower R → S → T with coefficients in a module N over T,
//
//	0 → D^0(T/S, N) → D^0(T/R, N) → D^0(S/R, N) → D^1(T/S, N) → ⋯,
//
// obtained by dualizing the chain-level diagram of chain_square.go. The
// two maps are those the change of base and g induce on the cochain
// complexes, the transposed Jacobians; the connecting map is the
// connecting map of the dual of the split short exact sequence of totals,
// carried by the duals of the left and the right edge. A linear map of
// coefficient modules carries the sequence to the one with the new
// coefficients.

package transitivity

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/cotangent_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/chain_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_complex_duality"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/partial_derivative"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/registry"
)

// scalarModule is T as a module over itself: the coefficients of the
// chain-level diagram, whose dual with coefficients in N is the cochain
// side.
const scalarModule = "regular_module(T)"

// The three totals with coefficients in T, their cells' generators, and
// the bases the totals take from cells based by the identity.
const (
	leftTotalScalar   = "triangle_left_total(R, S, f, T, g, " + scalarModule + ")"
	middleTotalScalar = "triangle_middle_total(R, S, f, T, g, " + scalarModule + ")"
	rightTotalScalar  = "triangle_right_total⟨U:U⟩(R, S, f, T, g, " + scalarModule + ")"

	leftCells   = "λp:num. λq:num. image(universe_tag(0), standard_names(R, S, p))"
	middleCells = "triangle_column_names(R, S, T)"
	rightCells  = "relative_names(R, S, T)"

	totalExpand      = "double_total_expand(finite_supp_module(" + scalarModule + ", 𝕌⟨A:U⟩), λp:num. λq:num. λa:(U → C). a)"
	totalCoordinates = "double_total_coordinates(T, λp:num. λq:num. λu:(U → C). u)"
	identityBasis    = "λk:num. λu:(U → C). u"
)

// totalBasis spells the basis of degree-indexed generators of the total
// whose cell (p, q) has the generators cells(p, q).
func totalBasis(cells string) string { return "double_total_basis(" + cells + ")" }

// totalDual spells the dual with coefficients in N of a total based from
// identity-based cells.
func totalDual(total, cells string) string {
	return "free_dual_complex(T, N, " + total + ", " + totalBasis(
		cells) + ", " + totalExpand + ", " + totalCoordinates + ")"
}

// The duals of the three totals, and the transposes of the edges and of
// the inclusion and the projection of totals.
var (
	leftDual   = totalDual(leftTotalScalar, leftCells)
	middleDual = totalDual(middleTotalScalar, middleCells)
	rightDual  = totalDual(rightTotalScalar, rightCells)

	leftEdgeDual = "free_dual_map(T, N, " + totalBasis(
		leftCells) + ", " + totalExpand + ", " + identityBasis + ", " + leftEdge + ")"
	rightEdgeScalar = "λm:num. λu:(num → U → C). triangle_right_eps(R, S, f, T, " + scalarModule + ", m, u(0))"
	rightEdgeDual   = "free_dual_map(T, N, " + totalBasis(
		rightCells) + ", " + totalExpand + ", " + identityBasis + ", " + rightEdgeScalar + ")"
	inclusionDual = "free_dual_map(T, N, " + totalBasis(
		leftCells) + ", " + totalExpand + ", " + totalCoordinates + ", double_total_map(triangle_inclusion))"
	projectionDual = "free_dual_map(T, N, " + totalBasis(
		middleCells) + ", " + totalExpand + ", " + totalCoordinates + ", double_total_map(triangle_projection))"
	cochainSR           = "cotangent_cochain(R, S, f, T, g, N)"
	cochainTR           = "cotangent_cochain(R, T, λa:A. g(f(a)), T, λc:C. c, N)"
	cochainTS           = "cotangent_cochain(S, T, g, T, λc:C. c, N)"
	baseChangeTranspose = "λm:num. λw:(U → D). " +
		"free_algebra_jacobian_transpose(universe_embedding(R), " +
		"universe_embedding(S), R, S, standard_names(R, T, m), standard_names(S, " +
		"T, m), standard_base_change(R, S, f, m), standard_to_base(S, T, g, m), N, w)"
	functorialTranspose = "λm:num. λw:(U → D). " +
		"free_algebra_jacobian_transpose(universe_embedding(R), universe_embedding(R), " +
		"R, R, standard_names(R, S, m), standard_names(R, T, m), standard_map(R, S, T, " +
		"g, m), λu:U. standard_to_base(R, T, λa:A. g(f(a)), m, u), N, w)"
)

// ---------------------------------------------------------------------------
// The maps of the long exact sequence
// ---------------------------------------------------------------------------

// CoTransitivityLeftMapDef — `co_transitivity_left_map(R, S, f, T, g, N, n,
// s)`: the map D^n(T/S, N) → D^n(T/R, N) of the cohomology sequence, the
// map on cohomology of the transposed Jacobian of the change of base
// standard_base_change(R, S, f).
var CoTransitivityLeftMapDef = coTransitivityLeftMapDefThm{family.Define(registry.DefEntry{
	Name:  "CoTransitivityLeftMapDef",
	Key:   "prop_5fa81bc4770c8523",
	Const: "co_transitivity_left_map",
	Type:  towerType + "num → set(U → D) → set(U → D)",
	Equations: []string{
		towerBinders + "∀n:num. ∀s:set(U → D). co_transitivity_left_map(R, S, f, T, g, N, n, s) = " +
			"cohomology_map(" + cochainTR + ", " + baseChangeTranspose + ", n, s)",
	},
	Reading: "Left and right name the places in the cohomology sequence, which runs the " +
		"other way from the homology one: this is the transpose of the homology sequence's " +
		"right map. It is the dual of the change of base G, read on the cochain complexes " +
		"cotangent_cochain already names, with no basis or identification in between.",
})}

// CoTransitivityRightMapDef — `co_transitivity_right_map(R, S, f, T, g, N,
// n, s)`: the map D^n(T/R, N) → D^n(S/R, N) of the cohomology sequence, the
// map on cohomology of the transposed Jacobian of standard_map(R, S, T, g).
var CoTransitivityRightMapDef = coTransitivityRightMapDefThm{family.Define(registry.DefEntry{
	Name:  "CoTransitivityRightMapDef",
	Key:   "prop_6f82477b86fd3ab8",
	Const: "co_transitivity_right_map",
	Type:  towerType + "num → set(U → D) → set(U → D)",
	Equations: []string{
		towerBinders + "∀n:num. ∀s:set(U → D). co_transitivity_right_map(R, S, f, T, g, N, n, s) = " +
			"cohomology_map(" + cochainSR + ", " + functorialTranspose + ", n, s)",
	},
	Reading: "The transpose of the homology sequence's left map, the map g induces on " +
		"the cotangent complexes; the augmentation is read as standard_to_base of T over R, " +
		"which is the augmentation the cochain complex of T over R reads in each degree.",
})}

// CoTransitivityConnectingDef — `co_transitivity_connecting(R, S, f, T, g,
// N, n, s)`: the connecting map D^n(S/R, N) → D^(n+1)(T/S, N), the
// connecting map of the dual sequence of totals carried by the duals of
// the left edge, forwards, and of the right edge, inverted on its
// carrier.
var CoTransitivityConnectingDef = coTransitivityConnectingDefThm{family.Define(registry.DefEntry{
	Name:  "CoTransitivityConnectingDef",
	Key:   "prop_3a5fa082f5c7ceb4",
	Const: "co_transitivity_connecting",
	Type:  towerType + "num → set(U → D) → set(U → D)",
	Equations: []string{
		towerBinders + "∀n:num. ∀s:set(U → D). co_transitivity_connecting(R, S, f, T, g, N, n, s) = " +
			"inverse_on(cohomology(" + cochainTS + ", n + 1), cohomology_map(" + rightDual + ", " + rightEdgeDual + ", n + 1), " +
			"coconnecting_hom(" + rightDual + ", " + middleDual + ", " + projectionDual + ", " + inclusionDual + ", n, " +
			"cohomology_map(" + leftDual + ", " + leftEdgeDual + ", n, s)))",
	},
	Reading: "Indexed as coconnecting_hom is, by the source degree: it raises the degree by " +
		"one. The class s is carried to the dual of the left total by the dual of the left edge, " +
		"the dual sequence of totals — 0 → C^∨ → B^∨ → A^∨ → 0, exact because the totals' sequence " +
		"splits in every degree — takes it to degree n + 1 of the dual of the right total, and the " +
		"inverse of the dual of the right edge, an isomorphism on cohomology, brings it to " +
		"D^(n+1)(T/S, N). The duals of the cotangent complexes are cotangent_cochain itself, so the " +
		"inverse is taken on cotangent_cochain's cohomology; off the classes the value is never read.",
	Deps: []registry.EntryLike{
		TriangleLeftTotalDef,
		TriangleMiddleTotalDef,
		TriangleRightTotalDef,
		TriangleColumnNamesDef,
		TriangleInclusionDef,
		TriangleProjectionDef,
		TriangleLeftEpsDef,
		TriangleRightEpsDef,
	},
})}

// ---------------------------------------------------------------------------
// The long exact sequence
// ---------------------------------------------------------------------------

// CotangentCohomologyTransitivity — the cohomology long exact sequence of
// the tower, 0 → D^0(T/S, N) → D^0(T/R, N) → D^0(S/R, N) → D^1(T/S, N) →
// ⋯, with its named maps.
var CotangentCohomologyTransitivity = cotangentCohomologyTransitivityThm{family.Add(registry.ProofEntry{
	Name: "CotangentCohomologyTransitivity",
	Key:  "prop_d82f5ec0873cafa9",
	Reading: "Left and right name places in the cohomology sequence: co_transitivity_left_map " +
		"transposes the change of base, the homology sequence's right map, and co_transitivity_right_map " +
		"transposes the map g induces. The three maps are named, so the card says which maps are exact; " +
		"with the maps quantified the sequence would say nothing, since at S = R every D^n(S/R, N) " +
		"vanishes. In degree 0 the left map is injective: D^0(T/S, N) and D^0(T/R, N) are the " +
		"derivations of T into N over S and over R, and the first are among the second.",
	Deps: []registry.EntryLike{
		TriangleTotalsBased,
		TriangleTotalSplit,
		MiddleTotalChainComparison,
		TransitivityLeftChainSquare,
		TransitivityRightChainSquare,
		free_complex_duality.SplitZigzagDualLongExact,
		chain_complex.CohomologyMapCongruence,
		CoTransitivityLeftMapDef,
		CoTransitivityRightMapDef,
		CoTransitivityConnectingDef,
		TriangleTotalShortExact,
		LeftTotalQuasiIsomorphism,
		RightTotalQuasiIsomorphism,
		middleTotalChainComparisonDef,
		cotangent_complex.CotangentScalarBased,
		cotangent_complex.CotangentDualAgreement,
		cotangent_complex.CotangentMapsDualAgreement,
		cotangent_complex.CotangentFunctorialMap,
		cotangent_complex.CotangentBaseChangeMap,
		cotangent_complex.CotangentCohomologyDef,
		chain_complex.CohomologyModuleDef,
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
		Conclusion: "injective_on(«cohomologyTS»(0).carrier, «cohomologyLeftMap»(N, 0)) ∧ " +
			"(∀n:num. " +
			"    exact_at(«cohomologySR»(n).zero, " +
			"        «cohomologyTS»(n).carrier, " +
			"        «cohomologyTR»(n).carrier, " +
			"        «cohomologyLeftMap»(N, n), " +
			"        «cohomologyRightMap»(N, n))) ∧ " +
			"(∀n:num. " +
			"    exact_at(«cohomologyTS»(n + 1).zero, " +
			"        «cohomologyTR»(n).carrier, " +
			"        «cohomologySR»(n).carrier, " +
			"        «cohomologyRightMap»(N, n), " +
			"        «cohomologyConnecting»(N, n))) ∧ " +
			"(∀n:num. " +
			"    exact_at(«cohomologyTR»(n + 1).zero, " +
			"        «cohomologySR»(n).carrier, " +
			"        «cohomologyTS»(n + 1).carrier, " +
			"        «cohomologyConnecting»(N, n), " +
			"        «cohomologyLeftMap»(N, n + 1)))",
		Abbrev: Abbrev{
			{Name: "cohomologySR", Text: "cotangent_cohomology(R, S, f, T, g, N)"},
			{Name: "cohomologyTR", Text: "cotangent_cohomology(R, T, λa:A. g(f(a)), T, λc:C. c, N)"},
			{Name: "cohomologyTS", Text: "cotangent_cohomology⟨U:U⟩(S, T, g, T, λc:C. c, N)"},
			{Name: "cohomologyLeftMap", Text: "co_transitivity_left_map(R, S, f, T, g)"},
			{Name: "cohomologyRightMap", Text: "co_transitivity_right_map(R, S, f, T, g)"},
			{Name: "cohomologyConnecting", Text: "co_transitivity_connecting(R, S, f, T, g)"},
		},
	},
		"SplitZigzagDualLongExact at the chain-level diagram with coefficients in T: the top row the "+
			"three totals, based by TriangleTotalsBased, short exact (TriangleTotalShortExact at the "+
			"regular module) and split (TriangleTotalSplit); the bottom row the three cotangent complexes, "+
			"based by CotangentScalarBased; a the left edge (LeftTotalQuasiIsomorphism), b = "+
			"middle_total_chain_comparison (MiddleTotalChainComparison), c the right edge "+
			"(RightTotalQuasiIsomorphism); φ the map g induces (CotangentFunctorialMap) and ψ the change of "+
			"base (CotangentBaseChangeMap); the left square up to homotopy (TransitivityLeftChainSquare), "+
			"the right square on the nose (TransitivityRightChainSquare) with the zero homotopy. The bottom "+
			"duals are cotangent_cochain with the same cohomology modules (CotangentDualAgreement); the "+
			"duals of φ and ψ are the transposes the two maps are defined with, on the terms "+
			"(CotangentMapsDualAgreement, CohomologyMapCongruence); the connecting map is the zigzag's by "+
			"definition (CoTransitivityConnectingDef). A cohomology module's carrier is the cohomology and "+
			"its zero the coboundaries (CohomologyModuleDef, CotangentCohomologyDef)"),
})}

// CotangentCohomologyTransitivityCoefficientNatural — a linear map of
// coefficient modules carries the cohomology sequence of the tower to the
// one with the new coefficients, connecting map included.
var CotangentCohomologyTransitivityCoefficientNatural = cotangentCohomologyTransitivityCoefficientNaturalThm{family.Add(registry.ProofEntry{
	Name: "CotangentCohomologyTransitivityCoefficientNatural",
	Key:  "prop_acc9277b7de06261",
	Reading: "Naturality in the coefficient module only; a change of the " +
		"tower R → S → T is another statement, not made here. The equations are " +
		"of classes, each side a coset of the coboundaries with coefficients in N'.",
	Deps: []registry.EntryLike{
		free_complex_duality.FreeDualSplitShortExact,
		TriangleTotalSplit,
		TriangleTotalShortExact,
		TriangleTotalsBased,
		cotangent_complex.CotangentScalarBased,
		LeftTotalQuasiIsomorphism,
		free_module.HomPrecomposeCoefficientNatural,
		partial_derivative.JacobianTransposeAgreement,
		chain_complex.CohomologyMapCompose,
		chain_complex.CohomologyMapCongruence,
		chain_complex.CoconnectingNaturality,
		free_complex_duality.FreeDualQuasiIsomorphism,
		CoTransitivityLeftMapDef,
		CoTransitivityRightMapDef,
		CoTransitivityConnectingDef,
		RightTotalQuasiIsomorphism,
		cotangent_complex.CotangentCochainDef,
		cotangent_complex.CotangentCochainComplex,
		cotangent_complex.CotangentDualAgreement,
		cotangent_complex.CotangentMapsDualAgreement,
		partial_derivative.FreeAlgebraJacobianTransposeDef,
		module_homomorphism.HomSum,
		module_homomorphism.HomSmul,
		chain_complex.CohomologyMapDef,
		functions.InverseOnLeft,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D). " +
			"∀N':module_ops(C, E). " +
			"∀k:(D → E).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"module_on(T, N)",
			"module_on(T, N')",
			"module_homomorphism(T, N, N', k)",
		},
		Conclusion: "(∀n:num. ∀s:set(U → D). " +
			"    s ∈ cotangent_cohomology⟨U:U⟩(S, T, g, T, λc:C. c, N, n).carrier ⇒ " +
			"    cohomology_map(cotangent_cochain(R, T, λa:A. g(f(a)), T, λc:C. c, N'), " +
			"        λm:num. λw:(U → D). λu:U. k(w(u)), " +
			"        n, " +
			"        co_transitivity_left_map(R, S, f, T, g, N, n, s)) = " +
			"    co_transitivity_left_map(R, " +
			"        S, " +
			"        f, " +
			"        T, " +
			"        g, " +
			"        N', " +
			"        n, " +
			"        cohomology_map(cotangent_cochain(S, T, g, T, λc:C. c, N'), " +
			"            λm:num. λw:(U → D). λu:U. k(w(u)), " +
			"            n, " +
			"            s))) ∧ " +
			"(∀n:num. ∀s:set(U → D). " +
			"    s ∈ cotangent_cohomology(R, T, λa:A. g(f(a)), T, λc:C. c, N, n).carrier ⇒ " +
			"    cohomology_map(cotangent_cochain(R, S, f, T, g, N'), " +
			"        λm:num. λw:(U → D). λu:U. k(w(u)), " +
			"        n, " +
			"        co_transitivity_right_map(R, S, f, T, g, N, n, s)) = " +
			"    co_transitivity_right_map(R, " +
			"        S, " +
			"        f, " +
			"        T, " +
			"        g, " +
			"        N', " +
			"        n, " +
			"        cohomology_map(cotangent_cochain(R, T, λa:A. g(f(a)), T, λc:C. c, N'), " +
			"            λm:num. λw:(U → D). λu:U. k(w(u)), " +
			"            n, " +
			"            s))) ∧ " +
			"(∀n:num. ∀s:set(U → D). " +
			"    s ∈ cotangent_cohomology(R, S, f, T, g, N, n).carrier ⇒ " +
			"    cohomology_map(cotangent_cochain(S, T, g, T, λc:C. c, N'), " +
			"        λm:num. λw:(U → D). λu:U. k(w(u)), " +
			"        n + 1, " +
			"        co_transitivity_connecting(R, S, f, T, g, N, n, s)) = " +
			"    co_transitivity_connecting(R, " +
			"        S, " +
			"        f, " +
			"        T, " +
			"        g, " +
			"        N', " +
			"        n, " +
			"        cohomology_map(cotangent_cochain(R, S, f, T, g, N'), " +
			"            λm:num. λw:(U → D). λu:U. k(w(u)), " +
			"            n, " +
			"            s)))",
	},
		"w ↦ k ∘ w is a cochain map of each cotangent_cochain and commutes with the transposed "+
			"Jacobians that define the two maps (k passes the finite sums, HomSum, HomSmul — "+
			"HomPrecomposeCoefficientNatural through JacobianTransposeAgreement), hence on "+
			"cohomology (CohomologyMapCompose, CohomologyMapCongruence). For the connecting map, k "+
			"∘ − is a map between the dual short exact sequences of totals — it commutes with the "+
			"transposes of the inclusion and the projection (HomPrecomposeCoefficientNatural) — so "+
			"CoconnectingNaturality commutes it with their connecting maps; it commutes with the "+
			"transposes of the two edges likewise, and with the inverse of the right edge's map, "+
			"both maps being bijections on the classes (CoTransitivityConnectingDef, InverseOnLeft)"),
})}
