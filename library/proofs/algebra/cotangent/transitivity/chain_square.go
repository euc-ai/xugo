// chain_square.go — the transitivity triangle as a diagram of chain
// complexes with coefficients in T itself, ready to be dualized. The top
// row is the short exact sequence of totals, split in every degree by the
// section and the retraction it determines. The bottom row is the three
// cotangent complexes with the map g induces and the change of base. The
// vertical maps are the left edge onto L_{S/R} ⊗ T, the right edge onto
// L_{T/S} ⊗ T, and, from L_{T/R} ⊗ T into the middle total, the
// comparison after the Alexander–Whitney map of the constant rows. The
// left square commutes up to a chain homotopy found on the diagonal of
// the relative standard resolution, the right square on the nose.

package transitivity

import (
	. "github.com/euc-ai/xugo/library/authoring"

	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/cotangent_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/resolution_comparison"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/simplicial_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/standard_resolution"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/chain_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_complex_duality"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/partial_derivative"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_homotopy"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_module"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The sections by the Alexander–Whitney map
// ---------------------------------------------------------------------------

// constantTotalAWSectionDef — `constant_total_aw_section(R, T, φ, N, n, y)`:
// the Alexander–Whitney map of the bisimplicial module with constant rows
// at a member y of degree n of the cotangent complex of T over R, the
// diagonal of the constant rows: a member of degree n of their total.
var constantTotalAWSectionDef = constantTotalAWSectionDefThm{family.Define(registry.DefEntry{
	Name:  "constantTotalAWSectionDef",
	Key:   "prop_48f78e5e9c65d112",
	Const: "constant_total_aw_section",
	Type:  "ring_ops(A) → ring_ops(C) → (A → C) → module_ops(C, D) → num → (U → D) → num → U → D",
	Equations: []string{
		"∀R:ring_ops(A). ∀T:ring_ops(C). ∀φ:(A → C). ∀N:module_ops(C, D). ∀n:num. ∀y:(U → D). " +
			"    constant_total_aw_section(R, T, φ, N, n, y) = " +
			"    alexander_whitney(finite_supp_module(N, 𝕌⟨A:U⟩), " +
			"        λp:num. λq:num. λi:num. λv:(U → D). v, " +
			"        λp:num. " +
			"            differential_face(R, " +
			"                standard_names(R, T), " +
			"                standard_face(R, T, φ), " +
			"                λu:U. standard_eps(R, T, φ, u), " +
			"                N), " +
			"        n, " +
			"        y)",
	},
	Reading: "The horizontal faces of the constant rows are identities, so the " +
		"diagonal's faces are the cotangent complex's own and the map reads the coordinate " +
		"0 as y: it is a section of the edge λm u. u(0) of the total with constant rows.",
})}

// leftTotalAWSectionDef — `left_total_aw_section(R, S, f, T, g, N, n, z)`:
// a member z of degree n of the cotangent complex of S over R carried under
// the first tag into the diagonal of the left bisimplicial module, then by
// its Alexander–Whitney map into the left total.
var leftTotalAWSectionDef = leftTotalAWSectionDefThm{family.Define(registry.DefEntry{
	Name:  "leftTotalAWSectionDef",
	Key:   "prop_7f848fd0e02c1291",
	Const: "left_total_aw_section",
	Type:  towerType + "num → (U → D) → num → U → D",
	Equations: []string{
		towerBinders + "∀n:num. ∀z:(U → D). left_total_aw_section(R, S, f, T, g, N, n, z) = " +
			"alexander_whitney(finite_supp_module(N, 𝕌⟨A:U⟩), " + middleHorizontalFaces + ", " + middleVerticalFaces + ", n, " +
			"λt:U. COND(t ∈ image(universe_tag(0), 𝕌⟨A:U⟩), z(inverse_on(𝕌⟨A:U⟩, universe_tag(0), t)), N.zero))",
	},
	Reading: "The vertical faces of the left term are identities, so the map reads the " +
		"corner (n, 0) as the tagged z, and the left edge, which untags the coordinate n, gives " +
		"z back: it is a section of the left edge. The left and the middle bisimplicial modules " +
		"share their faces, so the same map read in the middle total is the inclusion of this one.",
	Deps: []registry.EntryLike{TriangleColumnNamesDef},
})}

// middleTotalChainComparisonDef — `middle_total_chain_comparison(R, S, f,
// T, g, N, n, y)`: a member y of degree n of the cotangent complex of T
// over R carried into the total with constant rows by the Alexander–Whitney
// section, then into the middle total by the comparison of totals.
var middleTotalChainComparisonDef = middleTotalChainComparisonDefThm{family.Define(registry.DefEntry{
	Name:  "middleTotalChainComparisonDef",
	Key:   "prop_b8ac2f511add915f",
	Const: "middle_total_chain_comparison",
	Type:  towerType + "num → (U → D) → num → U → D",
	Equations: []string{
		towerBinders + "∀n:num. ∀y:(U → D). middle_total_chain_comparison(R, S, f, T, g, N, n, y) = " +
			"double_total_map(triangle_middle_comparison(R, S, f, T, g, N), n, constant_total_aw_section(R, T, λa:A. g(f(a)), N, n, y))",
	},
	Reading: "It replaces the zigzag through the total with constant rows by " +
		"one chain map from L_{T/R} ⊗ N into the middle total: the Alexander–Whitney " +
		"section inverts the constant rows' edge on the nose on one side, so on " +
		"homology this map is the comparison after the inverse of that edge.",
	Deps: []registry.EntryLike{constantTotalAWSectionDef, triangleMiddleComparisonDef},
})}

// ---------------------------------------------------------------------------
// The splitting of the totals
// ---------------------------------------------------------------------------

// triangleTotalSectionDef — `triangle_total_section(N, n, u)`: the section
// of the projection of totals, triangle_section on every coordinate of a
// member u of degree n of the right total.
var triangleTotalSectionDef = triangleTotalSectionDefThm{family.Define(registry.DefEntry{
	Name:  "triangleTotalSectionDef",
	Key:   "prop_5f4f6186b6efb457",
	Const: "triangle_total_section",
	Type:  "module_ops(C, D) → num → (num → U → D) → num → U → D",
	Equations: []string{
		"∀N:module_ops(C, D). ∀n:num. ∀u:(num → U → D). " +
			"    triangle_total_section(N, n, u) = " +
			"    double_total_map(λp:num. λq:num. λx:(U → D). triangle_section(N, x), n, u)",
	},
	Reading: "Linear and splitting the projection in every degree, it is no chain " +
		"map: the vertical boundary of a second-tag function involves first-tag variables.",
	Deps: []registry.EntryLike{TriangleSectionDef},
})}

// triangleTotalRetractionDef — `triangle_total_retraction(N, n, v)`: the
// retraction of the inclusion of totals determined by the section, a member
// v of degree n of the middle total less the section of its projection.
var triangleTotalRetractionDef = triangleTotalRetractionDefThm{family.Define(registry.DefEntry{
	Name:  "triangleTotalRetractionDef",
	Key:   "prop_d7c21f7983b6a5f",
	Const: "triangle_total_retraction",
	Type:  "module_ops(C, D) → num → (num → U → D) → num → U → D",
	Equations: []string{
		"∀N:module_ops(C, D). ∀n:num. ∀v:(num → U → D). " +
			"    triangle_total_retraction(N, n, v) = " +
			"    (λp:num. λt:U. " +
			"        N.add(v(p, t), " +
			"            N.neg(triangle_total_section(N, " +
			"                    n, " +
			"                    double_total_map(triangle_projection, n, v), " +
			"                    p, " +
			"                    t))))",
	},
	Reading: "The inclusion of totals is the identity on functions, so the retraction " +
		"is v − τ(π(v)); that it lands in the left total is the exactness of each cell at " +
		"the middle, a function the projection kills being supported on the first-tag names.",
	Deps: []registry.EntryLike{triangleTotalSectionDef, TriangleProjectionDef},
})}

// ---------------------------------------------------------------------------
// The diagram with coefficients in T
// ---------------------------------------------------------------------------

// TriangleTotalsBased — with coefficients in T, the left, middle and right
// totals and the total with constant rows are based complexes, each cell
// based by the identity.
var TriangleTotalsBased = triangleTotalsBasedThm{family.Add(registry.ProofEntry{
	Name: "TriangleTotalsBased",
	Key:  "prop_858ae541dd965e6f",
	Reading: "With coefficients in T each cell is the free module over T on its " +
		"generators, and a total's generators of degree n are the pairs (p, s), s a " +
		"generator of the cell (p, n − p). With coefficients in a module N the cells " +
		"need not be free; that is why the chain-level diagram takes its coefficients " +
		"in T and the cohomology with coefficients in N is reached through the dual.",
	Deps: []registry.EntryLike{
		free_complex_duality.DoubleTotalBased,
		TriangleLeftDouble,
		TriangleMiddleDouble,
		TriangleRightDouble,
		ConstantCotangentDouble,
		triangleLeftDef,
		triangleMiddleDef,
		triangleRightDef,
		constantCotangentDef,
		cotangent_complex.CotangentComplexDef,
		cotangent_complex.DifferentialComplexDef,
		function_module.FiniteSuppModuleDef,
		free_module.FreeModuleRecordDef,
		TriangleLeftTotalDef,
		TriangleMiddleTotalDef,
		TriangleRightTotalDef,
		constantCotangentTotalDef,
		comm_ring.AlternatingSignDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀T:ring_ops(C). ∀g:(B → C).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
		},
		Conclusion: "based_chain_complex(T, " +
			"    «leftTotalScalar», " +
			"    double_total_basis(«leftCells»), " +
			"    «totalExpand», " +
			"    «totalCoordinates») ∧ " +
			"based_chain_complex(T, " +
			"    «middleTotalScalar», " +
			"    double_total_basis(triangle_column_names(R, S, T)), " +
			"    «totalExpand», " +
			"    «totalCoordinates») ∧ " +
			"based_chain_complex(T, " +
			"    «rightTotalScalar», " +
			"    double_total_basis(relative_names(R, S, T)), " +
			"    «totalExpand», " +
			"    «totalCoordinates») ∧ " +
			"based_chain_complex(T, " +
			"    «squareConstantTotal», " +
			"    double_total_basis(«squareConstantCells»), " +
			"    «totalExpand», " +
			"    «totalCoordinates»)",
		Abbrev: Abbrev{
			{Name: "squareConstantTotal", Text: "constant_cotangent_total⟨U:U⟩(R, " +
				"    T, " +
				"    λa:A. g(f(a)), " +
				"    regular_module(T))"},
			{Name: "squareConstantCells", Text: "λp:num. λq:num. standard_names(R, T, q)"},
			{Name: "leftTotalScalar", Text: "triangle_left_total(R, S, f, T, g, regular_module(T))"},
			{Name: "middleTotalScalar", Text: "triangle_middle_total(R, S, f, T, g, regular_module(T))"},
			{Name: "rightTotalScalar", Text: "triangle_right_total⟨U:U⟩(R, S, f, T, g, regular_module(T))"},
			{Name: "leftCells", Text: "λp:num. λq:num. image(universe_tag(0), standard_names(R, S, p))"},
			{Name: "totalExpand", Text: "double_total_expand(finite_supp_module(regular_module(T), 𝕌⟨A:U⟩), " +
				"    λp:num. λq:num. λa:(U → C). a)"},
			{Name: "totalCoordinates", Text: "double_total_coordinates(T, λp:num. λq:num. λu:(U → C). u)"},
		},
	},
		"DoubleTotalBased at each double complex — TriangleLeftDouble, TriangleMiddleDouble, "+
			"TriangleRightDouble, and ConstantCotangentDouble at g ∘ f, all with coefficients in "+
			"regular_module(T), a module over the commutative ring T — with the identity on each cell. "+
			"Every cell is finite_supp(T.zero, T.carrier, X) for its generators X (triangleLeftDef, "+
			"triangleMiddleDef, triangleRightDef, constantCotangentDef with CotangentComplexDef and "+
			"DifferentialComplexDef), the free module on X, and finite_supp_module restricted to it is "+
			"free_module_record(T, X) field by field (FiniteSuppModuleDef, FreeModuleRecordDef). The "+
			"totals are double_total at T's alternating signs (TriangleLeftTotalDef, "+
			"TriangleMiddleTotalDef, TriangleRightTotalDef, constantCotangentTotalDef, AlternatingSignDef)"),
})}

// TriangleTotalSplit — the short exact sequence of totals splits in every
// degree, by the section on every coordinate and the retraction it
// determines.
var TriangleTotalSplit = triangleTotalSplitThm{family.Add(registry.ProofEntry{
	Name: "TriangleTotalSplit",
	Key:  "prop_71fd4b07b55d09ea",
	Reading: "These are the splitting hypotheses of free_complex_duality's " +
		"FreeDualSplitShortExact and SplitZigzagDualLongExact, stated for any N; the " +
		"cohomology sequence reads them at N = T. Neither map commutes with the boundaries.",
	Deps: []registry.EntryLike{
		TriangleDegreewiseShortExact,
		triangleTotalSectionDef,
		triangleTotalRetractionDef,
		TriangleInclusionDef,
		TriangleProjectionDef,
		TriangleLeftTotalDef,
		TriangleMiddleTotalDef,
		TriangleRightTotalDef,
		chain_complex.DoubleTotalDef,
		chain_complex.DoubleTotalMapDef,
		chain_complex.DoubleTotalTermsDef,
		module_homomorphism.ModuleHomomorphismDef,
	},
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
		Conclusion: "module_homomorphism(T, " +
			"    complex_module(triangle_right_total⟨U:U⟩(R, S, f, T, g, N), n), " +
			"    complex_module(triangle_middle_total(R, S, f, T, g, N), n), " +
			"    triangle_total_section(N, n)) ∧ " +
			"module_homomorphism(T, " +
			"    complex_module(triangle_middle_total(R, S, f, T, g, N), n), " +
			"    complex_module(triangle_left_total(R, S, f, T, g, N), n), " +
			"    triangle_total_retraction⟨U:U⟩(N, n)) ∧ " +
			"(∀u:(num → U → D). " +
			"    u ∈ triangle_right_total⟨U:U⟩(R, S, f, T, g, N).terms(n) ⇒ " +
			"    double_total_map(triangle_projection, n, triangle_total_section(N, n, u)) = u) ∧ " +
			"(∀x:(num → U → D). " +
			"    x ∈ triangle_left_total(R, S, f, T, g, N).terms(n) ⇒ " +
			"    triangle_total_retraction(N, n, double_total_map(triangle_inclusion, n, x)) = x) ∧ " +
			"(∀v:(num → U → D). " +
			"    v ∈ triangle_middle_total(R, S, f, T, g, N).terms(n) ⇒ " +
			"    triangle_middle_total(R, S, f, T, g, N).add( " +
			"        double_total_map(triangle_inclusion, n, triangle_total_retraction(N, n, v)), " +
			"        triangle_total_section(N, n, double_total_map(triangle_projection, n, v))) = " +
			"    v)",
	},
		"coordinatewise, TriangleDegreewiseShortExact gives at every (p, q) the section linear and "+
			"splitting the projection, the inclusion the identity; so the section of totals is linear "+
			"into the middle total and the projection after it is the identity (triangleTotalSectionDef, "+
			"DoubleTotalMapDef, DoubleTotalTermsDef; past n every coordinate is N's zero function, which "+
			"the section keeps). The retraction v − τ(π(v)) is killed by the projection, so it lies at "+
			"each coordinate in the left term by exactness at the middle cell; it is linear, the "+
			"identity on the left total since the projection kills the left term, and the inclusion "+
			"after it plus the section after the projection is v by its definition, the inclusion being "+
			"the identity (TriangleInclusionDef, triangleTotalRetractionDef)"),
})}

// ConstantTotalAWSection — the Alexander–Whitney section of the constant
// rows is a chain map from L_{T/R} ⊗ T to their total, a strict section of
// the edge that reads coordinate 0, and a homotopy inverse of that edge.
var ConstantTotalAWSection = constantTotalAWSectionThm{family.Add(registry.ProofEntry{
	Name: "ConstantTotalAWSection",
	Key:  "prop_addc88a58e2b4c5e",
	Reading: "The section is strict on one side only: coordinate p of the " +
		"section at u(0) is the p-fold 0-th vertical face of u(0), not u(p), " +
		"so the section after the edge is the identity only up to the homotopy.",
	Deps: []registry.EntryLike{
		cotangent_complex.CotangentScalarBased,
		free_complex_duality.BasedQuasiIsomorphismHomotopyEquivalence,
		chain_complex.ChainHomotopyEquivalenceCancel,
		constantTotalAWSectionDef,
		ConstantCotangentBisimplicial,
		constantCotangentTotalDef,
		ConstantRowsTotal,
		TriangleTotalsBased,
		simplicial_module.AlexanderWhitneyChainMap,
		simplicial_module.AlexanderWhitneyConstantHorizontal,
		simplicial_module.FaceComplexDef,
		simplicial_homotopy.BisimplicialDiagonalSimplicesDef,
		simplicial_homotopy.BisimplicialDiagonalFaceDef,
		cotangent_complex.CotangentComplexDef,
		cotangent_complex.DifferentialComplexDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀T:ring_ops(C). ∀g:(B → C).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
		},
		Conclusion: "chain_map(T, " +
			"    cotangent_complex⟨U:U⟩(R, T, λa:A. g(f(a)), T, λc:C. c, regular_module(T)), " +
			"    constant_cotangent_total⟨U:U⟩(R, T, λa:A. g(f(a)), regular_module(T)), " +
			"    constant_total_aw_section(R, T, λa:A. g(f(a)), regular_module(T))) ∧ " +
			"(∀n:num. ∀y:(U → C). " +
			"    y ∈ cotangent_complex⟨U:U⟩(R, T, λa:A. g(f(a)), T, λc:C. c, regular_module(T)).terms(n) ⇒ " +
			"    constant_total_aw_section(R, T, λa:A. g(f(a)), regular_module(T), n, y, 0) = y) ∧ " +
			"(∃h:(num → (num → U → C) → num → U → C). " +
			"    chain_homotopy(T, " +
			"        constant_cotangent_total⟨U:U⟩(R, T, λa:A. g(f(a)), regular_module(T)), " +
			"        constant_cotangent_total⟨U:U⟩(R, T, λa:A. g(f(a)), regular_module(T)), " +
			"        λn:num. λu:(num → U → C). " +
			"            constant_total_aw_section(R, T, λa:A. g(f(a)), regular_module(T), n, u(0)), " +
			"        λn:num. λu:(num → U → C). u, " +
			"        h))",
	},
		"AlexanderWhitneyChainMap at ConstantCotangentBisimplicial (at g ∘ f, with coefficients in T) "+
			"is a chain map from the face complex of the diagonal into the total; the horizontal faces are "+
			"identities, so the diagonal's faces are the cotangent complex's own and the face complex is "+
			"L_{T/R} ⊗ T on terms and boundaries, all a chain map reads (BisimplicialDiagonalSimplicesDef, "+
			"BisimplicialDiagonalFaceDef, FaceComplexDef, CotangentComplexDef, DifferentialComplexDef). "+
			"AlexanderWhitneyConstantHorizontal reads coordinate 0 as y. So the section is a strict "+
			"section of the edge λm u. u(0), a quasi-isomorphism (ConstantRowsTotal) between based "+
			"complexes (TriangleTotalsBased, CotangentScalarBased), hence a chain homotopy equivalence "+
			"(BasedQuasiIsomorphismHomotopyEquivalence), and the third clause of "+
			"ChainHomotopyEquivalenceCancel makes the section after the edge homotopic to the identity"),
})}

// MiddleTotalChainComparison — the comparison after the Alexander–Whitney
// section, from L_{T/R} ⊗ T into the middle total, is a quasi-isomorphism
// with a chain homotopy inverse.
var MiddleTotalChainComparison = middleTotalChainComparisonThm{family.Add(registry.ProofEntry{
	Name: "MiddleTotalChainComparison",
	Key:  "prop_667e1ef7dc7c01e",
	Deps: []registry.EntryLike{
		cotangent_complex.CotangentScalarBased,
		free_complex_duality.BasedQuasiIsomorphismHomotopyEquivalence,
		middleTotalChainComparisonDef,
		MiddleTotalQuasiIsomorphism,
		ConstantTotalAWSection,
		ConstantRowsTotal,
		TriangleTotalsBased,
		chain_complex.QuasiIsomorphismCompose,
		chain_complex.QuasiIsomorphismDef,
		chain_complex.HomologyMapCoset,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀T:ring_ops(C). ∀g:(B → C).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
		},
		Conclusion: "quasi_isomorphism(T, " +
			"    cotangent_complex⟨U:U⟩(R, T, λa:A. g(f(a)), T, λc:C. c, regular_module(T)), " +
			"    triangle_middle_total(R, S, f, T, g, regular_module(T)), " +
			"    middle_total_chain_comparison(R, S, f, T, g, regular_module(T))) ∧ " +
			"(∃k:(num → (num → U → C) → U → C). " +
			"    chain_homotopy_equivalence(T, " +
			"        cotangent_complex⟨U:U⟩(R, T, λa:A. g(f(a)), T, λc:C. c, regular_module(T)), " +
			"        triangle_middle_total(R, S, f, T, g, regular_module(T)), " +
			"        middle_total_chain_comparison(R, S, f, T, g, regular_module(T)), " +
			"        k))",
	},
		"the comparison is the comparison of totals, a quasi-isomorphism "+
			"(MiddleTotalQuasiIsomorphism with coefficients in T), after the Alexander–Whitney section "+
			"of the constant rows (middleTotalChainComparisonDef). That section is a quasi-isomorphism: "+
			"the edge λm u. u(0) after it is the identity on the terms (ConstantTotalAWSection) and the "+
			"edge is one (ConstantRowsTotal), so on homology the section is the edge's inverse "+
			"(HomologyMapCoset, QuasiIsomorphismDef), and QuasiIsomorphismCompose gives the first "+
			"conjunct. L_{T/R} ⊗ T and the middle total are based (CotangentScalarBased, "+
			"TriangleTotalsBased), so BasedQuasiIsomorphismHomotopyEquivalence gives the inverse"),
})}

// LeftTotalAWSection — the Alexander–Whitney section of the left
// bisimplicial module is a chain map from L_{S/R} ⊗ T to the left total, a
// strict section of the left edge, and a homotopy inverse of it.
var LeftTotalAWSection = leftTotalAWSectionThm{family.Add(registry.ProofEntry{
	Name: "LeftTotalAWSection",
	Key:  "prop_c6786a162703b02",
	Reading: "The section is strict on one side only: coordinate p of the section at z " +
		"is a horizontal front face of z under the first tag, and the edge reads coordinate " +
		"n alone, so the section after the edge is the identity only up to the homotopy.",
	Deps: []registry.EntryLike{
		cotangent_complex.CotangentScalarBased,
		free_complex_duality.BasedQuasiIsomorphismHomotopyEquivalence,
		chain_complex.ChainHomotopyEquivalenceCancel,
		leftTotalAWSectionDef,
		TriangleLeftBisimplicial,
		LeftColumnsConstant,
		LeftTotalAugmented,
		LeftTotalQuasiIsomorphism,
		TriangleLeftEpsDef,
		TriangleTotalsBased,
		simplicial_module.AlexanderWhitneyChainMap,
		simplicial_module.AlexanderWhitneyConstantVertical,
		chain_complex.DoubleEdgeDef,
		simplicial_ring.TagInjective,
		functions.InverseOnLeft,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀T:ring_ops(C). ∀g:(B → C).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
		},
		Conclusion: "chain_map(T, " +
			"    cotangent_complex⟨U:U⟩(R, S, f, T, g, regular_module(T)), " +
			"    triangle_left_total(R, S, f, T, g, regular_module(T)), " +
			"    left_total_aw_section(R, S, f, T, g, regular_module(T))) ∧ " +
			"(∀n:num. ∀z:(U → C). " +
			"    z ∈ cotangent_complex⟨U:U⟩(R, S, f, T, g, regular_module(T)).terms(n) ⇒ " +
			"    double_edge(triangle_left_eps, " +
			"        n, " +
			"        left_total_aw_section(R, S, f, T, g, regular_module(T), n, z)) = " +
			"    z) ∧ " +
			"(∃h:(num → (num → U → C) → num → U → C). " +
			"    chain_homotopy(T, " +
			"        triangle_left_total(R, S, f, T, g, regular_module(T)), " +
			"        triangle_left_total(R, S, f, T, g, regular_module(T)), " +
			"        λn:num. λu:(num → U → C). " +
			"            left_total_aw_section(R, " +
			"                S, " +
			"                f, " +
			"                T, " +
			"                g, " +
			"                regular_module(T), " +
			"                n, " +
			"                double_edge(triangle_left_eps, n, u)), " +
			"        λn:num. λu:(num → U → C). u, " +
			"        h))",
	},
		"z under the first tag lies on the diagonal of the left bisimplicial module "+
			"(TriangleLeftBisimplicial), whose face complex is L_{S/R} ⊗ T under the first tag: its "+
			"vertical faces are identities on the left term (LeftColumnsConstant) and its horizontal "+
			"faces are P's faces carried by the first tag, the cotangent complex's faces (as in "+
			"LeftTotalAugmented). AlexanderWhitneyChainMap makes the section a chain map; "+
			"AlexanderWhitneyConstantVertical reads the corner (n, 0) as the tagged z, and the left "+
			"edge untags it (DoubleEdgeDef, TriangleLeftEpsDef, TagInjective, InverseOnLeft). The "+
			"edge is a quasi-isomorphism (LeftTotalQuasiIsomorphism with coefficients in T) between "+
			"based complexes (TriangleTotalsBased, CotangentScalarBased), so a chain homotopy "+
			"equivalence (BasedQuasiIsomorphismHomotopyEquivalence), and the third clause of "+
			"ChainHomotopyEquivalenceCancel makes the section after the edge homotopic to the identity"),
})}

// TransitivityLeftHomotopyOnSection — on the left Alexander–Whitney
// section, the inclusion of totals is chain homotopic to the middle
// comparison after the map g induces.
var TransitivityLeftHomotopyOnSection = transitivityLeftHomotopyOnSectionThm{family.Add(registry.ProofEntry{
	Name: "TransitivityLeftHomotopyOnSection",
	Key:  "prop_1ed58bb0e191286b",
	Reading: "The chain-level content of TransitivityLeftMapNatural, stopped " +
		"before homology: the homotopy is kept because the cohomology sequence " +
		"transposes it. The two maps differ on chains already in degree 0.",
	Deps: []registry.EntryLike{
		chain_complex.ChainHomotopyCalculus,
		leftTotalAWSectionDef,
		middleTotalChainComparisonDef,
		constantTotalAWSectionDef,
		TriangleInclusionDef,
		TriangleMiddleBisimplicial,
		TriangleLeftBisimplicial,
		ConstantCotangentBisimplicial,
		MiddleComparisonBisimplicialMap,
		MiddleComparisonDoubleMap,
		MiddleDiagonalDifferential,
		standard_resolution.RelativeDiagonalResolution,
		standard_resolution.RelativeDiagonalBaseInclusion,
		standard_resolution.RelativeDiagonalFromAbsolute,
		standard_resolution.StandardMapAlgebraMap,
		standard_resolution.StandardMapAugmentation,
		standard_resolution.StandardPolynomialAlgebra,
		resolution_comparison.SimplicialAlgebraMapCompose,
		resolution_comparison.ComparisonHomotopyExists,
		simplicial_ring.AugmentedAlongRingMap,
		cotangent_complex.DifferentialHomotopyChainHomotopy,
		cotangent_complex.DifferentialMapChainMap,
		cotangent_complex.DifferentialMapCompose,
		simplicial_module.AlexanderWhitneyChainMap,
		simplicial_module.AlexanderWhitneyNatural,
		partial_derivative.JacobianDelta,
		partial_derivative.PartialVar,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀T:ring_ops(C). ∀g:(B → C).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
		},
		Conclusion: "∃H:(num → (U → C) → num → U → C). " +
			"    chain_homotopy(T, " +
			"        cotangent_complex⟨U:U⟩(R, S, f, T, g, regular_module(T)), " +
			"        triangle_middle_total(R, S, f, T, g, regular_module(T)), " +
			"        λn:num. λz:(U → C). " +
			"            double_total_map(triangle_inclusion, " +
			"                n, " +
			"                left_total_aw_section(R, S, f, T, g, regular_module(T), n, z)), " +
			"        λn:num. λz:(U → C). " +
			"            middle_total_chain_comparison(R, " +
			"                S, " +
			"                f, " +
			"                T, " +
			"                g, " +
			"                regular_module(T), " +
			"                n, " +
			"                differential_map(R, " +
			"                    standard_names(R, S), " +
			"                    standard_names(R, T), " +
			"                    standard_face(R, T, λa:A. g(f(a))), " +
			"                    λu:U. standard_eps(R, T, λa:A. g(f(a)), u), " +
			"                    standard_map(R, S, T, g), " +
			"                    regular_module(T), " +
			"                    n, " +
			"                    z)), " +
			"        H)",
	},
		"on the diagonal of the relative standard resolution, a polynomial resolution of T over R "+
			"(RelativeDiagonalResolution), the first-tag inclusion F of P and G = relative_from_absolute "+
			"∘ standard_map(R, S, T, g) are simplicial algebra maps from P covering g "+
			"(RelativeDiagonalBaseInclusion, RelativeDiagonalFromAbsolute, StandardMapAlgebraMap, "+
			"SimplicialAlgebraMapCompose, StandardMapAugmentation); ComparisonHomotopyExists joins them, "+
			"and DifferentialHomotopyChainHomotopy makes their Jacobians chain homotopic as maps from "+
			"L_{S/R} ⊗ T into the differential complex of the diagonal (DifferentialMapChainMap, "+
			"AugmentedAlongRingMap at StandardPolynomialAlgebra). That complex is on its terms the face "+
			"complex of the diagonal of the middle bisimplicial module (MiddleDiagonalDifferential), "+
			"which the Alexander–Whitney map AW carries into the middle total by a chain map "+
			"(AlexanderWhitneyChainMap at TriangleMiddleBisimplicial); H is AW after that homotopy "+
			"(ChainHomotopyCalculus). AW ∘ J(F) is the inclusion after the left section: J(F)(z) is z "+
			"under the first tag (JacobianDelta, PartialVar), and the left and middle bisimplicial "+
			"modules share their faces (TriangleLeftBisimplicial, leftTotalAWSectionDef). AW ∘ J(G) is "+
			"the comparison after the map g induces: J(G) is the diagonal comparison after the Jacobian "+
			"of standard_map(R, S, T, g) (DifferentialMapCompose, MiddleDiagonalDifferential), and AW "+
			"after the comparison is the total comparison after the constant rows' AW "+
			"(AlexanderWhitneyNatural at MiddleComparisonBisimplicialMap and "+
			"ConstantCotangentBisimplicial, linear by MiddleComparisonDoubleMap), which is "+
			"middle_total_chain_comparison (middleTotalChainComparisonDef, constantTotalAWSectionDef)"),
})}

// TransitivityLeftChainSquare — the left square of the diagram commutes up
// to chain homotopy: the inclusion of totals is homotopic to the middle
// comparison after the map g induces after the left edge.
var TransitivityLeftChainSquare = transitivityLeftChainSquareThm{family.Add(registry.ProofEntry{
	Name: "TransitivityLeftChainSquare",
	Key:  "prop_368a49db89b3017d",
	Deps: []registry.EntryLike{
		chain_complex.ChainHomotopyCalculus,
		TransitivityLeftHomotopyOnSection,
		LeftTotalAWSection,
		TriangleInclusionDoubleMap,
		TriangleLeftDouble,
		TriangleMiddleDouble,
		LeftTotalQuasiIsomorphism,
		MiddleTotalChainComparison,
		chain_complex.DoubleComplexMapTotal,
		cotangent_complex.CotangentFunctorialMap,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀T:ring_ops(C). ∀g:(B → C).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
		},
		Conclusion: "∃h:(num → (num → U → C) → num → U → C). " +
			"    chain_homotopy(T, " +
			"        triangle_left_total(R, S, f, T, g, regular_module(T)), " +
			"        triangle_middle_total(R, S, f, T, g, regular_module(T)), " +
			"        double_total_map(triangle_inclusion), " +
			"        λn:num. λu:(num → U → C). " +
			"            middle_total_chain_comparison(R, " +
			"                S, " +
			"                f, " +
			"                T, " +
			"                g, " +
			"                regular_module(T), " +
			"                n, " +
			"                differential_map(R, " +
			"                    standard_names(R, S), " +
			"                    standard_names(R, T), " +
			"                    standard_face(R, T, λa:A. g(f(a))), " +
			"                    λu:U. standard_eps(R, T, λa:A. g(f(a)), u), " +
			"                    standard_map(R, S, T, g), " +
			"                    regular_module(T), " +
			"                    n, " +
			"                    double_edge(triangle_left_eps, n, u))), " +
			"        h)",
	},
		"with i the inclusion of totals and a the left edge, H from "+
			"TransitivityLeftHomotopyOnSection (i after the left section homotopic to the "+
			"comparison after the map g induces) and K from LeftTotalAWSection (the left section "+
			"after a homotopic to the identity), H ∘ a − i ∘ K joins i to the comparison after "+
			"the map g induces after a: precompose H with a, postcompose K with i and negate, and "+
			"add (ChainHomotopyCalculus). The maps are chain maps: i (TriangleInclusionDoubleMap, "+
			"DoubleComplexMapTotal), a (LeftTotalQuasiIsomorphism with coefficients in T), the "+
			"map g induces (CotangentFunctorialMap), the comparison (MiddleTotalChainComparison)"),
})}

// TransitivityRightChainSquare — the right square commutes on the nose:
// the right edge after the projection after the middle comparison is the
// change of base, on every chain.
var TransitivityRightChainSquare = transitivityRightChainSquareThm{family.Add(registry.ProofEntry{
	Name: "TransitivityRightChainSquare",
	Key:  "prop_4eb460eaecd64e32",
	Reading: "On every chain, not only on cycles; the " +
		"cohomology sequence uses it with the zero homotopy.",
	Deps: []registry.EntryLike{
		middleTotalChainComparisonDef,
		constantTotalAWSectionDef,
		ConstantCotangentBisimplicial,
		triangleMiddleComparisonDef,
		TriangleProjectionDef,
		TriangleRightEpsDef,
		TriangleRowAugmentationDef,
		simplicial_module.AlexanderWhitneyConstantHorizontal,
		chain_complex.DoubleTotalMapDef,
		simplicial_ring.TagInjective,
		partial_derivative.JacobianCompose,
		partial_derivative.JacobianCongruence,
		partial_derivative.JacobianDelta,
		partial_derivative.PartialVar,
		standard_resolution.RelativeFromAbsoluteMap,
		standard_resolution.RelativeFromAbsoluteDef,
		standard_resolution.RelativeHorizontalEpsVertical,
		standard_resolution.RelativeHorizontalEpsDef,
		standard_resolution.StandardBaseChangeDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀n:num. " +
			"∀y:(U → C).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"y ∈ cotangent_complex⟨U:U⟩(R, T, λa:A. g(f(a)), T, λc:C. c, regular_module(T)).terms(n)",
		},
		Conclusion: "triangle_right_eps(R, " +
			"    S, " +
			"    f, " +
			"    T, " +
			"    regular_module(T), " +
			"    n, " +
			"    double_total_map(triangle_projection, " +
			"        n, " +
			"        middle_total_chain_comparison(R, S, f, T, g, regular_module(T), n, y), " +
			"        0)) = " +
			"free_algebra_jacobian(universe_embedding(R), " +
			"    universe_embedding(S), " +
			"    R, " +
			"    S, " +
			"    standard_names(R, T, n), " +
			"    standard_names(S, T, n), " +
			"    standard_base_change(R, S, f, n), " +
			"    standard_to_base(S, T, g, n), " +
			"    regular_module(T), " +
			"    y)",
	},
		"the right edge reads coordinate 0, and coordinate 0 of the comparison at y is the comparison "+
			"at (0, n) of coordinate 0 of the constant rows' section at y, which is y "+
			"(AlexanderWhitneyConstantHorizontal at ConstantCotangentBisimplicial, DoubleTotalMapDef, "+
			"middleTotalChainComparisonDef, constantTotalAWSectionDef). Both sides are then the "+
			"pushforward of y along a map of names, each entry the augmentation of one; at n = 0 both "+
			"maps are the identity on the tags of T's elements, and at n = m + 1 the left one is x ↦ "+
			"triangle_row_augmentation(R, S, f, 0, m + 1, relative_from_absolute(R, m, x)), the "+
			"comparison carrying the variable of x to that of the second tag of relative_from_absolute(R, "+
			"m, x) and the projection untagging it (triangleMiddleComparisonDef, RelativeFromAbsoluteDef, "+
			"RelativeFromAbsoluteMap, TriangleProjectionDef, TagInjective, TriangleRightEpsDef, "+
			"JacobianDelta, PartialVar), and the right one x ↦ standard_base_change(R, S, f, m, x) "+
			"(StandardBaseChangeDef). They agree: triangle_row_augmentation(R, S, f, 0, q + 1) is "+
			"relative_horizontal_eps(R, S, f, q) (TriangleRowAugmentationDef, RelativeHorizontalEpsDef), "+
			"and relative_horizontal_eps after relative_from_absolute is standard_base_change by "+
			"induction on the degree, each carrying a name of degree q + 1 along f by the map one degree "+
			"down (RelativeFromAbsoluteDef, StandardBaseChangeDef). That composite is the one "+
			"TransitivityRightMapNatural's Reading names; read as one Jacobian it is JacobianCompose and "+
			"JacobianCongruence at RelativeFromAbsoluteMap and RelativeHorizontalEpsVertical"),
})}
