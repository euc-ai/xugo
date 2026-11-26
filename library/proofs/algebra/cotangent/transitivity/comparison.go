// comparison.go — the double complex whose every column is the cotangent
// complex of T over R, with the identity faces horizontally, and its map
// into the middle term: in each column the Jacobian of the map of
// resolutions of T over R from the standard resolution into the column
// of Q. Each column map is a chain homotopy equivalence and the maps
// commute with the horizontal boundaries, so the totals are
// quasi-isomorphic; the total with constant rows maps quasi-isomorphically
// onto its column 0, the cotangent complex of T over R itself.

package transitivity

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/cotangent_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/standard_resolution"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/chain_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/partial_derivative"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_module"
	"github.com/euc-ai/xugo/library/registry"
)

const constantTotal = "constant_cotangent_total⟨U:U⟩(R, T, λa:A. g(f(a)), N)"

// ---------------------------------------------------------------------------
// The cotangent complex of T over R in every column
// ---------------------------------------------------------------------------

// constantCotangentDef — `constant_cotangent(R, T, φ, N, p, q)`: the term
// at (p, q) of the double complex whose every column is the cotangent
// complex of T over R through φ with coefficients in N, its term of
// degree q.
var constantCotangentDef = constantCotangentDefThm{family.Define(registry.DefEntry{
	Name:  "constantCotangentDef",
	Key:   "prop_d164d4a2d99a134e",
	Const: "constant_cotangent",
	Type:  "ring_ops(A) → ring_ops(C) → (A → C) → module_ops(C, D) → num → num → set(U → D)",
	Equations: []string{
		"∀R:ring_ops(A). ∀T:ring_ops(C). ∀φ:(A → C). ∀N:module_ops(C, D). ∀p q:num. " +
			"    constant_cotangent(R, T, φ, N, p, q) = cotangent_complex(R, T, φ, T, λc:C. c, N).terms(q)",
	},
	Reading: "The same in every column p: the finitely supported " +
		"functions on standard_names(R, T, q). In the triangle φ is λa:A. " +
		"g(f(a)), through which the columns of Q are resolutions of T over R.",
})}

// constantCotangentHorizontalDef — `constant_cotangent_horizontal(T, N, p,
// q, u)`: the horizontal boundary out of column p of the double complex
// with constant rows, the alternating sum of p + 1 identities.
var constantCotangentHorizontalDef = constantCotangentHorizontalDefThm{family.Define(registry.DefEntry{
	Name:  "constantCotangentHorizontalDef",
	Key:   "prop_74a22f6c9bb9dd7a",
	Const: "constant_cotangent_horizontal",
	Type:  "ring_ops(C) → module_ops(C, D) → num → num → (U → D) → U → D",
	Equations: []string{
		"∀T:ring_ops(C). ∀N:module_ops(C, D). ∀p q:num. ∀u:(U → D). " +
			"    constant_cotangent_horizontal(T, N, p, q, u) = " +
			"    face_boundary(T, finite_supp_module(N, 𝕌⟨A:U⟩), λn:num. λi:num. λv:(U → D). v, p, u)",
	},
	Reading: "Every horizontal face is the identity, so out of an odd column the boundary " +
		"is zero and out of an even column p ≥ 2 the identity; each row is the face complex of a " +
		"constant simplicial module, exact above column 0, augmented onto column 0 by the identity.",
})}

// constantCotangentVerticalDef — `constant_cotangent_vertical(R, T, φ, N,
// p, q)`: the vertical boundary out of (p, q) of the double complex with
// constant rows, the boundary of the cotangent complex of T over R
// through φ out of degree q.
var constantCotangentVerticalDef = constantCotangentVerticalDefThm{family.Define(registry.DefEntry{
	Name:  "constantCotangentVerticalDef",
	Key:   "prop_c3afef07c8e3f54e",
	Const: "constant_cotangent_vertical",
	Type:  "ring_ops(A) → ring_ops(C) → (A → C) → module_ops(C, D) → num → num → (U → D) → U → D",
	Equations: []string{
		"∀R:ring_ops(A). ∀T:ring_ops(C). ∀φ:(A → C). ∀N:module_ops(C, D). ∀p q:num. " +
			"    constant_cotangent_vertical(R, T, φ, N, p, q) = " +
			"    cotangent_complex(R, T, φ, T, λc:C. c, N).d(q)",
	},
	Reading: "The same in every column p, so each column is the cotangent complex of T over " +
		"R itself and the augmentation of each row onto column 0 commutes with it on the nose.",
})}

// ConstantCotangentDoubleData — `constant_cotangent_double(R, T, φ, N)`:
// the module, terms and boundaries of the double complex whose every
// column is the cotangent complex of T over R through φ, named once.
var ConstantCotangentDoubleData = family.Tuple(
	"constant_cotangent_double",
	[]string{"R", "T", "φ", "N"},
	"finite_supp_module(N, 𝕌⟨A:U⟩)",
	"constant_cotangent(R, T, φ, N)",
	"constant_cotangent_horizontal(T, N)",
	"constant_cotangent_vertical(R, T, φ, N)")

// constantCotangentTotalDef — `constant_cotangent_total(R, T, φ, N)`: the
// total complex of the double complex with constant rows.
var constantCotangentTotalDef = constantCotangentTotalDefThm{family.Define(registry.DefEntry{
	Name:  "constantCotangentTotalDef",
	Key:   "prop_d1e985b78f12af65",
	Const: "constant_cotangent_total",
	Type:  "ring_ops(A) → ring_ops(C) → (A → C) → module_ops(C, D) → complex_ops(C, num → U → D)",
	Equations: []string{
		"∀R:ring_ops(A). ∀T:ring_ops(C). ∀φ:(A → C). ∀N:module_ops(C, D). " +
			"    constant_cotangent_total(R, T, φ, N) = " +
			"    double_total(finite_supp_module(N, 𝕌⟨A:U⟩), " +
			"        constant_cotangent(R, T, φ, N), " +
			"        constant_cotangent_horizontal(T, N), " +
			"        constant_cotangent_vertical(R, T, φ, N), " +
			"        alternating_sign(T.one, T.neg))",
	},
	Reading: "Reading the coordinate 0 of a diagonal maps it quasi-isomorphically onto " +
		"the cotangent complex of T over R, and the column maps carry it quasi-isomorphically " +
		"onto the middle total: the zigzag through which the middle total computes D_n(T/R, N).",
	Deps: []registry.EntryLike{
		constantCotangentDef,
		constantCotangentHorizontalDef,
		constantCotangentVerticalDef,
	},
})}

// triangleMiddleComparisonDef — `triangle_middle_comparison(R, S, f, T,
// g, N, p, q, u)`: the map of the double complex with constant rows into
// the middle term at (p, q), the Jacobian of the map from the standard
// resolution of T over R into column p of Q, read on the differentials in
// degree q.
var triangleMiddleComparisonDef = triangleMiddleComparisonDefThm{family.Define(registry.DefEntry{
	Name:  "triangleMiddleComparisonDef",
	Key:   "prop_e79ef8aafd83bcc8",
	Const: "triangle_middle_comparison",
	Type:  towerType + "num → num → (U → D) → U → D",
	Equations: []string{
		towerBinders + "∀p q:num. ∀u:(U → D). triangle_middle_comparison(R, S, f, T, g, N, p, q, u) = " +
			"differential_map(R, standard_names(R, T), triangle_column_names(R, S, T, p), relative_vertical_face(R, S, f, T, g, p), relative_vertical_eps(R, S, f, T, g, p), " +
			"relative_from_absolute(R), N, q, u)",
	},
	Reading: "The map of resolutions relative_from_absolute does not depend on p and the " +
		"horizontal maps of Q fix every value it takes, so these Jacobians commute with the horizontal " +
		"boundaries; it is a map over T when T is an algebra over R through g ∘ f, so each column map " +
		"is one of differential complexes of two resolutions of T covering the identity of T.",
	Deps: []registry.EntryLike{TriangleColumnNamesDef},
})}

// ---------------------------------------------------------------------------
// The double complex with constant rows
// ---------------------------------------------------------------------------

// ConstantCotangentDouble — the cotangent complex of T over R repeated in
// every column, with the identity faces horizontally, is a double complex
// over T.
var ConstantCotangentDouble = constantCotangentDoubleThm{family.Add(registry.ProofEntry{
	Name: "ConstantCotangentDouble",
	Key:  "prop_d18398fd4640f4e4",
	Deps: []registry.EntryLike{
		constantCotangentDef,
		constantCotangentHorizontalDef,
		constantCotangentVerticalDef,
		chain_complex.DoubleComplex,
		chain_complex.ChainComplex,
		cotangent_complex.CotangentChainComplex,
		cotangent_complex.CotangentComplexDef,
		cotangent_complex.DifferentialComplexDef,
		ring_homomorphism.RingHomIdentity,
		ring_homomorphism.Target,
		simplicial_module.FaceBoundaryDef,
		comm_ring.AlternatingSignDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀T:ring_ops(C). ∀φ:(A → C). ∀N:module_ops(C, D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, T, φ)",
			"module_on(T, N)",
		},
		Conclusion: "double_complex(T, constant_cotangent_double(R, T, φ, N))",
	},
		"the cotangent complex of T over R through φ, at the identity of T (RingHomIdentity, T a "+
			"commutative ring by Target), is a chain complex over T (CotangentChainComplex): its "+
			"terms finite_supp(N, standard_names(R, T, q)) are submodules of finite_supp_module(N, 𝕌) "+
			"under the same operations (CotangentComplexDef, DifferentialComplexDef) and its boundary "+
			"is linear with square zero. The horizontal boundary out of column p is Σ_{i ≤ p} (−1)^i "+
			"times the identity, zero or the identity (FaceBoundaryDef, AlternatingSignDef), which "+
			"squares to zero against the next and commutes with every linear map"),
})}

// ConstantRowsTotal — the total of the double complex with constant rows
// maps quasi-isomorphically onto the cotangent complex of T over R by
// reading the coordinate 0 of a diagonal.
var ConstantRowsTotal = constantRowsTotalThm{family.Add(registry.ProofEntry{
	Name: "ConstantRowsTotal",
	Key:  "prop_93fe66a016565fe9",
	Reading: "AugmentedAssemblyRows at the identity augmentation of every row onto column 0: " +
		"each row is the face complex of a constant simplicial module, its boundaries 0 and the " +
		"identity alternately from column 1 on, and h(1, q) = 0 makes the identity augmentation onto " +
		"column 0 exact; column 0 is the cotangent complex itself, so the augmentation commutes with " +
		"the vertical boundary on the nose. Only R's and T's universes are needed; S does not occur.",
	Deps: []registry.EntryLike{
		ConstantCotangentDouble,
		constantCotangentTotalDef,
		constantCotangentDef,
		constantCotangentHorizontalDef,
		constantCotangentVerticalDef,
		chain_complex.AugmentedAssemblyRows,
		chain_complex.QuasiIsomorphismDef,
		cotangent_complex.CotangentChainComplex,
		ring_homomorphism.RingHomIdentity,
		comm_ring.AlternatingSignDef,
		simplicial_module.FaceBoundaryDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀T:ring_ops(C). ∀φ:(A → C). ∀N:module_ops(C, D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, T, φ)",
			"module_on(T, N)",
		},
		Conclusion: "quasi_isomorphism(T, " +
			"    constant_cotangent_total(R, T, φ, N), " +
			"    cotangent_complex(R, T, φ, T, λc:C. c, N), " +
			"    λm:num. λu:(num → U → D). u(0))",
	},
		"AugmentedAssemblyRows at ConstantCotangentDouble with b(q) the identity, E the "+
			"cotangent complex (CotangentChainComplex at RingHomIdentity): the identity is linear "+
			"and onto E's terms, which the double complex's terms are (constantCotangentDef); the "+
			"rows have boundaries alternately zero and the identity (constantCotangentHorizontalDef, "+
			"FaceBoundaryDef, AlternatingSignDef), exact above column 0, with the zero boundary out "+
			"of column 1 matching the injective augmentation; the vertical boundary is E's "+
			"(constantCotangentVerticalDef); the conclusion is QuasiIsomorphismDef"),
})}

// ---------------------------------------------------------------------------
// The middle term against the cotangent complex of T over R
// ---------------------------------------------------------------------------

// MiddleColumnComparison — in every column the Jacobian of the map from
// the standard resolution of T over R into the column of Q is a chain
// homotopy equivalence of the differential complexes.
var MiddleColumnComparison = middleColumnComparisonThm{family.Add(registry.ProofEntry{
	Name: "MiddleColumnComparison",
	Key:  "prop_fa0a7f59b7ae1e14",
	Reading: "The two columns are the differential complexes of two polynomial " +
		"resolutions of T over R through g ∘ f — the standard one (StandardResolution at g ∘ " +
		"f) and Q(p, •) (RelativeColumnResolution) — and relative_from_absolute between them " +
		"covers the identity of T, so the card is ResolutionMapChainHomotopyEquivalence at " +
		"that map. The coefficients of both reach N through the identity of T: λu. (λc. " +
		"c)(ε(u)) there is the augmentation itself up to β and η.",
	Deps: []registry.EntryLike{
		constantCotangentDef,
		constantCotangentVerticalDef,
		triangleMiddleDef,
		TriangleVerticalDef,
		triangleMiddleComparisonDef,
		cotangent_complex.ResolutionMapChainHomotopyEquivalence,
		cotangent_complex.CotangentComplexDef,
		cotangent_complex.DifferentialComplexDef,
		standard_resolution.StandardResolution,
		standard_resolution.RelativeColumnResolution,
		standard_resolution.RelativeFromAbsoluteMap,
		ring_homomorphism.RingHomIdentity,
		ring_homomorphism.RingHomomorphism,
		chain_complex.DoubleColumnDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D). " +
			"∀p:num.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"module_on(T, N)",
		},
		Conclusion: "∃G:(num → (U → D) → U → D). " +
			"    chain_homotopy_equivalence(T, " +
			"        double_column(finite_supp_module(N, 𝕌⟨A:U⟩), " +
			"            constant_cotangent(R, T, λa:A. g(f(a)), N), " +
			"            constant_cotangent_vertical(R, T, λa:A. g(f(a)), N), " +
			"            p), " +
			"        double_column(finite_supp_module(N, 𝕌⟨A:U⟩), " +
			"            triangle_middle(R, S, T, N), " +
			"            triangle_vertical(R, S, f, T, g, N), " +
			"            p), " +
			"        triangle_middle_comparison(R, S, f, T, g, N, p), " +
			"        G)",
	},
		"ResolutionMapChainHomotopyEquivalence at the standard resolution of T over R through "+
			"λa:A. g(f(a)), a ring map (RingHomomorphism), a resolution of T (StandardResolution), "+
			"and column p of Q (RelativeColumnResolution), with F = relative_from_absolute(R), a "+
			"simplicial algebra map covering the identity of T (RelativeFromAbsoluteMap), and the "+
			"identity of T as the coefficient map (RingHomIdentity). The two differential complexes "+
			"are the two columns (CotangentComplexDef, constantCotangentDef, "+
			"constantCotangentVerticalDef; triangleMiddleDef, TriangleVerticalDef, DoubleColumnDef, "+
			"DifferentialComplexDef) and its Jacobians the comparison (triangleMiddleComparisonDef)"),
})}

// MiddleComparisonDoubleMap — the column comparisons commute with the
// horizontal boundaries: a map of double complexes from the double
// complex with constant rows to the middle term.
var MiddleComparisonDoubleMap = middleComparisonDoubleMapThm{family.Add(registry.ProofEntry{
	Name: "MiddleComparisonDoubleMap",
	Key:  "prop_732335f729b14dba",
	Reading: "No horizontal map of Q moves a value of relative_from_absolute, which lands in " +
		"the algebra on second-tag names alone; so each horizontal face after the comparison out of " +
		"column p + 1 is the comparison out of column p, and the alternating sums of p + 2 " +
		"identities and of p + 2 such faces agree. relative_from_absolute does not depend on p, and " +
		"every horizontal map of Q fixes its values (RelativeFromAbsoluteNatural holds for any h), " +
		"so both alternating sums are (Σ_{i ≤ p+1} sign(i)) times the comparison out of column p.",
	Deps: []registry.EntryLike{
		MiddleColumnComparison,
		ConstantCotangentDouble,
		TriangleMiddleDouble,
		triangleMiddleComparisonDef,
		triangleHorizontalDef,
		constantCotangentHorizontalDef,
		chain_complex.DoubleComplexMapDef,
		chain_complex.ChainHomotopyEquivalenceDef,
		chain_complex.ChainMapDef,
		standard_resolution.RelativeFromAbsoluteNatural,
		standard_resolution.RelativeAugmentationC,
		partial_derivative.JacobianCompose,
		partial_derivative.JacobianCongruence,
		cotangent_complex.DifferentialMapDef,
		simplicial_module.FaceBoundaryDef,
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
		Conclusion: "double_complex_map(T, " +
			"    constant_cotangent_double(R, T, λa:A. g(f(a)), N), " +
			"    triangle_middle_double(R, S, f, T, g, N), " +
			"    triangle_middle_comparison(R, S, f, T, g, N))",
	},
		"each column map is a chain map (MiddleColumnComparison, ChainHomotopyEquivalenceDef, "+
			"ChainMapDef), so linear and commuting with the vertical boundaries. Horizontally, each face of "+
			"Q fixes every value of relative_from_absolute (RelativeFromAbsoluteNatural), so by the chain "+
			"rule the Jacobian of the face after the comparison out of column p + 1 is the comparison out of "+
			"column p (JacobianCompose, the augmentations agreeing after the face by RelativeAugmentationC, "+
			"JacobianCongruence); the constant rows' faces are identities (constantCotangentHorizontalDef), "+
			"and the two alternating sums agree term by term (FaceBoundaryDef)"),
})}

// MiddleTotalQuasiIsomorphism — the column comparisons induce a
// quasi-isomorphism of the totals, from the total with constant rows to
// the middle total.
var MiddleTotalQuasiIsomorphism = middleTotalQuasiIsomorphismThm{family.Add(registry.ProofEntry{
	Name: "MiddleTotalQuasiIsomorphism",
	Key:  "prop_86c2823047e8552a",
	Deps: []registry.EntryLike{
		MiddleComparisonDoubleMap,
		MiddleColumnComparison,
		ConstantCotangentDouble,
		TriangleMiddleDouble,
		constantCotangentTotalDef,
		TriangleMiddleTotalDef,
		chain_complex.ColumnQuasiIsomorphismTotal,
		chain_complex.ChainHomotopyEquivalenceQuasiIsomorphism,
		chain_complex.DoubleColumnChainComplex,
		comm_ring.AlternatingSignDef,
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
			"    constant_cotangent_total⟨U:U⟩(R, T, λa:A. g(f(a)), N), " +
			"    triangle_middle_total(R, S, f, T, g, N), " +
			"    double_total_map(triangle_middle_comparison(R, S, f, T, g, N)))",
	},
		"ColumnQuasiIsomorphismTotal at ConstantCotangentDouble, TriangleMiddleDouble and "+
			"MiddleComparisonDoubleMap over T, both totals being double_total at T's alternating sign "+
			"(constantCotangentTotalDef, TriangleMiddleTotalDef, AlternatingSignDef): each column map is "+
			"a chain homotopy equivalence of chain complexes (MiddleColumnComparison, "+
			"DoubleColumnChainComplex), so a quasi-isomorphism (ChainHomotopyEquivalenceQuasiIsomorphism)"),
})}
