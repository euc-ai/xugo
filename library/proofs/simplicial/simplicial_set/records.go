// records.go — a simplicial set held as one value, `simplicial_ops(A)`:
// the simplices of every dimension, the faces and the degeneracies; and
// the simplicial sets this chapter builds, each one value of the record.

package simplicial_set

import (
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/datatypes/datatype_universe"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// SimplicialOpsData — the record `simplicial_ops(A)`: `mk_simplicial(X,
// d, s)` packs the n-simplices, the faces and the degeneracies. Under a
// binder X of the type, `X.simplices(n)` is the set of n-simplices,
// `X.d(n, i, x)` the i-th face of x and `X.s(n, i, x)` its i-th
// degeneracy.
var SimplicialOpsData = family.DefineData(registry.DataEntry{
	Name: "SimplicialOps", Type: "simplicial_ops", Params: []string{"A"},
	Constructors: []proof.DataConstructorSpec{
		{Name: "mk_simplicial", Args: []string{"num → set(A)", "num → num → A → A", "num → num → A → A"}},
	},
	Fields: []registry.DataField{
		{Name: "SimplicialSimplicesDef", Const: "simplicial_simplices", Field: "simplices"},
		{Name: "SimplicialFaceDef", Const: "simplicial_face", Field: "d"},
		{Name: "SimplicialDegeneracyDef", Const: "simplicial_degeneracy", Field: "s"},
	},
	Principles: registry.DataPrinciples{
		Induction:      "SimplicialOpsInduction",
		Recursion:      "SimplicialOpsRecursion",
		Injective:      "MkSimplicialInjective",
		Extensionality: "SimplicialOpsEq",
	},
	Deps: []registry.EntryLike{
		datatype_universe.Recursion,
		datatype_universe.FamilyCons,
		datatype_universe.NodeInjective,
		pairs.PairEq,
		pairs.Fst,
		pairs.Snd,
	},
})

// recordFields are the record's three projections, read by every
// definition stated on the record.
var recordFields = []registry.EntryLike{
	SimplicialOpsData.Fields[0],
	SimplicialOpsData.Fields[1],
	SimplicialOpsData.Fields[2],
}

// RestrictSimplicialSetDef — `restrict_simplicial_set(X, Y)`: the
// simplices Y with the faces and degeneracies of X, a simplicial set
// when Y is closed under them (SubSimplicialSet).
var RestrictSimplicialSetDef = restrictSimplicialSetDefThm{family.Define(registry.DefEntry{
	Name:  "RestrictSimplicialSetDef",
	Key:   "prop_ea63e707b284b72e",
	Const: "restrict_simplicial_set",
	Type:  "simplicial_ops(A) → (num → set(A)) → simplicial_ops(A)",
	Equations: []string{
		"∀X:simplicial_ops(A). ∀Y:(num → set(A)). " +
			"    restrict_simplicial_set(X, Y) = mk_simplicial(Y, X.d, X.s)",
	},
	Deps: recordFields,
})}

// ConstantSimplicialSetDef — `constant_simplicial_set(S)`: the set S in
// every dimension, every face and degeneracy the identity.
var ConstantSimplicialSetDef = constantSimplicialSetDefThm{family.Define(registry.DefEntry{
	Name:  "ConstantSimplicialSetDef",
	Key:   "prop_f9cb8e80c21ea637",
	Const: "constant_simplicial_set",
	Type:  "set(A) → simplicial_ops(A)",
	Equations: []string{
		"∀S:set(A). " +
			"    constant_simplicial_set(S) = " +
			"    mk_simplicial(λn:num. S, λn:num. λi:num. λx:A. x, λn:num. λi:num. λx:A. x)",
	},
	Deps: recordFields,
})}

// SimplicialPointDef — `simplicial_point(a)`: the point a in every
// dimension, its faces and degeneracies the constant maps at a.
var SimplicialPointDef = simplicialPointDefThm{family.Define(registry.DefEntry{
	Name:  "SimplicialPointDef",
	Key:   "prop_c2d3aa3feeb7f5f0",
	Const: "simplicial_point",
	Type:  "A → simplicial_ops(A)",
	Equations: []string{
		"∀a:A. " +
			"    simplicial_point(a) = " +
			"    mk_simplicial(simplicial_point_simplices(a), " +
			"        λn:num. λi:num. λx:A. a, " +
			"        λn:num. λi:num. λx:A. a)",
	},
	Deps: append([]registry.EntryLike{SimplicialPointSimplicesDef}, recordFields...),
})}

// OppositeSimplicialSetDef — `opposite_simplicial_set(X)`: the simplices
// of X with the faces and degeneracies read backwards.
var OppositeSimplicialSetDef = oppositeSimplicialSetDefThm{family.Define(registry.DefEntry{
	Name:  "OppositeSimplicialSetDef",
	Key:   "prop_a1cbd50b65e24a17",
	Const: "opposite_simplicial_set",
	Type:  "simplicial_ops(A) → simplicial_ops(A)",
	Equations: []string{
		"∀X:simplicial_ops(A). " +
			"    opposite_simplicial_set(X) = " +
			"    mk_simplicial(X.simplices, opposite_face(X.d), opposite_degeneracy(X.s))",
	},
	Deps: append([]registry.EntryLike{OppositeFaceDef, OppositeDegeneracyDef}, recordFields...),
})}

// StandardSimplexDef — `standard_simplex(n)`: the monotone sequences into
// 0 .. n, with the faces and degeneracies of sequences.
var StandardSimplexDef = standardSimplexDefThm{family.Define(registry.DefEntry{
	Name:  "StandardSimplexDef",
	Key:   "prop_9c81894365385470",
	Const: "standard_simplex",
	Type:  "num → simplicial_ops(num → num)",
	Equations: []string{
		"∀n:num. " +
			"    standard_simplex(n) = " +
			"    mk_simplicial(standard_simplex_simplices(n), " +
			"        λm:num. simplex_face, " +
			"        λm:num. simplex_degeneracy)",
	},
	Deps: append(
		[]registry.EntryLike{StandardSimplexSimplicesDef, SimplexFaceDef, SimplexDegeneracyDef},
		recordFields...),
})}

// SimplexHornDef — `simplex_horn(n, k)`: the horn Λⁿₖ, the sequences
// missing a vertex other than k, with the operators of Δⁿ.
var SimplexHornDef = simplexHornDefThm{family.Define(registry.DefEntry{
	Name:  "SimplexHornDef",
	Key:   "prop_e56bb8375edaad00",
	Const: "simplex_horn",
	Type:  "num → num → simplicial_ops(num → num)",
	Equations: []string{
		"∀n k:num. " +
			"    simplex_horn(n, k) = " +
			"    restrict_simplicial_set(standard_simplex(n), simplex_horn_simplices(n, k))",
	},
	Deps: []registry.EntryLike{
		RestrictSimplicialSetDef,
		StandardSimplexDef,
		SimplexHornSimplicesDef,
	},
})}

// SimplexConeDef — `simplex_cone(X, r, k)`: the cone under the r-simplex
// k, its q-simplices the (r + q + 1)-simplices of X whose first r + 1
// vertices span k, with the operators of X past them.
var SimplexConeDef = simplexConeDefThm{family.Define(registry.DefEntry{
	Name:     "SimplexConeDef",
	Key:      "prop_55992c26b6b65fd0",
	Const:    "simplex_cone",
	Type:     "simplicial_ops(A) → num → A → simplicial_ops(A)",
	Implicit: []string{"X"},
	Equations: []string{
		"∀X:simplicial_ops(A). ∀r:num. ∀k:A. " +
			"    simplex_cone(X, r, k) = " +
			"    mk_simplicial(simplex_cone_simplices(X, r, k), " +
			"        simplex_cone_face(X.d, r), " +
			"        simplex_cone_degeneracy(X.s, r))",
	},
	Deps: append(
		[]registry.EntryLike{SimplexConeSimplicesDef, SimplexConeFaceDef, simplexConeDegeneracyDef},
		recordFields...),
})}

// SimplexBoundaryConeDef — `simplex_boundary_cone(X, r, k)`: the cone
// under the boundary of k, its q-simplices the compatible families of
// (r + q)-simplices over the faces of k.
var SimplexBoundaryConeDef = simplexBoundaryConeDefThm{family.Define(registry.DefEntry{
	Name:     "SimplexBoundaryConeDef",
	Key:      "prop_cee985dc4b78a7f3",
	Const:    "simplex_boundary_cone",
	Type:     "simplicial_ops(A) → num → A → simplicial_ops(num → A)",
	Implicit: []string{"X"},
	Equations: []string{
		"∀X:simplicial_ops(A). ∀r:num. ∀k:A. " +
			"    simplex_boundary_cone(X, r, k) = " +
			"    mk_simplicial(simplex_boundary_cone_simplices(X, r, k), " +
			"        simplex_boundary_cone_face(X.d, r), " +
			"        simplex_boundary_cone_degeneracy(X.s, r))",
	},
	Deps: append(
		[]registry.EntryLike{
			SimplexBoundaryConeSimplicesDef,
			SimplexBoundaryConeFaceDef,
			simplexBoundaryConeDegeneracyDef,
		},
		recordFields...),
})}
