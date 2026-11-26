// records.go — a bisimplicial set held as one value,
// `bisimplicial_ops(A)`, and the simplicial sets read off it: its
// diagonal, its rows and its columns.

package simplicial_homotopy

import (
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/datatypes/datatype_universe"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// BisimplicialOpsData — the record `bisimplicial_ops(A)`:
// `mk_bisimplicial(X, dh, sh, dv, sv)` packs the (p, q)-simplices, the
// horizontal faces and degeneracies, and the vertical ones. Under a
// binder X of the type, `X.simplices(p, q)` is the set of
// (p, q)-simplices, `X.dh(p, q, i, x)` the i-th horizontal face out of
// column p on row q and `X.dv(p, q, j, x)` the j-th vertical face.
var BisimplicialOpsData = family.DefineData(registry.DataEntry{
	Name: "BisimplicialOps", Type: "bisimplicial_ops", Params: []string{"A"},
	Constructors: []proof.DataConstructorSpec{{
		Name: "mk_bisimplicial",
		Args: []string{
			"num → num → set(A)",
			"num → num → num → A → A",
			"num → num → num → A → A",
			"num → num → num → A → A",
			"num → num → num → A → A",
		},
	}},
	Fields: []registry.DataField{
		{Name: "BisimplicialSimplicesDef", Const: "bisimplicial_simplices", Field: "simplices"},
		{Name: "BisimplicialHorizontalFaceDef", Const: "bisimplicial_horizontal_face", Field: "dh"},
		{
			Name:  "bisimplicialHorizontalDegeneracyDef",
			Const: "bisimplicial_horizontal_degeneracy",
			Field: "sh",
		},
		{Name: "BisimplicialVerticalFaceDef", Const: "bisimplicial_vertical_face", Field: "dv"},
		{Name: "bisimplicialVerticalDegeneracyDef", Const: "bisimplicial_vertical_degeneracy", Field: "sv"},
	},
	Principles: registry.DataPrinciples{
		Induction:      "BisimplicialOpsInduction",
		Recursion:      "BisimplicialOpsRecursion",
		Injective:      "MkBisimplicialInjective",
		Extensionality: "BisimplicialOpsEq",
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

// bisimplicialFields are the record's five projections, read by every
// definition stated on the record.
var bisimplicialFields = []registry.EntryLike{
	BisimplicialOpsData.Fields[0],
	BisimplicialOpsData.Fields[1],
	BisimplicialOpsData.Fields[2],
	BisimplicialOpsData.Fields[3],
	BisimplicialOpsData.Fields[4],
}

// BisimplicialDiagonalDef — `bisimplicial_diagonal(X)`: the (n, n)-simplices
// with the composite faces and degeneracies of the two directions.
var BisimplicialDiagonalDef = bisimplicialDiagonalDefThm{family.Define(registry.DefEntry{
	Name:  "BisimplicialDiagonalDef",
	Key:   "prop_2427e3449046af52",
	Const: "bisimplicial_diagonal",
	Type:  "bisimplicial_ops(A) → simplicial_ops(A)",
	Equations: []string{
		"∀X:bisimplicial_ops(A). " +
			"    bisimplicial_diagonal(X) = " +
			"    mk_simplicial(bisimplicial_diagonal_simplices(X), " +
			"        bisimplicial_diagonal_face(X.dh, X.dv), " +
			"        bisimplicial_diagonal_degeneracy(X.sh, X.sv))",
	},
	Deps: append(
		[]registry.EntryLike{
			BisimplicialDiagonalSimplicesDef,
			BisimplicialDiagonalFaceDef,
			BisimplicialDiagonalDegeneracyDef,
		},
		bisimplicialFields...),
})}

// BisimplicialRowDef — `bisimplicial_row(X, q)`: row q, its p-simplices
// the (p, q)-simplices, with the horizontal operators.
var BisimplicialRowDef = bisimplicialRowDefThm{family.Define(registry.DefEntry{
	Name:  "BisimplicialRowDef",
	Key:   "prop_1976094ab3337c62",
	Const: "bisimplicial_row",
	Type:  "bisimplicial_ops(A) → num → simplicial_ops(A)",
	Equations: []string{
		"∀X:bisimplicial_ops(A). ∀q:num. " +
			"    bisimplicial_row(X, q) = " +
			"    mk_simplicial(λp:num. X.simplices(p, q), " +
			"        λp:num. λi:num. X.dh(p, q, i), " +
			"        λp:num. λi:num. X.sh(p, q, i))",
	},
	Deps: bisimplicialFields,
})}

// BisimplicialColumnDef — `bisimplicial_column(X, p)`: column p, its
// q-simplices the (p, q)-simplices, with the vertical operators.
var BisimplicialColumnDef = bisimplicialColumnDefThm{family.Define(registry.DefEntry{
	Name:  "BisimplicialColumnDef",
	Key:   "prop_7f3ea3aed530115a",
	Const: "bisimplicial_column",
	Type:  "bisimplicial_ops(A) → num → simplicial_ops(A)",
	Equations: []string{
		"∀X:bisimplicial_ops(A). ∀p:num. " +
			"    bisimplicial_column(X, p) = " +
			"    mk_simplicial(λq:num. X.simplices(p, q), " +
			"        λq:num. λj:num. X.dv(p, q, j), " +
			"        λq:num. λj:num. X.sv(p, q, j))",
	},
	Deps: bisimplicialFields,
})}
