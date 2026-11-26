// bisimplicial.go — bisimplicial modules: a bisimplicial set whose every
// row and every column is a simplicial module in one ambient module; their
// laws; and their double complex, the alternating face sums of the two
// directions.

package simplicial_module

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/chain_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_homotopy"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Bisimplicial modules and their double complex
// ---------------------------------------------------------------------------

// BisimplicialModule — `bisimplicial_module(R, V, D)`: a bisimplicial
// set whose every row and every column is a simplicial module in the one
// module V over R, so that each D.simplices(p, q) is a submodule of V and
// every horizontal and vertical face and degeneracy is linear.
var BisimplicialModule = bisimplicialModuleThm{family.DefineStructure(registry.DefEntry{
	Name:  "BisimplicialModule",
	Key:   "prop_39d8703af367d081",
	Const: "bisimplicial_module",
	Type:  "ring_ops(A) → module_ops(A, B) → bisimplicial_ops(B) → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀V:module_ops(A, B). ∀D:bisimplicial_ops(B). " +
			"    bisimplicial_module(R, V, D) ⇔ " +
			"    bisimplicial_set(D) ∧ " +
			"    (∀q:num. simplicial_module(R, V, bisimplicial_row(D, q))) ∧ " +
			"    (∀p:num. simplicial_module(R, V, bisimplicial_column(D, p)))",
	},
	Reading: "The rows and the columns carry the modules and the linearity, bisimplicial_set the " +
		"commutation of the two directions; the simplicial identities of a row or a column are said by " +
		"both. D.dh(p, q, i) is the i-th horizontal face out of column p on row q, into D.simplices(p − " +
		"1, q); D.dv(p, q, j) the j-th vertical face out of row q in column p, into D.simplices(p, q − 1).",
	Deps: []registry.EntryLike{SimplicialModule},
})}

// BisimplicialModuleDoubleComplex — the alternating face sums of a
// bisimplicial module in the two directions form a double complex.
var BisimplicialModuleDoubleComplex = bisimplicialModuleDoubleComplexThm{family.Add(registry.ProofEntry{
	Name: "BisimplicialModuleDoubleComplex",
	Key:  "prop_365e6c90a01a2f63",
	Reading: "The two boundaries commute rather than anticommute, double_complex's convention; " +
		"the sign alternating_sign(p) enters only in the total complex. Only the face–face identities " +
		"of the rows and columns, the linearity of the faces and bisimplicial_set's commutation of dh " +
		"with dv are read; no degeneracy and no face of a vertex — h(0, q) and v(p, 0) are never read.",
	Deps: []registry.EntryLike{
		BisimplicialModule,
		chain_complex.DoubleComplex,
		FaceBoundaryHom,
		FaceComplexChain,
		FaceComplexDef,
		FaceBoundaryDef,
		chain_complex.ChainComplex,
		chain_complex.ComplexModuleDef,
		simplicial_homotopy.BisimplicialSet,
		module_homomorphism.HomSum,
		module_homomorphism.HomSmul,
		module.ModuleSumSwap,
		module.ModuleSumSmul,
	},
	Build: family.Card(
		BisimplicialModule.Statement(
			"double_complex(R, "+
				"    V, "+
				"    D.simplices, "+
				"    λp:num. λq:num. face_boundary(R, V, λm:num. λi:num. D.dh(m, q, i), p), "+
				"    λp:num. λq:num. face_boundary(R, V, λm:num. λj:num. D.dv(p, m, j), q))"),
		"unfold DoubleComplex: V is a module and each D(p, q) a submodule, from the simplicial module "+
			"of row q; the horizontal sum out of column p + 1 is linear and two in a row vanish, by "+
			"FaceBoundaryHom and FaceComplexChain at row q (ComplexModuleDef), and the vertical sums "+
			"likewise at column p. They commute: on D(p + 1, q + 1) both composites are Σ_i Σ_j (−1)^{i+j} "+
			"of a horizontal face after a vertical one, the faces being linear (HomSum, HomSmul), each "+
			"pair equal by the commutation of the two directions in bisimplicial_set (BisimplicialSet), "+
			"and the two double sums equal after exchanging them (ModuleSumSwap, ModuleSumSmul)"),
})}

// ---------------------------------------------------------------------------
// The laws of a bisimplicial module
// ---------------------------------------------------------------------------

// BisimplicialUnderlyingSet — the underlying D of a bisimplicial module is
// a bisimplicial set.
var BisimplicialUnderlyingSet = bisimplicialUnderlyingSetThm{family.Add(registry.ProofEntry{
	Name:  "BisimplicialUnderlyingSet",
	Key:   "prop_fbed8f41586c69f7",
	Build: BisimplicialModule.Axiom("bisimplicial_set(D)"),
})}

// BisimplicialRows — every row of a bisimplicial module is a simplicial
// module in V.
var BisimplicialRows = bisimplicialRowsThm{family.Add(registry.ProofEntry{
	Name:  "BisimplicialRows",
	Key:   "prop_2e760e512df67c8c",
	Build: BisimplicialModule.Axiom("∀q:num. simplicial_module(R, V, bisimplicial_row(D, q))"),
})}

// BisimplicialColumns — every column of a bisimplicial module is a
// simplicial module in V.
var BisimplicialColumns = bisimplicialColumnsThm{family.Add(registry.ProofEntry{
	Name:  "BisimplicialColumns",
	Key:   "prop_a85a5068be96be5b",
	Build: BisimplicialModule.Axiom("∀p:num. simplicial_module(R, V, bisimplicial_column(D, p))"),
})}

// BisimplicialAmbientModule — the ambient V of a bisimplicial module is a
// module: it is the ambient module of the row 0.
var BisimplicialAmbientModule = bisimplicialAmbientModuleThm{family.Add(registry.ProofEntry{
	Name: "BisimplicialAmbientModule",
	Key:  "prop_869b4b8a148d7e54",
	Build: BisimplicialModule.Law("module_on(R, V)",
		func(a *Argument, bisimplicial BisimplicialModuleFact[on.R, on.V]) {
			rowZero := a.Have(
				"the row 0 is a simplicial module in V",
				"simplicial_module(R, V, bisimplicial_row(D, 0))",
				By(BisimplicialRows.Read(bisimplicial)))
			a.Show(
				"so V is a module",
				By(AmbientModule.Read(rowZero)))
		}),
})}

// BisimplicialSubmodules — every D(p, q) is a submodule of V: it is the
// degree p of the row q.
var BisimplicialSubmodules = bisimplicialSubmodulesThm{family.Add(registry.ProofEntry{
	Name: "BisimplicialSubmodules",
	Key:  "prop_2c2fe5524bacdcf7",
	Build: BisimplicialModule.Law("∀p q:num. submodule(R, V, D.simplices(p, q))",
		func(a *Argument, bisimplicial BisimplicialModuleFact[on.R, on.V], p, q *Expr[Nat]) {
			row := a.Have(
				"the row q is a simplicial module in V",
				"simplicial_module(R, V, bisimplicial_row(D, q))",
				By(BisimplicialRows.Read(bisimplicial).At(q)))
			a.Show(
				"whose degree p is D(p, q)",
				By(SimplicesSubmodule.Read(row).At(p), simplicial_homotopy.BisimplicialRowDef))
		}),
})}

// BisimplicialHorizontalHom — every horizontal face dh(p + 1, q, i) is a
// homomorphism from D(p + 1, q) to D(p, q): it is a face of the row q.
var BisimplicialHorizontalHom = bisimplicialHorizontalHomThm{family.Add(registry.ProofEntry{
	Name: "BisimplicialHorizontalHom",
	Key:  "prop_3e5aa7515557c244",
	Build: BisimplicialModule.Law(Statement{
		Binders: "∀p q i:num.",
		Hypotheses: []string{
			"i ≤ p + 1",
		},
		Conclusion: "module_homomorphism(R, " +
			"    restrict_module(V, D.simplices(p + 1, q)), " +
			"    restrict_module(V, D.simplices(p, q)), " +
			"    D.dh(p + 1, q, i))",
	},
		func(a *Argument, bisimplicial BisimplicialModuleFact[on.R, on.V], p, q, i *Expr[Nat], bound Fact) {
			row := a.Have(
				"the row q is a simplicial module in V",
				"simplicial_module(R, V, bisimplicial_row(D, q))",
				By(BisimplicialRows.Read(bisimplicial).At(q)))
			a.Show(
				"a horizontal face is a face of the row q",
				By(bound, FaceHom.Read(row).At(p, i), simplicial_homotopy.BisimplicialRowDef))
		}),
})}

// BisimplicialVerticalHom — every vertical face dv(p, q + 1, j) is a
// homomorphism from D(p, q + 1) to D(p, q): it is a face of the column p.
var BisimplicialVerticalHom = bisimplicialVerticalHomThm{family.Add(registry.ProofEntry{
	Name: "BisimplicialVerticalHom",
	Key:  "prop_91a5dcf1d2de8053",
	Build: BisimplicialModule.Law(Statement{
		Binders: "∀p q j:num.",
		Hypotheses: []string{
			"j ≤ q + 1",
		},
		Conclusion: "module_homomorphism(R, " +
			"    restrict_module(V, D.simplices(p, q + 1)), " +
			"    restrict_module(V, D.simplices(p, q)), " +
			"    D.dv(p, q + 1, j))",
	},
		func(a *Argument, bisimplicial BisimplicialModuleFact[on.R, on.V], p, q, j *Expr[Nat], bound Fact) {
			column := a.Have(
				"the column p is a simplicial module in V",
				"simplicial_module(R, V, bisimplicial_column(D, p))",
				By(BisimplicialColumns.Read(bisimplicial).At(p)))
			a.Show(
				"a vertical face is a face of the column p",
				By(bound, FaceHom.Read(column).At(q, j), simplicial_homotopy.BisimplicialColumnDef))
		}),
})}

// DiagonalFaceHom — the face i of the diagonal out of dimension n + 1,
// the vertical face dv(n + 1, n + 1, i) followed by the horizontal face
// dh(n + 1, n, i), is a homomorphism from D(n + 1, n + 1) to D(n, n): a
// composite of two homomorphisms.
var DiagonalFaceHom = diagonalFaceHomThm{family.Add(registry.ProofEntry{
	Name: "DiagonalFaceHom",
	Key:  "prop_dba106e689821a",
	Build: BisimplicialModule.Law(Statement{
		Binders: "∀n i:num.",
		Hypotheses: []string{
			"i ≤ n + 1",
		},
		Conclusion: "module_homomorphism(R, " +
			"    restrict_module(V, D.simplices(n + 1, n + 1)), " +
			"    restrict_module(V, D.simplices(n, n)), " +
			"    λx:B. D.dh(n + 1, n, i, D.dv(n + 1, n + 1, i, x)))",
	},
		func(a *Argument, bisimplicial BisimplicialModuleFact[on.R, on.V], n, i *Expr[Nat], bound Fact) {
			a.Show(
				"a diagonal face composes one vertical and one horizontal face",
				By(
					bound,
					BisimplicialHorizontalHom.Read(bisimplicial).At(n, n, i),
					BisimplicialVerticalHom.Read(bisimplicial).At(a.TermAs[Nat]("n + 1"), n, i),
					module_homomorphism.HomCompose.At(
						a.TermAs[RingOps[A]]("R"),
						a.TermAs[ModuleOps[A, B]]("restrict_module(V, D.simplices(n + 1, n + 1))"),
						a.TermAs[ModuleOps[A, B]]("restrict_module(V, D.simplices(n + 1, n))"),
						a.TermAs[ModuleOps[A, B]]("restrict_module(V, D.simplices(n, n))"),
						a.TermAs[Fun[B, B]]("D.dv(n + 1, n + 1, i)"),
						a.TermAs[Fun[B, B]]("D.dh(n + 1, n, i)")),
					functions.ComposeApply))
		}),
})}

// DiagonalSimplicialModule — the diagonal of a bisimplicial module is a
// simplicial module in the same V. Its degree n is D(n, n), a submodule;
// its face i out of n + 1 is the vertical face followed by the horizontal
// one (DiagonalFaceHom), and its degeneracy i out of n is the vertical
// degeneracy, linear in the column n, followed by the horizontal one,
// linear in the row n + 1.
var DiagonalSimplicialModule = diagonalSimplicialModuleThm{family.Add(registry.ProofEntry{
	Name: "DiagonalSimplicialModule",
	Key:  "prop_d8bb98e8056c039d",
	Build: BisimplicialModule.Law("simplicial_module(R, V, bisimplicial_diagonal(D))",
		func(a *Argument, bisimplicial BisimplicialModuleFact[on.R, on.V]) {
			a.Show(
				"the diagonal meets the conditions of a simplicial module",
				SimplicialModule.Intro(
					Case(
						"V is a module",
						By(BisimplicialAmbientModule.Read(bisimplicial))),
					Case(
						"every diagonal degree D(n, n) is a submodule of V",
						Simp(Fwd(simplicial_homotopy.BisimplicialDiagonalSimplicesDef)),
						By(BisimplicialSubmodules.Read(bisimplicial))),
					Case(
						"the diagonal is a simplicial set",
						By(simplicial_homotopy.DiagonalSimplicialSet, BisimplicialUnderlyingSet.Read(bisimplicial))),
					Case(
						"every diagonal face is linear",
						Derive(func(b *Argument) {
							n := b.FixAs[Nat]("n")
							i := b.FixAs[Nat]("i")
							bound := b.Assume()
							face := b.Have(
								"the face i out of n + 1 is the vertical face followed by the horizontal one",
								"bisimplicial_diagonal_face(D.dh, D.dv, n + 1, i) = "+
									"(λx:B. D.dh(n + 1, n, i, D.dv(n + 1, n + 1, i, x)))",
								Funext(),
								Simp(Fwd(simplicial_homotopy.BisimplicialDiagonalFaceDef)),
								ByArith())
							b.Show(
								"which is linear from D(n + 1, n + 1) to D(n, n)",
								Simp(Fwd(face), Fwd(simplicial_homotopy.BisimplicialDiagonalSimplicesDef)),
								By(bound, DiagonalFaceHom.Read(bisimplicial).At(n, i)))
						})),
					Case(
						"every diagonal degeneracy is linear",
						Derive(func(b *Argument) {
							n := b.FixAs[Nat]("n")
							i := b.FixAs[Nat]("i")
							bound := b.Assume()
							degeneracy := b.Have(
								"the degeneracy i out of n is the vertical degeneracy followed by the horizontal one",
								"bisimplicial_diagonal_degeneracy(D.sh, D.sv, n, i) = (λx:B. D.sh(n, n + 1, i, D.sv(n, n, i, x)))",
								Funext(),
								By(simplicial_homotopy.BisimplicialDiagonalDegeneracyDef))
							column := b.Have(
								"the column n is a simplicial module in V",
								"simplicial_module(R, V, bisimplicial_column(D, n))",
								By(BisimplicialColumns.Read(bisimplicial).At(n)))
							row := b.Have(
								"the row n + 1 is a simplicial module in V",
								"simplicial_module(R, V, bisimplicial_row(D, n + 1))",
								By(BisimplicialRows.Read(bisimplicial).At(b.TermAs[Nat]("n + 1"))))
							b.Show(
								"the vertical degeneracy into D(n, n + 1) and the "+
									"horizontal one into D(n + 1, n + 1) compose to a linear map",
								Simp(Fwd(degeneracy), Fwd(simplicial_homotopy.BisimplicialDiagonalSimplicesDef)),
								By(
									bound,
									DegeneracyHom.Read(column).At(n, i),
									DegeneracyHom.Read(row).At(n, i),
									simplicial_homotopy.BisimplicialColumnDef,
									simplicial_homotopy.BisimplicialRowDef,
									module_homomorphism.HomCompose.At(
										b.TermAs[RingOps[A]]("R"),
										b.TermAs[ModuleOps[A, B]]("restrict_module(V, D.simplices(n, n))"),
										b.TermAs[ModuleOps[A, B]]("restrict_module(V, D.simplices(n, n + 1))"),
										b.TermAs[ModuleOps[A, B]]("restrict_module(V, D.simplices(n + 1, n + 1))"),
										b.TermAs[Fun[B, B]]("D.sv(n, n, i)"),
										b.TermAs[Fun[B, B]]("D.sh(n, n + 1, i)")),
									functions.ComposeApply))
						}))))
		}),
})}
