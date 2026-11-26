// chain_complex.go — chain complexes of modules on sets at one type:
// a sequence of modules P.terms(n) over one ring, sharing the type's
// operations, with boundary maps P.d(n+1): P.terms(n+1) → P.terms(n) composing to
// zero; cycles, boundaries and homology, the quotient module of the
// cycles by the boundaries; chain maps and the homomorphism they
// induce on homology, written without choosing a representative;
// chain homotopy; and the long exact sequence of a short exact
// sequence of complexes, with its connecting homomorphism.
//
// The record P holds shared operations, degree carriers P.terms(n), and
// boundary maps P.d(n). The boundary out of degree zero is not read:
// every member of P.terms(0) is a cycle. The chain-complex predicate
// supplies the module and differential laws over the ring record R.

package chain_complex

import (
	"github.com/euc-ai/xugo/ext/on"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"

	. "github.com/euc-ai/xugo/library/authoring"
)

// ---------------------------------------------------------------------------
// Complexes and their homology
// ---------------------------------------------------------------------------

// ChainComplex — `chain_complex(R, P)`: every P.terms(n) is an R-module,
// every P.d(n+1) is a homomorphism to degree n, and consecutive
// boundaries compose to zero.
var ChainComplex = chainComplexThm{family.DefineStructure(registry.DefEntry{
	Name: "ChainComplex", Const: "chain_complex", Type: "ring_ops(A) → complex_ops(A, B) → bool",
	Key:     "prop_c89351ff2346d176",
	Subject: "P",
	Equations: []string{
		"∀R:ring_ops(A). ∀P:complex_ops(A, B). " +
			"    chain_complex(R, P) ⇔ " +
			"    (∀n:num. module_on(R, complex_module(P, n))) ∧ " +
			"    (∀n:num. " +
			"        module_homomorphism(R, complex_module(P, n + 1), complex_module(P, n), P.d(n + 1))) ∧ " +
			"    (∀n:num. ∀u:B. u ∈ P.terms(n + 2) ⇒ P.d(n + 1)(P.d(n + 2)(u)) = P.zero)",
	},
	Deps: []registry.EntryLike{ComplexModuleDef, ComplexDifferentialDef},
})}

// ComplexModules — every term is a module.
var ComplexModules = complexModulesThm{family.Add(registry.ProofEntry{
	Name:  "ComplexModules",
	Key:   "prop_e9f951f5994c1810",
	Build: ChainComplex.Axiom("∀n:num. module_on(R, complex_module(P, n))"),
})}

// ComplexBoundaryHom — every boundary map is a homomorphism.
var ComplexBoundaryHom = complexBoundaryHomThm{family.Add(registry.ProofEntry{
	Name: "ComplexBoundaryHom",
	Key:  "prop_3e29272a56a49e4b",
	Build: ChainComplex.Axiom(
		"∀n:num. module_homomorphism(R, complex_module(P, n + 1), complex_module(P, n), P.d(n + 1))"),
})}

// ComplexBoundaryTwice — two boundaries in a row are zero.
var ComplexBoundaryTwice = complexBoundaryTwiceThm{family.Add(registry.ProofEntry{
	Name: "ComplexBoundaryTwice",
	Key:  "prop_14353e514de9cdf4",
	Build: ChainComplex.Axiom(Statement{
		Binders: "∀n:num. ∀u:B.",
		Hypotheses: []string{
			"u ∈ P.terms(n + 2)",
		},
		Conclusion: "P.d(n + 1)(P.d(n + 2)(u)) = P.zero",
	}),
})}

// CyclesDef — `cycles(P, n)`, the complex record P: the members of
// P.terms(n) that P.d(n) kills; at degree 0, all of P.terms(0).
var CyclesDef = cyclesDefThm{family.Define(registry.DefEntry{
	Name: "CyclesDef", Const: "cycles", Type: "complex_ops(A, B) → num → set(B)",
	Key: "prop_2dc3a2bd7b5cd1fa",

	Equations: []string{
		"∀P:complex_ops(A, B). ∀n:num. " +
			"    cycles(P, n) = {u:B | u ∈ P.terms(n) ∧ (n = 0 ∨ P.d(n)(u) = P.zero)}",
	},
	Deps: []registry.EntryLike{ComplexZeroDef, ComplexTermsDef, ComplexDifferentialDef},
})}

// BoundariesDef — `boundaries(P, n)`: the image of P.d(n+1).
var BoundariesDef = boundariesDefThm{family.Define(registry.DefEntry{
	Name: "BoundariesDef", Const: "boundaries", Type: "complex_ops(A, B) → num → set(B)",
	Key: "prop_65cb68268d6e639e",

	Equations: []string{
		"∀P:complex_ops(A, B). ∀n:num. boundaries(P, n) = image(P.d(n + 1), P.terms(n + 1))",
	},
	Deps: []registry.EntryLike{ComplexTermsDef, ComplexDifferentialDef},
})}

// HomologyDef — `homology(P, n)`: the cycles modulo the boundaries, as
// cosets.
var HomologyDef = homologyDefThm{family.Define(registry.DefEntry{
	Name: "HomologyDef", Const: "homology", Type: "complex_ops(A, B) → num → set(set(B))",
	Key: "prop_baf5c770b15e54c1",

	Equations: []string{
		"∀P:complex_ops(A, B). ∀n:num. homology(P, n) = left_cosets(P.add, cycles(P, n), boundaries(P, n))",
	},
	Deps: []registry.EntryLike{ComplexAddDef, CyclesDef, BoundariesDef},
})}

// HomologyModuleDef — the cycles modulo the boundaries, as a module record.
var HomologyModuleDef = homologyModuleDefThm{family.Define(registry.DefEntry{
	Name: "HomologyModuleDef", Const: "homology_module",
	Key:  "prop_ac248659ac460406",
	Type: "complex_ops(A, B) → num → module_ops(A, set(B))",
	Equations: []string{
		"∀P:complex_ops(A, B). ∀n:num. " +
			"    homology_module(P, n) = " +
			"    quotient_module(restrict_module(complex_module(P, n), cycles(P, n)), boundaries(P, n))",
	},
	Deps: []registry.EntryLike{ComplexModuleDef, CyclesDef, BoundariesDef},
})}

// CyclesKernel — above degree 0 the cycles are the kernel of the
// boundary map, the form in which exactness is read: n + 1 is not 0, so
// the degree-0 disjunct of the cycles' comprehension drops and what is
// left is the kernel's.
var CyclesKernel = cyclesKernelThm{family.Add(registry.ProofEntry{
	Name: "CyclesKernel",
	Key:  "prop_a44f1642bfb8cd8e",
	Build: family.Theorem("∀P:complex_ops(A, B). ∀n:num. "+
		"    cycles(P, n + 1) = group_kernel(P.zero, P.terms(n + 1), P.d(n + 1))",
		func(a *Argument, P *Expr[ComplexOps[A, B]], n *Expr[Nat]) {
			a.Do(Unfold(CyclesDef), Unfold(group_homomorphism.GroupKernelDef))
			positive := a.Have(
				"a successor is not 0",
				"n + 1 ≠ 0",
				ByArith())
			a.Show(
				"so the degree-0 disjunct drops, and the two comprehensions agree",
				BySets(positive))
		}),
})}

// CyclesZero — at degree 0 the cycles are the whole term: the boundary
// out of degree 0 is not read, so the degree-0 disjunct of the cycles'
// comprehension holds and membership in P.terms(0) is all it asks.
var CyclesZero = cyclesZeroThm{family.Add(registry.ProofEntry{
	Name: "CyclesZero",
	Key:  "prop_ec1f2d0bbef09a91",
	Build: family.Theorem("∀P:complex_ops(A, B). cycles(P, 0) = P.terms(0)",
		func(a *Argument, P *Expr[ComplexOps[A, B]]) {
			a.Show(
				"a degree-0 cycle need only lie in P.terms(0)",
				Unfold(CyclesDef),
				BySets())
		}),
})}

// CyclesSubmodule — the cycles of every degree are a submodule of the
// degree's module: at degree 0 they are all of P.terms(0), and a module is
// a submodule of itself; at a degree m + 1 they are the kernel of the
// boundary map P.d(m + 1), a homomorphism of the degree modules, and a
// kernel is a submodule of its source.
var CyclesSubmodule = cyclesSubmoduleThm{family.Add(registry.ProofEntry{
	Name: "CyclesSubmodule",
	Key:  "prop_7acfc573e0cb2a26",
	Build: ChainComplex.Law("∀n:num. submodule(R, complex_module(P, n), cycles(P, n))",
		func(a *Argument, complexP ChainComplexFact[on.R], n *Expr[Nat]) {
			a.Cases(a.Term("n = 0"))
			a.When(
				"at degree 0 the cycles are the whole module P.terms(0)",
				func(b *Argument, isZero Fact) {
					b.Do(isZero.Rw(), Simp(Fwd(CyclesZero)))
					moduleAtZero := b.Have(
						"P.terms(0) is a module",
						"module_on(R, complex_module(P, 0))",
						By(ComplexModules.Read(complexP).At(b.TermAs[Nat]("0"))))
					b.Show(
						"and a module is a submodule of itself",
						By(submodule.CarrierSubmodule.Read(moduleAtZero)))
				})
			a.Otherwise(
				"above degree 0 the cycles are the kernel of the boundary map",
				func(b *Argument, positive Fact) {
					m, isSuc := b.ObtainAs[Nat](
						"a positive degree is a successor",
						"∃m:num. n = m + 1",
						By(positive, nat_arith.NonzeroIsSucc.At(n)))
					b.Do(isSuc.Rw())
					hom := b.Have(
						"the boundary out of m + 1 is a homomorphism of the degree modules",
						"module_homomorphism(R, complex_module(P, m + 1), complex_module(P, m), P.d(m + 1))",
						By(ComplexBoundaryHom.Read(complexP).At(m)))
					P := b.TermAs[ComplexOps[A, B]]("P")
					b.Show(
						"so its kernel, the cycles of degree m + 1, is a submodule of P.terms(m + 1)",
						By(module_homomorphism.KernelSubmodule.Read(hom), CyclesKernel.At(P, m)))
				})
		}),
})}

// BoundariesSubmodule — the boundaries are a submodule of P.terms(n): the
// image of P.d(n+1).
var BoundariesSubmodule = boundariesSubmoduleThm{family.Add(registry.ProofEntry{
	Name: "BoundariesSubmodule",
	Key:  "prop_9d4297ebb115642d",
	Build: ChainComplex.Law("∀n:num. submodule(R, complex_module(P, n), boundaries(P, n))",
		func(a *Argument, complexP ChainComplexFact[on.R], n *Expr[Nat]) {
			a.Do(Unfold(BoundariesDef))
			hom := a.Have(
				"the boundary out of n + 1 is a homomorphism of the degree modules",
				"module_homomorphism(R, complex_module(P, n + 1), complex_module(P, n), P.d(n + 1))",
				By(ComplexBoundaryHom.Read(complexP).At(n)))
			a.Show(
				"so its image is a submodule of its target module",
				By(module_homomorphism.ImageSubmodule.Read(hom)))
		}),
})}

// CyclesSubsetTerms — the cycles of degree n lie in the degree-n term:
// a cycle is by definition a member of P.terms(n), one the boundary out
// of degree n kills when n is positive.
var CyclesSubsetTerms = cyclesSubsetTermsThm{family.Add(registry.ProofEntry{
	Name: "CyclesSubsetTerms",
	Key:  "prop_40131e11c9e5c66f",
	Build: family.Theorem("∀P:complex_ops(A, B). ∀n:num. cycles(P, n) ⊆ P.terms(n)",
		func(a *Argument, P *Expr[ComplexOps[A, B]], n *Expr[Nat]) {
			a.Show(
				"a cycle is by definition a member of P.terms(n)",
				Unfold(CyclesDef),
				BySets())
		}),
})}

// BoundariesSubsetCycles — every boundary is a cycle: a member of the
// image of P.d(n + 1) lies in P.terms(n), the boundary map carrying P.terms(n + 1)
// there; at degree 0 that is all a cycle asks, and at a degree m + 1
// P.d(m + 1) kills it, two boundaries in a row being zero.
var BoundariesSubsetCycles = boundariesSubsetCyclesThm{family.Add(registry.ProofEntry{
	Name: "BoundariesSubsetCycles",
	Key:  "prop_4a18ceb82779849",
	Build: ChainComplex.Law("∀n:num. boundaries(P, n) ⊆ cycles(P, n)",
		func(a *Argument, complexP ChainComplexFact[on.R], n *Expr[Nat]) {
			modules, boundaryMaps := ComplexModules.Read(complexP), ComplexBoundaryHom.Read(complexP)
			a.Do(Unfold(set_basic.SubsetDef), Unfold(BoundariesDef))
			a.Cases(a.Term("n = 0"))
			a.When(
				"at degree 0 every member of P.terms(0) is a cycle",
				func(b *Argument, isZero Fact) {
					b.Do(isZero.Rw(), Simp(Fwd(CyclesZero)))
					b.Fix("u")
					boundary := b.Assume()
					b.Show(
						"u lies in P.terms(0), P.d(0 + 1) carrying P.terms(0 + 1) there",
						ByChase(Depth(0), modules, boundaryMaps, boundary))
				})
			a.Otherwise(
				"above degree 0 P.d(n) kills every boundary too",
				func(b *Argument, positive Fact) {
					_, isSuc := b.ObtainAs[Nat](
						"a positive degree is a successor",
						"∃m:num. n = m + 1",
						By(positive, nat_arith.NonzeroIsSucc.At(n)))
					b.Do(isSuc.Rw(), Unfold(CyclesDef))
					b.Fix("u")
					boundary := b.Assume()
					cycle := b.Have(
						"u lies in P.terms(m + 1) and P.d(m + 1) kills it, two boundaries in a row being zero",
						"u ∈ P.terms(m + 1) ∧ P.d(m + 1)(u) = P.zero",
						ByChase(Depth(0), modules, boundaryMaps, ComplexBoundaryTwice.Read(complexP), boundary))
					b.Show(
						"so u is a cycle",
						BySets(cycle))
				})
		}),
})}

// InHomology — a homology class is the coset of a cycle by the
// boundaries, and the coset of every cycle is a class: the cycles are a
// submodule of P.terms(n), so a module and a group under P.add, and the
// boundaries lie in them, so the cosets of the boundaries by the cycles
// are read off as the quotient group chapter reads them.
var InHomology = inHomologyThm{family.Add(registry.ProofEntry{
	Name: "InHomology",
	Key:  "prop_8885026063bc0117",
	Build: ChainComplex.Law("∀n:num. ∀s:set(B). "+
		"    s ∈ homology(P, n) ⇔ ∃u:B. s = left_coset(P.add, u, boundaries(P, n)) ∧ u ∈ cycles(P, n)",
		func(a *Argument, complexP ChainComplexFact[on.R], n *Expr[Nat], s *Expr[Set[B]]) {
			moduleAtN := a.Have(
				"P.terms(n) is a module",
				"module_on(R, complex_module(P, n))",
				By(ComplexModules.Read(complexP)))
			cyclesModule := a.Have(
				"the cycles, a submodule of it, are a module",
				"module_on(R, restrict_module(complex_module(P, n), cycles(P, n)))",
				By(submodule.SubmoduleModuleOn.Read(moduleAtN), CyclesSubmodule.Read(complexP)))
			cyclesGroup := a.Simplified(
				module.AddGroupOn.Read(cyclesModule),
				Fwd(module_record.ModuleAdditiveGroupDef),
				Fwd(module_record.RestrictModuleDef),
				Fwd(ComplexModuleDef),
				Fwd(module_record.ModAddDef),
				Fwd(module_record.ModZeroDef),
				Fwd(module_record.ModNegDef),
				Fwd(module_record.ModCarrierDef))
			a.Show(
				"the boundaries lie in the cycles, so a class, a "+
					"coset of them by a cycle, is the coset of some cycle",
				Unfold(HomologyDef),
				By(quotient_group.InLeftCosets.Read(cyclesGroup), BoundariesSubsetCycles.Read(complexP)))
		}),
})}

// CycleCorrection — a cycle corrected by a boundary is still a cycle,
// and it is a boundary only if the cycle is one: the boundary of z is
// a cycle, the cycles are a module, and u is the corrected cycle plus
// the boundary of z.
var CycleCorrection = cycleCorrectionThm{family.Add(registry.ProofEntry{
	Name: "CycleCorrection",
	Key:  "prop_7baba34ede7fa36b",
	Build: ChainComplex.Law(Statement{
		Binders: "∀n:num. ∀u z:B.",
		Hypotheses: []string{
			"u ∈ cycles(P, n)",
			"z ∈ P.terms(n + 1)",
		},
		Conclusion: "P.add(u, P.neg(P.d(n + 1)(z))) ∈ cycles(P, n) ∧ " +
			"(P.add(u, P.neg(P.d(n + 1)(z))) ∈ boundaries(P, n) ⇒ u ∈ boundaries(P, n))",
	},
		func(a *Argument, complexP Fact, n *Expr[Nat], u, z *Expr[B], given Fact) {
			parts := a.Conjuncts(
				given,
				"u is a cycle of P",
				"z lies in P.terms(n + 1)")
			cycle, zIn := parts[0], parts[1]
			modules, boundaryMaps := ComplexModules.Read(complexP), ComplexBoundaryHom.Read(complexP)
			boundary := a.Have(
				"the boundary of z is a boundary",
				"P.d(n + 1)(z) ∈ boundaries(P, n)",
				Unfold(BoundariesDef),
				ByChase(Depth(0), modules, boundaryMaps, zIn))
			boundaryCycle := a.Have(
				"so it is a cycle",
				"P.d(n + 1)(z) ∈ cycles(P, n)",
				BySets(boundary, BoundariesSubsetCycles.Read(complexP).At(n)))
			moduleAtN := a.Have(
				"P.terms(n) is a module",
				"module_on(R, complex_module(P, n))",
				By(modules))
			cyclesModule := a.Have(
				"the cycles are a module",
				"module_on(R, restrict_module(complex_module(P, n), cycles(P, n)))",
				By(submodule.SubmoduleModuleOn.Read(moduleAtN), CyclesSubmodule.Read(complexP)))
			corrected := a.Have(
				"u minus the boundary of z is a cycle",
				"P.add(u, P.neg(P.d(n + 1)(z))) ∈ cycles(P, n)",
				ByChase(Depth(0), cyclesModule, cycle, boundaryCycle))
			P := a.TermAs[ComplexOps[A, B]]("P")
			uIn := a.Have(
				"u lies in P.terms(n)",
				"u ∈ P.terms(n)",
				BySets(cycle, CyclesSubsetTerms.At(P, n)))
			reflected := a.Have(
				"if the corrected cycle is a boundary, so is u",
				"P.add(u, P.neg(P.d(n + 1)(z))) ∈ boundaries(P, n) ⇒ u ∈ boundaries(P, n)",
				Derive(func(b *Argument) {
					correctedBoundary := b.Unfolded(b.Assume(), BoundariesDef)
					b.Show(
						"u is the corrected cycle plus the boundary of z",
						Simp(Fwd(BoundariesDef)),
						ByChase(Depth(1), modules, boundaryMaps, uIn, zIn, correctedBoundary))
				}))
			a.Show(
				"both halves hold",
				By(corrected, reflected))
		}),
})}

// HomologyModuleOn — homology is a module: the cycles, a submodule of
// P.terms(n), are a module; the boundaries, a submodule of P.terms(n)
// lying in the cycles, are a submodule of that module; and the quotient
// of a module by a submodule is a module.
var HomologyModuleOn = homologyModuleOnThm{family.Add(registry.ProofEntry{
	Name: "HomologyModuleOn",
	Key:  "prop_1c8271f565b70d18",
	Build: ChainComplex.Law("∀n:num. module_on(R, homology_module(P, n))",
		func(a *Argument, complexP ChainComplexFact[on.R], n *Expr[Nat]) {
			moduleAtN := a.Have(
				"P.terms(n) is a module",
				"module_on(R, complex_module(P, n))",
				By(ComplexModules.Read(complexP)))
			cyclesModule := a.Have(
				"the cycles, a submodule of it, are a module",
				"module_on(R, restrict_module(complex_module(P, n), cycles(P, n)))",
				By(submodule.SubmoduleModuleOn.Read(moduleAtN), CyclesSubmodule.Read(complexP)))
			boundariesInCycles := a.Have(
				"the boundaries, a submodule of P.terms(n) lying in the cycles, are a submodule of the cycles",
				"submodule(R, restrict_module(complex_module(P, n), cycles(P, n)), boundaries(P, n))",
				By(
					BoundariesSubmodule.Read(complexP),
					BoundariesSubsetCycles.Read(complexP),
					submodule.SubmoduleRestrict))
			a.Show(
				"so the homology, the quotient of the cycles by the boundaries, is a module",
				Unfold(HomologyModuleDef),
				By(submodule.QuotientModuleOn.Read(cyclesModule), boundariesInCycles))
		}),
})}

// HomologyTrivialIffExact — homology at n is one point exactly when
// every cycle is a boundary.
var HomologyTrivialIffExact = homologyTrivialIffExactThm{family.Add(registry.ProofEntry{
	Name: "HomologyTrivialIffExact",
	Key:  "prop_332600113fc8990e",
	Deps: []registry.EntryLike{
		HomologyModuleDef,
		HomologyDef,
		ComplexModules,
		CyclesSubmodule,
		BoundariesSubmodule,
		BoundariesSubsetCycles,
		submodule.SubmoduleModuleOn,
		submodule.SubmoduleRestrict,
		submodule.SubmoduleSubgroup,
		module.AddGroupOn,
		quotient_group.QuotientTrivialIff,
	},
	Build: family.Card(
		ChainComplex.Statement(
			"∀n:num. (homology(P, n) = {boundaries(P, n)} ⇔ cycles(P, n) = boundaries(P, n))"),
		"quotient_group.QuotientTrivialIff in the additive group on the cycles "+
			"(SubmoduleModuleOn, AddGroupOn), the boundaries a subgroup of it (SubmoduleRestrict)"),
})}

// ---------------------------------------------------------------------------
// Chain maps and the map on homology
// ---------------------------------------------------------------------------

// ChainMapDef — `chain_map(P, Q, f)`, the complex records: f(n):
// P.terms(n) → Q.terms(n) are homomorphisms commuting with the boundaries.
var ChainMapDef = chainMapDefThm{family.Define(registry.DefEntry{
	Name:     "ChainMapDef",
	Const:    "chain_map",
	Type:     "ring_ops(A) → complex_ops(A, B) → complex_ops(A, C) → (num → B → C) → bool",
	Key:      "prop_881ef2e4efa0652d",
	Implicit: []string{"R"},
	Equations: []string{
		"∀R:ring_ops(A). ∀P:complex_ops(A, B). ∀Q:complex_ops(A, C). ∀f:(num → B → C). " +
			"    chain_map(R, P, Q, f) ⇔ " +
			"    (∀n:num. module_homomorphism(R, complex_module(P, n), complex_module(Q, n), f(n))) ∧ " +
			"    (∀n:num. ∀u:B. u ∈ P.terms(n + 1) ⇒ f(n)(P.d(n + 1)(u)) = Q.d(n + 1)(f(n + 1)(u)))",
	},
	Deps: []registry.EntryLike{ComplexModuleDef, ComplexDifferentialDef},
})}

// ChainMapHom — every component is a module homomorphism.
var ChainMapHom = chainMapHomThm{family.Add(registry.ProofEntry{
	Name: "ChainMapHom",
	Key:  "prop_4e88dc4e400add4b",
	Build: ChainMapDef.Entry().Conjunct(
		"∀n:num. module_homomorphism(R, complex_module(P, n), complex_module(Q, n), f(n))"),
})}

// ChainMapSquare — each differential square commutes on its source.
var ChainMapSquare = chainMapSquareThm{family.Add(registry.ProofEntry{
	Name: "ChainMapSquare",
	Key:  "prop_9f853f063d26ad6a",
	Build: ChainMapDef.Entry().Conjunct(Statement{
		Binders: "∀n:num. ∀u:B.",
		Hypotheses: []string{
			"u ∈ P.terms(n + 1)",
		},
		Conclusion: "f(n)(P.d(n + 1)(u)) = Q.d(n + 1)(f(n + 1)(u))",
	}),
})}

// ChainMapIdentity — the identity of a chain complex is a chain map: each
// component is the identity of a module, and both sides of each square
// are the boundary.
var ChainMapIdentity = chainMapIdentityThm{family.Add(registry.ProofEntry{
	Name: "ChainMapIdentity",
	Key:  "prop_a7720994e3322c3d",
	Build: ChainComplex.Law("chain_map(R, P, P, (λn:num. λx:B. x))",
		func(a *Argument, complexP ChainComplexFact[on.R]) {
			a.Show(
				"each component is the identity of a module, and each square reads P.d(n + 1)(u) on both sides",
				Unfold(ChainMapDef),
				Unfold(module_homomorphism.ModuleHomomorphismDef),
				By(ComplexModules.Read(complexP)))
		}),
})}

// ChainMapCompose — chain maps compose: each component of the composite
// is linear, and its square is f's square followed by g's.
var ChainMapCompose = chainMapComposeThm{family.Add(registry.ProofEntry{
	Name: "ChainMapCompose",
	Key:  "prop_daf5a01bd119adbc",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀P:complex_ops(A, B). " +
			"∀Q:complex_ops(A, C). " +
			"∀W:complex_ops(A, D). " +
			"∀f:(num → B → C). " +
			"∀g:(num → C → D).",
		Hypotheses: []string{
			"chain_map(R, P, Q, f)",
			"chain_map(R, Q, W, g)",
		},
		Conclusion: "chain_map(R, P, W, λn:num. λx:B. g(n)(f(n)(x)))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			P *Expr[ComplexOps[A, B]],
			Q *Expr[ComplexOps[A, C]],
			W *Expr[ComplexOps[A, D]],
			f *Arrow2[Nat, B, C],
			g *Arrow2[Nat, C, D],
			maps Fact,
		) {
			given := a.Conjuncts(
				maps,
				"f is a chain map",
				"g is a chain map")
			chainF, chainG := given[0], given[1]
			linear := a.Have(
				"each component of the composite is linear",
				"∀n:num. module_homomorphism(R, complex_module(P, n), complex_module(W, n), λx:B. g(n)(f(n)(x)))",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					composite := b.Have(
						"g(n) ∘ f(n) is linear",
						"module_homomorphism(R, complex_module(P, n), complex_module(W, n), g(n) ∘ f(n))",
						By(module_homomorphism.HomCompose, ChainMapHom.Read(chainF).At(n), ChainMapHom.Read(chainG).At(n)))
					b.Show(
						"g(n) ∘ f(n) is λx. g(n)(f(n)(x)) read pointwise",
						composite.Simp(Fwd(functions.ComposeApply)),
						By(composite))
				}))
			squares := a.Have(
				"the composite commutes with the boundaries",
				"∀n:num. ∀u:B. u ∈ P.terms(n + 1) ⇒ g(n)(f(n)(P.d(n + 1)(u))) = W.d(n + 1)(g(n + 1)(f(n + 1)(u)))",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					u := b.FixAs[B]("u")
					inP := b.Assume()
					next := b.TermAs[Nat]("n + 1")
					linearNext := b.Have(
						"f(n + 1) is linear",
						"module_homomorphism(R, complex_module(P, n + 1), complex_module(Q, n + 1), f(n + 1))",
						By(ChainMapHom.Read(chainF).At(next)))
					b.Show(
						"f's square at u, then g's at f(n + 1)(u), which lies in Q.terms(n + 1)",
						By(
							ChainMapSquare.Read(chainF).At(n, u),
							ChainMapSquare.Read(chainG).At(n, b.TermAs[C]("f(n + 1)(u)")),
							module_homomorphism.HomIn.Read(linearNext).At(proof.MemberOf(u, inP))))
				}))
			a.Show(
				"both clauses of a chain map",
				By(ChainMapDef, linear, squares))
		}),
})}

// HomologyMapDef — `homology_map(Q, f, n, s)`, the target complex Q a
// record: the image of a homology class under a chain map, the images
// of its members plus the target's boundaries — no representative
// chosen.
var HomologyMapDef = homologyMapDefThm{family.Define(registry.DefEntry{
	Name:  "HomologyMapDef",
	Const: "homology_map",
	Type:  "complex_ops(A, C) → (num → B → C) → num → set(B) → set(C)",
	Key:   "prop_3afef340ea083dc8",

	Equations: []string{
		"∀Q:complex_ops(A, C). ∀f:(num → B → C). ∀n:num. ∀s:set(B). " +
			"    homology_map(Q, f, n, s) = set_mul(Q.add, image(f(n), s), boundaries(Q, n))",
	},
	Deps: []registry.EntryLike{ComplexAddDef, BoundariesDef},
})}

// ChainMapCycles — a chain map carries cycles to cycles and boundaries
// to boundaries, each step one chase through the square
// f(m) ∘ P.d(m + 1) = Q.d(m + 1) ∘ f(m + 1), Q.d the boundary of Q. A cycle
// u of P.terms(n) goes into Q.terms(n), which is all a cycle asks at degree 0; at a
// degree m + 1, Q.d(m + 1)(f(m + 1)(u)) = f(m)(P.d(m + 1)(u)) = f(m)(P.zero),
// the zero of Q.terms(m). A boundary P.d(n + 1)(v) goes to
// f(n)(P.d(n + 1)(v)) = Q.d(n + 1)(f(n + 1)(v)), a boundary of Q.
var ChainMapCycles = chainMapCyclesThm{family.Add(registry.ProofEntry{
	Name: "ChainMapCycles",
	Key:  "prop_b30a0d560eed270",
	Build: ChainComplex.Law(Statement{
		Binders: "∀Q:complex_ops(A, C). ∀f:(num → B → C). ∀n:num.",
		Hypotheses: []string{
			"chain_complex(R, Q)",
			"chain_map(P, Q, f)",
		},
		Conclusion: "(∀u:B. u ∈ cycles(P, n) ⇒ f(n)(u) ∈ cycles(Q, n)) ∧ " +
			"(∀u:B. u ∈ boundaries(P, n) ⇒ f(n)(u) ∈ boundaries(Q, n))",
	},
		func(
			a *Argument,
			complexP Fact,
			complexQ ChainComplexFact[on.R],
			_ *Arrow2[Nat, B, C],
			n *Expr[Nat],
			chainMap Fact,
		) {
			clauses := []Fact{Read(ChainMapHom, chainMap), Read(ChainMapSquare, chainMap)}
			homs, square := clauses[0], clauses[1]
			modulesP, modulesQ := ComplexModules.Read(complexP), ComplexModules.Read(complexQ)
			a.Do(SplitConj(
				Case(
					"a cycle goes to a cycle",
					Derive(func(b *Argument) {
						b.FixAs[B]("u")
						cycle := b.Assume()
						opened := b.Conjuncts(
							b.Have(
								"u lies in P.terms(n), and P.d(n) kills it unless n = 0",
								"u ∈ P.terms(n) ∧ (n = 0 ∨ P.d(n)(u) = P.zero)",
								BySets(b.Unfolded(cycle, CyclesDef))),
							"u lies in P.terms(n)",
							"n = 0 or P.d(n) kills u")
						inP, killedUnlessZero := opened[0], opened[1]
						inQ := b.Have(
							"f(n) carries P.terms(n) into Q.terms(n)",
							"f(n)(u) ∈ Q.terms(n)",
							ByChase(Depth(0), modulesP, modulesQ, homs, inP))
						positive := b.Unless(
							b.Term("n = 0"),
							"at degree 0 every member of Q.terms(0) is a cycle",
							Given(func(c *Argument, isZero Fact) {
								whole := c.Have(
									"n being 0, the cycles of Q there are all of Q.terms(n)",
									"cycles(Q, n) = Q.terms(n)",
									isZero.Rw(),
									Cite(CyclesZero))
								c.Show(
									"and f(n)(u) lies in Q.terms(n)",
									whole.Rw(),
									By(inQ))
							}))
						_, isSuc := b.ObtainAs[Nat](
							"a positive degree is a successor",
							"∃m:num. n = m + 1",
							By(positive, nat_arith.NonzeroIsSucc.At(n)))
						lifted := b.Have(
							"so u is a cycle at degree m + 1",
							"u ∈ P.terms(m + 1) ∧ P.d(m + 1)(u) = P.zero",
							By(Normalized, inP, killedUnlessZero, positive, isSuc))
						imageKilled := b.Have(
							"Q.d(m + 1)(f(m + 1)(u)) = f(m)(P.d(m + 1)(u)) = f(m)(P.zero) = Q.zero",
							"Q.d(m + 1)(f(m + 1)(u)) = Q.zero",
							ByChase(Depth(0), modulesP, modulesQ, ComplexBoundaryHom.Read(complexP), homs, square, lifted))
						atN := b.Have(
							"which is Q.d(n) killing f(n)(u), n being m + 1",
							"Q.d(n)(f(n)(u)) = Q.zero",
							By(Normalized, imageKilled, isSuc))
						b.Show(
							"so f(n)(u) is a cycle of Q",
							Unfold(CyclesDef),
							BySets(inQ, atN))
					})),
				Case(
					"a boundary goes to a boundary",
					Unfold(BoundariesDef),
					Derive(func(b *Argument) {
						b.FixAs[B]("u")
						boundary := b.Assume()
						b.Show(
							"f(n)(u) is Q.d(n + 1) at f(n + 1) of a preimage of u under P.d(n + 1)",
							ByChase(
								Depth(0),
								modulesP,
								modulesQ,
								ComplexBoundaryHom.Read(complexP),
								ComplexBoundaryHom.Read(complexQ),
								homs,
								square,
								boundary))
					})),
			))
		}),
})}

// HomologyMapCoset — the map on homology carries the class of a cycle
// u to the class of f(n)(u). With N and N' the boundaries of P and Q at
// n, the image f(n)(u + N) + N' of the class u + N is f(n)(u) + N': the
// boundaries of Q absorb f(n) of P's, by the square.
var HomologyMapCoset = homologyMapCosetThm{family.Add(registry.ProofEntry{
	Name: "HomologyMapCoset",
	Key:  "prop_699695984d38435",
	Build: ChainComplex.Law(Statement{
		Binders: "∀Q:complex_ops(A, C). ∀f:(num → B → C). ∀n:num. ∀u:B.",
		Hypotheses: []string{
			"chain_complex(R, Q)",
			"chain_map(P, Q, f)",
			"u ∈ cycles(P, n)",
		},
		Conclusion: "homology_map(Q, f, n, left_coset(P.add, u, boundaries(P, n))) = " +
			"left_coset(Q.add, f(n)(u), boundaries(Q, n))",
	},
		func(
			a *Argument,
			complexP Fact,
			complexQ ChainComplexFact[on.R],
			f *Arrow2[Nat, B, C],
			n *Expr[Nat],
			u *Expr[B],
			hyps Fact,
		) {
			given := a.Conjuncts(
				hyps,
				"f is a chain map",
				"u is a cycle of P")
			hom := a.Have(
				"f(n) is a module homomorphism",
				"module_homomorphism(R, complex_module(P, n), complex_module(Q, n), f(n))",
				By(Read(ChainMapHom, given[0]).At(n)))
			groupHom := a.Simplified(
				module_homomorphism.HomGroup.Read(hom),
				Fwd(module_record.ModuleAdditiveGroupDef),
				Fwd(ComplexModuleDef),
				Fwd(module_record.ModAddDef),
				Fwd(module_record.ModZeroDef),
				Fwd(module_record.ModNegDef),
				Fwd(module_record.ModCarrierDef))
			sourceBoundaries := a.Have(
				"the boundaries of P form a submodule",
				"submodule(R, complex_module(P, n), boundaries(P, n))",
				By(BoundariesSubmodule.Read(complexP).At(n)))
			sourceSubgroup := a.Simplified(
				submodule.SubmoduleSubgroup.Read(sourceBoundaries),
				Fwd(module_record.ModuleAdditiveGroupDef),
				Fwd(ComplexModuleDef),
				Fwd(module_record.ModAddDef),
				Fwd(module_record.ModZeroDef),
				Fwd(module_record.ModNegDef),
				Fwd(module_record.ModCarrierDef))
			targetBoundaries := a.Have(
				"the boundaries of Q form a submodule",
				"submodule(R, complex_module(Q, n), boundaries(Q, n))",
				By(BoundariesSubmodule.Read(complexQ).At(n)))
			targetSubgroup := a.Simplified(
				submodule.SubmoduleSubgroup.Read(targetBoundaries),
				Fwd(module_record.ModuleAdditiveGroupDef),
				Fwd(ComplexModuleDef),
				Fwd(module_record.ModAddDef),
				Fwd(module_record.ModZeroDef),
				Fwd(module_record.ModNegDef),
				Fwd(module_record.ModCarrierDef))
			P := a.TermAs[ComplexOps[A, B]]("P")
			uIn := a.Have(
				"u lies in P.terms(n)",
				"u ∈ P.terms(n)",
				BySets(given[1], CyclesSubsetTerms.At(P, n)))
			mapBoundaries := a.Have(
				"f(n) carries boundaries to boundaries",
				"∀b:B. b ∈ boundaries(P, n) ⇒ f(n)(b) ∈ boundaries(Q, n)",
				By(Read(ChainMapCycles, complexP, complexQ).At(f, n), given[0]))
			a.Show(
				"the image coset is the coset of f(n)(u)",
				Unfold(HomologyMapDef),
				By(
					quotient_group.ImageLeftCosetMul.Read(groupHom).At(
						a.TermAs[Set[B]]("boundaries(P, n)"), a.TermAs[Set[C]]("boundaries(Q, n)"), proof.MemberOf(u, uIn)),
					sourceSubgroup,
					targetSubgroup,
					mapBoundaries))
		}),
})}

// HomologyMapHom — the map a chain map induces on homology is a
// homomorphism of the homology modules. f(n) carries the cycles of P into
// those of Q, so it restricts to a homomorphism of the cycle modules; its
// graph, read as a relation between representatives, is total, closed
// under sums and scalar multiples, and computes the map on homology class
// by class (HomologyMapCoset), and such a relation induces a homomorphism
// of the quotients by the boundaries.
var HomologyMapHom = homologyMapHomThm{family.Add(registry.ProofEntry{
	Name: "HomologyMapHom",
	Key:  "prop_db342d6873db076a",
	Build: ChainComplex.Law(Statement{
		Binders: "∀Q:complex_ops(A, C). ∀f:(num → B → C). ∀n:num.",
		Hypotheses: []string{
			"chain_complex(R, Q)",
			"chain_map(P, Q, f)",
		},
		Conclusion: "module_homomorphism(R, " +
			"    homology_module(P, n), " +
			"    homology_module(Q, n), " +
			"    homology_map(Q, f, n))",
	},
		func(
			a *Argument,
			complexP ChainComplexFact[on.R],
			Q *Expr[ComplexOps[A, C]],
			f *Arrow2[Nat, B, C],
			n *Expr[Nat],
			complexQ ChainComplexFact[on.R],
			chainMap Fact,
		) {
			onCycles := a.Have(
				"f(n), carrying cycles to cycles, restricts to a homomorphism of the cycle modules",
				"module_homomorphism(R, "+
					"    restrict_module(complex_module(P, n), cycles(P, n)), "+
					"    restrict_module(complex_module(Q, n), cycles(Q, n)), "+
					"    f(n))",
				By(
					module_homomorphism.HomRestrict,
					ChainMapHom.Read(chainMap),
					CyclesSubmodule.Read(complexP),
					CyclesSubmodule.Read(complexQ),
					chainMap,
					Read(ChainMapCycles, complexP, complexQ).At(f, n)))
			sourceBoundaries := a.Have(
				"the boundaries of P are a submodule of its cycles",
				"submodule(R, restrict_module(complex_module(P, n), cycles(P, n)), boundaries(P, n))",
				By(
					BoundariesSubmodule.Read(complexP),
					BoundariesSubsetCycles.Read(complexP),
					submodule.SubmoduleRestrict))
			targetBoundaries := a.Have(
				"the boundaries of Q are a submodule of its cycles",
				"submodule(R, restrict_module(complex_module(Q, n), cycles(Q, n)), boundaries(Q, n))",
				By(
					BoundariesSubmodule.Read(complexQ),
					BoundariesSubsetCycles.Read(complexQ),
					submodule.SubmoduleRestrict))
			total := a.Have(
				"every cycle of P has its image among the cycles of Q",
				"∀u:B. u ∈ cycles(P, n) ⇒ ∃v:C. v ∈ cycles(Q, n) ∧ f(n)(u) = v",
				a.ForEach(func(u *Expr[B]) Action {
					return By(module_homomorphism.HomIn.Read(onCycles).AsFact().At(u))
				}))
			sums := a.Have(
				"the images of two cycles add to the image of their sum",
				Statement{
					Binders: "∀u v:B. ∀x y:C.",
					Hypotheses: []string{
						"u ∈ cycles(P, n)",
						"v ∈ cycles(P, n)",
						"x ∈ cycles(Q, n)",
						"y ∈ cycles(Q, n)",
						"f(n)(u) = x",
						"f(n)(v) = y",
					},
					Conclusion: "f(n)(P.add(u, v)) = Q.add(x, y)",
				},
				Derive(func(b *Argument) {
					u, v := b.FixAs[B]("u"), b.FixAs[B]("v")
					b.Show(
						"f(n) is additive on the cycles",
						By(Normalized, module_homomorphism.HomAdd.Read(onCycles).AsFact().At(u, v)))
				}))
			multiples := a.Have(
				"and the image of a multiple of a cycle is the multiple of its image",
				Statement{
					Binders: "∀c:A. ∀u:B. ∀v:C.",
					Hypotheses: []string{
						"c ∈ R.carrier",
						"u ∈ cycles(P, n)",
						"v ∈ cycles(Q, n)",
						"f(n)(u) = v",
					},
					Conclusion: "f(n)(P.smul(c, u)) = Q.smul(c, v)",
				},
				Derive(func(b *Argument) {
					c, u := b.FixAs[A]("c"), b.FixAs[B]("u")
					b.Show(
						"f(n) is linear on the cycles",
						By(Normalized, module_homomorphism.HomSmul.Read(onCycles).AsFact().At(c, u)))
				}))
			cosets := a.Have(
				"the map on homology sends the class of a cycle to the class of its image",
				Statement{
					Binders: "∀u:B. ∀v:C.",
					Hypotheses: []string{
						"u ∈ cycles(P, n)",
						"v ∈ cycles(Q, n)",
						"f(n)(u) = v",
					},
					Conclusion: "homology_map(Q, f, n, left_coset(P.add, u, boundaries(P, n))) = " +
						"left_coset(Q.add, v, boundaries(Q, n))",
				},
				a.ForEach(func(u *Expr[B]) Action {
					return By(Read(HomologyMapCoset, complexP, complexQ).At(f, n, u), chainMap)
				}))
			a.Show(
				"so the graph of f(n) on the cycles induces a homomorphism of their quotients by the boundaries",
				Unfold(HomologyModuleDef),
				By(
					module_homomorphism.HomSource.Read(onCycles),
					module_homomorphism.HomTarget.Read(onCycles),
					sourceBoundaries,
					targetBoundaries,
					total,
					sums,
					multiples,
					cosets,
					Where(
						module_homomorphism.QuotientRelationHom,
						"T",
						a.TermAs[Fun2[B, C, Bool]]("λu:B. λv:C. f(n)(u) = v"))))
		}),
})}

// HomologyIsomorphismCriterion — a chain map induces an isomorphism on
// homology in degree n when every cycle of Q there is the image of a
// cycle of P and a cycle of P whose image is a boundary is itself one:
// the first makes the map onto the classes, the second one-to-one.
var HomologyIsomorphismCriterion = homologyIsomorphismCriterionThm{family.Add(registry.ProofEntry{
	Name: "HomologyIsomorphismCriterion",
	Key:  "prop_c3984f25d0c2053e",
	Build: ChainComplex.Law(Statement{
		Binders: "∀Q:complex_ops(A, C). ∀f:(num → B → C). ∀n:num.",
		Hypotheses: []string{
			"chain_complex(R, Q)",
			"chain_map(P, Q, f)",
			"∀w:C. w ∈ cycles(Q, n) ⇒ ∃u:B. u ∈ cycles(P, n) ∧ f(n)(u) = w",
			"∀u:B. u ∈ cycles(P, n) ∧ f(n)(u) ∈ boundaries(Q, n) ⇒ u ∈ boundaries(P, n)",
		},
		Conclusion: "module_isomorphism(R, " +
			"    homology_module(P, n), " +
			"    homology_module(Q, n), " +
			"    homology_map(Q, f, n))",
	},
		func(
			a *Argument,
			complexP Fact,
			complexQ ChainComplexFact[on.R],
			f *Arrow2[Nat, B, C],
			n *Expr[Nat],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"f is a chain map",
				"every cycle of Q at n is f(n) of a cycle of P",
				"a cycle of P whose image is a boundary is a boundary")
			chainMap, lifts, reflects := parts[0], parts[1], parts[2]
			homs := ChainMapHom.Read(chainMap)
			P := a.TermAs[ComplexOps[A, B]]("P")
			hom := a.Have(
				"the map on homology is linear",
				"module_homomorphism(R, homology_module(P, n), homology_module(Q, n), homology_map(Q, f, n))",
				By(HomologyMapHom.Read(complexP), complexQ, chainMap))
			moduleAtN := a.Have(
				"P.terms(n) is a module",
				"module_on(R, complex_module(P, n))",
				By(ComplexModules.Read(complexP)))
			cyclesModule := a.Have(
				"the cycles of P are a module",
				"module_on(R, restrict_module(complex_module(P, n), cycles(P, n)))",
				By(submodule.SubmoduleModuleOn.Read(moduleAtN), CyclesSubmodule.Read(complexP)))
			imagesP := a.Have(
				"the boundaries of P at n are a submodule",
				"submodule(R, complex_module(P, n), image(P.d(n + 1), P.terms(n + 1)))",
				By(BoundariesSubmodule.Read(complexP), BoundariesDef))
			imagesQ := a.Have(
				"the boundaries of Q at n are a submodule",
				"submodule(R, complex_module(Q, n), image(Q.d(n + 1), Q.terms(n + 1)))",
				By(BoundariesSubmodule.Read(complexQ), BoundariesDef))

			injective := a.Have(
				"two classes with one image differ by the class of a "+
					"cycle whose image is a boundary, so f* is one-to-one",
				"injective_on(homology(P, n), homology_map(Q, f, n))",
				Unfold(functions.InjectiveOnDef),
				Derive(func(b *Argument) {
					b.FixAs[Set[B]]("s")
					b.FixAs[Set[B]]("t")
					pair := b.Conjuncts(
						b.Assume(),
						"s is a class of P",
						"t is a class of P",
						"f* sends s and t to one class")
					_, sIs := b.ObtainAs[B](
						"s is the class of a cycle u₁",
						"∃u₁:B. s = left_coset(P.add, u₁, boundaries(P, n)) ∧ u₁ ∈ cycles(P, n)",
						By(pair[0], InHomology.Read(complexP)))
					_, tIs := b.ObtainAs[B](
						"t is the class of a cycle u₂",
						"∃u₂:B. t = left_coset(P.add, u₂, boundaries(P, n)) ∧ u₂ ∈ cycles(P, n)",
						By(pair[1], InHomology.Read(complexP)))
					sClass := b.Conjuncts(
						sIs,
						"s is the class of u₁",
						"u₁ is a cycle of P")
					tClass := b.Conjuncts(
						tIs,
						"t is the class of u₂",
						"u₂ is a cycle of P")
					sImage := b.Have(
						"f* sends the class of u₁ to the class of f(n)(u₁)",
						"homology_map(Q, f, n, left_coset(P.add, u₁, boundaries(P, n))) = "+
							"left_coset(Q.add, f(n)(u₁), boundaries(Q, n))",
						By(HomologyMapCoset.Read(complexP), complexQ, chainMap, sClass[1]))
					tImage := b.Have(
						"f* sends the class of u₂ to the class of f(n)(u₂)",
						"homology_map(Q, f, n, left_coset(P.add, u₂, boundaries(P, n))) = "+
							"left_coset(Q.add, f(n)(u₂), boundaries(Q, n))",
						By(HomologyMapCoset.Read(complexP), complexQ, chainMap, tClass[1]))
					images := b.Have(
						"so f(n)(u₁) and f(n)(u₂) have one class",
						"left_coset(Q.add, f(n)(u₁), image(Q.d(n + 1), Q.terms(n + 1))) = "+
							"left_coset(Q.add, f(n)(u₂), image(Q.d(n + 1), Q.terms(n + 1)))",
						By(sClass[0], tClass[0], pair[2], sImage, tImage, BoundariesDef))
					members := b.Have(
						"u₁ and u₂ lie in P.terms(n)",
						"u₁ ∈ P.terms(n) ∧ u₂ ∈ P.terms(n)",
						BySets(sClass[1], tClass[1], CyclesSubsetTerms.At(P, n)))
					imageDifference := b.Have(
						"f(n) carries u₂ − u₁ into the boundaries of Q",
						"f(n)(P.add(P.neg(u₁), u₂)) ∈ image(Q.d(n + 1), Q.terms(n + 1))",
						ByChase(Depth(0), homs, ComplexBoundaryHom.Read(complexQ), members, imagesQ, images))
					cycleDifference := b.Have(
						"u₂ − u₁ is a cycle",
						"P.add(P.neg(u₁), u₂) ∈ cycles(P, n)",
						ByChase(Depth(0), cyclesModule, sClass[1], tClass[1]))
					boundaryDifference := b.Have(
						"so u₂ − u₁ is a boundary",
						"P.add(P.neg(u₁), u₂) ∈ boundaries(P, n)",
						By(
							reflects.At(b.TermAs[B]("P.add(P.neg(u₁), u₂)")),
							cycleDifference,
							imageDifference,
							BoundariesDef))
					imageOfDifference := b.Have(
						"that is, an image of P.d(n + 1)",
						"P.add(P.neg(u₁), u₂) ∈ image(P.d(n + 1), P.terms(n + 1))",
						By(boundaryDifference, BoundariesDef))
					classes := b.Have(
						"so u₁ and u₂ have one class",
						"left_coset(P.add, u₁, image(P.d(n + 1), P.terms(n + 1))) = "+
							"left_coset(P.add, u₂, image(P.d(n + 1), P.terms(n + 1)))",
						ByChase(Depth(0), ComplexBoundaryHom.Read(complexP), members, imagesP, imageOfDifference))
					b.Show(
						"s = t",
						By(sClass[0], tClass[0], classes, BoundariesDef))
				}))

			into := a.Have(
				"f* carries classes of P to classes of Q",
				"∀S:set(B). S ∈ homology(P, n) ⇒ homology_map(Q, f, n, S) ∈ homology(Q, n)",
				Unfold(HomologyDef),
				By(module_homomorphism.HomIn.Read(hom)))
			reach := a.Have(
				"every class of Q is f* of a class of P",
				"∀S:set(C). S ∈ homology(Q, n) ⇒ S ∈ image(homology_map(Q, f, n), homology(P, n))",
				Derive(func(b *Argument) {
					b.FixAs[Set[C]]("S")
					sIn := b.Assume()
					_, sIs := b.ObtainAs[C](
						"S is the class of a cycle w of Q",
						"∃w:C. S = left_coset(Q.add, w, boundaries(Q, n)) ∧ w ∈ cycles(Q, n)",
						By(sIn, InHomology.Read(complexQ)))
					sClass := b.Conjuncts(
						sIs,
						"S is the class of w",
						"w is a cycle of Q")
					u, uIs := b.ObtainAs[B](
						"w is f(n) of a cycle u of P",
						"∃u:B. u ∈ cycles(P, n) ∧ f(n)(u) = w",
						By(lifts, sClass[1]))
					lift := b.Conjuncts(
						uIs,
						"u is a cycle of P",
						"f(n)(u) = w")
					image := b.Have(
						"f* sends the class of u to the class of f(n)(u)",
						"homology_map(Q, f, n, left_coset(P.add, u, boundaries(P, n))) = "+
							"left_coset(Q.add, f(n)(u), boundaries(Q, n))",
						By(HomologyMapCoset.Read(complexP), complexQ, chainMap, lift[0]))
					class := b.Have(
						"the class of u is a class of P",
						"left_coset(P.add, u, boundaries(P, n)) ∈ homology(P, n)",
						Simp(Fwd(InHomology.Read(complexP))),
						Derive(func(c *Argument) {
							c.Take(u)
							c.Show(
								"the class of the cycle u",
								By(lift[0]))
						}))
					reached := b.Have(
						"S, the class of w = f(n)(u), is f* of the class of u",
						"S = homology_map(Q, f, n, left_coset(P.add, u, boundaries(P, n)))",
						By(sClass[0], lift[1], image))
					b.Do(Simp(Fwd(set_basic.InImage.Inst(TypeBinder.BindA[Set[B]](), TypeBinder.BindB[Set[C]]()))))
					b.Take(b.TermAs[Set[B]]("left_coset(P.add, u, boundaries(P, n))"))
					b.Show(
						"so S lies in the image of f*",
						By(reached, class))
				}))
			pointwise := a.Have(
				"a class of Q is in the image of f* exactly when it is a class",
				"∀S:set(C). S ∈ image(homology_map(Q, f, n), homology(P, n)) ⇔ S ∈ homology(Q, n)",
				Derive(func(b *Argument) {
					b.FixAs[Set[C]]("S")
					b.Iff()
					b.Forward(
						"f* of a class of P is a class of Q",
						func(c *Argument, sIn Fact) {
							x, xIs := c.ObtainAs[Set[B]](
								"S is f* of a class X of P",
								"∃X:set(B). S = homology_map(Q, f, n, X) ∧ X ∈ homology(P, n)",
								By(sIn, set_basic.InImage))
							c.Show(
								"so S is a class of Q",
								By(Normalized, into.At(x), xIs))
						})
					b.Backward(
						"every class of Q is reached",
						func(c *Argument, sIn Fact) {
							c.Show(
								"by the lift of its cycle",
								By(reach, sIn))
						})
				}))
			onto := a.Have(
				"so f* is onto",
				"image(homology_map(Q, f, n), homology(P, n)) = homology(Q, n)",
				By(pointwise, set_basic.Extension))
			// A homology module's carrier is the cosets of the boundaries by the cycles, which homology unfolds to.
			a.Show(
				"a bijective linear map of the homology modules is an isomorphism",
				By(
					module_homomorphism.ModuleIsomorphismDef,
					hom,
					a.Unfolded(injective, HomologyDef),
					a.Unfolded(onto, HomologyDef)))
		}),
})}

// HomologyMapIdentity — the identity chain map induces the identity on
// homology: a class is the class of a cycle u, and the identity, a chain
// map, sends it to the class of u.
var HomologyMapIdentity = homologyMapIdentityThm{family.Add(registry.ProofEntry{
	Name: "HomologyMapIdentity",
	Key:  "prop_ca43b504b5694ff6",
	Build: ChainComplex.Law(Statement{
		Binders: "∀n:num. ∀s:set(B).",
		Hypotheses: []string{
			"s ∈ homology(P, n)",
		},
		Conclusion: "homology_map(P, λm:num. λx:B. x, n, s) = s",
	},
		func(a *Argument, complexP ChainComplexFact[on.R], n *Expr[Nat], s *Expr[Set[B]], sIn Fact) {
			u, sIs := a.ObtainAs[B](
				"s is the class of a cycle u",
				"∃u:B. s = left_coset(P.add, u, boundaries(P, n)) ∧ u ∈ cycles(P, n)",
				By(sIn, InHomology.Read(complexP)))
			class := a.Conjuncts(
				sIs,
				"s is the class of u",
				"u is a cycle of P")
			P, identity := a.TermAs[ComplexOps[A, B]]("P"), a.TermAs[Fun2[Nat, B, B]]("λm:num. λx:B. x")
			// A λ-term in the map slot is not matched against the goal bare, so the cite is grounded at the identity.
			a.Show(
				"the identity, a chain map, sends the class of u to the class of u",
				class[0].Rw(),
				By(
					HomologyMapCoset.Read(complexP).At(P, identity, n, u),
					complexP,
					ChainMapIdentity.Read(complexP),
					class[1]))
		}),
})}

// HomologyMapCompose — on every homology class, the map on homology of
// a composite of chain maps is the map of the second after the map of
// the first: the composite is a chain map; a class is the class of a
// cycle u, f(n)(u) is a cycle of Q, and the composite's map and the map
// of f followed by the map of g both send the class of u to the class of
// g(n)(f(n)(u)).
var HomologyMapCompose = homologyMapComposeThm{family.Add(registry.ProofEntry{
	Name: "HomologyMapCompose",
	Key:  "prop_5552bb1703f19255",
	Build: ChainComplex.Law(Statement{
		Binders: "∀Q:complex_ops(A, C). " +
			"∀W:complex_ops(A, D). " +
			"∀f:(num → B → C). " +
			"∀g:(num → C → D). " +
			"∀n:num. " +
			"∀s:set(B).",
		Hypotheses: []string{
			"chain_complex(R, Q)",
			"chain_complex(R, W)",
			"chain_map(P, Q, f) ∧ chain_map(Q, W, g)",
			"s ∈ homology(P, n)",
		},
		Conclusion: "homology_map(W, λm:num. λx:B. g(m)(f(m)(x)), n, s) = " +
			"homology_map(W, g, n, homology_map(Q, f, n, s))",
	},
		func(
			a *Argument,
			complexP ChainComplexFact[on.R],
			Q *Expr[ComplexOps[A, C]],
			W *Expr[ComplexOps[A, D]],
			f *Arrow2[Nat, B, C],
			g *Arrow2[Nat, C, D],
			n *Expr[Nat],
			s *Expr[Set[B]],
			complexQ, complexW, chainMaps, sIn Fact,
		) {
			maps := a.Conjuncts(
				chainMaps,
				"f is a chain map",
				"g is a chain map")
			fChain, gChain := maps[0], maps[1]
			gf := a.TermAs[Fun2[Nat, B, D]]("λm:num. λx:B. g(m)(f(m)(x))")
			composite := a.Have(
				"the composite is a chain map",
				"chain_map(P, W, λm:num. λx:B. g(m)(f(m)(x)))",
				By(ChainMapCompose, fChain, gChain))

			u, sIs := a.ObtainAs[B](
				"s is the class of a cycle u",
				"∃u:B. s = left_coset(P.add, u, boundaries(P, n)) ∧ u ∈ cycles(P, n)",
				By(sIn, InHomology.Read(complexP)))
			class := a.Conjuncts(
				sIs,
				"s is the class of u",
				"u is a cycle of P")
			fCycle := a.Have(
				"f(n) carries the cycle u to a cycle of Q",
				"f(n)(u) ∈ cycles(Q, n)",
				By(Read(ChainMapCycles, complexP, complexQ).At(f, n), fChain, class[1]))
			// A λ-term in the map slot is not matched against the goal bare, so the cite is grounded at the composite.
			byComposite := a.Have(
				"the composite's map sends the class of u to the class of g(n)(f(n)(u))",
				"homology_map(W, λm:num. λx:B. g(m)(f(m)(x)), n, left_coset(P.add, u, boundaries(P, n))) = "+
					"left_coset(W.add, g(n)(f(n)(u)), boundaries(W, n))",
				By(HomologyMapCoset.Read(complexP).At(W, gf, n, u), complexW, composite, class[1]))
			byF := a.Have(
				"the map of f sends it to the class of f(n)(u)",
				"homology_map(Q, f, n, left_coset(P.add, u, boundaries(P, n))) = "+
					"left_coset(Q.add, f(n)(u), boundaries(Q, n))",
				By(HomologyMapCoset.Read(complexP), complexQ, fChain, class[1]))
			byG := a.Have(
				"and the map of g sends that to the class of g(n)(f(n)(u))",
				"homology_map(W, g, n, left_coset(Q.add, f(n)(u), boundaries(Q, n))) = "+
					"left_coset(W.add, g(n)(f(n)(u)), boundaries(W, n))",
				By(HomologyMapCoset.Read(complexQ), complexW, gChain, fCycle))
			a.Show(
				"so both sides are the class of g(n)(f(n)(u))",
				By(class[0], byComposite, byF, byG))
		}),
})}

// ---------------------------------------------------------------------------
// Chain homotopy
// ---------------------------------------------------------------------------

// ChainHomotopyDef — `chain_homotopy(P, Q, f, g, h)`, the complex
// records: h(n): P.terms(n) → Q.terms(n+1) with f − g = Q.d ∘ h + h ∘ P.d in every
// degree (and f − g = Q.d ∘ h at degree 0, where no boundary comes in).
var ChainHomotopyDef = chainHomotopyDefThm{family.Define(registry.DefEntry{
	Name:  "ChainHomotopyDef",
	Const: "chain_homotopy",
	Type: "ring_ops(A) → " +
		"complex_ops(A, B) → " +
		"complex_ops(A, C) → " +
		"(num → B → C) → " +
		"(num → B → C) → " +
		"(num → B → C) → " +
		"bool",
	Key:      "prop_ab03bd6f1d34f129",
	Implicit: []string{"R"},
	Equations: []string{
		"∀R:ring_ops(A). ∀P:complex_ops(A, B). ∀Q:complex_ops(A, C). ∀f g h:(num → B → C). " +
			"    chain_homotopy(R, P, Q, f, g, h) ⇔ " +
			"    (∀n:num. module_homomorphism(R, complex_module(P, n), complex_module(Q, n + 1), h(n))) ∧ " +
			"    (∀n:num. ∀u:B. " +
			"        u ∈ P.terms(n + 1) ⇒ " +
			"        Q.add(f(n + 1)(u), Q.neg(g(n + 1)(u))) = " +
			"        Q.add(Q.d(n + 2)(h(n + 1)(u)), h(n)(P.d(n + 1)(u)))) ∧ " +
			"    (∀u:B. u ∈ P.terms(0) ⇒ Q.add(f(0)(u), Q.neg(g(0)(u))) = Q.d(1)(h(0)(u)))",
	},
	Deps: []registry.EntryLike{ComplexModuleDef, ComplexDifferentialDef},
})}

// HomotopicSameHomologyMap — chain-homotopic chain maps induce the
// same map on homology. A class is u + B with u a cycle, and each map
// carries it to the class of its value at u, so what is to be shown is
// that f(n)(u) − g(n)(u) lies in the boundaries of Q, the image of
// Q.d(n + 1). At degree 0 the homotopy makes it Q.d(1)(h(0)(u)); at a
// degree m + 1 it makes it Q.d(m + 2)(h(m + 1)(u)) + h(m)(P.d(m + 1)(u)),
// and P.d(m + 1) kills the cycle u.
var HomotopicSameHomologyMap = homotopicSameHomologyMapThm{family.Add(registry.ProofEntry{
	Name: "HomotopicSameHomologyMap",
	Key:  "prop_a783b4d3a5af3e6f",
	Build: ChainComplex.Law(Statement{
		Binders: "∀Q:complex_ops(A, C). ∀f g h:(num → B → C). ∀n:num. ∀s:set(B).",
		Hypotheses: []string{
			"chain_complex(R, Q)",
			"chain_map(P, Q, f)",
			"chain_map(P, Q, g)",
			"chain_homotopy(P, Q, f, g, h)",
			"s ∈ homology(P, n)",
		},
		Conclusion: "homology_map(Q, f, n, s) = homology_map(Q, g, n, s)",
	},
		func(
			a *Argument,
			complexP, complexQ ChainComplexFact[on.R],
			_, _, _ *Arrow2[Nat, B, C],
			hyps Fact,
			n *Expr[Nat],
			_ *Expr[Set[B]],
			sIn Fact,
		) {
			given := a.Conjuncts(
				hyps,
				"f is a chain map",
				"g is a chain map",
				"h is a chain homotopy from f to g")
			fHoms := Read(ChainMapHom, given[0])
			gHoms := Read(ChainMapHom, given[1])
			homotopy := a.Conjuncts(
				a.Unfolded(given[2], ChainHomotopyDef),
				"each h(m) is a homomorphism from P.terms(m) to Q.terms(m + 1)",
				"f(m + 1) − g(m + 1) = Q.d(m + 2) ∘ h(m + 1) + h(m) ∘ P.d(m + 1) on P.terms(m + 1)",
				"f(0) − g(0) = Q.d(1) ∘ h(0) on P.terms(0)")
			hHoms, above, atZeroDegree := homotopy[0], homotopy[1], homotopy[2]
			modulesP, modulesQ := ComplexModules.Read(complexP), ComplexModules.Read(complexQ)
			boundaryHomsP, boundaryHomsQ := ComplexBoundaryHom.Read(complexP), ComplexBoundaryHom.Read(complexQ)

			_, sIs := a.Obtain(
				"s is the class of a cycle u",
				"∃u:B. s = left_coset(P.add, u, boundaries(P, n)) ∧ u ∈ cycles(P, n)",
				By(sIn, InHomology.Read(complexP)))
			class := a.Conjuncts(
				sIs,
				"s is the class of u",
				"u is a cycle of P")
			sEq, cycle := class[0], class[1]
			opened := a.Conjuncts(
				a.Have(
					"u lies in P.terms(n), and P.d(n) kills it unless n = 0",
					"u ∈ P.terms(n) ∧ (n = 0 ∨ P.d(n)(u) = P.zero)",
					BySets(a.Unfolded(cycle, CyclesDef))),
				"u lies in P.terms(n)",
				"n = 0 or P.d(n) kills u")
			inP, killedUnlessZero := opened[0], opened[1]
			// Each map carries the class of u to the class of its value at u, and the boundaries of Q are the image of Q.d(n + 1).
			a.Do(sEq.Rw(), Simp(Fwd(HomologyMapCoset.Read(complexP))), Unfold(BoundariesDef))
			a.Cases(a.Term("n = 0"))
			a.When(
				"at degree 0, f(n)(u) − g(n)(u) = Q.d(n + 1)(h(n)(u)) lies in the image of Q.d(n + 1)",
				func(b *Argument, isZero Fact) {
					atN := b.Have(
						"n being 0, the homotopy's degree-0 clause says f(n) − g(n) = Q.d(n + 1) ∘ h(n) on P.terms(n)",
						"∀u:B. u ∈ P.terms(n) ⇒ Q.add(f(n)(u), Q.neg(g(n)(u))) = Q.d(n + 1)(h(n)(u))",
						isZero.Rw(),
						Simp(Fwd(nat_arith.AddLeftZeroClause)),
						By(atZeroDegree))
					images := b.Unfolded(BoundariesSubmodule.Read(complexQ).At(n), BoundariesDef)
					b.Show(
						"so the classes agree: −f(n)(u) + g(n)(u) = Q.d(n + 1)(−h(n)(u))",
						ByChase(Depth(0), modulesP, modulesQ, boundaryHomsQ, fHoms, gHoms, hHoms, atN, inP, images))
				})
			a.Otherwise(
				"above degree 0, f(m + 1)(u) − g(m + 1)(u) = Q.d(m + 2)(h(m + 1)(u)), P.d(m + 1) killing u",
				func(b *Argument, positive Fact) {
					_, isSuc := b.ObtainAs[Nat](
						"a positive degree is a successor",
						"∃m:num. n = m + 1",
						By(positive, nat_arith.NonzeroIsSucc.At(n)))
					lifted := b.Have(
						"so u lies in P.terms(m + 1) and P.d(m + 1) kills it",
						"u ∈ P.terms(m + 1) ∧ P.d(m + 1)(u) = P.zero",
						By(Normalized, inP, killedUnlessZero, positive, isSuc))
					b.Do(isSuc.Rw())
					degree := b.TermAs[Nat]("m + 1")
					images := b.Unfolded(BoundariesSubmodule.Read(complexQ).At(degree), BoundariesDef)
					b.Show(
						"so the classes agree: −f(m + 1)(u) + g(m + 1)(u) = Q.d(m + 1 + 1)(−h(m + 1)(u))",
						ByChase(
							Depth(0),
							modulesP,
							modulesQ,
							boundaryHomsP,
							boundaryHomsQ,
							fHoms,
							gHoms,
							hHoms,
							above,
							lifted,
							images))
				})
		}),
})}

// ChainHomotopyCalculus — chain homotopies compose with chain maps on
// either side, reverse by negation and concatenate by addition, each
// with its witness written out.
var ChainHomotopyCalculus = chainHomotopyCalculusThm{family.Add(registry.ProofEntry{
	Name: "ChainHomotopyCalculus",
	Key:  "prop_362e80be69859b7",
	Reading: "The witnesses are explicit because a homotopy built from two others, " +
		"H ∘ a − i ∘ K, is assembled from these four rules. Postcomposing shifts the " +
		"map's degree: the homotopy h(n) lands in Q.terms(n + 1), so b(n + 1) follows it.",
	Deps: []registry.EntryLike{
		ChainHomotopyDef,
		ChainMapHom,
		ChainMapSquare,
		ComplexModules,
		ComplexBoundaryHom,
		module_homomorphism.HomCompose,
		module_homomorphism.HomAdd,
		module_homomorphism.HomNeg,
		module_homomorphism.HomDiff,
		module_homomorphism.HomZero,
		module.AddGroupOn,
		module.AddComm,
		module.SmulNeg,
	},
	Build: family.Card(ChainComplex.Statement(Statement{
		Binders: "∀Q:complex_ops(A, C).",
		Hypotheses: []string{
			"chain_complex(R, Q)",
		},
		Conclusion: "(∀P':complex_ops(A, D). " +
			"    chain_complex(R, P') ⇒ " +
			"    ∀a:(num → D → B). ∀f g h:(num → B → C). " +
			"        chain_map(R, P', P, a) ∧ " +
			"        chain_map(R, P, Q, f) ∧ " +
			"        chain_map(R, P, Q, g) ∧ " +
			"        chain_homotopy(R, P, Q, f, g, h) ⇒ " +
			"        chain_homotopy(R, " +
			"            P', " +
			"            Q, " +
			"            λn:num. λx:D. f(n)(a(n)(x)), " +
			"            λn:num. λx:D. g(n)(a(n)(x)), " +
			"            λn:num. λx:D. h(n)(a(n)(x)))) ∧ " +
			"(∀Q':complex_ops(A, E). " +
			"    chain_complex(R, Q') ⇒ " +
			"    ∀b:(num → C → E). ∀f g h:(num → B → C). " +
			"        chain_map(R, Q, Q', b) ∧ " +
			"        chain_map(R, P, Q, f) ∧ " +
			"        chain_map(R, P, Q, g) ∧ " +
			"        chain_homotopy(R, P, Q, f, g, h) ⇒ " +
			"        chain_homotopy(R, " +
			"            P, " +
			"            Q', " +
			"            λn:num. λx:B. b(n)(f(n)(x)), " +
			"            λn:num. λx:B. b(n)(g(n)(x)), " +
			"            λn:num. λx:B. b(n + 1)(h(n)(x)))) ∧ " +
			"(∀f g h:(num → B → C). " +
			"    chain_map(R, P, Q, f) ∧ chain_map(R, P, Q, g) ∧ chain_homotopy(R, P, Q, f, g, h) ⇒ " +
			"    chain_homotopy(R, P, Q, g, f, λn:num. λx:B. Q.neg(h(n)(x)))) ∧ " +
			"(∀f g k h h':(num → B → C). " +
			"    chain_map(R, P, Q, f) ∧ " +
			"    chain_map(R, P, Q, g) ∧ " +
			"    chain_map(R, P, Q, k) ∧ " +
			"    chain_homotopy(R, P, Q, f, g, h) ∧ " +
			"    chain_homotopy(R, P, Q, g, k, h') ⇒ " +
			"    chain_homotopy(R, P, Q, f, k, λn:num. λx:B. Q.add(h(n)(x), h'(n)(x))))",
	}),
		"precomposing, f a − g a = (Q.d h + h P.d) a with P.d a = a P'.d (ChainMapSquare for "+
			"a), a(n) carrying P'.terms(n) into P.terms(n) (ChainMapHom); postcomposing, b (f − g) "+
			"= b (Q.d h + h P.d) = Q'.d (b h) + (b h) P.d, b(n + 1) linear and commuting with the "+
			"boundaries (ChainMapHom, HomAdd, HomNeg, ChainMapSquare); negation, g − f = −(f − g) "+
			"= Q.d(−h) + (−h) P.d, Q.d linear (ComplexBoundaryHom, HomNeg); concatenation, f − k = "+
			"(f − g) + (g − k), the values of f, g, k in Q's terms (ChainMapHom) under its abelian "+
			"group laws (ComplexModules, AddGroupOn, AddComm), and Q.d additive. Each new homotopy "+
			"is linear: a composite (HomCompose), or a negative or a sum of homomorphisms, linear "+
			"by Q's group laws and SmulNeg as the difference is by HomDiff. The degree-0 clause "+
			"follows the same way, with Q.d(1) in place of Q.d(n + 2) and no boundary out of P"),
})}

// ---------------------------------------------------------------------------
// Short exact sequences of complexes and the long exact sequence
// ---------------------------------------------------------------------------

// ExactComplexesDef — `exact_complexes(P', P, the quotient complex, i, p)`, the three
// complex records: in every degree, i(n) is injective on P'.terms(n), the
// image of i(n) is the kernel of p(n), and p(n) maps P.terms(n) onto the quotient complex.terms(n).
var ExactComplexesDef = exactComplexesDefThm{family.Define(registry.DefEntry{
	Name:  "ExactComplexesDef",
	Const: "exact_complexes",
	Type: "complex_ops(A, B) → " +
		"complex_ops(A, C) → " +
		"complex_ops(A, D) → " +
		"(num → B → C) → " +
		"(num → C → D) → " +
		"bool",
	Key: "prop_9719007a4c5ba8d0",

	Equations: []string{
		"∀P':complex_ops(A, B). " +
			"∀P:complex_ops(A, C). " +
			"∀P'':complex_ops(A, D). " +
			"∀i:(num → B → C). " +
			"∀p:(num → C → D). " +
			"    exact_complexes(P', P, P'', i, p) ⇔ " +
			"    ∀n:num. " +
			"        injective_on(P'.terms(n), i(n)) ∧ " +
			"        exact_at(P''.zero, P'.terms(n), P.terms(n), i(n), p(n)) ∧ " +
			"        image(p(n), P.terms(n)) = P''.terms(n)",
	},
	Deps: []registry.EntryLike{ComplexZeroDef, ComplexTermsDef},
})}

// ShortExactComplexes — `short_exact_complexes(…)`: three complexes
// P', P, the quotient complex at three types over one ring, chain maps i: P' → P and
// p: P → the quotient complex, exact in every degree; with no single subject, its laws
// fold under the letter S.
var ShortExactComplexes = shortExactComplexesThm{family.DefineStructure(registry.DefEntry{
	Name:  "ShortExactComplexes",
	Const: "short_exact_complexes",
	Type: "ring_ops(A) → " +
		"complex_ops(A, B) → " +
		"complex_ops(A, C) → " +
		"complex_ops(A, D) → " +
		"(num → B → C) → " +
		"(num → C → D) → " +
		"bool",
	Key:    "prop_b85087c4c5b87b70",
	Letter: "S",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀P':complex_ops(A, B). " +
			"∀P:complex_ops(A, C). " +
			"∀P'':complex_ops(A, D). " +
			"∀i:(num → B → C). " +
			"∀p:(num → C → D). " +
			"    short_exact_complexes(R, P', P, P'', i, p) ⇔ " +
			"    chain_complex(R, P') ∧ " +
			"    chain_complex(R, P) ∧ " +
			"    chain_complex(R, P'') ∧ " +
			"    chain_map(R, P', P, i) ∧ " +
			"    chain_map(R, P, P'', p) ∧ " +
			"    exact_complexes(P', P, P'', i, p)",
	},
	Deps: []registry.EntryLike{ChainComplex, ChainMapDef, ExactComplexesDef},
})}

// ShortExactSubComplex — the subcomplex.
var ShortExactSubComplex = shortExactSubComplexThm{family.Add(registry.ProofEntry{
	Name:  "ShortExactSubComplex",
	Key:   "prop_4f0f6fc86073cbef",
	Build: ShortExactComplexes.Axiom("chain_complex(R, P')"),
})}

// ShortExactMiddleComplex — the middle complex.
var ShortExactMiddleComplex = shortExactMiddleComplexThm{family.Add(registry.ProofEntry{
	Name:  "ShortExactMiddleComplex",
	Key:   "prop_367f50509726c208",
	Build: ShortExactComplexes.Axiom("chain_complex(R, P)"),
})}

// ShortExactQuotientComplex — the quotient complex.
var ShortExactQuotientComplex = shortExactQuotientComplexThm{family.Add(registry.ProofEntry{
	Name:  "ShortExactQuotientComplex",
	Key:   "prop_cdec98c4010257a4",
	Build: ShortExactComplexes.Axiom("chain_complex(R, P'')"),
})}

// ShortExactInclusionMap — the inclusion is a map of complexes.
var ShortExactInclusionMap = shortExactInclusionMapThm{family.Add(registry.ProofEntry{
	Name:  "ShortExactInclusionMap",
	Key:   "prop_3a82316b35b2706f",
	Build: ShortExactComplexes.Axiom("chain_map(R, P', P, i)"),
})}

// ShortExactProjectionMap — the projection is a map of complexes.
var ShortExactProjectionMap = shortExactProjectionMapThm{family.Add(registry.ProofEntry{
	Name:  "ShortExactProjectionMap",
	Key:   "prop_c2b16e4ab76b21a3",
	Build: ShortExactComplexes.Axiom("chain_map(R, P, P'', p)"),
})}

// ShortExactDegreewise — the sequence is exact in every degree.
var ShortExactDegreewise = shortExactDegreewiseThm{family.Add(registry.ProofEntry{
	Name:  "ShortExactDegreewise",
	Key:   "prop_4041d1aa0904c5e0",
	Build: ShortExactComplexes.Axiom("exact_complexes(P', P, P'', i, p)"),
})}

// ConnectingHomDef — `connecting_hom(P', P, i, p, n, s)`, the complex
// records: the connecting homomorphism from quotient homology in degree
// n + 1 to subcomplex homology in degree n. For a class s, lift a
// member of s to P.terms(n+1) through p, take its boundary, pull it back
// through i to P'.terms(n), and take the class. The member, lift and
// pull-back are chosen; the class does not depend on the choice.
var ConnectingHomDef = connectingHomDefThm{family.Define(registry.DefEntry{
	Name:  "ConnectingHomDef",
	Const: "connecting_hom",
	Type: "complex_ops(A, B) → " +
		"complex_ops(A, C) → " +
		"(num → B → C) → " +
		"(num → C → D) → " +
		"num → " +
		"set(D) → " +
		"set(B)",
	Key: "prop_b200fa530ec3883e",

	Equations: []string{
		"∀P':complex_ops(A, B). " +
			"∀P:complex_ops(A, C). " +
			"∀i:(num → B → C). " +
			"∀p:(num → C → D). " +
			"∀n:num. " +
			"∀s:set(D). " +
			"    connecting_hom(P', P, i, p, n, s) = " +
			"    left_coset(P'.add, " +
			"        εw:B. " +
			"            w ∈ P'.terms(n) ∧ " +
			"            (∃u:C. u ∈ P.terms(n + 1) ∧ p(n + 1)(u) ∈ s ∧ i(n)(w) = P.d(n + 1)(u)), " +
			"        boundaries(P', n))",
	},
	Deps: []registry.EntryLike{
		ComplexAddDef,
		ComplexTermsDef,
		ComplexDifferentialDef,
		BoundariesDef,
	},
})}

// CycleLiftPullback — lift a cycle through p, pull its boundary back
// through i, and use the commuting square and injectivity of i to show
// the pull-back is a cycle; in degree 0 its membership suffices.
var CycleLiftPullback = cycleLiftPullbackThm{family.Add(registry.ProofEntry{
	Name: "CycleLiftPullback",
	Key:  "prop_72008edf8c040a13",
	Build: ShortExactComplexes.Law(Statement{
		Binders: "∀n:num. ∀z:D.",
		Hypotheses: []string{
			"z ∈ cycles(P'', n + 1)",
		},
		Conclusion: "∃u:C. ∃w:B. " +
			"    u ∈ P.terms(n + 1) ∧ " +
			"    p(n + 1)(u) = z ∧ " +
			"    w ∈ P'.terms(n) ∧ " +
			"    i(n)(w) = P.d(n + 1)(u) ∧ " +
			"    w ∈ cycles(P', n)",
	},
		func(a *Argument, S ShortExactComplexesFact[on.R], n *Expr[Nat], z *Expr[D], zCycle Fact) {
			parts := []Fact{
				Read(ShortExactSubComplex, S),
				Read(ShortExactMiddleComplex, S),
				Read(ShortExactQuotientComplex, S),
				Read(ShortExactInclusionMap, S),
				Read(ShortExactProjectionMap, S),
				Read(ShortExactDegreewise, S),
			}
			sub, middle, quotient := parts[0], parts[1], parts[2]
			iClauses := []Fact{Read(ChainMapHom, parts[3]), Read(ChainMapSquare, parts[3])}
			pClauses := []Fact{Read(ChainMapHom, parts[4]), Read(ChainMapSquare, parts[4])}
			iHoms, iSquare, pHoms, pSquare := iClauses[0], iClauses[1], pClauses[0], pClauses[1]
			exact := a.Unfolded(parts[5], ExactComplexesDef)
			subModules, middleModules, quotientModules :=
				ComplexModules.Read(sub), ComplexModules.Read(middle), ComplexModules.Read(quotient)
			subBoundaryHoms, middleBoundaryHoms, quotientBoundaryHoms :=
				ComplexBoundaryHom.Read(sub), ComplexBoundaryHom.Read(middle), ComplexBoundaryHom.Read(quotient)

			zKernel := a.Have(
				"above degree 0 the cycle z lies in the kernel of the boundary map",
				"z ∈ group_kernel(P''.zero, P''.terms(n + 1), P''.d(n + 1))",
				By(zCycle, CyclesKernel.At(a.TermAs[ComplexOps[A, D]]("P''"), n)))
			u, uIs := a.ObtainAs[C](
				"z lifts to a u of P.terms(n + 1), p(n + 1) being onto",
				"∃u:C. u ∈ P.terms(n + 1) ∧ p(n + 1)(u) = z",
				ByChase(Depth(1), middleModules, quotientModules, pHoms, exact, zKernel))
			w, wIs := a.ObtainAs[B](
				"the square puts P.d(n + 1)(u) in the kernel of p(n), so exactness pulls it back through i(n)",
				"∃w:B. w ∈ P'.terms(n) ∧ i(n)(w) = P.d(n + 1)(u)",
				ByChase(
					Depth(1),
					subModules,
					middleModules,
					quotientModules,
					middleBoundaryHoms,
					quotientBoundaryHoms,
					iHoms,
					pHoms,
					pSquare,
					exact,
					zKernel,
					uIs))
			lift := a.Conjuncts(
				uIs,
				"u lies in P.terms(n + 1)",
				"u lifts z")
			pull := a.Conjuncts(
				wIs,
				"w lies in P'.terms(n)",
				"w pulls back P.d(n + 1)(u)")
			wCycle := a.Have(
				"w is a cycle of P'",
				"w ∈ cycles(P', n)",
				Derive(func(b *Argument) {
					positive := b.Unless(
						b.Term("n = 0"),
						"at degree 0 every member of P'.terms(0) is a cycle",
						Given(func(c *Argument, isZero Fact) {
							whole := c.Have(
								"n being 0, the cycles of P' there are all of P'.terms(n)",
								"cycles(P', n) = P'.terms(n)",
								isZero.Rw(),
								Cite(CyclesZero))
							c.Show(
								"and w lies in P'.terms(n)",
								whole.Rw(),
								By(pull[0]))
						}))
					_, isSuc := b.ObtainAs[Nat](
						"a positive degree is a successor",
						"∃m:num. n = m + 1",
						By(positive, nat_arith.NonzeroIsSucc))
					lifted := b.Have(
						"read the lift and pull-back at n = m + 1",
						"w ∈ P'.terms(m + 1) ∧ i(m + 1)(w) = P.d(m + 1 + 1)(u) ∧ u ∈ P.terms(m + 1 + 1)",
						By(Normalized, pull[0], pull[1], lift[0], isSuc))
					killed := b.Have(
						"the square and two successive boundaries give i(m)(P'.d(m "+
							"+ 1)(w)) = 0, so injectivity kills P'.d(m + 1)(w)",
						"P'.d(m + 1)(w) = P'.zero",
						ByChase(
							Depth(1),
							subModules,
							middleModules,
							subBoundaryHoms,
							middleBoundaryHoms,
							ComplexBoundaryTwice.Read(middle),
							iHoms,
							iSquare,
							exact,
							lifted))
					atN := b.Have(
						"which is P'.d(n) killing w",
						"P'.d(n)(w) = P'.zero",
						By(Normalized, killed, isSuc))
					b.Show(
						"so w is a cycle",
						Unfold(CyclesDef),
						BySets(pull[0], atN))
				}))
			a.Take(u)
			a.Take(w)
			a.Show(
				"u lifts z and the cycle w pulls back its boundary",
				By(lift[0], lift[1], pull[0], pull[1], wCycle))
		}),
})}

// ConnectingHomCoset — the connecting map on the class of a cycle z,
// computed from any lift u of z and any pull-back w of P.d(n + 1)(u): the
// class of w. The map takes the chosen pull-back w₁ of P.d(n + 1)(u₁), u₁
// a lift of a member of the class, and w and u realise the choice. Then
// p(n + 1)(u₁) = z + b with b a boundary of the quotient complex, and
// the rest pulls back twice: b is the quotient differential of y, and
// y = p(n + 2)(x) for an x of P.terms(n + 2), p(n + 2) being onto, so
// b = p(n + 1)(P.d(n + 2)(x)) and P.d(n + 1) kills P.d(n + 2)(x). So
// u₁ − u − P.d(n + 2)(x) lies in the kernel of p(n + 1) and is i(n + 1)(v),
// whence i(n)(w₁ − w) = P.d(n + 1)(i(n + 1)(v)) = i(n)(P'.d(n + 1)(v)); i(n)
// is one-to-one, so w₁ − w = P'.d(n + 1)(v) is a boundary of P' at n.
var ConnectingHomCoset = connectingHomCosetThm{family.Add(registry.ProofEntry{
	Name: "ConnectingHomCoset",
	Key:  "prop_4f0458db0f76f183",
	Build: ShortExactComplexes.Law(Statement{
		Binders: "∀n:num. ∀z:D. ∀u:C. ∀w:B.",
		Hypotheses: []string{
			"u ∈ P.terms(n + 1)",
			"p(n + 1)(u) = z",
			"w ∈ P'.terms(n)",
			"i(n)(w) = P.d(n + 1)(u)",
		},
		Conclusion: "connecting_hom(P', P, i, p, n, left_coset(P''.add, z, boundaries(P'', n + 1))) = " +
			"left_coset(P'.add, w, boundaries(P', n))",
	},
		func(
			a *Argument,
			S ShortExactComplexesFact[on.R],
			n *Expr[Nat],
			z *Expr[D],
			u *Expr[C],
			w *Expr[B],
			hyps Fact,
		) {
			parts := []Fact{
				Read(ShortExactSubComplex, S),
				Read(ShortExactMiddleComplex, S),
				Read(ShortExactQuotientComplex, S),
				Read(ShortExactInclusionMap, S),
				Read(ShortExactProjectionMap, S),
				Read(ShortExactDegreewise, S),
			}
			sub, middle, quotient := parts[0], parts[1], parts[2]
			iClauses := []Fact{Read(ChainMapHom, parts[3]), Read(ChainMapSquare, parts[3])}
			pClauses := []Fact{Read(ChainMapHom, parts[4]), Read(ChainMapSquare, parts[4])}
			iHoms, iSquare, pHoms, pSquare := iClauses[0], iClauses[1], pClauses[0], pClauses[1]
			exact := a.Unfolded(parts[5], ExactComplexesDef)
			subModules, middleModules, quotientModules :=
				ComplexModules.Read(sub), ComplexModules.Read(middle), ComplexModules.Read(quotient)
			subBoundaryHoms, middleBoundaryHoms, quotientBoundaryHoms :=
				ComplexBoundaryHom.Read(sub), ComplexBoundaryHom.Read(middle), ComplexBoundaryHom.Read(quotient)
			given := a.Conjuncts(
				hyps,
				"u lies in P.terms(n + 1)",
				"u lifts z",
				"w lies in P'.terms(n)",
				"w pulls back P.d(n + 1)(u)")
			uIn, uLifts, wIn, wPulls := given[0], given[1], given[2], given[3]

			ownClass := a.Have(
				"p(n + 1)(u) = z lies in the class of z, as z + P''.zero",
				"p(n + 1)(u) ∈ left_coset(P''.add, z, boundaries(P'', n + 1))",
				Derive(func(b *Argument) {
					b.Do(Simp(
						Fwd(group.LeftCosetDef.Inst[D]()),
						Fwd(set_basic.InImage.Inst(TypeBinder.BindA[D](), TypeBinder.BindB[D]())),
						Fwd(BoundariesDef)))
					b.Take(b.Term("P''.zero"))
					b.Show(
						"p(n + 1)(u) = z = z + P''.zero, and P''.zero = P''.d(n + 2)(P''.zero) is a boundary",
						ByChase(Depth(0), middleModules, quotientModules, quotientBoundaryHoms, pHoms, uIn, uLifts))
				}))
			targetBoundaries := a.Have(
				"the boundaries of P' at n are the image of P'.d(n + 1)",
				"boundaries(P', n) = image(P'.d(n + 1), P'.terms(n + 1))",
				By(BoundariesDef))

			// The map's value is the class of the chosen pull-back.
			a.Do(Simp(Fwd(ConnectingHomDef)), targetBoundaries.Rw())
			_, chosen := a.ObtainChosen(
				"w pulls back P.d(n + 1)(u), and u lifts a member of the class",
				"∃w₁:B. "+
					"    w₁ ∈ P'.terms(n) ∧ "+
					"    (∃u₁:C. "+
					"        u₁ ∈ P.terms(n + 1) ∧ "+
					"        p(n + 1)(u₁) ∈ left_coset(P''.add, z, boundaries(P'', n + 1)) ∧ "+
					"        i(n)(w₁) = P.d(n + 1)(u₁))",
				wIn,
				uIn,
				wPulls,
				ownClass)
			pullBack := a.Conjuncts(
				chosen,
				"the chosen w₁ lies in P'.terms(n)",
				"w₁ pulls back P.d(n + 1)(u₁) for a lift u₁ of a member of the class")
			_, lift := a.Unpack(pullBack[1])
			lifted := a.Conjuncts(
				lift,
				"u₁ lies in P.terms(n + 1)",
				"p(n + 1)(u₁) lies in the class of z",
				"i(n)(w₁) = P.d(n + 1)(u₁)")
			_, member := a.Obtain(
				"p(n + 1)(u₁) is z + b for a boundary b of P'' at n + 1",
				"∃b:D. p(n + 1)(u₁) = P''.add(z, b) ∧ b ∈ boundaries(P'', n + 1)",
				By(a.Unfolded(lifted[1], group.LeftCosetDef), set_basic.InImage))
			images := a.Have(
				"the image of P'.d(n + 1) is a submodule of P'.terms(n)",
				"submodule(R, complex_module(P', n), image(P'.d(n + 1), P'.terms(n + 1)))",
				targetBoundaries.RwRev(),
				By(BoundariesSubmodule.Read(sub).At(n)))
			a.Show(
				"u₁ − u differs from i(n + 1)(v) by a boundary of "+
					"P; injectivity of i(n) gives w₁ − w = P'.d(n + 1)(v)",
				ByChase(
					Depth(2),
					subModules,
					middleModules,
					quotientModules,
					subBoundaryHoms,
					middleBoundaryHoms,
					quotientBoundaryHoms,
					ComplexBoundaryTwice.Read(middle),
					iHoms,
					pHoms,
					iSquare,
					pSquare,
					exact,
					uIn,
					uLifts,
					wIn,
					wPulls,
					pullBack[0],
					lifted[0],
					lifted[2],
					a.Unfolded(member, BoundariesDef),
					images))
		}),
})}

// ConnectingHom — a quotient cycle is related to the cycle pulled back
// from its lift's boundary. Sums and scalar multiples of lifts keep this
// relation, and its coset values give the connecting homomorphism.
var ConnectingHom = connectingHomThm{family.Add(registry.ProofEntry{
	Name: "ConnectingHom",
	Key:  "prop_39f3689a452d7183",
	Build: ShortExactComplexes.Law("∀n:num. "+
		"    module_homomorphism(R, "+
		"        homology_module(P'', n + 1), "+
		"        homology_module(P', n), "+
		"        connecting_hom(P', P, i, p, n))",
		func(a *Argument, S ShortExactComplexesFact[on.R], n *Expr[Nat]) {
			sub, middle, quotient :=
				ShortExactSubComplex.Read(S), ShortExactMiddleComplex.Read(S), ShortExactQuotientComplex.Read(S)
			iHoms := ChainMapHom.Read(ShortExactInclusionMap.Read(S))
			pHoms := ChainMapHom.Read(ShortExactProjectionMap.Read(S))
			dHoms := ComplexBoundaryHom.Read(middle)
			quotientAt := a.Have(
				"the source degree is a module",
				"module_on(R, complex_module(P'', n + 1))",
				By(ComplexModules.Read(quotient)))
			subAt := a.Have(
				"the target degree is a module",
				"module_on(R, complex_module(P', n))",
				By(ComplexModules.Read(sub)))
			sourceBoundaries := a.Have(
				"source boundaries form a submodule of cycles",
				"submodule(R, "+
					"    restrict_module(complex_module(P'', n + 1), cycles(P'', n + 1)), "+
					"    boundaries(P'', n + 1))",
				By(
					BoundariesSubmodule.Read(quotient),
					BoundariesSubsetCycles.Read(quotient),
					submodule.SubmoduleRestrict))
			targetBoundaries := a.Have(
				"target boundaries form a submodule of cycles",
				"submodule(R, restrict_module(complex_module(P', n), cycles(P', n)), boundaries(P', n))",
				By(BoundariesSubmodule.Read(sub), BoundariesSubsetCycles.Read(sub), submodule.SubmoduleRestrict))

			relationTotal := a.Have(
				"every source cycle has a related target cycle",
				Statement{
					Binders: "∀z:D.",
					Hypotheses: []string{
						"z ∈ cycles(P'', n + 1)",
					},
					Conclusion: "∃w:B. " +
						"    w ∈ cycles(P', n) ∧ (∃u:C. u ∈ P.terms(n + 1) ∧ p(n + 1)(u) = z ∧ i(n)(w) = P.d(n + 1)(u))",
				},
				By(CycleLiftPullback.Read(S)))
			relationAdd := a.Have(
				"sums of related pairs are related",
				Statement{
					Binders: "∀z₁ z₂:D. ∀w₁ w₂:B.",
					Hypotheses: []string{
						"z₁ ∈ cycles(P'', n + 1)",
						"z₂ ∈ cycles(P'', n + 1)",
						"w₁ ∈ cycles(P', n)",
						"w₂ ∈ cycles(P', n)",
						"∃u₁:C. u₁ ∈ P.terms(n + 1) ∧ p(n + 1)(u₁) = z₁ ∧ i(n)(w₁) = P.d(n + 1)(u₁)",
						"∃u₂:C. u₂ ∈ P.terms(n + 1) ∧ p(n + 1)(u₂) = z₂ ∧ i(n)(w₂) = P.d(n + 1)(u₂)",
					},
					Conclusion: "∃u:C. " +
						"    u ∈ P.terms(n + 1) ∧ p(n + 1)(u) = P''.add(z₁, z₂) ∧ i(n)(P'.add(w₁, w₂)) = P.d(n + 1)(u)",
				},
				Derive(func(b *Argument) {
					b.FixAs[D]("z₁")
					b.FixAs[D]("z₂")
					b.FixAs[B]("w₁")
					b.FixAs[B]("w₂")
					related := b.Assume()
					members := b.Have(
						"the target cycles lie in the target degree",
						"w₁ ∈ P'.terms(n) ∧ w₂ ∈ P'.terms(n)",
						BySets(related, CyclesDef.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[B]())))
					_, firstLift := b.ObtainAs[C](
						"the first related pair has a lift",
						"∃u₁:C. u₁ ∈ P.terms(n + 1) ∧ p(n + 1)(u₁) = z₁ ∧ i(n)(w₁) = P.d(n + 1)(u₁)",
						By(related))
					_, secondLift := b.ObtainAs[C](
						"the second related pair has a lift",
						"∃u₂:C. u₂ ∈ P.terms(n + 1) ∧ p(n + 1)(u₂) = z₂ ∧ i(n)(w₂) = P.d(n + 1)(u₂)",
						By(related))
					b.Take(b.TermAs[C]("P.add(u₁, u₂)"))
					b.Show(
						"the sum of the lifts realizes the sum of the related pairs",
						ByChase(Depth(0), pHoms, iHoms, dHoms, members, firstLift, secondLift))
				}))
			relationScale := a.Have(
				"scalar multiples of related pairs are related",
				Statement{
					Binders: "∀c:A. ∀z:D. ∀w:B.",
					Hypotheses: []string{
						"c ∈ R.carrier",
						"z ∈ cycles(P'', n + 1)",
						"w ∈ cycles(P', n)",
						"∃u:C. u ∈ P.terms(n + 1) ∧ p(n + 1)(u) = z ∧ i(n)(w) = P.d(n + 1)(u)",
					},
					Conclusion: "∃u:C. " +
						"    u ∈ P.terms(n + 1) ∧ p(n + 1)(u) = P''.smul(c, z) ∧ i(n)(P'.smul(c, w)) = P.d(n + 1)(u)",
				},
				Derive(func(b *Argument) {
					b.FixAs[A]("c")
					b.FixAs[D]("z")
					b.FixAs[B]("w")
					related := b.Assume()
					member := b.Have(
						"the target cycle lies in the target degree",
						"w ∈ P'.terms(n)",
						BySets(related, CyclesDef.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[B]())))
					_, lift := b.ObtainAs[C](
						"the related pair has a lift",
						"∃u:C. u ∈ P.terms(n + 1) ∧ p(n + 1)(u) = z ∧ i(n)(w) = P.d(n + 1)(u)",
						By(related))
					b.Take(b.TermAs[C]("P.smul(c, u)"))
					b.Show(
						"the scaled lift realizes the scaled related pair",
						ByChase(Depth(0), pHoms, iHoms, dHoms, member, related, lift))
				}))
			relationValue := a.Have(
				"related cycles compute the connecting map on their classes",
				Statement{
					Binders: "∀z:D. ∀w:B.",
					Hypotheses: []string{
						"z ∈ cycles(P'', n + 1)",
						"w ∈ cycles(P', n)",
						"∃u:C. u ∈ P.terms(n + 1) ∧ p(n + 1)(u) = z ∧ i(n)(w) = P.d(n + 1)(u)",
					},
					Conclusion: "connecting_hom(P', P, i, p, n, left_coset(P''.add, z, boundaries(P'', n + 1))) = " +
						"left_coset(P'.add, w, boundaries(P', n))",
				},
				Derive(func(b *Argument) {
					b.FixAs[D]("z")
					b.FixAs[B]("w")
					related := b.Assume()
					member := b.Have(
						"the target cycle lies in the target degree",
						"w ∈ P'.terms(n)",
						BySets(related, CyclesDef.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[B]())))
					_, lift := b.ObtainAs[C](
						"the related pair has a lift",
						"∃u:C. u ∈ P.terms(n + 1) ∧ p(n + 1)(u) = z ∧ i(n)(w) = P.d(n + 1)(u)",
						By(related))
					b.Show(
						"the lift computes the image class",
						By(ConnectingHomCoset.Read(S), related, member, lift))
				}))
			a.Show(
				"the relation induces a linear map on homology",
				Unfold(HomologyModuleDef),
				By(
					submodule.SubmoduleModuleOn.Read(quotientAt),
					CyclesSubmodule.Read(quotient),
					submodule.SubmoduleModuleOn.Read(subAt),
					CyclesSubmodule.Read(sub),
					sourceBoundaries,
					targetBoundaries,
					relationTotal,
					relationAdd,
					relationScale,
					relationValue,
					Where(
						module_homomorphism.QuotientRelationHom.Inst(
							TypeBinder.BindA[A](), TypeBinder.BindB[D](), TypeBinder.BindC[B]()),
						"T",
						a.TermAs[Fun2[D, B, Bool]](
							"λz:D. λw:B. ∃u:C. u ∈ P.terms(n + 1) ∧ p(n + 1)(u) = z ∧ i(n)(w) = P.d(n + 1)(u)"))))
		}),
})}

// LongExactMiddle — the long exact sequence at H(n)(P): the image of i*
// is the kernel of p*, an equation of two sets of classes read one class
// s at a time. Write N for the boundaries of the quotient complex at n,
// the image of its boundary map out of degree n + 1: the zero class there
// is N, the class of the zero. A class in the image of i* is i* of the
// class of a cycle w of P' at n: the class of i(n)(w), a cycle of P, a
// chain map keeping cycles; p* sends that to the class of p(n)(i(n)(w)),
// zero by exactness, which is N. Conversely a class of a cycle u of P
// that p* sends to N has p(n)(u) in N, the boundary of a y of the
// quotient complex at n + 1, and y = p(n + 1)(x) for an x of P.terms(n + 1),
// p(n + 1) being onto; so p(n) kills u − P.d(n + 1)(x), the square carrying
// P.d(n + 1)(x) to the boundary of y, and u − P.d(n + 1)(x) = i(n)(w) for a w
// of P'.terms(n) by exactness. That w is a cycle: above degree 0,
// i(n − 1)(P'.d(n)(w)) = P.d(n)(u) − P.d(n)(P.d(n + 1)(x)) is zero and i(n − 1)
// is one-to-one. The class of u is the class of i(n)(w), the two
// differing by the boundary P.d(n + 1)(x), and that is i* of the class of w.
var LongExactMiddle = longExactMiddleThm{family.Add(registry.ProofEntry{
	Name: "LongExactMiddle",
	Key:  "prop_4bc739f7a4317454",
	Build: ShortExactComplexes.Law("∀n:num. "+
		"    exact_at(boundaries(P'', n), "+
		"        homology(P', n), "+
		"        homology(P, n), "+
		"        homology_map(P, i, n), "+
		"        homology_map(P'', p, n))",
		func(a *Argument, S ShortExactComplexesFact[on.R], n *Expr[Nat]) {
			parts := []Fact{
				Read(ShortExactSubComplex, S),
				Read(ShortExactMiddleComplex, S),
				Read(ShortExactQuotientComplex, S),
				Read(ShortExactInclusionMap, S),
				Read(ShortExactProjectionMap, S),
				Read(ShortExactDegreewise, S),
			}
			sub, middle, quotient, iChainMap, pChainMap := parts[0], parts[1], parts[2], parts[3], parts[4]
			iClauses := []Fact{Read(ChainMapHom, parts[3]), Read(ChainMapSquare, parts[3])}
			pClauses := []Fact{Read(ChainMapHom, parts[4]), Read(ChainMapSquare, parts[4])}
			iHoms, iSquare, pHoms, pSquare := iClauses[0], iClauses[1], pClauses[0], pClauses[1]
			exact := a.Unfolded(parts[5], ExactComplexesDef)
			subModules, middleModules, quotientModules :=
				ComplexModules.Read(sub), ComplexModules.Read(middle), ComplexModules.Read(quotient)
			subBoundaryHoms, middleBoundaryHoms, quotientBoundaryHoms :=
				ComplexBoundaryHom.Read(sub), ComplexBoundaryHom.Read(middle), ComplexBoundaryHom.Read(quotient)

			// The boundaries of P and of P'' at n as images, and the zero class of H(n)(P''): the image of P''.d(n + 1), the class of P''.zero.
			boundariesP := a.Have(
				"the boundaries of P at n are the image of P.d(n + 1)",
				"boundaries(P, n) = image(P.d(n + 1), P.terms(n + 1))",
				By(BoundariesDef))
			imagesP := a.Have(
				"the image of P.d(n + 1) is a submodule of P.terms(n)",
				"submodule(R, complex_module(P, n), image(P.d(n + 1), P.terms(n + 1)))",
				boundariesP.RwRev(),
				By(BoundariesSubmodule.Read(middle).At(n)))
			boundariesQuotient := a.Have(
				"the boundaries of P'' at n are the image of P''.d(n + 1)",
				"boundaries(P'', n) = image(P''.d(n + 1), P''.terms(n + 1))",
				By(BoundariesDef))
			imagesQuotient := a.Have(
				"the image of P''.d(n + 1) is a submodule of P''.terms(n)",
				"submodule(R, complex_module(P'', n), image(P''.d(n + 1), P''.terms(n + 1)))",
				boundariesQuotient.RwRev(),
				By(BoundariesSubmodule.Read(quotient).At(n)))
			subgroup := a.Simplified(
				submodule.SubmoduleSubgroup.Read(imagesQuotient),
				Fwd(module_record.ModuleAdditiveGroupDef),
				Fwd(ComplexModuleDef),
				Fwd(module_record.ModAddDef),
				Fwd(module_record.ModZeroDef),
				Fwd(module_record.ModNegDef),
				Fwd(module_record.ModCarrierDef))
			moduleAtN := a.Have(
				"P''.terms(n) is a module",
				"module_on(R, complex_module(P'', n))",
				By(quotientModules))
			groupAtN := a.Simplified(
				module.AddGroupOn.Read(moduleAtN),
				Fwd(module_record.ModuleAdditiveGroupDef),
				Fwd(ComplexModuleDef),
				Fwd(module_record.ModAddDef),
				Fwd(module_record.ModZeroDef),
				Fwd(module_record.ModNegDef),
				Fwd(module_record.ModCarrierDef))
			zeroClass := a.Have(
				"so the image of P''.d(n + 1) is the class of P''.zero, "+
					"the identity of the additive group of P''.terms(n)",
				"left_coset(P''.add, P''.zero, image(P''.d(n + 1), P''.terms(n + 1))) = "+
					"image(P''.d(n + 1), P''.terms(n + 1))",
				By(group.LeftCosetOneOn.Read(groupAtN), group.SubgroupSubset, subgroup))

			// The two sets of classes of P, a class s at a time: s is i* of a class of P', or s is a class that p* sends to the zero class.
			a.Do(Simp(
				Fwd(module_homomorphism.ExactAtDef),
				Fwd(set_basic.Extension.Inst[Set[C]]()),
				Fwd(group_homomorphism.InKernel)))
			a.FixAs[Set[C]]("s")
			a.Iff()
			a.Forward(
				"i* sends the class of a cycle w to the class of the cycle i(n)(w), "+
					"which p* sends to the class of p(n)(i(n)(w)), zero by exactness",
				func(b *Argument, sIn Fact) {
					_, sIs := b.Obtain(
						"s is i*(t) for a class t of P' at n",
						"∃t:set(B). s = homology_map(P, i, n, t) ∧ t ∈ homology(P', n)",
						By(sIn, set_basic.InImage.Inst(TypeBinder.BindA[Set[B]](), TypeBinder.BindB[Set[C]]())))
					sMap := b.Conjuncts(
						sIs,
						"s is i*(t)",
						"t is a class of P' at n")
					_, tIs := b.ObtainAs[B](
						"t is the class of a cycle w",
						"∃w:B. t = left_coset(P'.add, w, boundaries(P', n)) ∧ w ∈ cycles(P', n)",
						By(sMap[1], InHomology.Read(sub)))
					tClass := b.Conjuncts(
						tIs,
						"t is the class of w",
						"w is a cycle of P'")
					Pʹ, P, i :=
						b.TermAs[ComplexOps[A, B]]("P'"), b.TermAs[ComplexOps[A, C]]("P"), b.TermAs[Fun2[Nat, B, C]]("i")
					wIn := b.Have(
						"w lies in P'.terms(n)",
						"w ∈ P'.terms(n)",
						BySets(tClass[1], CyclesSubsetTerms.At(Pʹ, n)))
					iwCycle := b.Have(
						"i(n)(w) is a cycle of P, a chain map keeping cycles",
						"i(n)(w) ∈ cycles(P, n)",
						By(ChainMapCycles.Read(sub).At(P, i, n), middle, iChainMap, tClass[1]))
					iClass := b.Have(
						"i* sends the class of w to the class of i(n)(w)",
						"homology_map(P, i, n, left_coset(P'.add, w, boundaries(P', n))) = "+
							"left_coset(P.add, i(n)(w), boundaries(P, n))",
						By(HomologyMapCoset.Read(sub), middle, iChainMap, tClass[1]))
					iwClass := b.Have(
						"the class of i(n)(w) is a class of P at n",
						"left_coset(P.add, i(n)(w), boundaries(P, n)) ∈ homology(P, n)",
						Simp(Fwd(InHomology.Read(middle))),
						Derive(func(c *Argument) {
							c.Take(c.Term("i(n)(w)"))
							c.Show(
								"the class of i(n)(w) is the class of the cycle i(n)(w)",
								By(iwCycle))
						}))
					iwZero := b.Have(
						"and p* sends it to the zero class",
						"homology_map(P'', p, n, left_coset(P.add, i(n)(w), boundaries(P, n))) = boundaries(P'', n)",
						CalcEq(
							Leg(
								b.TermAs[Set[D]]("left_coset(P''.add, p(n)(i(n)(w)), boundaries(P'', n))"),
								"p* sends the class of i(n)(w) to the class of p(n)(i(n)(w))",
								By(HomologyMapCoset.Read(middle), quotient, pChainMap, iwCycle)),
							Leg(
								b.TermAs[Set[D]]("left_coset(P''.add, P''.zero, image(P''.d(n + 1), P''.terms(n + 1)))"),
								"p(n)(i(n)(w)) is P''.zero by exactness, so its class is the class of P''.zero",
								boundariesQuotient.Rw(),
								ByChase(
									Depth(0),
									subModules,
									middleModules,
									quotientModules,
									quotientBoundaryHoms,
									iHoms,
									pHoms,
									exact,
									wIn,
									imagesQuotient)),
							FinalLeg(
								"which is the zero class",
								boundariesQuotient.Rw(),
								By(zeroClass)),
						))
					b.Show(
						"s is i*(t), t the class of w, so s is the class of "+
							"i(n)(w), a class of P that p* sends to the zero class",
						sMap[0].Rw(),
						tClass[0].Rw(),
						iClass.Rw(),
						By(iwClass, iwZero))
				})
			a.Backward(
				"a cycle whose class p* kills is i(n)(w) plus a boundary, "+
					"with w a cycle of P'; its class is i* of the class of w",
				func(b *Argument, sIn Fact) {
					kernel := b.Conjuncts(
						sIn,
						"s is a class of P at n",
						"p* sends s to the zero class")
					_, sIs := b.ObtainAs[C](
						"s is the class of a cycle u",
						"∃u:C. s = left_coset(P.add, u, boundaries(P, n)) ∧ u ∈ cycles(P, n)",
						By(kernel[0], InHomology.Read(middle)))
					sClass := b.Conjuncts(
						sIs,
						"s is the class of u",
						"u is a cycle of P")
					opened := b.Conjuncts(
						b.Have(
							"u lies in P.terms(n), and P.d(n) kills it unless n = 0",
							"u ∈ P.terms(n) ∧ (n = 0 ∨ P.d(n)(u) = P.zero)",
							BySets(b.Unfolded(sClass[1], CyclesDef))),
						"u lies in P.terms(n)",
						"n = 0 or P.d(n) kills u")
					uIn, killedUnlessZero := opened[0], opened[1]
					uZero := b.Have(
						"so the class of p(n)(u) is the zero class, the class of P''.zero",
						"left_coset(P''.add, p(n)(u), image(P''.d(n + 1), P''.terms(n + 1))) = "+
							"left_coset(P''.add, P''.zero, image(P''.d(n + 1), P''.terms(n + 1)))",
						CalcEq(
							Leg(
								b.TermAs[Set[D]]("homology_map(P'', p, n, s)"),
								"the class of p(n)(u) is p*(s), s being the class of u",
								boundariesQuotient.RwRev(),
								sClass[0].Rw(),
								By(HomologyMapCoset.Read(middle), quotient, pChainMap, sClass[1])),
							Leg(
								b.TermAs[Set[D]]("image(P''.d(n + 1), P''.terms(n + 1))"),
								"which is the zero class",
								boundariesQuotient.RwRev(),
								By(kernel[1])),
							FinalLeg(
								"the class of P''.zero",
								By(zeroClass)),
						))
					_, yIs := b.ObtainAs[D](
						"so p(n)(u) is a boundary P''.d(n + 1)(y)",
						"∃y:D. y ∈ P''.terms(n + 1) ∧ P''.d(n + 1)(y) = p(n)(u)",
						ByChase(
							Depth(0),
							middleModules,
							quotientModules,
							quotientBoundaryHoms,
							pHoms,
							imagesQuotient,
							uIn,
							uZero))
					_, xIs := b.ObtainAs[C](
						"y lifts to an x of P.terms(n + 1), p(n + 1) being onto",
						"∃x:C. x ∈ P.terms(n + 1) ∧ p(n + 1)(x) = y",
						ByChase(Depth(1), middleModules, quotientModules, pHoms, exact, yIs))
					lift := b.Conjuncts(
						xIs,
						"x lies in P.terms(n + 1)",
						"x lifts y")
					w, wIs := b.ObtainAs[B](
						"p(n) kills u − P.d(n + 1)(x), as p(n)(P.d(n + 1)(x)) = P''.d(n + "+
							"1)(y) = p(n)(u), so u − P.d(n + 1)(x) is i(n)(w) for a w of P'.terms(n)",
						"∃w:B. w ∈ P'.terms(n) ∧ i(n)(w) = P.add(u, P.neg(P.d(n + 1)(x)))",
						ByChase(
							Depth(1),
							subModules,
							middleModules,
							quotientModules,
							middleBoundaryHoms,
							quotientBoundaryHoms,
							iHoms,
							pHoms,
							pSquare,
							exact,
							uIn,
							yIs,
							xIs))
					pull := b.Conjuncts(
						wIs,
						"w lies in P'.terms(n)",
						"w pulls back u − P.d(n + 1)(x)")
					wCycle := b.Have(
						"w is a cycle of P'",
						"w ∈ cycles(P', n)",
						Derive(func(c *Argument) {
							positive := c.Unless(
								c.Term("n = 0"),
								"at degree 0 every member of P'.terms(0) is a cycle",
								Given(func(e *Argument, isZero Fact) {
									whole := e.Have(
										"n being 0, the cycles of P' there are all of P'.terms(n)",
										"cycles(P', n) = P'.terms(n)",
										isZero.Rw(),
										Cite(CyclesZero))
									e.Show(
										"and w lies in P'.terms(n)",
										whole.Rw(),
										By(pull[0]))
								}))
							_, isSuc := c.ObtainAs[Nat](
								"a positive degree is a successor",
								"∃m:num. n = m + 1",
								By(positive, nat_arith.NonzeroIsSucc.At(n)))
							lifted := c.Have(
								"at n = m + 1, the pull-back equation and cycle conditions hold at the successor degree",
								"w ∈ P'.terms(m + 1) ∧ "+
									"i(m + 1)(w) = P.add(u, P.neg(P.d(m + 1 + 1)(x))) ∧ "+
									"u ∈ P.terms(m + 1) ∧ "+
									"P.d(m + 1)(u) = P.zero ∧ "+
									"x ∈ P.terms(m + 1 + 1)",
								By(Normalized, pull[0], pull[1], uIn, killedUnlessZero, positive, lift[0], isSuc))
							wKilled := c.Have(
								"i(m)(P'.d(m + 1)(w)) = P.d(m + 1)(u) − P.d(m + 1)(P.d(m + "+
									"2)(x)) is zero and i(m) is one-to-one, so P'.d(m + 1) kills w",
								"P'.d(m + 1)(w) = P'.zero",
								ByChase(
									Depth(1),
									subModules,
									middleModules,
									subBoundaryHoms,
									middleBoundaryHoms,
									ComplexBoundaryTwice.Read(middle),
									iHoms,
									iSquare,
									exact,
									lifted))
							atN := c.Have(
								"which is P'.d(n) killing w, n being m + 1",
								"P'.d(n)(w) = P'.zero",
								By(Normalized, wKilled, isSuc))
							c.Show(
								"so w is a cycle",
								Unfold(CyclesDef),
								BySets(pull[0], atN))
						}))
					sameClass := b.Have(
						"u and i(n)(w) differ by the boundary P.d(n + 1)(x), so their classes agree",
						"left_coset(P.add, u, image(P.d(n + 1), P.terms(n + 1))) = "+
							"left_coset(P.add, i(n)(w), image(P.d(n + 1), P.terms(n + 1)))",
						ByChase(Depth(0), middleModules, middleBoundaryHoms, imagesP, uIn, lift[0], pull[1]))
					iClass := b.Have(
						"i* sends the class of w to the class of i(n)(w)",
						"homology_map(P, i, n, left_coset(P'.add, w, boundaries(P', n))) = "+
							"left_coset(P.add, i(n)(w), boundaries(P, n))",
						By(HomologyMapCoset.Read(sub), middle, iChainMap, wCycle))
					wClass := b.Have(
						"the class of w is a class of P' at n",
						"left_coset(P'.add, w, boundaries(P', n)) ∈ homology(P', n)",
						Simp(Fwd(InHomology.Read(sub))),
						Derive(func(c *Argument) {
							c.Take(w)
							c.Show(
								"the class of w is the class of the cycle w",
								By(wCycle))
						}))
					b.Do(Simp(Fwd(set_basic.InImage.Inst(TypeBinder.BindA[Set[B]](), TypeBinder.BindB[Set[C]]()))))
					b.Take(b.Term("left_coset(P'.add, w, boundaries(P', n))"))
					b.Show(
						"s, the class of u, is the class of i(n)(w), which is i* of the class of w",
						iClass.Rw(),
						sClass[0].Rw(),
						boundariesP.Rw(),
						By(sameClass, wClass))
				})
		}),
})}

// LongExactQuotient — the long exact sequence at H(n + 1) of the
// quotient complex: the image of p* is the kernel of δ, an equation of
// two sets of classes read one class s at a time. Write N for the
// boundaries of P' at n, the image of P'.d(n + 1): the zero class of
// H(n)(P') is N, the class of the zero of P'. A class in the image of p*
// is p* of the class of a cycle u of P at n + 1: the class of
// p(n + 1)(u), a cycle of the quotient complex, p being a chain map;
// P.d(n + 1) kills u, so the zero of P' pulls P.d(n + 1)(u) back, and δ,
// computed from the lift u itself, sends the class of p(n + 1)(u) to the
// zero class. Conversely a class of a cycle z of the quotient complex
// that δ sends to the zero class: z lifts to u in P.terms(n + 1), p(n + 1)
// being onto, and P.d(n + 1)(u) = i(n)(w) for a w of P'.terms(n); δ sends the
// class of z to the class of w, which is N, so w = P'.d(n + 1)(v) for a v
// of P'.terms(n + 1). Then x = u − i(n + 1)(v) is a cycle of P, P.d(n + 1)(x)
// being i(n)(w) − i(n)(P'.d(n + 1)(v)), the zero of P, by the square; and
// p(n + 1)(x) = z, p(n + 1) killing i(n + 1)(v); p* sends the class of x
// to the class of z.
var LongExactQuotient = longExactQuotientThm{family.Add(registry.ProofEntry{
	Name: "LongExactQuotient",
	Key:  "prop_10db513b1ebf92b",
	Build: ShortExactComplexes.Law("∀n:num. "+
		"    exact_at(boundaries(P', n), "+
		"        homology(P, n + 1), "+
		"        homology(P'', n + 1), "+
		"        homology_map(P'', p, n + 1), "+
		"        connecting_hom(P', P, i, p, n))",
		func(a *Argument, S ShortExactComplexesFact[on.R], n *Expr[Nat]) {
			parts := []Fact{
				Read(ShortExactSubComplex, S),
				Read(ShortExactMiddleComplex, S),
				Read(ShortExactQuotientComplex, S),
				Read(ShortExactInclusionMap, S),
				Read(ShortExactProjectionMap, S),
				Read(ShortExactDegreewise, S),
			}
			sub, middle, quotient, pChainMap := parts[0], parts[1], parts[2], parts[4]
			iClauses := []Fact{Read(ChainMapHom, parts[3]), Read(ChainMapSquare, parts[3])}
			pClauses := []Fact{Read(ChainMapHom, parts[4]), Read(ChainMapSquare, parts[4])}
			iHoms, iSquare, pHoms, pSquare := iClauses[0], iClauses[1], pClauses[0], pClauses[1]
			exact := a.Unfolded(parts[5], ExactComplexesDef)
			subModules, middleModules, quotientModules :=
				ComplexModules.Read(sub), ComplexModules.Read(middle), ComplexModules.Read(quotient)
			subBoundaryHoms, middleBoundaryHoms, quotientBoundaryHoms :=
				ComplexBoundaryHom.Read(sub), ComplexBoundaryHom.Read(middle), ComplexBoundaryHom.Read(quotient)

			// The zero class of H(n)(P'): the boundaries N, the image of P'.d(n + 1), and the class of P'.zero.
			boundariesSub := a.Have(
				"the boundaries of P' at n are the image of P'.d(n + 1)",
				"boundaries(P', n) = image(P'.d(n + 1), P'.terms(n + 1))",
				By(BoundariesDef))
			images := a.Have(
				"the image of P'.d(n + 1) is a submodule of P'.terms(n)",
				"submodule(R, complex_module(P', n), image(P'.d(n + 1), P'.terms(n + 1)))",
				boundariesSub.RwRev(),
				By(BoundariesSubmodule.Read(sub).At(n)))
			subgroup := a.Simplified(
				submodule.SubmoduleSubgroup.Read(images),
				Fwd(module_record.ModuleAdditiveGroupDef))
			moduleAtN := a.Have(
				"P'.terms(n) is a module",
				"module_on(R, complex_module(P', n))",
				By(subModules))
			groupAtN := a.Simplified(
				module.AddGroupOn.Read(moduleAtN),
				Fwd(module_record.ModuleAdditiveGroupDef))
			zeroClass := a.Have(
				"so the image of P'.d(n + 1) is the class of P'.zero, "+
					"the identity of the additive group of P'.terms(n)",
				"left_coset(P'.add, P'.zero, image(P'.d(n + 1), P'.terms(n + 1))) = "+
					"image(P'.d(n + 1), P'.terms(n + 1))",
				By(group.LeftCosetOneOn.Read(groupAtN), group.SubgroupSubset, subgroup))

			// The two sets of classes of P'', a class s at a time: s is p* of a class of P, or s is a class that δ sends to the zero class.
			a.Do(Simp(
				Fwd(module_homomorphism.ExactAtDef),
				Fwd(set_basic.Extension.Inst[Set[D]]()),
				Fwd(group_homomorphism.InKernel)))
			a.FixAs[Set[D]]("s")
			a.Iff()
			a.Forward(
				"p* sends the class of a cycle u to the class of p(n + 1)(u), "+
					"which δ computes from the lift u and sends to the zero class",
				func(b *Argument, sIn Fact) {
					_, sIs := b.Obtain(
						"s is p*(t) for a class t of P at n + 1",
						"∃t:set(C). s = homology_map(P'', p, n + 1, t) ∧ t ∈ homology(P, n + 1)",
						By(sIn, set_basic.InImage.Inst(TypeBinder.BindA[Set[C]](), TypeBinder.BindB[Set[D]]())))
					sMap := b.Conjuncts(
						sIs,
						"s is p*(t)",
						"t is a class of P at n + 1")
					u, tIs := b.ObtainAs[C](
						"t is the class of a cycle u",
						"∃u:C. t = left_coset(P.add, u, boundaries(P, n + 1)) ∧ u ∈ cycles(P, n + 1)",
						By(sMap[1], InHomology.Read(middle)))
					tClass := b.Conjuncts(
						tIs,
						"t is the class of u",
						"u is a cycle of P")
					uKernel := b.Have(
						"above degree 0 a cycle lies in the kernel: u lies in P.terms(n + 1) and P.d(n + 1) kills it",
						"u ∈ group_kernel(P.zero, P.terms(n + 1), P.d(n + 1))",
						Simp(Rev(CyclesKernel)),
						By(tClass[1]))
					zCycle := b.Have(
						"p keeps cycles: P''.d(n + 1)(p(n + 1)(u)) = p(n)(P.d(n + 1)(u)), the zero of P''",
						"p(n + 1)(u) ∈ cycles(P'', n + 1)",
						Simp(Fwd(CyclesKernel)),
						ByChase(
							Depth(0),
							middleModules,
							quotientModules,
							middleBoundaryHoms,
							quotientBoundaryHoms,
							pHoms,
							pSquare,
							uKernel))
					zeroPulls := b.Have(
						"u lies in P.terms(n + 1), and P.d(n + 1)(u) is P.zero, which P'.zero pulls back",
						"u ∈ P.terms(n + 1) ∧ P'.zero ∈ P'.terms(n) ∧ i(n)(P'.zero) = P.d(n + 1)(u)",
						ByChase(Depth(0), subModules, middleModules, middleBoundaryHoms, iHoms, uKernel))
					classIs := b.Have(
						"δ, computed from the lift u, sends the class of p(n + 1)(u) to the class of P'.zero",
						"connecting_hom(P', P, i, p, n, left_coset(P''.add, p(n + 1)(u), boundaries(P'', n + 1))) = "+
							"left_coset(P'.add, P'.zero, boundaries(P', n))",
						By(
							ConnectingHomCoset.Read(S).At(n, b.TermAs[D]("p(n + 1)(u)"), u, b.TermAs[B]("P'.zero")),
							zCycle,
							zeroPulls))
					pClass := b.Have(
						"p* sends the class of u to the class of p(n + 1)(u)",
						"homology_map(P'', p, n + 1, left_coset(P.add, u, boundaries(P, n + 1))) = "+
							"left_coset(P''.add, p(n + 1)(u), boundaries(P'', n + 1))",
						By(HomologyMapCoset.Read(middle), quotient, pChainMap, tClass[1]))
					zClass := b.Have(
						"the class of p(n + 1)(u) is a class of P'' at n + 1",
						"left_coset(P''.add, p(n + 1)(u), boundaries(P'', n + 1)) ∈ homology(P'', n + 1)",
						Simp(Fwd(InHomology.Read(quotient))),
						Derive(func(c *Argument) {
							c.Take(c.Term("p(n + 1)(u)"))
							c.Show(
								"the class of p(n + 1)(u) is the class of the cycle p(n + 1)(u)",
								By(zCycle))
						}))
					b.Show(
						"s is p*(t), t the class of u, so s is the class of p(n + 1)(u), which δ sends to the zero class",
						sMap[0].Rw(),
						tClass[0].Rw(),
						pClass.Rw(),
						classIs.Rw(),
						boundariesSub.Rw(),
						By(zClass, zeroClass))
				})
			a.Backward(
				"δ(s) being zero, a lift u of z has P.d(n + 1)(u) pull back to a "+
					"boundary P'.d(n + 1)(v), and p* sends the class of u − i(n + 1)(v) to s",
				func(b *Argument, sIn Fact) {
					kernel := b.Conjuncts(
						sIn,
						"s is a class of P'' at n + 1",
						"δ sends s to the zero class")
					z, sIs := b.ObtainAs[D](
						"s is the class of a cycle z",
						"∃z:D. s = left_coset(P''.add, z, boundaries(P'', n + 1)) ∧ z ∈ cycles(P'', n + 1)",
						By(kernel[0], InHomology.Read(quotient)))
					sClass := b.Conjuncts(
						sIs,
						"s is the class of z",
						"z is a cycle of P''")
					zKernel := b.Have(
						"above degree 0 a cycle lies in the kernel: z lies in P''.terms(n + 1) and P''.d(n + 1) kills it",
						"z ∈ group_kernel(P''.zero, P''.terms(n + 1), P''.d(n + 1))",
						Simp(Rev(CyclesKernel)),
						By(sClass[1]))
					u, uIs := b.ObtainAs[C](
						"z lifts to a u of P.terms(n + 1), p(n + 1) being onto",
						"∃u:C. u ∈ P.terms(n + 1) ∧ p(n + 1)(u) = z",
						ByChase(Depth(1), middleModules, quotientModules, pHoms, exact, zKernel))
					lift := b.Conjuncts(
						uIs,
						"u lies in P.terms(n + 1)",
						"u lifts z")
					w, wIs := b.ObtainAs[B](
						"p(n) kills P.d(n + 1)(u), as p(n)(P.d(n + 1)(u)) = P''.d(n "+
							"+ 1)(z), so P.d(n + 1)(u) is i(n)(w) for a w of P'.terms(n)",
						"∃w:B. w ∈ P'.terms(n) ∧ i(n)(w) = P.d(n + 1)(u)",
						ByChase(
							Depth(1),
							subModules,
							middleModules,
							quotientModules,
							middleBoundaryHoms,
							quotientBoundaryHoms,
							iHoms,
							pHoms,
							pSquare,
							exact,
							zKernel,
							uIs))
					pull := b.Conjuncts(
						wIs,
						"w lies in P'.terms(n)",
						"w pulls back P.d(n + 1)(u)")
					classIs := b.Have(
						"δ sends the class of z to the class of w",
						"connecting_hom(P', P, i, p, n, left_coset(P''.add, z, boundaries(P'', n + 1))) = "+
							"left_coset(P'.add, w, boundaries(P', n))",
						By(ConnectingHomCoset.Read(S).At(n, z, u, w), sClass[1], lift[0], lift[1], pull[0], pull[1]))
					wZero := b.Have(
						"so the class of w is the zero class, the class of P'.zero",
						"left_coset(P'.add, w, image(P'.d(n + 1), P'.terms(n + 1))) = "+
							"left_coset(P'.add, P'.zero, image(P'.d(n + 1), P'.terms(n + 1)))",
						CalcEq(
							Leg(
								b.TermAs[Set[B]]("connecting_hom(P', P, i, p, n, s)"),
								"the class of w is δ(s), s being the class of z",
								boundariesSub.RwRev(),
								sClass[0].Rw(),
								By(classIs)),
							Leg(
								b.TermAs[Set[B]]("image(P'.d(n + 1), P'.terms(n + 1))"),
								"which is the zero class",
								boundariesSub.RwRev(),
								By(kernel[1])),
							FinalLeg(
								"the class of P'.zero",
								By(zeroClass)),
						))
					_, vIs := b.ObtainAs[B](
						"so w is a boundary P'.d(n + 1)(v)",
						"∃v:B. v ∈ P'.terms(n + 1) ∧ w = P'.d(n + 1)(v)",
						ByChase(Depth(0), subModules, subBoundaryHoms, images, pull[0], wZero))
					xIs := b.Let("x", b.Term("P.add(u, P.neg(i(n + 1)(v)))"))
					xCycle := b.Have(
						"x is a cycle: P.d(n + 1)(x) = i(n)(w) − P.d(n + 1)(i(n + "+
							"1)(v)) = i(n)(w) − i(n)(P'.d(n + 1)(v)) = P.zero, by the square",
						"x ∈ cycles(P, n + 1)",
						Simp(Fwd(CyclesKernel)),
						ByChase(
							Depth(0),
							subModules,
							middleModules,
							subBoundaryHoms,
							middleBoundaryHoms,
							iHoms,
							iSquare,
							uIs,
							pull[1],
							vIs,
							xIs))
					xLifts := b.Have(
						"p(n + 1) carries x to z, as p(n + 1) kills i(n + 1)(v) by exactness",
						"p(n + 1)(x) = z",
						ByChase(Depth(0), subModules, middleModules, quotientModules, iHoms, pHoms, exact, uIs, vIs, xIs))
					xClass := b.Have(
						"the class of x is a class of P at n + 1",
						"left_coset(P.add, x, boundaries(P, n + 1)) ∈ homology(P, n + 1)",
						Simp(Fwd(InHomology.Read(middle))),
						Derive(func(c *Argument) {
							c.Take(c.Term("x"))
							c.Show(
								"the class of x is the class of the cycle x",
								By(xCycle))
						}))
					xMaps := b.Have(
						"p* sends the class of x to the class of p(n + 1)(x)",
						"homology_map(P'', p, n + 1, left_coset(P.add, x, boundaries(P, n + 1))) = "+
							"left_coset(P''.add, p(n + 1)(x), boundaries(P'', n + 1))",
						By(HomologyMapCoset.Read(middle), quotient, pChainMap, xCycle))
					b.Do(Simp(Fwd(set_basic.InImage.Inst(TypeBinder.BindA[Set[C]](), TypeBinder.BindB[Set[D]]()))))
					b.Take(b.Term("left_coset(P.add, x, boundaries(P, n + 1))"))
					b.Show(
						"s, the class of z, is p* of the class of x",
						xMaps.Rw(),
						xLifts.Rw(),
						By(sClass[0], xClass))
				})
		}),
})}

// LongExactSub — CycleLiftPullback supplies a lift u of a quotient
// cycle z and a cycle w pulling back its boundary. The connecting map
// sends the class of z to the class of w, and i* sends that class to
// the class of i(n)(w) = P.d(n + 1)(u), a boundary, hence the zero class.
// Conversely, if i* kills the class of a cycle w, then i(n)(w) is a
// boundary P.d(n + 1)(u). The square and exactness make p(n + 1)(u) a
// quotient cycle whose class the connecting map sends to the class of w.
var LongExactSub = longExactSubThm{family.Add(registry.ProofEntry{
	Name: "LongExactSub",
	Key:  "prop_bbadc70ff0497d8e",
	Build: ShortExactComplexes.Law("∀n:num. "+
		"    exact_at(boundaries(P, n), "+
		"        homology(P'', n + 1), "+
		"        homology(P', n), "+
		"        connecting_hom(P', P, i, p, n), "+
		"        homology_map(P, i, n))",
		func(a *Argument, S ShortExactComplexesFact[on.R], n *Expr[Nat]) {
			parts := []Fact{
				Read(ShortExactSubComplex, S),
				Read(ShortExactMiddleComplex, S),
				Read(ShortExactQuotientComplex, S),
				Read(ShortExactInclusionMap, S),
				Read(ShortExactProjectionMap, S),
				Read(ShortExactDegreewise, S),
			}
			sub, middle, quotient, iChainMap := parts[0], parts[1], parts[2], parts[3]
			iHoms := Read(ChainMapHom, parts[3])
			pClauses := []Fact{Read(ChainMapHom, parts[4]), Read(ChainMapSquare, parts[4])}
			pHoms, pSquare := pClauses[0], pClauses[1]
			exact := a.Unfolded(parts[5], ExactComplexesDef)
			subModules, middleModules, quotientModules :=
				ComplexModules.Read(sub), ComplexModules.Read(middle), ComplexModules.Read(quotient)
			middleBoundaryHoms, quotientBoundaryHoms :=
				ComplexBoundaryHom.Read(middle), ComplexBoundaryHom.Read(quotient)

			// The zero class of H(n)(P): the boundaries B, the image of P.d(n + 1), and the class of P.zero.
			boundariesP := a.Have(
				"the boundaries of P at n are the image of P.d(n + 1)",
				"boundaries(P, n) = image(P.d(n + 1), P.terms(n + 1))",
				By(BoundariesDef))
			images := a.Have(
				"the image of P.d(n + 1) is a submodule of P.terms(n)",
				"submodule(R, complex_module(P, n), image(P.d(n + 1), P.terms(n + 1)))",
				boundariesP.RwRev(),
				By(BoundariesSubmodule.Read(middle).At(n)))
			subgroup := a.Simplified(
				submodule.SubmoduleSubgroup.Read(images),
				Fwd(module_record.ModuleAdditiveGroupDef))
			moduleAtN := a.Have(
				"P.terms(n) is a module",
				"module_on(R, complex_module(P, n))",
				By(middleModules))
			groupAtN := a.Simplified(
				module.AddGroupOn.Read(moduleAtN),
				Fwd(module_record.ModuleAdditiveGroupDef))
			zeroClass := a.Have(
				"so the image of P.d(n + 1) is the class of P.zero, "+
					"the identity of the additive group of P.terms(n)",
				"left_coset(P.add, P.zero, image(P.d(n + 1), P.terms(n + 1))) = image(P.d(n + 1), P.terms(n + 1))",
				By(group.LeftCosetOneOn.Read(groupAtN), group.SubgroupSubset, subgroup))

			// The two sets of classes of P', a class s at a time: s is in the image of δ, or s is a class that i* sends to the zero class.
			a.Do(Simp(
				Fwd(module_homomorphism.ExactAtDef),
				Fwd(set_basic.Extension.Inst[Set[B]]()),
				Fwd(group_homomorphism.InKernel)))
			a.FixAs[Set[B]]("s")
			a.Iff()
			a.Forward(
				"δ sends the class of a cycle z to the class of a pull-back w of "+
					"P.d(n + 1)(u), u a lift of z, and i* sends that to the zero class",
				func(b *Argument, sIn Fact) {
					_, sIs := b.Obtain(
						"s is δ(t) for a class t of P'' at n + 1",
						"∃t:set(D). s = connecting_hom(P', P, i, p, n, t) ∧ t ∈ homology(P'', n + 1)",
						By(sIn, set_basic.InImage.Inst(TypeBinder.BindA[Set[D]](), TypeBinder.BindB[Set[B]]())))
					sDelta := b.Conjuncts(
						sIs,
						"s is δ(t)",
						"t is a class of P'' at n + 1")
					z, tIs := b.ObtainAs[D](
						"t is the class of a cycle z",
						"∃z:D. t = left_coset(P''.add, z, boundaries(P'', n + 1)) ∧ z ∈ cycles(P'', n + 1)",
						By(sDelta[1], InHomology.Read(quotient)))
					tClass := b.Conjuncts(
						tIs,
						"t is the class of z",
						"z is a cycle of P''")
					u, w, realized := b.Obtain2As[C, B](
						"lift z and pull its boundary back to a cycle w",
						"∃u:C. ∃w:B. "+
							"    u ∈ P.terms(n + 1) ∧ "+
							"    p(n + 1)(u) = z ∧ "+
							"    w ∈ P'.terms(n) ∧ "+
							"    i(n)(w) = P.d(n + 1)(u) ∧ "+
							"    w ∈ cycles(P', n)",
						By(tClass[1], Read(CycleLiftPullback, S).At(n, z)))
					r := b.Conjuncts(
						realized,
						"u lies in P.terms(n + 1)",
						"u lifts z",
						"w lies in P'.terms(n)",
						"w pulls back P.d(n + 1)(u)",
						"w is a cycle of P'")
					uIn, uLifts, wIn, wPulls, wCycle := r[0], r[1], r[2], r[3], r[4]
					classIs := b.Have(
						"δ sends the class of z to the class of w",
						"connecting_hom(P', P, i, p, n, left_coset(P''.add, z, boundaries(P'', n + 1))) = "+
							"left_coset(P'.add, w, boundaries(P', n))",
						By(ConnectingHomCoset.Read(S).At(n, z, u, w), tClass[1], uIn, uLifts, wIn, wPulls))
					wClass := b.Have(
						"so the class of w is a class of P'",
						"left_coset(P'.add, w, boundaries(P', n)) ∈ homology(P', n)",
						Simp(Fwd(InHomology.Read(sub))),
						Derive(func(c *Argument) {
							c.Take(w)
							c.Show(
								"the class of w is the class of the cycle w",
								By(wCycle))
						}))
					wZero := b.Have(
						"and i* sends it to the zero class",
						"homology_map(P, i, n, left_coset(P'.add, w, boundaries(P', n))) = boundaries(P, n)",
						CalcEq(
							Leg(
								b.TermAs[Set[C]]("left_coset(P.add, i(n)(w), boundaries(P, n))"),
								"i* sends the class of w to the class of i(n)(w)",
								By(
									Read(HomologyMapCoset, sub, middle).At(b.TermAs[Fun2[Nat, B, C]]("i"), n, w),
									iChainMap,
									wCycle)),
							Leg(
								b.TermAs[Set[C]]("left_coset(P.add, P.zero, image(P.d(n + 1), P.terms(n + 1)))"),
								"i(n)(w) = P.d(n + 1)(u) is a boundary, so its class is the class of P.zero",
								boundariesP.Rw(),
								ByChase(Depth(0), middleModules, middleBoundaryHoms, images, uIn, wPulls)),
							FinalLeg(
								"which is the zero class",
								boundariesP.Rw(),
								By(zeroClass)),
						))
					b.Show(
						"s is δ(t), t the class of z, so s is the class of w",
						sDelta[0].Rw(),
						tClass[0].Rw(),
						classIs.Rw(),
						By(wClass, wZero))
				})
			a.Backward(
				"a class of a cycle w that i* sends to the zero class has i(n)(w) = "+
					"P.d(n + 1)(u), and δ sends the class of the cycle p(n + 1)(u) to it",
				func(b *Argument, sIn Fact) {
					kernel := b.Conjuncts(
						sIn,
						"s is a class of P' at n",
						"i* sends s to the zero class")
					w, sIs := b.ObtainAs[B](
						"s is the class of a cycle w",
						"∃w:B. s = left_coset(P'.add, w, boundaries(P', n)) ∧ w ∈ cycles(P', n)",
						By(kernel[0], InHomology.Read(sub)))
					sClass := b.Conjuncts(
						sIs,
						"s is the class of w",
						"w is a cycle of P'")
					Pʹ := b.TermAs[ComplexOps[A, B]]("P'")
					wIn := b.Have(
						"w lies in P'.terms(n)",
						"w ∈ P'.terms(n)",
						BySets(sClass[1], CyclesSubsetTerms.At(Pʹ, n)))
					wZero := b.Have(
						"so the class of i(n)(w) is the zero class, the class of P.zero",
						"left_coset(P.add, i(n)(w), image(P.d(n + 1), P.terms(n + 1))) = "+
							"left_coset(P.add, P.zero, image(P.d(n + 1), P.terms(n + 1)))",
						CalcEq(
							Leg(
								b.TermAs[Set[C]]("homology_map(P, i, n, s)"),
								"the class of i(n)(w) is i*(s), s being the class of w",
								boundariesP.RwRev(),
								sClass[0].Rw(),
								By(
									Read(HomologyMapCoset, sub, middle).At(b.TermAs[Fun2[Nat, B, C]]("i"), n, w),
									iChainMap,
									sClass[1])),
							Leg(
								b.TermAs[Set[C]]("image(P.d(n + 1), P.terms(n + 1))"),
								"which is the zero class",
								boundariesP.RwRev(),
								By(kernel[1])),
							FinalLeg(
								"the class of P.zero",
								By(zeroClass)),
						))
					u, uIs := b.ObtainAs[C](
						"so i(n)(w) is a boundary P.d(n + 1)(u)",
						"∃u:C. u ∈ P.terms(n + 1) ∧ i(n)(w) = P.d(n + 1)(u)",
						ByChase(Depth(0), subModules, middleModules, middleBoundaryHoms, iHoms, images, wIn, wZero))
					lift := b.Conjuncts(
						uIs,
						"u lies in P.terms(n + 1)",
						"i(n)(w) = P.d(n + 1)(u)")
					z, zIs := b.LetAs[D]("z", "p(n + 1)(u)")
					zCycle := b.Have(
						"z is a cycle of P'': P''.d(n + 1)(z) = p(n)(P.d(n + 1)(u)) = p(n)(i(n)(w)), zero by exactness",
						"z ∈ cycles(P'', n + 1)",
						Simp(Fwd(CyclesKernel)),
						ByChase(
							Depth(0),
							subModules,
							middleModules,
							quotientModules,
							quotientBoundaryHoms,
							iHoms,
							pHoms,
							pSquare,
							exact,
							wIn,
							uIs,
							zIs))
					classIs := b.Have(
						"δ sends the class of z to the class of w",
						"connecting_hom(P', P, i, p, n, left_coset(P''.add, z, boundaries(P'', n + 1))) = "+
							"left_coset(P'.add, w, boundaries(P', n))",
						By(ConnectingHomCoset.Read(S).At(n, z, u, w), zCycle, lift[0], zIs, wIn, lift[1]))
					zClass := b.Have(
						"the class of z is a class of P'' at n + 1",
						"left_coset(P''.add, z, boundaries(P'', n + 1)) ∈ homology(P'', n + 1)",
						Simp(Fwd(InHomology.Read(quotient))),
						Derive(func(c *Argument) {
							c.Take(z)
							c.Show(
								"the class of z is the class of the cycle z",
								By(zCycle))
						}))
					b.Do(Simp(Fwd(set_basic.InImage.Inst(TypeBinder.BindA[Set[D]](), TypeBinder.BindB[Set[B]]()))))
					b.Take(b.Term("left_coset(P''.add, z, boundaries(P'', n + 1))"))
					b.Show(
						"s, the class of w, is δ of the class of z",
						classIs.Rw(),
						By(sClass[0], zClass))
				})
		}),
})}

// ---------------------------------------------------------------------------
// The five lemma
// ---------------------------------------------------------------------------

func onto(n string) string { return "image(f(" + n + "), P.terms(" + n + ")) = Q.terms(" + n + ")" }

// FourLemmaInjective — the four lemma, injective half: the exactness of P
// at 2 and of Q at 3, every cycle a boundary, read as the kernel of one
// boundary map equal to the image of the next, and then one chase of
// three pull-backs. For u, v of P.terms(2) with f(2)(u) = f(2)(v), put
// w = u − v: f(1)(P.d(2)(w)) = Q.d(2)(f(2)(w)) is zero and f(1) is
// one-to-one, so P.d(2)(w) is zero and w = P.d(3)(a) by exactness of P at 2;
// Q.d(3)(f(3)(a)) = f(2)(P.d(3)(a)) is zero, so f(3)(a) = Q.d(4)(b') by
// exactness of Q at 3, and b' = f(4)(b) since f(4) is onto;
// f(3)(P.d(4)(b)) = Q.d(4)(f(4)(b)) = f(3)(a) and f(3) is one-to-one, so
// a = P.d(4)(b), whence w = P.d(3)(P.d(4)(b)) = P.zero.
var FourLemmaInjective = fourLemmaInjectiveThm{family.Add(registry.ProofEntry{
	Name: "FourLemmaInjective",
	Key:  "prop_1bc803d06590b5cf",
	Build: ChainComplex.Law(Statement{
		Binders: "∀Q:complex_ops(A, C). ∀f:(num → B → C).",
		Hypotheses: []string{
			"chain_complex(R, Q)",
			"chain_map(P, Q, f)",
			"cycles(P, 2) = boundaries(P, 2)",
			"cycles(Q, 3) = boundaries(Q, 3)",
			"image(f(4), P.terms(4)) = Q.terms(4)",
			"injective_on(P.terms(3), f(3))",
			"injective_on(P.terms(1), f(1))",
		},
		Conclusion: "injective_on(P.terms(2), f(2))",
	},
		func(a *Argument, complexP Fact, complexQ ChainComplexFact[on.R], _ *Arrow2[Nat, B, C], hyps Fact) {
			given := a.Conjuncts(
				hyps,
				"f is a chain map",
				"P is exact at degree 2",
				"Q is exact at degree 3",
				"f(4) maps P.terms(4) onto Q.terms(4)",
				"f(3) is one-to-one on P.terms(3)",
				"f(1) is one-to-one on P.terms(1)")
			exactP2, exactQ3 := given[1], given[2]
			onto4, oneToOne3, oneToOne1 := given[3], given[4], given[5]
			clauses := []Fact{Read(ChainMapHom, given[0]), Read(ChainMapSquare, given[0])}
			homs, square := clauses[0], clauses[1]
			P := a.TermAs[ComplexOps[A, B]]("P")
			Q := a.TermAs[ComplexOps[A, C]]("Q")
			degree1, degree2, degree3 := a.Ctx().Nat(1), a.Ctx().Nat(2), a.Ctx().Nat(3)
			kernelP2 := a.Have(
				"so the kernel of P.d(2) is the image of P.d(3), the "+
					"cycles read at 1 + 1 and the boundaries' image at 2 + 1",
				"group_kernel(P.zero, P.terms(2), P.d(2)) = image(P.d(3), P.terms(3))",
				ByArith(exactP2, CyclesKernel.At(P, degree1), BoundariesDef.At(P, degree2)))
			kernelQ3 := a.Have(
				"and the kernel of Q.d(3) the image of Q.d(4), at 2 + 1 and 3 + 1",
				"group_kernel(Q.zero, Q.terms(3), Q.d(3)) = image(Q.d(4), Q.terms(4))",
				ByArith(exactQ3, CyclesKernel.At(Q, degree2), BoundariesDef.At(Q, degree3)))
			a.Show(
				"f(2) is one-to-one: P.d(2) kills u − v, so u − v = P.d(3)(a); f(3)(a) "+
					"= Q.d(4)(b') with b' = f(4)(b), so a = P.d(4)(b) and u − v = P.zero",
				ByChase(
					Depth(3),
					ComplexModules.Read(complexP),
					ComplexModules.Read(complexQ),
					ComplexBoundaryHom.Read(complexP),
					ComplexBoundaryHom.Read(complexQ),
					ComplexBoundaryTwice.Read(complexP),
					homs,
					square,
					kernelP2,
					kernelQ3,
					onto4,
					oneToOne3,
					oneToOne1))
		}),
})}

// FourLemmaSurjective — the four lemma, surjective half: the exactness
// of P at 1 and of Q at 2 read as the kernel of one boundary map equal to
// the image of the next, as in the injective half, and then one chase;
// the argument needs no exactness of P at 2 or of Q at 1, Q being a
// complex. f(2) carries P.terms(2) into Q.terms(2); for z of Q.terms(2), Q.d(2)(z) = f(1)(t)
// for a t of P.terms(1), f(1) being onto; f(0)(P.d(1)(t)) = Q.d(1)(f(1)(t)) =
// Q.d(1)(Q.d(2)(z)) is zero and f(0) is one-to-one, so P.d(1)(t) is zero and
// t = P.d(2)(x) by exactness of P at 1; Q.d(2)(z − f(2)(x)) =
// f(1)(t) − f(1)(P.d(2)(x)) is zero, so z − f(2)(x) = Q.d(3)(y') by exactness
// of Q at 2, y' = f(3)(y) since f(3) is onto, and
// z = f(2)(x) + Q.d(3)(f(3)(y)) = f(2)(x + P.d(3)(y)).
var FourLemmaSurjective = fourLemmaSurjectiveThm{family.Add(registry.ProofEntry{
	Name: "FourLemmaSurjective",
	Key:  "prop_14962c7d17265e3",
	Build: ChainComplex.Law(Statement{
		Binders: "∀Q:complex_ops(A, C). ∀f:(num → B → C).",
		Hypotheses: []string{
			"chain_complex(R, Q)",
			"chain_map(P, Q, f)",
			"cycles(P, 1) = boundaries(P, 1)",
			"cycles(Q, 2) = boundaries(Q, 2)",
			"image(f(3), P.terms(3)) = Q.terms(3)",
			"image(f(1), P.terms(1)) = Q.terms(1)",
			"injective_on(P.terms(0), f(0))",
		},
		Conclusion: "image(f(2), P.terms(2)) = Q.terms(2)",
	},
		func(a *Argument, complexP Fact, complexQ ChainComplexFact[on.R], _ *Arrow2[Nat, B, C], hyps Fact) {
			given := a.Conjuncts(
				hyps,
				"f is a chain map",
				"P is exact at degree 1",
				"Q is exact at degree 2",
				"f(3) maps P.terms(3) onto Q.terms(3)",
				"f(1) maps P.terms(1) onto Q.terms(1)",
				"f(0) is one-to-one on P.terms(0)")
			exactP1, exactQ2 := given[1], given[2]
			onto3, onto1, oneToOne0 := given[3], given[4], given[5]
			clauses := []Fact{Read(ChainMapHom, given[0]), Read(ChainMapSquare, given[0])}
			homs, square := clauses[0], clauses[1]
			P := a.TermAs[ComplexOps[A, B]]("P")
			Q := a.TermAs[ComplexOps[A, C]]("Q")
			degree0, degree1, degree2 := a.Ctx().Nat(0), a.Ctx().Nat(1), a.Ctx().Nat(2)
			kernelP1 := a.Have(
				"so the kernel of P.d(1) is the image of P.d(2), the "+
					"cycles read at 0 + 1 and the boundaries' image at 1 + 1",
				"group_kernel(P.zero, P.terms(1), P.d(1)) = image(P.d(2), P.terms(2))",
				ByArith(exactP1, CyclesKernel.At(P, degree0), BoundariesDef.At(P, degree1)))
			kernelQ2 := a.Have(
				"and the kernel of Q.d(2) the image of Q.d(3), at 1 + 1 and 2 + 1",
				"group_kernel(Q.zero, Q.terms(2), Q.d(2)) = image(Q.d(3), Q.terms(3))",
				ByArith(exactQ2, CyclesKernel.At(Q, degree1), BoundariesDef.At(Q, degree2)))
			a.Show(
				"f(2) is onto: Q.d(2)(z) = f(1)(t), t = P.d(2)(x), z − f(2)(x) "+
					"= Q.d(3)(y') with y' = f(3)(y), so z = f(2)(x + P.d(3)(y))",
				ByChase(
					Depth(3),
					ComplexModules.Read(complexP),
					ComplexModules.Read(complexQ),
					ComplexBoundaryHom.Read(complexP),
					ComplexBoundaryHom.Read(complexQ),
					ComplexBoundaryTwice.Read(complexQ),
					homs,
					square,
					kernelP1,
					kernelQ2,
					onto3,
					onto1,
					oneToOne0))
		}),
})}

// FiveLemma — f(2) is a homomorphism, being a component of the chain
// map; it is one-to-one by the four lemma's injective half and onto by
// its surjective half, f(3) and f(1) being one-to-one and onto as
// isomorphisms.
var FiveLemma = fiveLemmaThm{family.Add(registry.ProofEntry{
	Name: "FiveLemma",
	Key:  "prop_772bf5bbb6819e95",
	Build: ChainComplex.Law(Statement{
		Binders: "∀Q:complex_ops(A, C). ∀f:(num → B → C).",
		Hypotheses: []string{
			"chain_complex(R, Q)",
			"chain_map(P, Q, f)",
			"cycles(P, 2) = boundaries(P, 2)",
			"cycles(P, 1) = boundaries(P, 1)",
			"cycles(Q, 3) = boundaries(Q, 3)",
			"cycles(Q, 2) = boundaries(Q, 2)",
			"image(f(4), P.terms(4)) = Q.terms(4)",
			"injective_on(P.terms(0), f(0))",
			"module_isomorphism(R, complex_module(P, 3), complex_module(Q, 3), f(3))",
			"module_isomorphism(R, complex_module(P, 1), complex_module(Q, 1), f(1))",
		},
		Conclusion: "module_isomorphism(R, complex_module(P, 2), complex_module(Q, 2), f(2))",
	},
		func(a *Argument, complexP Fact, complexQ ChainComplexFact[on.R], f *Arrow2[Nat, B, C], hyps Fact) {
			given := a.Conjuncts(
				hyps,
				"f is a chain map",
				"P is exact at degree 2",
				"P is exact at degree 1",
				"Q is exact at degree 3",
				"Q is exact at degree 2",
				"f(4) maps P.terms(4) onto Q.terms(4)",
				"f(0) is one-to-one on P.terms(0)",
				"f(3) is an isomorphism of P.terms(3) onto Q.terms(3)",
				"f(1) is an isomorphism of P.terms(1) onto Q.terms(1)")
			isChainMap := given[0]
			exactP2, exactP1, exactQ3, exactQ2 := given[1], given[2], given[3], given[4]
			onto4, oneToOne0 := given[5], given[6]
			iso3 := a.Conjuncts(
				a.Unfolded(given[7], module_homomorphism.ModuleIsomorphismDef),
				"f(3) is a homomorphism from P.terms(3) to Q.terms(3)",
				"f(3) is one-to-one on P.terms(3)",
				"f(3) maps P.terms(3) onto Q.terms(3)")
			iso1 := a.Conjuncts(
				a.Unfolded(given[8], module_homomorphism.ModuleIsomorphismDef),
				"f(1) is a homomorphism from P.terms(1) to Q.terms(1)",
				"f(1) is one-to-one on P.terms(1)",
				"f(1) maps P.terms(1) onto Q.terms(1)")
			homs := Read(ChainMapHom, isChainMap)
			oneToOne2 := a.Have(
				"f(2) is one-to-one on P.terms(2), by the injective half",
				"injective_on(P.terms(2), f(2))",
				By(
					Read(FourLemmaInjective, complexP, complexQ).At(f),
					isChainMap,
					exactP2,
					exactQ3,
					onto4,
					iso3[1],
					iso1[1]))
			onto2 := a.Have(
				"and maps P.terms(2) onto Q.terms(2), by the surjective half",
				"image(f(2), P.terms(2)) = Q.terms(2)",
				By(
					Read(FourLemmaSurjective, complexP, complexQ).At(f),
					isChainMap,
					exactP1,
					exactQ2,
					iso3[2],
					iso1[2],
					oneToOne0))
			a.Show(
				"so f(2), a homomorphism, is an isomorphism of P.terms(2) onto Q.terms(2)",
				By(module_homomorphism.ModuleIsomorphismDef, homs, oneToOne2, onto2))
		}),
})}
