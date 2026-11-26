// Cochain complexes of modules, their cohomology and the long exact sequence.

package chain_complex

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// ---------------------------------------------------------------------------
// Cochain complexes, cochain maps and their cohomology
// ---------------------------------------------------------------------------

// CochainComplex — `cochain_complex(R, Q)`: modules Q.terms(n) with
// coboundaries Q.d(n) to degree n+1, composing to zero.
var CochainComplex = cochainComplexThm{family.DefineStructure(registry.DefEntry{
	Name: "CochainComplex", Const: "cochain_complex", Type: "ring_ops(A) → complex_ops(A, B) → bool",
	Key:     "prop_63a3120d3a636d46",
	Subject: "Q",
	Equations: []string{
		"∀R:ring_ops(A). ∀Q:complex_ops(A, B). " +
			"    cochain_complex(R, Q) ⇔ " +
			"    (∀n:num. module_on(R, complex_module(Q, n))) ∧ " +
			"    (∀n:num. module_homomorphism(R, complex_module(Q, n), complex_module(Q, n + 1), Q.d(n))) ∧ " +
			"    (∀n:num. ∀u:B. u ∈ Q.terms(n) ⇒ Q.d(n + 1)(Q.d(n)(u)) = Q.zero)",
	},
	Deps: []registry.EntryLike{ComplexModuleDef, ComplexDifferentialDef},
})}

// CochainModules — every term is a module.
var CochainModules = cochainModulesThm{family.Add(registry.ProofEntry{
	Name:  "CochainModules",
	Key:   "prop_87ad06c019c14b0b",
	Build: CochainComplex.Axiom("∀n:num. module_on(R, complex_module(Q, n))"),
})}

// CochainCoboundaryHom — every coboundary map is a homomorphism.
var CochainCoboundaryHom = cochainCoboundaryHomThm{family.Add(registry.ProofEntry{
	Name: "CochainCoboundaryHom",
	Key:  "prop_afd3bcb48eef390a",
	Build: CochainComplex.Axiom(
		"∀n:num. module_homomorphism(R, complex_module(Q, n), complex_module(Q, n + 1), Q.d(n))"),
})}

// CochainCoboundaryTwice — two coboundaries in a row are zero.
var CochainCoboundaryTwice = cochainCoboundaryTwiceThm{family.Add(registry.ProofEntry{
	Name: "CochainCoboundaryTwice",
	Key:  "prop_b8521afbd8f41276",
	Build: CochainComplex.Axiom(Statement{
		Binders: "∀n:num. ∀u:B.",
		Hypotheses: []string{
			"u ∈ Q.terms(n)",
		},
		Conclusion: "Q.d(n + 1)(Q.d(n)(u)) = Q.zero",
	}),
})}

// CocyclesDef — `cocycles(Q, n)`, the complex record Q: the members
// of Q.terms(n) that Q.d(n) kills.
var CocyclesDef = cocyclesDefThm{family.Define(registry.DefEntry{
	Name: "CocyclesDef", Const: "cocycles", Type: "complex_ops(A, B) → num → set(B)",
	Key: "prop_1c388dc9582f8b34",

	Equations: []string{
		"∀Q:complex_ops(A, B). ∀n:num. cocycles(Q, n) = {u:B | u ∈ Q.terms(n) ∧ Q.d(n)(u) = Q.zero}",
	},
	Deps: []registry.EntryLike{
		ComplexAddDef,
		ComplexZeroDef,
		ComplexNegDef,
		ComplexSmulDef,
		ComplexTermsDef,
		ComplexDifferentialDef,
	},
})}

// CocyclesKernel — cocycles are the kernel of the differential at every degree.
var CocyclesKernel = cocyclesKernelThm{family.Add(registry.ProofEntry{
	Name: "CocyclesKernel",
	Key:  "prop_a74ee73a0bca2abd",
	Build: family.Theorem("∀Q:complex_ops(A, B). ∀n:num. "+
		"    cocycles(Q, n) = group_kernel(Q.zero, Q.terms(n), Q.d(n))",
		func(a *Argument, Q *Expr[ComplexOps[A, B]], n *Expr[Nat]) {
			a.Do(Simp(Fwd(CocyclesDef), Fwd(group_homomorphism.GroupKernelDef)), Refl())
		}),
})}

// CoboundariesDef — `coboundaries(Q, n)`: the image of Q.d(n−1), and
// {Q.zero} at degree 0.
var CoboundariesDef = coboundariesDefThm{family.Define(registry.DefEntry{
	Name: "CoboundariesDef", Const: "coboundaries", Type: "complex_ops(A, B) → num → set(B)",
	Key: "prop_8a0bd8a6c63b533b",

	Equations: []string{
		"∀Q:complex_ops(A, B). ∀n:num. " +
			"    coboundaries(Q, n) = COND(n = 0, {Q.zero}, image(Q.d(n - 1), Q.terms(n - 1)))",
	},
	Deps: []registry.EntryLike{
		ComplexAddDef,
		ComplexZeroDef,
		ComplexNegDef,
		ComplexSmulDef,
		ComplexTermsDef,
		ComplexDifferentialDef,
	},
})}

// CoboundariesSucc — a successor degree selects the preceding differential's image.
var CoboundariesSucc = coboundariesSuccThm{family.Add(registry.ProofEntry{
	Name: "CoboundariesSucc",
	Key:  "prop_55bac8bd0d70b1d0",
	Build: CochainComplex.Law("∀n:num. coboundaries(Q, n + 1) = image(Q.d(n), Q.terms(n))",
		func(a *Argument, complex CochainComplexFact[on.R], n *Expr[Nat]) {
			// The opened goal has the guard 0 = n + 1; normalized AddEqZero matches this orientation.
			a.Do(Simp(
				Fwd(CoboundariesDef),
				Fwd(nat_monus.AddSubCancel),
				Fwd(MakeFact(a.Ctx().DepNormalized(nat_arith.AddEqZero))),
				Fwd(nat_arith.OneNotZero)), Basic())
		}),
})}

// CocyclesSubmodule — the cocycles of every degree are a submodule of
// the degree's module: they are the kernel of the coboundary map Q.d(n),
// a homomorphism of the degree modules, and a kernel is a submodule of
// its source.
var CocyclesSubmodule = cocyclesSubmoduleThm{family.Add(registry.ProofEntry{
	Name: "CocyclesSubmodule",
	Key:  "prop_ec5d8d4d12a25537",
	Build: CochainComplex.Law("∀n:num. submodule(R, complex_module(Q, n), cocycles(Q, n))",
		func(a *Argument, complexQ CochainComplexFact[on.R], n *Expr[Nat]) {
			hom := a.Have(
				"the coboundary out of degree n is a homomorphism of the degree modules",
				"module_homomorphism(R, complex_module(Q, n), complex_module(Q, n + 1), Q.d(n))",
				By(CochainCoboundaryHom.Read(complexQ)))
			Q := a.TermAs[ComplexOps[A, B]]("Q")
			a.Show(
				"so its kernel, the cocycles of degree n, is a submodule of Q.terms(n)",
				By(module_homomorphism.KernelSubmodule.Read(hom), CocyclesKernel.At(Q, n)))
		}),
})}

// CoboundariesSubsetCocycles — every coboundary is a cocycle: at degree
// 0 the coboundaries are the zero alone, which Q.d(0) kills; at a degree
// m + 1 they are the image of Q.d(m), which Q.d(m + 1) kills, two
// coboundaries in a row being zero.
var CoboundariesSubsetCocycles = coboundariesSubsetCocyclesThm{family.Add(registry.ProofEntry{
	Name: "CoboundariesSubsetCocycles",
	Key:  "prop_b3a16237a56de5a2",
	Build: CochainComplex.Law("∀n:num. coboundaries(Q, n) ⊆ cocycles(Q, n)",
		func(a *Argument, complexQ CochainComplexFact[on.R], n *Expr[Nat]) {
			modules, coboundaryHoms := CochainModules.Read(complexQ), CochainCoboundaryHom.Read(complexQ)
			a.Cases(a.Term("n = 0"))
			a.When(
				"at degree 0 the coboundaries are the zero alone, which Q.d(0) kills",
				func(b *Argument, isZero Fact) {
					b.Do(isZero.Rw(), Unfold(CoboundariesDef), Simp(Fwd(set_order.SingSubset)), Unfold(CocyclesDef))
					zero := b.Have(
						"Q.zero lies in Q.terms(0) and Q.d(0) kills it",
						"Q.zero ∈ Q.terms(0) ∧ Q.d(0)(Q.zero) = Q.zero",
						ByChase(Depth(0), modules, coboundaryHoms))
					b.Show(
						"so the zero is a cocycle",
						BySets(zero))
				})
			a.Otherwise(
				"above degree 0 the coboundaries are the image of Q.d(m), which Q.d(m + 1) kills",
				func(b *Argument, positive Fact) {
					_, isSuc := b.ObtainAs[Nat](
						"a positive degree is a successor",
						"∃m:num. n = m + 1",
						By(positive, nat_arith.NonzeroIsSucc.At(n)))
					b.Do(isSuc.Rw(), Simp(Fwd(CoboundariesSucc.Read(complexQ)), Fwd(CocyclesDef)))
					killed := b.Have(
						"Q.d(m) carries Q.terms(m) into Q.terms(m + 1), and two coboundaries in a row are zero",
						"∀u:B. u ∈ Q.terms(m) ⇒ Q.d(m)(u) ∈ Q.terms(m + 1) ∧ Q.d(m + 1)(Q.d(m)(u)) = Q.zero",
						ByChase(Depth(0), modules, coboundaryHoms, CochainCoboundaryTwice.Read(complexQ)))
					b.Show(
						"so every coboundary is a cocycle",
						BySets(killed))
				})
		}),
})}

// CohomologyDef — `cohomology(Q, n)`: the cocycles modulo the
// coboundaries, as cosets.
var CohomologyDef = cohomologyDefThm{family.Define(registry.DefEntry{
	Name: "CohomologyDef", Const: "cohomology", Type: "complex_ops(A, B) → num → set(set(B))",
	Key: "prop_8e30a7ae7db80ca1",

	Equations: []string{
		"∀Q:complex_ops(A, B). ∀n:num. " +
			"    cohomology(Q, n) = left_cosets(Q.add, cocycles(Q, n), coboundaries(Q, n))",
	},
	Deps: []registry.EntryLike{
		ComplexAddDef,
		ComplexZeroDef,
		ComplexNegDef,
		ComplexSmulDef,
		ComplexTermsDef,
		ComplexDifferentialDef,
		CocyclesDef,
		CoboundariesDef,
	},
})}

// InCohomology — a cohomology class is the coset of a cocycle by the
// coboundaries, and the coset of every cocycle is a class: the cocycles
// are a submodule of Q.terms(n), so a module and a group under Q.add,
// and the coboundaries lie in them, so the cosets of the coboundaries by
// the cocycles are read off as the quotient group chapter reads them.
var InCohomology = inCohomologyThm{family.Add(registry.ProofEntry{
	Name: "InCohomology",
	Key:  "prop_b3006f79d9efbd16",
	Build: CochainComplex.Law("∀n:num. ∀s:set(B). "+
		"    s ∈ cohomology(Q, n) ⇔ "+
		"    ∃u:B. s = left_coset(Q.add, u, coboundaries(Q, n)) ∧ u ∈ cocycles(Q, n)",
		func(a *Argument, complexQ CochainComplexFact[on.R], n *Expr[Nat], s *Expr[Set[B]]) {
			moduleAtN := a.Have(
				"Q.terms(n) is a module",
				"module_on(R, complex_module(Q, n))",
				By(CochainModules.Read(complexQ)))
			cocyclesModule := a.Have(
				"the cocycles, a submodule of it, are a module",
				"module_on(R, restrict_module(complex_module(Q, n), cocycles(Q, n)))",
				By(submodule.SubmoduleModuleOn.Read(moduleAtN), CocyclesSubmodule.Read(complexQ)))
			// so the cocycles are a group under Q.add, the additive group of their module
			cocyclesGroup := a.Simplified(
				module.AddGroupOn.Read(cocyclesModule),
				Fwd(module_record.ModuleAdditiveGroupDef),
				Fwd(module_record.RestrictModuleDef),
				Fwd(ComplexModuleDef))
			a.Show(
				"the coboundaries lie in the cocycles, so a class, a "+
					"coset of them by a cocycle, is the coset of some cocycle",
				Unfold(CohomologyDef),
				By(quotient_group.InLeftCosets.Read(cocyclesGroup), CoboundariesSubsetCocycles.Read(complexQ)))
		}),
})}

// CohomologyModuleDef — the cocycles modulo the coboundaries, as a module record.
var CohomologyModuleDef = cohomologyModuleDefThm{family.Define(registry.DefEntry{
	Name: "CohomologyModuleDef", Const: "cohomology_module",
	Key:  "prop_2694963e101af19a",
	Type: "complex_ops(A, B) → num → module_ops(A, set(B))",
	Equations: []string{
		"∀Q:complex_ops(A, B). ∀n:num. " +
			"    cohomology_module(Q, n) = " +
			"    quotient_module(restrict_module(complex_module(Q, n), cocycles(Q, n)), coboundaries(Q, n))",
	},
	Deps: []registry.EntryLike{ComplexModuleDef, CocyclesDef, CoboundariesDef},
})}

// CochainMapDef — `cochain_map(Q, Q', f)`, the complex records: f(n):
// Q.terms(n) → Q'.terms(n) are homomorphisms commuting with the coboundaries.
var CochainMapDef = cochainMapDefThm{family.Define(registry.DefEntry{
	Name:     "CochainMapDef",
	Const:    "cochain_map",
	Type:     "ring_ops(A) → complex_ops(A, B) → complex_ops(A, C) → (num → B → C) → bool",
	Key:      "prop_21f4c92fe5dbe17c",
	Implicit: []string{"R"},
	Equations: []string{
		"∀R:ring_ops(A). ∀Q:complex_ops(A, B). ∀Q':complex_ops(A, C). ∀f:(num → B → C). " +
			"    cochain_map(R, Q, Q', f) ⇔ " +
			"    (∀n:num. module_homomorphism(R, complex_module(Q, n), complex_module(Q', n), f(n))) ∧ " +
			"    (∀n:num. ∀u:B. u ∈ Q.terms(n) ⇒ f(n + 1)(Q.d(n)(u)) = Q'.d(n)(f(n)(u)))",
	},
	Deps: []registry.EntryLike{
		ComplexAddDef,
		ComplexZeroDef,
		ComplexNegDef,
		ComplexSmulDef,
		ComplexTermsDef,
		ComplexDifferentialDef,
		ComplexModuleDef,
	},
})}

// CochainMapHom — every component is a module homomorphism.
var CochainMapHom = cochainMapHomThm{family.Add(registry.ProofEntry{
	Name: "CochainMapHom",
	Key:  "prop_8fdc0dd46b24f2bf",
	Build: CochainMapDef.Entry().Conjunct(
		"∀n:num. module_homomorphism(R, complex_module(Q, n), complex_module(Q', n), f(n))"),
})}

// CochainMapSquare — each differential square commutes on its source.
var CochainMapSquare = cochainMapSquareThm{family.Add(registry.ProofEntry{
	Name: "CochainMapSquare",
	Key:  "prop_2e8def84703537ce",
	Build: CochainMapDef.Entry().Conjunct(Statement{
		Binders: "∀n:num. ∀u:B.",
		Hypotheses: []string{
			"u ∈ Q.terms(n)",
		},
		Conclusion: "f(n + 1)(Q.d(n)(u)) = Q'.d(n)(f(n)(u))",
	}),
})}

// CochainMapIdentity — the identity of a cochain complex is a cochain map:
// each component is the identity of a module, and both sides of each
// square are the coboundary.
var CochainMapIdentity = cochainMapIdentityThm{family.Add(registry.ProofEntry{
	Name: "CochainMapIdentity",
	Key:  "prop_43f0b498834af054",
	Build: CochainComplex.Law("cochain_map(R, Q, Q, (λn:num. λx:B. x))",
		func(a *Argument, complexQ CochainComplexFact[on.R]) {
			a.Show(
				"each component is the identity of a module, and each square reads Q.d(n)(u) on both sides",
				Unfold(CochainMapDef),
				Unfold(module_homomorphism.ModuleHomomorphismDef),
				By(CochainModules.Read(complexQ)))
		}),
})}

// CochainMapCompose — cochain maps compose: each component of the
// composite is linear, and its square is f's square followed by g's.
var CochainMapCompose = cochainMapComposeThm{family.Add(registry.ProofEntry{
	Name: "CochainMapCompose",
	Key:  "prop_d0e6dbc54be26195",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀Q:complex_ops(A, B). " +
			"∀Q':complex_ops(A, C). " +
			"∀Q'':complex_ops(A, D). " +
			"∀f:(num → B → C). " +
			"∀g:(num → C → D).",
		Hypotheses: []string{
			"cochain_map(R, Q, Q', f)",
			"cochain_map(R, Q', Q'', g)",
		},
		Conclusion: "cochain_map(R, Q, Q'', λn:num. λx:B. g(n)(f(n)(x)))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			Q *Expr[ComplexOps[A, B]],
			Qʹ *Expr[ComplexOps[A, C]],
			Qʺ *Expr[ComplexOps[A, D]],
			f *Arrow2[Nat, B, C],
			g *Arrow2[Nat, C, D],
			maps Fact,
		) {
			given := a.Conjuncts(
				maps,
				"f is a cochain map",
				"g is a cochain map")
			cochainF, cochainG := given[0], given[1]
			linear := a.Have(
				"each component of the composite is linear",
				"∀n:num. module_homomorphism(R, complex_module(Q, n), complex_module(Q'', n), λx:B. g(n)(f(n)(x)))",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					composite := b.Have(
						"g(n) ∘ f(n) is linear",
						"module_homomorphism(R, complex_module(Q, n), complex_module(Q'', n), g(n) ∘ f(n))",
						By(
							module_homomorphism.HomCompose,
							CochainMapHom.Read(cochainF).At(n),
							CochainMapHom.Read(cochainG).At(n)))
					b.Show(
						"g(n) ∘ f(n) is λx. g(n)(f(n)(x)) read pointwise",
						composite.Simp(Fwd(functions.ComposeApply)),
						By(composite))
				}))
			squares := a.Have(
				"the composite commutes with the coboundaries",
				"∀n:num. ∀u:B. u ∈ Q.terms(n) ⇒ g(n + 1)(f(n + 1)(Q.d(n)(u))) = Q''.d(n)(g(n)(f(n)(u)))",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					u := b.FixAs[B]("u")
					inQ := b.Assume()
					linearF := b.Have(
						"f(n) is linear",
						"module_homomorphism(R, complex_module(Q, n), complex_module(Q', n), f(n))",
						By(CochainMapHom.Read(cochainF).At(n)))
					b.Show(
						"f's square at u, then g's at f(n)(u), which lies in Q'.terms(n)",
						By(
							CochainMapSquare.Read(cochainF).At(n, u),
							CochainMapSquare.Read(cochainG).At(n, b.TermAs[C]("f(n)(u)")),
							module_homomorphism.HomIn.Read(linearF).At(proof.MemberOf(u, inQ))))
				}))
			a.Show(
				"both clauses of a cochain map",
				By(CochainMapDef, linear, squares))
		}),
})}

// CochainHomotopyDef — `cochain_homotopy(Q, Q', f, g, h)`:
// h(n+1): Q.terms(n+1) → Q'.terms(n) with f − g = Q'.d ∘ h + h ∘ Q.d in every degree
// (and f − g = h ∘ Q.d at degree 0, where no coboundary comes in).
var CochainHomotopyDef = cochainHomotopyDefThm{family.Define(registry.DefEntry{
	Name:  "CochainHomotopyDef",
	Const: "cochain_homotopy",
	Type: "ring_ops(A) → " +
		"complex_ops(A, B) → " +
		"complex_ops(A, C) → " +
		"(num → B → C) → " +
		"(num → B → C) → " +
		"(num → B → C) → " +
		"bool",
	Key:      "prop_e8903bcbc0cce03",
	Implicit: []string{"R"},
	Equations: []string{
		"∀R:ring_ops(A). ∀Q:complex_ops(A, B). ∀Q':complex_ops(A, C). ∀f g h:(num → B → C). " +
			"    cochain_homotopy(R, Q, Q', f, g, h) ⇔ " +
			"    (∀n:num. " +
			"        module_homomorphism(R, complex_module(Q, n + 1), complex_module(Q', n), h(n + 1))) ∧ " +
			"    (∀n:num. ∀u:B. " +
			"        u ∈ Q.terms(n + 1) ⇒ " +
			"        Q'.add(f(n + 1)(u), Q'.neg(g(n + 1)(u))) = " +
			"        Q'.add(Q'.d(n)(h(n + 1)(u)), h(n + 2)(Q.d(n + 1)(u)))) ∧ " +
			"    (∀u:B. u ∈ Q.terms(0) ⇒ Q'.add(f(0)(u), Q'.neg(g(0)(u))) = h(1)(Q.d(0)(u)))",
	},
	Deps: []registry.EntryLike{
		ComplexAddDef,
		ComplexZeroDef,
		ComplexNegDef,
		ComplexSmulDef,
		ComplexTermsDef,
		ComplexDifferentialDef,
		ComplexModuleDef,
	},
})}

// CochainHomotopyEquivalenceDef — `cochain_homotopy_equivalence(R, Q, Q',
// f, g)`: f: Q → Q' and g: Q' → Q are cochain maps whose two composites,
// taken degree by degree, are each cochain homotopic to the identity. The
// inverse g is part of the data, as in chain_homotopy_equivalence.
var CochainHomotopyEquivalenceDef = cochainHomotopyEquivalenceDefThm{family.Define(registry.DefEntry{
	Name: "CochainHomotopyEquivalenceDef", Const: "cochain_homotopy_equivalence",
	Key: "prop_12d8d9f3eefbc32c",
	Type: "ring_ops(A) → " +
		"complex_ops(A, B) → " +
		"complex_ops(A, C) → " +
		"(num → B → C) → " +
		"(num → C → B) → " +
		"bool",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀Q:complex_ops(A, B). " +
			"∀Q':complex_ops(A, C). " +
			"∀f:(num → B → C). " +
			"∀g:(num → C → B). " +
			"    cochain_homotopy_equivalence(R, Q, Q', f, g) ⇔ " +
			"    cochain_map(R, Q, Q', f) ∧ " +
			"    cochain_map(R, Q', Q, g) ∧ " +
			"    (∃k:(num → B → B). " +
			"        cochain_homotopy(R, Q, Q, (λn:num. λx:B. g(n)(f(n)(x))), (λn:num. λx:B. x), k)) ∧ " +
			"    (∃l:(num → C → C). " +
			"        cochain_homotopy(R, Q', Q', (λn:num. λy:C. f(n)(g(n)(y))), (λn:num. λy:C. y), l))",
	},
	Deps: []registry.EntryLike{CochainMapDef, CochainHomotopyDef},
	Reading: "The mirror of chain_homotopy_equivalence: the homotopies are " +
		"existential and the inverse is an argument. No hypothesis makes Q or Q' a " +
		"cochain complex; the laws that read cohomology take cochain_complex beside it.",
})}

// CohomologyMapDef — `cohomology_map(Q, f, n, s)`, the target complex record Q: the image of a cohomology class under a cochain map, no
// representative chosen.
var CohomologyMapDef = cohomologyMapDefThm{family.Define(registry.DefEntry{
	Name:  "CohomologyMapDef",
	Const: "cohomology_map",
	Type:  "complex_ops(A, C) → (num → B → C) → num → set(B) → set(C)",
	Key:   "prop_145e6f0375809868",

	Equations: []string{
		"∀Q':complex_ops(A, C). ∀f:(num → B → C). ∀n:num. ∀s:set(B). " +
			"    cohomology_map(Q', f, n, s) = set_mul(Q'.add, image(f(n), s), coboundaries(Q', n))",
	},
	Deps: []registry.EntryLike{
		ComplexAddDef,
		ComplexZeroDef,
		ComplexNegDef,
		ComplexSmulDef,
		ComplexTermsDef,
		ComplexDifferentialDef,
		CoboundariesDef,
	},
})}

// CoconnectingHomDef — `coconnecting_hom(Q', Q, i, p, n, s)`:
// the connecting homomorphism from degree n cohomology of the quotient
// complex to degree n + 1 cohomology of Q': lift a member of the class
// through p, take its coboundary, pull it back
// through i, take the class.
var CoconnectingHomDef = coconnectingHomDefThm{family.Define(registry.DefEntry{
	Name:  "CoconnectingHomDef",
	Const: "coconnecting_hom",
	Type: "complex_ops(A, B) → " +
		"complex_ops(A, C) → " +
		"(num → B → C) → " +
		"(num → C → D) → " +
		"num → " +
		"set(D) → " +
		"set(B)",
	Key: "prop_f1ce5249aec893b6",

	Equations: []string{
		"∀Q':complex_ops(A, B). " +
			"∀Q:complex_ops(A, C). " +
			"∀i:(num → B → C). " +
			"∀p:(num → C → D). " +
			"∀n:num. " +
			"∀s:set(D). " +
			"    coconnecting_hom(Q', Q, i, p, n, s) = " +
			"    left_coset(Q'.add, " +
			"        εw:B. " +
			"            w ∈ Q'.terms(n + 1) ∧ " +
			"            (∃u:C. u ∈ Q.terms(n) ∧ p(n)(u) ∈ s ∧ i(n + 1)(w) = Q.d(n)(u)), " +
			"        coboundaries(Q', n + 1))",
	},
	Deps: []registry.EntryLike{
		ComplexAddDef,
		ComplexZeroDef,
		ComplexNegDef,
		ComplexSmulDef,
		ComplexTermsDef,
		ComplexDifferentialDef,
		CoboundariesDef,
	},
})}

// ShortExactCochainComplexes — a subcomplex, a middle complex and a
// quotient complex at three types over one ring, with inclusion i and
// projection p,
// exact in every degree; with no single subject, its laws fold under
// the letter S.
var ShortExactCochainComplexes = shortExactCochainComplexesThm{family.DefineStructure(registry.DefEntry{
	Name:  "ShortExactCochainComplexes",
	Const: "short_exact_cochain_complexes",
	Type: "ring_ops(A) → " +
		"complex_ops(A, B) → " +
		"complex_ops(A, C) → " +
		"complex_ops(A, D) → " +
		"(num → B → C) → " +
		"(num → C → D) → " +
		"bool",
	Key:    "prop_c9b5088db0e3293e",
	Letter: "S",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀Q':complex_ops(A, B). " +
			"∀Q:complex_ops(A, C). " +
			"∀Q'':complex_ops(A, D). " +
			"∀i:(num → B → C). " +
			"∀p:(num → C → D). " +
			"    short_exact_cochain_complexes(R, Q', Q, Q'', i, p) ⇔ " +
			"    cochain_complex(R, Q') ∧ " +
			"    cochain_complex(R, Q) ∧ " +
			"    cochain_complex(R, Q'') ∧ " +
			"    cochain_map(R, Q', Q, i) ∧ " +
			"    cochain_map(R, Q, Q'', p) ∧ " +
			"    exact_complexes(Q', Q, Q'', i, p)",
	},
	Deps: []registry.EntryLike{CochainComplex, CochainMapDef, ExactComplexesDef},
})}

// ShortExactCochainSubComplex — the subcomplex is a cochain complex.
var ShortExactCochainSubComplex = shortExactCochainSubComplexThm{family.Add(registry.ProofEntry{
	Name:  "ShortExactCochainSubComplex",
	Key:   "prop_a6f36c3f4ed9853a",
	Build: ShortExactCochainComplexes.Axiom("cochain_complex(R, Q')"),
})}

// ShortExactCochainMiddleComplex — the middle complex is a cochain complex.
var ShortExactCochainMiddleComplex = shortExactCochainMiddleComplexThm{family.Add(registry.ProofEntry{
	Name:  "ShortExactCochainMiddleComplex",
	Key:   "prop_d482ea2b80a77168",
	Build: ShortExactCochainComplexes.Axiom("cochain_complex(R, Q)"),
})}

// ShortExactCochainQuotientComplex — the quotient complex is a cochain complex.
var ShortExactCochainQuotientComplex = shortExactCochainQuotientComplexThm{family.Add(registry.ProofEntry{
	Name:  "ShortExactCochainQuotientComplex",
	Key:   "prop_f2335137e6534929",
	Build: ShortExactCochainComplexes.Axiom("cochain_complex(R, Q'')"),
})}

// ShortExactCochainInclusionMap — the inclusion is a cochain map.
var ShortExactCochainInclusionMap = shortExactCochainInclusionMapThm{family.Add(registry.ProofEntry{
	Name:  "ShortExactCochainInclusionMap",
	Key:   "prop_43789b7c9f02937d",
	Build: ShortExactCochainComplexes.Axiom("cochain_map(R, Q', Q, i)"),
})}

// ShortExactCochainProjectionMap — the projection is a cochain map.
var ShortExactCochainProjectionMap = shortExactCochainProjectionMapThm{family.Add(registry.ProofEntry{
	Name:  "ShortExactCochainProjectionMap",
	Key:   "prop_efcb70f2201a48b2",
	Build: ShortExactCochainComplexes.Axiom("cochain_map(R, Q, Q'', p)"),
})}

// ShortExactCochainDegreewise — the sequence is exact at every degree.
var ShortExactCochainDegreewise = shortExactCochainDegreewiseThm{family.Add(registry.ProofEntry{
	Name:  "ShortExactCochainDegreewise",
	Key:   "prop_ceb00d43cc9d5611",
	Build: ShortExactCochainComplexes.Axiom("exact_complexes(Q', Q, Q'', i, p)"),
})}

// CohomologyModuleOn — cohomology is a module: the quotient of the
// cocycles by the coboundaries.
var CohomologyModuleOn = cohomologyModuleOnThm{family.Add(registry.ProofEntry{
	Name: "CohomologyModuleOn",
	Key:  "prop_ebe12c66b4a40906",
	Deps: []registry.EntryLike{
		CohomologyModuleDef,
		CohomologyDef,
		CocyclesDef,
		CoboundariesDef,
		CochainModules,
		CochainCoboundaryHom,
		CochainCoboundaryTwice,
		module_homomorphism.KernelSubmodule,
		module_homomorphism.ImageSubmodule,
		submodule.QuotientModuleOn,
		submodule.SubmoduleModuleOn,
		submodule.SubmoduleRestrict,
		submodule.ZeroSubmodule,
	},
	Build: family.Card(CochainComplex.Statement("∀n:num. module_on(R, cohomology_module(Q, n))"),
		"the cocycles are the kernel of Q.d(n), a submodule; the coboundaries "+
			"are {Q.zero} or the image of Q.d(n−1), a submodule inside the "+
			"cocycles (two coboundaries in a row vanish); QuotientModuleOn"),
})}

// CochainMapCocycles — a cochain map carries cocycles to cocycles and
// coboundaries to coboundaries: the square f(m + 1) ∘ Q.d(m) = Q'.d(m) ∘ f(m)
// turns a member Q.d(n) kills into one Q'.d(n) kills and a value of Q.d(m)
// into a value of Q'.d(m), and at degree 0, where the coboundaries are the
// zero alone, f(0) sends the zero of Q to the zero of Q'.
var CochainMapCocycles = cochainMapCocyclesThm{family.Add(registry.ProofEntry{
	Name: "CochainMapCocycles",
	Key:  "prop_50d52ab2bbdb70a0",
	Build: CochainComplex.Law(Statement{
		Binders: "∀Q':complex_ops(A, C). ∀f:(num → B → C). ∀n:num.",
		Hypotheses: []string{
			"cochain_complex(R, Q')",
			"cochain_map(Q, Q', f)",
		},
		Conclusion: "(∀u:B. u ∈ cocycles(Q, n) ⇒ f(n)(u) ∈ cocycles(Q', n)) ∧ " +
			"(∀u:B. u ∈ coboundaries(Q, n) ⇒ f(n)(u) ∈ coboundaries(Q', n))",
	},
		func(
			a *Argument,
			sourceComplex Fact,
			targetComplex CochainComplexFact[on.R],
			_ *Arrow2[Nat, B, C],
			n *Expr[Nat],
			cochainMap Fact,
		) {
			clauses := []Fact{Read(CochainMapHom, cochainMap), Read(CochainMapSquare, cochainMap)}
			homs, square := clauses[0], clauses[1]
			modules, targetModules := CochainModules.Read(sourceComplex), CochainModules.Read(targetComplex)
			coboundaryHoms, targetCoboundaryHoms :=
				CochainCoboundaryHom.Read(sourceComplex), CochainCoboundaryHom.Read(targetComplex)
			a.Do(SplitConj(
				Case(
					"a cocycle goes to a cocycle",
					Unfold(CocyclesDef),
					Derive(func(b *Argument) {
						b.FixAs[B]("u")
						cocycle := b.Assume()
						opened := b.Have(
							"u lies in Q.terms(n) and Q.d(n) kills it",
							"u ∈ Q.terms(n) ∧ Q.d(n)(u) = Q.zero",
							BySets(cocycle))
						mappedCocycle := b.Have(
							"f(n)(u) lies in Q'.terms(n), and Q'.d(n)(f(n)(u)) "+
								"= f(n + 1)(Q.d(n)(u)) = f(n + 1)(Q.zero) = Q'.zero",
							"f(n)(u) ∈ Q'.terms(n) ∧ Q'.d(n)(f(n)(u)) = Q'.zero",
							ByChase(Depth(0), modules, targetModules, coboundaryHoms, homs, square, opened))
						b.Show(
							"so f(n)(u) is a cocycle of Q'",
							BySets(mappedCocycle))
					})),
				Case(
					"a coboundary goes to a coboundary",
					Derive(func(b *Argument) {
						b.Cases(b.Term("n = 0"))
						b.When(
							"at degree 0 the coboundaries are {Q.zero}, and f(0) keeps zero",
							func(c *Argument, isZero Fact) {
								c.Do(isZero.Rw(), Unfold(CoboundariesDef), Simp(
									Fwd(set_basic.InSing.Inst[B]()),
									Fwd(set_basic.InSing.Inst[C]())))
								c.FixAs[B]("u")
								coboundary := c.Assume()
								c.Show(
									"u = Q.zero, and f(0)(Q.zero) = Q'.zero",
									ByChase(Depth(0), modules, targetModules, homs, coboundary))
							})
						b.Otherwise(
							"above degree 0 the coboundaries are the image of "+
								"Q.d(m), and f(m + 1)(Q.d(m)(v)) = Q'.d(m)(f(m)(v))",
							func(c *Argument, positive Fact) {
								_, isSuc := c.ObtainAs[Nat](
									"a positive degree is a successor",
									"∃m:num. n = m + 1",
									By(positive, nat_arith.NonzeroIsSucc.At(n)))
								c.Do(isSuc.Rw(), Simp(
									Fwd(Read(CoboundariesSucc, sourceComplex)),
									Fwd(Read(CoboundariesSucc, targetComplex))))
								c.FixAs[B]("u")
								coboundary := c.Assume()
								c.Show(
									"f(m + 1)(u) = Q'.d(m)(f(m)(v)) lies in the image of Q'.d(m)",
									ByChase(
										Depth(0),
										modules,
										targetModules,
										coboundaryHoms,
										targetCoboundaryHoms,
										homs,
										square,
										coboundary))
							})
					})),
			))
		}),
})}

// CohomologyMapCoset — write N and N' for the two coboundary submodules
// at n. They are zero submodules at degree 0 and differential images in
// positive degree. CochainMapCocycles gives f(n)(N) ⊆ N', and f(n) is an
// additive group homomorphism. ImageLeftCosetMul then identifies
// f(n)(u + N) + N' with f(n)(u) + N'.
var CohomologyMapCoset = cohomologyMapCosetThm{family.Add(registry.ProofEntry{
	Name: "CohomologyMapCoset",
	Key:  "prop_d876027393affe50",
	Build: CochainComplex.Law(Statement{
		Binders: "∀Q':complex_ops(A, C). ∀f:(num → B → C). ∀n:num. ∀u:B.",
		Hypotheses: []string{
			"cochain_complex(R, Q')",
			"cochain_map(Q, Q', f)",
			"u ∈ cocycles(Q, n)",
		},
		Conclusion: "cohomology_map(Q', f, n, left_coset(Q.add, u, coboundaries(Q, n))) = " +
			"left_coset(Q'.add, f(n)(u), coboundaries(Q', n))",
	},
		func(
			a *Argument,
			sourceComplex Fact,
			targetComplex Fact,
			f *Arrow2[Nat, B, C],
			n *Expr[Nat],
			u *Expr[B],
			hyps Fact,
		) {
			given := a.Conjuncts(
				hyps,
				"f is a cochain map",
				"u is a cocycle of Q")
			homs := Read(CochainMapHom, given[0])
			modules, targetModules := CochainModules.Read(sourceComplex), CochainModules.Read(targetComplex)
			coboundaryHoms, targetCoboundaryHoms :=
				CochainCoboundaryHom.Read(sourceComplex), CochainCoboundaryHom.Read(targetComplex)
			uIn := a.Have(
				"u lies in Q.terms(n)",
				"u ∈ Q.terms(n)",
				BySets(a.Unfolded(given[1], CocyclesDef)))

			coboundarySubmodules := a.Conjuncts(
				a.Have(
					"the coboundaries in both complexes are submodules",
					"submodule(R, complex_module(Q, n), coboundaries(Q, n)) ∧ "+
						"submodule(R, complex_module(Q', n), coboundaries(Q', n))",
					Derive(func(b *Argument) {
						b.Cases(b.Term("n = 0"))
						b.When(
							"at degree 0 the coboundaries are the zero submodules",
							func(c *Argument, isZero Fact) {
								c.Do(isZero.Rw(), Unfold(CoboundariesDef))
								zero := c.TermAs[Nat]("0")
								source := c.Have(
									"Q at degree 0 is a module",
									"module_on(R, complex_module(Q, 0))",
									By(modules.At(zero)))
								target := c.Have(
									"and so is Q' at degree 0",
									"module_on(R, complex_module(Q', 0))",
									By(targetModules.At(zero)))
								c.Show(
									"the zero alone is a submodule in each module",
									By(submodule.ZeroSubmodule.Read(source), submodule.ZeroSubmodule.Read(target)))
							})
						b.Otherwise(
							"in a positive degree the coboundaries are the images of the preceding differentials",
							func(c *Argument, positive Fact) {
								m, isSuc := c.ObtainAs[Nat](
									"a positive degree is a successor",
									"∃m:num. n = m + 1",
									By(positive, nat_arith.NonzeroIsSucc.At(n)))
								c.Do(isSuc.Rw(), Simp(
									Fwd(Read(CoboundariesSucc, sourceComplex)),
									Fwd(Read(CoboundariesSucc, targetComplex))))
								source := c.Have(
									"Q.d(m) is a homomorphism of the degree modules",
									"module_homomorphism(R, complex_module(Q, m), complex_module(Q, m + 1), Q.d(m))",
									By(coboundaryHoms.At(m)))
								target := c.Have(
									"and so is Q'.d(m)",
									"module_homomorphism(R, complex_module(Q', m), complex_module(Q', m + 1), Q'.d(m))",
									By(targetCoboundaryHoms.At(m)))
								c.Show(
									"so their images are submodules of their target modules",
									By(
										module_homomorphism.ImageSubmodule.Read(source),
										module_homomorphism.ImageSubmodule.Read(target)))
							})
					})),
				"the source coboundaries form a submodule",
				"the target coboundaries form a submodule")
			additiveHom := a.Have(
				"f(n) is an additive group homomorphism",
				"group_homomorphism(mk_group(Q.add, Q.zero, Q.neg, Q.terms(n)), "+
					"    mk_group(Q'.add, Q'.zero, Q'.neg, Q'.terms(n)), "+
					"    f(n))",
				Derive(func(b *Argument) {
					hom := b.Have(
						"f(n) is a homomorphism of the degree modules",
						"module_homomorphism(R, complex_module(Q, n), complex_module(Q', n), f(n))",
						By(homs.At(n)))
					additive := b.Simplified(
						module_homomorphism.HomGroup.Read(hom),
						Fwd(module_record.ModuleAdditiveGroupDef))
					b.Show(
						"so it is one of their additive groups",
						By(additive))
				}))
			sourceSubgroup := a.Simplified(
				submodule.SubmoduleSubgroup.Read(coboundarySubmodules[0]),
				Fwd(module_record.ModuleAdditiveGroupDef))
			targetSubgroup := a.Simplified(
				submodule.SubmoduleSubgroup.Read(coboundarySubmodules[1]),
				Fwd(module_record.ModuleAdditiveGroupDef))
			subgroups := a.Have(
				"the two coboundary submodules are additive subgroups",
				"subgroup(mk_group(Q.add, Q.zero, Q.neg, Q.terms(n)), coboundaries(Q, n)) ∧ "+
					"subgroup(mk_group(Q'.add, Q'.zero, Q'.neg, Q'.terms(n)), coboundaries(Q', n))",
				By(sourceSubgroup, targetSubgroup))
			mapsCoboundaries := a.Have(
				"f(n) carries source coboundaries to target coboundaries",
				"∀v:B. v ∈ coboundaries(Q, n) ⇒ f(n)(v) ∈ coboundaries(Q', n)",
				By(Read(CochainMapCocycles, sourceComplex, targetComplex).At(f, n), given[0]))
			a.Show(
				"the image coset enlarged by the target coboundaries is the coset of f(n)(u)",
				Simp(Fwd(CohomologyMapDef)),
				By(
					quotient_group.ImageLeftCosetMul.Read(additiveHom).At(
						a.TermAs[Set[B]]("coboundaries(Q, n)"),
						a.TermAs[Set[C]]("coboundaries(Q', n)"),
						proof.MemberOf(u, uIn)),
					subgroups,
					mapsCoboundaries))
		}),
})}

// CohomologyMapHom — the map on cohomology is a homomorphism of the
// cohomology modules.
var CohomologyMapHom = cohomologyMapHomThm{family.Add(registry.ProofEntry{
	Name: "CohomologyMapHom",
	Key:  "prop_f3ad53b30ad543a5",
	Deps: []registry.EntryLike{
		CohomologyMapCoset,
		CohomologyModuleOn,
		CochainMapCocycles,
		module_homomorphism.ModuleHomomorphismDef,
		module_homomorphism.HomAdd,
		module_homomorphism.HomSmul,
		quotient_group.InLeftCosets,
		quotient_group.LeftCosetMulOn,
		submodule.QuotientSmulCoset,
	},
	Build: family.Card(CochainComplex.Statement(Statement{
		Binders: "∀Q':complex_ops(A, C). ∀f:(num → B → C). ∀n:num.",
		Hypotheses: []string{
			"cochain_complex(R, Q')",
			"cochain_map(Q, Q', f)",
		},
		Conclusion: "module_homomorphism(R, " +
			"    quotient_module(restrict_module(complex_module(Q, n), cocycles(Q, n)), coboundaries(Q, n)), " +
			"    quotient_module(restrict_module(complex_module(Q', n), cocycles(Q', n)), " +
			"        coboundaries(Q', n)), " +
			"    cohomology_map(Q', f, n))",
	}),
		"every class is some u + B^n(Q) with u a cocycle; CohomologyMapCoset reads each clause off f(n)'s"),
})}

// HomotopicSameCohomologyMap — cochain-homotopic cochain maps induce
// the same map on cohomology. A class is u + N with u a cocycle and N
// the coboundaries of Q at n, and each map carries it to the class of
// its value at u, so what is to be shown is that f(n)(u) − g(n)(u) lies
// in the coboundaries of Q'. Above degree 0 the homotopy makes it
// Q'.d(n − 1)(h(n)(u)) + h(n + 1)(Q.d(n)(u)), and Q.d(n) kills the
// cocycle u, so it is the coboundary Q'.d(n − 1)(h(n)(u)); at degree 0
// it is h(1)(Q.d(0)(u)), zero for the same reason.
var HomotopicSameCohomologyMap = homotopicSameCohomologyMapThm{family.Add(registry.ProofEntry{
	Name: "HomotopicSameCohomologyMap",
	Key:  "prop_90e19237469f2aa1",
	Build: CochainComplex.Law(Statement{
		Binders: "∀Q':complex_ops(A, C). ∀f g h:(num → B → C). ∀n:num. ∀s:set(B).",
		Hypotheses: []string{
			"cochain_complex(R, Q')",
			"cochain_map(Q, Q', f)",
			"cochain_map(Q, Q', g)",
			"cochain_homotopy(Q, Q', f, g, h)",
			"s ∈ cohomology(Q, n)",
		},
		Conclusion: "cohomology_map(Q', f, n, s) = cohomology_map(Q', g, n, s)",
	},
		func(
			a *Argument,
			sourceComplex Fact,
			targetComplex CochainComplexFact[on.R],
			f, g, _ *Arrow2[Nat, B, C],
			hyps Fact,
			n *Expr[Nat],
			_ *Expr[Set[B]],
			sIn Fact,
		) {
			given := a.Conjuncts(
				hyps,
				"f is a cochain map",
				"g is a cochain map",
				"h is a cochain homotopy from f to g")
			fHoms := Read(CochainMapHom, given[0])
			gHoms := Read(CochainMapHom, given[1])
			homotopy := a.Conjuncts(
				a.Unfolded(given[2], CochainHomotopyDef),
				"each h(m + 1) is a homomorphism from Q.terms(m + 1) to Q'.terms(m)",
				"f(m + 1) − g(m + 1) = Q'.d(m) ∘ h(m + 1) + h(m + 2) ∘ Q.d(m + 1) on Q.terms(m + 1)",
				"f(0) − g(0) = h(1) ∘ Q.d(0) on Q.terms(0)")
			hHoms, above, atZeroDegree := homotopy[0], homotopy[1], homotopy[2]
			modules, targetModules := CochainModules.Read(sourceComplex), CochainModules.Read(targetComplex)
			coboundaryHoms, targetCoboundaryHoms :=
				CochainCoboundaryHom.Read(sourceComplex), CochainCoboundaryHom.Read(targetComplex)

			u, sIs := a.ObtainAs[B](
				"s is the class of a cocycle u",
				"∃u:B. s = left_coset(Q.add, u, coboundaries(Q, n)) ∧ u ∈ cocycles(Q, n)",
				By(sIn, InCohomology.Read(sourceComplex)))
			class := a.Conjuncts(
				sIs,
				"s is the class of u",
				"u is a cocycle of Q")
			sEq, cocycle := class[0], class[1]
			opened := a.Have(
				"u lies in Q.terms(n) and Q.d(n) kills it",
				"u ∈ Q.terms(n) ∧ Q.d(n)(u) = Q.zero",
				BySets(a.Unfolded(cocycle, CocyclesDef)))
			// Each map carries the class of u to the class of its value at u.
			fClass := a.Have(
				"f sends the class of u to the class of f(n)(u)",
				"cohomology_map(Q', f, n, left_coset(Q.add, u, coboundaries(Q, n))) = "+
					"left_coset(Q'.add, f(n)(u), coboundaries(Q', n))",
				By(Read(CohomologyMapCoset, sourceComplex, targetComplex).At(f, n, u), given[0], cocycle))
			gClass := a.Have(
				"g sends the class of u to the class of g(n)(u)",
				"cohomology_map(Q', g, n, left_coset(Q.add, u, coboundaries(Q, n))) = "+
					"left_coset(Q'.add, g(n)(u), coboundaries(Q', n))",
				By(Read(CohomologyMapCoset, sourceComplex, targetComplex).At(g, n, u), given[1], cocycle))
			a.Do(sEq.Rw(), fClass.Rw(), gClass.Rw())
			a.Cases(a.Term("n = 0"))
			a.When(
				"at degree 0, f(0)(u) − g(0)(u) = h(1)(Q.d(0)(u)) = "+
					"h(1)(Q.zero) = Q'.zero, and equal representatives have one class",
				func(b *Argument, isZero Fact) {
					atZero := b.Have(
						"so u lies in Q.terms(0) and Q.d(0) kills it",
						"u ∈ Q.terms(0) ∧ Q.d(0)(u) = Q.zero",
						isZero.Rw(),
						Basic())
					same := b.Have(
						"f(0) and g(0) agree at u",
						"f(0)(u) = g(0)(u)",
						ByChase(
							Depth(0),
							modules,
							targetModules,
							coboundaryHoms,
							fHoms,
							gHoms,
							hHoms,
							atZeroDegree,
							atZero))
					b.Show(
						"so the two classes agree",
						isZero.Rw(),
						same.Rw(),
						Basic())
				})
			a.Otherwise(
				"above degree 0 the coboundaries are the image of Q'.d(m), and "+
					"f(m + 1)(u) − g(m + 1)(u) = Q'.d(m)(h(m + 1)(u)) lies in it",
				func(b *Argument, positive Fact) {
					m, isSuc := b.ObtainAs[Nat](
						"a positive degree is a successor",
						"∃m:num. n = m + 1",
						By(positive, nat_arith.NonzeroIsSucc.At(n)))
					lifted := b.Have(
						"so u lies in Q.terms(m + 1) and Q.d(m + 1) kills it",
						"u ∈ Q.terms(m + 1) ∧ Q.d(m + 1)(u) = Q.zero",
						By(Normalized, opened, isSuc))
					b.Do(isSuc.Rw())
					targetCoboundaries := b.Have(
						"the coboundaries of Q' at m + 1 are the image of Q'.d(m)",
						"coboundaries(Q', m + 1) = image(Q'.d(m), Q'.terms(m))",
						By(Read(CoboundariesSucc, targetComplex).At(m)))
					b.Do(targetCoboundaries.Rw())
					images := b.Have(
						"the image of Q'.d(m) is a submodule of Q'.terms(m + 1)",
						"submodule(R, complex_module(Q', m + 1), image(Q'.d(m), Q'.terms(m)))",
						Derive(func(c *Argument) {
							hom := c.Have(
								"Q'.d(m) is a homomorphism of the degree modules",
								"module_homomorphism(R, complex_module(Q', m), complex_module(Q', m + 1), Q'.d(m))",
								By(targetCoboundaryHoms.At(m)))
							c.Show(
								"so its image is a submodule of its target module",
								By(module_homomorphism.ImageSubmodule.Read(hom)))
						}))
					b.Show(
						"the classes agree: −f(m + 1)(u) + g(m + 1)(u) = Q'.d(m)(−h(m + 1)(u))",
						ByChase(
							Depth(0),
							modules,
							targetModules,
							coboundaryHoms,
							targetCoboundaryHoms,
							fHoms,
							gHoms,
							hHoms,
							above,
							lifted,
							images))
				})
		}),
})}

// CohomologyMapIdentity — the identity induces the identity on cohomology.
var CohomologyMapIdentity = cohomologyMapIdentityThm{family.Add(registry.ProofEntry{
	Name: "CohomologyMapIdentity",
	Key:  "prop_1c077005ce0f362d",
	Deps: []registry.EntryLike{
		CohomologyMapCoset,
		CohomologyDef,
		CocyclesDef,
		CochainMapIdentity,
		quotient_group.InLeftCosets,
	},
	Build: family.Card(CochainComplex.Statement(Statement{
		Binders: "∀n:num. ∀s:set(B).",
		Hypotheses: []string{
			"s ∈ cohomology(Q, n)",
		},
		Conclusion: "cohomology_map(Q, λm:num. λx:B. x, n, s) = s",
	}),
		"every class is the class of a cocycle u (CohomologyDef, InLeftCosets), and the identity, "+
			"a cochain map (CochainMapIdentity), sends it to the class of u (CohomologyMapCoset)"),
})}

// CohomologyMapCompose — the map of a composite of cochain maps is the
// composite of their maps.
var CohomologyMapCompose = cohomologyMapComposeThm{family.Add(registry.ProofEntry{
	Name: "CohomologyMapCompose",
	Key:  "prop_db6786cc0eb08ee9",
	Deps: []registry.EntryLike{
		CohomologyMapCoset,
		CohomologyDef,
		CocyclesDef,
		CochainMapCocycles,
		CochainMapCompose,
		quotient_group.InLeftCosets,
	},
	Build: family.Card(CochainComplex.Statement(Statement{
		Binders: "∀Q':complex_ops(A, C). " +
			"∀Q'':complex_ops(A, D). " +
			"∀f:(num → B → C). " +
			"∀g:(num → C → D). " +
			"∀n:num. " +
			"∀s:set(B).",
		Hypotheses: []string{
			"cochain_complex(R, Q')",
			"cochain_complex(R, Q'')",
			"cochain_map(R, Q, Q', f)",
			"cochain_map(R, Q', Q'', g)",
			"s ∈ cohomology(Q, n)",
		},
		Conclusion: "cohomology_map(Q'', λm:num. λx:B. g(m)(f(m)(x)), n, s) = " +
			"cohomology_map(Q'', g, n, cohomology_map(Q', f, n, s))",
	}),
		"every class is the class of a cocycle u (CohomologyDef, InLeftCosets); the composite, a cochain "+
			"map (CochainMapCompose), sends it to the class of g(f(u)) (CohomologyMapCoset), which is g's "+
			"map at the class of the cocycle f(u) (CochainMapCocycles), itself f's map at the class of u"),
})}

// CohomologyMapCongruence — cochain maps that agree on the terms induce
// the same map on cohomology.
var CohomologyMapCongruence = cohomologyMapCongruenceThm{family.Add(registry.ProofEntry{
	Name: "CohomologyMapCongruence",
	Key:  "prop_4b97a726aa0a4917",
	Reading: "Nothing is asked of f' but its values on Q's terms: a class lies in " +
		"Q.terms(n), and cohomology_map reads f'(n) only through its image of the class. It " +
		"is what lets a map written by another formula that agrees on the terms, such as a " +
		"composite unfolded or an identity written out, stand for a cochain map on cohomology.",
	Deps: []registry.EntryLike{
		CohomologyMapDef,
		CohomologyDef,
		CocyclesDef,
		CoboundariesDef,
		CoboundariesSucc,
		CochainModules,
		CochainCoboundaryHom,
		module_homomorphism.ImageSubmodule,
		module.AddGroupOn,
		submodule.ZeroSubmodule,
		submodule.SubmoduleSubgroup,
		quotient_group.InLeftCosets,
		set_basic.InImage,
		set_basic.Extension,
	},
	Build: family.Card(CochainComplex.Statement(Statement{
		Binders: "∀Q':complex_ops(A, C). ∀f f':(num → B → C). ∀n:num. ∀s:set(B).",
		Hypotheses: []string{
			"cochain_complex(R, Q')",
			"cochain_map(R, Q, Q', f)",
			"∀m:num. ∀x:B. x ∈ Q.terms(m) ⇒ f(m)(x) = f'(m)(x)",
			"s ∈ cohomology(Q, n)",
		},
		Conclusion: "cohomology_map(Q', f', n, s) = cohomology_map(Q', f, n, s)",
	}),
		"a class s lies in Q.terms(n), the cocycle u and the coboundaries there being in "+
			"it (CohomologyDef, InLeftCosets, CocyclesDef, CoboundariesDef, CoboundariesSucc, "+
			"the group closure by AddGroupOn), so image(f'(n), s) = image(f(n), s) (InImage, "+
			"Extension), and CohomologyMapDef reads f'(n) only through that image"),
})}

// CochainHomotopyCongruence — a cochain homotopy between two maps is one
// between any two maps that agree with them on the terms: every clause of
// cochain_homotopy evaluates the maps at a point of Q's terms.
var CochainHomotopyCongruence = cochainHomotopyCongruenceThm{family.Add(registry.ProofEntry{
	Name: "CochainHomotopyCongruence",
	Key:  "prop_9dafa883e41f78c3",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀Q:complex_ops(A, B). " +
			"∀Q':complex_ops(A, C). " +
			"∀f g h f' g':(num → B → C).",
		Hypotheses: []string{
			"cochain_homotopy(R, Q, Q', f, g, h)",
			"∀n:num. ∀u:B. u ∈ Q.terms(n) ⇒ f'(n)(u) = f(n)(u) ∧ g'(n)(u) = g(n)(u)",
		},
		Conclusion: "cochain_homotopy(R, Q, Q', f', g', h)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			Q *Expr[ComplexOps[A, B]],
			Qʹ *Expr[ComplexOps[A, C]],
			f, g, h, fʹ, gʹ *Arrow2[Nat, B, C],
			given Fact,
		) {
			a.Show(
				"every clause of cochain_homotopy evaluates the maps "+
					"at a point of Q's terms, where f' is f and g' is g",
				By(given, CochainHomotopyDef))
		}),
})}

// CochainHomotopyEquivalenceIsomorphism — a cochain homotopy equivalence
// induces an isomorphism on cohomology in every degree. The map g induces
// is a two-sided inverse of f's: the map of g ∘ f is g's after f's, and
// g ∘ f, homotopic to the identity, induces the identity; likewise f ∘ g.
// A linear map with a two-sided inverse is a bijection of the classes.
var CochainHomotopyEquivalenceIsomorphism = cochainHomotopyEquivalenceIsomorphismThm{family.Add(registry.ProofEntry{
	Name: "CochainHomotopyEquivalenceIsomorphism",
	Key:  "prop_95e0c3db2dc7e3f1",
	Build: CochainComplex.Law(Statement{
		Binders: "∀Q':complex_ops(A, C). ∀f:(num → B → C). ∀g:(num → C → B). ∀n:num.",
		Hypotheses: []string{
			"cochain_complex(R, Q')",
			"cochain_homotopy_equivalence(R, Q, Q', f, g)",
		},
		Conclusion: "module_isomorphism(R, " +
			"    cohomology_module(Q, n), " +
			"    cohomology_module(Q', n), " +
			"    cohomology_map(Q', f, n))",
	},
		func(
			a *Argument,
			sourceComplex CochainComplexFact[on.R],
			QPrime *Expr[ComplexOps[A, C]],
			f *Arrow2[Nat, B, C],
			g *Arrow2[Nat, C, B],
			n *Expr[Nat],
			hyps Fact,
		) {
			given := a.Conjuncts(
				hyps,
				"Q' is a cochain complex",
				"f and g are a cochain homotopy equivalence")
			targetComplex := given[0]
			equivalence := a.Conjuncts(
				a.Unfolded(given[1], CochainHomotopyEquivalenceDef),
				"f is a cochain map from Q to Q'",
				"g is a cochain map from Q' to Q",
				"some k is a cochain homotopy from g ∘ f to the identity of Q",
				"some l is a cochain homotopy from f ∘ g to the identity of Q'")
			fMap, gMap := equivalence[0], equivalence[1]
			k, kHomotopy := a.UnpackAs[Fun2[Nat, B, B]](equivalence[2], "k")
			l, lHomotopy := a.UnpackAs[Fun2[Nat, C, C]](equivalence[3], "l")

			R := a.TermAs[RingOps[A]]("R")
			Q := a.TermAs[ComplexOps[A, B]]("Q")
			gAfterF := a.TermAs[Fun2[Nat, B, B]]("λm:num. λx:B. g(m)(f(m)(x))")
			fAfterG := a.TermAs[Fun2[Nat, C, C]]("λm:num. λy:C. f(m)(g(m)(y))")
			identity := a.TermAs[Fun2[Nat, B, B]]("λm:num. λx:B. x")
			identityPrime := a.TermAs[Fun2[Nat, C, C]]("λm:num. λy:C. y")
			gfMap := a.Have(
				"g ∘ f is a cochain map from Q to itself",
				"cochain_map(R, Q, Q, (λm:num. λx:B. g(m)(f(m)(x))))",
				By(CochainMapCompose.At(R, Q, QPrime, Q, f, g), fMap, gMap))
			fgMap := a.Have(
				"f ∘ g is a cochain map from Q' to itself",
				"cochain_map(R, Q', Q', (λm:num. λy:C. f(m)(g(m)(y))))",
				By(CochainMapCompose.At(R, QPrime, Q, QPrime, g, f), gMap, fMap))

			backAndForth := a.Have(
				"g's map undoes f's on the classes of Q",
				"∀s:set(B). s ∈ cohomology(Q, n) ⇒ cohomology_map(Q, g, n, cohomology_map(Q', f, n, s)) = s",
				Derive(func(b *Argument) {
					s := b.FixAs[Set[B]]("s")
					sIn := b.Assume()
					b.Show(
						"through the map of g ∘ f, which is the identity's",
						CalcEq(
							Leg(
								b.TermAs[Set[B]]("cohomology_map(Q, (λm:num. λx:B. g(m)(f(m)(x))), n, s)"),
								"g's map after f's is the map of g ∘ f",
								By(
									CohomologyMapCompose.Read(sourceComplex).At(QPrime, Q, f, g, n, s),
									targetComplex,
									sourceComplex,
									fMap,
									gMap,
									sIn)),
							Leg(
								b.TermAs[Set[B]]("cohomology_map(Q, (λm:num. λx:B. x), n, s)"),
								"k makes g ∘ f homotopic to the identity, so the two agree on cohomology",
								By(
									HomotopicSameCohomologyMap.Read(sourceComplex).At(Q, gAfterF, identity, k, n, s),
									sourceComplex,
									gfMap,
									CochainMapIdentity.Read(sourceComplex),
									kHomotopy,
									sIn)),
							FinalLeg(
								"the identity induces the identity",
								By(CohomologyMapIdentity.Read(sourceComplex).At(n, s), sIn)),
						))
				}))
			forthAndBack := a.Have(
				"f's map undoes g's on the classes of Q'",
				"∀t:set(C). t ∈ cohomology(Q', n) ⇒ cohomology_map(Q', f, n, cohomology_map(Q, g, n, t)) = t",
				Derive(func(b *Argument) {
					t := b.FixAs[Set[C]]("t")
					tIn := b.Assume()
					b.Show(
						"through the map of f ∘ g, which is the identity's",
						CalcEq(
							Leg(
								b.TermAs[Set[C]]("cohomology_map(Q', (λm:num. λy:C. f(m)(g(m)(y))), n, t)"),
								"f's map after g's is the map of f ∘ g",
								By(
									CohomologyMapCompose.Read(targetComplex).At(Q, QPrime, g, f, n, t),
									sourceComplex,
									targetComplex,
									gMap,
									fMap,
									tIn)),
							Leg(
								b.TermAs[Set[C]]("cohomology_map(Q', (λm:num. λy:C. y), n, t)"),
								"l makes f ∘ g homotopic to the identity, so the two agree on cohomology",
								By(
									HomotopicSameCohomologyMap.Read(targetComplex).At(QPrime, fAfterG, identityPrime, l, n, t),
									targetComplex,
									fgMap,
									CochainMapIdentity.Read(targetComplex),
									lHomotopy,
									tIn)),
							FinalLeg(
								"the identity induces the identity",
								By(CohomologyMapIdentity.Read(targetComplex).At(n, t), tIn)),
						))
				}))

			fLinear := a.Have(
				"f's map is linear",
				"module_homomorphism(R, "+
					"    cohomology_module(Q, n), "+
					"    cohomology_module(Q', n), "+
					"    cohomology_map(Q', f, n))",
				Unfold(CohomologyModuleDef),
				By(CohomologyMapHom.Read(sourceComplex).At(QPrime, f, n), targetComplex, fMap))
			gLinear := a.Have(
				"and so is g's",
				"module_homomorphism(R, "+
					"    cohomology_module(Q', n), "+
					"    cohomology_module(Q, n), "+
					"    cohomology_map(Q, g, n))",
				Unfold(CohomologyModuleDef),
				By(CohomologyMapHom.Read(targetComplex).At(Q, g, n), sourceComplex, gMap))
			fInto := a.Have(
				"f's map carries the classes of Q to classes of Q'",
				"∀s:set(B). s ∈ cohomology(Q, n) ⇒ cohomology_map(Q', f, n, s) ∈ cohomology(Q', n)",
				Unfold(CohomologyDef),
				By(module_homomorphism.HomIn.Read(fLinear)))
			gInto := a.Have(
				"and g's those of Q' to classes of Q",
				"∀t:set(C). t ∈ cohomology(Q', n) ⇒ cohomology_map(Q, g, n, t) ∈ cohomology(Q, n)",
				Unfold(CohomologyDef),
				By(module_homomorphism.HomIn.Read(gLinear)))

			classes := a.TermAs[Set[Set[B]]]("cohomology(Q, n)")
			classesPrime := a.TermAs[Set[Set[C]]]("cohomology(Q', n)")
			fStar := a.TermAs[Fun[Set[B], Set[C]]]("cohomology_map(Q', f, n)")
			gStar := a.TermAs[Fun[Set[C], Set[B]]]("cohomology_map(Q, g, n)")
			bijective := a.Have(
				"so f's map is a bijection of the classes, g's its inverse",
				"injective_on(cohomology(Q, n), cohomology_map(Q', f, n)) ∧ "+
					"image(cohomology_map(Q', f, n), cohomology(Q, n)) = cohomology(Q', n)",
				By(
					backAndForth,
					forthAndBack,
					fInto,
					gInto,
					functions.TwoSidedInverseBijection.At(classes, classesPrime, fStar, gStar)))
			cohomologyModule := a.TermAs[ModuleOps[A, Set[B]]]("cohomology_module(Q, n)")
			cohomologyModulePrime := a.TermAs[ModuleOps[A, Set[C]]]("cohomology_module(Q', n)")
			a.Show(
				"a linear bijection of the classes, the carriers of the cohomology modules, is an isomorphism",
				By(
					module_homomorphism.ModuleIsomorphismDef.At(R, cohomologyModule, cohomologyModulePrime, fStar),
					fLinear,
					bijective,
					CohomologyDef.At(Q, n),
					CohomologyDef.At(QPrime, n)))
		}),
})}

// ---------------------------------------------------------------------------
// The cochain snake lemma
// ---------------------------------------------------------------------------

// CocycleLiftPullback — surjectivity lifts a quotient cocycle, and exactness
// pulls its differential back. The commuting square and the square-zero law
// kill the pullback's differential after i, so injectivity kills it already.
var CocycleLiftPullback = cocycleLiftPullbackThm{family.Add(registry.ProofEntry{
	Name: "CocycleLiftPullback",
	Key:  "prop_3a8779bd7fc20876",
	Build: ShortExactCochainComplexes.Law(Statement{
		Binders: "∀n:num. ∀z:D.",
		Hypotheses: []string{
			"z ∈ cocycles(Q'', n)",
		},
		Conclusion: "∃u:C. ∃w:B. " +
			"    u ∈ Q.terms(n) ∧ " +
			"    p(n)(u) = z ∧ " +
			"    w ∈ Q'.terms(n + 1) ∧ " +
			"    i(n + 1)(w) = Q.d(n)(u) ∧ " +
			"    w ∈ cocycles(Q', n + 1)",
	},
		func(a *Argument, S ShortExactCochainComplexesFact[on.R], n *Expr[Nat], z *Expr[D], zCocycle Fact) {
			parts := []Fact{
				Read(ShortExactCochainSubComplex, S),
				Read(ShortExactCochainMiddleComplex, S),
				Read(ShortExactCochainQuotientComplex, S),
				Read(ShortExactCochainInclusionMap, S),
				Read(ShortExactCochainProjectionMap, S),
				Read(ShortExactCochainDegreewise, S),
			}
			sub, middle, quotient := parts[0], parts[1], parts[2]
			iClauses := []Fact{Read(CochainMapHom, parts[3]), Read(CochainMapSquare, parts[3])}
			pClauses := []Fact{Read(CochainMapHom, parts[4]), Read(CochainMapSquare, parts[4])}
			iHoms, iSquare, pHoms, pSquare := iClauses[0], iClauses[1], pClauses[0], pClauses[1]
			exact := a.Unfolded(parts[5], ExactComplexesDef)
			subModules, middleModules, quotientModules :=
				CochainModules.Read(sub), CochainModules.Read(middle), CochainModules.Read(quotient)
			subCoboundaryHoms, middleCoboundaryHoms, quotientCoboundaryHoms :=
				CochainCoboundaryHom.Read(sub),
				CochainCoboundaryHom.Read(middle),
				CochainCoboundaryHom.Read(quotient)

			zOpen := a.Have(
				"z lies in Q''.terms(n) and its differential is zero",
				"z ∈ Q''.terms(n) ∧ Q''.d(n)(z) = Q''.zero",
				BySets(a.Unfolded(zCocycle, CocyclesDef)))
			u, lift := a.ObtainAs[C](
				"surjectivity of p(n) gives a lift u of z",
				"∃u:C. u ∈ Q.terms(n) ∧ p(n)(u) = z",
				ByChase(Depth(1), middleModules, quotientModules, pHoms, exact, zOpen))
			w, pull := a.ObtainAs[B](
				"the p-square kills the differential of u, so exactness pulls it back through i(n + 1)",
				"∃w:B. w ∈ Q'.terms(n + 1) ∧ i(n + 1)(w) = Q.d(n)(u)",
				ByChase(
					Depth(1),
					subModules,
					middleModules,
					quotientModules,
					middleCoboundaryHoms,
					quotientCoboundaryHoms,
					iHoms,
					pHoms,
					pSquare,
					exact,
					zOpen,
					lift))
			killed := a.Have(
				"the i-square and the square-zero law kill i(n + "+
					"2)(Q'.d(n + 1)(w)); injectivity kills Q'.d(n + 1)(w)",
				"Q'.d(n + 1)(w) = Q'.zero",
				ByChase(
					Depth(1),
					subModules,
					middleModules,
					subCoboundaryHoms,
					middleCoboundaryHoms,
					CochainCoboundaryTwice.Read(middle),
					iHoms,
					iSquare,
					exact,
					lift,
					pull))
			wCocycle := a.Have(
				"w is a cocycle of Q'",
				"w ∈ cocycles(Q', n + 1)",
				Simp(Fwd(CocyclesDef.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[B]()))),
				BySets(pull, killed))
			a.Take(u)
			a.Take(w)
			a.Show(
				"u lifts z and the cocycle w pulls back its differential",
				By(lift, pull, wCocycle))
		}),
})}

// CoconnectingHomCoset — the connecting map on the class of a cocycle
// z, computed from any lift u of z and any pull-back w of Q.d(n)(u): the
// class of w. The map takes the chosen pull-back w₁ of Q.d(n)(u₁), u₁ a
// lift of a member of the class, and w and u realise the choice. Then
// p(n)(u₁) = z + b with b a coboundary of the quotient complex, and b is
// p(n)(c) for a c of Q.terms(n) that Q.d(n) kills: the zero at degree 0, and
// above it Q.d(m)(x), b being the coboundary of p(m)(x) in the quotient.
// So u₁ − u − c lies in the kernel of p(n) and is i(n)(v), whence
// i(n + 1)(w₁ − w) = Q.d(n)(i(n)(v)) = i(n + 1)(Q'.d(n)(v)); i(n + 1) is
// one-to-one, so w₁ − w = Q'.d(n)(v) is a coboundary of Q' at n + 1.
var CoconnectingHomCoset = coconnectingHomCosetThm{family.Add(registry.ProofEntry{
	Name: "CoconnectingHomCoset",
	Key:  "prop_20e009e8600cb31f",
	Build: ShortExactCochainComplexes.Law(Statement{
		Binders: "∀n:num. ∀z:D. ∀u:C. ∀w:B.",
		Hypotheses: []string{
			"u ∈ Q.terms(n)",
			"p(n)(u) = z",
			"w ∈ Q'.terms(n + 1)",
			"i(n + 1)(w) = Q.d(n)(u)",
		},
		Conclusion: "coconnecting_hom(Q', Q, i, p, n, left_coset(Q''.add, z, coboundaries(Q'', n))) = " +
			"left_coset(Q'.add, w, coboundaries(Q', n + 1))",
	},
		func(
			a *Argument,
			S ShortExactCochainComplexesFact[on.R],
			n *Expr[Nat],
			z *Expr[D],
			u *Expr[C],
			w *Expr[B],
			hyps Fact,
		) {
			parts := []Fact{
				Read(ShortExactCochainSubComplex, S),
				Read(ShortExactCochainMiddleComplex, S),
				Read(ShortExactCochainQuotientComplex, S),
				Read(ShortExactCochainInclusionMap, S),
				Read(ShortExactCochainProjectionMap, S),
				Read(ShortExactCochainDegreewise, S),
			}
			sub, middle, quotient := parts[0], parts[1], parts[2]
			iClauses := []Fact{Read(CochainMapHom, parts[3]), Read(CochainMapSquare, parts[3])}
			pClauses := []Fact{Read(CochainMapHom, parts[4]), Read(CochainMapSquare, parts[4])}
			iHoms, iSquare, pHoms, pSquare := iClauses[0], iClauses[1], pClauses[0], pClauses[1]
			exact := a.Unfolded(parts[5], ExactComplexesDef)
			subModules, middleModules, quotientModules :=
				CochainModules.Read(sub), CochainModules.Read(middle), CochainModules.Read(quotient)
			subCoboundaryHoms, middleCoboundaryHoms, quotientCoboundaryHoms :=
				CochainCoboundaryHom.Read(sub),
				CochainCoboundaryHom.Read(middle),
				CochainCoboundaryHom.Read(quotient)
			given := a.Conjuncts(
				hyps,
				"u lies in Q.terms(n)",
				"u lifts z",
				"w lies in Q'.terms(n + 1)",
				"w pulls back Q.d(n)(u)")
			uIn, uLifts, wIn, wPulls := given[0], given[1], given[2], given[3]

			coboundaryFacts := a.Conjuncts(
				a.Have(
					"Q''.zero is a coboundary of Q'' at n, and a coboundary of "+
						"Q'' at n is p(n) of an element of Q.terms(n) that Q.d(n) kills",
					"Q''.zero ∈ coboundaries(Q'', n) ∧ "+
						"(∀b:D. b ∈ coboundaries(Q'', n) ⇒ ∃c:C. c ∈ Q.terms(n) ∧ Q.d(n)(c) = Q.zero ∧ p(n)(c) = b)",
					Derive(func(b *Argument) {
						b.Cases(b.Term("n = 0"))
						b.When(
							"at degree 0 the coboundaries of Q'' are the zero alone, and Q.zero lifts it",
							func(c *Argument, isZero Fact) {
								c.Do(isZero.Rw(), Unfold(CoboundariesDef), Simp(Fwd(set_basic.InSing.Inst[D]())), TrivialSimplify())
								c.FixAs[D]("b")
								bIsZero := c.Assume()
								c.Take(c.Term("Q.zero"))
								c.Show(
									"Q.zero lies in Q.terms(0), and Q.d(0) and p(0) keep zero",
									ByChase(Depth(0), middleModules, quotientModules, middleCoboundaryHoms, pHoms, bIsZero))
							})
						b.Otherwise(
							"above degree 0 they are the image of Q''.d(m), and Q''.d(m)(y) "+
								"is p(m + 1)(Q.d(m)(x)) for a lift x of y, which Q.d(m + 1) kills",
							func(c *Argument, positive Fact) {
								_, isSuc := c.ObtainAs[Nat](
									"a positive degree is a successor",
									"∃m:num. n = m + 1",
									By(positive, nat_arith.NonzeroIsSucc.At(n)))
								c.Do(isSuc.Rw(), Simp(Fwd(Read(CoboundariesSucc, quotient))))
								c.Do(SplitConj(
									Case(
										"Q''.zero = Q''.d(m)(Q''.zero) is a coboundary",
										ByChase(Depth(0), quotientModules, quotientCoboundaryHoms)),
									Case(
										"a coboundary Q''.d(m)(y) lifts to Q.d(m)(x)",
										Derive(func(d *Argument) {
											d.FixAs[D]("b")
											coboundary := d.Assume()
											_, yIs := d.Obtain(
												"b is Q''.d(m)(y) for a y of Q''.terms(m)",
												"∃y:D. b = Q''.d(m)(y) ∧ y ∈ Q''.terms(m)",
												By(coboundary, set_basic.InImage))
											_, xIs := d.Obtain(
												"y is p(m)(x) for an x of Q.terms(m), p(m) being onto",
												"∃x:C. x ∈ Q.terms(m) ∧ p(m)(x) = y",
												ByChase(Depth(1), middleModules, quotientModules, pHoms, exact, yIs))
											d.Take(d.Term("Q.d(m)(x)"))
											d.Show(
												"Q.d(m)(x) lies in Q.terms(m + 1), Q.d(m + 1) kills "+
													"it, and p(m + 1)(Q.d(m)(x)) = Q''.d(m)(p(m)(x)) = b",
												ByChase(
													Depth(0),
													middleModules,
													quotientModules,
													middleCoboundaryHoms,
													quotientCoboundaryHoms,
													CochainCoboundaryTwice.Read(middle),
													pHoms,
													pSquare,
													xIs,
													yIs))
										})),
								))
							})
					})),
				"Q''.zero is a coboundary of Q''",
				"a coboundary of Q'' lifts to an element of Q.terms(n) that Q.d(n) kills")
			zeroIn, lifts := coboundaryFacts[0], coboundaryFacts[1]

			ownClass := a.Have(
				"p(n)(u) = z lies in the class of z, as z + Q''.zero",
				"p(n)(u) ∈ left_coset(Q''.add, z, coboundaries(Q'', n))",
				Derive(func(b *Argument) {
					b.Do(Simp(
						Fwd(group.LeftCosetDef.Inst[D]()),
						Fwd(set_basic.InImage.Inst(TypeBinder.BindA[D](), TypeBinder.BindB[D]()))))
					b.Take(b.Term("Q''.zero"))
					b.Show(
						"p(n)(u) = z = z + Q''.zero, and Q''.zero is a coboundary",
						ByChase(Depth(0), middleModules, quotientModules, pHoms, uIn, uLifts, zeroIn))
				}))

			targetCoboundaries := a.Have(
				"the coboundaries of Q' at n + 1 are the image of Q'.d(n)",
				"coboundaries(Q', n + 1) = image(Q'.d(n), Q'.terms(n))",
				By(Read(CoboundariesSucc, sub).At(n)))

			// The map's value is the class of the chosen pull-back.
			a.Do(Simp(Fwd(CoconnectingHomDef)), targetCoboundaries.Rw())
			_, chosen := a.ObtainChosen(
				"w pulls back Q.d(n)(u), and u lifts a member of the class",
				"∃w₁:B. "+
					"    w₁ ∈ Q'.terms(n + 1) ∧ "+
					"    (∃u₁:C. "+
					"        u₁ ∈ Q.terms(n) ∧ "+
					"        p(n)(u₁) ∈ left_coset(Q''.add, z, coboundaries(Q'', n)) ∧ "+
					"        i(n + 1)(w₁) = Q.d(n)(u₁))",
				wIn,
				uIn,
				wPulls,
				ownClass)
			pullBack := a.Conjuncts(
				chosen,
				"the chosen w₁ lies in Q'.terms(n + 1)",
				"w₁ pulls back Q.d(n)(u₁) for a lift u₁ of a member of the class")
			_, lift := a.Unpack(pullBack[1])
			lifted := a.Conjuncts(
				lift,
				"u₁ lies in Q.terms(n)",
				"p(n)(u₁) lies in the class of z",
				"i(n + 1)(w₁) = Q.d(n)(u₁)")
			_, member := a.Obtain(
				"p(n)(u₁) is z + b for a coboundary b of Q'' at n",
				"∃b:D. p(n)(u₁) = Q''.add(z, b) ∧ b ∈ coboundaries(Q'', n)",
				By(a.Unfolded(lifted[1], group.LeftCosetDef), set_basic.InImage))
			_, lifting := a.Obtain(
				"b is p(n)(c) for a c of Q.terms(n) that Q.d(n) kills",
				"∃c:C. c ∈ Q.terms(n) ∧ Q.d(n)(c) = Q.zero ∧ p(n)(c) = b",
				By(lifts, member))
			images := a.Have(
				"the image of Q'.d(n) is a submodule of Q'.terms(n + 1)",
				"submodule(R, complex_module(Q', n + 1), image(Q'.d(n), Q'.terms(n)))",
				Derive(func(b *Argument) {
					hom := b.Have(
						"Q'.d(n) is a homomorphism of the degree modules",
						"module_homomorphism(R, complex_module(Q', n), complex_module(Q', n + 1), Q'.d(n))",
						By(subCoboundaryHoms.At(n)))
					b.Show(
						"so its image is a submodule of its target module",
						By(module_homomorphism.ImageSubmodule.Read(hom)))
				}))
			a.Show(
				"p(n) kills u₁ − u − c, so it is i(n)(v), and i(n + 1)(w₁ − w) = "+
					"i(n + 1)(Q'.d(n)(v)): w₁ − w = Q'.d(n)(v), i(n + 1) being one-to-one",
				ByChase(
					Depth(1),
					subModules,
					middleModules,
					quotientModules,
					subCoboundaryHoms,
					middleCoboundaryHoms,
					iHoms,
					pHoms,
					iSquare,
					exact,
					uIn,
					uLifts,
					wIn,
					wPulls,
					pullBack[0],
					lifted[0],
					lifted[2],
					member,
					lifting,
					images))
		}),
})}

// CoconnectingHom — a quotient cocycle is related to the cocycle pulled
// back from its lift's coboundary. Sums and scalar multiples of lifts keep
// this relation, and its coset values give the coconnecting homomorphism.
var CoconnectingHom = coconnectingHomThm{family.Add(registry.ProofEntry{
	Name: "CoconnectingHom",
	Key:  "prop_ce64a203d5ae6b4a",
	Build: ShortExactCochainComplexes.Law("∀n:num. "+
		"    module_homomorphism(R, "+
		"        quotient_module(restrict_module(complex_module(Q'', n), cocycles(Q'', n)), "+
		"            coboundaries(Q'', n)), "+
		"        quotient_module(restrict_module(complex_module(Q', n + 1), cocycles(Q', n + 1)), "+
		"            coboundaries(Q', n + 1)), "+
		"        coconnecting_hom(Q', Q, i, p, n))",
		func(a *Argument, S ShortExactCochainComplexesFact[on.R], n *Expr[Nat]) {
			sub, middle, quotient :=
				ShortExactCochainSubComplex.Read(S),
				ShortExactCochainMiddleComplex.Read(S),
				ShortExactCochainQuotientComplex.Read(S)
			iHoms := CochainMapHom.Read(ShortExactCochainInclusionMap.Read(S))
			pHoms := CochainMapHom.Read(ShortExactCochainProjectionMap.Read(S))
			dHoms := CochainCoboundaryHom.Read(middle)
			quotientAt := a.Have(
				"the source degree is a module",
				"module_on(R, complex_module(Q'', n))",
				By(CochainModules.Read(quotient)))
			subAt := a.Have(
				"the target degree is a module",
				"module_on(R, complex_module(Q', n + 1))",
				By(CochainModules.Read(sub)))
			quotientDifferential := a.Have(
				"the source differential is linear",
				"module_homomorphism(R, complex_module(Q'', n), complex_module(Q'', n + 1), Q''.d(n))",
				By(CochainCoboundaryHom.Read(quotient)))
			source := a.Have(
				"source cocycles form a module",
				"module_on(R, restrict_module(complex_module(Q'', n), cocycles(Q'', n)))",
				By(
					submodule.SubmoduleModuleOn.Read(quotientAt),
					CocyclesKernel.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[D]()),
					module_homomorphism.KernelSubmodule.Read(quotientDifferential)))
			quotientBoundaries := a.Have(
				"source coboundaries form a submodule",
				"submodule(R, complex_module(Q'', n), coboundaries(Q'', n))",
				Derive(func(b *Argument) {
					b.Cases(b.Term("n = 0"))
					b.When(
						"at degree zero the coboundaries form the zero submodule",
						func(c *Argument, isZero Fact) {
							c.Do(isZero.Rw(), Unfold(CoboundariesDef))
							c.Show(
								"the singleton zero is a submodule",
								By(submodule.ZeroSubmodule.Read(c.Hyp("module_on(R, complex_module(Q'', 0))"))))
						})
					b.Otherwise(
						"at a successor degree the coboundaries form the differential's image",
						func(c *Argument, positive Fact) {
							_, isSuc := c.ObtainAs[Nat](
								"a positive degree is a successor",
								"∃m:num. n = m + 1",
								By(positive, nat_arith.NonzeroIsSucc))
							c.Do(isSuc.Rw(), Simp(
								Fwd(CoboundariesSucc.Read(quotient)),
								Fwd(ComplexModuleDef.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[D]()))))
							differential := c.Have(
								"the preceding differential is linear",
								"module_homomorphism(R, complex_module(Q'', m), complex_module(Q'', m + 1), Q''.d(m))",
								By(CochainCoboundaryHom.Read(quotient)))
							c.Show(
								"the image is a submodule",
								By(
									module_homomorphism.ImageSubmodule.Read(differential),
									ComplexModuleDef.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[D]())))
						})
				}))
			quotientBoundaryCycles := a.Have(
				"source coboundaries are cocycles",
				"coboundaries(Q'', n) ⊆ cocycles(Q'', n)",
				Derive(func(b *Argument) {
					b.Cases(b.Term("n = 0"))
					b.When(
						"the zero coboundary is a cocycle",
						func(c *Argument, isZero Fact) {
							c.Do(isZero.Rw(), Unfold(CoboundariesDef), Unfold(CocyclesDef))
							zero := c.Have(
								"zero belongs to the source degree and the differential kills it",
								"Q''.zero ∈ Q''.terms(0) ∧ Q''.d(0)(Q''.zero) = Q''.zero",
								ByChase(Depth(0), CochainModules.Read(quotient), CochainCoboundaryHom.Read(quotient)))
							c.Show(
								"the singleton zero lies in the cocycles",
								BySets(zero))
						})
					b.Otherwise(
						"two consecutive coboundaries vanish",
						func(c *Argument, positive Fact) {
							_, isSuc := c.ObtainAs[Nat](
								"a positive degree is a successor",
								"∃m:num. n = m + 1",
								By(positive, nat_arith.NonzeroIsSucc))
							c.Do(isSuc.Rw(), Simp(
								Fwd(CoboundariesSucc.Read(quotient)),
								Fwd(CocyclesDef.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[D]()))))
							killed := c.Have(
								"the image of the preceding differential lies in this differential's kernel",
								"∀u:D. u ∈ Q''.terms(m) ⇒ Q''.d(m)(u) ∈ Q''.terms(m + 1) ∧ Q''.d(m + 1)(Q''.d(m)(u)) = Q''.zero",
								ByChase(
									Depth(0),
									CochainModules.Read(quotient),
									CochainCoboundaryHom.Read(quotient),
									CochainCoboundaryTwice.Read(quotient)))
							c.Show(
								"the coboundary image lies in the cocycles",
								BySets(killed))
						})
				}))
			sourceBoundaries := a.Have(
				"source coboundaries form a submodule of cocycles",
				"submodule(R, restrict_module(complex_module(Q'', n), cocycles(Q'', n)), coboundaries(Q'', n))",
				By(quotientBoundaries, quotientBoundaryCycles, submodule.SubmoduleRestrict))
			subDifferential := a.Have(
				"the target differential is linear",
				"module_homomorphism(R, complex_module(Q', n + 1), complex_module(Q', n + 1 + 1), Q'.d(n + 1))",
				By(CochainCoboundaryHom.Read(sub)))
			target := a.Have(
				"target cocycles form a module",
				"module_on(R, restrict_module(complex_module(Q', n + 1), cocycles(Q', n + 1)))",
				By(
					submodule.SubmoduleModuleOn.Read(subAt),
					CocyclesKernel.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[B]()),
					module_homomorphism.KernelSubmodule.Read(subDifferential)))
			subBoundaries := a.Have(
				"target coboundaries form a submodule",
				"submodule(R, complex_module(Q', n + 1), coboundaries(Q', n + 1))",
				Simp(Fwd(CoboundariesSucc.Read(sub)), Fwd(ComplexModuleDef)),
				Derive(func(b *Argument) {
					differential := b.Have(
						"the preceding differential is linear",
						"module_homomorphism(R, complex_module(Q', n), complex_module(Q', n + 1), Q'.d(n))",
						By(CochainCoboundaryHom.Read(sub)))
					b.Show(
						"the image is a submodule",
						By(
							module_homomorphism.ImageSubmodule.Read(differential),
							ComplexModuleDef.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[B]())))
				}))
			subBoundaryCycles := a.Have(
				"target coboundaries are cocycles",
				"coboundaries(Q', n + 1) ⊆ cocycles(Q', n + 1)",
				Simp(Fwd(CoboundariesSucc.Read(sub)), Fwd(CocyclesDef)),
				Derive(func(b *Argument) {
					killed := b.Have(
						"the image of the preceding differential lies in this differential's kernel",
						"∀u:B. u ∈ Q'.terms(n) ⇒ Q'.d(n)(u) ∈ Q'.terms(n + 1) ∧ Q'.d(n + 1)(Q'.d(n)(u)) = Q'.zero",
						ByChase(
							Depth(0),
							CochainModules.Read(sub),
							CochainCoboundaryHom.Read(sub),
							CochainCoboundaryTwice.Read(sub)))
					b.Show(
						"the coboundary image lies in the cocycles",
						BySets(killed))
				}))
			targetBoundaries := a.Have(
				"target coboundaries form a submodule of cocycles",
				"submodule(R, "+
					"    restrict_module(complex_module(Q', n + 1), cocycles(Q', n + 1)), "+
					"    coboundaries(Q', n + 1))",
				By(subBoundaries, subBoundaryCycles, submodule.SubmoduleRestrict))

			relationTotal := a.Have(
				"every source cocycle has a related target cocycle",
				Statement{
					Binders: "∀z:D.",
					Hypotheses: []string{
						"z ∈ cocycles(Q'', n)",
					},
					Conclusion: "∃w:B. " +
						"    w ∈ cocycles(Q', n + 1) ∧ (∃u:C. u ∈ Q.terms(n) ∧ p(n)(u) = z ∧ i(n + 1)(w) = Q.d(n)(u))",
				},
				By(CocycleLiftPullback.Read(S)))
			relationAdd := a.Have(
				"sums of related pairs are related",
				Statement{
					Binders: "∀z₁ z₂:D. ∀w₁ w₂:B.",
					Hypotheses: []string{
						"z₁ ∈ cocycles(Q'', n)",
						"z₂ ∈ cocycles(Q'', n)",
						"w₁ ∈ cocycles(Q', n + 1)",
						"w₂ ∈ cocycles(Q', n + 1)",
						"∃u₁:C. u₁ ∈ Q.terms(n) ∧ p(n)(u₁) = z₁ ∧ i(n + 1)(w₁) = Q.d(n)(u₁)",
						"∃u₂:C. u₂ ∈ Q.terms(n) ∧ p(n)(u₂) = z₂ ∧ i(n + 1)(w₂) = Q.d(n)(u₂)",
					},
					Conclusion: "∃u:C. " +
						"    u ∈ Q.terms(n) ∧ p(n)(u) = Q''.add(z₁, z₂) ∧ i(n + 1)(Q'.add(w₁, w₂)) = Q.d(n)(u)",
				},
				Derive(func(b *Argument) {
					b.FixAs[D]("z₁")
					b.FixAs[D]("z₂")
					b.FixAs[B]("w₁")
					b.FixAs[B]("w₂")
					related := b.Assume()
					members := b.Have(
						"the target cocycles lie in the target degree",
						"w₁ ∈ Q'.terms(n + 1) ∧ w₂ ∈ Q'.terms(n + 1)",
						BySets(related, CocyclesDef.At(b.TermAs[ComplexOps[A, B]]("Q'"), b.TermAs[Nat]("n + 1"))))
					_, firstLift := b.ObtainAs[C](
						"the first related pair has a lift",
						"∃u₁:C. u₁ ∈ Q.terms(n) ∧ p(n)(u₁) = z₁ ∧ i(n + 1)(w₁) = Q.d(n)(u₁)",
						By(related))
					_, secondLift := b.ObtainAs[C](
						"the second related pair has a lift",
						"∃u₂:C. u₂ ∈ Q.terms(n) ∧ p(n)(u₂) = z₂ ∧ i(n + 1)(w₂) = Q.d(n)(u₂)",
						By(related))
					b.Take(b.TermAs[C]("Q.add(u₁, u₂)"))
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
						"z ∈ cocycles(Q'', n)",
						"w ∈ cocycles(Q', n + 1)",
						"∃u:C. u ∈ Q.terms(n) ∧ p(n)(u) = z ∧ i(n + 1)(w) = Q.d(n)(u)",
					},
					Conclusion: "∃u:C. u ∈ Q.terms(n) ∧ p(n)(u) = Q''.smul(c, z) ∧ i(n + 1)(Q'.smul(c, w)) = Q.d(n)(u)",
				},
				Derive(func(b *Argument) {
					b.FixAs[A]("c")
					b.FixAs[D]("z")
					b.FixAs[B]("w")
					related := b.Assume()
					member := b.Have(
						"the target cocycle lies in the target degree",
						"w ∈ Q'.terms(n + 1)",
						Derive(func(c *Argument) {
							c.Show(
								"a cocycle lies in its degree",
								BySets(related, CocyclesDef.At(c.TermAs[ComplexOps[A, B]]("Q'"), c.TermAs[Nat]("n + 1"))))
						}))
					_, lift := b.ObtainAs[C](
						"the related pair has a lift",
						"∃u:C. u ∈ Q.terms(n) ∧ p(n)(u) = z ∧ i(n + 1)(w) = Q.d(n)(u)",
						By(related))
					pHom := b.Have(
						"the projection is linear in the source degree",
						"module_homomorphism(R, complex_module(Q, n), complex_module(Q'', n), p(n))",
						By(pHoms))
					iHom := b.Have(
						"the inclusion is linear in the target degree",
						"module_homomorphism(R, complex_module(Q', n + 1), complex_module(Q, n + 1), i(n + 1))",
						By(iHoms))
					dHom := b.Have(
						"the coboundary is linear",
						"module_homomorphism(R, complex_module(Q, n), complex_module(Q, n + 1), Q.d(n))",
						By(dHoms))
					projects := b.Have(
						"u lifts z",
						"p(n)(u) = z",
						By(lift))
					pullsBack := b.Have(
						"w pulls back the coboundary of u",
						"i(n + 1)(w) = Q.d(n)(u)",
						By(lift))
					scaledLift := b.Have(
						"the scaled lift projects to the scaled cocycle",
						"p(n)(Q.smul(c, u)) = Q''.smul(c, z)",
						CalcEq(
							Leg(
								b.TermAs[D]("Q''.smul(c, p(n)(u))"),
								"the projection preserves scaling",
								By(module_homomorphism.HomSmul.Read(pHom), related, lift)),
							FinalLeg(
								"u projects to z",
								projects.Rw(),
								Basic()),
						))
					scaledPullback := b.Have(
						"the scaled target cocycle pulls back the coboundary of the scaled lift",
						"i(n + 1)(Q'.smul(c, w)) = Q.d(n)(Q.smul(c, u))",
						CalcEq(
							Leg(
								b.TermAs[C]("Q.smul(c, i(n + 1)(w))"),
								"the inclusion preserves scaling",
								By(module_homomorphism.HomSmul.Read(iHom), related, member)),
							Leg(
								b.TermAs[C]("Q.smul(c, Q.d(n)(u))"),
								"w pulls back the coboundary",
								pullsBack.Rw(),
								Basic()),
							FinalLeg(
								"the coboundary preserves scaling",
								By(module_homomorphism.HomSmul.Read(dHom), related, lift)),
						))
					b.Take(b.TermAs[C]("Q.smul(c, u)"))
					b.Show(
						"the scaled lift realizes the scaled related pair",
						ByChase(Depth(0), CochainModules.Read(middle), related, lift, scaledLift, scaledPullback))
				}))
			relationValue := a.Have(
				"related cocycles compute the coconnecting map on their classes",
				Statement{
					Binders: "∀z:D. ∀w:B.",
					Hypotheses: []string{
						"z ∈ cocycles(Q'', n)",
						"w ∈ cocycles(Q', n + 1)",
						"∃u:C. u ∈ Q.terms(n) ∧ p(n)(u) = z ∧ i(n + 1)(w) = Q.d(n)(u)",
					},
					Conclusion: "coconnecting_hom(Q', Q, i, p, n, left_coset(Q''.add, z, coboundaries(Q'', n))) = " +
						"left_coset(Q'.add, w, coboundaries(Q', n + 1))",
				},
				Derive(func(b *Argument) {
					b.FixAs[D]("z")
					b.FixAs[B]("w")
					related := b.Assume()
					member := b.Have(
						"the target cocycle lies in the target degree",
						"w ∈ Q'.terms(n + 1)",
						Derive(func(c *Argument) {
							c.Show(
								"a cocycle lies in its degree",
								BySets(related, CocyclesDef.At(c.TermAs[ComplexOps[A, B]]("Q'"), c.TermAs[Nat]("n + 1"))))
						}))
					_, lift := b.ObtainAs[C](
						"the related pair has a lift",
						"∃u:C. u ∈ Q.terms(n) ∧ p(n)(u) = z ∧ i(n + 1)(w) = Q.d(n)(u)",
						By(related))
					b.Show(
						"the lift computes the image class",
						By(CoconnectingHomCoset.Read(S), related, member, lift))
				}))
			a.Show(
				"the relation induces a linear map on cohomology",
				By(
					source,
					target,
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
							"λz:D. λw:B. ∃u:C. u ∈ Q.terms(n) ∧ p(n)(u) = z ∧ i(n + 1)(w) = Q.d(n)(u)"))))
		}),
})}

// CoLongExactStart — the long exact sequence starts one-to-one: in degree
// 0 the map the injection induces on cohomology is one-to-one. The
// coboundaries of degree 0 are the zero alone, so a class of Q there is its
// one element, and i* sends the class of a cocycle w of Q' to the class
// {i(0)(w)}. Two classes of cocycles w₁, w₂ with one image then have
// i(0)(w₁) = i(0)(w₂), and i(0), one-to-one on Q'.terms(0) by the
// degreewise exactness, makes w₁ = w₂.
var CoLongExactStart = coLongExactStartThm{family.Add(registry.ProofEntry{
	Name: "CoLongExactStart",
	Key:  "prop_c56a0dd86b18c627",
	Build: ShortExactCochainComplexes.Law("injective_on(cohomology(Q', 0), cohomology_map(Q, i, 0))",
		func(a *Argument, S ShortExactCochainComplexesFact[on.R]) {
			sub, middle, iCochainMap :=
				ShortExactCochainSubComplex.Read(S),
				ShortExactCochainMiddleComplex.Read(S),
				ShortExactCochainInclusionMap.Read(S)
			iHoms := CochainMapHom.Read(iCochainMap)
			exact := a.Unfolded(Read(ShortExactCochainDegreewise, S), ExactComplexesDef)
			i, zero := a.TermAs[Fun2[Nat, B, C]]("i"), a.TermAs[Nat]("0")

			singleton := a.Have(
				"a class of Q in degree 0 is its one element, the coboundaries there being the zero alone",
				"∀x:C. x ∈ Q.terms(0) ⇒ left_coset(Q.add, x, coboundaries(Q, 0)) = {x}",
				Derive(func(b *Argument) {
					b.FixAs[C]("x")
					xIn := b.Assume()
					sum := b.Have(
						"adding Q.zero leaves x, Q.terms(0) being a module",
						"Q.add(x, Q.zero) = x",
						ByChase(Depth(0), CochainModules.Read(middle), xIn))
					b.Show(
						"the coboundaries of degree 0 are {Q.zero}, and its image under y ↦ x + y is {x}",
						Unfold(CoboundariesDef),
						Unfold(group.LeftCosetDef),
						BySets(sum))
				}))

			// Two classes s and t of degree 0 with one image under i*.
			a.Do(Simp(Fwd(functions.InjectiveOnDef)))
			a.FixAs[Set[B]]("s")
			a.FixAs[Set[B]]("t")
			given := a.Conjuncts(
				a.Assume(),
				"s is a class of Q' in degree 0",
				"so is t",
				"i* sends s and t to one class")
			w1, sIs := a.ObtainAs[B](
				"s is the class of a cocycle w₁",
				"∃w₁:B. s = left_coset(Q'.add, w₁, coboundaries(Q', 0)) ∧ w₁ ∈ cocycles(Q', 0)",
				By(given[0], InCohomology.Read(sub)))
			sClass := a.Conjuncts(
				sIs,
				"s is the class of w₁",
				"w₁ is a cocycle of Q'")
			w2, tIs := a.ObtainAs[B](
				"t is the class of a cocycle w₂",
				"∃w₂:B. t = left_coset(Q'.add, w₂, coboundaries(Q', 0)) ∧ w₂ ∈ cocycles(Q', 0)",
				By(given[1], InCohomology.Read(sub)))
			tClass := a.Conjuncts(
				tIs,
				"t is the class of w₂",
				"w₂ is a cocycle of Q'")
			members := a.Have(
				"w₁ and w₂ lie in Q'.terms(0)",
				"w₁ ∈ Q'.terms(0) ∧ w₂ ∈ Q'.terms(0)",
				BySets(a.Unfolded(sClass[1], CocyclesDef), a.Unfolded(tClass[1], CocyclesDef)))
			images := a.Have(
				"so i(0)(w₁) and i(0)(w₂) lie in Q.terms(0)",
				"i(0)(w₁) ∈ Q.terms(0) ∧ i(0)(w₂) ∈ Q.terms(0)",
				ByChase(Depth(0), iHoms, members))

			sImage := a.Have(
				"i* sends s to {i(0)(w₁)}",
				"cohomology_map(Q, i, 0, s) = {i(0)(w₁)}",
				CalcEq(
					Leg(
						a.TermAs[Set[C]]("left_coset(Q.add, i(0)(w₁), coboundaries(Q, 0))"),
						"i* sends the class of w₁ to the class of i(0)(w₁)",
						sClass[0].Rw(),
						By(Read(CohomologyMapCoset, sub, middle).At(i, zero, w1), iCochainMap, sClass[1])),
					FinalLeg(
						"a class of Q in degree 0 is its one element",
						By(singleton.At(a.TermAs[C]("i(0)(w₁)")), images)),
				))
			tImage := a.Have(
				"i* sends t to {i(0)(w₂)}",
				"cohomology_map(Q, i, 0, t) = {i(0)(w₂)}",
				CalcEq(
					Leg(
						a.TermAs[Set[C]]("left_coset(Q.add, i(0)(w₂), coboundaries(Q, 0))"),
						"i* sends the class of w₂ to the class of i(0)(w₂)",
						tClass[0].Rw(),
						By(Read(CohomologyMapCoset, sub, middle).At(i, zero, w2), iCochainMap, tClass[1])),
					FinalLeg(
						"a class of Q in degree 0 is its one element",
						By(singleton.At(a.TermAs[C]("i(0)(w₂)")), images)),
				))
			oneSet := a.Have(
				"so the one-point images of s and t agree",
				"{i(0)(w₁)} = {i(0)(w₂)}",
				CalcEq(
					Leg(
						a.TermAs[Set[C]]("cohomology_map(Q, i, 0, s)"),
						"i* sends s to {i(0)(w₁)}",
						By(Normalized, sImage)),
					Leg(
						a.TermAs[Set[C]]("cohomology_map(Q, i, 0, t)"),
						"s and t have one image",
						By(given[2])),
					FinalLeg(
						"i* sends t to {i(0)(w₂)}",
						By(tImage)),
				))
			imagesAgree := a.Have(
				"two one-point sets that agree have one point",
				"i(0)(w₁) = i(0)(w₂)",
				BySets(oneSet))
			same := a.Have(
				"i(0) is one-to-one on Q'.terms(0), so w₁ = w₂",
				"w₁ = w₂",
				By(exact, members, imagesAgree, functions.InjectiveOnDef))
			a.Show(
				"so s and t are the class of one cocycle",
				sClass[0].Rw(),
				tClass[0].Rw(),
				same.Rw(),
				Basic())
		}),
})}

// CoLongExactMiddle — the long exact sequence at H^n(Q): the image of i*
// is the kernel of p*, an equation of two sets of classes read one class
// s at a time. Write N and M for the coboundaries of Q and of the
// quotient complex at n: the zero class of the quotient's cohomology is
// M, the class of its zero. A class in the image is i* of the class of a
// cocycle w of Q', which is the class of the cocycle i(n)(w), and p*
// sends that to the class of p(n)(i(n)(w)), the zero by exactness at
// Q.terms(n). Conversely a class of a cocycle u that p* sends to M has p(n)(u)
// in M, and a coboundary of the quotient is p(n)(c) for a coboundary c of
// Q that Q.d(n) kills: the zero at degree 0, and above it Q.d(m)(x) for a
// lift x of the y whose coboundary in the quotient is p(n)(u). Then p(n)
// kills u − c, so u − c is i(n)(w) for a w of Q'.terms(n); w is a cocycle,
// since i(n + 1)(Q'.d(n)(w)) = Q.d(n)(u − c) is zero and i(n + 1) is
// one-to-one; and u = i(n)(w) + c has the class of i(n)(w), i* of the
// class of w.
var CoLongExactMiddle = coLongExactMiddleThm{family.Add(registry.ProofEntry{
	Name: "CoLongExactMiddle",
	Key:  "prop_20dc3cda61e06f56",
	Build: ShortExactCochainComplexes.Law("∀n:num. "+
		"    exact_at(coboundaries(Q'', n), "+
		"        cohomology(Q', n), "+
		"        cohomology(Q, n), "+
		"        cohomology_map(Q, i, n), "+
		"        cohomology_map(Q'', p, n))",
		func(a *Argument, S ShortExactCochainComplexesFact[on.R], n *Expr[Nat]) {
			parts := []Fact{
				Read(ShortExactCochainSubComplex, S),
				Read(ShortExactCochainMiddleComplex, S),
				Read(ShortExactCochainQuotientComplex, S),
				Read(ShortExactCochainInclusionMap, S),
				Read(ShortExactCochainProjectionMap, S),
				Read(ShortExactCochainDegreewise, S),
			}
			sub, middle, quotient, iCochainMap, pCochainMap := parts[0], parts[1], parts[2], parts[3], parts[4]
			i, p := a.TermAs[Fun2[Nat, B, C]]("i"), a.TermAs[Fun2[Nat, C, D]]("p")
			iClauses := []Fact{Read(CochainMapHom, iCochainMap), Read(CochainMapSquare, iCochainMap)}
			pClauses := []Fact{Read(CochainMapHom, pCochainMap), Read(CochainMapSquare, pCochainMap)}
			iHoms, iSquare, pHoms, pSquare := iClauses[0], iClauses[1], pClauses[0], pClauses[1]
			exact := a.Unfolded(parts[5], ExactComplexesDef)
			subModules, middleModules, quotientModules :=
				CochainModules.Read(sub), CochainModules.Read(middle), CochainModules.Read(quotient)
			subCoboundaryHoms, middleCoboundaryHoms, quotientCoboundaryHoms :=
				CochainCoboundaryHom.Read(sub),
				CochainCoboundaryHom.Read(middle),
				CochainCoboundaryHom.Read(quotient)

			coboundaryFacts := a.Conjuncts(
				a.Have(
					"quotient coboundaries include zero and lift to "+
						"coboundaries of Q; adding a coboundary leaves a class",
					"Q''.zero ∈ coboundaries(Q'', n) ∧ "+
						"(∀b:D. b ∈ coboundaries(Q'', n) ⇒ b ∈ Q''.terms(n)) ∧ "+
						"(∀b:D. "+
						"    b ∈ coboundaries(Q'', n) ⇒ "+
						"    ∃c:C. c ∈ coboundaries(Q, n) ∧ c ∈ Q.terms(n) ∧ Q.d(n)(c) = Q.zero ∧ p(n)(c) = b) ∧ "+
						"(∀x c:C. "+
						"    x ∈ Q.terms(n) ∧ c ∈ coboundaries(Q, n) ⇒ "+
						"    left_coset(Q.add, Q.add(x, c), coboundaries(Q, n)) = "+
						"    left_coset(Q.add, x, coboundaries(Q, n)))",
					Derive(func(b *Argument) {
						b.Cases(b.Term("n = 0"))
						b.When(
							"at degree 0 the coboundaries are the zeros alone: "+
								"Q.zero lifts Q''.zero, and adding Q.zero moves nothing",
							func(c *Argument, isZero Fact) {
								c.Do(isZero.Rw(), Unfold(CoboundariesDef), Simp(
									Fwd(set_basic.InSing.Inst[D]()),
									Fwd(set_basic.InSing.Inst[C]())), TrivialSimplify())
								c.Do(SplitConjAll(
									Case(
										"Q''.zero lies in Q''.terms(0)",
										Derive(func(d *Argument) {
											d.FixAs[D]("b")
											bIsZero := d.Assume()
											d.Show(
												"b is Q''.zero, the zero of Q''.terms(0)",
												ByChase(Depth(0), quotientModules, bIsZero))
										})),
									Case(
										"Q.zero lifts Q''.zero",
										Derive(func(d *Argument) {
											d.FixAs[D]("b")
											bIsZero := d.Assume()
											d.Take(d.Term("Q.zero"))
											d.Show(
												"Q.zero lies in Q.terms(0), and Q.d(0) and p(0) keep zero",
												ByChase(Depth(0), Normalized, middleModules, quotientModules, middleCoboundaryHoms, pHoms, bIsZero))
										})),
									Case(
										"x + Q.zero is x",
										Derive(func(d *Argument) {
											d.FixAs[C]("x")
											d.FixAs[C]("c")
											given := d.Assume()
											same := d.Have(
												"x + c is x, c being Q.zero",
												"Q.add(x, c) = x",
												ByChase(Depth(0), middleModules, given))
											d.Show(
												"so the two classes agree",
												same.Rw(),
												Basic())
										})),
								))
							})
						b.Otherwise(
							"above degree 0 they are the images of Q''.d(m) and Q.d(m), "+
								"Q''.d(m)(y) is p(m + 1)(Q.d(m)(x)) for a lift x of y",
							func(c *Argument, positive Fact) {
								m, isSuc := c.ObtainAs[Nat](
									"a positive degree is a successor",
									"∃m:num. n = m + 1",
									By(positive, nat_arith.NonzeroIsSucc.At(n)))
								c.Do(isSuc.Rw(), Simp(Fwd(Read(CoboundariesSucc, middle)), Fwd(Read(CoboundariesSucc, quotient))))
								c.Do(SplitConjAll(
									Case(
										"Q''.zero = Q''.d(m)(Q''.zero) is a coboundary",
										ByChase(Depth(0), quotientModules, quotientCoboundaryHoms)),
									Case(
										"Q''.d(m) maps Q''.terms(m) into Q''.terms(m + 1)",
										Derive(func(d *Argument) {
											d.FixAs[D]("b")
											coboundary := d.Assume()
											d.Show(
												"b = Q''.d(m)(y) lies in Q''.terms(m + 1)",
												ByChase(Depth(0), quotientModules, quotientCoboundaryHoms, coboundary))
										})),
									Case(
										"a coboundary Q''.d(m)(y) lifts to Q.d(m)(x)",
										Derive(func(d *Argument) {
											d.FixAs[D]("b")
											coboundary := d.Assume()
											_, yIs := d.Obtain(
												"b is Q''.d(m)(y) for a y of Q''.terms(m)",
												"∃y:D. b = Q''.d(m)(y) ∧ y ∈ Q''.terms(m)",
												By(coboundary, set_basic.InImage))
											_, xIs := d.Obtain(
												"y is p(m)(x) for an x of Q.terms(m), p(m) being onto",
												"∃x:C. x ∈ Q.terms(m) ∧ p(m)(x) = y",
												ByChase(Depth(1), middleModules, quotientModules, pHoms, exact, yIs))
											d.Take(d.Term("Q.d(m)(x)"))
											d.Show(
												"Q.d(m)(x) is a coboundary of Q in Q.terms(m + 1), Q.d(m + "+
													"1) kills it, and p(m + 1)(Q.d(m)(x)) = Q''.d(m)(p(m)(x)) = b",
												ByChase(
													Depth(0),
													middleModules,
													quotientModules,
													middleCoboundaryHoms,
													quotientCoboundaryHoms,
													CochainCoboundaryTwice.Read(middle),
													pHoms,
													pSquare,
													xIs,
													yIs))
										})),
									Case(
										"x + Q.d(m)(v) has the class of x",
										Derive(func(d *Argument) {
											d.FixAs[C]("x")
											d.FixAs[C]("c")
											given := d.Assume()
											images := d.Have(
												"the image of Q.d(m) is a submodule of Q.terms(m + 1)",
												"submodule(R, complex_module(Q, m + 1), image(Q.d(m), Q.terms(m)))",
												Derive(func(e *Argument) {
													hom := e.Have(
														"Q.d(m) is a homomorphism of the degree modules",
														"module_homomorphism(R, complex_module(Q, m), complex_module(Q, m + 1), Q.d(m))",
														By(middleCoboundaryHoms.At(m)))
													e.Show(
														"so its image is a submodule of its target module",
														By(module_homomorphism.ImageSubmodule.Read(hom)))
												}))
											d.Show(
												"x + c and x differ by c, a member of the image",
												ByChase(Depth(0), middleModules, middleCoboundaryHoms, given, images))
										})),
								))
							})
					})),
				"Q''.zero is a coboundary of Q''",
				"a coboundary of Q'' lies in Q''.terms(n)",
				"a coboundary of Q'' lifts to a coboundary of Q that Q.d(n) kills",
				"adding a coboundary of Q leaves a class of Q")
			zeroIn, inQuotient, lifts, absorbs :=
				coboundaryFacts[0], coboundaryFacts[1], coboundaryFacts[2], coboundaryFacts[3]

			// The zero class of H^n(Q''): the coboundaries B'', the class of Q''.zero.
			quotientCoboundaries := a.Have(
				"so the coboundaries of Q'' lie in Q''.terms(n)",
				"coboundaries(Q'', n) ⊆ Q''.terms(n)",
				BySets(inQuotient))
			moduleAtN := a.Have(
				"Q''.terms(n) is a module",
				"module_on(R, complex_module(Q'', n))",
				By(quotientModules))
			groupAtN := a.Simplified(
				module.AddGroupOn.Read(moduleAtN),
				Fwd(module_record.ModuleAdditiveGroupDef))
			zeroClass := a.Have(
				"so the coboundaries of Q'' are the class of Q''.zero, "+
					"the identity of the additive group of Q''.terms(n)",
				"left_coset(Q''.add, Q''.zero, coboundaries(Q'', n)) = coboundaries(Q'', n)",
				By(group.LeftCosetOneOn.Read(groupAtN), quotientCoboundaries))

			// The two sets of classes of Q, a class s at a time: s is in the image of i*, or s is a class that p* sends to the zero class.
			a.Do(Simp(
				Fwd(module_homomorphism.ExactAtDef.Inst(
					TypeBinder.BindD[Set[D]](), TypeBinder.BindB[Set[B]](), TypeBinder.BindC[Set[C]]())),
				Fwd(set_basic.Extension.Inst[Set[C]]()),
				Fwd(group_homomorphism.InKernel.Inst(TypeBinder.BindA[Set[C]](), TypeBinder.BindB[Set[D]]()))))
			a.FixAs[Set[C]]("s")
			a.Iff()
			a.Forward(
				"i* sends the class of a cocycle w to the class of the cocycle "+
					"i(n)(w), and p* sends that to the class of p(n)(i(n)(w)) = Q''.zero",
				func(b *Argument, sIn Fact) {
					_, sIs := b.Obtain(
						"s is i*(t) for a class t of Q' at n",
						"∃t:set(B). s = cohomology_map(Q, i, n, t) ∧ t ∈ cohomology(Q', n)",
						By(sIn, set_basic.InImage.Inst(TypeBinder.BindA[Set[B]](), TypeBinder.BindB[Set[C]]())))
					sImage := b.Conjuncts(
						sIs,
						"s is i*(t)",
						"t is a class of Q' at n")
					w, tIs := b.ObtainAs[B](
						"t is the class of a cocycle w",
						"∃w:B. t = left_coset(Q'.add, w, coboundaries(Q', n)) ∧ w ∈ cocycles(Q', n)",
						By(sImage[1], InCohomology.Read(sub)))
					tClass := b.Conjuncts(
						tIs,
						"t is the class of w",
						"w is a cocycle of Q'")
					wCocycle := b.Have(
						"w lies in Q'.terms(n) and Q'.d(n) kills it",
						"w ∈ Q'.terms(n) ∧ Q'.d(n)(w) = Q'.zero",
						BySets(b.Unfolded(tClass[1], CocyclesDef)))
					mappedOpen := b.Have(
						"i(n)(w) lies in Q.terms(n), and Q.d(n)(i(n)(w)) = i(n + 1)(Q'.d(n)(w)) = Q.zero",
						"i(n)(w) ∈ Q.terms(n) ∧ Q.d(n)(i(n)(w)) = Q.zero",
						ByChase(Depth(0), subModules, middleModules, subCoboundaryHoms, iHoms, iSquare, wCocycle))
					mappedCocycle := b.Have(
						"so i(n)(w) is a cocycle of Q",
						"i(n)(w) ∈ cocycles(Q, n)",
						Simp(Fwd(CocyclesDef.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[C]()))),
						BySets(mappedOpen))
					mappedClass := b.Have(
						"and its class is a class of Q",
						"left_coset(Q.add, i(n)(w), coboundaries(Q, n)) ∈ cohomology(Q, n)",
						Simp(Fwd(InCohomology.Read(middle))),
						Derive(func(c *Argument) {
							c.Take(c.TermAs[C]("i(n)(w)"))
							c.Show(
								"the class of i(n)(w) is the class of the cocycle i(n)(w)",
								By(mappedCocycle))
						}))
					killed := b.Have(
						"p(n)(i(n)(w)) = Q''.zero, the sequence being exact at Q.terms(n)",
						"p(n)(i(n)(w)) = Q''.zero",
						ByChase(Depth(0), subModules, middleModules, quotientModules, iHoms, pHoms, exact, wCocycle))
					// i* sends the class of w to the class of i(n)(w), and p* sends that to the class of p(n)(i(n)(w)).
					iClass := b.Have(
						"i* sends the class of w to the class of i(n)(w)",
						"cohomology_map(Q, i, n, left_coset(Q'.add, w, coboundaries(Q', n))) = "+
							"left_coset(Q.add, i(n)(w), coboundaries(Q, n))",
						By(Read(CohomologyMapCoset, sub, middle).At(i, n, w), iCochainMap, tClass[1]))
					pClass := b.Have(
						"p* sends that class to the class of p(n)(i(n)(w))",
						"cohomology_map(Q'', p, n, left_coset(Q.add, i(n)(w), coboundaries(Q, n))) = "+
							"left_coset(Q''.add, p(n)(i(n)(w)), coboundaries(Q'', n))",
						By(
							Read(CohomologyMapCoset, middle, quotient).At(p, n, b.TermAs[C]("i(n)(w)")),
							pCochainMap,
							mappedCocycle))
					b.Do(sImage[0].Rw(), tClass[0].Rw(), iClass.Rw(), pClass.Rw())
					b.Show(
						"so s is the class of i(n)(w), and p* sends it to the class of Q''.zero, the zero class",
						killed.Rw(),
						By(mappedClass, zeroClass))
				})
			a.Backward(
				"p* sends the class of a cocycle u to zero: p(n)(u) = p(n)(c), c "+
					"a coboundary, u − c = i(n)(w), and i* sends the class of w to it",
				func(b *Argument, sIn Fact) {
					kernel := b.Conjuncts(
						sIn,
						"s is a class of Q at n",
						"p* sends s to the zero class")
					u, sIs := b.ObtainAs[C](
						"s is the class of a cocycle u",
						"∃u:C. s = left_coset(Q.add, u, coboundaries(Q, n)) ∧ u ∈ cocycles(Q, n)",
						By(kernel[0], InCohomology.Read(middle)))
					sClass := b.Conjuncts(
						sIs,
						"s is the class of u",
						"u is a cocycle of Q")
					uCocycle := b.Have(
						"u lies in Q.terms(n) and Q.d(n) kills it",
						"u ∈ Q.terms(n) ∧ Q.d(n)(u) = Q.zero",
						BySets(b.Unfolded(sClass[1], CocyclesDef)))
					imageZero := b.Have(
						"so the class of p(n)(u) is the zero class",
						"left_coset(Q''.add, p(n)(u), coboundaries(Q'', n)) = coboundaries(Q'', n)",
						CalcEq(
							Leg(
								b.TermAs[Set[D]]("cohomology_map(Q'', p, n, s)"),
								"the class of p(n)(u) is p*(s), s being the class of the cocycle u",
								sClass[0].Rw(),
								By(Read(CohomologyMapCoset, middle, quotient).At(p, n, u), pCochainMap, sClass[1])),
							FinalLeg(
								"which is the zero class",
								By(kernel[1])),
						))
					ownClass := b.Have(
						"p(n)(u) lies in its own class, as p(n)(u) + Q''.zero",
						"p(n)(u) ∈ left_coset(Q''.add, p(n)(u), coboundaries(Q'', n))",
						Derive(func(c *Argument) {
							c.Do(Simp(
								Fwd(group.LeftCosetDef.Inst[D]()),
								Fwd(set_basic.InImage.Inst(TypeBinder.BindA[D](), TypeBinder.BindB[D]()))))
							c.Take(c.Term("Q''.zero"))
							c.Show(
								"p(n)(u) = p(n)(u) + Q''.zero, and Q''.zero is a coboundary",
								ByChase(Depth(0), middleModules, quotientModules, pHoms, uCocycle, zeroIn))
						}))
					c, lifting := b.ObtainAs[C](
						"so p(n)(u), a coboundary of Q'', is p(n)(c) for a coboundary c of Q that Q.d(n) kills",
						"∃c:C. c ∈ coboundaries(Q, n) ∧ c ∈ Q.terms(n) ∧ Q.d(n)(c) = Q.zero ∧ p(n)(c) = p(n)(u)",
						By(lifts, ownClass, imageZero))
					cCoboundary := b.Conjuncts(
						lifting,
						"c is a coboundary of Q",
						"c lies in Q.terms(n)",
						"Q.d(n) kills c",
						"p(n)(c) = p(n)(u)")[0]
					w, wIs := b.ObtainAs[B](
						"p(n) kills u − c, so u − c is i(n)(w) for a w of "+
							"Q'.terms(n), the sequence being exact at Q.terms(n)",
						"∃w:B. w ∈ Q'.terms(n) ∧ i(n)(w) = Q.add(u, Q.neg(c))",
						ByChase(
							Depth(1),
							subModules,
							middleModules,
							quotientModules,
							iHoms,
							pHoms,
							exact,
							uCocycle,
							lifting))
					pull := b.Conjuncts(
						wIs,
						"w lies in Q'.terms(n)",
						"i(n)(w) = u − c")
					killed := b.Have(
						"i(n + 1)(Q'.d(n)(w)) = Q.d(n)(u − c) is zero and i(n + 1) is one-to-one, so Q'.d(n) kills w",
						"Q'.d(n)(w) = Q'.zero",
						ByChase(
							Depth(1),
							subModules,
							middleModules,
							subCoboundaryHoms,
							middleCoboundaryHoms,
							iHoms,
							iSquare,
							exact,
							uCocycle,
							lifting,
							wIs))
					wCocycle := b.Have(
						"so w is a cocycle of Q'",
						"w ∈ cocycles(Q', n)",
						Simp(Fwd(CocyclesDef.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[B]()))),
						BySets(pull[0], killed))
					sum := b.Conjuncts(
						b.Have(
							"i(n)(w) lies in Q.terms(n), and u = i(n)(w) + c",
							"i(n)(w) ∈ Q.terms(n) ∧ u = Q.add(i(n)(w), c)",
							ByChase(Depth(0), subModules, middleModules, iHoms, uCocycle, lifting, wIs)),
						"i(n)(w) lies in Q.terms(n)",
						"u = i(n)(w) + c")
					sameClass := b.Have(
						"u and i(n)(w) differ by the coboundary c, so they have one class",
						"left_coset(Q.add, u, coboundaries(Q, n)) = left_coset(Q.add, i(n)(w), coboundaries(Q, n))",
						sum[1].Rw(),
						By(absorbs.At(b.TermAs[C]("i(n)(w)"), c), sum[0], cCoboundary))
					wClass := b.Have(
						"the class of w is a class of Q'",
						"left_coset(Q'.add, w, coboundaries(Q', n)) ∈ cohomology(Q', n)",
						Simp(Fwd(InCohomology.Read(sub))),
						Derive(func(d *Argument) {
							d.Take(w)
							d.Show(
								"the class of w is the class of the cocycle w",
								By(wCocycle))
						}))
					iClass := b.Have(
						"i* sends the class of w to the class of i(n)(w)",
						"cohomology_map(Q, i, n, left_coset(Q'.add, w, coboundaries(Q', n))) = "+
							"left_coset(Q.add, i(n)(w), coboundaries(Q, n))",
						By(Read(CohomologyMapCoset, sub, middle).At(i, n, w), iCochainMap, wCocycle))
					b.Do(Simp(Fwd(set_basic.InImage.Inst(TypeBinder.BindA[Set[B]](), TypeBinder.BindB[Set[C]]()))))
					b.Take(b.TermAs[Set[B]]("left_coset(Q'.add, w, coboundaries(Q', n))"))
					b.Show(
						"s is the class of u, which is the class of i(n)(w), i* of the class of w",
						sClass[0].Rw(),
						iClass.Rw(),
						By(sameClass, wClass))
				})
		}),
})}

// CoLongExactQuotient — the long exact sequence at H^n of the quotient
// complex: the image of p* is the kernel of δ, an equation of two sets of
// classes read one class s at a time. Write N for the coboundaries of Q'
// at n + 1, the image of Q'.d(n): the zero class of H^(n+1)(Q') is N, the
// class of the zero of Q'. A class in the image of p* is p* of the class
// of a cocycle u of Q at n: the class of p(n)(u), a cocycle of the
// quotient complex, p being a cochain map; Q.d(n) kills u, so the zero of
// Q' pulls Q.d(n)(u) back, and δ, computed from the lift u itself, sends
// the class of p(n)(u) to the zero class. Conversely a class of a cocycle
// z of the quotient complex that δ sends to the zero class: z lifts to u
// in Q.terms(n), p(n) being onto, and Q.d(n)(u) = i(n + 1)(w) for a w of
// Q'.terms(n + 1); δ sends the class of z to the class of w, which is N, so
// w = Q'.d(n)(v) for a v of Q'.terms(n). Then x = u − i(n)(v) is a cocycle of Q,
// Q.d(n)(x) being i(n + 1)(w) − i(n + 1)(Q'.d(n)(v)), the zero of Q, by the
// square; and p(n)(x) = z, p(n) killing i(n)(v); p* sends the class of x
// to the class of z.
var CoLongExactQuotient = coLongExactQuotientThm{family.Add(registry.ProofEntry{
	Name: "CoLongExactQuotient",
	Key:  "prop_2e609f63e7cce3d4",
	Build: ShortExactCochainComplexes.Law("∀n:num. "+
		"    exact_at(coboundaries(Q', n + 1), "+
		"        cohomology(Q, n), "+
		"        cohomology(Q'', n), "+
		"        cohomology_map(Q'', p, n), "+
		"        coconnecting_hom(Q', Q, i, p, n))",
		func(a *Argument, S ShortExactCochainComplexesFact[on.R], n *Expr[Nat]) {
			parts := []Fact{
				Read(ShortExactCochainSubComplex, S),
				Read(ShortExactCochainMiddleComplex, S),
				Read(ShortExactCochainQuotientComplex, S),
				Read(ShortExactCochainInclusionMap, S),
				Read(ShortExactCochainProjectionMap, S),
				Read(ShortExactCochainDegreewise, S),
			}
			sub, middle, quotient, pCochainMap := parts[0], parts[1], parts[2], parts[4]
			p := a.TermAs[Fun2[Nat, C, D]]("p")
			iClauses := []Fact{Read(CochainMapHom, parts[3]), Read(CochainMapSquare, parts[3])}
			pClauses := []Fact{Read(CochainMapHom, pCochainMap), Read(CochainMapSquare, pCochainMap)}
			iHoms, iSquare, pHoms, pSquare := iClauses[0], iClauses[1], pClauses[0], pClauses[1]
			exact := a.Unfolded(parts[5], ExactComplexesDef)
			subModules, middleModules, quotientModules :=
				CochainModules.Read(sub), CochainModules.Read(middle), CochainModules.Read(quotient)
			subCoboundaryHoms, middleCoboundaryHoms, quotientCoboundaryHoms :=
				CochainCoboundaryHom.Read(sub),
				CochainCoboundaryHom.Read(middle),
				CochainCoboundaryHom.Read(quotient)

			// The zero class of H^(n+1)(Q'): the coboundaries N, the image of Q'.d(n), and the class of Q'.zero.
			coboundariesSub := a.Have(
				"the coboundaries of Q' at n + 1 are the image of Q'.d(n)",
				"coboundaries(Q', n + 1) = image(Q'.d(n), Q'.terms(n))",
				By(Read(CoboundariesSucc, sub).At(n)))
			images := a.Have(
				"the image of Q'.d(n) is a submodule of Q'.terms(n + 1)",
				"submodule(R, complex_module(Q', n + 1), image(Q'.d(n), Q'.terms(n)))",
				Derive(func(b *Argument) {
					hom := b.Have(
						"Q'.d(n) is a homomorphism of the degree modules",
						"module_homomorphism(R, complex_module(Q', n), complex_module(Q', n + 1), Q'.d(n))",
						By(subCoboundaryHoms.At(n)))
					b.Show(
						"so its image is a submodule of its target module",
						By(module_homomorphism.ImageSubmodule.Read(hom)))
				}))
			subgroup := a.Simplified(
				submodule.SubmoduleSubgroup.Read(images),
				Fwd(module_record.ModuleAdditiveGroupDef))
			moduleAtNext := a.Have(
				"Q'.terms(n + 1) is a module",
				"module_on(R, complex_module(Q', n + 1))",
				By(subModules))
			groupAtNext := a.Simplified(
				module.AddGroupOn.Read(moduleAtNext),
				Fwd(module_record.ModuleAdditiveGroupDef))
			zeroClass := a.Have(
				"so the image of Q'.d(n) is the class of Q'.zero, "+
					"the identity of the additive group of Q'.terms(n + 1)",
				"left_coset(Q'.add, Q'.zero, image(Q'.d(n), Q'.terms(n))) = image(Q'.d(n), Q'.terms(n))",
				By(group.LeftCosetOneOn.Read(groupAtNext), group.SubgroupSubset, subgroup))

			// The two sets of classes of Q'', a class s at a time: s is p* of a class of Q, or s is a class that δ sends to the zero class.
			a.Do(Simp(
				Fwd(module_homomorphism.ExactAtDef.Inst(
					TypeBinder.BindD[Set[B]](), TypeBinder.BindB[Set[C]](), TypeBinder.BindC[Set[D]]())),
				Fwd(set_basic.Extension.Inst[Set[D]]()),
				Fwd(group_homomorphism.InKernel.Inst(TypeBinder.BindA[Set[D]](), TypeBinder.BindB[Set[B]]()))))
			a.FixAs[Set[D]]("s")
			a.Iff()
			a.Forward(
				"p* sends the class of a cocycle u to the class of p(n)(u), "+
					"which δ computes from the lift u and sends to the zero class",
				func(b *Argument, sIn Fact) {
					_, sIs := b.Obtain(
						"s is p*(t) for a class t of Q at n",
						"∃t:set(C). s = cohomology_map(Q'', p, n, t) ∧ t ∈ cohomology(Q, n)",
						By(sIn, set_basic.InImage.Inst(TypeBinder.BindA[Set[C]](), TypeBinder.BindB[Set[D]]())))
					sMap := b.Conjuncts(
						sIs,
						"s is p*(t)",
						"t is a class of Q at n")
					u, tIs := b.ObtainAs[C](
						"t is the class of a cocycle u",
						"∃u:C. t = left_coset(Q.add, u, coboundaries(Q, n)) ∧ u ∈ cocycles(Q, n)",
						By(sMap[1], InCohomology.Read(middle)))
					tClass := b.Conjuncts(
						tIs,
						"t is the class of u",
						"u is a cocycle of Q")
					uCocycle := b.Have(
						"u lies in Q.terms(n) and Q.d(n) kills it",
						"u ∈ Q.terms(n) ∧ Q.d(n)(u) = Q.zero",
						BySets(b.Unfolded(tClass[1], CocyclesDef)))
					zOpen := b.Have(
						"p(n)(u) lies in Q''.terms(n), and Q''.d(n)(p(n)(u)) "+
							"= p(n + 1)(Q.d(n)(u)), the zero of Q''.terms(n + 1)",
						"p(n)(u) ∈ Q''.terms(n) ∧ Q''.d(n)(p(n)(u)) = Q''.zero",
						ByChase(
							Depth(0),
							middleModules,
							quotientModules,
							middleCoboundaryHoms,
							quotientCoboundaryHoms,
							pHoms,
							pSquare,
							uCocycle))
					zCocycle := b.Have(
						"so p(n)(u) is a cocycle of the quotient complex",
						"p(n)(u) ∈ cocycles(Q'', n)",
						Simp(Fwd(CocyclesDef.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[D]()))),
						BySets(zOpen))
					zeroPulls := b.Have(
						"Q.d(n)(u) is Q.zero, which Q'.zero pulls back",
						"Q'.zero ∈ Q'.terms(n + 1) ∧ i(n + 1)(Q'.zero) = Q.d(n)(u)",
						ByChase(Depth(0), subModules, middleModules, middleCoboundaryHoms, iHoms, uCocycle))
					classIs := b.Have(
						"δ, computed from the lift u, sends the class of p(n)(u) to the class of Q'.zero",
						"coconnecting_hom(Q', Q, i, p, n, left_coset(Q''.add, p(n)(u), coboundaries(Q'', n))) = "+
							"left_coset(Q'.add, Q'.zero, coboundaries(Q', n + 1))",
						By(
							CoconnectingHomCoset.Read(S).At(n, b.TermAs[D]("p(n)(u)"), u, b.TermAs[B]("Q'.zero")),
							zCocycle,
							uCocycle,
							zeroPulls))
					pClass := b.Have(
						"p* sends the class of u to the class of p(n)(u)",
						"cohomology_map(Q'', p, n, left_coset(Q.add, u, coboundaries(Q, n))) = "+
							"left_coset(Q''.add, p(n)(u), coboundaries(Q'', n))",
						By(Read(CohomologyMapCoset, middle, quotient).At(p, n, u), pCochainMap, tClass[1]))
					zClass := b.Have(
						"the class of p(n)(u) is a class of the quotient complex at n",
						"left_coset(Q''.add, p(n)(u), coboundaries(Q'', n)) ∈ cohomology(Q'', n)",
						Simp(Fwd(InCohomology.Read(quotient))),
						Derive(func(c *Argument) {
							c.Take(c.Term("p(n)(u)"))
							c.Show(
								"the class of p(n)(u) is the class of the cocycle p(n)(u)",
								By(zCocycle))
						}))
					b.Show(
						"s is p*(t), t the class of u, so s is the class of p(n)(u), which δ sends to the zero class",
						sMap[0].Rw(),
						tClass[0].Rw(),
						pClass.Rw(),
						classIs.Rw(),
						coboundariesSub.Rw(),
						By(zClass, zeroClass))
				})
			a.Backward(
				"δ(s) being zero, a lift u of z has Q.d(n)(u) pull back to a "+
					"coboundary Q'.d(n)(v), and p* sends the class of u − i(n)(v) to s",
				func(b *Argument, sIn Fact) {
					kernel := b.Conjuncts(
						sIn,
						"s is a class of the quotient complex at n",
						"δ sends s to the zero class")
					z, sIs := b.ObtainAs[D](
						"s is the class of a cocycle z",
						"∃z:D. s = left_coset(Q''.add, z, coboundaries(Q'', n)) ∧ z ∈ cocycles(Q'', n)",
						By(kernel[0], InCohomology.Read(quotient)))
					sClass := b.Conjuncts(
						sIs,
						"s is the class of z",
						"z is a cocycle of the quotient complex")
					zCocycle := b.Have(
						"z lies in Q''.terms(n) and Q''.d(n) kills it",
						"z ∈ Q''.terms(n) ∧ Q''.d(n)(z) = Q''.zero",
						BySets(b.Unfolded(sClass[1], CocyclesDef)))
					u, uIs := b.ObtainAs[C](
						"z lifts to a u of Q.terms(n), p(n) being onto",
						"∃u:C. u ∈ Q.terms(n) ∧ p(n)(u) = z",
						ByChase(Depth(1), middleModules, quotientModules, pHoms, exact, zCocycle))
					lift := b.Conjuncts(
						uIs,
						"u lies in Q.terms(n)",
						"u lifts z")
					w, wIs := b.ObtainAs[B](
						"p(n + 1) kills Q.d(n)(u), as p(n + 1)(Q.d(n)(u)) = Q''.d(n)(z), "+
							"so Q.d(n)(u) is i(n + 1)(w) for a w of Q'.terms(n + 1)",
						"∃w:B. w ∈ Q'.terms(n + 1) ∧ i(n + 1)(w) = Q.d(n)(u)",
						ByChase(
							Depth(1),
							subModules,
							middleModules,
							quotientModules,
							middleCoboundaryHoms,
							quotientCoboundaryHoms,
							iHoms,
							pHoms,
							pSquare,
							exact,
							zCocycle,
							uIs))
					pull := b.Conjuncts(
						wIs,
						"w lies in Q'.terms(n + 1)",
						"w pulls back Q.d(n)(u)")
					classIs := b.Have(
						"δ sends the class of z to the class of w",
						"coconnecting_hom(Q', Q, i, p, n, left_coset(Q''.add, z, coboundaries(Q'', n))) = "+
							"left_coset(Q'.add, w, coboundaries(Q', n + 1))",
						By(CoconnectingHomCoset.Read(S).At(n, z, u, w), sClass[1], lift[0], lift[1], pull[0], pull[1]))
					wZero := b.Have(
						"so the class of w is the zero class, the class of Q'.zero",
						"left_coset(Q'.add, w, image(Q'.d(n), Q'.terms(n))) = "+
							"left_coset(Q'.add, Q'.zero, image(Q'.d(n), Q'.terms(n)))",
						CalcEq(
							Leg(
								b.TermAs[Set[B]]("coconnecting_hom(Q', Q, i, p, n, s)"),
								"the class of w is δ(s), s being the class of z",
								coboundariesSub.RwRev(),
								sClass[0].Rw(),
								By(classIs)),
							Leg(
								b.TermAs[Set[B]]("image(Q'.d(n), Q'.terms(n))"),
								"which is the zero class",
								coboundariesSub.RwRev(),
								By(kernel[1])),
							FinalLeg(
								"the class of Q'.zero",
								By(zeroClass)),
						))
					_, vIs := b.ObtainAs[B](
						"so w is a coboundary Q'.d(n)(v)",
						"∃v:B. v ∈ Q'.terms(n) ∧ w = Q'.d(n)(v)",
						ByChase(Depth(0), subModules, subCoboundaryHoms, images, pull[0], wZero))
					xIs := b.Let("x", b.Term("Q.add(u, Q.neg(i(n)(v)))"))
					xOpen := b.Have(
						"x lies in Q.terms(n); the square identifies "+
							"Q.d(n)(x) with i(n + 1)(w − Q'.d(n)(v)), which is zero",
						"x ∈ Q.terms(n) ∧ Q.d(n)(x) = Q.zero",
						ByChase(
							Depth(0),
							subModules,
							middleModules,
							subCoboundaryHoms,
							middleCoboundaryHoms,
							iHoms,
							iSquare,
							uIs,
							pull[1],
							vIs,
							xIs))
					xCocycle := b.Have(
						"so x is a cocycle of Q",
						"x ∈ cocycles(Q, n)",
						Simp(Fwd(CocyclesDef.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[C]()))),
						BySets(xOpen))
					xLifts := b.Have(
						"p(n) carries x to z, as p(n) kills i(n)(v) by exactness",
						"p(n)(x) = z",
						ByChase(Depth(0), subModules, middleModules, quotientModules, iHoms, pHoms, exact, uIs, vIs, xIs))
					xClass := b.Have(
						"the class of x is a class of Q at n",
						"left_coset(Q.add, x, coboundaries(Q, n)) ∈ cohomology(Q, n)",
						Simp(Fwd(InCohomology.Read(middle))),
						Derive(func(c *Argument) {
							c.Take(c.Term("x"))
							c.Show(
								"the class of x is the class of the cocycle x",
								By(xCocycle))
						}))
					xMaps := b.Have(
						"p* sends the class of x to the class of p(n)(x)",
						"cohomology_map(Q'', p, n, left_coset(Q.add, x, coboundaries(Q, n))) = "+
							"left_coset(Q''.add, p(n)(x), coboundaries(Q'', n))",
						By(Read(CohomologyMapCoset, middle, quotient).At(p, n, b.TermAs[C]("x")), pCochainMap, xCocycle))
					b.Do(Simp(Fwd(set_basic.InImage.Inst(TypeBinder.BindA[Set[C]](), TypeBinder.BindB[Set[D]]()))))
					b.Take(b.Term("left_coset(Q.add, x, coboundaries(Q, n))"))
					b.Show(
						"s, the class of z, is p* of the class of x",
						xMaps.Rw(),
						xLifts.Rw(),
						By(sClass[0], xClass))
				})
		}),
})}

// CoLongExactSub — the long exact sequence at H^(n+1)(Q'): the image of
// the connecting map is the kernel of i's map, an equation of two sets of
// classes read one class s at a time. Write N for the coboundaries of Q at
// n + 1, the image of Q.d(n): the zero class of H^(n+1)(Q) is N, the class
// of the zero of Q. A class in the image is δ of the class of a cocycle z
// of the quotient complex at n. CocycleLiftPullback supplies a lift u in
// Q.terms(n) and a cocycle w in Q'.terms(n + 1) with i(n + 1)(w) = Q.d(n)(u), so δ sends
// the class of z to the class of w. Then i* sends the class of w to the
// class of i(n + 1)(w) = Q.d(n)(u), a member of N, hence to N. Conversely a
// class of a cocycle w that i* sends to N has
// i(n + 1)(w) in N, i(n + 1)(w) = Q.d(n)(u); then z = p(n)(u) is a cocycle
// of the quotient complex, its coboundary being p(n + 1)(i(n + 1)(w)),
// zero by exactness, and δ sends the class of z to the class of w.
var CoLongExactSub = coLongExactSubThm{family.Add(registry.ProofEntry{
	Name: "CoLongExactSub",
	Key:  "prop_7957906c917317cb",
	Build: ShortExactCochainComplexes.Law("∀n:num. "+
		"    exact_at(coboundaries(Q, n + 1), "+
		"        cohomology(Q'', n), "+
		"        cohomology(Q', n + 1), "+
		"        coconnecting_hom(Q', Q, i, p, n), "+
		"        cohomology_map(Q, i, n + 1))",
		func(a *Argument, S ShortExactCochainComplexesFact[on.R], n *Expr[Nat]) {
			parts := []Fact{
				Read(ShortExactCochainSubComplex, S),
				Read(ShortExactCochainMiddleComplex, S),
				Read(ShortExactCochainQuotientComplex, S),
				Read(ShortExactCochainInclusionMap, S),
				Read(ShortExactCochainProjectionMap, S),
				Read(ShortExactCochainDegreewise, S),
			}
			sub, middle, quotient, iCochainMap := parts[0], parts[1], parts[2], parts[3]
			i := a.TermAs[Fun2[Nat, B, C]]("i")
			iHoms := Read(CochainMapHom, iCochainMap)
			pHoms, pSquare := Read(CochainMapHom, parts[4]), Read(CochainMapSquare, parts[4])
			exact := a.Unfolded(parts[5], ExactComplexesDef)
			subModules, middleModules, quotientModules :=
				CochainModules.Read(sub), CochainModules.Read(middle), CochainModules.Read(quotient)
			middleCoboundaryHoms, quotientCoboundaryHoms :=
				CochainCoboundaryHom.Read(middle), CochainCoboundaryHom.Read(quotient)

			// The zero class of H^(n+1)(Q): the coboundaries N, the image of Q.d(n), and the class of Q.zero.
			coboundariesQ := a.Have(
				"the coboundaries of Q at n + 1 are the image of Q.d(n)",
				"coboundaries(Q, n + 1) = image(Q.d(n), Q.terms(n))",
				By(Read(CoboundariesSucc, middle).At(n)))
			images := a.Have(
				"the image of Q.d(n) is a submodule of Q.terms(n + 1)",
				"submodule(R, complex_module(Q, n + 1), image(Q.d(n), Q.terms(n)))",
				Derive(func(b *Argument) {
					hom := b.Have(
						"Q.d(n) is a homomorphism of the degree modules",
						"module_homomorphism(R, complex_module(Q, n), complex_module(Q, n + 1), Q.d(n))",
						By(middleCoboundaryHoms.At(n)))
					b.Show(
						"so its image is a submodule of its target module",
						By(module_homomorphism.ImageSubmodule.Read(hom)))
				}))
			subgroup := a.Simplified(
				submodule.SubmoduleSubgroup.Read(images),
				Fwd(module_record.ModuleAdditiveGroupDef))
			moduleAtNext := a.Have(
				"Q.terms(n + 1) is a module",
				"module_on(R, complex_module(Q, n + 1))",
				By(middleModules))
			groupAtNext := a.Simplified(
				module.AddGroupOn.Read(moduleAtNext),
				Fwd(module_record.ModuleAdditiveGroupDef))
			zeroClass := a.Have(
				"so the image of Q.d(n) is the class of Q.zero, the "+
					"identity of the additive group of Q.terms(n + 1)",
				"left_coset(Q.add, Q.zero, image(Q.d(n), Q.terms(n))) = image(Q.d(n), Q.terms(n))",
				By(group.LeftCosetOneOn.Read(groupAtNext), group.SubgroupSubset, subgroup))

			// The two sets of classes of Q', a class s at a time: s is in the image of δ, or s is a class that i* sends to the zero class.
			a.Do(Simp(
				Fwd(module_homomorphism.ExactAtDef.Inst(
					TypeBinder.BindD[Set[C]](), TypeBinder.BindB[Set[D]](), TypeBinder.BindC[Set[B]]())),
				Fwd(set_basic.Extension.Inst[Set[B]]()),
				Fwd(group_homomorphism.InKernel.Inst(TypeBinder.BindA[Set[B]](), TypeBinder.BindB[Set[C]]()))))
			a.FixAs[Set[B]]("s")
			a.Iff()
			a.Forward(
				"δ sends the class of a cocycle z to the class of a pull-back w "+
					"of Q.d(n)(u), u a lift of z, and i* sends that to the zero class",
				func(b *Argument, sIn Fact) {
					_, sIs := b.Obtain(
						"s is δ(t) for a class t of the quotient complex at n",
						"∃t:set(D). s = coconnecting_hom(Q', Q, i, p, n, t) ∧ t ∈ cohomology(Q'', n)",
						By(sIn, set_basic.InImage.Inst(TypeBinder.BindA[Set[D]](), TypeBinder.BindB[Set[B]]())))
					sDelta := b.Conjuncts(
						sIs,
						"s is δ(t)",
						"t is a class of the quotient complex at n")
					z, tIs := b.ObtainAs[D](
						"t is the class of a cocycle z",
						"∃z:D. t = left_coset(Q''.add, z, coboundaries(Q'', n)) ∧ z ∈ cocycles(Q'', n)",
						By(sDelta[1], InCohomology.Read(quotient)))
					tClass := b.Conjuncts(
						tIs,
						"t is the class of z",
						"z is a cocycle of the quotient complex")
					u, w, realized := b.Obtain2As[C, B](
						"z lifts to u, whose coboundary pulls back to a cocycle w",
						"∃u:C. ∃w:B. "+
							"    u ∈ Q.terms(n) ∧ "+
							"    p(n)(u) = z ∧ "+
							"    w ∈ Q'.terms(n + 1) ∧ "+
							"    i(n + 1)(w) = Q.d(n)(u) ∧ "+
							"    w ∈ cocycles(Q', n + 1)",
						By(Read(CocycleLiftPullback, S).At(n, z), tClass[1]))
					r := b.Conjuncts(
						realized,
						"u lies in Q.terms(n)",
						"u lifts z",
						"w lies in Q'.terms(n + 1)",
						"w pulls back Q.d(n)(u)",
						"w is a cocycle of Q'")
					classIs := b.Have(
						"δ sends the class of z to the class of w",
						"coconnecting_hom(Q', Q, i, p, n, left_coset(Q''.add, z, coboundaries(Q'', n))) = "+
							"left_coset(Q'.add, w, coboundaries(Q', n + 1))",
						By(CoconnectingHomCoset.Read(S).At(n, z, u, w), tClass[1], r[0], r[1], r[2], r[3]))
					wClass := b.Have(
						"so the class of w is a class of Q' at n + 1",
						"left_coset(Q'.add, w, coboundaries(Q', n + 1)) ∈ cohomology(Q', n + 1)",
						Simp(Fwd(InCohomology.Read(sub))),
						Derive(func(c *Argument) {
							c.Take(w)
							c.Show(
								"the class of w is the class of the cocycle w",
								By(r[4]))
						}))
					wZero := b.Have(
						"and i* sends it to the zero class",
						"cohomology_map(Q, i, n + 1, left_coset(Q'.add, w, coboundaries(Q', n + 1))) = "+
							"coboundaries(Q, n + 1)",
						CalcEq(
							Leg(
								b.TermAs[Set[C]]("left_coset(Q.add, i(n + 1)(w), coboundaries(Q, n + 1))"),
								"i* sends the class of w to the class of i(n + 1)(w)",
								By(Read(CohomologyMapCoset, sub, middle).At(i, b.TermAs[Nat]("n + 1"), w), iCochainMap, r[4])),
							Leg(
								b.TermAs[Set[C]]("left_coset(Q.add, Q.zero, image(Q.d(n), Q.terms(n)))"),
								"i(n + 1)(w) = Q.d(n)(u) is a coboundary, so its class is the class of Q.zero",
								coboundariesQ.Rw(),
								ByChase(Depth(0), middleModules, middleCoboundaryHoms, images, r[0], r[3])),
							FinalLeg(
								"which is the zero class",
								coboundariesQ.Rw(),
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
				"a class of a cocycle w that i* sends to the zero class has i(n + "+
					"1)(w) = Q.d(n)(u), and δ sends the class of the cocycle p(n)(u) to it",
				func(b *Argument, sIn Fact) {
					kernel := b.Conjuncts(
						sIn,
						"s is a class of Q' at n + 1",
						"i* sends s to the zero class")
					w, sIs := b.ObtainAs[B](
						"s is the class of a cocycle w",
						"∃w:B. s = left_coset(Q'.add, w, coboundaries(Q', n + 1)) ∧ w ∈ cocycles(Q', n + 1)",
						By(kernel[0], InCohomology.Read(sub)))
					sClass := b.Conjuncts(
						sIs,
						"s is the class of w",
						"w is a cocycle of Q'")
					wIn := b.Have(
						"w lies in Q'.terms(n + 1)",
						"w ∈ Q'.terms(n + 1)",
						BySets(b.Unfolded(sClass[1], CocyclesDef)))
					wZero := b.Have(
						"so the class of i(n + 1)(w) is the zero class, the class of Q.zero",
						"left_coset(Q.add, i(n + 1)(w), image(Q.d(n), Q.terms(n))) = "+
							"left_coset(Q.add, Q.zero, image(Q.d(n), Q.terms(n)))",
						CalcEq(
							Leg(
								b.TermAs[Set[C]]("cohomology_map(Q, i, n + 1, s)"),
								"the class of i(n + 1)(w) is i*(s), s being the class of w",
								coboundariesQ.RwRev(),
								sClass[0].Rw(),
								By(Read(CohomologyMapCoset, sub, middle).At(i, b.TermAs[Nat]("n + 1"), w), iCochainMap, sClass[1])),
							Leg(
								b.TermAs[Set[C]]("image(Q.d(n), Q.terms(n))"),
								"which is the zero class",
								coboundariesQ.RwRev(),
								By(kernel[1])),
							FinalLeg(
								"the class of Q.zero",
								By(zeroClass)),
						))
					u, uIs := b.ObtainAs[C](
						"so i(n + 1)(w) is a coboundary Q.d(n)(u)",
						"∃u:C. u ∈ Q.terms(n) ∧ i(n + 1)(w) = Q.d(n)(u)",
						ByChase(Depth(0), subModules, middleModules, middleCoboundaryHoms, iHoms, images, wIn, wZero))
					lift := b.Conjuncts(
						uIs,
						"u lies in Q.terms(n)",
						"i(n + 1)(w) = Q.d(n)(u)")
					z, zIs := b.LetAs[D]("z", "p(n)(u)")
					zOpen := b.Have(
						"z lies in Q''.terms(n), and Q''.d(n)(z) = p(n + "+
							"1)(Q.d(n)(u)) = p(n + 1)(i(n + 1)(w)) is zero by exactness",
						"z ∈ Q''.terms(n) ∧ Q''.d(n)(z) = Q''.zero",
						ByChase(
							Depth(0),
							subModules,
							middleModules,
							quotientModules,
							quotientCoboundaryHoms,
							iHoms,
							pHoms,
							pSquare,
							exact,
							wIn,
							uIs,
							zIs))
					zCocycle := b.Have(
						"so z is a cocycle of the quotient complex",
						"z ∈ cocycles(Q'', n)",
						Simp(Fwd(CocyclesDef.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[D]()))),
						BySets(zOpen))
					classIs := b.Have(
						"δ sends the class of z to the class of w",
						"coconnecting_hom(Q', Q, i, p, n, left_coset(Q''.add, z, coboundaries(Q'', n))) = "+
							"left_coset(Q'.add, w, coboundaries(Q', n + 1))",
						By(CoconnectingHomCoset.Read(S).At(n, z, u, w), zCocycle, lift[0], zIs, wIn, lift[1]))
					zClass := b.Have(
						"the class of z is a class of the quotient complex at n",
						"left_coset(Q''.add, z, coboundaries(Q'', n)) ∈ cohomology(Q'', n)",
						Simp(Fwd(InCohomology.Read(quotient))),
						Derive(func(c *Argument) {
							c.Take(z)
							c.Show(
								"the class of z is the class of the cocycle z",
								By(zCocycle))
						}))
					b.Do(Simp(Fwd(set_basic.InImage.Inst(TypeBinder.BindA[Set[D]](), TypeBinder.BindB[Set[B]]()))))
					b.Take(b.Term("left_coset(Q''.add, z, coboundaries(Q'', n))"))
					b.Show(
						"s, the class of w, is δ of the class of z",
						classIs.Rw(),
						By(sClass[0], zClass))
				})
		}),
})}

// CoconnectingNaturality — a map of short exact sequences of cochain
// complexes commutes with their connecting maps.
var CoconnectingNaturality = coconnectingNaturalityThm{family.Add(registry.ProofEntry{
	Name: "CoconnectingNaturality",
	Key:  "prop_8d5723081bedf0bf",
	Reading: "The two squares are asked on the terms only, which is all the connecting " +
		"map reads: a lift, its coboundary and a pull-back, each in a term of its complex. " +
		"The cohomology sequence of a tower is natural in its coefficient module through this.",
	Deps: []registry.EntryLike{
		ShortExactCochainComplexes,
		ShortExactCochainSubComplex,
		ShortExactCochainMiddleComplex,
		ShortExactCochainQuotientComplex,
		CocycleLiftPullback,
		CoconnectingHomCoset,
		CohomologyMapCoset,
		CochainMapCocycles,
		CochainMapHom,
		CochainMapSquare,
		CohomologyDef,
		quotient_group.InLeftCosets,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀Q':complex_ops(A, B). " +
			"∀Q:complex_ops(A, C). " +
			"∀Q'':complex_ops(A, D). " +
			"∀i:(num → B → C). " +
			"∀p:(num → C → D). " +
			"∀W':complex_ops(A, E). " +
			"∀W:complex_ops(A, F). " +
			"∀W'':complex_ops(A, G). " +
			"∀i':(num → E → F). " +
			"∀p':(num → F → G). " +
			"∀α:(num → B → E). " +
			"∀β:(num → C → F). " +
			"∀γ:(num → D → G). " +
			"∀n:num. " +
			"∀s:set(D).",
		Hypotheses: []string{
			"short_exact_cochain_complexes(R, Q', Q, Q'', i, p)",
			"short_exact_cochain_complexes(R, W', W, W'', i', p')",
			"cochain_map(R, Q', W', α)",
			"cochain_map(R, Q, W, β)",
			"cochain_map(R, Q'', W'', γ)",
			"∀n:num. ∀x:B. x ∈ Q'.terms(n) ⇒ β(n)(i(n)(x)) = i'(n)(α(n)(x))",
			"∀n:num. ∀y:C. y ∈ Q.terms(n) ⇒ γ(n)(p(n)(y)) = p'(n)(β(n)(y))",
			"s ∈ cohomology(Q'', n)",
		},
		Conclusion: "cohomology_map(W', α, n + 1, coconnecting_hom(Q', Q, i, p, n, s)) = " +
			"coconnecting_hom(W', W, i', p', n, cohomology_map(W'', γ, n, s))",
	},
		"let s be the class of a cocycle z of Q'' (CohomologyDef, InLeftCosets); CocycleLiftPullback "+
			"gives u ∈ Q.terms(n) over z and a cocycle w ∈ Q'.terms(n + 1) with i(n + 1)(w) = Q.d(n)(u), "+
			"and the connecting map sends s to the class of w (CoconnectingHomCoset), which α's map sends "+
			"to the class of α(n + 1)(w) (CohomologyMapCoset). On the other side γ's map sends s to the "+
			"class of the cocycle γ(n)(z) (CohomologyMapCoset, CochainMapCocycles); β(n)(u) lies in "+
			"W.terms(n) over γ(n)(z) (the second square), and W.d(n)(β(n)(u)) = β(n + 1)(Q.d(n)(u)) = β(n + "+
			"1)(i(n + 1)(w)) = i'(n + 1)(α(n + 1)(w)) (CochainMapSquare, the first square), so the second "+
			"connecting map sends the class of γ(n)(z) to the class of α(n + 1)(w) (CoconnectingHomCoset)"),
})}
