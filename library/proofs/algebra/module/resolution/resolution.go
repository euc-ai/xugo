// resolution.go — free resolutions of a module on a set: a chain
// complex of free modules on index sets S(n) ⊆ I, exact in every
// positive degree, with an augmentation ε mapping the degree-0 term
// onto the module with the boundaries as kernel. The terms are free
// modules on subsets of ONE index type, so they share the type I → A
// and the pointwise operations, which is what lets a resolution be a
// sequence. Every module has one, under the hypothesis that the index
// type is large enough — the module and the free module on the whole
// index type both inject into it; the cardinal chapter supplies such a
// type. A homomorphism lifts to a chain map between resolutions, unique
// up to chain homotopy: the comparison theorem. Its uniqueness half is
// stated for any free chain complex as source: two chain maps from it into
// a resolution that agree after the augmentation are homotopic.

package resolution

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/chain_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinal"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// FreeComplexOf — the free modules on S(n), with differential d.
var FreeComplexOf = freeComplexOfThm{family.Define(registry.DefEntry{
	Name: "FreeComplexOf", Const: "free_complex",
	Key:  "prop_f10ed9dc51179bca",
	Type: "ring_ops(A) → (num → set(I)) → (num → (I → A) → I → A) → complex_ops(A, I → A)",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:(num → set(I)). ∀d:(num → (I → A) → I → A). " +
			"    free_complex(R, S, d) = " +
			"    pack_complex(fun_add⟨D:I⟩(R.add), " +
			"        fun_zero⟨D:I⟩(R.zero), " +
			"        fun_neg⟨D:I⟩(R.neg), " +
			"        fun_smul⟨D:I⟩(R.mul), " +
			"        λn:num. finite_supp(R.zero, R.carrier, S(n)), " +
			"        d)",
	},
})}

// FreeResolution — the free complex is exact above degree zero, and
// its augmentation resolves the R-module M.
var FreeResolution = freeResolutionThm{family.DefineStructure(registry.DefEntry{
	Name:  "FreeResolution",
	Const: "free_resolution",
	Type: "ring_ops(A) → " +
		"module_ops(A, B) → " +
		"(num → set(I)) → " +
		"(num → (I → A) → I → A) → " +
		"((I → A) → B) → " +
		"bool",
	Key:     "prop_fc25351990f0e73e",
	Subject: "S",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀S:(num → set(I)). " +
			"∀d:(num → (I → A) → I → A). " +
			"∀eps:((I → A) → B). " +
			"    free_resolution(R, M, S, d, eps) ⇔ " +
			"    module_on(R, M) ∧ " +
			"    chain_complex(R, free_complex(R, S, d)) ∧ " +
			"    (∀n:num. cycles(free_complex(R, S, d), n + 1) = boundaries(free_complex(R, S, d), n + 1)) ∧ " +
			"    module_homomorphism(R, complex_module(free_complex(R, S, d), 0), M, eps) ∧ " +
			"    image(eps, finite_supp(R.zero, R.carrier, S(0))) = M.carrier ∧ " +
			"    group_kernel(M.zero, finite_supp(R.zero, R.carrier, S(0)), eps) = " +
			"    boundaries(free_complex(R, S, d), 0)",
	},
	Deps: []registry.EntryLike{FreeComplexOf},
})}

// ResolutionModule — the resolved module is a module.
var ResolutionModule = resolutionModuleThm{family.Add(registry.ProofEntry{
	Name:  "ResolutionModule",
	Key:   "prop_9f8a86bb061143e5",
	Build: FreeResolution.Axiom("module_on(R, M)"),
})}

// ResolutionComplex — the free terms with their boundaries are a chain
// complex.
var ResolutionComplex = resolutionComplexThm{family.Add(registry.ProofEntry{
	Name:  "ResolutionComplex",
	Key:   "prop_ff4793d610197972",
	Build: FreeResolution.Axiom("chain_complex(R, free_complex(R, S, d))"),
})}

// ResolutionExact — the complex is exact above degree 0.
var ResolutionExact = resolutionExactThm{family.Add(registry.ProofEntry{
	Name: "ResolutionExact",
	Key:  "prop_68c27476fd50cbfa",
	Build: FreeResolution.Axiom(
		"∀n:num. cycles(free_complex(R, S, d), n + 1) = boundaries(free_complex(R, S, d), n + 1)"),
})}

// ResolutionAugmentationHom — the augmentation is a homomorphism.
var ResolutionAugmentationHom = resolutionAugmentationHomThm{family.Add(registry.ProofEntry{
	Name: "ResolutionAugmentationHom",
	Key:  "prop_eeddfa4c8641193a",
	Build: FreeResolution.Axiom(
		"module_homomorphism(R, complex_module(free_complex(R, S, d), 0), M, eps)"),
})}

// ResolutionAugmentationOnto — the augmentation maps onto M.
var ResolutionAugmentationOnto = resolutionAugmentationOntoThm{family.Add(registry.ProofEntry{
	Name:  "ResolutionAugmentationOnto",
	Key:   "prop_5544b86b5f2f770e",
	Build: FreeResolution.Axiom("image(eps, finite_supp(R.zero, R.carrier, S(0))) = M.carrier"),
})}

// ResolutionAugmentationKernel — the kernel of the augmentation is the
// boundaries at degree 0.
var ResolutionAugmentationKernel = resolutionAugmentationKernelThm{family.Add(registry.ProofEntry{
	Name: "ResolutionAugmentationKernel",
	Key:  "prop_1ee0de62d86ebc1f",
	Build: FreeResolution.Axiom(
		"group_kernel(M.zero, finite_supp(R.zero, R.carrier, S(0)), eps) = " +
			"boundaries(free_complex(R, S, d), 0)"),
})}

// ---------------------------------------------------------------------------
// The terms of a free complex
// ---------------------------------------------------------------------------

// FreeComplexModule — the module at each degree of a free complex is the
// free module on S(n): both are the pointwise operations on the finitely
// supported functions on S(n).
var FreeComplexModule = freeComplexModuleThm{family.Add(registry.ProofEntry{
	Name: "FreeComplexModule",
	Key:  "prop_ffaae5917051d636",
	Build: family.Theorem(
		"∀R:ring_ops(A). ∀S:(num → set(I)). ∀d:(num → (I → A) → I → A). ∀n:num. "+
			"    complex_module(free_complex(R, S, d), n) = free_module_record(R, S(n))",
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			S *Arrow[Nat, Set[I]],
			d *Expr[Fun3[Nat, Fun[I, A], I, A]],
			n *Expr[Nat],
		) {
			a.Show(
				"each degree has the free-module record",
				Simp(Fwd(FreeComplexOf), Fwd(free_module.FreeModuleRecordDef), Fwd(chain_complex.ComplexModuleDef)),
				Basic())
		}),
})}

// FreeComplexFields — the free complex has the finitely supported
// functions on S(n) as its term in degree n, d(n) as its differential out
// of degree n, and the zero function as its zero.
var FreeComplexFields = freeComplexFieldsThm{family.Add(registry.ProofEntry{
	Name: "FreeComplexFields",
	Key:  "prop_bdd74a6bbaae74bd",
	Build: family.Theorem(
		"∀R:ring_ops(A). ∀S:(num → set(I)). ∀d:(num → (I → A) → I → A). ∀n:num. "+
			"    free_complex(R, S, d).terms(n) = finite_supp(R.zero, R.carrier, S(n)) ∧ "+
			"    free_complex(R, S, d).d(n) = d(n) ∧ "+
			"    free_complex(R, S, d).zero = fun_zero(R.zero)",
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			S *Arrow[Nat, Set[I]],
			d *Expr[Fun3[Nat, Fun[I, A], I, A]],
			n *Expr[Nat],
		) {
			a.Show(
				"the free complex has the specified carriers and differential",
				Simp(Fwd(FreeComplexOf)),
				Basic())
		}),
})}

// FreeComplexDifferentialHom — when the free complex is a chain complex,
// each differential d(n + 1) is linear from the free module on S(n + 1)
// to the free module on S(n): the complex's differential out of degree
// n + 1 is linear between its degree modules, which are those free
// modules.
var FreeComplexDifferentialHom = freeComplexDifferentialHomThm{family.Add(registry.ProofEntry{
	Name: "FreeComplexDifferentialHom",
	Key:  "prop_c22f6e23d8d21375",
	Build: family.Theorem(Statement{
		Binders:    "∀R:ring_ops(A). ∀S:(num → set(I)). ∀d:(num → (I → A) → I → A). ∀n:num.",
		Hypotheses: []string{"chain_complex(R, free_complex(R, S, d))"},
		Conclusion: "module_homomorphism(R, " +
			"    free_module_record(R, S(n + 1)), " +
			"    free_module_record(R, S(n)), " +
			"    d(n + 1))",
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		S *Arrow[Nat, Set[I]],
		d *Expr[Fun3[Nat, Fun[I, A], I, A]],
		complex chain_complex.ChainComplexFact[on.R],
		n *Expr[Nat],
	) {
		next := a.TermAs[Nat]("n + 1")
		a.Show(
			"each differential of the complex is linear between consecutive free terms",
			By(
				chain_complex.ComplexBoundaryHom.Read(complex).At(n),
				FreeComplexModule.At(R, S, d, n),
				FreeComplexModule.At(R, S, d, next),
				FreeComplexFields.At(R, S, d, next)))
	}),
})}

// ---------------------------------------------------------------------------
// Lifting through a surjection, and existence
// ---------------------------------------------------------------------------

// FreeLiftThrough — a homomorphism from a free module into the target
// of a surjective homomorphism lifts through it: its values lie in the
// target, all of which is the image, so the free module's projectivity
// lifts it.
var FreeLiftThrough = freeLiftThroughThm{family.Add(registry.ProofEntry{
	Name: "FreeLiftThrough",
	Key:  "prop_22c11723ea514df7",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀N:module_ops(A, C). " +
			"∀S:set(D). " +
			"∀g:(B → C). " +
			"∀f:((D → A) → C).",
		Hypotheses: []string{
			"module_homomorphism(R, M, N, g)",
			"image(g, M.carrier) = N.carrier",
			"module_homomorphism(R, free_module_record(R, S), N, f)",
		},
		Conclusion: "∃h:((D → A) → B). " +
			"    module_homomorphism(R, free_module_record(R, S), M, h) ∧ " +
			"    (∀x:(D → A). x ∈ finite_supp(R.zero, R.carrier, S) ⇒ g(h(x)) = f(x))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			M *Expr[ModuleOps[A, B]],
			N *Expr[ModuleOps[A, C]],
			S *Expr[Set[D]],
			g *Arrow[B, C],
			f *Arrow[Fun[D, A], C],
			linearG, onto, linearF Fact,
		) {
			a.Show(
				"f takes the free module into N, which is the image of g, so f lifts along g",
				By(
					module_homomorphism.HomIn.Read(linearF),
					linearG,
					onto,
					linearF,
					free_module.FreeModuleLift.At(R, N, M, S, f, g)))
		}),
})}

// LiftThroughBoundaries — a linear map from a free module into the
// degree-m term of a free chain complex whose values are boundaries lifts
// through the differential out of degree m + 1: the boundaries at m are
// the image of that differential, which is linear, so the free module's
// projectivity lifts the map.
var LiftThroughBoundaries = liftThroughBoundariesThm{family.Add(registry.ProofEntry{
	Name: "LiftThroughBoundaries",
	Key:  "prop_3cc44a16e1d15912",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀T:(num → set(E)). " +
			"∀e:(num → (E → A) → E → A). " +
			"∀m:num. " +
			"∀X:set(I). " +
			"∀f:((I → A) → E → A).",
		Hypotheses: []string{
			"chain_complex(R, free_complex(R, T, e))",
			"module_homomorphism(R, free_module_record(R, X), free_module_record(R, T(m)), f)",
			"∀x:(I → A). x ∈ finite_supp(R.zero, R.carrier, X) ⇒ f(x) ∈ boundaries(free_complex(R, T, e), m)",
		},
		Conclusion: "∃k:((I → A) → E → A). " +
			"    module_homomorphism(R, free_module_record(R, X), free_module_record(R, T(m + 1)), k) ∧ " +
			"    (∀x:(I → A). x ∈ finite_supp(R.zero, R.carrier, X) ⇒ e(m + 1, k(x)) = f(x))",
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		T *Arrow[Nat, Set[E]],
		e *Expr[Fun3[Nat, Fun[E, A], E, A]],
		complex chain_complex.ChainComplexFact[on.R],
		m *Expr[Nat],
		X *Expr[Set[I]],
		f *Arrow[Fun[I, A], Fun[E, A]],
		linearF, intoBoundaries Fact,
	) {
		Q := a.TermAs[chain_complex.ComplexOps[A, Fun[E, A]]]("free_complex(R, T, e)")
		V := a.TermAs[ModuleOps[A, Fun[E, A]]]("free_module_record(R, T(m))")
		V1 := a.TermAs[ModuleOps[A, Fun[E, A]]]("free_module_record(R, T(m + 1))")
		e1 := a.TermAs[Fun[Fun[E, A], Fun[E, A]]]("e(m + 1)")
		a.Show(
			"the boundaries at m are the image of the linear differential out of m + 1, so f lifts along it",
			By(
				complex,
				linearF,
				intoBoundaries,
				chain_complex.BoundariesDef.At(Q, m),
				FreeComplexFields.At(R, T, e, a.TermAs[Nat]("m + 1")),
				FreeComplexDifferentialHom.At(R, T, e, m),
				free_module.FreeModuleLift.At(R, V, V1, X, f, e1)))
	}),
})}

// FreeResolutionExists — a module has a free resolution on any index
// type that is large enough: the module injects into it, and so does
// the free module on all of it. Then every kernel met is a subset of
// that free module, injects into the index type, and is the image of
// the free module on its image.
var FreeResolutionExists = freeResolutionExistsThm{family.Add(registry.ProofEntry{
	Name: "FreeResolutionExists",
	Key:  "prop_186c5cb33ad64fe9",
	Deps: []registry.EntryLike{
		FreeResolution,
		free_module.FreeLiftHom,
		free_module.FreeLiftDelta,
		free_module.DeltaAtIn,
		free_module.FreeModuleOn,
		function_module.FiniteSuppDef,
		module_homomorphism.KernelSubmodule,
		module_homomorphism.HomRestrict,
		group_homomorphism.InKernel,
		submodule.SubmoduleModuleOn,
		module.RingOn,
		chain_complex.ChainComplex,
		chain_complex.CyclesDef,
		chain_complex.BoundariesDef,
		nat_arith.DependentChoice,
		cardinal.CardLeDef,
		cardinal.CardLeSubset,
		cardinal.CardLeTrans,
		set_basic.InImage,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B).",
		Hypotheses: []string{
			"module_on(R, M)",
			"card_le(M.carrier, 𝕌⟨A:I⟩)",
			"card_le(finite_supp(R.zero, R.carrier, 𝕌⟨A:I⟩), 𝕌⟨A:I⟩)",
		},
		Conclusion: "∃S:(num → set(I)). ∃d:(num → (I → A) → I → A). ∃eps:((I → A) → B). " +
			"    free_resolution(R, M, S, d, eps)",
	},
		"Inject the carrier into I and extend the inverse. At each successor inject the preceding "+
			"kernel into I and extend its inverse; primitive recursion constructs the resolution."),
})}

// ---------------------------------------------------------------------------
// The comparison theorem
// ---------------------------------------------------------------------------

// ResolutionComparison — a homomorphism f: M → N lifts to a chain map
// from the free resolution on S to the free resolution on T, compatible
// with the augmentations. Degree 0 lifts f ∘ eps through eta, which maps
// onto N (liftAugmentation). Each later degree lifts the previous lift
// after the source differential through the target differential, which
// maps onto the target boundaries (liftDegree, by LiftThroughBoundaries):
// the invariant that each lift is linear and carries source boundaries
// into target boundaries puts that map into the boundaries, and
// exactness carries the invariant one degree up. The lifts are assembled
// into one sequence by dependent choice along ℕ (nat_arith.DependentChoice).
var ResolutionComparison = resolutionComparisonThm{family.Add(registry.ProofEntry{
	Name: "ResolutionComparison",
	Key:  "prop_7edb0eddd1510f7f",
	Build: family.Sections(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀S:(num → set(I)). " +
			"∀d:(num → (I → A) → I → A). " +
			"∀eps:((I → A) → B). " +
			"∀N:module_ops(A, C). " +
			"∀T:(num → set(E)). " +
			"∀e:(num → (E → A) → E → A). " +
			"∀eta:((E → A) → C). " +
			"∀f:(B → C).",
		Hypotheses: []string{
			"free_resolution(R, M, S, d, eps)",
			"free_resolution(R, N, T, e, eta)",
			"module_homomorphism(R, M, N, f)",
		},
		Conclusion: "∃g:(num → (I → A) → E → A). " +
			"    chain_map(R, free_complex(R, S, d), free_complex(R, T, e), g) ∧ " +
			"    (∀x:(I → A). x ∈ finite_supp(R.zero, R.carrier, S(0)) ⇒ eta(g(0)(x)) = f(eps(x)))",
	},
		func(ctx *Script, headline string) *GoalStackNode {
			// liftDegree is stated at n + 2, the degree ComplexBoundaryTwice names; a
			// differential or LinearKeepsBoundaries taken one degree up spells it n + 1 + 1.
			nextIndex := ctx.Lemma(
				"∀n:num. n + 1 + 1 = n + 2",
				func(a *Argument, n *Expr[Nat]) {
					a.Show(
						"two adjacent successor degrees agree",
						ByArith())
				})

			liftDegree := ctx.Lemma(Statement{
				Binders: "∀R:ring_ops(A). " +
					"∀S:(num → set(I)). " +
					"∀d:(num → (I → A) → I → A). " +
					"∀T:(num → set(E)). " +
					"∀e:(num → (E → A) → E → A). " +
					"∀n:num. " +
					"∀h:((I → A) → E → A).",
				Hypotheses: []string{
					"chain_complex(R, free_complex(R, S, d))",
					"chain_complex(R, free_complex(R, T, e))",
					"cycles(free_complex(R, T, e), n + 1) = boundaries(free_complex(R, T, e), n + 1)",
					"module_homomorphism(R, free_module_record(R, S(n)), free_module_record(R, T(n)), h)",
					"∀x:(I → A). " +
						"    x ∈ finite_supp(R.zero, R.carrier, S(n + 1)) ⇒ " +
						"    h(d(n + 1, x)) ∈ boundaries(free_complex(R, T, e), n)",
				},
				Conclusion: "∃k:((I → A) → E → A). " +
					"    module_homomorphism(R, " +
					"        free_module_record(R, S(n + 1)), " +
					"        free_module_record(R, T(n + 1)), " +
					"        k) ∧ " +
					"    (∀x:(I → A). " +
					"        x ∈ finite_supp(R.zero, R.carrier, S(n + 2)) ⇒ " +
					"        k(d(n + 2, x)) ∈ boundaries(free_complex(R, T, e), n + 1)) ∧ " +
					"    (∀x:(I → A). x ∈ finite_supp(R.zero, R.carrier, S(n + 1)) ⇒ e(n + 1, k(x)) = h(d(n + 1, x)))",
			}, func(
				a *Argument,
				R *Expr[RingOps[A]],
				S *Arrow[Nat, Set[I]],
				d *Expr[Fun3[Nat, Fun[I, A], I, A]],
				sourceIsComplex chain_complex.ChainComplexFact[on.R],
				T *Arrow[Nat, Set[E]],
				e *Expr[Fun3[Nat, Fun[E, A], E, A]],
				targetIsComplex chain_complex.ChainComplexFact[on.R],
				n *Expr[Nat],
				exactAtNext Fact,
				h *Arrow[Fun[I, A], Fun[E, A]],
				linearH, intoBoundaries Fact,
			) {
				next := a.TermAs[Nat]("n + 1")
				U := a.TermAs[ModuleOps[A, Fun[I, A]]]("free_module_record(R, S(n))")
				U1 := a.TermAs[ModuleOps[A, Fun[I, A]]]("free_module_record(R, S(n + 1))")
				V := a.TermAs[ModuleOps[A, Fun[E, A]]]("free_module_record(R, T(n))")
				d1 := a.TermAs[Fun[Fun[I, A], Fun[I, A]]]("d(n + 1)")
				composite := a.TermAs[Fun[Fun[I, A], Fun[E, A]]]("h ∘ d(n + 1)")
				Q := a.TermAs[chain_complex.ComplexOps[A, Fun[E, A]]]("free_complex(R, T, e)")
				linearComposite := a.Have(
					"compose the current lift with the source differential",
					"module_homomorphism(R, "+
						"    free_module_record(R, S(n + 1)), "+
						"    free_module_record(R, T(n)), "+
						"    h ∘ d(n + 1))",
					By(
						linearH,
						sourceIsComplex,
						FreeComplexDifferentialHom.At(R, S, d, n),
						module_homomorphism.HomCompose.At(R, U1, U, V, d1, h)))
				compositeIntoBoundaries := a.Have(
					"h keeps source boundaries in target boundaries, so the composite takes its values there",
					Statement{
						Binders:    "∀x:(I → A).",
						Hypotheses: []string{"x ∈ finite_supp(R.zero, R.carrier, S(n + 1))"},
						Conclusion: "(h ∘ d(n + 1))(x) ∈ boundaries(free_complex(R, T, e), n)",
					},
					By(intoBoundaries, functions.ComposeApply))
				k, lift := a.UnpackAs[Fun[Fun[I, A], Fun[E, A]]](
					GroupPremises(
						targetIsComplex,
						linearComposite,
						compositeIntoBoundaries,
						LiftThroughBoundaries.At(R, T, e, n, a.TermAs[Set[I]]("S(n + 1)"), composite)),
					"k")
				parts := a.Conjuncts(
					lift,
					"the new lift is linear",
					"the adjacent square commutes")
				linearK, square := parts[0], parts[1]
				linearNextD := a.Have(
					"the next source differential lands in the next source term",
					"module_homomorphism(R, "+
						"    free_module_record(R, S(n + 2)), "+
						"    free_module_record(R, S(n + 1)), "+
						"    d(n + 2))",
					By(Normalized, At(nextIndex, n), sourceIsComplex, FreeComplexDifferentialHom.At(R, S, d, next)))
				twiceZero := a.Have(
					"successive source differentials compose to zero",
					Statement{
						Binders: "∀x:(I → A).", Hypotheses: []string{"x ∈ finite_supp(R.zero, R.carrier, S(n + 2))"},
						Conclusion: "d(n + 1, d(n + 2, x)) = fun_zero(R.zero)",
					},
					By(
						chain_complex.ComplexBoundaryTwice.Read(sourceIsComplex).AsFact().At(n),
						FreeComplexFields.At(R, S, d, next),
						FreeComplexFields.At(R, S, d, a.TermAs[Nat]("n + 2"))))
				nextPreserves := a.Have(
					"the new lift preserves boundaries",
					Statement{
						Binders: "∀x:(I → A).", Hypotheses: []string{"x ∈ finite_supp(R.zero, R.carrier, S(n + 2))"},
						Conclusion: "k(d(n + 2, x)) ∈ boundaries(free_complex(R, T, e), n + 1)",
					},
					Derive(func(b *Argument) {
						x := b.FixAs[Fun[I, A]]()
						xIn := b.Assume()
						dx := b.TermAs[Fun[I, A]]("d(n + 2, x)")
						dxIn := b.Have(
							"the source boundary lies in the domain of the new lift",
							"d(n + 2, x) ∈ finite_supp(R.zero, R.carrier, S(n + 1))",
							By(xIn, module_homomorphism.HomIn.Read(linearNextD)))
						killed := b.Have(
							"the adjacent square sends the next source boundary to a target cycle",
							"e(n + 1, k(d(n + 2, x))) = fun_zero(R.zero)",
							By(
								xIn,
								dxIn,
								module_homomorphism.HomZero.Read(linearH),
								twiceZero.At(x),
								square.At(dx),
								functions.ComposeApply))
						kxIn := b.Have(
							"the image lies in the next target term",
							"k(d(n + 2, x)) ∈ finite_supp(R.zero, R.carrier, T(n + 1))",
							By(dxIn, module_homomorphism.HomIn.Read(linearK)))
						cycle := b.Have(
							"the new image is a target cycle",
							"k(d(n + 2, x)) ∈ cycles(free_complex(R, T, e), n + 1)",
							BySets(Normalized, killed, kxIn, chain_complex.CyclesDef.At(Q, next)))
						b.Show(
							"exactness at degree n + 1 makes this cycle a boundary",
							By(cycle, exactAtNext))
					}))
				a.Take(k)
				a.Show(
					"the new lift is linear, preserves boundaries, and fills the adjacent square",
					By(nextPreserves, square, linearK, functions.ComposeApply))
			})

			liftAugmentation := ctx.Lemma(Statement{
				Binders: "∀R:ring_ops(A). " +
					"∀M:module_ops(A, B). " +
					"∀S:(num → set(I)). " +
					"∀d:(num → (I → A) → I → A). " +
					"∀eps:((I → A) → B). " +
					"∀N:module_ops(A, C). " +
					"∀T:(num → set(E)). " +
					"∀e:(num → (E → A) → E → A). " +
					"∀eta:((E → A) → C). " +
					"∀f:(B → C).",
				Hypotheses: []string{
					"free_resolution(R, M, S, d, eps)",
					"free_resolution(R, N, T, e, eta)",
					"module_homomorphism(R, M, N, f)",
				},
				Conclusion: "∃h:((I → A) → E → A). " +
					"    module_homomorphism(R, free_module_record(R, S(0)), free_module_record(R, T(0)), h) ∧ " +
					"    (∀x:(I → A). " +
					"        x ∈ finite_supp(R.zero, R.carrier, S(1)) ⇒ " +
					"        h(d(1, x)) ∈ boundaries(free_complex(R, T, e), 0)) ∧ " +
					"    (∀x:(I → A). x ∈ finite_supp(R.zero, R.carrier, S(0)) ⇒ eta(h(x)) = f(eps(x)))",
			}, func(
				a *Argument,
				R *Expr[RingOps[A]],
				M *Expr[ModuleOps[A, B]],
				S *Arrow[Nat, Set[I]],
				d *Expr[Fun3[Nat, Fun[I, A], I, A]],
				eps *Arrow[Fun[I, A], B],
				source FreeResolutionFact[on.R, on.M],
				N *Expr[ModuleOps[A, C]],
				T *Arrow[Nat, Set[E]],
				e *Expr[Fun3[Nat, Fun[E, A], E, A]],
				eta *Arrow[Fun[E, A], C],
				target FreeResolutionFact[on.R, on.N],
				f *Arrow[B, C],
				linearF Fact,
			) {
				zero, one := a.TermAs[Nat]("0"), a.TermAs[Nat]("1")
				U0 := a.TermAs[ModuleOps[A, Fun[I, A]]]("free_module_record(R, S(0))")
				V0 := a.TermAs[ModuleOps[A, Fun[E, A]]]("free_module_record(R, T(0))")
				epsLinear := a.Have(
					"the source augmentation is linear from the free degree-zero term",
					"module_homomorphism(R, free_module_record(R, S(0)), M, eps)",
					By(Normalized, ResolutionAugmentationHom.Read(source), FreeComplexModule.At(R, S, d, zero)))
				etaLinear := a.Have(
					"the target augmentation is linear from its degree-zero term",
					"module_homomorphism(R, free_module_record(R, T(0)), N, eta)",
					By(Normalized, ResolutionAugmentationHom.Read(target), FreeComplexModule.At(R, T, e, zero)))
				compositeLinear := a.Have(
					"compose the source augmentation with the given module map",
					"module_homomorphism(R, free_module_record(R, S(0)), N, f ∘ eps)",
					By(linearF, epsLinear, module_homomorphism.HomCompose.At(R, U0, M, N, eps, f)))
				h, lifted := a.UnpackAs[Fun[Fun[I, A], Fun[E, A]]](
					GroupPremises(
						etaLinear,
						ResolutionAugmentationOnto.Read(target),
						compositeLinear,
						FreeLiftThrough.At(
							R, V0, N, a.TermAs[Set[I]]("S(0)"), eta, a.TermAs[Fun[Fun[I, A], C]]("f ∘ eps"))),
					"h")
				parts := a.Conjuncts(
					lifted,
					"the initial lift is linear",
					"the augmentation square commutes")
				linearH, square := parts[0], parts[1]
				initialPreserves := a.Have(
					"the initial lift takes source boundaries into target boundaries",
					Statement{
						Binders: "∀x:(I → A).", Hypotheses: []string{"x ∈ finite_supp(R.zero, R.carrier, S(1))"},
						Conclusion: "h(d(1, x)) ∈ boundaries(free_complex(R, T, e), 0)",
					},
					Derive(func(b *Argument) {
						b.FixAs[Fun[I, A]]()
						xIn := b.Assume()
						dx := b.TermAs[Fun[I, A]]("d(1, x)")
						hdx := b.TermAs[Fun[E, A]]("h(d(1, x))")
						P := b.TermAs[chain_complex.ComplexOps[A, Fun[I, A]]]("free_complex(R, S, d)")
						d1 := b.TermAs[Fun[Fun[I, A], Fun[I, A]]]("d(1)")
						sourceCarrier0 := b.TermAs[Set[Fun[I, A]]]("finite_supp(R.zero, R.carrier, S(0))")
						sourceCarrier1 := b.TermAs[Set[Fun[I, A]]]("finite_supp(R.zero, R.carrier, S(1))")
						targetCarrier0 := b.TermAs[Set[Fun[E, A]]]("finite_supp(R.zero, R.carrier, T(0))")
						mZero, nZero := b.TermAs[B]("M.zero"), b.TermAs[C]("N.zero")
						inKernel := b.Have(
							"the first source boundary lies in the augmentation kernel",
							"d(1, x) ∈ group_kernel(M.zero, finite_supp(R.zero, R.carrier, S(0)), eps)",
							By(
								ResolutionAugmentationKernel.Read(source),
								nat_arith.AddLeftZeroClause.At(one),
								xIn,
								chain_complex.BoundariesDef.At(P, zero),
								FreeComplexFields.At(R, S, d, one),
								set_basic.InImage.At(d1, sourceCarrier1, dx)))
						kernelData := b.Have(
							"the boundary lies in degree zero and its augmentation vanishes",
							"d(1, x) ∈ finite_supp(R.zero, R.carrier, S(0)) ∧ eps(d(1, x)) = M.zero",
							By(inKernel, group_homomorphism.InKernel.At(mZero, sourceCarrier0, eps, dx)))
						hdxIn := b.Have(
							"the lifted boundary lies in target degree zero",
							"h(d(1, x)) ∈ finite_supp(R.zero, R.carrier, T(0))",
							By(module_homomorphism.HomIn.Read(linearH), kernelData))
						killed := b.Have(
							"the augmentation square kills the lifted boundary",
							"eta(h(d(1, x))) = N.zero",
							By(module_homomorphism.HomZero.Read(linearF), kernelData, square.At(dx), functions.ComposeApply))
						b.Show(
							"the target augmentation kernel consists of boundaries",
							By(
								ResolutionAugmentationKernel.Read(target),
								hdxIn,
								killed,
								group_homomorphism.InKernel.At(nZero, targetCarrier0, eta, hdx)))
					}))
				a.Take(h)
				a.Show(
					"the initial lift is linear, preserves boundaries, and fills the augmentation square",
					By(square, initialPreserves, linearH, functions.ComposeApply))
			})

			return ctx.Theorem(headline, func(
				a *Argument,
				R *Expr[RingOps[A]],
				M *Expr[ModuleOps[A, B]],
				S *Arrow[Nat, Set[I]],
				d *Expr[Fun3[Nat, Fun[I, A], I, A]],
				eps *Arrow[Fun[I, A], B],
				source FreeResolutionFact[on.R, on.M],
				N *Expr[ModuleOps[A, C]],
				T *Arrow[Nat, Set[E]],
				e *Expr[Fun3[Nat, Fun[E, A], E, A]],
				eta *Arrow[Fun[E, A], C],
				target FreeResolutionFact[on.R, on.N],
				f *Arrow[B, C],
				linearF Fact,
			) {
				LinearKeepsBoundaries, linearKeepsBoundariesDef := a.LetAs[Fun2[Nat, Fun[Fun[I, A], Fun[E, A]], Bool]](
					"LinearKeepsBoundaries",
					"λn:num. λh:((I → A) → E → A). "+
						"    module_homomorphism(R, free_module_record(R, S(n)), free_module_record(R, T(n)), h) ∧ "+
						"    (∀x:(I → A). "+
						"        x ∈ finite_supp(R.zero, R.carrier, S(n + 1)) ⇒ "+
						"        h(d(n + 1, x)) ∈ boundaries(free_complex(R, T, e), n))")
				Square, squareDef := a.LetAs[Fun3[Nat, Fun[Fun[I, A], Fun[E, A]], Fun[Fun[I, A], Fun[E, A]], Bool]](
					"Square",
					"λn:num. λh:((I → A) → E → A). λk:((I → A) → E → A). ∀x:(I → A). "+
						"    x ∈ finite_supp(R.zero, R.carrier, S(n + 1)) ⇒ e(n + 1, k(x)) = h(d(n + 1, x))")
				h0, initial := a.UnpackAs[Fun[Fun[I, A], Fun[E, A]]](
					GroupPremises(source, target, linearF, At(liftAugmentation, R, M, S, d, eps, N, T, e, eta, f)),
					"h₀")
				initialPreserves := a.Have(
					"the augmentation lift is linear and keeps boundaries at degree zero",
					"LinearKeepsBoundaries(0, h₀)",
					By(linearKeepsBoundariesDef, initial, nat_arith.AddLeftZeroClause.At(a.TermAs[Nat]("1"))))
				step := a.Have(
					"the degree lift extends every linear map that keeps boundaries",
					Statement{
						Binders: "∀n:num. ∀h:((I → A) → E → A).", Hypotheses: []string{"LinearKeepsBoundaries(n, h)"},
						Conclusion: "∃k:((I → A) → E → A). LinearKeepsBoundaries(n + 1, k) ∧ Square(n, h, k)",
					},
					Derive(func(b *Argument) {
						n := b.FixAs[Nat]()
						h := b.FixAs[Fun[Fun[I, A], Fun[E, A]]]()
						preserves := b.Assume()
						b.Do(linearKeepsBoundariesDef.Rw(), squareDef.Rw())
						b.Show(
							"the degree lift supplies a linear successor that keeps boundaries, and the adjacent square",
							By(
								At(nextIndex, n),
								preserves,
								ResolutionComplex.Read(source),
								ResolutionComplex.Read(target),
								ResolutionExact.Read(target).At(n),
								At(liftDegree, R, S, d, T, e, n, h)))
					}))
				g, assembled := a.UnpackAs[Fun3[Nat, Fun[I, A], E, A]](
					GroupPremises(
						initialPreserves,
						step,
						nat_arith.DependentChoice.At(LinearKeepsBoundaries, Square, h0)),
					"g")
				parts := a.Conjuncts(
					assembled,
					"the sequence starts at the augmentation lift",
					"each degree map is linear and keeps boundaries, and its adjacent square commutes")
				starts, degrees := parts[0], parts[1]
				a.Take(g)
				a.Show(
					"the assembled maps form a chain map lifting f",
					SplitConj(
						Case(
							"the degree maps form a chain map",
							Simp(Fwd(chain_complex.ChainMapDef)),
							SplitConj(
								Case(
									"every degree map is linear",
									Derive(func(b *Argument) {
										n := b.FixAs[Nat]()
										b.Show(
											"project the linearity conjunct of LinearKeepsBoundaries: "+
												"the degree map is linear between the free terms",
											By(
												Normalized,
												degrees.At(n),
												linearKeepsBoundariesDef,
												FreeComplexModule.At(R, S, d, n),
												FreeComplexModule.At(R, T, e, n)))
									})),
								Case(
									"every adjacent differential square commutes",
									Derive(func(b *Argument) {
										n := b.FixAs[Nat]()
										b.FixAs[Fun[I, A]]()
										xIn := b.Assume()
										b.Show(
											"the recursive adjacent relation is the chain-map square",
											By(degrees.At(n), squareDef, xIn))
									})))),
						Case(
							"the augmentation square commutes",
							starts.Rw(),
							By(initial))))
			})
		}),
})}

// ResolutionComparisonHomotopy — two chain maps from a free chain complex
// into a free resolution that agree after the augmentation are chain
// homotopic. Their difference delta is a chain map that carries the
// degree-zero term into the kernel of the augmentation, which is the
// boundaries at 0, so delta(0) lifts through e(1) to h(0)
// (LiftThroughBoundaries). Once h(n) is linear and e(n + 1) agrees on
// delta(n + 1) and on h(n) after d(n + 1), the map
// delta(n + 1) − h(n) ∘ d(n + 1) lands in the cycles at n + 1, which
// exactness makes boundaries, and lifts through e(n + 2) to h(n + 1); the
// relation of the lift is the homotopy identity in degree n + 1, and
// d ∘ d = 0 carries the invariant one degree up (extendHomotopy). The
// lifts are assembled into one sequence by dependent choice along ℕ
// (nat_arith.DependentChoice).
var ResolutionComparisonHomotopy = resolutionComparisonHomotopyThm{family.Add(registry.ProofEntry{
	Name: "ResolutionComparisonHomotopy",
	Key:  "prop_c8fbfb93fea8985d",
	Build: family.Sections(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:(num → set(I)). " +
			"∀d:(num → (I → A) → I → A). " +
			"∀N:module_ops(A, C). " +
			"∀T:(num → set(E)). " +
			"∀e:(num → (E → A) → E → A). " +
			"∀eta:((E → A) → C). " +
			"∀g g':(num → (I → A) → E → A).",
		Hypotheses: []string{
			"chain_complex(R, free_complex(R, S, d))",
			"free_resolution(R, N, T, e, eta)",
			"chain_map(R, free_complex(R, S, d), free_complex(R, T, e), g)",
			"chain_map(R, free_complex(R, S, d), free_complex(R, T, e), g')",
			"∀x:(I → A). x ∈ finite_supp(R.zero, R.carrier, S(0)) ⇒ eta(g(0)(x)) = eta(g'(0)(x))",
		},
		Conclusion: "∃h:(num → (I → A) → E → A). " +
			"    chain_homotopy(R, free_complex(R, S, d), free_complex(R, T, e), g, g', h)",
	},
		func(ctx *Script, headline string) *GoalStackNode {
			// extendHomotopy and Splits are stated at n + 2; the lift through the
			// differential out of n + 1 + 1, the square of delta at n + 1 and
			// RemainderIsCycle taken one degree up spell that degree n + 1 + 1.
			nextIndex := ctx.Lemma(
				"∀n:num. n + 1 + 1 = n + 2",
				func(a *Argument, n *Expr[Nat]) {
					a.Show(
						"two adjacent successor degrees agree",
						ByArith())
				})

			// A chain map between free complexes, read in the free terms: its
			// components are linear between the free modules, and it commutes
			// with the given differentials d and e.
			freeChainMap := ctx.Lemma(Statement{
				Binders: "∀R:ring_ops(A). " +
					"∀S:(num → set(I)). " +
					"∀d:(num → (I → A) → I → A). " +
					"∀T:(num → set(E)). " +
					"∀e:(num → (E → A) → E → A). " +
					"∀g:(num → (I → A) → E → A).",
				Hypotheses: []string{"chain_map(R, free_complex(R, S, d), free_complex(R, T, e), g)"},
				Conclusion: "(∀n:num. " +
					"    module_homomorphism(R, free_module_record(R, S(n)), free_module_record(R, T(n)), g(n))) ∧ " +
					"(∀n:num. ∀x:(I → A). " +
					"    x ∈ finite_supp(R.zero, R.carrier, S(n + 1)) ⇒ g(n, d(n + 1, x)) = e(n + 1, g(n + 1, x)))",
			}, func(
				a *Argument,
				R *Expr[RingOps[A]],
				S *Arrow[Nat, Set[I]],
				d *Expr[Fun3[Nat, Fun[I, A], I, A]],
				T *Arrow[Nat, Set[E]],
				e *Expr[Fun3[Nat, Fun[E, A], E, A]],
				g *Arrow2[Nat, Fun[I, A], Fun[E, A]],
				chain Fact,
			) {
				a.Show(
					"the components and squares of g, read in the free terms",
					SplitConj(
						Case(
							"each component is linear between the free modules its degree modules are",
							Derive(func(b *Argument) {
								n := b.FixAs[Nat]()
								b.Show(
									"the degree modules of both complexes are the free modules",
									By(
										Normalized,
										chain_complex.ChainMapHom.Read(chain).At(n),
										FreeComplexModule.At(R, S, d, n),
										FreeComplexModule.At(R, T, e, n)))
							})),
						Case(
							"each square is the chain-map square with the complexes' differentials d and e",
							Derive(func(b *Argument) {
								n := b.FixAs[Nat]()
								x := b.FixAs[Fun[I, A]]()
								xIn := b.Assume()
								next := b.TermAs[Nat]("n + 1")
								b.Show(
									"the free complexes' terms and differentials are the given ones",
									By(
										xIn,
										chain_complex.ChainMapSquare.Read(chain).At(n, x),
										FreeComplexFields.At(R, S, d, next),
										FreeComplexFields.At(R, T, e, next)))
							}))))
			})

			// The inductive step, the target exact at n + 1: when h is linear from
			// the free term on S(n) to the one on T(n + 1) and e(n + 1) agrees on
			// delta(n + 1) and on h ∘ d(n + 1), a linear k one degree up splits
			// delta(n + 1) as e(n + 2) ∘ k + h ∘ d(n + 1), and e(n + 2) agrees on
			// delta(n + 2) and on k ∘ d(n + 2).
			extendHomotopy := ctx.Lemma(Statement{
				Binders: "∀R:ring_ops(A). " +
					"∀S:(num → set(I)). " +
					"∀d:(num → (I → A) → I → A). " +
					"∀T:(num → set(E)). " +
					"∀e:(num → (E → A) → E → A). " +
					"∀delta:(num → (I → A) → E → A). " +
					"∀n:num. " +
					"∀h:((I → A) → E → A).",
				Hypotheses: []string{
					"chain_complex(R, free_complex(R, S, d))",
					"chain_complex(R, free_complex(R, T, e))",
					"module_homomorphism(R, " +
						"    free_module_record(R, S(n + 1)), " +
						"    free_module_record(R, T(n + 1)), " +
						"    delta(n + 1))",
					"∀x:(I → A). " +
						"    x ∈ finite_supp(R.zero, R.carrier, S(n + 2)) ⇒ " +
						"    delta(n + 1, d(n + 2, x)) = e(n + 2, delta(n + 2, x))",
					"cycles(free_complex(R, T, e), n + 1) = boundaries(free_complex(R, T, e), n + 1)",
					"module_homomorphism(R, free_module_record(R, S(n)), free_module_record(R, T(n + 1)), h)",
					"∀x:(I → A). " +
						"    x ∈ finite_supp(R.zero, R.carrier, S(n + 1)) ⇒ " +
						"    e(n + 1, delta(n + 1, x)) = e(n + 1, h(d(n + 1, x)))",
				},
				Conclusion: "∃k:((I → A) → E → A). " +
					"    module_homomorphism(R, " +
					"        free_module_record(R, S(n + 1)), " +
					"        free_module_record(R, T(n + 2)), " +
					"        k) ∧ " +
					"    (∀x:(I → A). " +
					"        x ∈ finite_supp(R.zero, R.carrier, S(n + 2)) ⇒ " +
					"        e(n + 2, delta(n + 2, x)) = e(n + 2, k(d(n + 2, x)))) ∧ " +
					"    (∀x:(I → A). " +
					"        x ∈ finite_supp(R.zero, R.carrier, S(n + 1)) ⇒ " +
					"        delta(n + 1, x) = fun_add(R.add, e(n + 2, k(x)), h(d(n + 1, x))))",
				Abbrev: Abbrev{
					{Name: "psi", Text: "λx:(I → A). fun_add(R.add, delta(n + 1, x), fun_neg(R.neg, h(d(n + 1, x))))"},
				},
			}, func(
				a *Argument,
				R *Expr[RingOps[A]],
				S *Arrow[Nat, Set[I]],
				d *Expr[Fun3[Nat, Fun[I, A], I, A]],
				source chain_complex.ChainComplexFact[on.R],
				T *Arrow[Nat, Set[E]],
				e *Expr[Fun3[Nat, Fun[E, A], E, A]],
				target chain_complex.ChainComplexFact[on.R],
				delta *Expr[Fun3[Nat, Fun[I, A], E, A]],
				n *Expr[Nat],
				linearDelta, squareDelta, exactAtNext Fact,
				h *Arrow[Fun[I, A], Fun[E, A]],
				linearH, agree Fact,
			) {
				next := a.TermAs[Nat]("n + 1")
				U := a.TermAs[ModuleOps[A, Fun[I, A]]]("free_module_record(R, S(n))")
				U1 := a.TermAs[ModuleOps[A, Fun[I, A]]]("free_module_record(R, S(n + 1))")
				V1 := a.TermAs[ModuleOps[A, Fun[E, A]]]("free_module_record(R, T(n + 1))")
				Q := a.TermAs[chain_complex.ComplexOps[A, Fun[E, A]]]("free_complex(R, T, e)")
				Tn := a.TermAs[Set[E]]("T(n)")
				Tnext := a.TermAs[Set[E]]("T(n + 1)")
				hd := a.TermAs[Fun[Fun[I, A], Fun[E, A]]]("h ∘ d(n + 1)")
				psi := a.TermAs[Fun[Fun[I, A], Fun[E, A]]]("«psi»")
				linearComposite := a.Have(
					"compose h with the source differential",
					"module_homomorphism(R, "+
						"    free_module_record(R, S(n + 1)), "+
						"    free_module_record(R, T(n + 1)), "+
						"    h ∘ d(n + 1))",
					By(
						linearH,
						source,
						FreeComplexDifferentialHom.At(R, S, d, n),
						module_homomorphism.HomCompose.At(
							R, U1, U, V1, a.TermAs[Fun[Fun[I, A], Fun[I, A]]]("d(n + 1)"), h)))
				linearPsi := a.Have(
					"delta(n + 1) minus h after d(n + 1) is linear",
					"module_homomorphism(R, free_module_record(R, S(n + 1)), free_module_record(R, T(n + 1)), «psi»)",
					By(
						linearDelta,
						linearComposite,
						module_homomorphism.HomDiff.At(R, U1, V1, a.TermAs[Fun[Fun[I, A], Fun[E, A]]]("delta(n + 1)"), hd),
						free_module.FreeModuleRecordDef,
						functions.ComposeApply))
				intoBoundaries := a.Have(
					"the difference takes the source term into the boundaries at n + 1",
					Statement{
						Binders:    "∀x:(I → A).",
						Hypotheses: []string{"x ∈ finite_supp(R.zero, R.carrier, S(n + 1))"},
						Conclusion: "«psi»(x) ∈ boundaries(free_complex(R, T, e), n + 1)",
					},
					Derive(func(b *Argument) {
						x := b.FixAs[Fun[I, A]]()
						xIn := b.Assume()
						killed := b.Have(
							"e(n + 1) kills it, as it agrees on delta(n + 1)(x) and on h(d(n + 1)(x))",
							"e(n + 1, «psi»(x)) = fun_zero(R.zero)",
							ByChase(
								Depth(0),
								agree.At(x),
								xIn,
								linearDelta,
								linearH,
								target,
								source,
								FreeComplexDifferentialHom.At(R, T, e, n),
								FreeComplexDifferentialHom.At(R, S, d, n),
								free_module.FreeModuleRecordDef.At(R, Tnext),
								free_module.FreeModuleRecordDef.At(R, Tn)))
						cycle := b.Have(
							"so it is a cycle at n + 1, lying in the free term on T(n + 1) as a value of a linear map",
							"«psi»(x) ∈ cycles(free_complex(R, T, e), n + 1)",
							BySets(
								Normalized,
								killed,
								xIn,
								module_homomorphism.HomIn.Read(linearPsi),
								chain_complex.CyclesDef.At(Q, next)))
						b.Show(
							"exactness at n + 1 makes the cycle a boundary",
							By(cycle, exactAtNext))
					}))
				k, lift := a.UnpackAs[Fun[Fun[I, A], Fun[E, A]]](
					GroupPremises(
						target,
						linearPsi,
						intoBoundaries,
						LiftThroughBoundaries.At(R, T, e, next, a.TermAs[Set[I]]("S(n + 1)"), psi)),
					"k")
				parts := a.Conjuncts(
					lift,
					"k is linear into the free term on T(n + 2)",
					"e(n + 2) after k is the difference")
				linearK, square := parts[0], parts[1]
				splits := a.Have(
					"delta(n + 1) splits as e(n + 2) after k plus h after d(n + 1)",
					Statement{
						Binders:    "∀x:(I → A).",
						Hypotheses: []string{"x ∈ finite_supp(R.zero, R.carrier, S(n + 1))"},
						Conclusion: "delta(n + 1, x) = fun_add(R.add, e(n + 2, k(x)), h(d(n + 1, x)))",
					},
					Derive(func(b *Argument) {
						x := b.FixAs[Fun[I, A]]()
						xIn := b.Assume()
						b.Show(
							"e(n + 2) sends k(x) to delta(n + 1)(x) minus h(d(n + 1)(x)); add h(d(n + 1)(x)) back",
							ByChase(
								Depth(0),
								square.At(x),
								xIn,
								linearH,
								linearK,
								linearDelta,
								target,
								source,
								FreeComplexDifferentialHom.At(R, T, e, next),
								FreeComplexDifferentialHom.At(R, S, d, n),
								free_module.FreeModuleRecordDef.At(R, Tnext)))
					}))
				twiceZero := a.Have(
					"successive source differentials compose to zero",
					Statement{
						Binders:    "∀x:(I → A).",
						Hypotheses: []string{"x ∈ finite_supp(R.zero, R.carrier, S(n + 2))"},
						Conclusion: "d(n + 1, d(n + 2, x)) = fun_zero(R.zero)",
					},
					By(
						chain_complex.ComplexBoundaryTwice.Read(source).AsFact().At(n),
						FreeComplexFields.At(R, S, d, next),
						FreeComplexFields.At(R, S, d, a.TermAs[Nat]("n + 2"))))
				agreeNext := a.Have(
					"e(n + 2) agrees on delta(n + 2) and on k after d(n + 2)",
					Statement{
						Binders:    "∀x:(I → A).",
						Hypotheses: []string{"x ∈ finite_supp(R.zero, R.carrier, S(n + 2))"},
						Conclusion: "e(n + 2, delta(n + 2, x)) = e(n + 2, k(d(n + 2, x)))",
					},
					Derive(func(b *Argument) {
						x := b.FixAs[Fun[I, A]]()
						xIn := b.Assume()
						b.Show(
							"both sides are delta(n + 1)(d(n + 2)(x)): the square "+
								"of delta, the square of k, d ∘ d = 0 and h(0) = 0",
							ByChase(
								Depth(0),
								squareDelta,
								square,
								twiceZero.At(x),
								xIn,
								linearH,
								linearK,
								linearDelta,
								source,
								target,
								FreeComplexDifferentialHom.At(R, S, d, next),
								FreeComplexDifferentialHom.At(R, S, d, n),
								FreeComplexDifferentialHom.At(R, T, e, next),
								free_module.FreeModuleRecordDef.At(R, Tnext),
								free_module.FreeModuleRecordDef.At(R, a.TermAs[Set[I]]("S(n)"))))
					}))
				a.Take(k)
				a.Show(
					"k is linear, agrees one degree up, and splits delta(n + 1)",
					By(Normalized, At(nextIndex, n), linearK, agreeNext, splits))
			})

			return ctx.Theorem(headline, func(
				a *Argument,
				R *Expr[RingOps[A]],
				S *Arrow[Nat, Set[I]],
				d *Expr[Fun3[Nat, Fun[I, A], I, A]],
				source chain_complex.ChainComplexFact[on.R],
				N *Expr[ModuleOps[A, C]],
				T *Arrow[Nat, Set[E]],
				e *Expr[Fun3[Nat, Fun[E, A], E, A]],
				eta *Arrow[Fun[E, A], C],
				target FreeResolutionFact[on.R, on.N],
				g, gʹ *Arrow2[Nat, Fun[I, A], Fun[E, A]],
				chainG, chainGʹ, agree Fact,
			) {
				zero, one := a.TermAs[Nat]("0"), a.TermAs[Nat]("1")
				freeG := a.Conjuncts(
					GroupPremises(chainG, At(freeChainMap, R, S, d, T, e, g)),
					"each g(n) is linear between the free terms",
					"g commutes with d and e")
				linearG, squareG := freeG[0], freeG[1]
				freeGʹ := a.Conjuncts(
					GroupPremises(chainGʹ, At(freeChainMap, R, S, d, T, e, gʹ)),
					"each g'(n) is linear between the free terms",
					"g' commutes with d and e")
				linearGʹ, squareGʹ := freeGʹ[0], freeGʹ[1]
				delta, deltaDef := a.LetAs[Fun3[Nat, Fun[I, A], E, A]](
					"delta", "λn:num. λx:(I → A). fun_add(R.add, g(n, x), fun_neg(R.neg, g'(n, x)))")
				linearDelta := a.Have(
					"delta is linear in every degree",
					"∀n:num. "+
						"    module_homomorphism(R, free_module_record(R, S(n)), free_module_record(R, T(n)), delta(n))",
					Derive(func(b *Argument) {
						n := b.FixAs[Nat]()
						b.Show(
							"the difference of two linear maps is linear",
							By(
								deltaDef,
								linearG.At(n),
								linearGʹ.At(n),
								module_homomorphism.HomDiff.At(
									R,
									b.TermAs[ModuleOps[A, Fun[I, A]]]("free_module_record(R, S(n))"),
									b.TermAs[ModuleOps[A, Fun[E, A]]]("free_module_record(R, T(n))"),
									b.TermAs[Fun[Fun[I, A], Fun[E, A]]]("g(n)"),
									b.TermAs[Fun[Fun[I, A], Fun[E, A]]]("g'(n)")),
								free_module.FreeModuleRecordDef))
					}))
				squareDelta := a.Have(
					"delta commutes with the differentials",
					Statement{
						Binders:    "∀n:num. ∀x:(I → A).",
						Hypotheses: []string{"x ∈ finite_supp(R.zero, R.carrier, S(n + 1))"},
						Conclusion: "delta(n, d(n + 1, x)) = e(n + 1, delta(n + 1, x))",
					},
					Derive(func(b *Argument) {
						n := b.FixAs[Nat]()
						b.FixAs[Fun[I, A]]()
						xIn := b.Assume()
						b.Show(
							"e(n + 1) is linear, and g and g' commute with d and e",
							deltaDef.Rw(),
							ByChase(
								Depth(0),
								xIn,
								linearG,
								linearGʹ,
								squareG,
								squareGʹ,
								source,
								ResolutionComplex.Read(target),
								FreeComplexDifferentialHom.At(R, T, e, n),
								FreeComplexDifferentialHom.At(R, S, d, n),
								free_module.FreeModuleRecordDef.At(R, b.TermAs[Set[E]]("T(n + 1)")),
								free_module.FreeModuleRecordDef.At(R, b.TermAs[Set[E]]("T(n)"))))
					}))
				etaLinear := a.Have(
					"the target augmentation is linear from its free degree-zero term",
					"module_homomorphism(R, free_module_record(R, T(0)), N, eta)",
					By(Normalized, ResolutionAugmentationHom.Read(target), FreeComplexModule.At(R, T, e, zero)))
				intoKernel := a.Have(
					"delta(0) takes the degree-zero term into the boundaries at 0",
					Statement{
						Binders:    "∀x:(I → A).",
						Hypotheses: []string{"x ∈ finite_supp(R.zero, R.carrier, S(0))"},
						Conclusion: "delta(0, x) ∈ boundaries(free_complex(R, T, e), 0)",
					},
					Derive(func(b *Argument) {
						x := b.FixAs[Fun[I, A]]()
						xIn := b.Assume()
						killed := b.Have(
							"eta kills delta(0)(x): g(0) and g'(0) agree after eta",
							"eta(delta(0, x)) = N.zero",
							deltaDef.Rw(),
							ByChase(
								Depth(0),
								agree.At(x),
								xIn,
								linearG,
								linearGʹ,
								etaLinear,
								free_module.FreeModuleRecordDef.At(R, b.TermAs[Set[E]]("T(0)"))))
						b.Show(
							"the kernel of eta is the boundaries at 0",
							By(
								killed,
								xIn,
								linearDelta.At(zero),
								module_homomorphism.HomIn,
								ResolutionAugmentationKernel.Read(target),
								group_homomorphism.InKernel.At(
									b.TermAs[C]("N.zero"),
									b.TermAs[Set[Fun[E, A]]]("finite_supp(R.zero, R.carrier, T(0))"),
									eta,
									b.TermAs[Fun[E, A]]("delta(0, x)"))))
					}))
				h0, initial := a.UnpackAs[Fun[Fun[I, A], Fun[E, A]]](
					GroupPremises(
						ResolutionComplex.Read(target),
						linearDelta.At(zero),
						intoKernel,
						LiftThroughBoundaries.At(
							R, T, e, zero, a.TermAs[Set[I]]("S(0)"), a.TermAs[Fun[Fun[I, A], Fun[E, A]]]("delta(0)"))),
					"h₀")
				lifted := a.Conjuncts(
					initial,
					"h₀ is linear into the free term on T(1)",
					"e(1) after h₀ is delta(0)")
				linearH0, square0 := lifted[0], lifted[1]
				// RemainderIsCycle(n, h): h is linear from degree n to degree n + 1, and
				// e(n + 1) agrees on delta(n + 1) and on h ∘ d(n + 1), so it kills the
				// remainder delta(n + 1) − h ∘ d(n + 1).
				RemainderIsCycle, remainderIsCycleDef := a.LetAs[Fun2[Nat, Fun[Fun[I, A], Fun[E, A]], Bool]](
					"RemainderIsCycle",
					"λn:num. λh:((I → A) → E → A). "+
						"    module_homomorphism(R, free_module_record(R, S(n)), free_module_record(R, T(n + 1)), h) ∧ "+
						"    (∀x:(I → A). "+
						"        x ∈ finite_supp(R.zero, R.carrier, S(n + 1)) ⇒ "+
						"        e(n + 1, delta(n + 1, x)) = e(n + 1, h(d(n + 1, x))))")
				Splits, splitsDef := a.LetAs[Fun3[Nat, Fun[Fun[I, A], Fun[E, A]], Fun[Fun[I, A], Fun[E, A]], Bool]](
					"Splits",
					"λn:num. λh:((I → A) → E → A). λk:((I → A) → E → A). ∀x:(I → A). "+
						"    x ∈ finite_supp(R.zero, R.carrier, S(n + 1)) ⇒ "+
						"    delta(n + 1, x) = fun_add(R.add, e(n + 2, k(x)), h(d(n + 1, x)))")
				initialRemainder := a.Have(
					"h₀ is linear and e(1) agrees on delta(1) and on h₀ after d(1)",
					"RemainderIsCycle(0, h₀)",
					remainderIsCycleDef.Rw(),
					SplitConj(
						Case(
							"h₀ is linear",
							By(linearH0)),
						Case(
							"both are delta(0) after d(1), by the square of delta and the square of h₀",
							Derive(func(b *Argument) {
								x := b.FixAs[Fun[I, A]]()
								xIn := b.Assume()
								b.Show(
									"the square of h₀ read at d(1)(x), a member of the degree-zero term",
									By(
										squareDelta.At(zero, x),
										// d(1)(x) as squareDelta.At(zero, x) spells it
										square0.At(b.TermAs[Fun[I, A]]("d(0 + 1, x)")),
										xIn,
										FreeComplexDifferentialHom.At(R, S, d, zero),
										source,
										module_homomorphism.HomIn))
							}))))
				step := a.Have(
					"each linear map whose remainder is a cycle has a "+
						"successor of the same kind that splits delta(n + 1)",
					Statement{
						Binders:    "∀n:num. ∀h:((I → A) → E → A).",
						Hypotheses: []string{"RemainderIsCycle(n, h)"},
						Conclusion: "∃k:((I → A) → E → A). RemainderIsCycle(n + 1, k) ∧ Splits(n, h, k)",
					},
					Derive(func(b *Argument) {
						n := b.FixAs[Nat]()
						h := b.FixAs[Fun[Fun[I, A], Fun[E, A]]]()
						remainderCycle := b.Assume()
						b.Do(remainderIsCycleDef.Rw(), splitsDef.Rw())
						next := b.TermAs[Nat]("n + 1")
						b.Show(
							"the inductive step extends h by a lift through e(n + 2)",
							By(
								At(nextIndex, n),
								remainderCycle,
								linearDelta.At(next),
								squareDelta.At(next),
								source,
								ResolutionComplex.Read(target),
								ResolutionExact.Read(target).At(n),
								At(extendHomotopy, R, S, d, T, e, delta, n, h)))
					}))
				H, assembled := a.UnpackAs[Fun3[Nat, Fun[I, A], E, A]](
					GroupPremises(
						initialRemainder,
						step,
						nat_arith.DependentChoice.At(RemainderIsCycle, Splits, h0)),
					"H")
				parts := a.Conjuncts(
					assembled,
					"the sequence starts at h₀",
					"each H(n) is linear with a cycle as remainder, and H(n + 1) splits delta(n + 1) against H(n)")
				starts, degrees := parts[0], parts[1]
				a.Take(H)
				a.Show(
					"the sequence is a chain homotopy from g to g'",
					Simp(Fwd(chain_complex.ChainHomotopyDef)),
					SplitConjAll(
						Case(
							"each H(n) is linear from degree n to degree n + 1",
							Derive(func(b *Argument) {
								n := b.FixAs[Nat]()
								b.Show(
									"the linearity conjunct of RemainderIsCycle, between the degree modules",
									By(
										degrees.At(n),
										remainderIsCycleDef,
										FreeComplexModule.At(R, S, d, n),
										FreeComplexModule.At(R, T, e, b.TermAs[Nat]("n + 1"))))
							})),
						Case(
							"in degree n + 1 the difference is e(n + 2) after H(n + 1) plus H(n) after d(n + 1)",
							Derive(func(b *Argument) {
								n := b.FixAs[Nat]()
								b.FixAs[Fun[I, A]]()
								uIn := b.Assume()
								b.Do(splitsDef.Rw(), deltaDef.Rw())
								b.Show(
									"Splits(n, H(n), H(n + 1))",
									By(degrees.At(n), uIn))
							})),
						Case(
							"in degree 0 the difference is e(1) after H(0) = h₀",
							By(starts, square0, deltaDef, nat_arith.AddLeftZeroClause.At(one)))))
			})
		}),
})}

// ResolutionComparisonEquivalence — chain maps between two free
// resolutions of one module, each lifting the identity of the module, are
// inverse chain homotopy equivalences: each round trip is a chain map of
// its own resolution that agrees with that resolution's identity after the
// augmentation, and two such chain maps are homotopic.
var ResolutionComparisonEquivalence = resolutionComparisonEquivalenceThm{family.Add(registry.ProofEntry{
	Name: "ResolutionComparisonEquivalence",
	Key:  "prop_b4ab58f99996f605",
	Build: family.Sections(FreeResolution.Statement(Statement{
		Binders: "∀T:(num → set(E)). " +
			"∀e:(num → (E → A) → E → A). " +
			"∀eta:((E → A) → B). " +
			"∀g:(num → (I → A) → E → A). " +
			"∀g':(num → (E → A) → I → A).",
		Hypotheses: []string{
			"free_resolution(R, M, T, e, eta)",
			"chain_map(R, free_complex(R, S, d), free_complex(R, T, e), g)",
			"chain_map(R, free_complex(R, T, e), free_complex(R, S, d), g')",
			"∀x:(I → A). x ∈ finite_supp(R.zero, R.carrier, S(0)) ⇒ eta(g(0)(x)) = eps(x)",
			"∀y:(E → A). y ∈ finite_supp(R.zero, R.carrier, T(0)) ⇒ eps(g'(0)(y)) = eta(y)",
		},
		Conclusion: "chain_homotopy_equivalence(R, free_complex(R, S, d), free_complex(R, T, e), g, g')",
	}),
		func(ctx *Script, headline string) *GoalStackNode {
			// The round trip P → Q → P, P the free complex of the resolution on
			// S and Q the free complex on T, is homotopic to the identity of P.
			// Q need not be a resolution, so the lemma serves both round trips.
			roundTrip := ctx.Lemma(FreeResolution.Statement(Statement{
				Binders: "∀T:(num → set(E)). " +
					"∀e:(num → (E → A) → E → A). " +
					"∀eta:((E → A) → B). " +
					"∀g:(num → (I → A) → E → A). " +
					"∀g':(num → (E → A) → I → A).",
				Hypotheses: []string{
					"chain_map(R, free_complex(R, S, d), free_complex(R, T, e), g)",
					"chain_map(R, free_complex(R, T, e), free_complex(R, S, d), g')",
					"∀x:(I → A). x ∈ finite_supp(R.zero, R.carrier, S(0)) ⇒ eta(g(0)(x)) = eps(x)",
					"∀y:(E → A). y ∈ finite_supp(R.zero, R.carrier, T(0)) ⇒ eps(g'(0)(y)) = eta(y)",
				},
				Conclusion: "∃k:(num → (I → A) → I → A). " +
					"    chain_homotopy(R, " +
					"        free_complex(R, S, d), " +
					"        free_complex(R, S, d), " +
					"        λn:num. λx:(I → A). g'(n)(g(n)(x)), " +
					"        λn:num. λx:(I → A). x, " +
					"        k)",
			}),
				func(
					a *Argument,
					R *Expr[RingOps[A]],
					M *Expr[ModuleOps[A, B]],
					S *Arrow[Nat, Set[I]],
					d *Arrow2[Nat, Fun[I, A], Fun[I, A]],
					eps *Arrow[Fun[I, A], B],
					res FreeResolutionFact[on.R, on.M],
					T *Arrow[Nat, Set[E]],
					e *Arrow2[Nat, Fun[E, A], Fun[E, A]],
					eta *Arrow[Fun[E, A], B],
					g *Arrow2[Nat, Fun[I, A], Fun[E, A]],
					gʹ *Arrow2[Nat, Fun[E, A], Fun[I, A]],
					maps Fact,
				) {
					given := a.Conjuncts(
						maps,
						"g is a chain map P → Q",
						"g' is a chain map Q → P",
						"g lifts the identity of M",
						"g' lifts the identity of M")
					chainG, chainGʹ, liftG, liftGʹ := given[0], given[1], given[2], given[3]
					throughQ := a.Have(
						"g' ∘ g is a chain map of P",
						"chain_map(R, free_complex(R, S, d), free_complex(R, S, d), λn:num. λx:(I → A). g'(n)(g(n)(x)))",
						By(chain_complex.ChainMapCompose, chainG, chainGʹ))
					lifts := a.Have(
						"g' ∘ g lifts the identity of M: eps(g'(0)(g(0)(x))) = eta(g(0)(x)) = eps(x)",
						"∀x:(I → A). x ∈ finite_supp(R.zero, R.carrier, S(0)) ⇒ eps(g'(0)(g(0)(x))) = eps(x)",
						Derive(func(b *Argument) {
							x := b.Fix("x")
							xIn := b.Assume()
							linear := b.Have(
								"g(0) is linear",
								"module_homomorphism(R, "+
									"    complex_module(free_complex(R, S, d), 0), "+
									"    complex_module(free_complex(R, T, e), 0), "+
									"    g(0))",
								By(chain_complex.ChainMapHom.Read(chainG)))
							image := b.Have(
								"so g(0)(x) lies in the free module on T(0)",
								"g(0)(x) ∈ finite_supp(R.zero, R.carrier, T(0))",
								By(module_homomorphism.HomIn.Read(linear), xIn))
							b.Show(
								"g' lifts at g(0)(x) and g at x",
								By(liftGʹ.At(b.Term("g(0)(x)")), liftG.At(x), image, xIn))
						}))
					a.Show(
						"the identity of P is a chain map of P as well, and two chain maps "+
							"into a resolution that agree after its augmentation are homotopic",
						By(
							ResolutionComparisonHomotopy.Read(res),
							ResolutionComplex.Read(res),
							throughQ,
							chain_complex.ChainMapIdentity.Read(ResolutionComplex.Read(res)),
							lifts))
				})
			return ctx.Theorem(headline,
				func(
					a *Argument,
					R *Expr[RingOps[A]],
					M *Expr[ModuleOps[A, B]],
					S *Arrow[Nat, Set[I]],
					d *Arrow2[Nat, Fun[I, A], Fun[I, A]],
					eps *Arrow[Fun[I, A], B],
					res FreeResolutionFact[on.R, on.M],
					T *Arrow[Nat, Set[E]],
					e *Arrow2[Nat, Fun[E, A], Fun[E, A]],
					eta *Arrow[Fun[E, A], B],
					g *Arrow2[Nat, Fun[I, A], Fun[E, A]],
					gʹ *Arrow2[Nat, Fun[E, A], Fun[I, A]],
					given Fact,
				) {
					parts := a.Conjuncts(
						given,
						"M has a second free resolution on T",
						"g is a chain map P → Q",
						"g' is a chain map Q → P",
						"g lifts the identity of M",
						"g' lifts the identity of M")
					second, chainG, chainGʹ, liftG, liftGʹ := parts[0], parts[1], parts[2], parts[3], parts[4]
					back := a.Have(
						"g' ∘ g is homotopic to the identity of P",
						"∃k:(num → (I → A) → I → A). "+
							"    chain_homotopy(R, "+
							"        free_complex(R, S, d), "+
							"        free_complex(R, S, d), "+
							"        λn:num. λx:(I → A). g'(n)(g(n)(x)), "+
							"        λn:num. λx:(I → A). x, "+
							"        k)",
						By(At(roundTrip, R, M, S, d, eps, T, e, eta, g, gʹ), res, chainG, chainGʹ, liftG, liftGʹ))
					forth := a.Have(
						"g ∘ g' is homotopic to the identity of Q: the round trip with the two resolutions exchanged",
						"∃l:(num → (E → A) → E → A). "+
							"    chain_homotopy(R, "+
							"        free_complex(R, T, e), "+
							"        free_complex(R, T, e), "+
							"        λn:num. λy:(E → A). g(n)(g'(n)(y)), "+
							"        λn:num. λy:(E → A). y, "+
							"        l)",
						By(At(roundTrip, R, M, T, e, eta, S, d, eps, gʹ, g), second, chainGʹ, chainG, liftGʹ, liftG))
					a.Show(
						"so g and g' are inverse chain homotopy equivalences",
						By(chain_complex.ChainHomotopyEquivalenceDef, chainG, chainGʹ, back, forth))
				})
		}),
})}
