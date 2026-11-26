// flat_module.go — flat modules over a commutative ring on a set: the
// definition through Tor₁ against the quotients of the ring by its
// ideals, Tor against free modules, flatness as the exactness of the
// tensor product, the module M/JM over the quotient ring R/J, and
// flatness across a square-zero thickening R → R/J.

package flat_module

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/chain_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/resolution"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/tensor_product"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/tor_ext"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/quotient_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The spelling of the statements
// ---------------------------------------------------------------------------

// flatRegular is the ring R as a module over itself.
const (
	flatRegular = "regular_module(R)"
)

// flatSpan is the submodule JM of the module M, spanned by the products
// of members of J with vectors.
const flatSpan = "module_span(R, M, {c • x | c:A, x:B | c ∈ J ∧ x ∈ M.carrier})"

// flatTorZero says Tor_d(m, n) over R is the zero module: its one class is
// the boundaries.
func flatTorZero(m, n, d string) string {
	return "tor(R, " + m + ", " + n + ", " + d + ") = {tor_zero(R, " + m + ", " + n + ", " + d + ")}"
}

// ---------------------------------------------------------------------------
// The definitions
// ---------------------------------------------------------------------------

// FlatModuleDef — `flat_module(R, M)`: M is a module over R, and Tor₁(M,
// R/I) is the zero module for every ideal I of R.
var FlatModuleDef = flatModuleDefThm{family.Define(registry.DefEntry{
	Name:  "FlatModuleDef",
	Key:   "prop_dd24f2a9eb26a29f",
	Const: "flat_module",
	Type:  "ring_ops(A) → module_ops(A, B) → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀M:module_ops(A, B). flat_module(R, M) ⇔ module_on(R, M) ∧ (∀I:set(A). ring_ideal(R, I) ⇒ " + flatTorZero(
			"M", "quotient_module("+flatRegular+", I)", "1") + ")",
	},
	Reading: "Zero is the one-class module: the only class of Tor₁ is tor_zero, the " +
		"boundaries. The test modules are the cyclic R/I at the type set(A) the cosets " +
		"live at, since a constant cannot range over modules at a type it does not carry; " +
		"FlatTorVanishes recovers every module at every type and every degree from one up. " +
		"I = R.carrier makes R/I the zero module and I = {R.zero} makes it a copy of R, " +
		"and both vanish for every module; over the zero ring every module is zero and flat.",
})}

// IdealQuotientModuleDef — `ideal_quotient_module(R, J, M)`: M/JM as a
// module over R/J, the cosets of the submodule JM added as sets, a coset
// of J acting on a coset of JM by the products of their members pushed
// onto JM.
var IdealQuotientModuleDef = idealQuotientModuleDefThm{family.Define(registry.DefEntry{
	Name:  "IdealQuotientModuleDef",
	Key:   "prop_e32f5e11a8c4f367",
	Const: "ideal_quotient_module",
	Type:  "ring_ops(A) → set(A) → module_ops(A, B) → module_ops(set(A), set(B))",
	Equations: []string{
		"∀R:ring_ops(A). ∀J:set(A). ∀M:module_ops(A, B). ideal_quotient_module(R, J, M) = mk_module(set_mul(M.add), " + flatSpan + ", set_inv(M.neg), " +
			"λs:set(A). λX:set(B). set_mul(M.add, {c • x | c:A, x:B | c ∈ s ∧ x ∈ X}, " + flatSpan + "), left_cosets(M.add, M.carrier, " + flatSpan + "))",
	},
	Reading: "JM is the span of the products c • x with c in J. A coset a + J acts on x + JM " +
		"through the products (a + j) • (x + k), each a • x plus a member of JM, so pushed onto JM " +
		"they are the coset a • x + JM: no representative is chosen, as the quotient ring's " +
		"product chooses none. When J² = 0 the ideal J, a module over R, goes to J/J·J with J·J = " +
		"{R.zero}, its members the singletons {j}: J as a module over R/J. For a module M, J = " +
		"{R.zero} gives the singletons of M.carrier and J = R.carrier the one member M.carrier.",
})}

// ---------------------------------------------------------------------------
// Tor against free modules
// ---------------------------------------------------------------------------

// TorFreeSecondVariableZero — Tor_n(M, R) is zero in every positive
// degree: tensoring the resolution with R gives the resolution back.
var TorFreeSecondVariableZero = torFreeSecondVariableZeroThm{family.Add(registry.ProofEntry{
	Name: "TorFreeSecondVariableZero",
	Key:  "prop_8ff0dd092f1749e5",
	Reading: "Degree zero is left out: Tor₀(M, R) is M ⊗ R, a copy of M. The module " +
		"hypothesis is load-bearing, since the canonical resolution resolves only a module.",
	Deps: []registry.EntryLike{
		tor_ext.TorDef,
		tor_ext.TorZeroDef,
		tor_ext.TorOfResolutionDef,
		tor_ext.CanonicalTensorComplexDef,
		tor_ext.TensorComplexOf,
		tor_ext.TensorBoundaryDef,
		resolution.CanonicalResolution,
		resolution.ResolutionExact,
		resolution.FreeComplexOf,
		free_module.FreeHomExpand,
		chain_complex.HomologyDef,
		chain_complex.CyclesDef,
		chain_complex.BoundariesDef,
		chain_complex.HomologyTrivialIffExact,
		module.RegularModuleOn,
	},
	Build: family.Card(module.ModuleOn.Statement(Statement{
		Binders: "∀n:num.",
		Hypotheses: []string{
			"1 ≤ n",
		},
		Conclusion: "tor(R, M, regular_module(R), n) = {tor_zero(R, M, regular_module(R), n)}",
	}),
		"at N = R the terms finite_supp(R.zero, R.carrier, S(n)) are the free modules of the "+
			"canonical resolution (one comprehension, FiniteSuppDef), and the tensor boundary Σ_x "+
			"d(n)(δ_x)(y) * g(x) is d(n)(g)(y), d(n) at g being the sum of the g(x) • d(n)(δ_x) "+
			"(FreeHomExpand), so the canonical tensor complex at R is the resolution's free complex; "+
			"it is exact in positive degrees (CanonicalResolution, ResolutionExact), so the cycles "+
			"are the boundaries and the homology is the one class (HomologyTrivialIffExact)"),
})}

// TorFiniteSuppSecondVariable — Tor commutes with finitely supported sums in
// the second variable: where Tor_n(M, N) is zero, so is Tor_n(M, N^(S)).
var TorFiniteSuppSecondVariable = torFiniteSuppSecondVariableThm{family.Add(registry.ProofEntry{
	Name: "TorFiniteSuppSecondVariable",
	Key:  "prop_fe0b24a74f24f5b7",
	Reading: "Every degree, zero included. The sum is finite_supp_module(N, S), the " +
		"finitely supported N-valued functions on S — the direct sum, not the product; " +
		"S = ∅ gives the zero module, whose Tor vanishes whatever Tor_n(M, N) is.",
	Deps: []registry.EntryLike{
		tor_ext.TorDef,
		tor_ext.TorZeroDef,
		tor_ext.TorOfResolutionDef,
		tor_ext.CanonicalTensorComplexDef,
		tor_ext.TensorComplexOf,
		tor_ext.TensorBoundaryDef,
		tor_ext.TensorComplex,
		function_module.FiniteSuppDef,
		function_module.FiniteSuppModuleDef,
		function_module.FiniteSuppModuleOn,
		resolution.CanonicalResolution,
		chain_complex.CyclesDef,
		chain_complex.BoundariesDef,
		chain_complex.HomologyDef,
		chain_complex.HomologyTrivialIffExact,
		function_module.ModuleSumApply,
		function_module.FunAddDef,
	},
	Build: family.Card(module.ModuleOn.Statement(Statement{
		Binders: "∀N:module_ops(A, C). ∀S:set(I). ∀n:num.",
		Hypotheses: []string{
			"module_on(R, N)",
			"tor(R, M, N, n) = {tor_zero(R, M, N, n)}",
		},
		Conclusion: "tor(R, M, finite_supp_module(N, S), n) = " +
			"{tor_zero(R, M, finite_supp_module(N, S), n)}",
	}),
		"a chain of the tensor complex at finite_supp_module(N, S) is a finitely supported function g "+
			"with g(x) a finitely supported function on S, and the tensor boundary acts slice by slice: "+
			"its value at s is the boundary of x ↦ g(x)(s), the sum and the scaling of finite_supp_module "+
			"being pointwise (TensorBoundaryDef, FiniteSuppModuleDef, ModuleSumApply); a cycle z "+
			"therefore has a cycle of the complex at N for each slice, finitely many of them nonzero, "+
			"each the boundary of some w_s by Tor_n(M, N) = 0 (HomologyTrivialIffExact), and w(x)(s) = "+
			"w_s(x), zero at the slices that are zero, is finitely supported with boundary z"),
})}

// ---------------------------------------------------------------------------
// Flatness through Tor and the tensor product
// ---------------------------------------------------------------------------

// FlatIsomorphic — a module isomorphic to a flat module is flat.
var FlatIsomorphic = flatIsomorphicThm{family.Add(registry.ProofEntry{
	Name: "FlatIsomorphic",
	Key:  "prop_c3b47822835337ee",
	Reading: "The two modules may live at different types: Tor is functorial in its first " +
		"variable at any type, and an isomorphism and its inverse induce inverse maps on every Tor.",
	Deps: []registry.EntryLike{
		FlatModuleDef,
		tor_ext.TorMapLeftHom,
		tor_ext.TorMapLeftIdentity,
		tor_ext.TorMapLeftCompose,
		tor_ext.TorMapLeftCongruence,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀M':module_ops(A, C). ∀h:(B → C).",
		Hypotheses: []string{
			"module_isomorphism(R, M, M', h)",
			"flat_module(R, M)",
		},
		Conclusion: "flat_module(R, M')",
	},
		"h and its inverse on the carriers (inverse_on) are homomorphisms whose composites "+
			"are the identities on M and M' — on the carriers only; tor_map_left of each at "+
			"R/I, composed, is the identity on Tor₁ (TorMapLeftCompose, then "+
			"TorMapLeftCongruence to replace the composite by λu. u, then TorMapLeftIdentity), "+
			"so Tor₁(M', R/I) is the image of the zero module Tor₁(M, R/I) under a homomorphism "+
			"(TorMapLeftHom), hence zero; module_on(R, M') is a conjunct of the isomorphism"),
})}

// FlatTorVanishes — a flat module has Tor_n(M, N) = 0 for every module N,
// at every type, in every positive degree.
var FlatTorVanishes = flatTorVanishesThm{family.Add(registry.ProofEntry{
	Name: "FlatTorVanishes",
	Key:  "prop_8c552697b4f5d475",
	Reading: "N ranges over every module at every type C, while the definition tests only the cyclic " +
		"R/I at set(A); the converse at degree one is the definition read at N = R/I, so with this card " +
		"flat_module(R, M) says Tor₁(M, N) = 0 for every module N. Degree zero is M ⊗ N and is not asked.",
	Deps: []registry.EntryLike{
		FlatModuleDef,
		TorFreeSecondVariableZero,
		tor_ext.TorLongExactMiddle,
		tor_ext.TorLongExactQuotient,
		tor_ext.TorMapHom,
		tor_ext.TorMapIdentity,
		tor_ext.TorMapCompose,
		tor_ext.TorDef,
		tor_ext.TorZeroDef,
		tor_ext.TensorComplexOf,
		function_module.FiniteSuppDef,
		chain_complex.HomologyTrivialIffExact,
		module_homomorphism.ShortExactModules,
		module_homomorphism.FirstIsomorphism,
		module_homomorphism.ProjectionHom,
		module_homomorphism.ProjectionKernel,
		submodule.ModuleSpanDef,
		submodule.SpanSubmodule,
		submodule.QuotientModuleOn,
		submodule.SubmoduleModuleOn,
		tor_ext.TorMapCongruence,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀n:num.",
		Hypotheses: []string{
			"flat_module(R, M)",
			"module_on(R, N)",
			"1 ≤ n",
		},
		Conclusion: "tor(R, M, N, n) = {tor_zero(R, M, N, n)}",
	},
		"fix a degree n with Tor_n(M, R/I) = 0 for every ideal I. Then Tor_n(M, N) = 0 for every N: "+
			"for a cyclic N ≅ R/ann(x) because tor_map carries an isomorphism to one (TorMapHom, "+
			"TorMapIdentity, TorMapCongruence — the inverse is the identity only on the carrier —, "+
			"TorMapCompose); for N spanned by x₁ … x_k by induction on k, the middle of 0 → N_{k−1} → N_k "+
			"→ N_k/N_{k−1} → 0 (TorLongExactMiddle) with a cyclic quotient; for any N because a cycle is "+
			"finitely supported, so its values lie in a finitely generated submodule N' in whose complex "+
			"it is already a boundary. Degree one is the definition; from n to n + 1, 0 → I → R → R/I → 0 "+
			"and Tor_{n+1}(M, R) = 0 (TorFreeSecondVariableZero) make the connecting map Tor_{n+1}(M, "+
			"R/I) → Tor_n(M, I) one-to-one (TorLongExactQuotient), and Tor_n(M, I) = 0 by the first part"),
})}

// FlatTensorInjective — tensoring with a flat module keeps a one-to-one
// homomorphism one-to-one.
var FlatTensorInjective = flatTensorInjectiveThm{family.Add(registry.ProofEntry{
	Name: "FlatTensorInjective",
	Key:  "prop_3fe30ca9ccee2daf",
	Reading: "The map M ⊗ i is named by its action on pure tensors: one homomorphism " +
		"does that (TensorUniversal) and it is unique on the tensor product " +
		"(TensorUniversalUnique). Only this direction is stated over free types C and D of " +
		"test modules — at a one-point type every module is zero and every map one-to-one, " +
		"so the converse would fail there; the converse is FlatIdealCriterion, at the ideals.",
	Deps: []registry.EntryLike{
		FlatTorVanishes,
		tor_ext.TorLongExactSub,
		tor_ext.TorZero,
		tor_ext.TorMapDef,
		tor_ext.TorDef,
		tor_ext.TorZeroDef,
		module_homomorphism.ShortExactModules,
		module_homomorphism.ProjectionHom,
		module_homomorphism.ProjectionKernel,
		module_homomorphism.ImageSubmodule,
		module_homomorphism.KernelTrivialIffInjective,
		submodule.QuotientModuleOn,
		tensor_product.TensorUniversal,
		tensor_product.TensorUniversalUnique,
		tensor_product.TensorSpan,
		tor_ext.TorZeroNatural,
		FlatModuleDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀N':module_ops(A, C). " +
			"∀N:module_ops(A, D). " +
			"∀i:(C → D). " +
			"∀f:(set(prod(B, C) → A) → set(prod(B, D) → A)).",
		Hypotheses: []string{
			"flat_module(R, M)",
			"module_homomorphism(R, N', N, i)",
			"injective_on(N'.carrier, i)",
			"module_homomorphism(R, tensor_module(R, M, N'), tensor_module(R, M, N), f)",
			"∀u:B. ∀v:C. u ∈ M.carrier ∧ v ∈ N'.carrier ⇒ f(tensor(R, M, N', u, v)) = tensor(R, M, N, u, i(v))",
		},
		Conclusion: "injective_on(tensor_product(R, M, N'), f)",
	},
		"i and the projection onto N'' = quotient_module(N, image(i, N'.carrier)) are a short "+
			"exact sequence (ImageSubmodule, ProjectionHom, ProjectionKernel); Tor₁(M, N'') = 0 "+
			"(FlatTorVanishes) makes tor_map(i) one-to-one in degree zero (TorLongExactSub at n = 0, "+
			"KernelTrivialIffInjective). The identification of Tor₀ with the tensor product (TorZero, "+
			"TorZeroNatural), g ↦ Σ_x eps(δ_x) ⊗ g(x), commutes with the maps induced by i, and f is "+
			"the induced map on the tensor products (TensorUniversalUnique), so f is one-to-one"),
})}

// FlatIdealCriterion — the ideal criterion: M is flat exactly when, for
// every ideal I, the map M ⊗ I → M ⊗ R the inclusion induces is
// one-to-one.
var FlatIdealCriterion = flatIdealCriterionThm{family.Add(registry.ProofEntry{
	Name: "FlatIdealCriterion",
	Key:  "prop_684dfeae647c8682",
	Reading: "The definition asks Tor₁(M, R/I) = 0, and the long exact sequence of 0 → I " +
		"→ R → R/I → 0 makes that group the kernel of M ⊗ I → M ⊗ R, Tor₁(M, R) being zero; " +
		"module_on(R, M) is on the right because flat_module asks it. The map is named by " +
		"its action on pure tensors, as in FlatTensorInjective, and exists by TensorUniversal.",
	Deps: []registry.EntryLike{
		FlatModuleDef,
		FlatTensorInjective,
		TorFreeSecondVariableZero,
		tor_ext.TorLongExactSub,
		tor_ext.TorLongExactQuotient,
		tor_ext.TorZero,
		module.RegularModuleOn,
		module_homomorphism.ShortExactModules,
		module_homomorphism.ProjectionHom,
		module_homomorphism.ProjectionKernel,
		module_homomorphism.KernelTrivialIffInjective,
		ring_ideal.IdealSubset,
		submodule.SubmoduleModuleOn,
		tensor_product.TensorUniversal,
		tensor_product.TensorUniversalUnique,
		tor_ext.TorZeroNatural,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B).",
		Conclusion: "flat_module(R, M) ⇔ " +
			"module_on(R, M) ∧ " +
			"(∀I:set(A). ∀f:(set(prod(B, A) → A) → set(prod(B, A) → A)). " +
			"    ring_ideal(R, I) ∧ " +
			"    module_homomorphism(R, " +
			"        tensor_module(R, M, restrict_module(regular_module(R), I)), " +
			"        tensor_module(R, M, regular_module(R)), " +
			"        f) ∧ " +
			"    (∀u:B. ∀x:A. " +
			"        u ∈ M.carrier ∧ x ∈ I ⇒ " +
			"        f(tensor(R, M, restrict_module(regular_module(R), I), u, x)) = " +
			"        tensor(R, M, regular_module(R), u, x)) ⇒ " +
			"    injective_on(tensor_product(R, M, restrict_module(regular_module(R), I)), f))",
	},
		"⇒ is FlatTensorInjective at the inclusion of the ideal I, a module over R inside the regular "+
			"module (IdealSubset, RegularModuleOn). ⇐: the inclusion and the projection onto R/I are "+
			"short exact (ProjectionHom, ProjectionKernel); Tor₁(M, R) = 0 (TorFreeSecondVariableZero) "+
			"makes the connecting map Tor₁(M, R/I) → Tor₀(M, I) one-to-one (TorLongExactQuotient), and "+
			"its image is the kernel of tor_map in degree zero (TorLongExactSub), which TorZero's "+
			"identification carries to the kernel of f, zero by hypothesis"),
})}

// ---------------------------------------------------------------------------
// Modules over the quotient ring
// ---------------------------------------------------------------------------

// IdealQuotientModuleOn — M/JM is a module over R/J: the cosets of JM with
// their sum are quotient_module's abelian group, and the action of a + J on
// x + JM is the coset of a • x, so every other condition is M's own at
// representatives.
var IdealQuotientModuleOn = idealQuotientModuleOnThm{family.Add(registry.ProofEntry{
	Name: "IdealQuotientModuleOn",
	Key:  "prop_f8e527dc2d00b243",
	Reading: "The ideal is load-bearing twice: the cosets of J are a ring only " +
		"for an ideal, and a coset a + J acts by the one coset a • x + JM because J " +
		"• M lies in JM. No square-zero hypothesis: this is M ⊗_R R/J for any ideal J.",
	Build: family.Sections(module.ModuleOn.Statement(Statement{
		Binders: "∀J:set(A).",
		Hypotheses: []string{
			"ring_ideal(R, J)",
		},
		Conclusion: "module_on(ideal_quotient_ring(R, J), ideal_quotient_module(R, J, M))",
		Abbrev: Abbrev{
			{Name: "JM", Text: "module_span(R, M, {c • x | c:A, x:B | c ∈ J ∧ x ∈ M.carrier})"},
			{Name: "cosets", Text: "left_cosets(M.add, M.carrier, «JM»)"},
			{Name: "act", Text: "λs:set(A). λX:set(B). " +
				"    set_mul(M.add, {c • x | c:A, x:B | c ∈ s ∧ x ∈ X}, «JM»)"},
		},
	}),
		func(ctx *Script, headline string) *GoalStackNode {
			// The one computation: a coset a + J acts on a coset x + N by the
			// coset of a • x, for any submodule N holding the products of J
			// with the vectors.
			actionOnCosets := ctx.Lemma(module.ModuleOn.Statement(Statement{
				Binders: "∀J:set(A). ∀N:set(B). ∀a:A. ∀x:B.",
				Hypotheses: []string{
					"ring_ideal(R, J)",
					"submodule(R, M, N)",
					"∀c:A. ∀y:B. c ∈ J ∧ y ∈ M.carrier ⇒ c • y ∈ N",
					"a ∈ R.carrier",
					"x ∈ M.carrier",
				},
				Conclusion: "set_mul(M.add, " +
					"    {c • y | c:A, y:B | c ∈ left_coset(R.add, a, J) ∧ y ∈ left_coset(M.add, x, N)}, " +
					"    N) = " +
					"left_coset(M.add, a • x, N)",
			}),
				func(
					arg *Argument,
					R *Expr[RingOps[A]],
					M *Expr[ModuleOps[A, B]],
					ambient module.ModuleFact[on.R, on.M],
					J *Expr[Set[A]],
					N *Expr[Set[B]],
					ideal, sub, products Fact,
					a *Member[A, on.R],
					x *Member[B, on.M],
				) {
					ring := module.RingOn.Read(ambient)
					inRing := arg.Unfolded(ring_ideal.IdealSubset.Read(ideal), set_basic.SubsetDef)
					inModule := arg.Unfolded(submodule.SubmoduleSubset.Read(sub).AsFact(), set_basic.SubsetDef)
					pointwise := arg.Have(
						"the products of the two cosets plus N and the coset of a • x have the same points",
						"∀z:B. "+
							"    z ∈ "+
							"    set_mul(M.add, "+
							"        {c • y | c:A, y:B | c ∈ left_coset(R.add, a, J) ∧ y ∈ left_coset(M.add, x, N)}, "+
							"        N) ⇔ "+
							"    z ∈ left_coset(M.add, a • x, N)",
						Derive(func(b *Argument) {
							b.FixAs[B]("z")
							b.Iff()
							b.Forward(
								"a point (a + j) • (x + k) + n is a • x plus j • x + (a + j) • k + n, which N holds",
								func(d *Argument, member Fact) {
									j, k, n, point := d.Obtain3As[A, B, B](
										"z is (a + j) • (x + k) + n for some j in J and k and n in N",
										"∃j:A. ∃k n:B. j ∈ J ∧ k ∈ N ∧ n ∈ N ∧ z = (a + j) • (x + k) + n",
										member.Simp(Fwd(quotient_group.InSetMul), Fwd(group.LeftCosetDef), Fwd(set_basic.InImage)),
										By(member))
									pieces := d.Conjuncts(
										point,
										"j lies in J",
										"k lies in N",
										"so does n",
										"z is (a + j) • (x + k) + n")
									jR := d.MemberOf[on.R](j, GroupPremises(pieces[0], inRing.At(j)))
									kM, nM :=
										d.MemberOf[on.M](k, GroupPremises(pieces[1], inModule.At(k))),
										d.MemberOf[on.M](n, GroupPremises(pieces[2], inModule.At(n)))
									regroup := d.Have(
										"z regroups as a • x + (j • x + (a + j) • k + n)",
										"z = a • x + (j • x + (a + j) • k + n)",
										ByChase(Depth(0), ambient, a, x, jR, kM, nM, pieces[3]))
									inN := d.Have(
										"N holds j • x, a product, (a + j) • k, a multiple of k, and n",
										"j • x + (a + j) • k + n ∈ N",
										By(
											submodule.SubmoduleAdd.Read(sub),
											submodule.SubmoduleSmul.Read(sub),
											comm_ring.AddIn.Read(ring),
											products,
											a,
											x,
											jR,
											pieces[0],
											pieces[1],
											pieces[2]))
									d.Do(Simp(Fwd(group.LeftCosetDef), Fwd(set_basic.InImage)))
									d.Take(d.TermAs[B]("j • x + (a + j) • k + n"))
									d.Show(
										"so z is a • x plus a point of N",
										By(regroup, inN))
								})
							b.Backward(
								"a point a • x + n of the coset of a • x is the product of a and x, each in its own coset, plus n",
								func(d *Argument, member Fact) {
									_, point := d.UnpackAs[B](d.Simplified(
										member,
										Fwd(group.LeftCosetDef),
										Fwd(set_basic.InImage)), "n")
									own := d.Have(
										"a and x each lie in their own coset",
										"a ∈ left_coset(R.add, a, J) ∧ x ∈ left_coset(M.add, x, N)",
										By(
											group.InOwnLeftCosetOn.Read(abelian_group.GroupOn.Read(comm_ring.AddGroupOn.Read(ring))),
											group.InOwnLeftCosetOn.Read(module.AddGroupOn.Read(ambient)),
											quotient_ring.IdealSubgroup.Read(ring),
											submodule.SubmoduleSubgroup.Read(sub),
											a,
											x,
											ideal))
									d.Show(
										"so z is a • x, a point of the products, plus n",
										By(point, own, quotient_group.InSetMul))
								})
						}))
					arg.Show(
						"two sets with the same points are equal",
						By(pointwise, set_basic.Extension))
				})

			return ctx.Theorem(headline,
				func(
					arg *Argument,
					R *Expr[RingOps[A]],
					M *Expr[ModuleOps[A, B]],
					ambient module.ModuleFact[on.R, on.M],
					J *Expr[Set[A]],
					ideal Fact,
				) {
					ring := module.RingOn.Read(ambient)
					ringAdditive := abelian_group.GroupOn.Read(comm_ring.AddGroupOn.Read(ring))
					additive := module.AddGroupOn.Read(ambient)
					JM := arg.TermAs[Set[B]]("«JM»")
					inCarrier := arg.Have(
						"the products of J with the vectors are vectors",
						"{c • x | c:A, x:B | c ∈ J ∧ x ∈ M.carrier} ⊆ M.carrier",
						BySets(ring_ideal.IdealSubset, module.SmulIn, ideal, ambient))
					sub := arg.Have(
						"so their span JM is a submodule of M",
						"submodule(R, M, «JM»)",
						By(inCarrier, submodule.SpanSubmodule.Read(ambient)))
					inSpan := arg.Have(
						"and it holds each of them",
						"∀c:A. ∀y:B. c ∈ J ∧ y ∈ M.carrier ⇒ c • y ∈ «JM»",
						By(
							submodule.SubsetSpan.At(R, M, arg.TermAs[Set[B]]("{c • x | c:A, x:B | c ∈ J ∧ x ∈ M.carrier}")),
							set_basic.SubsetDef))
					action := arg.Have(
						"the action of a + J on x + JM is the coset of a • x",
						Statement{
							Binders: "∀a:A. ∀x:B.",
							Hypotheses: []string{
								"a ∈ R.carrier",
								"x ∈ M.carrier",
							},
							Conclusion: "«act»(left_coset(R.add, a, J), left_coset(M.add, x, «JM»)) = " +
								"left_coset(M.add, a • x, «JM»)",
						},
						By(inSpan, ambient, ideal, sub, actionOnCosets))
					quotient := arg.Have(
						"the cosets of JM are a module over R",
						"module_on(R, quotient_module(M, «JM»))",
						By(sub, submodule.QuotientModuleOn.Read(ambient)))
					commutes := arg.Have(
						"so their sum commutes",
						"∀u v:set(B). u ∈ «cosets» ∧ v ∈ «cosets» ⇒ set_mul(M.add, u, v) = set_mul(M.add, v, u)",
						By(module.AddComm.Read(quotient)))
					normal := arg.Have(
						"JM is a normal subgroup of the vectors",
						"normal_subgroup(module_additive_group(M), «JM»)",
						By(sub, submodule.SubmoduleNormal.Read(ambient)))
					cosetGroup := arg.Have(
						"so the cosets are a group under their sum, the additive group of M/JM over R/J",
						"group_on(module_additive_group(ideal_quotient_module(R, J, M)))",
						Simp(Fwd(module_record.ModuleAdditiveGroupDef), Fwd(IdealQuotientModuleDef)),
						By(
							normal,
							quotient_group.QuotientGroupOn.Read(additive),
							quotient_group.QuotientGroupDef.At(
								arg.TermAs[group.GroupOps[B]]("module_additive_group(M)"),
								arg.TermAs[Set[B]]("«JM»"))))
					cosetSum := arg.Have(
						"the sum of the cosets of x and y is the coset of x + y",
						Statement{
							Binders: "∀x y:B.",
							Hypotheses: []string{
								"x ∈ M.carrier",
								"y ∈ M.carrier",
							},
							Conclusion: "set_mul(M.add, left_coset(M.add, x, «JM»), left_coset(M.add, y, «JM»)) = " +
								"left_coset(M.add, x + y, «JM»)",
						},
						By(normal, quotient_group.LeftCosetMulOn.Read(additive)))
					scalarSum := arg.Have(
						"the sum of the cosets of a and b is the coset of a + b",
						Statement{
							Binders: "∀a b:A.",
							Hypotheses: []string{
								"a ∈ R.carrier",
								"b ∈ R.carrier",
							},
							Conclusion: "set_mul(R.add, left_coset(R.add, a, J), left_coset(R.add, b, J)) = " +
								"left_coset(R.add, a + b, J)",
						},
						By(quotient_group.LeftCosetMulOn.Read(ringAdditive), quotient_ring.IdealNormal.Read(ring), ideal))
					scalarProduct := arg.Have(
						"and their product is the coset of a * b",
						Statement{
							Binders: "∀a b:A.",
							Hypotheses: []string{
								"a ∈ R.carrier",
								"b ∈ R.carrier",
							},
							Conclusion: "quotient_mul(J, left_coset(R.add, a, J), left_coset(R.add, b, J)) = " +
								"left_coset(R.add, a * b, J)",
						},
						By(quotient_ring.QuotientMulCoset.Read(ring), ideal))
					// The conditions of module_on over R/J are proved here, before
					// the unfolding below: it also opens the resident modules, so
					// their handles die. Each is read from representatives: J lies
					// in R's carrier and JM in M's, so a quantifier over cosets is
					// one over points. The laws that say so are Simp rules guarded
					// by these inclusions, discharged from the hypotheses, so the
					// first stays resident with no handle: no close lists it. A
					// condition with a scalar guard is stated curried, the scalars
					// first.
					arg.Have(
						"J lies in R's carrier",
						"J ⊆ R.carrier",
						By(ideal, ring_ideal.IdealSubset))
					within := arg.Have(
						"and JM in M's",
						"«JM» ⊆ M.carrier",
						By(sub, submodule.SubmoduleSubset))
					closed := arg.Have(
						"a coset a + J scales each coset to a coset, that of a • x",
						"∀c:set(A). "+
							"    c ∈ left_cosets(R.add, R.carrier, J) ⇒ ∀u:set(B). u ∈ «cosets» ⇒ «act»(c, u) ∈ «cosets»",
						Simp(Fwd(quotient_group.ForallInLeftCosets.Read(ringAdditive))),
						Derive(func(b *Argument) {
							a := b.FixAs[A]("a")
							am := b.MemberOf[on.R](a, b.Assume())
							b.Do(Simp(Fwd(quotient_group.ForallInLeftCosets.Read(additive))))
							x := b.FixAs[B]("x")
							xm := b.MemberOf[on.M](x, b.Assume())
							b.Show(
								"(a + J)(x + JM) is the coset of a • x, a point of M",
								GroupPremises(am, xm, action.At(a, x)).Rw(),
								By(
									quotient_group.LeftCosetInLeftCosets.Read(additive).At(JM, module.SmulIn.Read(ambient).At(am, xm)),
									within))
						}))
					distributes := arg.Have(
						"a coset a + J distributes over the coset sum, because a does over the vector sum",
						"∀c:set(A). "+
							"    c ∈ left_cosets(R.add, R.carrier, J) ⇒ "+
							"    ∀u v:set(B). "+
							"        u ∈ «cosets» ∧ v ∈ «cosets» ⇒ "+
							"        «act»(c, set_mul(M.add, u, v)) = set_mul(M.add, «act»(c, u), «act»(c, v))",
						Simp(Fwd(quotient_group.ForallInLeftCosets.Read(ringAdditive))),
						Derive(func(b *Argument) {
							b.FixAs[A]("a")
							b.Assume()
							b.Do(Simp(Fwd(quotient_group.ForallInLeftCosetsPair.Read(additive))))
							b.FixAs[B]("x")
							b.FixAs[B]("y")
							b.Assume()
							b.Show(
								"(a + J)((x + y) + JM) is the coset of a • (x + y) = a • x + a • y, the sum of the two images",
								Simp(
									Fwd(cosetSum),
									Fwd(action),
									Fwd(module.SmulAddLeft.Read(ambient)),
									Fwd(group.MulIn.Read(additive)),
									Fwd(module.SmulIn.Read(ambient))),
								Refl())
						}))
					sums := arg.Have(
						"a coset sum of scalars distributes over every coset, because a + b does over a vector",
						"∀c d:set(A). "+
							"    c ∈ left_cosets(R.add, R.carrier, J) ∧ d ∈ left_cosets(R.add, R.carrier, J) ⇒ "+
							"    ∀u:set(B). "+
							"        u ∈ «cosets» ⇒ «act»(set_mul(R.add, c, d), u) = set_mul(M.add, «act»(c, u), «act»(d, u))",
						Simp(Fwd(quotient_group.ForallInLeftCosetsPair.Read(ringAdditive))),
						Derive(func(b *Argument) {
							b.FixAs[A]("a")
							b.FixAs[A]("b")
							b.Assume()
							b.Do(Simp(Fwd(quotient_group.ForallInLeftCosets.Read(additive))))
							b.FixAs[B]("x")
							b.Assume()
							b.Show(
								"the coset of a + b takes x + JM to the coset of (a "+
									"+ b) • x = a • x + b • x, the sum of the two images",
								Simp(
									Fwd(scalarSum),
									Fwd(action),
									Fwd(module.SmulAddRight.Read(ambient)),
									Fwd(cosetSum),
									Fwd(comm_ring.AddIn.Read(ring)),
									Fwd(module.SmulIn.Read(ambient))),
								Refl())
						}))
					twice := arg.Have(
						"a coset product of scalars scales every coset as "+
							"its factors do in turn, because a * b does a vector",
						"∀c d:set(A). "+
							"    c ∈ left_cosets(R.add, R.carrier, J) ∧ d ∈ left_cosets(R.add, R.carrier, J) ⇒ "+
							"    ∀u:set(B). u ∈ «cosets» ⇒ «act»(quotient_mul(J, c, d), u) = «act»(c, «act»(d, u))",
						Simp(Fwd(quotient_group.ForallInLeftCosetsPair.Read(ringAdditive))),
						Derive(func(b *Argument) {
							b.FixAs[A]("a")
							b.FixAs[A]("b")
							b.Assume()
							b.Do(Simp(Fwd(quotient_group.ForallInLeftCosets.Read(additive))))
							b.FixAs[B]("x")
							b.Assume()
							b.Show(
								"the coset of a * b takes x + JM to the coset of (a * b) "+
									"• x = a • (b • x), which a + J takes the coset of b • x to",
								Simp(
									Fwd(scalarProduct),
									Fwd(action),
									Fwd(module.SmulMul.Read(ambient)),
									Fwd(comm_ring.MulIn.Read(ring)),
									Fwd(module.SmulIn.Read(ambient))),
								Refl())
						}))
					one := arg.Have(
						"the coset of the ring's one fixes every coset, because the one fixes every vector",
						"∀u:set(B). u ∈ «cosets» ⇒ «act»(left_coset(R.add, R.one, J), u) = u",
						Simp(Fwd(quotient_group.ForallInLeftCosets.Read(additive))),
						Derive(func(b *Argument) {
							b.FixAs[B]("x")
							b.Assume()
							b.Show(
								"one + J takes x + JM to the coset of R.one • x, which is x + JM",
								Simp(Fwd(action), Fwd(module.SmulOne.Read(ambient)), Fwd(comm_ring.OneIn.Read(ring))),
								Refl())
						}))
					ringOn := arg.Have(
						"the cosets of J are a commutative ring",
						"comm_ring_on(ideal_quotient_ring(R, J))",
						By(ideal, quotient_ring.QuotientRingOn.Read(ring)))
					arg.Show(
						"unfolded, module_on over R/J is the facts above, the curried ones with their guards joined",
						Unfold(module.ModuleOn),
						By(ringOn, cosetGroup, commutes, closed, distributes, sums, twice, one))
				})
		}),
})}

// TensorOverQuotient — for a module N over R/J, M ⊗_R N is M/JM ⊗_{R/J} N,
// v ⊗ u going to (v + JM) ⊗ u.
var TensorOverQuotient = tensorOverQuotientThm{family.Add(registry.ProofEntry{
	Name: "TensorOverQuotient",
	Key:  "prop_e486d3e51346eaab",
	Reading: "Any ideal J. N is a module over R/J, its scalars the cosets; over R it is " +
		"read through a ↦ a + J, so J acts on it by zero, which is what lets v ⊗ u depend on " +
		"v + JM only. The isomorphism is over R and is R/J-linear as well, R → R/J being onto.",
	Deps: []registry.EntryLike{
		IdealQuotientModuleOn,
		IdealQuotientModuleDef,
		quotient_ring.IdealQuotientProjection,
		quotient_ring.CosetEqIdealIff,
		tensor_product.TensorUniversal,
		tensor_product.TensorUniversalUnique,
		tensor_product.TensorSpan,
		tensor_product.TensorModuleOn,
		tensor_product.TensorZeroRight,
		tensor_product.TensorSmulLeft,
		tensor_product.TensorSmulRightFactor,
		tensor_product.TensorBalance,
		module.ZeroSmul,
		module_homomorphism.ModuleIsomorphismDef,
	},
	Build: family.Card(module.ModuleOn.Statement(Statement{
		Binders: "∀J:set(A). ∀N:module_ops(set(A), C).",
		Hypotheses: []string{
			"ring_ideal(R, J)",
			"module_on(ideal_quotient_ring(R, J), N)",
		},
		Conclusion: "∃h:(set(prod(B, C) → A) → set(prod(set(B), C) → set(A))). " +
			"    module_isomorphism(R, " +
			"        tensor_module(R, M, scalar_restriction(ideal_quotient_projection(R, J), N)), " +
			"        scalar_restriction(ideal_quotient_projection(R, J), " +
			"            tensor_module(ideal_quotient_ring(R, J), ideal_quotient_module(R, J, M), N)), " +
			"        h) ∧ " +
			"    (∀v:B. ∀u:C. " +
			"        v ∈ M.carrier ∧ u ∈ N.carrier ⇒ " +
			"        h(tensor(R, M, scalar_restriction(ideal_quotient_projection(R, J), N), v, u)) = " +
			"        tensor(ideal_quotient_ring(R, J), " +
			"            ideal_quotient_module(R, J, M), " +
			"            N, " +
			"            left_coset(M.add, " +
			"                v, " +
			"                module_span(R, M, {c • x | c:A, x:B | c ∈ J ∧ x ∈ M.carrier})), " +
			"            u))",
	}),
		"h is induced by the bilinear (v, u) ↦ (v + JM) ⊗ u over R (TensorUniversal; a scalar a "+
			"acts on both sides through a + J). The inverse is induced over R/J by (v + JM, u) ↦ v ⊗ "+
			"u, its target M ⊗_R N read over R/J with a coset acting through any of its members "+
			"(inverse_on of the projection) — well defined because J acts by zero there, j • (v ⊗ u) "+
			"= v ⊗ N.smul(J, u) = v ⊗ N.zero; the map itself is well defined because (j • m) ⊗ u = m "+
			"⊗ ((j + J) • u) = m ⊗ N.zero, the relations, for j ∈ J (CosetEqIdealIff, TensorSmulLeft, "+
			"TensorZeroRight); bilinear over R/J since a + J acts on each side as a does. The two "+
			"composites fix pure tensors, so they are identities (TensorUniversalUnique)"),
})}

// TensorSquareZeroBaseChange — for a square-zero ideal J, M ⊗_R J is
// M/JM ⊗_{R/J} J, v ⊗ j going to (v + JM) ⊗ {j}.
var TensorSquareZeroBaseChange = tensorSquareZeroBaseChangeThm{family.Add(registry.ProofEntry{
	Name: "TensorSquareZeroBaseChange",
	Key:  "prop_b4020110505fd76d",
	Reading: "J² = 0 is what makes J a module over R/J: the span J·J of the " +
		"products is then {R.zero}, so ideal_quotient_module at J read as a module " +
		"over R has the singletons for its members, and {j} is the class of j. The " +
		"isomorphism is over R; the tensor products put M first, as Tor does.",
	Deps: []registry.EntryLike{
		TensorOverQuotient,
		IdealQuotientModuleOn,
		IdealQuotientModuleDef,
		submodule.SpanLeast,
		submodule.ZeroSubmodule,
		quotient_ring.IdealQuotientProjection,
		tensor_product.TensorUniversal,
		tensor_product.TensorUniversalUnique,
		module_homomorphism.ModuleIsomorphismDef,
		module_homomorphism.HomCompose,
	},
	Build: family.Card(module.ModuleOn.Statement(Statement{
		Binders: "∀J:set(A).",
		Hypotheses: []string{
			"ring_ideal(R, J)",
			"∀x y:A. x ∈ J ∧ y ∈ J ⇒ R.mul(x, y) = R.zero",
		},
		Conclusion: "∃h:(set(prod(B, A) → A) → set(prod(set(B), set(A)) → set(A))). " +
			"    module_isomorphism(R, " +
			"        tensor_module(R, M, restrict_module(regular_module(R), J)), " +
			"        scalar_restriction(ideal_quotient_projection(R, J), " +
			"            tensor_module(ideal_quotient_ring(R, J), " +
			"                ideal_quotient_module(R, J, M), " +
			"                ideal_quotient_module(R, J, restrict_module(regular_module(R), J)))), " +
			"        h) ∧ " +
			"    (∀v:B. ∀j:A. " +
			"        v ∈ M.carrier ∧ j ∈ J ⇒ " +
			"        h(tensor(R, M, restrict_module(regular_module(R), J), v, j)) = " +
			"        tensor(ideal_quotient_ring(R, J), " +
			"            ideal_quotient_module(R, J, M), " +
			"            ideal_quotient_module(R, J, restrict_module(regular_module(R), J)), " +
			"            left_coset(M.add, " +
			"                v, " +
			"                module_span(R, M, {c • x | c:A, x:B | c ∈ J ∧ x ∈ M.carrier})), " +
			"            {j}))",
	}),
		"J·J is {R.zero} (SpanLeast at ZeroSubmodule, every product of J vanishing), so j "+
			"↦ {j} is an isomorphism over R of the ideal J onto its ideal_quotient_module read "+
			"over R, a + J acting on {j} as a does. TensorOverQuotient at that module over R/J "+
			"gives M ⊗_R J/J·J ≅ M/JM ⊗_{R/J} J/J·J, and tensoring M with the isomorphism j ↦ "+
			"{j} (TensorUniversal both ways, TensorUniversalUnique) composes to h"),
})}

// FlatQuotientBaseChange — a flat module stays flat on reduction modulo an
// ideal: M/JM is flat over R/J.
var FlatQuotientBaseChange = flatQuotientBaseChangeThm{family.Add(registry.ProofEntry{
	Name: "FlatQuotientBaseChange",
	Key:  "prop_afadd8ecb3b5903e",
	Reading: "Any ideal J, square-zero or not. The converse fails: over ℤ with J = " +
		"2ℤ, the module ℤ/2 reduces to 𝔽₂ over 𝔽₂, flat, while ℤ/2 is not flat over ℤ — " +
		"what SquareZeroFlatCriterion adds for a square-zero J is the injectivity of μ.",
	Deps: []registry.EntryLike{
		FlatIdealCriterion,
		FlatTensorInjective,
		TensorOverQuotient,
		IdealQuotientModuleOn,
		quotient_ring.IdealQuotientProjection,
		tensor_product.TensorUniversalUnique,
		module_homomorphism.ModuleIsomorphismDef,
		module_homomorphism.HomCompose,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀J:set(A).",
		Hypotheses: []string{
			"flat_module(R, M)",
			"ring_ideal(R, J)",
		},
		Conclusion: "flat_module(ideal_quotient_ring(R, J), ideal_quotient_module(R, J, M))",
	},
		"FlatIdealCriterion over R/J, M/JM being a module there (IdealQuotientModuleOn): for an "+
			"ideal I₀ of R/J, TensorOverQuotient at I₀ and at R/J itself, both modules over R/J, "+
			"identifies M/JM ⊗ I₀ → M/JM ⊗ R/J with M ⊗_R I₀ → M ⊗_R R/J, the two isomorphisms "+
			"being named on pure tensors so that the square commutes (TensorUniversalUnique); the "+
			"latter is one-to-one by FlatTensorInjective at the inclusion of I₀ read over R"),
})}

// ---------------------------------------------------------------------------
// Flatness across a square-zero thickening
// ---------------------------------------------------------------------------

// SquareZeroFlatForward — for M flat over R and J² = 0, μ : M/JM ⊗_{R/J}
// J → JM, (v + JM) ⊗ {j} ↦ j • v, is an isomorphism.
var SquareZeroFlatForward = squareZeroFlatForwardThm{family.Add(registry.ProofEntry{
	Name: "SquareZeroFlatForward",
	Key:  "prop_83fe515742efa66d",
	Reading: "J² = 0 is what makes μ well defined: j • (v + Σ jᵢ • mᵢ) = j • v. The " +
		"image is JM for every module; flatness makes μ one-to-one, through Tor₁(M, R/J) = " +
		"0, the kernel of M ⊗ J → M. μ is named by its action on pure tensors and over R; " +
		"one such homomorphism exists, through TensorSquareZeroBaseChange and TensorUniversal.",
	Deps: []registry.EntryLike{
		FlatModuleDef,
		FlatTensorInjective,
		TensorSquareZeroBaseChange,
		tensor_product.TensorUniversal,
		tensor_product.TensorUniversalUnique,
		tensor_product.TensorSpan,
		module.RegularModuleOn,
		ring_ideal.IdealSubset,
		module_homomorphism.ImageSubmodule,
		module_homomorphism.HomCompose,
		submodule.SpanLeast,
		submodule.SubsetSpan,
		tensor_product.TensorRegular,
		tor_ext.TorZeroNatural,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀M:module_ops(A, B). " +
			"∀J:set(A). " +
			"∀μ:(set(prod(set(B), set(A)) → set(A)) → B).",
		Hypotheses: []string{
			"flat_module(R, M)",
			"ring_ideal(R, J)",
			"∀x y:A. x ∈ J ∧ y ∈ J ⇒ R.mul(x, y) = R.zero",
			"module_homomorphism(R, " +
				"    scalar_restriction(ideal_quotient_projection(R, J), " +
				"        tensor_module(ideal_quotient_ring(R, J), " +
				"            ideal_quotient_module(R, J, M), " +
				"            ideal_quotient_module(R, J, restrict_module(regular_module(R), J)))), " +
				"    M, " +
				"    μ)",
			"∀v:B. ∀j:A. " +
				"    v ∈ M.carrier ∧ j ∈ J ⇒ " +
				"    μ(tensor(ideal_quotient_ring(R, J), " +
				"            ideal_quotient_module(R, J, M), " +
				"            ideal_quotient_module(R, J, restrict_module(regular_module(R), J)), " +
				"            left_coset(M.add, " +
				"                v, " +
				"                module_span(R, M, {c • x | c:A, x:B | c ∈ J ∧ x ∈ M.carrier})), " +
				"            {j})) = " +
				"    j • v",
		},
		Conclusion: "injective_on(tensor_product(ideal_quotient_ring(R, J), " +
			"        ideal_quotient_module(R, J, M), " +
			"        ideal_quotient_module(R, J, restrict_module(regular_module(R), J))), " +
			"    μ) ∧ " +
			"image(μ, " +
			"    tensor_product(ideal_quotient_ring(R, J), " +
			"        ideal_quotient_module(R, J, M), " +
			"        ideal_quotient_module(R, J, restrict_module(regular_module(R), J)))) = " +
			"module_span(R, M, {c • x | c:A, x:B | c ∈ J ∧ x ∈ M.carrier})",
	},
		"the inclusion of J into R is one-to-one, so M ⊗ J → M ⊗ R is one-to-one "+
			"(FlatTensorInjective); after M ⊗ R ≅ M, v ⊗ r ↦ r • v (TensorUniversal both ways), "+
			"it is v ⊗ j ↦ j • v, which is μ ∘ h for h of TensorSquareZeroBaseChange — the two "+
			"agree on pure tensors (TensorUniversalUnique) — so μ is one-to-one. The image of μ "+
			"is a submodule (ImageSubmodule) holding each j • v and inside JM, each member being "+
			"a sum of scaled pure tensors (TensorSpan), so it is JM (SpanLeast, SubsetSpan)"),
})}

// SquareZeroFlatConverse — for J² = 0, Tor₁(M, R/J) = 0 and M/JM flat
// over R/J make M flat over R.
var SquareZeroFlatConverse = squareZeroFlatConverseThm{family.Add(registry.ProofEntry{
	Name: "SquareZeroFlatConverse",
	Key:  "prop_470e15d64a3a29b0",
	Reading: "The nilpotence of J replaces any finiteness hypothesis: every module N " +
		"sits in 0 → JN → N → N/JN → 0 with both ends killed by J when J² = 0. Without " +
		"it the card fails: over ℤ with J = 2ℤ, the module ℤ/3 has Tor₁(ℤ/3, ℤ/2) = 0 " +
		"and reduces to the zero module, flat over 𝔽₂, yet ℤ/3 is not flat over ℤ.",
	Deps: []registry.EntryLike{
		FlatModuleDef,
		FlatTorVanishes,
		FlatTensorInjective,
		TorFiniteSuppSecondVariable,
		TensorOverQuotient,
		IdealQuotientModuleOn,
		tor_ext.TorLongExactMiddle,
		tor_ext.TorLongExactSub,
		tor_ext.TorZero,
		tor_ext.TorMapHom,
		tor_ext.TorMapIdentity,
		tor_ext.TorMapCompose,
		free_module.FreeLiftHom,
		free_module.FreeLiftDelta,
		module_homomorphism.ShortExactModules,
		module_homomorphism.ProjectionHom,
		module_homomorphism.ProjectionKernel,
		submodule.SpanSubmodule,
		submodule.QuotientModuleOn,
		tor_ext.TorZeroNatural,
		tensor_product.TensorUniversal,
	},
	Build: family.Card(module.ModuleOn.Statement(Statement{
		Binders: "∀J:set(A).",
		Hypotheses: []string{
			"ring_ideal(R, J)",
			"∀x y:A. x ∈ J ∧ y ∈ J ⇒ R.mul(x, y) = R.zero",
			"tor(R, M, quotient_module(regular_module(R), J), 1) = " +
				"{tor_zero(R, M, quotient_module(regular_module(R), J), 1)}",
			"flat_module(ideal_quotient_ring(R, J), ideal_quotient_module(R, J, M))",
		},
		Conclusion: "flat_module(R, M)",
	}),
		"show Tor₁(M, N) = 0 for every module N over R, in three steps. A free module over R/J, read "+
			"over R, is finite_supp_module(R/J, S): TorFiniteSuppSecondVariable at Tor₁(M, R/J) = 0. A "+
			"module N killed by J is the quotient of such an F by a K killed by J (FreeLiftHom): the "+
			"middle of the long exact sequence puts Tor₁(M, N) into the kernel of M ⊗ K → M ⊗ F "+
			"(TorLongExactSub, TorZero), which TensorOverQuotient identifies with M/JM ⊗ K → M/JM ⊗ F "+
			"over R/J, one-to-one by FlatTensorInjective there. Any N: JN and N/JN are killed by J since "+
			"J² = 0, so TorLongExactMiddle at 0 → JN → N → N/JN → 0; the definition is the case N = R/I"),
})}

// SquareZeroFlatCriterion — the local flatness criterion for a square-zero
// ideal J: M is flat over R exactly when M/JM is flat over R/J and μ :
// M/JM ⊗_{R/J} J → M is one-to-one.
var SquareZeroFlatCriterion = squareZeroFlatCriterionThm{family.Add(registry.ProofEntry{
	Name: "SquareZeroFlatCriterion",
	Key:  "prop_5fe81b8bfa2fb4aa",
	Reading: "The kernel of μ is Tor₁(M, R/J): the long exact sequence of 0 → J → R → R/J → 0 " +
		"with Tor₁(M, R) = 0 makes Tor₁(M, R/J) the kernel of M ⊗ J → M, which " +
		"TensorSquareZeroBaseChange carries to the kernel of μ. No finiteness is asked of R or M; the " +
		"nilpotence of J is load-bearing (SquareZeroFlatConverse has the counterexample without it).",
	Deps: []registry.EntryLike{
		SquareZeroFlatForward,
		SquareZeroFlatConverse,
		FlatQuotientBaseChange,
		TensorSquareZeroBaseChange,
		TorFreeSecondVariableZero,
		tor_ext.TorLongExactQuotient,
		tor_ext.TorLongExactSub,
		tor_ext.TorZero,
		module_homomorphism.ProjectionHom,
		module_homomorphism.ProjectionKernel,
		module_homomorphism.KernelTrivialIffInjective,
		tensor_product.TensorUniversal,
		tensor_product.TensorUniversalUnique,
		tensor_product.TensorRegular,
		tor_ext.TorZeroNatural,
	},
	Build: family.Card(module.ModuleOn.Statement(Statement{
		Binders: "∀J:set(A). ∀μ:(set(prod(set(B), set(A)) → set(A)) → B).",
		Hypotheses: []string{
			"ring_ideal(R, J)",
			"∀x y:A. x ∈ J ∧ y ∈ J ⇒ R.mul(x, y) = R.zero",
			"module_homomorphism(R, " +
				"    scalar_restriction(ideal_quotient_projection(R, J), " +
				"        tensor_module(ideal_quotient_ring(R, J), " +
				"            ideal_quotient_module(R, J, M), " +
				"            ideal_quotient_module(R, J, restrict_module(regular_module(R), J)))), " +
				"    M, " +
				"    μ)",
			"∀v:B. ∀j:A. " +
				"    v ∈ M.carrier ∧ j ∈ J ⇒ " +
				"    μ(tensor(ideal_quotient_ring(R, J), " +
				"            ideal_quotient_module(R, J, M), " +
				"            ideal_quotient_module(R, J, restrict_module(regular_module(R), J)), " +
				"            left_coset(M.add, " +
				"                v, " +
				"                module_span(R, M, {c • x | c:A, x:B | c ∈ J ∧ x ∈ M.carrier})), " +
				"            {j})) = " +
				"    j • v",
		},
		Conclusion: "flat_module(R, M) ⇔ " +
			"flat_module(ideal_quotient_ring(R, J), ideal_quotient_module(R, J, M)) ∧ " +
			"injective_on(tensor_product(ideal_quotient_ring(R, J), " +
			"        ideal_quotient_module(R, J, M), " +
			"        ideal_quotient_module(R, J, restrict_module(regular_module(R), J))), " +
			"    μ)",
	}),
		"⇒: FlatQuotientBaseChange and SquareZeroFlatForward. ⇐: Tor₁(M, R) = 0 "+
			"(TorFreeSecondVariableZero) makes the connecting map Tor₁(M, R/J) → Tor₀(M, J) one-to-one "+
			"(TorLongExactQuotient) onto the kernel of tor_map of the inclusion (TorLongExactSub), "+
			"which TorZero's identification, M ⊗ R ≅ M and the h of TensorSquareZeroBaseChange carry "+
			"to the kernel of μ, zero; so Tor₁(M, R/J) = 0 and SquareZeroFlatConverse applies"),
})}
