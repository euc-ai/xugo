// dual.go — the dual of a based chain complex with coefficients in a
// module N: in degree n the N-valued functions on the generators S(n),
// zero off S(n), and as coboundary the transpose of the boundary read in
// coordinates. The transpose is hom_precompose: a function u on the
// target generators goes to s ↦ Σ_t Φ(δ_s)(t) • u(t) on the source
// generators. Chain maps and chain homotopies transpose the same way,
// reversing the arrows. The dual is a cochain complex, functorial and
// homotopy invariant; it turns a quasi-isomorphism into a cochain
// homotopy equivalence and a degreewise split short exact sequence into
// a short exact sequence of cochain complexes; at a free complex based
// by the identity it is hom_complex. Together these give the long exact
// sequence of a split zigzag.

package free_complex_duality

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/chain_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The dual complex, the dual map and the dual homotopy
// ---------------------------------------------------------------------------

// FreeDualComplexDef — `free_dual_complex(R, N, P, S, e, r)`: the dual of
// the based complex (P, S, e, r) with coefficients in N. Degree n holds
// fun_module(N.zero, N.carrier, S(n)) under the pointwise operations, and
// the coboundary out of degree n is the transpose of the boundary
// P.d(n + 1) read in coordinates, r(n) ∘ P.d(n + 1) ∘ e(n + 1).
var FreeDualComplexDef = freeDualComplexDefThm{family.Define(registry.DefEntry{
	Name:  "FreeDualComplexDef",
	Key:   "prop_ee2ed83b7728593a",
	Const: "free_dual_complex",
	Type: "ring_ops(A) → " +
		"module_ops(A, C) → " +
		"complex_ops(A, B) → " +
		"(num → set(I)) → " +
		"(num → (I → A) → B) → " +
		"(num → B → I → A) → " +
		"complex_ops(A, I → C)",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀N:module_ops(A, C). " +
			"∀P:complex_ops(A, B). " +
			"∀S:(num → set(I)). " +
			"∀e:(num → (I → A) → B). " +
			"∀r:(num → B → I → A). " +
			"    free_dual_complex(R, N, P, S, e, r) = " +
			"    pack_complex(fun_add⟨D:I⟩(N.add), " +
			"        fun_zero⟨D:I⟩(N.zero), " +
			"        fun_neg⟨D:I⟩(N.neg), " +
			"        fun_smul⟨D:I⟩(N.smul), " +
			"        λn:num. fun_module(N.zero, N.carrier, S(n)), " +
			"        λn:num. hom_precompose(R, N, S(n + 1), λa:(I → A). r(n)(P.d(n + 1)(e(n + 1)(a)))))",
	},
	Reading: "It is Hom(P, N) read on the chosen bases: a homomorphism " +
		"out of the free module on S(n) is its values on the generators, and " +
		"precomposing with the boundary is transposing its matrix.",
})}

// FreeDualMapDef — `free_dual_map(R, N, S, e, r', f, n)`: the transpose in
// degree n of a chain map f read in coordinates, r'(n) ∘ f(n) ∘ e(n), from
// the N-valued functions on the target's generators to those on the
// source's generators S(n).
var FreeDualMapDef = freeDualMapDefThm{family.Define(registry.DefEntry{
	Name:  "FreeDualMapDef",
	Key:   "prop_29357c3ef31f1838",
	Const: "free_dual_map",
	Type: "ring_ops(A) → " +
		"module_ops(A, C) → " +
		"(num → set(I)) → " +
		"(num → (I → A) → B) → " +
		"(num → D → E → A) → " +
		"(num → B → D) → " +
		"num → " +
		"(E → C) → " +
		"I → " +
		"C",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀N:module_ops(A, C). " +
			"∀S:(num → set(I)). " +
			"∀e:(num → (I → A) → B). " +
			"∀r':(num → D → E → A). " +
			"∀f:(num → B → D). " +
			"∀n:num. " +
			"    free_dual_map(R, N, S, e, r', f, n) = " +
			"    hom_precompose(R, N, S(n), λa:(I → A). r'(n)(f(n)(e(n)(a))))",
	},
	Reading: "S and e are the source's generators and expansion, r' the target's coordinates; " +
		"the map runs the other way, from the target's dual to the source's. f need not be a chain map " +
		"for the definition: the splittings of a short exact sequence transpose by the same formula.",
})}

// freeDualHomotopyDef — `free_dual_homotopy(R, N, S, e, r', h, n)`: the
// transpose of a chain homotopy h, h(n) from degree n of the source into
// degree n + 1 of the target, indexed as cochain_homotopy reads it: degree
// n + 1 holds the transpose of h(n) read in coordinates, and degree 0 the
// zero map.
var freeDualHomotopyDef = freeDualHomotopyDefThm{family.Define(registry.DefEntry{
	Name:  "freeDualHomotopyDef",
	Key:   "prop_e6a69fc95bc621d",
	Const: "free_dual_homotopy",
	Type: "ring_ops(A) → " +
		"module_ops(A, C) → " +
		"(num → set(I)) → " +
		"(num → (I → A) → B) → " +
		"(num → D → E → A) → " +
		"(num → B → D) → " +
		"num → " +
		"(E → C) → " +
		"I → " +
		"C",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀N:module_ops(A, C). " +
			"∀S:(num → set(I)). " +
			"∀e:(num → (I → A) → B). " +
			"∀r':(num → D → E → A). " +
			"∀h:(num → B → D). " +
			"∀n:num. " +
			"    free_dual_homotopy(R, N, S, e, r', h, n) = " +
			"    COND(n = 0, " +
			"        λw:(E → C). λx:I. N.zero, " +
			"        hom_precompose(R, N, S(n - 1), λa:(I → A). r'(n)(h(n - 1)(e(n - 1)(a)))))",
	},
	Reading: "cochain_homotopy reads its homotopy at n + 1 as a map from degree n + 1 down to " +
		"degree n, and never at 0; the transpose of h(n), from the target's degree n + 1 to the " +
		"source's degree n, therefore stands at n + 1. Putting it at n would shift every degree by one.",
})}

// FreeDualCochainComplex — the dual of a based complex with coefficients
// in a module is a cochain complex.
var FreeDualCochainComplex = freeDualCochainComplexThm{family.Add(registry.ProofEntry{
	Name: "FreeDualCochainComplex",
	Key:  "prop_5f07ca043f516f0b",
	Deps: []registry.EntryLike{
		free_module.HomPrecomposeHom,
		free_module.HomPrecomposeCompose,
		free_module.HomPrecomposeCongruence,
		free_module.HomPrecomposeLinear,
		FreeDualComplexDef,
		BasedComplexChain,
		BasedExpandHom,
		BasedCoordinatesHom,
		BasedExpandCoordinates,
		chain_complex.CochainComplex,
		chain_complex.ComplexBoundaryHom,
		chain_complex.ComplexBoundaryTwice,
		function_module.FunModuleOn,
		function_module.FunctionModuleDef,
		module_homomorphism.HomCompose,
		module_homomorphism.HomZero,
	},
	Build: family.Card(BasedChainComplex.Statement(Statement{
		Binders: "∀N:module_ops(A, C).",
		Hypotheses: []string{
			"module_on(R, N)",
		},
		Conclusion: "cochain_complex(R, free_dual_complex(R, N, P, S, e, r))",
	}),
		"Each degree is function_module(N, S(n)) (FunModuleOn, FunctionModuleDef; FreeDualComplexDef). "+
			"The coboundary out of n is the transpose of Φ(n) = r(n) ∘ P.d(n + 1) ∘ e(n + 1), linear "+
			"between the free modules (BasedExpandHom, ComplexBoundaryHom, BasedCoordinatesHom, "+
			"HomCompose), so linear (HomPrecomposeHom). Two in a row: the transpose of Φ(n + 1) after that "+
			"of Φ(n) is the transpose of Φ(n) ∘ Φ(n + 1) (HomPrecomposeCompose), which on the free module "+
			"on S(n + 2) is r(n) ∘ P.d(n + 1) ∘ P.d(n + 2) ∘ e(n + 2) — e(n + 1) ∘ r(n + 1) cancelling on "+
			"P.terms(n + 1) (BasedExpandCoordinates) — the zero map (ComplexBoundaryTwice, HomZero), whose "+
			"transpose is zero (HomPrecomposeCongruence, HomPrecomposeLinear)."),
})}

// FreeDualMapIdentity — the identity transposes to the identity on the
// dual's terms.
var FreeDualMapIdentity = freeDualMapIdentityThm{family.Add(registry.ProofEntry{
	Name: "FreeDualMapIdentity",
	Key:  "prop_ff3e4bb1f66f8992",
	Reading: "Claimed at w in the function module only, and the guard " +
		"is load-bearing: hom_precompose is N.zero off the generators, so " +
		"at a w nonzero off S(m) the transpose of the identity is not w.",
	Deps: []registry.EntryLike{
		FreeDualMapDef,
		BasedCoordinatesExpand,
		free_module.HomPrecomposeCongruence,
		free_module.HomPrecomposeIdentity,
	},
	Build: family.Card(BasedChainComplex.Statement(Statement{
		Binders: "∀N:module_ops(A, C). ∀m:num. ∀w:(I → C).",
		Hypotheses: []string{
			"module_on(R, N)",
			"w ∈ fun_module(N.zero, N.carrier, S(m))",
		},
		Conclusion: "free_dual_map(R, N, S, e, r, λn:num. λx:B. x, m, w) = w",
	}),
		"r(m) ∘ e(m) is the identity on the free module (BasedCoordinatesExpand), "+
			"so HomPrecomposeCongruence and HomPrecomposeIdentity"),
})}

// FreeDualCochainMap — a chain map of based complexes transposes to a
// cochain map of the duals, in the opposite direction.
var FreeDualCochainMap = freeDualCochainMapThm{family.Add(registry.ProofEntry{
	Name: "FreeDualCochainMap",
	Key:  "prop_b6083a71fefd6c09",
	Deps: []registry.EntryLike{
		free_module.HomPrecomposeHom,
		free_module.HomPrecomposeCompose,
		free_module.HomPrecomposeCongruence,
		FreeDualMapDef,
		FreeDualComplexDef,
		BasedExpandHom,
		BasedCoordinatesHom,
		BasedExpandCoordinates,
		chain_complex.ChainMapHom,
		chain_complex.ChainMapSquare,
		chain_complex.CochainMapDef,
		module_homomorphism.HomCompose,
	},
	Build: family.Card(BasedChainComplex.Statement(Statement{
		Binders: "∀N:module_ops(A, C). " +
			"∀Q:complex_ops(A, D). " +
			"∀S':(num → set(E)). " +
			"∀e':(num → (E → A) → D). " +
			"∀r':(num → D → E → A). " +
			"∀f:(num → B → D).",
		Hypotheses: []string{
			"module_on(R, N)",
			"based_chain_complex(R, Q, S', e', r')",
			"chain_map(R, P, Q, f)",
		},
		Conclusion: "cochain_map(R, " +
			"    free_dual_complex(R, N, Q, S', e', r'), " +
			"    free_dual_complex(R, N, P, S, e, r), " +
			"    free_dual_map(R, N, S, e, r', f))",
	}),
		"each degree transposes r'(n) ∘ f(n) ∘ e(n), linear (BasedExpandHom, ChainMapHom, "+
			"BasedCoordinatesHom, HomCompose; HomPrecomposeHom). The square: on the free "+
			"module on S(n + 1), (r'(n) d' e'(n + 1)) ∘ (r'(n + 1) f(n + 1) e(n + 1)) = (r'(n) "+
			"f(n) e(n)) ∘ (r(n) d e(n + 1)), both being r'(n) ∘ Q.d(n + 1) ∘ f(n + 1) ∘ e(n + "+
			"1) once e ∘ r cancels in the middle (BasedExpandCoordinates) and ChainMapSquare "+
			"is applied; transpose both sides (HomPrecomposeCompose, HomPrecomposeCongruence)"),
})}

// FreeDualMapCompose — a composite of chain maps transposes to the
// reversed composite of the transposes on the dual's terms.
var FreeDualMapCompose = freeDualMapComposeThm{family.Add(registry.ProofEntry{
	Name: "FreeDualMapCompose",
	Key:  "prop_152652695c3561b",
	Reading: "The composite's transpose is read with the source's basis and the " +
		"far target's coordinates; the middle complex's basis cancels on its terms.",
	Deps: []registry.EntryLike{
		free_module.HomPrecomposeCompose,
		free_module.HomPrecomposeCongruence,
		FreeDualMapDef,
		BasedExpandHom,
		BasedCoordinatesHom,
		BasedExpandCoordinates,
		chain_complex.ChainMapHom,
		module_homomorphism.HomCompose,
	},
	Build: family.Card(BasedChainComplex.Statement(Statement{
		Binders: "∀N:module_ops(A, C). " +
			"∀Q:complex_ops(A, D). " +
			"∀S':(num → set(E)). " +
			"∀e':(num → (E → A) → D). " +
			"∀r':(num → D → E → A). " +
			"∀W:complex_ops(A, H). " +
			"∀S'':(num → set(F)). " +
			"∀e'':(num → (F → A) → H). " +
			"∀r'':(num → H → F → A). " +
			"∀f:(num → B → D). " +
			"∀g:(num → D → H). " +
			"∀m:num. " +
			"∀w:(F → C).",
		Hypotheses: []string{
			"module_on(R, N)",
			"based_chain_complex(R, Q, S', e', r')",
			"based_chain_complex(R, W, S'', e'', r'')",
			"chain_map(R, P, Q, f)",
			"chain_map(R, Q, W, g)",
			"w ∈ fun_module(N.zero, N.carrier, S''(m))",
		},
		Conclusion: "free_dual_map(R, N, S, e, r'', λn:num. λx:B. g(n)(f(n)(x)), m, w) = " +
			"free_dual_map(R, N, S, e, r', f, m, free_dual_map(R, N, S', e', r'', g, m, w))",
	}),
		"r''(m) g(m) f(m) e(m) = (r''(m) g(m) e'(m)) ∘ (r'(m) f(m) e(m)) on the "+
			"free module, e' ∘ r' cancelling on Q.terms(m) (BasedExpandCoordinates); "+
			"HomPrecomposeCompose and HomPrecomposeCongruence"),
})}

// FreeDualHomotopy — a chain homotopy between maps of based complexes
// transposes to a cochain homotopy between the transposed maps.
var FreeDualHomotopy = freeDualHomotopyThm{family.Add(registry.ProofEntry{
	Name: "FreeDualHomotopy",
	Key:  "prop_ff37acbbe3f1a963",
	Reading: "cochain_homotopy reads its homotopy at n + 1 as a map from degree n + 1 down to n and " +
		"never at 0, so the transpose of h(n) stands at n + 1; putting it at n would shift every degree.",
	Deps: []registry.EntryLike{
		free_module.HomPrecomposeHom,
		free_module.HomPrecomposeLinear,
		free_module.HomPrecomposeCompose,
		free_module.HomPrecomposeCongruence,
		freeDualHomotopyDef,
		FreeDualMapDef,
		FreeDualComplexDef,
		BasedExpandHom,
		BasedCoordinatesHom,
		BasedExpandCoordinates,
		chain_complex.ChainHomotopyDef,
		chain_complex.CochainHomotopyDef,
		chain_complex.ChainMapHom,
		module_homomorphism.HomCompose,
	},
	Build: family.Card(BasedChainComplex.Statement(Statement{
		Binders: "∀N:module_ops(A, C). " +
			"∀Q:complex_ops(A, D). " +
			"∀S':(num → set(E)). " +
			"∀e':(num → (E → A) → D). " +
			"∀r':(num → D → E → A). " +
			"∀f g h:(num → B → D).",
		Hypotheses: []string{
			"module_on(R, N)",
			"based_chain_complex(R, Q, S', e', r')",
			"chain_map(R, P, Q, f)",
			"chain_map(R, P, Q, g)",
			"chain_homotopy(R, P, Q, f, g, h)",
		},
		Conclusion: "cochain_homotopy(R, " +
			"    free_dual_complex(R, N, Q, S', e', r'), " +
			"    free_dual_complex(R, N, P, S, e, r), " +
			"    free_dual_map(R, N, S, e, r', f), " +
			"    free_dual_map(R, N, S, e, r', g), " +
			"    free_dual_homotopy(R, N, S, e, r', h))",
	}),
		"free_dual_homotopy puts the transpose of h(n), read in coordinates as r'(n + 1) ∘ h(n) ∘ e(n), "+
			"at n + 1, from degree n + 1 of the dual of Q to degree n of the dual of P "+
			"(freeDualHomotopyDef), linear by HomPrecomposeHom. The chain identity f − g = Q.d ∘ h + h ∘ "+
			"P.d at degree n + 1, read in coordinates with e ∘ r cancelled in the middle, transposes term "+
			"by term — difference and sum by HomPrecomposeLinear, each composite reversed by "+
			"HomPrecomposeCompose, maps equal on the free module by HomPrecomposeCongruence — to f^∨ − g^∨ "+
			"= k(n + 2) ∘ δ_Q(n + 1) + δ_P(n) ∘ k(n + 1); degree 0, f(0) − g(0) = Q.d(1) ∘ h(0), transposes "+
			"to f^∨(0) − g^∨(0) = k(1) ∘ δ_Q(0), cochain_homotopy's degree-0 clause (CochainHomotopyDef)."),
})}

// FreeDualHomotopyEquivalence — a chain homotopy equivalence of based
// complexes transposes to a cochain homotopy equivalence of the duals:
// the transposes of f and g are cochain maps, and the homotopy from g ∘ f
// to the identity of P transposes to one from the transpose of g ∘ f to
// that of the identity, which on the terms of the dual are the transpose
// of f after that of g and the identity; a cochain homotopy reads its two
// maps only on the terms, so it joins those. Likewise f ∘ g on Q.
var FreeDualHomotopyEquivalence = freeDualHomotopyEquivalenceThm{family.Add(registry.ProofEntry{
	Name: "FreeDualHomotopyEquivalence",
	Key:  "prop_3f613a3c71abef5a",
	Build: BasedChainComplex.Law(Statement{
		Binders: "∀N:module_ops(A, C). " +
			"∀Q:complex_ops(A, D). " +
			"∀S':(num → set(E)). " +
			"∀e':(num → (E → A) → D). " +
			"∀r':(num → D → E → A). " +
			"∀f:(num → B → D). " +
			"∀g:(num → D → B).",
		Hypotheses: []string{
			"module_on(R, N)",
			"based_chain_complex(R, Q, S', e', r')",
			"chain_homotopy_equivalence(R, P, Q, f, g)",
		},
		Conclusion: "cochain_homotopy_equivalence(R, " +
			"    free_dual_complex(R, N, Q, S', e', r'), " +
			"    free_dual_complex(R, N, P, S, e, r), " +
			"    free_dual_map(R, N, S, e, r', f), " +
			"    free_dual_map(R, N, S', e', r, g))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			P *Expr[ComplexOps[A, B]],
			S *Expr[Fun2[Nat, I, Bool]],
			e *Expr[Fun2[Nat, Fun[I, A], B]],
			r *Expr[Fun3[Nat, B, I, A]],
			based BasedChainComplexFact[on.R],
			N *Expr[ModuleOps[A, C]],
			Q *Expr[ComplexOps[A, D]],
			SPrime *Expr[Fun2[Nat, E, Bool]],
			ePrime *Expr[Fun2[Nat, Fun[E, A], D]],
			rPrime *Expr[Fun3[Nat, D, E, A]],
			f *Arrow2[Nat, B, D],
			g *Arrow2[Nat, D, B],
			given Fact,
		) {
			hyps := a.Conjuncts(
				given,
				"N is a module",
				"Q is based",
				"f and g are inverse chain homotopy equivalences")
			module, basedQ := hyps[0], hyps[1]
			parts := a.Conjuncts(
				a.Unfolded(hyps[2], chain_complex.ChainHomotopyEquivalenceDef),
				"f is a chain map",
				"g is a chain map",
				"g ∘ f is homotopic to the identity of P",
				"f ∘ g is homotopic to the identity of Q")
			fChain, gChain := parts[0], parts[1]
			k, kHomotopy := a.UnpackAs[Fun2[Nat, B, B]](parts[2], "k")
			l, lHomotopy := a.UnpackAs[Fun2[Nat, D, D]](parts[3], "l")

			fDual := a.Have(
				"the transpose of f is a cochain map from the dual of Q to the dual of P",
				"cochain_map(R, "+
					"    free_dual_complex(R, N, Q, S', e', r'), "+
					"    free_dual_complex(R, N, P, S, e, r), "+
					"    free_dual_map(R, N, S, e, r', f))",
				By(FreeDualCochainMap.Read(based).At(N, Q, SPrime, ePrime, rPrime, f), module, basedQ, fChain))
			gDual := a.Have(
				"the transpose of g is a cochain map from the dual of P to the dual of Q",
				"cochain_map(R, "+
					"    free_dual_complex(R, N, P, S, e, r), "+
					"    free_dual_complex(R, N, Q, S', e', r'), "+
					"    free_dual_map(R, N, S', e', r, g))",
				By(FreeDualCochainMap.Read(basedQ).At(N, P, S, e, r, g), module, based, gChain))

			// On P: g ∘ f and the identity are chain maps of P, and k
			// transposes to a homotopy between their transposes.
			gf := a.TermAs[Fun2[Nat, B, B]]("λn:num. λx:B. g(n)(f(n)(x))")
			idP := a.TermAs[Fun2[Nat, B, B]]("λn:num. λx:B. x")
			kTransposed := a.Have(
				"k transposes to a homotopy from the transpose of g ∘ f to that of the identity on the dual of P",
				"cochain_homotopy(R, "+
					"    free_dual_complex(R, N, P, S, e, r), "+
					"    free_dual_complex(R, N, P, S, e, r), "+
					"    free_dual_map(R, N, S, e, r, (λn:num. λx:B. g(n)(f(n)(x)))), "+
					"    free_dual_map(R, N, S, e, r, (λn:num. λx:B. x)), "+
					"    free_dual_homotopy(R, N, S, e, r, k))",
				By(
					FreeDualHomotopy.Read(based).At(N, P, S, e, r, gf, idP, k),
					module,
					based,
					chain_complex.ChainMapCompose.At(R, P, Q, P, f, g),
					chain_complex.ChainMapIdentity.Read(BasedComplexChain.Read(based)),
					fChain,
					gChain,
					kHomotopy))
			agreeOnP := a.Have(
				"on the terms of the dual of P, f's transpose after g's is the "+
					"transpose of g ∘ f, and the identity's transpose is the identity",
				Statement{
					Binders: "∀n:num. ∀u:(I → C).",
					Hypotheses: []string{
						"u ∈ free_dual_complex(R, N, P, S, e, r).terms(n)",
					},
					Conclusion: "free_dual_map(R, N, S, e, r', f, n, free_dual_map(R, N, S', e', r, g, n, u)) = " +
						"free_dual_map(R, N, S, e, r, λn:num. λx:B. g(n)(f(n)(x)), n, u) ∧ " +
						"u = free_dual_map(R, N, S, e, r, λn:num. λx:B. x, n, u)",
				},
				Derive(func(b *Argument) {
					n, u := b.FixAs[Nat]("n"), b.FixAs[Fun[I, C]]("u")
					inFunctions := b.Simplified(b.Assume(), Fwd(FreeDualComplexDef))
					b.Show(
						"the terms of the dual are the N-valued functions on S(n), where both laws of the transpose hold",
						By(
							Normalized,
							FreeDualMapCompose.Read(based).At(N, Q, SPrime, ePrime, rPrime, P, S, e, r, f, g, n, u),
							FreeDualMapIdentity.Read(based).At(N, n, u),
							module,
							basedQ,
							based,
							fChain,
							gChain,
							inFunctions))
				}))
			homotopyOnDualP := a.Have(
				"so k's transpose is a homotopy from the transpose "+
					"of f after that of g to the identity of the dual of P",
				"cochain_homotopy(R, "+
					"    free_dual_complex(R, N, P, S, e, r), "+
					"    free_dual_complex(R, N, P, S, e, r), "+
					"    (λn:num. λy:(I → C). "+
					"        free_dual_map(R, N, S, e, r', f, n, free_dual_map(R, N, S', e', r, g, n, y))), "+
					"    (λn:num. λy:(I → C). y), "+
					"    free_dual_homotopy(R, N, S, e, r, k))",
				By(chain_complex.CochainHomotopyCongruence, kTransposed, agreeOnP))

			// On Q: likewise with f ∘ g and l.
			fg := a.TermAs[Fun2[Nat, D, D]]("λn:num. λy:D. f(n)(g(n)(y))")
			idQ := a.TermAs[Fun2[Nat, D, D]]("λn:num. λy:D. y")
			lTransposed := a.Have(
				"l transposes to a homotopy from the transpose of f ∘ g to that of the identity on the dual of Q",
				"cochain_homotopy(R, "+
					"    free_dual_complex(R, N, Q, S', e', r'), "+
					"    free_dual_complex(R, N, Q, S', e', r'), "+
					"    free_dual_map(R, N, S', e', r', (λn:num. λy:D. f(n)(g(n)(y)))), "+
					"    free_dual_map(R, N, S', e', r', (λn:num. λy:D. y)), "+
					"    free_dual_homotopy(R, N, S', e', r', l))",
				By(
					FreeDualHomotopy.Read(basedQ).At(N, Q, SPrime, ePrime, rPrime, fg, idQ, l),
					module,
					basedQ,
					chain_complex.ChainMapCompose.At(R, Q, P, Q, g, f),
					chain_complex.ChainMapIdentity.Read(BasedComplexChain.Read(basedQ)),
					fChain,
					gChain,
					lHomotopy))
			agreeOnQ := a.Have(
				"on the terms of the dual of Q, g's transpose after f's is the "+
					"transpose of f ∘ g, and the identity's transpose is the identity",
				Statement{
					Binders: "∀n:num. ∀u:(E → C).",
					Hypotheses: []string{
						"u ∈ free_dual_complex(R, N, Q, S', e', r').terms(n)",
					},
					Conclusion: "free_dual_map(R, N, S', e', r, g, n, free_dual_map(R, N, S, e, r', f, n, u)) = " +
						"free_dual_map(R, N, S', e', r', λn:num. λy:D. f(n)(g(n)(y)), n, u) ∧ " +
						"u = free_dual_map(R, N, S', e', r', λn:num. λy:D. y, n, u)",
				},
				Derive(func(b *Argument) {
					n, u := b.FixAs[Nat]("n"), b.FixAs[Fun[E, C]]("u")
					inFunctions := b.Simplified(b.Assume(), Fwd(FreeDualComplexDef))
					b.Show(
						"the terms of the dual are the N-valued functions on S'(n), where both laws of the transpose hold",
						By(
							Normalized,
							FreeDualMapCompose.Read(basedQ).At(N, P, S, e, r, Q, SPrime, ePrime, rPrime, g, f, n, u),
							FreeDualMapIdentity.Read(basedQ).At(N, n, u),
							module,
							basedQ,
							based,
							fChain,
							gChain,
							inFunctions))
				}))
			homotopyOnDualQ := a.Have(
				"so l's transpose is a homotopy from the transpose "+
					"of g after that of f to the identity of the dual of Q",
				"cochain_homotopy(R, "+
					"    free_dual_complex(R, N, Q, S', e', r'), "+
					"    free_dual_complex(R, N, Q, S', e', r'), "+
					"    (λn:num. λx:(E → C). "+
					"        free_dual_map(R, N, S', e', r, g, n, free_dual_map(R, N, S, e, r', f, n, x))), "+
					"    (λn:num. λx:(E → C). x), "+
					"    free_dual_homotopy(R, N, S', e', r', l))",
				By(chain_complex.CochainHomotopyCongruence, lTransposed, agreeOnQ))

			a.Show(
				"so the two transposes, with the transposes of l and k "+
					"as the homotopies, are a cochain homotopy equivalence",
				Unfold(chain_complex.CochainHomotopyEquivalenceDef),
				By(fDual, gDual, homotopyOnDualQ, homotopyOnDualP))
		}),
})}

// FreeDualQuasiIsomorphism — the dual of a quasi-isomorphism between
// based complexes is a cochain homotopy equivalence and an isomorphism on
// cohomology in every degree.
var FreeDualQuasiIsomorphism = freeDualQuasiIsomorphismThm{family.Add(registry.ProofEntry{
	Name: "FreeDualQuasiIsomorphism",
	Key:  "prop_8b5c5d5f68dede84",
	Reading: "The inverse of the dual is the dual of a homotopy inverse g, transposed with Q's " +
		"basis and P's coordinates; the statement names it beside the chain homotopy equivalence it " +
		"comes from. The isomorphism on cohomology needs no choice of g: it is the map of f^∨ alone.",
	Deps: []registry.EntryLike{
		BasedQuasiIsomorphismHomotopyEquivalence,
		FreeDualHomotopyEquivalence,
		FreeDualCochainComplex,
		chain_complex.CochainHomotopyEquivalenceIsomorphism,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀P:complex_ops(A, B). " +
			"∀S:(num → set(I)). " +
			"∀e:(num → (I → A) → B). " +
			"∀r:(num → B → I → A). " +
			"∀Q:complex_ops(A, D). " +
			"∀S':(num → set(E)). " +
			"∀e':(num → (E → A) → D). " +
			"∀r':(num → D → E → A). " +
			"∀N:module_ops(A, C). " +
			"∀f:(num → B → D).",
		Hypotheses: []string{
			"based_chain_complex(R, P, S, e, r)",
			"based_chain_complex(R, Q, S', e', r')",
			"module_on(R, N)",
			"quasi_isomorphism(R, P, Q, f)",
		},
		Conclusion: "(∃g:(num → D → B). " +
			"    chain_homotopy_equivalence(R, P, Q, f, g) ∧ " +
			"    cochain_homotopy_equivalence(R, " +
			"        free_dual_complex(R, N, Q, S', e', r'), " +
			"        free_dual_complex(R, N, P, S, e, r), " +
			"        free_dual_map(R, N, S, e, r', f), " +
			"        free_dual_map(R, N, S', e', r, g))) ∧ " +
			"(∀n:num. " +
			"    module_isomorphism(R, " +
			"        cohomology_module(free_dual_complex(R, N, Q, S', e', r'), n), " +
			"        cohomology_module(free_dual_complex(R, N, P, S, e, r), n), " +
			"        cohomology_map(free_dual_complex(R, N, P, S, e, r), " +
			"            free_dual_map(R, N, S, e, r', f), " +
			"            n)))",
	},
		"BasedQuasiIsomorphismHomotopyEquivalence gives g with f and g inverse "+
			"chain homotopy equivalences; their transposes are inverse cochain homotopy "+
			"equivalences (FreeDualHomotopyEquivalence), and a cochain homotopy "+
			"equivalence of the duals, cochain complexes by FreeDualCochainComplex, is "+
			"an isomorphism on cohomology (CochainHomotopyEquivalenceIsomorphism)."),
})}

// FreeDualSplitShortExact — a short exact sequence of based complexes
// split in every degree by linear maps dualizes to a short exact sequence
// of cochain complexes, the arrows reversed.
var FreeDualSplitShortExact = freeDualSplitShortExactThm{family.Add(registry.ProofEntry{
	Name: "FreeDualSplitShortExact",
	Key:  "prop_819f1516e08deefe",
	Reading: "τ and σ are linear but need not commute with the " +
		"boundaries; only their transposes degree by degree are read.",
	Deps: []registry.EntryLike{
		free_module.HomPrecomposeIdentity,
		free_module.HomPrecomposeCompose,
		free_module.HomPrecomposeLinear,
		free_module.HomPrecomposeCongruence,
		free_module.HomPrecomposeHom,
		FreeDualCochainComplex,
		FreeDualCochainMap,
		FreeDualMapDef,
		FreeDualComplexDef,
		BasedExpandCoordinates,
		chain_complex.ShortExactComplexes,
		chain_complex.ShortExactCochainComplexes,
		chain_complex.ExactComplexesDef,
		module_homomorphism.ExactAtDef,
		module_homomorphism.ExactComposeZero,
		function_module.FunModuleDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀N:module_ops(A, C). " +
			"∀P':complex_ops(A, B). " +
			"∀P:complex_ops(A, D). " +
			"∀P'':complex_ops(A, G). " +
			"∀S₁:(num → set(I)). " +
			"∀e₁:(num → (I → A) → B). " +
			"∀r₁:(num → B → I → A). " +
			"∀S₂:(num → set(E)). " +
			"∀e₂:(num → (E → A) → D). " +
			"∀r₂:(num → D → E → A). " +
			"∀S₃:(num → set(F)). " +
			"∀e₃:(num → (F → A) → G). " +
			"∀r₃:(num → G → F → A). " +
			"∀i:(num → B → D). " +
			"∀p:(num → D → G). " +
			"∀τ:(num → G → D). " +
			"∀σ:(num → D → B).",
		Hypotheses: []string{
			"module_on(R, N)",
			"based_chain_complex(R, P', S₁, e₁, r₁)",
			"based_chain_complex(R, P, S₂, e₂, r₂)",
			"based_chain_complex(R, P'', S₃, e₃, r₃)",
			"short_exact_complexes(R, P', P, P'', i, p)",
			"∀n:num. module_homomorphism(R, complex_module(P'', n), complex_module(P, n), τ(n))",
			"∀n:num. module_homomorphism(R, complex_module(P, n), complex_module(P', n), σ(n))",
			"∀n:num. ∀z:G. z ∈ P''.terms(n) ⇒ p(n)(τ(n)(z)) = z",
			"∀n:num. ∀x:B. x ∈ P'.terms(n) ⇒ σ(n)(i(n)(x)) = x",
			"∀n:num. ∀y:D. y ∈ P.terms(n) ⇒ P.add(i(n)(σ(n)(y)), τ(n)(p(n)(y))) = y",
		},
		Conclusion: "short_exact_cochain_complexes(R, " +
			"    free_dual_complex(R, N, P'', S₃, e₃, r₃), " +
			"    free_dual_complex(R, N, P, S₂, e₂, r₂), " +
			"    free_dual_complex(R, N, P', S₁, e₁, r₁), " +
			"    free_dual_map(R, N, S₂, e₂, r₃, p), " +
			"    free_dual_map(R, N, S₁, e₁, r₂, i))",
	},
		"The duals are cochain complexes and p^∨, i^∨ cochain maps (FreeDualCochainComplex, "+
			"FreeDualCochainMap). In each degree transpose the splitting, read in coordinates with e ∘ "+
			"r cancelled in the middle (BasedExpandCoordinates): τ^∨ ∘ p^∨ = (p ∘ τ)^∨ = id makes p^∨ "+
			"one-to-one; i^∨ ∘ σ^∨ = (σ ∘ i)^∨ = id makes i^∨ onto; i^∨ ∘ p^∨ = (p ∘ i)^∨ = 0 "+
			"(ExactComposeZero at the degreewise exactness); and w with i^∨(w) = 0 is (i σ + τ p)^∨(w) "+
			"= σ^∨(i^∨(w)) + p^∨(τ^∨(w)) = p^∨(τ^∨(w)) — exactness at the middle (HomPrecomposeCompose, "+
			"HomPrecomposeIdentity, HomPrecomposeLinear, HomPrecomposeCongruence; ExactComplexesDef, "+
			"ExactAtDef). τ^∨ and σ^∨ are free_dual_map at τ and σ, which need not be chain maps, "+
			"landing in the function modules by HomPrecomposeHom."),
})}

// FreeDualCoefficientShortExact — a short exact sequence of coefficient
// modules gives a short exact sequence of the duals of one based complex,
// composition with i and p in every degree: no splitting is asked, since
// the terms are all functions on the generators and every argument runs
// at one generator at a time. Composition with a linear map is linear in
// each degree and passes through every coboundary, the transpose of the
// boundary read in coordinates; i stays one-to-one at each generator, a
// function p kills is i of the preimages inverse_on chooses, and a
// function into the quotient is p of a preimage chosen on S(n), N.zero
// off it.
var FreeDualCoefficientShortExact = freeDualCoefficientShortExactThm{family.Add(registry.ProofEntry{
	Name: "FreeDualCoefficientShortExact",
	Key:  "prop_36c42d5581f2a85a",
	Reading: "The coefficient twin of FreeDualSplitShortExact, which varies the based " +
		"complex instead and needs a degreewise splitting. Onto in each degree needs a " +
		"preimage chosen at each generator, which inverse_on supplies, N.zero off S(n).",
	Build: family.Sections(BasedChainComplex.Statement(Statement{
		Binders: "∀N':module_ops(A, C). " +
			"∀N:module_ops(A, D). " +
			"∀N'':module_ops(A, E). " +
			"∀i:(C → D). " +
			"∀p:(D → E).",
		Hypotheses: []string{
			"short_exact_modules(R, N', N, N'', i, p)",
		},
		Conclusion: "short_exact_cochain_complexes(R, " +
			"    free_dual_complex(R, N', P, S, e, r), " +
			"    free_dual_complex(R, N, P, S, e, r), " +
			"    free_dual_complex(R, N'', P, S, e, r), " +
			"    λn:num. λw:(I → C). λx:I. i(w(x)), " +
			"    λn:num. λw:(I → D). λx:I. p(w(x)))",
	}),
		func(ctx *Script, headline string) *GoalStackNode {
			// A function lies in fun_module exactly when its values lie in the
			// carrier and it vanishes off the generators: the definition read
			// at one function.
			member := ctx.Lemma(
				"∀zero:C. ∀c:set(C). ∀T:set(I). ∀w:(I → C). "+
					"    w ∈ fun_module(zero, c, T) ⇔ (∀x:I. w(x) ∈ c) ∧ (∀x:I. x ∉ T ⇒ w(x) = zero)",
				Chain(Simp(Fwd(function_module.FunModuleDef)), BySets()))

			// Composing with a linear map keeps a function vanishing off the
			// generators: its values stay in the carrier and N.zero goes to N'.zero.
			composed := ctx.Lemma("∀R:ring_ops(A). ∀N:module_ops(A, C). ∀N':module_ops(A, D). ∀k:(C → D). "+
				"    module_homomorphism(R, N, N', k) ⇒ "+
				"    ∀T:set(I). ∀w:(I → C). "+
				"        w ∈ fun_module(N.zero, N.carrier, T) ⇒ "+
				"        (λx:I. k(w(x))) ∈ fun_module(N'.zero, N'.carrier, T)",
				func(
					a *Argument,
					R *Expr[RingOps[A]],
					N *Expr[ModuleOps[A, C]],
					Nʹ *Expr[ModuleOps[A, D]],
					k *Arrow[C, D],
					linear Fact,
					T, w Term,
					wIn Fact,
				) {
					pointwise := a.Have(
						"w is valued in N and vanishes off T",
						"(∀x:I. w(x) ∈ N.carrier) ∧ (∀x:I. x ∉ T ⇒ w(x) = N.zero)",
						By(wIn, member))
					values := a.Have(
						"k keeps each value in N'",
						"∀x:I. k(w(x)) ∈ N'.carrier",
						By(pointwise, module_homomorphism.HomIn.Read(linear)))
					offT := a.Have(
						"off T it sends N.zero to N'.zero",
						"∀x:I. x ∉ T ⇒ k(w(x)) = N'.zero",
						By(pointwise, module_homomorphism.HomZero.Read(linear)))
					a.Show(
						"so k ∘ w is an N'-valued function vanishing off T",
						By(values, offT, member))
				})

			// A linear map of coefficient modules induces a cochain map of the
			// duals, composition with it in every degree.
			coefficientMap := ctx.Lemma(BasedChainComplex.Statement(Statement{
				Binders: "∀N:module_ops(A, C). ∀N':module_ops(A, D). ∀k:(C → D).",
				Hypotheses: []string{
					"module_homomorphism(R, N, N', k)",
				},
				Conclusion: "cochain_map(R, " +
					"    free_dual_complex(R, N, P, S, e, r), " +
					"    free_dual_complex(R, N', P, S, e, r), " +
					"    λn:num. λw:(I → C). λx:I. k(w(x)))",
			}),
				func(
					a *Argument,
					R *Expr[RingOps[A]],
					P *Expr[ComplexOps[A, B]],
					S, e, r Term,
					based BasedChainComplexFact[on.R],
					N *Expr[ModuleOps[A, C]],
					Nʹ *Expr[ModuleOps[A, D]],
					k *Arrow[C, D],
					linear Fact,
				) {
					moduleN, moduleNʹ :=
						module_homomorphism.HomSource.Read(linear), module_homomorphism.HomTarget.Read(linear)
					coordinates := a.Have(
						"the boundary read in coordinates is linear between the free modules",
						"∀n:num. "+
							"    module_homomorphism(R, "+
							"        free_module_record(R, S(n + 1)), "+
							"        free_module_record(R, S(n)), "+
							"        λa:(I → A). r(n)(P.d(n + 1)(e(n + 1)(a))))",
						Derive(func(b *Argument) {
							n := b.FixAs[Nat]("n")
							b.Have(
								"r(n) ∘ P.d(n + 1) ∘ e(n + 1) is a composite of three linear maps",
								"module_homomorphism(R, "+
									"    free_module_record(R, S(n + 1)), "+
									"    free_module_record(R, S(n)), "+
									"    r(n) ∘ (P.d(n + 1) ∘ e(n + 1)))",
								By(
									module_homomorphism.HomCompose,
									BasedExpandHom.Read(based).At(b.TermAs[Nat]("n + 1")),
									chain_complex.ComplexBoundaryHom.Read(BasedComplexChain.Read(based)).At(n),
									BasedCoordinatesHom.Read(based).At(n)))
							b.Show(
								"and the composite is a ↦ r(n)(P.d(n + 1)(e(n + 1)(a)))",
								Unfold(functions.ComposeApply))
						}))
					degrees := a.Have(
						"in each degree composition with k is linear, from "+
							"the N-valued functions on S(n) to the N'-valued ones",
						"∀n:num. "+
							"    module_homomorphism(R, "+
							"        complex_module(free_dual_complex(R, N, P, S, e, r), n), "+
							"        complex_module(free_dual_complex(R, N', P, S, e, r), n), "+
							"        λw:(I → C). λx:I. k(w(x)))",
						Derive(func(b *Argument) {
							b.FixAs[Nat]("n")
							generators := b.Term("S(n)")
							values := b.Have(
								"a member's values lie in N",
								"∀u:(I → C). ∀x:I. u ∈ fun_module(N.zero, N.carrier, S(n)) ⇒ u(x) ∈ N.carrier",
								By(member))
							into := b.Have(
								"composing with k keeps a function vanishing off S(n)",
								Statement{
									Binders: "∀w:(I → C).",
									Hypotheses: []string{
										"w ∈ fun_module(N.zero, N.carrier, S(n))",
									},
									Conclusion: "(λx:I. k(w(x))) ∈ fun_module(N'.zero, N'.carrier, S(n))",
								},
								By(linear, composed))
							sums := b.Have(
								"composing with k carries a sum to the sum, k being additive at each generator",
								Statement{
									Binders: "∀u v:(I → C).",
									Hypotheses: []string{
										"u ∈ fun_module(N.zero, N.carrier, S(n))",
										"v ∈ fun_module(N.zero, N.carrier, S(n))",
									},
									Conclusion: "(λx:I. k(fun_add(u, v, x))) = fun_add(λx:I. k(u(x)), λx:I. k(v(x)))",
								},
								Derive(func(c *Argument) {
									c.Fix("u")
									c.Fix("v")
									members := c.Assume()
									c.Show(
										"at each x it is k(u(x) + v(x)) = k(u(x)) + k(v(x))",
										Funext(),
										Simp(Fwd(function_module.FunAddDef)),
										By(values, members, module_homomorphism.HomAdd.Read(linear)))
								}))
							multiples := b.Have(
								"composing with k carries a multiple to the multiple, k commuting with scaling at each generator",
								Statement{
									Binders: "∀c:A. ∀u:(I → C).",
									Hypotheses: []string{
										"c ∈ R.carrier",
										"u ∈ fun_module(N.zero, N.carrier, S(n))",
									},
									Conclusion: "(λx:I. k(fun_smul(N.smul, c, u, x))) = fun_smul(N'.smul, c, λx:I. k(u(x)))",
								},
								Derive(func(c *Argument) {
									c.FixAs[A]("c")
									c.Fix("u")
									given := c.Assume()
									c.Show(
										"at each x it is k(c • u(x)) = c • k(u(x))",
										Funext(),
										Simp(Fwd(function_module.FunSmulDef)),
										By(values, given, module_homomorphism.HomSmul.Read(linear)))
								}))
							source := b.Simplified(
								function_module.FunModuleOn.Read(moduleN).AsFact().At(generators),
								Fwd(function_module.FunctionModuleDef))
							target := b.Simplified(
								function_module.FunModuleOn.Read(moduleNʹ).AsFact().At(generators),
								Fwd(function_module.FunctionModuleDef))
							b.Do(Unfold(chain_complex.ComplexModuleDef))
							b.Show(
								"the degree modules are the function modules, between which composition with k is a homomorphism",
								By(module_homomorphism.ModuleHomomorphismDef, source, target, into, sums, multiples))
						}))
					squares := a.Have(
						"composition with k passes through each coboundary, the transpose of the boundary in coordinates",
						Statement{
							Binders: "∀n:num. ∀u:(I → C).",
							Hypotheses: []string{
								"u ∈ fun_module(N.zero, N.carrier, S(n))",
							},
							Conclusion: "(λx:I. " +
								"    k(hom_precompose(R, N, S(n + 1), λa:(I → A). r(n)(P.d(n + 1)(e(n + 1)(a))), u, x))) = " +
								"hom_precompose(R, N', S(n + 1), λa:(I → A). r(n)(P.d(n + 1)(e(n + 1)(a))), λx:I. k(u(x)))",
						},
						By(free_module.HomPrecomposeCoefficientNatural, moduleN, moduleNʹ, linear, coordinates))
					a.Show(
						"so composition with k is a cochain map",
						By(chain_complex.CochainMapDef, degrees, squares))
				})

			return ctx.Theorem(headline, func(
				a *Argument,
				R *Expr[RingOps[A]],
				P *Expr[ComplexOps[A, B]],
				S, e, r Term,
				based BasedChainComplexFact[on.R],
				Nʹ *Expr[ModuleOps[A, C]],
				N *Expr[ModuleOps[A, D]],
				Nʺ *Expr[ModuleOps[A, E]],
				i *Arrow[C, D],
				p *Arrow[D, E],
				sequence Fact,
			) {
				parts := a.Conjuncts(
					a.Unfolded(sequence, module_homomorphism.ShortExactModules),
					"i is linear",
					"p is linear",
					"i is one-to-one on N'",
					"the image of i is the kernel of p",
					"p maps N onto N''")
				linearI, linearP, oneToOne, exact, onto := parts[0], parts[1], parts[2], parts[3], parts[4]
				moduleNʹ, moduleN :=
					module_homomorphism.HomSource.Read(linearI), module_homomorphism.HomTarget.Read(linearI)

				dualʹ := a.Have(
					"the dual with coefficients in N' is a cochain complex",
					"cochain_complex(R, free_dual_complex(R, N', P, S, e, r))",
					By(FreeDualCochainComplex.Read(based).At(Nʹ), moduleNʹ))
				dual := a.Have(
					"so is the dual with coefficients in N",
					"cochain_complex(R, free_dual_complex(R, N, P, S, e, r))",
					By(FreeDualCochainComplex.Read(based).At(N), moduleN))
				dualʺ := a.Have(
					"and the dual with coefficients in N''",
					"cochain_complex(R, free_dual_complex(R, N'', P, S, e, r))",
					By(FreeDualCochainComplex.Read(based).At(Nʺ), module_homomorphism.HomTarget.Read(linearP)))
				inclusion := a.Have(
					"composition with i is a cochain map from the dual with coefficients in N' to the one in N",
					"cochain_map(R, "+
						"    free_dual_complex(R, N', P, S, e, r), "+
						"    free_dual_complex(R, N, P, S, e, r), "+
						"    (λn:num. λw:(I → C). λx:I. i(w(x))))",
					By(based, linearI, coefficientMap))
				projection := a.Have(
					"composition with p is a cochain map from the dual with coefficients in N to the one in N''",
					"cochain_map(R, "+
						"    free_dual_complex(R, N, P, S, e, r), "+
						"    free_dual_complex(R, N'', P, S, e, r), "+
						"    (λn:num. λw:(I → D). λx:I. p(w(x))))",
					By(based, linearP, coefficientMap))

				// Exactness of the modules, read at one element.
				imageIsKernel := a.Unfolded(exact, module_homomorphism.ExactAtDef)
				killed := a.Have(
					"p kills the image of i",
					"∀a:C. a ∈ N'.carrier ⇒ p(i(a)) = N''.zero",
					BySets(exact, module_homomorphism.ExactAtDef, group_homomorphism.GroupKernelDef))
				lifted := a.Have(
					"what p kills in N comes from N'",
					"∀y:D. y ∈ N.carrier ∧ p(y) = N''.zero ⇒ y ∈ image(i, N'.carrier)",
					Derive(func(b *Argument) {
						b.FixAs[D]("y")
						inKernel := b.Assume()
						b.Do(imageIsKernel.Rw(), Simp(Fwd(group_homomorphism.GroupKernelDef)))
						b.Show(
							"the image of i is the kernel of p, where y lies",
							BySets(inKernel))
					}))
				zeroPreimage := a.Have(
					"the chosen preimage of N.zero is N'.zero, i being one-to-one",
					"inverse_on(N'.carrier, i, N.zero) = N'.zero",
					By(
						Normalized,
						oneToOne,
						module_homomorphism.HomZero.Read(linearI),
						functions.InverseOnLeft.At(a.TermAs[Set[C]]("N'.carrier"), i, a.TermAs[C]("N'.zero")),
						group.OneIn.Read(module.AddGroupOn.Read(moduleNʹ))))

				exactness := a.Have(
					"composition with i and with p is exact in every degree, generator by generator",
					"exact_complexes(free_dual_complex(R, N', P, S, e, r), "+
						"    free_dual_complex(R, N, P, S, e, r), "+
						"    free_dual_complex(R, N'', P, S, e, r), "+
						"    (λn:num. λw:(I → C). λx:I. i(w(x))), "+
						"    (λn:num. λw:(I → D). λx:I. p(w(x))))",
					Derive(func(b *Argument) {
						b.Do(Unfold(chain_complex.ExactComplexesDef))
						b.FixAs[Nat]("n")
						oneToOneDegree := b.Have(
							"composition with i is one-to-one on the N'-valued "+
								"functions, i being one-to-one on N' at each generator",
							"injective_on(fun_module(N'.zero, N'.carrier, S(n)), λw:(I → C). λx:I. i(w(x)))",
							Simp(Fwd(functions.InjectiveOnDef)),
							Derive(func(c *Argument) {
								c.Fix("u")
								c.Fix("v")
								equal := c.Assume()
								c.Do(Funext())
								c.Show(
									"at each x, u(x) and v(x) lie in N' and have one image under i",
									By(equal, oneToOne, member, functions.InjectiveOnDef))
							}))

						imageInKernel := b.Have(
							"composition with i lands in the kernel of composition with p",
							Statement{
								Binders: "∀u:(I → C).",
								Hypotheses: []string{
									"u ∈ fun_module(N'.zero, N'.carrier, S(n))",
								},
								Conclusion: "(λx:I. i(u(x))) ∈ fun_module(N.zero, N.carrier, S(n)) ∧ " +
									"(λx:I. p(i(u(x)))) = fun_zero(N''.zero)",
							},
							Derive(func(c *Argument) {
								c.Fix("u")
								uIn := c.Assume()
								c.Do(SplitConj(
									Case(
										"composing with i keeps a function vanishing off S(n)",
										By(linearI, uIn, composed)),
									Case(
										"p(i(u(x))) is N''.zero at each generator",
										Funext(),
										Simp(Fwd(function_module.FunZeroDef)),
										By(killed, uIn, member)),
								))
							}))
						kernelInImage := b.Have(
							"what composition with p kills is i of the preimages chosen at each generator",
							Statement{
								Binders: "∀w:(I → D).",
								Hypotheses: []string{
									"w ∈ fun_module(N.zero, N.carrier, S(n))",
									"(λx:I. p(w(x))) = fun_zero(N''.zero)",
								},
								Conclusion: "∃u:(I → C). u ∈ fun_module(N'.zero, N'.carrier, S(n)) ∧ w = λx:I. i(u(x))",
							},
							Derive(func(c *Argument) {
								c.Fix("w")
								given := c.Conjuncts(
									c.Assume(),
									"w is an N-valued function vanishing off S(n)",
									"p kills every value of w")
								pointwise := c.Have(
									"w is valued in N and vanishes off S(n)",
									"(∀x:I. w(x) ∈ N.carrier) ∧ (∀x:I. x ∉ S(n) ⇒ w(x) = N.zero)",
									By(given[0], member))
								fromNʹ := c.Have(
									"each value of w comes from N'",
									"∀x:I. w(x) ∈ image(i, N'.carrier)",
									By(lifted, pointwise, given[1], function_module.FunZeroDef))
								c.Take(c.Term("λx:I. inverse_on(N'.carrier, i, w(x))"))
								inNʹ := c.Have(
									"the chosen preimages lie in N'",
									"∀x:I. inverse_on(N'.carrier, i, w(x)) ∈ N'.carrier",
									By(fromNʹ, functions.InverseOnIn))
								offS := c.Have(
									"off S(n) w is N.zero, whose chosen preimage is N'.zero",
									"∀x:I. x ∉ S(n) ⇒ inverse_on(N'.carrier, i, w(x)) = N'.zero",
									By(zeroPreimage, pointwise))
								c.Do(SplitConj(
									Case(
										"the preimages form an N'-valued function vanishing off S(n)",
										By(inNʹ, offS, member)),
									Case(
										"i takes each chosen preimage back to the value of w",
										Funext(),
										By(fromNʹ, functions.InverseOnRight)),
								))
							}))
						exactDegree := b.Have(
							"so the image of composition with i is the kernel of composition with p",
							"exact_at(fun_zero(N''.zero), "+
								"    fun_module(N'.zero, N'.carrier, S(n)), "+
								"    fun_module(N.zero, N.carrier, S(n)), "+
								"    λw:(I → C). λx:I. i(w(x)), "+
								"    λw:(I → D). λx:I. p(w(x)))",
							Simp(Fwd(module_homomorphism.ExactAtDef), Fwd(group_homomorphism.GroupKernelDef)),
							BySets(imageInKernel, kernelInImage))

						intoNʺ := b.Have(
							"composing with p keeps a function vanishing off S(n)",
							Statement{
								Binders: "∀w:(I → D).",
								Hypotheses: []string{
									"w ∈ fun_module(N.zero, N.carrier, S(n))",
								},
								Conclusion: "(λx:I. p(w(x))) ∈ fun_module(N''.zero, N''.carrier, S(n))",
							},
							By(linearP, composed))
						preimages := b.Have(
							"an N''-valued function vanishing off S(n) is p of a preimage chosen on S(n) and N.zero off it",
							Statement{
								Binders: "∀v:(I → E).",
								Hypotheses: []string{
									"v ∈ fun_module(N''.zero, N''.carrier, S(n))",
								},
								Conclusion: "∃w:(I → D). w ∈ fun_module(N.zero, N.carrier, S(n)) ∧ v = λx:I. p(w(x))",
							},
							Derive(func(c *Argument) {
								c.Fix("v")
								vIn := c.Assume()
								pointwise := c.Have(
									"v is valued in N'' and vanishes off S(n)",
									"(∀x:I. v(x) ∈ N''.carrier) ∧ (∀x:I. x ∉ S(n) ⇒ v(x) = N''.zero)",
									By(vIn, member))
								fromN := c.Have(
									"each value of v comes from N, p being onto N''",
									"∀x:I. v(x) ∈ image(p, N.carrier)",
									By(Normalized, onto, pointwise))
								c.Take(c.Term("λx:I. COND(x ∈ S(n), inverse_on(N.carrier, p, v(x)), N.zero)"))
								inN := c.Have(
									"the chosen preimages and N.zero lie in N",
									"∀x:I. COND(x ∈ S(n), inverse_on(N.carrier, p, v(x)), N.zero) ∈ N.carrier",
									By(fromN, functions.InverseOnIn, group.OneIn.Read(module.AddGroupOn.Read(moduleN))))
								c.Do(SplitConj(
									Case(
										"the preimages form an N-valued function vanishing off S(n)",
										By(inN, member)),
									Case(
										"p takes each preimage back to v(x) on S(n), and N.zero to N''.zero = v(x) off it",
										Funext(),
										By(fromN, pointwise, functions.InverseOnRight, module_homomorphism.HomZero.Read(linearP))),
								))
							}))
						ontoDegree := b.Have(
							"so composition with p is onto the N''-valued functions",
							"image(λw:(I → D). λx:I. p(w(x)), fun_module(N.zero, N.carrier, S(n))) = "+
								"fun_module(N''.zero, N''.carrier, S(n))",
							BySets(intoNʺ, preimages))
						b.Show(
							"one-to-one, exact in the middle and onto in degree n",
							By(oneToOneDegree, exactDegree, ontoDegree))
					}))
				a.Show(
					"the three duals and the two cochain maps form a short exact sequence",
					By(chain_complex.ShortExactCochainComplexes, dualʹ, dual, dualʺ, inclusion, projection, exactness))
			})
		}),
})}

// ---------------------------------------------------------------------------
// The long exact sequence of a split zigzag
// ---------------------------------------------------------------------------

// SplitZigzagDualLongExact — a degreewise split short exact sequence of
// based complexes, joined to a bottom row of based complexes by three
// quasi-isomorphisms and two squares commuting up to homotopy, dualizes
// to a long exact sequence of the bottom row's cohomology with the duals
// of its two maps.
var SplitZigzagDualLongExact = splitZigzagDualLongExactThm{family.Add(registry.ProofEntry{
	Name: "SplitZigzagDualLongExact",
	Key:  "prop_32ba2d1bff97f9e1",
	Reading: "The connecting map is the top row's carried across, (c^∨)_*⁻¹ ∘ δ^top ∘ (a^∨)_*, with " +
		"coconnecting_hom's convention and no sign; the inverse is inverse_on on the cohomology of Z^∨, " +
		"a genuine inverse there since (c^∨)_* is a bijection, and off the classes the value is never " +
		"read. A strict square c ∘ p ∘ b = ψ meets the second homotopy hypothesis with the zero homotopy.",
	Deps: []registry.EntryLike{
		chain_complex.CohomologyMapCompose,
		chain_complex.CohomologyMapCongruence,
		chain_complex.CoLongExactStart,
		FreeDualSplitShortExact,
		FreeDualQuasiIsomorphism,
		FreeDualCochainMap,
		FreeDualMapCompose,
		FreeDualHomotopy,
		FreeDualCochainComplex,
		chain_complex.CoLongExactMiddle,
		chain_complex.CoLongExactQuotient,
		chain_complex.CoLongExactSub,
		chain_complex.CoconnectingHom,
		chain_complex.HomotopicSameCohomologyMap,
		chain_complex.CohomologyMapHom,
		chain_complex.CoboundariesDef,
		chain_complex.CohomologyModuleDef,
		chain_complex.QuasiIsomorphismDef,
		chain_complex.ChainMapDef,
		module_homomorphism.ExactAtIsomorphism,
		module_homomorphism.IsomorphismInverse,
		module_homomorphism.ModuleIsomorphismDef,
		functions.InverseOnLeft,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀N:module_ops(A, C). " +
			"∀P' P P'':complex_ops(A, B). " +
			"∀S₁ S₂ S₃:(num → set(I)). " +
			"∀e₁ e₂ e₃:(num → (I → A) → B). " +
			"∀r₁ r₂ r₃:(num → B → I → A). " +
			"∀i p τ σ:(num → B → B). " +
			"∀X Y Z:complex_ops(A, D). " +
			"∀S₄ S₅ S₆:(num → set(E)). " +
			"∀e₄ e₅ e₆:(num → (E → A) → D). " +
			"∀r₄ r₅ r₆:(num → D → E → A). " +
			"∀a c:(num → B → D). " +
			"∀b:(num → D → B). " +
			"∀φ ψ:(num → D → D).",
		Hypotheses: []string{
			"module_on(R, N)",
			"based_chain_complex(R, P', S₁, e₁, r₁)",
			"based_chain_complex(R, P, S₂, e₂, r₂)",
			"based_chain_complex(R, P'', S₃, e₃, r₃)",
			"based_chain_complex(R, X, S₄, e₄, r₄)",
			"based_chain_complex(R, Y, S₅, e₅, r₅)",
			"based_chain_complex(R, Z, S₆, e₆, r₆)",
			"short_exact_complexes(R, P', P, P'', i, p)",
			"∀n:num. module_homomorphism(R, complex_module(P'', n), complex_module(P, n), τ(n))",
			"∀n:num. module_homomorphism(R, complex_module(P, n), complex_module(P', n), σ(n))",
			"∀n:num. ∀z:B. z ∈ P''.terms(n) ⇒ p(n)(τ(n)(z)) = z",
			"∀n:num. ∀x:B. x ∈ P'.terms(n) ⇒ σ(n)(i(n)(x)) = x",
			"∀n:num. ∀y:B. y ∈ P.terms(n) ⇒ P.add(i(n)(σ(n)(y)), τ(n)(p(n)(y))) = y",
			"quasi_isomorphism(R, P', X, a)",
			"quasi_isomorphism(R, Y, P, b)",
			"quasi_isomorphism(R, P'', Z, c)",
			"chain_map(R, X, Y, φ)",
			"chain_map(R, Y, Z, ψ)",
			"∃h:(num → B → B). chain_homotopy(R, P', P, i, λn:num. λx:B. b(n)(φ(n)(a(n)(x))), h)",
			"∃h:(num → D → D). chain_homotopy(R, Y, Z, λn:num. λy:D. c(n)(p(n)(b(n)(y))), ψ, h)",
		},
		Conclusion: "injective_on(cohomology(«dualZ», 0), cohomology_map(«dualY», «dualPsi», 0)) ∧ " +
			"(∀n:num. " +
			"    exact_at(coboundaries(«dualX», n), " +
			"        cohomology(«dualZ», n), " +
			"        cohomology(«dualY», n), " +
			"        cohomology_map(«dualY», «dualPsi», n), " +
			"        cohomology_map(«dualX», «dualPhi», n))) ∧ " +
			"(∀n:num. " +
			"    exact_at(coboundaries(«dualZ», n + 1), " +
			"        cohomology(«dualY», n), " +
			"        cohomology(«dualX», n), " +
			"        cohomology_map(«dualX», «dualPhi», n), " +
			"        λs:set(E → C). " +
			"            inverse_on(cohomology(«dualZ», n + 1), " +
			"                cohomology_map(«dualQuotient», «dualC», n + 1), " +
			"                coconnecting_hom(«dualQuotient», " +
			"                    «dualMiddle», " +
			"                    «dualProjection», " +
			"                    «dualInclusion», " +
			"                    n, " +
			"                    cohomology_map(«dualSub», «dualA», n, s))))) ∧ " +
			"(∀n:num. " +
			"    exact_at(coboundaries(«dualY», n + 1), " +
			"        cohomology(«dualX», n), " +
			"        cohomology(«dualZ», n + 1), " +
			"        λs:set(E → C). " +
			"            inverse_on(cohomology(«dualZ», n + 1), " +
			"                cohomology_map(«dualQuotient», «dualC», n + 1), " +
			"                coconnecting_hom(«dualQuotient», " +
			"                    «dualMiddle», " +
			"                    «dualProjection», " +
			"                    «dualInclusion», " +
			"                    n, " +
			"                    cohomology_map(«dualSub», «dualA», n, s))), " +
			"        cohomology_map(«dualY», «dualPsi», n + 1)))",
		Abbrev: Abbrev{
			{Name: "dualSub", Text: "free_dual_complex(R, N, P', S₁, e₁, r₁)"},
			{Name: "dualMiddle", Text: "free_dual_complex(R, N, P, S₂, e₂, r₂)"},
			{Name: "dualQuotient", Text: "free_dual_complex(R, N, P'', S₃, e₃, r₃)"},
			{Name: "dualX", Text: "free_dual_complex(R, N, X, S₄, e₄, r₄)"},
			{Name: "dualY", Text: "free_dual_complex(R, N, Y, S₅, e₅, r₅)"},
			{Name: "dualZ", Text: "free_dual_complex(R, N, Z, S₆, e₆, r₆)"},
			{Name: "dualPhi", Text: "free_dual_map(R, N, S₄, e₄, r₅, φ)"},
			{Name: "dualPsi", Text: "free_dual_map(R, N, S₅, e₅, r₆, ψ)"},
			{Name: "dualA", Text: "free_dual_map(R, N, S₁, e₁, r₄, a)"},
			{Name: "dualC", Text: "free_dual_map(R, N, S₃, e₃, r₆, c)"},
			{Name: "dualProjection", Text: "free_dual_map(R, N, S₂, e₂, r₃, p)"},
			{Name: "dualInclusion", Text: "free_dual_map(R, N, S₁, e₁, r₂, i)"},
		},
	},
		"Dualize the top row: FreeDualSplitShortExact makes 0 → P''^∨ → P^∨ → P'^∨ → 0 short exact, "+
			"with its long exact sequence (CoLongExactMiddle, CoLongExactQuotient, CoLongExactSub, "+
			"CoconnectingHom). The vertical maps (c^∨)_*: H(Z^∨) → H(P''^∨), (b^∨)_*: H(P^∨) → H(Y^∨), "+
			"(a^∨)_*: H(X^∨) → H(P'^∨) are isomorphisms (FreeDualQuasiIsomorphism). The squares commute on "+
			"cohomology: c ∘ p ∘ b ≃ ψ transposes to b^∨ p^∨ c^∨ ≃ ψ^∨, and i ≃ b ∘ φ ∘ a to a^∨ φ^∨ b^∨ ≃ "+
			"i^∨ (FreeDualCochainMap, FreeDualMapCompose, FreeDualHomotopy, HomotopicSameCohomologyMap, "+
			"CohomologyMapCompose, CohomologyMapCongruence), so ψ^∨_* = (b^∨)_* p^∨_* (c^∨)_* and φ^∨_* = "+
			"(a^∨)_*⁻¹ i^∨_* (b^∨)_*⁻¹, while δ is by definition (c^∨)_*⁻¹ ∘ δ^top ∘ (a^∨)_*; carry each "+
			"exactness across the isomorphisms (ExactAtIsomorphism, IsomorphismInverse, InverseOnLeft). "+
			"Degree 0: p^∨_* is one-to-one on H^0 (CoLongExactStart at the dual of the top row), hence so "+
			"is ψ^∨_*, the vertical maps being isomorphisms."),
})}
