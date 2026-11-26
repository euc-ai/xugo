// based.go — based chain complexes: a chain complex with a chosen basis
// in every degree, given as mutually inverse linear maps between the
// free module on a set of generators and the degree's module. The total
// complex of a double complex and the cone of a chain map inherit bases
// from their pieces: the total's generators keep the column p beside a
// generator of the cell (p, n − p), and the cone's generators are the
// target's under one tag and, above degree 0, the shifted source's under
// another.

package free_complex_duality

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/chain_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/resolution"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Based chain complexes
// ---------------------------------------------------------------------------

// BasedChainComplex — `based_chain_complex(R, P, S, e, r)`: P is a chain
// complex and in every degree n the expansion e(n) from the free module on
// the generators S(n) and the coordinates r(n) back into it are linear and
// inverse to each other on the two carriers. e and r are families of
// functions at fixed types, one per degree; nothing asks them to commute
// with the boundaries — the boundary in coordinates is r(n) ∘ P.d(n + 1) ∘
// e(n + 1).
var BasedChainComplex = basedChainComplexThm{family.DefineStructure(registry.DefEntry{
	Name:  "BasedChainComplex",
	Key:   "prop_9132dba6650527bc",
	Const: "based_chain_complex",
	Type: "ring_ops(A) → " +
		"complex_ops(A, B) → " +
		"(num → set(I)) → " +
		"(num → (I → A) → B) → " +
		"(num → B → I → A) → " +
		"bool",
	Subject: "P",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀P:complex_ops(A, B). " +
			"∀S:(num → set(I)). " +
			"∀e:(num → (I → A) → B). " +
			"∀r:(num → B → I → A). " +
			"    based_chain_complex(R, P, S, e, r) ⇔ " +
			"    chain_complex(R, P) ∧ " +
			"    (∀n:num. module_homomorphism(R, free_module_record(R, S(n)), complex_module(P, n), e(n))) ∧ " +
			"    (∀n:num. module_homomorphism(R, complex_module(P, n), free_module_record(R, S(n)), r(n))) ∧ " +
			"    (∀n:num. ∀a:(I → A). a ∈ finite_supp(R.zero, R.carrier, S(n)) ⇒ r(n)(e(n)(a)) = a) ∧ " +
			"    (∀n:num. ∀x:B. x ∈ P.terms(n) ⇒ e(n)(r(n)(x)) = x)",
	},
	Reading: "The basis is data, not a property: the same complex is based in many ways, and " +
		"every construction downstream — the dual complex, the transposed maps — reads e and r. The " +
		"two inverse laws hold on the carriers only; off them e and r are arbitrary total functions.",
})}

// BasedComplexChain — a based chain complex is a chain complex.
var BasedComplexChain = basedComplexChainThm{family.Add(registry.ProofEntry{
	Name:  "BasedComplexChain",
	Key:   "prop_e692b373dab10992",
	Build: BasedChainComplex.Axiom("chain_complex(R, P)"),
})}

// BasedExpandHom — the expansion is linear from the free module into the
// degree's module.
var BasedExpandHom = basedExpandHomThm{family.Add(registry.ProofEntry{
	Name: "BasedExpandHom",
	Key:  "prop_10480e8ceedec5c5",
	Build: BasedChainComplex.Axiom(
		"∀n:num. module_homomorphism(R, free_module_record(R, S(n)), complex_module(P, n), e(n))"),
})}

// BasedCoordinatesHom — the coordinates are linear from the degree's
// module into the free module.
var BasedCoordinatesHom = basedCoordinatesHomThm{family.Add(registry.ProofEntry{
	Name: "BasedCoordinatesHom",
	Key:  "prop_5452f333de0753fe",
	Build: BasedChainComplex.Axiom(
		"∀n:num. module_homomorphism(R, complex_module(P, n), free_module_record(R, S(n)), r(n))"),
})}

// BasedCoordinatesExpand — the coordinates of an expansion are the
// coefficients expanded.
var BasedCoordinatesExpand = basedCoordinatesExpandThm{family.Add(registry.ProofEntry{
	Name: "BasedCoordinatesExpand",
	Key:  "prop_9afc54359bfc1e79",
	Build: BasedChainComplex.Axiom(Statement{
		Binders: "∀n:num. ∀a:(I → A).",
		Hypotheses: []string{
			"a ∈ finite_supp(R.zero, R.carrier, S(n))",
		},
		Conclusion: "r(n)(e(n)(a)) = a",
	}),
})}

// BasedExpandCoordinates — every member of a degree is the expansion of
// its coordinates.
var BasedExpandCoordinates = basedExpandCoordinatesThm{family.Add(registry.ProofEntry{
	Name: "BasedExpandCoordinates",
	Key:  "prop_7329de94e374c2d0",
	Build: BasedChainComplex.Axiom(Statement{
		Binders: "∀n:num. ∀x:B.",
		Hypotheses: []string{
			"x ∈ P.terms(n)",
		},
		Conclusion: "e(n)(r(n)(x)) = x",
	}),
})}

// FreeComplexBased — a free complex is based by the identity.
var FreeComplexBased = freeComplexBasedThm{family.Add(registry.ProofEntry{
	Name: "FreeComplexBased",
	Key:  "prop_ea661c1618be5bf",
	Reading: "The free complex of every free resolution is based this way; " +
		"the cotangent complex with coefficients in its base ring is another.",
	Deps: []registry.EntryLike{
		BasedChainComplex,
		resolution.FreeComplexOf,
		chain_complex.ComplexModuleDef,
		chain_complex.ComplexModules,
		free_module.FreeModuleRecordDef,
		module_homomorphism.HomIdentity,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀S:(num → set(I)). ∀d:(num → (I → A) → I → A).",
		Hypotheses: []string{
			"chain_complex(R, free_complex(R, S, d))",
		},
		Conclusion: "based_chain_complex(R, " +
			"    free_complex(R, S, d), " +
			"    S, " +
			"    λn:num. λa:(I → A). a, " +
			"    λn:num. λa:(I → A). a)",
	},
		"The degree module of free_complex(R, S, d) is free_module_record(R, S(n)) field by "+
			"field (FreeComplexOf, ComplexModuleDef, FreeModuleRecordDef), so the identity is linear "+
			"both ways (HomIdentity, the term a module by ComplexModules) and inverse to itself."),
})}

// ---------------------------------------------------------------------------
// The basis of a total complex
// ---------------------------------------------------------------------------

// DoubleTotalBasisDef — `double_total_basis(S, n)`: the generators of
// degree n of the total complex of a double complex whose cell (p, q) has
// the generators S(p, q): the pairs (p, s) with p ≤ n and s a generator of
// the cell (p, n − p).
var DoubleTotalBasisDef = doubleTotalBasisDefThm{family.Define(registry.DefEntry{
	Name:  "DoubleTotalBasisDef",
	Key:   "prop_a0914a3e1ad184dc",
	Const: "double_total_basis",
	Type:  "(num → num → set(I)) → num → set(prod(num, I))",
	Equations: []string{
		"∀S:(num → num → set(I)). ∀n:num. " +
			"    double_total_basis(S, n) = {z:prod(num, I) | fst(z) ≤ n ∧ snd(z) ∈ S(fst(z), n - fst(z))}",
	},
	Reading: "The column p is kept beside the generator: two cells of one " +
		"diagonal may share generators, and the pair keeps their summands apart. A " +
		"diagonal has n + 1 cells, so the basis is finite over each finite slice " +
		"and a finitely supported function on it has finitely many nonzero slices.",
})}

// DoubleTotalExpandDef — `double_total_expand(V, e, n, a, p)`: the
// expansion of a coefficient function a on the total generators of degree
// n, the cell (p, n − p)'s expansion of the slice s ↦ a((p, s)) at
// coordinate p ≤ n and V.zero past n.
var DoubleTotalExpandDef = doubleTotalExpandDefThm{family.Define(registry.DefEntry{
	Name:  "DoubleTotalExpandDef",
	Key:   "prop_9ba4ab62731def0a",
	Const: "double_total_expand",
	Type:  "module_ops(A, B) → (num → num → (I → A) → B) → num → (prod(num, I) → A) → num → B",
	Equations: []string{
		"∀V:module_ops(A, B). ∀e:(num → num → (I → A) → B). ∀n:num. ∀a:(prod(num, I) → A). ∀p:num. " +
			"    double_total_expand(V, e, n, a, p) = COND(p ≤ n, e(p, n - p, λx:I. a((p, x))), V.zero)",
	},
	Reading: "With every cell's expansion the identity it reads a " +
		"function on pairs as the function of p whose value is the slice at " +
		"p: the total's coordinate p of degree n holds the cell (p, n − p).",
})}

// DoubleTotalCoordinatesDef — `double_total_coordinates(R, r, n, u, z)`:
// the coordinates of a member u of the total of degree n, at the pair
// z = (p, s) the cell (p, n − p)'s coordinate of u(p) at s, and R.zero at
// a column past n.
var DoubleTotalCoordinatesDef = doubleTotalCoordinatesDefThm{family.Define(registry.DefEntry{
	Name:  "DoubleTotalCoordinatesDef",
	Key:   "prop_f3e270a4e554502b",
	Const: "double_total_coordinates",
	Type:  "ring_ops(A) → (num → num → B → I → A) → num → (num → B) → prod(num, I) → A",
	Equations: []string{
		"∀R:ring_ops(A). ∀r:(num → num → B → I → A). ∀n:num. ∀u:(num → B). ∀z:prod(num, I). " +
			"    double_total_coordinates(R, r, n, u, z) = " +
			"    COND(fst(z) ≤ n, r(fst(z), n - fst(z), u(fst(z)), snd(z)), R.zero)",
	},
	Reading: "Finite support comes from the diagonal: only the n + 1 columns p " +
		"≤ n contribute, each through the finitely supported coordinates of one cell.",
})}

// DoubleTotalBased — a double complex whose cells are based has a based
// total, the generators of degree n the pairs (p, s) of the diagonal.
var DoubleTotalBased = doubleTotalBasedThm{family.Add(registry.ProofEntry{
	Name: "DoubleTotalBased",
	Key:  "prop_42ff9750d2c2255d",
	Reading: "The four facts a based total needs are all here — the maps land " +
		"in the right carriers, the coordinates are finitely supported (a " +
		"diagonal has finitely many cells), both maps are linear, both composites " +
		"are identities. Nothing of the boundary is read beyond DoubleTotalComplex.",
	Deps: []registry.EntryLike{
		BasedChainComplex,
		DoubleTotalBasisDef,
		DoubleTotalExpandDef,
		DoubleTotalCoordinatesDef,
		chain_complex.DoubleComplex,
		chain_complex.DoubleTotalComplex,
		chain_complex.DoubleTotalDef,
		chain_complex.DoubleTotalTermsDef,
		chain_complex.ComplexModuleDef,
		free_module.FreeModuleRecordDef,
		function_module.FiniteSuppDef,
		function_module.FiniteSupportDef,
		module_record.RestrictModuleDef,
		module_homomorphism.ModuleHomomorphismDef,
		finite_set.FiniteImageInjGeneral,
		finite_set.FiniteImage,
		finite_set.FiniteUnion,
		pairs.PairEq,
		pairs.PairSurjective,
	},
	Build: family.Card(chain_complex.DoubleComplex.Statement(Statement{
		Binders: "∀S:(num → num → set(I)). ∀e:(num → num → (I → A) → B). ∀r:(num → num → B → I → A).",
		Hypotheses: []string{
			"∀p q:num. " +
				"    module_homomorphism(R, free_module_record(R, S(p, q)), restrict_module(V, D(p, q)), e(p, q))",
			"∀p q:num. " +
				"    module_homomorphism(R, restrict_module(V, D(p, q)), free_module_record(R, S(p, q)), r(p, q))",
			"∀p q:num. ∀a:(I → A). a ∈ finite_supp(R.zero, R.carrier, S(p, q)) ⇒ r(p, q, e(p, q, a)) = a",
			"∀p q:num. ∀x:B. x ∈ D(p, q) ⇒ e(p, q, r(p, q, x)) = x",
		},
		Conclusion: "based_chain_complex(R, " +
			"    double_total(V, D, h, v, alternating_sign), " +
			"    double_total_basis(S), " +
			"    double_total_expand(V, e), " +
			"    double_total_coordinates(R, r))",
	}),
		"The total is a complex (DoubleTotalComplex). Expansion: for a finitely supported a on "+
			"double_total_basis(S, n), the slice x ↦ a((p, x)) is finitely supported (pairing with "+
			"p is one-to-one, FiniteImageInjGeneral) and zero off S(p, n − p), so e(p, n − p) puts "+
			"it in D(p, n − p), and past n the value is V.zero: the result lies in "+
			"double_total_terms(V, D, n). Coordinates: u(p) ∈ D(p, n − p) has finitely supported "+
			"coordinates on S(p, n − p), and only the n + 1 columns p ≤ n contribute, so the "+
			"coordinates are finitely supported on the basis. Both maps are linear coordinatewise, "+
			"the total's operations being pointwise in p (DoubleTotalDef); the composites are the "+
			"identity slice by slice (the cells' inverse laws), with V.zero past n on both sides."),
})}

// ---------------------------------------------------------------------------
// The basis of a cone
// ---------------------------------------------------------------------------

// chainConeBasisDef — `chain_cone_basis(S, S', ι, κ, n)`: the generators of
// degree n of the cone of a map from a complex with generators S to one
// with generators S', the target's generators of degree n under the tag κ
// and, above degree 0, the source's of degree n − 1 under the tag ι.
var chainConeBasisDef = chainConeBasisDefThm{family.Define(registry.DefEntry{
	Name:  "chainConeBasisDef",
	Key:   "prop_175ccd47c14de655",
	Const: "chain_cone_basis",
	Type:  "(num → set(I)) → (num → set(E)) → (I → F) → (E → F) → num → set(F)",
	Equations: []string{
		"∀S:(num → set(I)). ∀S':(num → set(E)). ∀ι:(I → F). ∀κ:(E → F). ∀n:num. " +
			"    chain_cone_basis(S, S', ι, κ, n) = image(κ, S'(n)) ∪ COND(n = 0, ∅⟨A:F⟩, image(ι, S(n - 1)))",
	},
	Reading: "The branch at n = 0 is load-bearing: n − 1 truncates to 0 on num, and " +
		"without it degree 0 would take the source's generators of degree 0, where the " +
		"cone's first component is P.zero alone. The two parts are disjoint and each a " +
		"copy of its generators exactly when the tags are one-to-one with disjoint images.",
})}

// chainConeExpandDef — `chain_cone_expand(P, e, e', ι, κ, n, a)`: the
// expansion of a coefficient function a on the cone's generators of degree
// n, the pair of the source's expansion of a ∘ ι in degree n − 1 —
// P.zero in degree 0 — and the target's expansion of a ∘ κ in degree n.
var chainConeExpandDef = chainConeExpandDefThm{family.Define(registry.DefEntry{
	Name:  "chainConeExpandDef",
	Key:   "prop_4a052a9431fd61c8",
	Const: "chain_cone_expand",
	Type: "complex_ops(A, B) → " +
		"(num → (I → A) → B) → " +
		"(num → (E → A) → C) → " +
		"(I → F) → " +
		"(E → F) → " +
		"num → " +
		"(F → A) → " +
		"prod(B, C)",
	Equations: []string{
		"∀P:complex_ops(A, B). " +
			"∀e:(num → (I → A) → B). " +
			"∀e':(num → (E → A) → C). " +
			"∀ι:(I → F). " +
			"∀κ:(E → F). " +
			"∀n:num. " +
			"∀a:(F → A). " +
			"    chain_cone_expand(P, e, e', ι, κ, n, a) = " +
			"    (COND(n = 0, P.zero, e(n - 1, λx:I. a(ι(x)))), e'(n, λy:E. a(κ(y))))",
	},
	Reading: "The first component sits in chain_shift(P).terms(n), which is {P.zero} " +
		"at n = 0; the order of the pair is chain_cone's, the shifted source first.",
})}

// chainConeCoordinatesDef — `chain_cone_coordinates(R, r, r', ι, κ, n, z, j)`:
// the coordinates of a pair z of the cone in degree n at a generator j, the
// target's coordinate of snd(z) in degree n at a κ-tagged j, the source's
// coordinate of fst(z) in degree n − 1 at an ι-tagged j above degree 0,
// and R.zero elsewhere.
var chainConeCoordinatesDef = chainConeCoordinatesDefThm{family.Define(registry.DefEntry{
	Name:  "chainConeCoordinatesDef",
	Key:   "prop_6b80eaad0c1832b7",
	Const: "chain_cone_coordinates",
	Type: "ring_ops(A) → " +
		"(num → B → I → A) → " +
		"(num → C → E → A) → " +
		"(I → F) → " +
		"(E → F) → " +
		"num → " +
		"prod(B, C) → " +
		"F → " +
		"A",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀r:(num → B → I → A). " +
			"∀r':(num → C → E → A). " +
			"∀ι:(I → F). " +
			"∀κ:(E → F). " +
			"∀n:num. " +
			"∀z:prod(B, C). " +
			"∀j:F. " +
			"    chain_cone_coordinates(R, r, r', ι, κ, n, z, j) = " +
			"    COND(j ∈ image(κ, 𝕌⟨A:E⟩), " +
			"        r'(n, snd(z), inverse_on(𝕌⟨A:E⟩, κ, j)), " +
			"        COND(¬(n = 0) ∧ j ∈ image(ι, 𝕌⟨A:I⟩), " +
			"            r(n - 1, fst(z), inverse_on(𝕌⟨A:I⟩, ι, j)), " +
			"            R.zero))",
	},
	Reading: "A tagged generator is untagged by the preimage inverse_on chooses, the " +
		"generator itself when the tag is one-to-one. The κ-test comes first; with disjoint images " +
		"the order of the two tests does not matter. In degree 0 the first component is not read.",
})}

// ChainConeBased — the cone of a chain map between based complexes is
// based, the target's generators under one tag and, above degree 0, the
// shifted source's under another.
var ChainConeBased = chainConeBasedThm{family.Add(registry.ProofEntry{
	Name: "ChainConeBased",
	Key:  "prop_60be58070000bd6c",
	Reading: "The branch at degree 0 in the basis, the expansion and " +
		"the coordinates is load-bearing: n − 1 truncates to 0 on num, and " +
		"degree 0 of the cone holds P.zero alone in its first component.",
	Deps: []registry.EntryLike{
		BasedChainComplex,
		BasedComplexChain,
		BasedExpandHom,
		BasedCoordinatesHom,
		BasedCoordinatesExpand,
		BasedExpandCoordinates,
		chainConeBasisDef,
		chainConeExpandDef,
		chainConeCoordinatesDef,
		chain_complex.ConeChainComplex,
		chain_complex.ChainConeDef,
		chain_complex.ChainShiftDef,
		chain_complex.ComplexModuleDef,
		free_module.FreeModuleRecordDef,
		function_module.FiniteSuppDef,
		function_module.FiniteSupportDef,
		module_homomorphism.ModuleHomomorphismDef,
		functions.InverseOnLeft,
		set_basic.InImage,
		set_basic.InUnion,
		set_product.InCross,
		finite_set.FiniteImageInjGeneral,
		finite_set.FiniteImage,
		finite_set.FiniteUnion,
		pairs.Fst,
		pairs.Snd,
		pairs.PairSurjective,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀P:complex_ops(A, B). " +
			"∀S:(num → set(I)). " +
			"∀e:(num → (I → A) → B). " +
			"∀r:(num → B → I → A). " +
			"∀Q:complex_ops(A, C). " +
			"∀S':(num → set(E)). " +
			"∀e':(num → (E → A) → C). " +
			"∀r':(num → C → E → A). " +
			"∀f:(num → B → C). " +
			"∀ι:(I → F). " +
			"∀κ:(E → F).",
		Hypotheses: []string{
			"based_chain_complex(R, P, S, e, r)",
			"based_chain_complex(R, Q, S', e', r')",
			"chain_map(R, P, Q, f)",
			"∀x y:I. ι(x) = ι(y) ⇒ x = y",
			"∀x y:E. κ(x) = κ(y) ⇒ x = y",
			"∀x:I. ∀y:E. ¬(ι(x) = κ(y))",
		},
		Conclusion: "based_chain_complex(R, " +
			"    chain_cone(P, Q, f), " +
			"    chain_cone_basis(S, S', ι, κ), " +
			"    chain_cone_expand(P, e, e', ι, κ), " +
			"    chain_cone_coordinates(R, r, r', ι, κ))",
	},
		"The cone is a complex (ConeChainComplex) whose degree module is the product of chain_shift(P)'s "+
			"and Q's, componentwise (ChainConeDef, ChainShiftDef). For finitely supported a on the cone's "+
			"basis, a ∘ κ is finitely supported on S'(n), and above degree 0, a ∘ ι on S(n − 1) — the tags "+
			"one-to-one with disjoint images, so a tagged generator of the basis untags into the right set; "+
			"in degree 0 the first component is P.zero, all of chain_shift(P)'s degree 0. The coordinates "+
			"read r'(n) at κ-tags and r(n − 1) at ι-tags through inverse_on, which undoes a one-to-one tag "+
			"(InverseOnLeft), R.zero elsewhere — finitely supported on the basis. Both maps are linear "+
			"componentwise, and the composites are the identity part by part (the two bases' inverse laws)."),
})}
