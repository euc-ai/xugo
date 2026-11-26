// cone.go — the shift and the mapping cone of complexes, and the three
// ways two complexes are compared: a chain isomorphism, a
// quasi-isomorphism and a chain homotopy equivalence.
//
// The cone of a chain map f: P → Q sits at the pair type: degree n holds
// the pairs (x, y) with x in the shifted P, P.terms(n − 1), and y in
// Q.terms(n), and the boundary is (x, y) ↦ (−P.d(x), f(x) + Q.d(y)). It
// sits in the short exact sequence Q → chain_cone(P, Q, f) →
// chain_shift(P), whose connecting map is f on homology, so the cone is
// exact exactly when f is a quasi-isomorphism.

package chain_complex

import (
	"github.com/euc-ai/xugo/ext/on"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
)

// ---------------------------------------------------------------------------
// The shift and the cone
// ---------------------------------------------------------------------------

// ChainShiftDef — `chain_shift(P)`: P moved up one degree with its
// boundary negated. Degree 0 holds P.zero alone and degree n + 1 holds
// P.terms(n); the boundary out of degree n + 2 is −P.d(n + 1), and the
// boundary out of degree 1, into the zero degree, is zero.
var ChainShiftDef = chainShiftDefThm{family.Define(registry.DefEntry{
	Name: "ChainShiftDef", Const: "chain_shift",
	Key:  "prop_9605b04f6641dbf7",
	Type: "complex_ops(A, B) → complex_ops(A, B)",
	Equations: []string{
		"∀P:complex_ops(A, B). " +
			"    chain_shift(P) = " +
			"    pack_complex(P.add, " +
			"        P.zero, " +
			"        P.neg, " +
			"        P.smul, " +
			"        (λn:num. COND(n = 0, {P.zero}, P.terms(n - 1))), " +
			"        (λn:num. λx:B. COND(n ≤ 1, P.zero, P.neg(P.d(n - 1)(x)))))",
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

// ChainConeDef — `chain_cone(P, Q, f)`: the mapping cone of f: P → Q at
// the pair type. Degree n holds the pairs (x, y) with x in
// chain_shift(P).terms(n) and y in Q.terms(n), added, negated and scaled
// componentwise. The boundary out of degree n + 1 sends (x, y), x in
// P.terms(n), to (chain_shift(P).d(n + 1)(x), f(n)(x) + Q.d(n + 1)(y)):
// to (−P.d(n)(x), f(n)(x) + Q.d(n + 1)(y)) above degree 1, and to
// (P.zero, f(0)(x) + Q.d(1)(y)) out of degree 1. The sign convention is
// this one throughout: the shifted boundary is negated and f is added.
var ChainConeDef = chainConeDefThm{family.Define(registry.DefEntry{
	Name: "ChainConeDef", Const: "chain_cone",
	Key:  "prop_d0e9e588127bdc29",
	Type: "complex_ops(A, B) → complex_ops(A, C) → (num → B → C) → complex_ops(A, prod(B, C))",
	Equations: []string{
		"∀P:complex_ops(A, B). ∀Q:complex_ops(A, C). ∀f:(num → B → C). " +
			"    chain_cone(P, Q, f) = " +
			"    pack_complex( " +
			"        (λz:prod(B, C). λw:prod(B, C). (P.add(fst(z), fst(w)), Q.add(snd(z), snd(w)))), " +
			"        (P.zero, Q.zero), " +
			"        (λz:prod(B, C). (P.neg(fst(z)), Q.neg(snd(z)))), " +
			"        (λc:A. λz:prod(B, C). (P.smul(c, fst(z)), Q.smul(c, snd(z)))), " +
			"        (λn:num. set_cross(chain_shift(P).terms(n), Q.terms(n))), " +
			"        (λn:num. λz:prod(B, C). " +
			"            (chain_shift(P).d(n)(fst(z)), Q.add(f(n - 1)(fst(z)), Q.d(n)(snd(z))))))",
	},
	Deps: []registry.EntryLike{
		ChainShiftDef,
		ComplexAddDef,
		ComplexZeroDef,
		ComplexNegDef,
		ComplexSmulDef,
		ComplexTermsDef,
		ComplexDifferentialDef,
	},
})}

// ---------------------------------------------------------------------------
// Comparing two complexes
// ---------------------------------------------------------------------------

// QuasiIsomorphismDef — `quasi_isomorphism(R, P, Q, f)`: f is a chain map
// inducing an isomorphism of the homology modules in every degree.
var QuasiIsomorphismDef = quasiIsomorphismDefThm{family.Define(registry.DefEntry{
	Name: "QuasiIsomorphismDef", Const: "quasi_isomorphism",
	Key:  "prop_2483e4eb4238cea",
	Type: "ring_ops(A) → complex_ops(A, B) → complex_ops(A, C) → (num → B → C) → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀P:complex_ops(A, B). ∀Q:complex_ops(A, C). ∀f:(num → B → C). " +
			"    quasi_isomorphism(R, P, Q, f) ⇔ " +
			"    chain_map(R, P, Q, f) ∧ " +
			"    (∀n:num. " +
			"        module_isomorphism(R, " +
			"            homology_module(P, n), " +
			"            homology_module(Q, n), " +
			"            homology_map(Q, f, n)))",
	},
	Deps: []registry.EntryLike{ChainMapDef, HomologyModuleDef, HomologyMapDef},
})}

// ChainIsomorphismDef — `chain_isomorphism(R, P, Q, f)`: f is a chain map
// that is an isomorphism of the degree modules in every degree.
var ChainIsomorphismDef = chainIsomorphismDefThm{family.Define(registry.DefEntry{
	Name: "ChainIsomorphismDef", Const: "chain_isomorphism",
	Key:  "prop_16a28629b61e2749",
	Type: "ring_ops(A) → complex_ops(A, B) → complex_ops(A, C) → (num → B → C) → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀P:complex_ops(A, B). ∀Q:complex_ops(A, C). ∀f:(num → B → C). " +
			"    chain_isomorphism(R, P, Q, f) ⇔ " +
			"    chain_map(R, P, Q, f) ∧ " +
			"    (∀n:num. module_isomorphism(R, complex_module(P, n), complex_module(Q, n), f(n)))",
	},
	Deps: []registry.EntryLike{ChainMapDef, ComplexModuleDef},
})}

// ChainHomotopyEquivalenceDef — `chain_homotopy_equivalence(R, P, Q, f,
// g)`: f: P → Q and g: Q → P are chain maps whose two composites, taken
// degree by degree, are each chain homotopic to the identity. The inverse
// g is part of the data; "f is an equivalence" is ∃g, and "P and Q are
// chain homotopy equivalent" is ∃f g.
var ChainHomotopyEquivalenceDef = chainHomotopyEquivalenceDefThm{family.Define(registry.DefEntry{
	Name: "ChainHomotopyEquivalenceDef", Const: "chain_homotopy_equivalence",
	Key: "prop_cb053a2a476eabcc",
	Type: "ring_ops(A) → " +
		"complex_ops(A, B) → " +
		"complex_ops(A, C) → " +
		"(num → B → C) → " +
		"(num → C → B) → " +
		"bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀P:complex_ops(A, B). ∀Q:complex_ops(A, C). ∀f:(num → B → C). ∀g:(num → C → B). " +
			"    chain_homotopy_equivalence(R, P, Q, f, g) ⇔ " +
			"    chain_map(R, P, Q, f) ∧ " +
			"    chain_map(R, Q, P, g) ∧ " +
			"    (∃k:(num → B → B). " +
			"        chain_homotopy(R, P, P, (λn:num. λx:B. g(n)(f(n)(x))), (λn:num. λx:B. x), k)) ∧ " +
			"    (∃l:(num → C → C). " +
			"        chain_homotopy(R, Q, Q, (λn:num. λy:C. f(n)(g(n)(y))), (λn:num. λy:C. y), l))",
	},
	Deps: []registry.EntryLike{ChainMapDef, ChainHomotopyDef},
	Reading: "The homotopies are existential and the inverse is an argument, so the " +
		"relation is symmetric by swapping f with g and the two complexes. No hypothesis " +
		"makes P or Q a complex: the laws that read homology take chain_complex beside it.",
})}

// ---------------------------------------------------------------------------
// The shift and the cone are complexes
// ---------------------------------------------------------------------------

// ShiftChainComplex — the shift of a complex is a complex.
var ShiftChainComplex = shiftChainComplexThm{family.Add(registry.ProofEntry{
	Name: "ShiftChainComplex",
	Key:  "prop_6edb5269eb661e4d",
	Reading: "Degree 0 of the shift is {P.zero} and the boundary out of degree 1 " +
		"is zero, so H_0 of the shift is trivial and H_{n+1} of the shift is H_n(P).",
	Deps: []registry.EntryLike{
		ChainShiftDef,
		ChainComplex,
		ComplexModules,
		ComplexBoundaryHom,
		ComplexBoundaryTwice,
		submodule.ZeroSubmodule,
		submodule.SubmoduleModuleOn,
		module_homomorphism.HomNeg,
		module_homomorphism.HomZero,
	},
	Build: family.Card(ChainComplex.Statement("chain_complex(R, chain_shift(P))"),
		"Degree 0 is {P.zero}, a module as the zero submodule of P.terms(0) (ZeroSubmodule, "+
			"SubmoduleModuleOn); above it the degrees are P's. Out of degree n + 2 the boundary is −P.d(n "+
			"+ 1), a homomorphism, and out of degree 1 the zero map; two boundaries in a row are P.d(n + "+
			"1)(P.d(n + 2)(x)) = 0 with the two negations cancelled by HomNeg, or land in the zero degree."),
})}

// ConeChainComplex — the cone of a chain map between complexes is a
// complex.
var ConeChainComplex = coneChainComplexThm{family.Add(registry.ProofEntry{
	Name: "ConeChainComplex",
	Key:  "prop_63bae23e25e4a15",
	Reading: "The chain-map hypothesis is what cancels the mixed term " +
		"−f(P.d(x)) + Q.d(f(x)) of the boundary twice, in every degree.",
	Deps: []registry.EntryLike{
		ChainConeDef,
		ChainShiftDef,
		ShiftChainComplex,
		ChainComplex,
		ChainMapDef,
		ChainMapHom,
		ChainMapSquare,
		ComplexModules,
		ComplexBoundaryHom,
		ComplexBoundaryTwice,
		module_homomorphism.HomAdd,
		module_homomorphism.HomNeg,
		pairs.Fst,
		pairs.Snd,
		set_basic.Extension,
	},
	Build: family.Card(ChainComplex.Statement(Statement{
		Binders: "∀Q:complex_ops(A, C). ∀f:(num → B → C).",
		Hypotheses: []string{
			"chain_complex(R, Q)",
			"chain_map(R, P, Q, f)",
		},
		Conclusion: "chain_complex(R, chain_cone(P, Q, f))",
	}),
		"Each degree is the product of a degree of chain_shift(P) (ShiftChainComplex) and one "+
			"of Q, a module componentwise, and the boundary is a homomorphism because each "+
			"component is. Twice, (x, y) goes to (P.d(P.d(x)), −f(P.d(x)) + Q.d(f(x)) + "+
			"Q.d(Q.d(y))): the first component and Q.d(Q.d(y)) vanish (ComplexBoundaryTwice, or the "+
			"zero degree), and the chain-map square f ∘ P.d = Q.d ∘ f cancels the rest (Weibel, An "+
			"Introduction to Homological Algebra, 1.5.1, with f added instead of subtracted)."),
})}

// ConeShortExact — the cone of f: P → Q sits in a short exact sequence
// Q → chain_cone(P, Q, f) → chain_shift(P), y ↦ (P.zero, y) and
// (x, y) ↦ x.
var ConeShortExact = coneShortExactThm{family.Add(registry.ProofEntry{
	Name: "ConeShortExact",
	Key:  "prop_2cdf91b6f3f64fdd",
	Reading: "With the cone's convention of adding f, the connecting " +
		"map of this sequence into H_n(Q) is +H_n(f), with no sign.",
	Deps: []registry.EntryLike{
		ConeChainComplex,
		ShiftChainComplex,
		ChainConeDef,
		ChainShiftDef,
		ShortExactComplexes,
		ExactComplexesDef,
		ChainMapDef,
		ChainMapHom,
		module_homomorphism.ExactAtDef,
		module_homomorphism.HomZero,
		pairs.PairEq,
		pairs.Fst,
		pairs.Snd,
	},
	Build: family.Card(ChainComplex.Statement(Statement{
		Binders: "∀Q:complex_ops(A, C). ∀f:(num → B → C).",
		Hypotheses: []string{
			"chain_complex(R, Q)",
			"chain_map(R, P, Q, f)",
		},
		Conclusion: "short_exact_complexes(R, " +
			"    Q, " +
			"    chain_cone(P, Q, f), " +
			"    chain_shift(P), " +
			"    λn:num. λy:C. (P.zero, y), " +
			"    λn:num. λz:prod(B, C). fst(z))",
	}),
		"The three complexes are Q, ConeChainComplex and ShiftChainComplex. The inclusion commutes "+
			"with the boundaries because f(n)(P.zero) = Q.zero (HomZero) and the shifted boundary "+
			"keeps P.zero, and the projection does by the first component of the cone's boundary; in "+
			"each degree the inclusion is one-to-one, its image the pairs with first component P.zero, "+
			"which is the projection's kernel, and the projection is onto (pair with Q.zero)."),
})}

// ConeQuasiIffAcyclic — a chain map between complexes is a
// quasi-isomorphism exactly when its cone is exact in every degree.
var ConeQuasiIffAcyclic = coneQuasiIffAcyclicThm{family.Add(registry.ProofEntry{
	Name: "ConeQuasiIffAcyclic",
	Key:  "prop_77580bb1a9693f13",
	Deps: []registry.EntryLike{
		ConeShortExact,
		QuasiIsomorphismDef,
		ConnectingHomCoset,
		LongExactMiddle,
		LongExactQuotient,
		LongExactSub,
		HomologyTrivialIffExact,
		HomologyMapCoset,
		CyclesDef,
		BoundariesDef,
		ChainShiftDef,
		module_homomorphism.ModuleIsomorphismDef,
	},
	Build: family.Card(ChainComplex.Statement(Statement{
		Binders: "∀Q:complex_ops(A, C). ∀f:(num → B → C).",
		Hypotheses: []string{
			"chain_complex(R, Q)",
			"chain_map(R, P, Q, f)",
		},
		Conclusion: "quasi_isomorphism(R, P, Q, f) ⇔ " +
			"∀n:num. cycles(chain_cone(P, Q, f), n) = boundaries(chain_cone(P, Q, f), n)",
	}),
		"Run the long exact sequence of ConeShortExact. The shift has H₀ = 0 and H_{n+1} = "+
			"H_n(P), and its connecting map into H_n(Q) is the map of f: a cycle x of P lifts to (x, "+
			"0), whose boundary is (0, f(n)(x)) (ConnectingHomCoset). So the cone is exact at 0 "+
			"exactly when H₀(f) is onto, and at n + 1 exactly when H_{n+1}(f) is onto and H_n(f) "+
			"one-to-one (LongExactSub, LongExactMiddle, LongExactQuotient, HomologyTrivialIffExact); "+
			"every degree together is every H_n(f) bijective (Weibel 1.5.4)."),
	Reading: "The cone's exactness is read in every degree, degree 0 included: there it says every " +
		"(P.zero, y) with y in Q.terms(0) is a boundary, which is H₀(f) onto. Exactness at n + 1 alone " +
		"gives H_{n+1}(f) onto and H_n(f) one-to-one, so the equivalence holds for all degrees at once " +
		"and not degree by degree; H_0(f) one-to-one comes from exactness at degree 1, where the shift's " +
		"boundary out of degree 1 is zero. f is assumed a chain map, which quasi_isomorphism also asks.",
})}

// DegreewiseSplitThirdTermCone — in a short exact sequence of complexes
// with a linear section of the projection in each degree, the cone of the
// inclusion maps to the quotient by (x, y) ↦ p(y), a quasi-isomorphism.
var DegreewiseSplitThirdTermCone = degreewiseSplitThirdTermConeThm{family.Add(registry.ProofEntry{
	Name: "DegreewiseSplitThirdTermCone",
	Key:  "prop_f542df41caab4969",
	Deps: []registry.EntryLike{
		ShortExactComplexes,
		ConeChainComplex,
		ConeQuasiIffAcyclic,
		ConeShortExact,
		ChainConeDef,
		QuasiIsomorphismDef,
		ChainMapDef,
		ShortExactDegreewise,
		LongExactMiddle,
		LongExactQuotient,
		LongExactSub,
		HomologyTrivialIffExact,
		module_homomorphism.ExactComposeZero,
	},
	Build: family.Card(ShortExactComplexes.Statement(Statement{
		Hypotheses: []string{
			"∀n:num. ∃σ:(D → C). " +
				"    module_homomorphism(R, complex_module(P'', n), complex_module(P, n), σ) ∧ " +
				"    (∀z:D. z ∈ P''.terms(n) ⇒ p(n)(σ(z)) = z)",
		},
		Conclusion: "quasi_isomorphism(R, chain_cone(P', P, i), P'', λn:num. λz:prod(B, C). p(n)(snd(z)))",
	}),
		"The map is a chain map: the cone's boundary (−P'.d(x), i(x) + P.d(y)) goes to "+
			"p(i(x)) + p(P.d(y)) = P''.d(p(y)), p ∘ i being zero (ExactComposeZero). It is onto "+
			"in each degree, and its kernel, the pairs (x, i(x')), is the cone of the identity "+
			"of P', which is exact; the long exact sequence of that kernel, the cone and P'' "+
			"(LongExactSub, LongExactMiddle, LongExactQuotient) makes the map an isomorphism on "+
			"homology. With the sections the comparison is moreover a chain homotopy equivalence."),
	Reading: "The sections are the hypothesis the sequences that use this law come with, not what " +
		"makes it true: the cone of the inclusion of any short exact sequence maps quasi-isomorphically " +
		"onto the quotient, the kernel of the map being the cone of the identity of P' carried in along " +
		"i, exact by ConeQuasiIffAcyclic; with the sections the comparison is moreover a chain homotopy " +
		"equivalence. In degree 0 the cone holds the pairs (P'.zero, y), mapped to p(0)(y).",
})}

// ConeContractibleHomotopyInverse — a contraction H of the cone of f
// yields a homotopy inverse of f and both homotopies, read off the
// components of H.
var ConeContractibleHomotopyInverse = coneContractibleHomotopyInverseThm{family.Add(registry.ProofEntry{
	Name: "ConeContractibleHomotopyInverse",
	Key:  "prop_37e9113ddd89f674",
	Reading: "The inverse and both homotopies are in the conclusion because their consumers " +
		"transpose them; a statement that f induces isomorphisms would not do. Degree 0 needs " +
		"no separate case: the cone's degree 0 is {P.zero} × Q.terms(0), and (x, Q.zero) for x " +
		"∈ P.terms(n) lies in degree n + 1. The contraction is an identity on the cone's terms " +
		"only, with no boundary out of degree 0, so it is d(1) ∘ H(0) = id there.",
	Deps: []registry.EntryLike{
		ChainConeDef,
		ChainShiftDef,
		ChainMapDef,
		ChainMapHom,
		ChainMapSquare,
		ChainHomotopyDef,
		ComplexModules,
		ComplexBoundaryHom,
		module_homomorphism.HomCompose,
		module_homomorphism.HomAdd,
		module_homomorphism.HomNeg,
		module_homomorphism.HomZero,
		module.AddGroupOn,
		module.AddComm,
		module.SmulZero,
		module.SmulNeg,
		pairs.Fst,
		pairs.Snd,
		pairs.PairEq,
		set_basic.InSing,
	},
	Build: family.Card(ChainComplex.Statement(Statement{
		Binders: "∀Q:complex_ops(A, C). ∀f:(num → B → C). ∀H:(num → prod(B, C) → prod(B, C)).",
		Hypotheses: []string{
			"chain_complex(R, Q)",
			"chain_map(R, P, Q, f)",
			"∀n:num. " +
				"    module_homomorphism(R, " +
				"        complex_module(chain_cone(P, Q, f), n), " +
				"        complex_module(chain_cone(P, Q, f), n + 1), " +
				"        H(n))",
			"∀z:prod(B, C). z ∈ chain_cone(P, Q, f).terms(0) ⇒ chain_cone(P, Q, f).d(1)(H(0)(z)) = z",
			"∀n:num. ∀z:prod(B, C). " +
				"    z ∈ chain_cone(P, Q, f).terms(n + 1) ⇒ " +
				"    chain_cone(P, Q, f).add(chain_cone(P, Q, f).d(n + 2)(H(n + 1)(z)), " +
				"        H(n)(chain_cone(P, Q, f).d(n + 1)(z))) = " +
				"    z",
		},
		Conclusion: "chain_map(R, Q, P, λn:num. λy:C. fst(H(n)((P.zero, y)))) ∧ " +
			"chain_homotopy(R, " +
			"    P, " +
			"    P, " +
			"    λn:num. λx:B. fst(H(n)((P.zero, f(n)(x)))), " +
			"    λn:num. λx:B. x, " +
			"    λn:num. λx:B. fst(H(n + 1)((x, Q.zero)))) ∧ " +
			"chain_homotopy(R, " +
			"    Q, " +
			"    Q, " +
			"    λn:num. λy:C. f(n)(fst(H(n)((P.zero, y)))), " +
			"    λn:num. λy:C. y, " +
			"    λn:num. λy:C. Q.neg(snd(H(n)((P.zero, y)))))",
	}),
		"write H(n)(P.zero, y) = (g(n)(y), k(n)(y)) and H(n + 1)(x, Q.zero) = (l(n)(x), ·); the cone's "+
			"boundary is (x, y) ↦ (−P.d(x), f(x) + Q.d(y)), with P.zero first out of degree 1 (ChainConeDef, "+
			"ChainShiftDef), and the boundary of (P.zero, y) is (P.zero, Q.d(y)) (HomZero for P.d and f). "+
			"The contraction identity at (P.zero, y) in degree n + 1, first component: −P.d(n + 1)(g(n + "+
			"1)(y)) + g(n)(Q.d(n + 1)(y)) = P.zero, so g is a chain map; second component: f(n + 1)(g(n + "+
			"1)(y)) + Q.d(n + 2)(k(n + 1)(y)) + k(n)(Q.d(n + 1)(y)) = y, so −k is a homotopy f ∘ g ≃ id, and "+
			"in degree 0, d(1)(H(0)(P.zero, y)) = (P.zero, y) gives f(0)(g(0)(y)) + Q.d(1)(k(0)(y)) = y. At "+
			"(x, Q.zero) with x ∈ P.terms(m): for m = 0 the cone's boundary of (x, Q.zero) is (P.zero, "+
			"f(0)(x)) and the first component reads g(0)(f(0)(x)) − x = P.d(1)(l(0)(x)); for m = n + 1 it is "+
			"(−P.d(n + 1)(x), f(n + 1)(x)) = −(P.d(n + 1)(x), Q.zero) + (P.zero, f(n + 1)(x)), and H(n + 1) "+
			"of it (linear) gives g(n + 1)(f(n + 1)(x)) − x = P.d(n + 2)(l(n + 1)(x)) + l(n)(P.d(n + 1)(x)). "+
			"g, k, l are linear as H is, with the pairings y ↦ (P.zero, y), x ↦ (x, Q.zero) and the "+
			"projections (HomCompose, pairs.Fst, pairs.Snd), and land in the right terms: (P.zero, y) lies "+
			"in the cone's degree n, H(n) of it in degree n + 1, which is P.terms(n) × Q.terms(n + 1)"),
})}

// ConeMapQuasiIsomorphism — a square of chain maps whose two vertical
// maps are quasi-isomorphisms induces a quasi-isomorphism of the cones of
// the horizontal maps, (x, y) ↦ (α(x), β(y)).
var ConeMapQuasiIsomorphism = coneMapQuasiIsomorphismThm{family.Add(registry.ProofEntry{
	Name: "ConeMapQuasiIsomorphism",
	Key:  "prop_584b3a238d79b003",
	Reading: "The square β ∘ f = f' ∘ α is what makes the two connecting maps, " +
		"H_n(f) and H_n(f'), commute with α_* and β_*, as the five lemma asks.",
	Deps: []registry.EntryLike{
		ConeShortExact,
		ConeChainComplex,
		ShiftChainComplex,
		ChainConeDef,
		ChainShiftDef,
		QuasiIsomorphismDef,
		ChainMapDef,
		ChainMapHom,
		ChainMapSquare,
		LongExactMiddle,
		LongExactQuotient,
		LongExactSub,
		FiveLemma,
	},
	Build: family.Card(ChainComplex.Statement(Statement{
		Binders: "∀Q:complex_ops(A, C). " +
			"∀P':complex_ops(A, D). " +
			"∀Q':complex_ops(A, E). " +
			"∀f:(num → B → C). " +
			"∀f':(num → D → E). " +
			"∀α:(num → B → D). " +
			"∀β:(num → C → E).",
		Hypotheses: []string{
			"chain_complex(R, Q)",
			"chain_complex(R, P')",
			"chain_complex(R, Q')",
			"chain_map(R, P, Q, f)",
			"chain_map(R, P', Q', f')",
			"quasi_isomorphism(R, P, P', α)",
			"quasi_isomorphism(R, Q, Q', β)",
			"∀n:num. ∀x:B. x ∈ P.terms(n) ⇒ β(n)(f(n)(x)) = f'(n)(α(n)(x))",
		},
		Conclusion: "quasi_isomorphism(R, " +
			"    chain_cone(P, Q, f), " +
			"    chain_cone(P', Q', f'), " +
			"    λn:num. λz:prod(B, C). (α(n - 1)(fst(z)), β(n)(snd(z))))",
	}),
		"The map is a chain map by the squares of α and β and the square β ∘ f = f' ∘ α; at degree 0 it "+
			"sends (P.zero, y) to (P'.zero, β(0)(y)), α(0) keeping zero. It carries the sequence Q → cone(f) "+
			"→ shift(P) of ConeShortExact to the one of f', inducing β and the shift of α, both isomorphisms "+
			"on homology; the five lemma on the two long exact sequences makes the middle one an isomorphism."),
})}

// ---------------------------------------------------------------------------
// Laws of the comparisons
// ---------------------------------------------------------------------------

// QuasiIsomorphismCompose — two quasi-isomorphisms compose, degree by
// degree, to a quasi-isomorphism. The composite is a chain map, and on
// every homology class its map is the map of g after the map of f, a
// composite of two isomorphisms. Homology maps are total maps on sets of
// vectors and the two agree only on the classes, which is why the last
// step reads an isomorphism off the agreement.
var QuasiIsomorphismCompose = quasiIsomorphismComposeThm{family.Add(registry.ProofEntry{
	Name: "QuasiIsomorphismCompose",
	Key:  "prop_1e168fb6312b7346",
	Build: ChainComplex.Law(Statement{
		Binders: "∀Q:complex_ops(A, C). ∀W:complex_ops(A, D). ∀f:(num → B → C). ∀g:(num → C → D).",
		Hypotheses: []string{
			"chain_complex(R, Q)",
			"chain_complex(R, W)",
			"quasi_isomorphism(R, P, Q, f) ∧ quasi_isomorphism(R, Q, W, g)",
		},
		Conclusion: "quasi_isomorphism(R, P, W, λn:num. λx:B. g(n)(f(n)(x)))",
	},
		func(
			a *Argument,
			complexP ChainComplexFact[on.R],
			Q *Expr[ComplexOps[A, C]],
			W *Expr[ComplexOps[A, D]],
			f *Arrow2[Nat, B, C],
			g *Arrow2[Nat, C, D],
			complexQ, complexW, quasi Fact,
		) {
			given := a.Conjuncts(
				quasi,
				"f is a quasi-isomorphism",
				"g is a quasi-isomorphism")
			fParts := a.Conjuncts(
				a.Unfolded(given[0], QuasiIsomorphismDef),
				"f is a chain map",
				"every homology map of f is an isomorphism")
			gParts := a.Conjuncts(
				a.Unfolded(given[1], QuasiIsomorphismDef),
				"g is a chain map",
				"every homology map of g is an isomorphism")
			fChain, fIsos, gChain, gIsos := fParts[0], fParts[1], gParts[0], gParts[1]

			chainMap := a.Have(
				"the composite is a chain map",
				"chain_map(P, W, λm:num. λx:B. g(m)(f(m)(x)))",
				By(ChainMapCompose, fChain, gChain))
			onClasses := a.Have(
				"on a class the composite's map is the map of g after the map of f",
				Statement{
					Binders: "∀n:num. ∀s:set(B).",
					Hypotheses: []string{
						"s ∈ homology(P, n)",
					},
					Conclusion: "homology_map(W, λm:num. λx:B. g(m)(f(m)(x)), n, s) = " +
						"homology_map(W, g, n, homology_map(Q, f, n, s))",
				},
				By(HomologyMapCompose.Read(complexP), complexQ, complexW, fChain, gChain))
			// The carrier of homology_module(P, n) is the cosets themselves, what homology(P, n) unfolds to, so the agreement is read unfolded.
			agree := a.Unfolded(onClasses, HomologyDef)

			iso := a.Have(
				"so each homology map of the composite is an isomorphism",
				"∀n:num. "+
					"    module_isomorphism(R, "+
					"        homology_module(P, n), "+
					"        homology_module(W, n), "+
					"        homology_map(W, λm:num. λx:B. g(m)(f(m)(x)), n))",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					both := b.Have(
						"the map of g after the map of f, a composite of two isomorphisms, is one",
						"module_isomorphism(R, "+
							"    homology_module(P, n), "+
							"    homology_module(W, n), "+
							"    homology_map(W, g, n) ∘ homology_map(Q, f, n))",
						By(module_homomorphism.IsomorphismCompose, fIsos.At(n), gIsos.At(n)))
					// IsomorphismCongruence compares the two maps' applied values, so the composite is read pointwise.
					pointwise := b.Unfolded(both, functions.ComposeApply)
					b.Show(
						"the composite's map agrees with it on every class, so is an isomorphism too",
						By(module_homomorphism.IsomorphismCongruence, pointwise, agree.At(n)))
				}))
			a.Show(
				"so the composite is a quasi-isomorphism",
				By(QuasiIsomorphismDef, chainMap, iso))
		}),
})}

// QuasiIsomorphismAcyclic — complexes joined by a quasi-isomorphism are
// exact in every degree together.
var QuasiIsomorphismAcyclic = quasiIsomorphismAcyclicThm{family.Add(registry.ProofEntry{
	Name: "QuasiIsomorphismAcyclic",
	Key:  "prop_3ad56ae49e38c268",
	Reading: "The equivalence holds degree by degree: P is exact at " +
		"n exactly when Q is, the homology map at n being a bijection.",
	Deps: []registry.EntryLike{
		QuasiIsomorphismDef,
		HomologyTrivialIffExact,
		HomologyModuleDef,
		HomologyDef,
		submodule.QuotientModuleDef,
		module_homomorphism.ModuleIsomorphismDef,
	},
	Build: family.Card(ChainComplex.Statement(Statement{
		Binders: "∀Q:complex_ops(A, C). ∀f:(num → B → C).",
		Hypotheses: []string{
			"chain_complex(R, Q)",
			"quasi_isomorphism(R, P, Q, f)",
		},
		Conclusion: "(∀n:num. cycles(P, n) = boundaries(P, n)) ⇔ ∀n:num. cycles(Q, n) = boundaries(Q, n)",
	}),
		"Each degree's exactness is homology being the one class of the boundaries "+
			"(HomologyTrivialIffExact), and the homology module's carrier is "+
			"homology(P, n); a bijection of the carriers keeps a carrier a single point."),
})}

// ChainIsomorphismQuasiIsomorphism — a chain isomorphism between complexes
// is a quasi-isomorphism.
var ChainIsomorphismQuasiIsomorphism = chainIsomorphismQuasiIsomorphismThm{family.Add(registry.ProofEntry{
	Name: "ChainIsomorphismQuasiIsomorphism",
	Key:  "prop_ea5da1de4016bed6",
	Deps: []registry.EntryLike{
		ChainIsomorphismDef,
		QuasiIsomorphismDef,
		ChainMapDef,
		ChainMapCycles,
		HomologyMapCoset,
		HomologyMapHom,
		module_homomorphism.IsomorphismInverse,
		module_homomorphism.ModuleIsomorphismDef,
	},
	Build: family.Card(ChainComplex.Statement(Statement{
		Binders: "∀Q:complex_ops(A, C). ∀f:(num → B → C).",
		Hypotheses: []string{
			"chain_complex(R, Q)",
			"chain_isomorphism(R, P, Q, f)",
		},
		Conclusion: "quasi_isomorphism(R, P, Q, f)",
	}),
		"The degreewise inverses (IsomorphismInverse) commute with the boundaries, "+
			"the squares read backwards through them, so they form a chain map g. By "+
			"HomologyMapCoset the homology maps of f and g are inverse on classes, so "+
			"each homology map of f is a bijective homomorphism (HomologyMapHom)."),
})}

// ChainHomotopyEquivalenceQuasiIsomorphism — both maps of a chain homotopy
// equivalence between complexes are quasi-isomorphisms. A homotopy from
// g ∘ f to the identity makes the map of g undo the map of f on every class
// of P: the map of a composite is the composite of the maps, and homotopic
// chain maps induce one map. With f ∘ g likewise on Q, the two homology maps
// are inverse bijections of the classes, and each is linear. Read with g
// first the two maps are again an equivalence, so g is the first map of that
// one.
var ChainHomotopyEquivalenceQuasiIsomorphism = chainHomotopyEquivalenceQuasiIsomorphismThm{family.Add(registry.ProofEntry{
	Name: "ChainHomotopyEquivalenceQuasiIsomorphism",
	Key:  "prop_68ec3a2d73512cd3",
	Reading: "The chain_complex hypotheses on P and Q are load-bearing: " +
		"chain_homotopy_equivalence carries none, and homology is read only on a complex.",
	Build: family.Sections(ChainComplex.Statement(Statement{
		Binders: "∀Q:complex_ops(A, C). ∀f:(num → B → C). ∀g:(num → C → B).",
		Hypotheses: []string{
			"chain_complex(R, Q)",
			"chain_homotopy_equivalence(R, P, Q, f, g)",
		},
		Conclusion: "quasi_isomorphism(R, P, Q, f) ∧ quasi_isomorphism(R, Q, P, g)",
	}),
		func(ctx *Script, headline string) *GoalStackNode {
			undoes := ctx.Lemma(ChainComplex.Statement(Statement{
				Binders: "∀Q:complex_ops(A, C). " +
					"∀f:(num → B → C). " +
					"∀g:(num → C → B). " +
					"∀k:(num → B → B). " +
					"∀n:num. " +
					"∀s:set(B).",
				Hypotheses: []string{
					"chain_complex(R, Q)",
					"chain_map(P, Q, f)",
					"chain_map(Q, P, g)",
					"chain_homotopy(P, P, λm:num. λx:B. g(m)(f(m)(x)), λm:num. λx:B. x, k)",
					"s ∈ homology(P, n)",
				},
				Conclusion: "homology_map(P, g, n, homology_map(Q, f, n, s)) = s",
			}),
				func(
					a *Argument,
					complexP ChainComplexFact[on.R],
					_ *Expr[ComplexOps[A, C]],
					_ *Arrow2[Nat, B, C],
					_ *Arrow2[Nat, C, B],
					_ *Arrow2[Nat, B, B],
					_ *Expr[Nat],
					_ *Expr[Set[B]],
					complexQ, fChain, gChain, homotopy, sIn Fact,
				) {
					a.Show(
						"so the map of g after the map of f fixes the class s",
						CalcEq(
							Leg(
								a.TermAs[Set[B]]("homology_map(P, λm:num. λx:B. g(m)(f(m)(x)), n, s)"),
								"the map of g after the map of f is the map of g ∘ f",
								By(HomologyMapCompose.Read(complexP), complexQ, fChain, gChain, sIn)),
							Leg(
								a.TermAs[Set[B]]("homology_map(P, λm:num. λx:B. x, n, s)"),
								"g ∘ f, a chain map, is homotopic to the identity, so the two induce one map",
								By(
									HomotopicSameHomologyMap.Read(complexP),
									ChainMapCompose,
									fChain,
									gChain,
									ChainMapIdentity.Read(complexP),
									homotopy,
									sIn)),
							FinalLeg(
								"and the identity induces the identity",
								By(HomologyMapIdentity.Read(complexP), sIn)),
						))
				})

			firstMap := ctx.Lemma(ChainComplex.Statement(Statement{
				Binders: "∀Q:complex_ops(A, C). ∀f:(num → B → C). ∀g:(num → C → B).",
				Hypotheses: []string{
					"chain_complex(R, Q)",
					"chain_homotopy_equivalence(R, P, Q, f, g)",
				},
				Conclusion: "quasi_isomorphism(R, P, Q, f)",
			}),
				func(
					a *Argument,
					complexP ChainComplexFact[on.R],
					_ *Expr[ComplexOps[A, C]],
					_ *Arrow2[Nat, B, C],
					_ *Arrow2[Nat, C, B],
					complexQ ChainComplexFact[on.R],
					equivalence Fact,
				) {
					parts := a.Conjuncts(
						a.Unfolded(equivalence, ChainHomotopyEquivalenceDef),
						"f is a chain map",
						"g is a chain map",
						"g ∘ f is homotopic to the identity of P",
						"f ∘ g is homotopic to the identity of Q")
					fChain, gChain := parts[0], parts[1]
					_, homotopyOnP := a.Unpack(parts[2])
					_, homotopyOnQ := a.Unpack(parts[3])
					left := a.Have(
						"on every class of P the map of g undoes the map of f",
						"∀n:num. ∀s:set(B). s ∈ homology(P, n) ⇒ homology_map(P, g, n, homology_map(Q, f, n, s)) = s",
						By(undoes, complexP, complexQ, fChain, gChain, homotopyOnP))
					right := a.Have(
						"and on every class of Q the map of f undoes the map of g",
						"∀n:num. ∀t:set(C). t ∈ homology(Q, n) ⇒ homology_map(Q, f, n, homology_map(P, g, n, t)) = t",
						By(undoes, complexQ, complexP, gChain, fChain, homotopyOnQ))
					isos := a.Have(
						"so each homology map of f is an isomorphism",
						"∀n:num. "+
							"    module_isomorphism(R, homology_module(P, n), homology_module(Q, n), homology_map(Q, f, n))",
						Derive(func(b *Argument) {
							n := b.FixAs[Nat]("n")
							forth := b.Have(
								"the map of f is linear",
								"module_homomorphism(R, homology_module(P, n), homology_module(Q, n), homology_map(Q, f, n))",
								By(HomologyMapHom.Read(complexP), complexQ, fChain))
							back := b.Have(
								"and so is the map of g",
								"module_homomorphism(R, homology_module(Q, n), homology_module(P, n), homology_map(P, g, n))",
								By(HomologyMapHom.Read(complexQ), complexP, gChain))
							// homology_module(P, n).carrier is homology(P, n) unfolded, so
							// HomIn meets each claim once Unfold(HomologyDef) opens it.
							forthInto := b.Have(
								"the map of f carries classes of P to classes of Q",
								"∀s:set(B). s ∈ homology(P, n) ⇒ homology_map(Q, f, n, s) ∈ homology(Q, n)",
								Unfold(HomologyDef),
								By(module_homomorphism.HomIn.Read(forth)))
							backInto := b.Have(
								"and the map of g classes of Q to classes of P",
								"∀t:set(C). t ∈ homology(Q, n) ⇒ homology_map(P, g, n, t) ∈ homology(P, n)",
								Unfold(HomologyDef),
								By(module_homomorphism.HomIn.Read(back)))
							classesP := b.TermAs[Set[Set[B]]]("homology(P, n)")
							classesQ := b.TermAs[Set[Set[C]]]("homology(Q, n)")
							fStar := b.TermAs[Fun[Set[B], Set[C]]]("homology_map(Q, f, n)")
							gStar := b.TermAs[Fun[Set[C], Set[B]]]("homology_map(P, g, n)")
							bijective := b.Have(
								"two maps of the classes that undo each other are bijections",
								"injective_on(homology(P, n), homology_map(Q, f, n)) ∧ "+
									"image(homology_map(Q, f, n), homology(P, n)) = homology(Q, n)",
								By(
									left.At(n),
									right.At(n),
									forthInto,
									backInto,
									functions.TwoSidedInverseBijection.At(classesP, classesQ, fStar, gStar)))
							// The isomorphism asks for a bijection of the carriers, homology
							// unfolded, so bijective is read unfolded too.
							b.Show(
								"a bijective linear map of the homology modules is an isomorphism",
								By(module_homomorphism.ModuleIsomorphismDef, forth, b.Unfolded(bijective, HomologyDef)))
						}))
					a.Show(
						"so f is a quasi-isomorphism",
						By(QuasiIsomorphismDef, fChain, isos))
				})

			return ctx.Theorem(headline,
				func(
					a *Argument,
					complexP ChainComplexFact[on.R],
					_ *Expr[ComplexOps[A, C]],
					_ *Arrow2[Nat, B, C],
					_ *Arrow2[Nat, C, B],
					complexQ ChainComplexFact[on.R],
					equivalence Fact,
				) {
					reversed := a.Have(
						"read with g first, the two maps are again an equivalence",
						"chain_homotopy_equivalence(R, Q, P, g, f)",
						By(ChainHomotopyEquivalenceDef, equivalence))
					a.Show(
						"f is the first map of the one equivalence and g of the other",
						By(firstMap, complexP, complexQ, equivalence, reversed))
				})
		}),
})}

// ChainHomotopyEquivalenceCancel — a chain homotopy equivalence cancels
// from either side of a homotopy, and a strict section of it is a
// homotopy inverse.
var ChainHomotopyEquivalenceCancel = chainHomotopyEquivalenceCancelThm{family.Add(registry.ProofEntry{
	Name: "ChainHomotopyEquivalenceCancel",
	Key:  "prop_6ca5eb6fa837c725",
	Reading: "The third clause is how a strict section j of a homotopy equivalence a " +
		"(a ∘ j = id on the nose) is recognised as its homotopy inverse; the " +
		"Alexander–Whitney sections of the cotangent totals are used this way. The " +
		"cancelled homotopies are existential: the witnesses the proof assembles depend " +
		"on the homotopies a ∘ a' ≃ id and a' ∘ a ≃ id, which the equivalence only asserts.",
	Deps: []registry.EntryLike{
		ChainHomotopyEquivalenceDef,
		ChainHomotopyCalculus,
		ChainHomotopyDef,
		ChainMapDef,
		ChainMapHom,
		ChainMapSquare,
		ComplexModules,
		ComplexBoundaryHom,
		module_homomorphism.HomCompose,
		module_homomorphism.HomIdentity,
		module_homomorphism.HomZero,
		module.AddGroupOn,
		module.SmulZero,
	},
	Build: family.Card(ChainComplex.Statement(Statement{
		Binders: "∀Q:complex_ops(A, C). ∀a:(num → B → C). ∀a':(num → C → B).",
		Hypotheses: []string{
			"chain_complex(R, Q)",
			"chain_homotopy_equivalence(R, P, Q, a, a')",
		},
		Conclusion: "(∀W:complex_ops(A, D). " +
			"    chain_complex(R, W) ⇒ " +
			"    ∀x y:(num → D → B). " +
			"        chain_map(R, W, P, x) ∧ " +
			"        chain_map(R, W, P, y) ∧ " +
			"        (∃h:(num → D → C). " +
			"            chain_homotopy(R, " +
			"                W, " +
			"                Q, " +
			"                λn:num. λw:D. a(n)(x(n)(w)), " +
			"                λn:num. λw:D. a(n)(y(n)(w)), " +
			"                h)) ⇒ " +
			"        ∃h:(num → D → B). chain_homotopy(R, W, P, x, y, h)) ∧ " +
			"(∀W:complex_ops(A, D). " +
			"    chain_complex(R, W) ⇒ " +
			"    ∀x y:(num → C → D). " +
			"        chain_map(R, Q, W, x) ∧ " +
			"        chain_map(R, Q, W, y) ∧ " +
			"        (∃h:(num → B → D). " +
			"            chain_homotopy(R, " +
			"                P, " +
			"                W, " +
			"                λn:num. λu:B. x(n)(a(n)(u)), " +
			"                λn:num. λu:B. y(n)(a(n)(u)), " +
			"                h)) ⇒ " +
			"        ∃h:(num → C → D). chain_homotopy(R, Q, W, x, y, h)) ∧ " +
			"(∀j:(num → C → B). " +
			"    chain_map(R, Q, P, j) ∧ (∀n:num. ∀v:C. v ∈ Q.terms(n) ⇒ a(n)(j(n)(v)) = v) ⇒ " +
			"    ∃h:(num → B → B). chain_homotopy(R, P, P, λn:num. λu:B. j(n)(a(n)(u)), λn:num. λu:B. u, h))",
	}),
		"left: postcompose a x ≃ a y with a', and x ≃ a' a x ≃ a' a y ≃ y, the outer two from a' "+
			"a ≃ id precomposed with x and with y, reversed for the first (ChainHomotopyCalculus, "+
			"ChainHomotopyEquivalenceDef; a composite of chain maps is a chain map by HomCompose and "+
			"the two squares). Right: precompose x a ≃ y a with a', and x ≃ x a a' ≃ y a a' ≃ y from "+
			"a a' ≃ id postcomposed with x and with y. Third clause: a ∘ (j ∘ a) = a on P's terms, "+
			"a(n)(u) lying in Q.terms(n) (ChainMapHom), so the zero homotopy λn u. Q.zero joins a ∘ "+
			"(j ∘ a) and a ∘ id (u − u = Q.zero = Q.d(Q.zero) + Q.zero, the boundary keeping zero by "+
			"HomZero), and left cancellation at W = P gives j ∘ a ≃ id"),
})}
