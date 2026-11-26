// koszul.go — the Koszul simplicial algebra of an element g of a
// commutative ring R: the polynomial simplicial algebra free on one
// generator x in degree 1 with d_0 x = g and d_1 x = 0. In degree n it is
// the free algebra on the variables x_1, …, x_n, named once for all
// degrees; the face d_i for 1 ≤ i < n sets x_i = x_{i+1}, d_n sets
// x_n = 0, d_0 sends x_1 to g and lowers every other index by one, and
// the degeneracy s_i raises the indices above i by one. Its Moore terms
// in degree n are the multiples of Π_n = (x_1 − x_2)⋯(x_{n−1} − x_n)·x_n
// over every commutative ring; a Moore cycle of degree at least 2 is
// Π_n (x_1 − g) times a polynomial whatever g is, one of degree 1 is so
// when g is not a zero divisor, and such a cycle has a preimage in closed
// form, so the algebra resolves R/(g) when g is not a zero divisor.

package cotangent_examples

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/simplicial_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/chain_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/free_algebra"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/quotient_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinal"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_module"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_set"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The names, the degrees, the faces and the degeneracies
// ---------------------------------------------------------------------------

// koszulNameDef — `koszul_name(j)`: the name in U of the j-th Koszul
// variable x_j, the number j carried into U by the universe's naming of
// the set of all numbers. One name serves x_j in every degree it lives
// in.
var koszulNameDef = koszulNameDefThm{family.Define(registry.DefEntry{
	Name:  "koszulNameDef",
	Key:   "prop_c51c5bd58d291fd5",
	Const: "koszul_name",
	Type:  "num → U",
	Equations: []string{
		"∀j:num. koszul_name(j) = carrier_tag(𝕌⟨A:num⟩, j)",
	},
	Reading: "The set named is all of num, the one carrier of every Koszul name, so x_j has " +
		"one name whatever the degree; a naming of 1 .. n would name x_j afresh in each degree and " +
		"the faces and degeneracies would no longer be renamings of one set of names. The naming " +
		"is injective in a universe for any ring, the room cotangent_universe asks for prod(num, " +
		"U) holding a copy of num, so the n names of degree n are distinct (KoszulNames). " +
		"koszul_name(0) names no variable of the algebra: the variables of degree n are x_1, …, x_n.",
})}

// koszulIndexDef — `koszul_index(x)`: the index j of the Koszul name x =
// koszul_name(j), read back through the naming.
var koszulIndexDef = koszulIndexDefThm{family.Define(registry.DefEntry{
	Name:  "koszulIndexDef",
	Key:   "prop_24df5a1c50b74e52",
	Const: "koszul_index",
	Type:  "U → num",
	Equations: []string{
		"∀x:U. koszul_index(x) = inverse_on(𝕌⟨A:num⟩, koszul_name, x)",
	},
	Reading: "Read on the names only; at a member of U that names no number the chosen index is " +
		"unspecified. It reads back j from koszul_name(j) once the naming is injective, in a universe.",
	Deps: []registry.EntryLike{koszulNameDef},
})}

// koszulNamesDef — `koszul_names(n)`: the names of the variables x_1, …,
// x_n of degree n; none in degree 0.
var koszulNamesDef = koszulNamesDefThm{family.Define(registry.DefEntry{
	Name:  "koszulNamesDef",
	Key:   "prop_5b5805d9ba1fcca8",
	Const: "koszul_names",
	Type:  "num → set(U)",
	Equations: []string{
		"∀n:num. koszul_names(n) = image(koszul_name, 1 .. n)",
	},
	Reading: "The name sets grow with the degree, each holding the one " +
		"below it: the Koszul algebra of degree n − 1 is a subring of the one " +
		"of degree n, and only the faces and degeneracies tell the degrees apart.",
	Deps: []registry.EntryLike{koszulNameDef},
})}

// koszulFaceValueDef — `koszul_face_value(R, g, n, i, k)`: the value of
// the face d_i out of degree n at the variable x_k — x_k for k ≤ i,
// except x_n ↦ 0 under d_n; the constant g for k = 1 > i; x_{k−1} for
// k > i otherwise.
var koszulFaceValueDef = koszulFaceValueDefThm{family.Define(registry.DefEntry{
	Name:  "koszulFaceValueDef",
	Key:   "prop_21e5bcb7e93504e5",
	Const: "koszul_face_value",
	Type:  "ring_ops(A) → A → num → num → num → U",
	Equations: []string{
		"∀R:ring_ops(A). ∀g:A. ∀n i k:num. " +
			"    koszul_face_value(R, g, n, i, k) = " +
			"    COND(k ≤ i, " +
			"        COND(k = n, " +
			"            universe_algebra_ring(R, 𝕌⟨A:U⟩).zero, " +
			"            universe_algebra_var(R, koszul_name(k))), " +
			"        COND(k = 1, universe_algebra_const(R, g), universe_algebra_var(R, koszul_name(k - 1))))",
	},
	Reading: "Read for i ≤ n and 1 ≤ k ≤ n. The face d_i for 1 ≤ i < n sends both " +
		"x_i and x_{i+1} to x_i, d_n sends x_n to 0 and keeps the others, and d_0 sends " +
		"x_1 to the constant g and x_k to x_{k−1}: g enters through d_0 alone, so out of " +
		"degree 1, where d_1 sends x_1 to 0, the two faces of x_1 agree exactly when g = 0.",
	Deps: []registry.EntryLike{koszulNameDef},
})}

// koszulFaceDef — `koszul_face(R, g, n, i, u)`: the face d_i out of
// degree n, the algebra map over R that fixes the constants and carries
// each variable x_k to koszul_face_value(R, g, n, i, k).
var koszulFaceDef = koszulFaceDefThm{family.Define(registry.DefEntry{
	Name:  "koszulFaceDef",
	Key:   "prop_9fa0380d76511481",
	Const: "koszul_face",
	Type:  "ring_ops(A) → A → num → num → U → U",
	Equations: []string{
		"∀R:ring_ops(A). ∀g:A. ∀n i:num. ∀u:U. " +
			"    koszul_face(R, g, n, i, u) = " +
			"    universe_algebra_eval(R, " +
			"        universe_algebra_ring(R, 𝕌⟨A:U⟩), " +
			"        universe_algebra_const(R), " +
			"        λx:U. koszul_face_value(R, g, n, i, koszul_index(x)), " +
			"        u)",
	},
	Reading: "An evaluation in the one ring of the universe with each constant " +
		"itself, so it is read on the Koszul algebra of degree n only, where every variable " +
		"is named by an index 1, …, n. Its values lie in the algebra of degree n − 1 once g " +
		"lies in R's carrier, the constant g being then a member of every algebra.",
	Deps: []registry.EntryLike{koszulFaceValueDef, koszulIndexDef},
})}

// koszulDegeneracyDef — `koszul_degeneracy(R, i, u)`: the degeneracy s_i,
// the algebra map over R induced by the renaming that keeps x_k for
// k ≤ i and sends x_k to x_{k+1} for k > i — one map of U for every
// degree.
var koszulDegeneracyDef = koszulDegeneracyDefThm{family.Define(registry.DefEntry{
	Name:  "koszulDegeneracyDef",
	Key:   "prop_b9d78c8bab525042",
	Const: "koszul_degeneracy",
	Type:  "ring_ops(A) → num → U → U",
	Equations: []string{
		"∀R:ring_ops(A). ∀i:num. ∀u:U. " +
			"    koszul_degeneracy(R, i, u) = " +
			"    universe_algebra_map(R, " +
			"        R, " +
			"        λa:A. a, " +
			"        λx:U. COND(koszul_index(x) ≤ i, x, koszul_name(koszul_index(x) + 1)), " +
			"        u)",
	},
	Reading: "The degree is no argument: the names being shared, s_i out of every degree " +
		"is the same renaming, which carries the names of degree n onto those of degree n + 1 " +
		"but x_{i+1}. The simplicial algebra's degeneracies are λn. koszul_degeneracy(R).",
	Deps: []registry.EntryLike{koszulIndexDef, koszulNameDef},
})}

// ---------------------------------------------------------------------------
// The product Π_n, and the base ring R/(g)
// ---------------------------------------------------------------------------

// koszulProductDef — `koszul_product(R, n)`: Π_n = (x_1 − x_2)(x_2 −
// x_3)⋯(x_{n−1} − x_n)·x_n in the free algebra over R, the product over
// j ≤ n of x_j − x_{j+1} for j < n and of x_n; Π_0 is one and Π_1 is x_1.
var koszulProductDef = koszulProductDefThm{family.Define(registry.DefEntry{
	Name:  "koszulProductDef",
	Key:   "prop_78d584d318b21e9c",
	Const: "koszul_product",
	Type:  "ring_ops(A) → num → U",
	Equations: []string{
		"∀R:ring_ops(A). ∀n:num. " +
			"    koszul_product(R, n) = " +
			"    module_sum(universe_algebra_ring(R, 𝕌⟨A:U⟩).mul, " +
			"        universe_algebra_ring(R, 𝕌⟨A:U⟩).one, " +
			"        1 .. n, " +
			"        λj:num. " +
			"            COND(j = n, " +
			"                universe_algebra_var(R, koszul_name(j)), " +
			"                universe_algebra_ring(R, 𝕌⟨A:U⟩).sub(universe_algebra_var(R, koszul_name(j)), " +
			"                    universe_algebra_var(R, koszul_name(j + 1)))))",
	},
	Reading: "Each factor is monic of degree one in its lowest variable, x_j − x_{j+1} in " +
		"x_j and x_n in x_n, so Π_n is not a zero divisor over any commutative ring. The faces " +
		"d_1, …, d_n each kill one factor; d_0 sends Π_{n+2} to (g − x_1)·Π_{n+1}, and Π_1 to g.",
	Deps: []registry.EntryLike{koszulNameDef},
})}

// KoszulQuotientDef — `koszul_quotient(R, g)`: the ring R/(g) as a ring
// record, the cosets of the ideal generated by g under the coset
// operations, the ideal as the zero.
var KoszulQuotientDef = koszulQuotientDefThm{family.Define(registry.DefEntry{
	Name:  "KoszulQuotientDef",
	Key:   "prop_974af18f4cb97690",
	Const: "koszul_quotient",
	Type:  "ring_ops(A) → A → ring_ops(set(A))",
	Equations: []string{
		"∀R:ring_ops(A). ∀g:A. " +
			"    koszul_quotient(R, g) = " +
			"    mk_ring(set_mul(R.add), " +
			"        ideal_span(R, {g}), " +
			"        set_inv(R.neg), " +
			"        quotient_mul(R.add, R.mul, ideal_span(R, {g})), " +
			"        left_coset(R.add, R.one, ideal_span(R, {g})), " +
			"        quotient_sub(R.add, R.neg), " +
			"        left_cosets(R.add, R.carrier, ideal_span(R, {g})))",
	},
	Reading: "The record is ideal_quotient_ring at the ideal generated by g, " +
		"so a commutative ring when R is one and g lies in its carrier. At g = 0 " +
		"the ideal is {R.zero} and the quotient is R again, its members singletons; " +
		"at a unit g the ideal is the carrier and the quotient is the zero ring.",
})}

// KoszulProjectionDef — `koszul_projection(R, g, a)`: the coset a + (g),
// the projection of R onto R/(g).
var KoszulProjectionDef = koszulProjectionDefThm{family.Define(registry.DefEntry{
	Name:  "KoszulProjectionDef",
	Key:   "prop_5fbe1d2b27354fd2",
	Const: "koszul_projection",
	Type:  "ring_ops(A) → A → A → set(A)",
	Equations: []string{
		"∀R:ring_ops(A). ∀g a:A. koszul_projection(R, g, a) = left_coset(R.add, a, ideal_span(R, {g}))",
	},
})}

// koszulAugmentationDef — `koszul_augmentation(R, g, u)`: the
// augmentation from the Koszul algebra of degree 0, the constants, onto
// R/(g): u evaluated in R/(g) with each coefficient projected and every
// variable at zero.
var koszulAugmentationDef = koszulAugmentationDefThm{family.Define(registry.DefEntry{
	Name:  "koszulAugmentationDef",
	Key:   "prop_f69a423fca0e7dd7",
	Const: "koszul_augmentation",
	Type:  "ring_ops(A) → A → U → set(A)",
	Equations: []string{
		"∀R:ring_ops(A). ∀g:A. ∀u:U. " +
			"    koszul_augmentation(R, g, u) = " +
			"    universe_algebra_eval(R, " +
			"        koszul_quotient(R, g), " +
			"        koszul_projection(R, g), " +
			"        λx:U. koszul_quotient(R, g).zero, " +
			"        u)",
	},
	Reading: "Read on the degree-0 algebra, which has no variables, so the value " +
		"given them is never read there: the constant a goes to a + (g). Through d_0 it " +
		"sends x_1 to g + (g), the zero coset, and through d_1 to the zero coset as well.",
	Deps: []registry.EntryLike{KoszulQuotientDef, KoszulProjectionDef},
})}

// ---------------------------------------------------------------------------
// The spelling of the statements
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// The simplicial algebra
// ---------------------------------------------------------------------------

// KoszulNames — in a universe, each Koszul name reads back to its index,
// so the names x_1, …, x_n of degree n are n distinct members of U.
var KoszulNames = koszulNamesThm{family.Add(registry.ProofEntry{
	Name: "KoszulNames",
	Key:  "prop_1a2479c3564c4a63",
	Reading: "R only carries the hypothesis: the room it asks for prod(num, U) reads no ring, " +
		"so every universe names the numbers. cotangent_universe's third clause alone gives the " +
		"injection of num into U, j ↦ e(j, u₀) for e the injection of prod(num, U) and any u₀ in U.",
	Deps: []registry.EntryLike{
		koszulIndexDef,
		koszulNameDef,
		simplicial_ring.CotangentUniverseDef,
		simplicial_ring.CarrierTagInjective,
		cardinal.CardLeDef,
		functions.InjectiveOnDef,
		functions.InverseOnLeft,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀j:num.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
		},
		Conclusion: "koszul_index⟨U:U⟩(koszul_name(j)) = j",
	},
		"the last clause of cotangent_universe is an injection of prod(num, U) into "+
			"U (CardLeDef); U being inhabited, j ↦ its image at (j, u) injects num into "+
			"U, so the naming of 𝕌⟨A:num⟩ is injective on it (CarrierTagInjective), and "+
			"the preimage chosen by koszul_index is the index itself (InverseOnLeft)"),
})}

// KoszulDegeneracies — the degeneracy s_i fixes the constants and sends
// x_k to x_k for k ≤ i and to x_{k+1} for k > i.
var KoszulDegeneracies = koszulDegeneraciesThm{family.Add(registry.ProofEntry{
	Name: "KoszulDegeneracies",
	Key:  "prop_4020c487cbcc668e",
	Reading: "True for every i and every k, and g plays no part: the " +
		"degeneracy is a renaming of the names over the identity of R.",
	Deps: []registry.EntryLike{
		koszulDegeneracyDef,
		KoszulNames,
		simplicial_ring.UniverseAlgebraMapDef,
		simplicial_ring.UniverseAlgebraConstDef,
		simplicial_ring.UniverseAlgebraVarDef,
		simplicial_ring.UniverseEmbeddingHost,
		free_algebra.FreeAlgebraMapConst,
		free_algebra.FreeAlgebraMapVar,
		ring_homomorphism.RingHomomorphism,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀i:num.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"comm_ring_on(R)",
		},
		Conclusion: "(∀a:A. " +
			"    a ∈ R.carrier ⇒ " +
			"    koszul_degeneracy(R, i, universe_algebra_const⟨U:U⟩(R, a)) = " +
			"    universe_algebra_const(R, a)) ∧ " +
			"(∀k:num. " +
			"    koszul_degeneracy(R, i, universe_algebra_var(R, koszul_name⟨U:U⟩(k))) = " +
			"    universe_algebra_var(R, koszul_name⟨U:U⟩(COND(k ≤ i, k, k + 1))))",
	},
		"the degeneracy is the map induced by the identity of R, a ring map of the commutative "+
			"ring R (RingHomomorphism), and a renaming of the names (UniverseAlgebraMapDef), so "+
			"FreeAlgebraMapConst and FreeAlgebraMapVar at the universe embedding "+
			"(UniverseEmbeddingHost); the index of koszul_name(k) is k (KoszulNames)"),
})}

// KoszulDegeneraciesHom — each degeneracy s_i out of degree n, i ≤ n, is
// an algebra map over R from the Koszul algebra of degree n to the one of
// degree n + 1.
var KoszulDegeneraciesHom = koszulDegeneraciesHomThm{family.Add(registry.ProofEntry{
	Name: "KoszulDegeneraciesHom",
	Key:  "prop_1d7a1cbc72a41e98",
	Deps: []registry.EntryLike{
		koszulDegeneracyDef,
		koszulNamesDef,
		KoszulNames,
		simplicial_ring.UniverseAlgebraHomomorphismDef,
		simplicial_ring.UniverseAlgebraMapDef,
		simplicial_ring.UniverseAlgebraDef,
		simplicial_ring.UniverseEmbeddingHost,
		free_algebra.FreeAlgebraMapHom,
		ring_homomorphism.RingHomomorphism,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀n i:num.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"comm_ring_on(R)",
			"i ≤ n",
		},
		Conclusion: "universe_algebra_homomorphism(R, " +
			"    koszul_names⟨U:U⟩(n), " +
			"    koszul_names(n + 1), " +
			"    koszul_degeneracy(R, i))",
	},
		"FreeAlgebraMapHom at the identity of R and the renaming, which carries koszul_name(k) for "+
			"1 ≤ k ≤ n to koszul_name(k) or koszul_name(k + 1), a name of degree n + 1 (KoszulNames)"),
})}

// KoszulFaces — the face d_i out of degree n fixes the constants and
// sends x_k to koszul_face_value(R, g, n, i, k).
var KoszulFaces = koszulFacesThm{family.Add(registry.ProofEntry{
	Name: "KoszulFaces",
	Key:  "prop_d41f210a8412773e",
	Reading: "g ∈ R.carrier is read at one value, d_0 sending x_1 to the constant g: the " +
		"evaluation returns a value only from the host ring's carrier, which the constant of " +
		"g reaches once g lies in R's carrier. The values 0 and the variables need nothing.",
	Deps: []registry.EntryLike{
		koszulFaceDef,
		koszulFaceValueDef,
		KoszulNames,
		simplicial_ring.UniverseAlgebraEvalDef,
		simplicial_ring.UniverseAlgebraRingDef,
		simplicial_ring.UniverseAlgebraConstDef,
		simplicial_ring.UniverseAlgebraVarDef,
		simplicial_ring.UniverseEmbeddingHost,
		free_algebra.FreeAlgebraEvalConst,
		free_algebra.FreeAlgebraEvalVar,
		free_algebra.FreeAlgebraConstHom,
		free_algebra.FreeAlgebraVarIn,
		free_algebra.FreeAlgebraCommRingOn,
		comm_ring.ZeroIn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀g:A. ∀n i:num.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"comm_ring_on(R)",
			"g ∈ R.carrier",
		},
		Conclusion: "(∀a:A. " +
			"    a ∈ R.carrier ⇒ " +
			"    koszul_face(R, g, n, i, universe_algebra_const⟨U:U⟩(R, a)) = " +
			"    universe_algebra_const(R, a)) ∧ " +
			"(∀k:num. " +
			"    koszul_face(R, g, n, i, universe_algebra_var(R, koszul_name⟨U:U⟩(k))) = " +
			"    koszul_face_value(R, g, n, i, k))",
	},
		"the face is an evaluation in the ring of the free algebra on 𝕌, a commutative ring "+
			"(FreeAlgebraCommRingOn at UniverseEmbeddingHost), with the constants, a ring map, as "+
			"coefficient map (FreeAlgebraConstHom): FreeAlgebraEvalConst gives the first conjunct; "+
			"FreeAlgebraEvalVar the second, the value 0, a variable (FreeAlgebraVarIn) or the constant of g "+
			"∈ R.carrier lying in that ring's carrier, and the index of koszul_name(k) being k (KoszulNames)"),
})}

// KoszulFacesHom — each face d_i out of degree n + 1, i ≤ n + 1, is an
// algebra map over R from the Koszul algebra of degree n + 1 to the one of
// degree n.
var KoszulFacesHom = koszulFacesHomThm{family.Add(registry.ProofEntry{
	Name: "KoszulFacesHom",
	Key:  "prop_1fa354f21f9e3fa8",
	Deps: []registry.EntryLike{
		koszulFaceDef,
		KoszulFaces,
		koszulNamesDef,
		simplicial_ring.UniverseAlgebraHomomorphismDef,
		simplicial_ring.UniverseAlgebraEvalDef,
		simplicial_ring.UniverseAlgebraRingDef,
		simplicial_ring.UniverseEmbeddingHost,
		free_algebra.FreeAlgebraEvalHom,
		free_algebra.FreeAlgebraOpsIndependentOfVariables,
		free_algebra.FreeAlgebraConstHom,
		free_algebra.FreeAlgebraVarIn,
		free_algebra.FreeAlgebraHomomorphismDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀g:A. ∀n i:num.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"comm_ring_on(R)",
			"g ∈ R.carrier",
			"i ≤ n + 1",
		},
		Conclusion: "universe_algebra_homomorphism(R, " +
			"    koszul_names⟨U:U⟩(n + 1), " +
			"    koszul_names(n), " +
			"    koszul_face(R, g, n + 1, i))",
	},
		"the evaluation reads its target ring through the operations only, which are those of the "+
			"algebra of degree n (FreeAlgebraOpsIndependentOfVariables), so FreeAlgebraEvalHom into that "+
			"algebra applies once the values at the names of degree n + 1 lie there: by KoszulFaces x_k "+
			"goes to 0, to x_k with k ≤ n, to the constant g or to x_{k−1} with 1 ≤ k − 1 ≤ n; the "+
			"constants are fixed (KoszulFaces), the last conjunct of FreeAlgebraHomomorphismDef at "+
			"UniverseAlgebraHomomorphismDef, the first being void at φ = λa. a"),
})}

// KoszulSimplicial — the Koszul algebras of all degrees, with the faces
// and the degeneracies, are a simplicial set.
var KoszulSimplicial = koszulSimplicialThm{family.Add(registry.ProofEntry{
	Name: "KoszulSimplicial",
	Key:  "prop_a6914aa1433cf175",
	Reading: "The identities are those of Δ[1], generated by one 1-simplex x whose vertices " +
		"are g and 0: a simplex of degree n is a monotone map of [n] to [1], named by its switch " +
		"point, the first index where it takes the value 1. x_k is the map switching at k, the " +
		"constant maps onto 1 and 0 give g and 0, and a face or degeneracy acts on switch points " +
		"by composition: d_i keeps k ≤ i and lowers k > i, s_i keeps k ≤ i and raises k > i.",
	Deps: []registry.EntryLike{
		simplicial_set.SimplicialSet,
		KoszulFacesHom,
		KoszulDegeneraciesHom,
		KoszulFaces,
		KoszulDegeneracies,
		simplicial_ring.UniverseAlgebraHomomorphismDef,
		free_algebra.FreeAlgebraHomomorphismDef,
		free_algebra.FreeAlgebraEvalUnique,
		ring_homomorphism.MapIn,
		ring_homomorphism.RingHomomorphism,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀g:A.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"comm_ring_on(R)",
			"g ∈ R.carrier",
		},
		Conclusion: "simplicial_set(koszul_simplicial_set⟨U:U⟩(R, g))",
	},
		"faces and degeneracies land in the neighbouring degrees (KoszulFacesHom, KoszulDegeneraciesHom, "+
			"MapIn). Each identity compares two composites of algebra maps over R between Koszul algebras, "+
			"which fix the constants and so agree once they agree on the variables (FreeAlgebraEvalUnique); "+
			"on x_k both are computed by KoszulFaces and KoszulDegeneracies, the constant g and 0 being "+
			"fixed by every algebra map, and agree by index arithmetic: d_i keeps x_k below i and lowers it "+
			"above, with x_1 ↦ g under d_0 and x_n ↦ 0 under d_n; s_j keeps x_k up to j and raises it above"),
})}

// KoszulPolynomialAlgebra — the Koszul algebra of g is a polynomial
// simplicial algebra over R.
var KoszulPolynomialAlgebra = koszulPolynomialAlgebraThm{family.Add(registry.ProofEntry{
	Name: "KoszulPolynomialAlgebra",
	Key:  "prop_f5c459f4e71618e1",
	Deps: []registry.EntryLike{
		simplicial_ring.PolynomialSimplicialAlgebra,
		KoszulSimplicial,
		KoszulFacesHom,
		KoszulDegeneraciesHom,
		KoszulDegeneracies,
		free_algebra.FreeAlgebraVarIn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀g:A.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"comm_ring_on(R)",
			"g ∈ R.carrier",
		},
		Conclusion: "polynomial_simplicial_algebra(R, " +
			"    koszul_names⟨U:U⟩, " +
			"    koszul_face(R, g), " +
			"    λn:num. koszul_degeneracy(R))",
	},
		"unfold PolynomialSimplicialAlgebra: the ring is commutative by hypothesis, the "+
			"simplicial set is KoszulSimplicial, the faces and the degeneracies are algebra maps "+
			"by KoszulFacesHom and KoszulDegeneraciesHom, and a degeneracy sends the variable of "+
			"a name of degree n to the variable of a name of degree n + 1 (KoszulDegeneracies)"),
})}

// KoszulAugmented — the Koszul algebra of g is augmented over R/(g)
// through the projection, the degree-0 algebra, the constants, going to
// the cosets of their coefficients.
var KoszulAugmented = koszulAugmentedThm{family.Add(registry.ProofEntry{
	Name: "KoszulAugmented",
	Key:  "prop_f25fa3bc96c20c4b",
	Reading: "No hypothesis on g beyond lying in R's carrier: ε d_0 and ε d_1 differ only at " +
		"x_1, sent to g + (g) and to 0 + (g), one coset. That one is load-bearing: off the carrier " +
		"no ideal of R holds g, so ideal_span of {g} is the whole type and R/(g) is no ring.",
	Deps: []registry.EntryLike{
		simplicial_ring.AugmentedPolynomialAlgebra,
		KoszulPolynomialAlgebra,
		KoszulFacesHom,
		KoszulFaces,
		koszulAugmentationDef,
		KoszulQuotientDef,
		KoszulProjectionDef,
		simplicial_ring.UniverseAlgebraEvalDef,
		ring_ideal.SpanIdeal,
		ring_ideal.SpanContains,
		quotient_ring.QuotientRingOn,
		quotient_ring.ProjectionHomomorphism,
		quotient_ring.CosetEqIff,
		free_algebra.FreeAlgebraNoVariables,
		free_algebra.FreeAlgebraEvalHom,
		free_algebra.FreeAlgebraEvalConst,
		free_algebra.FreeAlgebraEvalUnique,
		ring_homomorphism.RingHomomorphism,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀g:A.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"comm_ring_on(R)",
			"g ∈ R.carrier",
		},
		Conclusion: "augmented_polynomial_algebra(R, " +
			"    koszul_names⟨U:U⟩, " +
			"    koszul_face(R, g), " +
			"    λn:num. koszul_degeneracy(R), " +
			"    koszul_quotient(R, g), " +
			"    koszul_projection(R, g), " +
			"    koszul_augmentation(R, g))",
	},
		"the ideal generated by g is an ideal (SpanIdeal), so R/(g) is a commutative ring and the "+
			"projection a ring map (QuotientRingOn, ProjectionHomomorphism at the record's fields); the "+
			"degree-0 algebra is the constants (FreeAlgebraNoVariables) and the augmentation the "+
			"evaluation at the projection, a ring map sending the constant a to a + (g) "+
			"(FreeAlgebraEvalHom, FreeAlgebraEvalConst). ε d_0 and ε d_1 are ring maps out of the degree-1 "+
			"algebra agreeing on the constants and sending x_1 to g + (g) and to 0 + (g) (KoszulFaces), "+
			"one coset as g lies in the ideal (SpanContains, CosetEqIff); FreeAlgebraEvalUnique"),
})}

// ---------------------------------------------------------------------------
// The Moore complex
// ---------------------------------------------------------------------------

// KoszulProductRegular — Π_n lies in the Koszul algebra of degree n and is
// not a zero divisor there.
var KoszulProductRegular = koszulProductRegularThm{family.Add(registry.ProofEntry{
	Name: "KoszulProductRegular",
	Key:  "prop_5b8a22b939780112",
	Reading: "True over every commutative ring, the zero ring included: each " +
		"factor is monic of degree one in a variable the rest of it does not " +
		"involve. Π_0 is one. In the coordinates y_j = x_j − x_{j+1} for j < n and " +
		"y_n = x_n, a triangular change of variables, Π_n is the monomial y_1⋯y_n.",
	Deps: []registry.EntryLike{
		koszulProductDef,
		koszulNamesDef,
		KoszulNames,
		free_algebra.FreeAlgebraMonicLinearRegular,
		free_algebra.FreeAlgebraVarIn,
		free_algebra.FreeAlgebraCommRingOn,
		free_algebra.FreeAlgebraOpsIndependentOfVariables,
		simplicial_ring.UniverseEmbeddingHost,
		module.ModuleSumInsertMonoid,
		module.ModuleSumEmpty,
		module.ModuleSumInMonoid,
		comm_ring.MulMonoidOn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀n:num.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"comm_ring_on(R)",
		},
		Conclusion: "koszul_product(R, n) ∈ universe_algebra(R, koszul_names⟨U:U⟩(n)) ∧ " +
			"(∀u:U. " +
			"    u ∈ universe_algebra(R, koszul_names⟨U:U⟩(n)) ∧ " +
			"    universe_algebra_ring(R, 𝕌⟨A:U⟩).mul(koszul_product(R, n), u) = " +
			"    universe_algebra_ring(R, 𝕌⟨A:U⟩).zero ⇒ " +
			"    u = universe_algebra_ring(R, 𝕌⟨A:U⟩).zero)",
	},
		"Π_n is a fold of the multiplicative monoid of the algebra of degree n (MulMonoidOn "+
			"at FreeAlgebraCommRingOn, whose operations are the host's by "+
			"FreeAlgebraOpsIndependentOfVariables): along it (ModuleSumInsertMonoid, "+
			"ModuleSumEmpty) each factor lies in that algebra (FreeAlgebraVarIn), so Π_n does "+
			"(ModuleSumInMonoid), and each factor is var y − c with c not involving y — x_{j+1} "+
			"for y = x_j, 0 for y = x_n, the names distinct (KoszulNames) — so it is not a zero "+
			"divisor (FreeAlgebraMonicLinearRegular), and a product of non-zero-divisors is none"),
})}

// KoszulMooreTerms — the Moore terms of degree n are the multiples of Π_n.
var KoszulMooreTerms = koszulMooreTermsThm{family.Add(registry.ProofEntry{
	Name: "KoszulMooreTerms",
	Key:  "prop_6536f71ea3513eae",
	Reading: "True over every commutative ring and for every g: the faces d_1, …, d_n " +
		"do not read g. At n = 0 no face is asked to vanish and Π_0 is one, so the Moore " +
		"terms are the whole degree-0 algebra. s_i d_i is the substitution x_{i+1} := x_i " +
		"and s_{n−1} d_n the substitution x_n := 0, the degeneracies being one-to-one, so " +
		"the kernel of each face is the multiples of one monic linear factor.",
	Deps: []registry.EntryLike{
		simplicial_module.MooreTermsDef,
		KoszulFaces,
		KoszulFacesHom,
		koszulProductDef,
		KoszulProductRegular,
		KoszulNames,
		free_algebra.FreeAlgebraSubstituteHom,
		free_algebra.FreeAlgebraMonicLinearDivides,
		free_algebra.FreeAlgebraMonicLinearRegular,
		free_algebra.FreeAlgebraEvalUnique,
		ring_homomorphism.MapMul,
		simplicial_ring.UniverseAlgebraModuleDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀g:A. ∀n:num.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"comm_ring_on(R)",
			"g ∈ R.carrier",
		},
		Conclusion: "moore_terms(universe_algebra_module(R), koszul_simplicial_set⟨U:U⟩(R, g), n) = " +
			"{universe_algebra_ring(R, 𝕌⟨A:U⟩).mul(koszul_product(R, n), q) | " +
			"    q:U | " +
			"    q ∈ universe_algebra(R, koszul_names⟨U:U⟩(n))}",
	},
		"the face d_i for 1 ≤ i < n kills the factor x_i − x_{i+1} of Π_n and d_n its factor x_n "+
			"(KoszulFaces); the faces are ring maps (KoszulFacesHom), so the multiples are Moore terms. "+
			"Conversely d_i for 1 ≤ i < n is the substitution x_{i+1} := x_i followed by a renaming "+
			"injective on the algebra without x_{i+1}, and d_n the substitution x_n := 0 "+
			"(FreeAlgebraSubstituteHom, FreeAlgebraEvalUnique), so the kernel of d_i is the multiples of "+
			"x_i − x_{i+1} and that of d_n the multiples of x_n (FreeAlgebraMonicLinearDivides). Divide "+
			"a Moore term by x_n, then by x_{n−1} − x_n, and so on down to x_1 − x_2: each quotient "+
			"keeps vanishing under the faces left, which carry the factors already divided out to monic "+
			"linear factors, not zero divisors (FreeAlgebraMonicLinearRegular, KoszulProductRegular)"),
})}

// KoszulBoundaryOfProduct — d_0 sends Π_1 = x_1 to the constant g and
// Π_{n+2} to (g − x_1)·Π_{n+1}.
var KoszulBoundaryOfProduct = koszulBoundaryOfProductThm{family.Add(registry.ProofEntry{
	Name: "KoszulBoundaryOfProduct",
	Key:  "prop_dd882de4b6659bae",
	Deps: []registry.EntryLike{
		koszulProductDef,
		KoszulFaces,
		KoszulFacesHom,
		KoszulProductRegular,
		ring_homomorphism.MapMul,
		ring_homomorphism.MapOne,
		module.ModuleSumInsertMonoid,
		module.ModuleSumImageMonoid,
		module.ModuleSumMonoidHomomorphism,
		comm_ring.MulMonoidOn,
		ring_homomorphism.Source,
		free_algebra.FreeAlgebraHomomorphismDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀g:A.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"comm_ring_on(R)",
			"g ∈ R.carrier",
		},
		Conclusion: "koszul_face(R, g, 1, 0, koszul_product(R, 1)) = universe_algebra_const⟨U:U⟩(R, g) ∧ " +
			"(∀n:num. " +
			"    koszul_face(R, g, n + 2, 0, koszul_product(R, n + 2)) = " +
			"    universe_algebra_ring(R, 𝕌⟨A:U⟩).mul(universe_algebra_ring(R, 𝕌⟨A:U⟩).sub( " +
			"            universe_algebra_const⟨U:U⟩(R, g), universe_algebra_var(R, koszul_name⟨U:U⟩(1))), " +
			"        koszul_product(R, n + 1)))",
	},
		"d_0 is a ring map (KoszulFacesHom) sending the factor x_1 − x_2 of Π_{n+2} to g − x_1, the "+
			"factor x_j − x_{j+1} for 2 ≤ j ≤ n + 1 to x_{j−1} − x_j, and x_{n+2} to x_{n+1} (KoszulFaces); "+
			"the image of the product is the product of the images (ModuleSumMonoidHomomorphism at d_0's "+
			"MapMul and MapOne, on the multiplicative monoid of the algebra of degree n + 2 by Source and "+
			"MulMonoidOn); the first factor comes off by ModuleSumInsertMonoid and the rest is reindexed by "+
			"j ↦ j − 1 (ModuleSumImageMonoid); Π_1 = x_1 goes to g the same way"),
})}

// KoszulCycleDivisible — in degree n + 2, if Π_{n+2}·q is a Moore cycle
// then x_1 − g divides q.
var KoszulCycleDivisible = koszulCycleDivisibleThm{family.Add(registry.ProofEntry{
	Name: "KoszulCycleDivisible",
	Key:  "prop_83baed902f116d2b",
	Reading: "No hypothesis on g beyond R's carrier: the factor g − x_1 of d_0 Π_{n+2} is monic " +
		"in x_1 whatever g is, g = 0 included. In degree 1 the factor is missing — d_0 Π_1 is the " +
		"constant g — and the divisibility needs g not to be a zero divisor (KoszulCycleDegreeOne). " +
		"s_0 d_0 is the substitution x_1 := g, s_0 being one-to-one, so d_0 kills q exactly when " +
		"x_1 − g divides it; at g = 0 the algebra is exact in every degree from 2 on.",
	Deps: []registry.EntryLike{
		KoszulBoundaryOfProduct,
		KoszulFacesHom,
		KoszulFaces,
		KoszulProductRegular,
		KoszulNames,
		free_algebra.FreeAlgebraMonicLinearRegular,
		free_algebra.FreeAlgebraMonicLinearDivides,
		free_algebra.FreeAlgebraSubstituteHom,
		free_algebra.FreeAlgebraEvalUnique,
		ring_homomorphism.MapMul,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀g:A. ∀n:num. ∀q:U.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"comm_ring_on(R)",
			"g ∈ R.carrier",
			"q ∈ universe_algebra(R, koszul_names⟨U:U⟩(n + 2))",
			"koszul_face(R, " +
				"    g, " +
				"    n + 2, " +
				"    0, " +
				"    universe_algebra_ring(R, 𝕌⟨A:U⟩).mul(koszul_product(R, n + 2), q)) = " +
				"universe_algebra_ring(R, 𝕌⟨A:U⟩).zero",
		},
		Conclusion: "∃q':U. " +
			"    q' ∈ universe_algebra(R, koszul_names⟨U:U⟩(n + 2)) ∧ " +
			"    q = " +
			"    universe_algebra_ring(R, 𝕌⟨A:U⟩).mul(universe_algebra_ring(R, 𝕌⟨A:U⟩).sub( " +
			"            universe_algebra_var(R, koszul_name⟨U:U⟩(1)), universe_algebra_const⟨U:U⟩(R, g)), " +
			"        q')",
	},
		"d_0 keeps products (KoszulFacesHom), so (g − x_1)·Π_{n+1}·d_0(q) = 0 (KoszulBoundaryOfProduct); "+
			"g − x_1 is the negation of x_1 − g, monic in x_1 with g not involving x_1, and Π_{n+1} is not a "+
			"zero divisor (FreeAlgebraMonicLinearRegular, KoszulProductRegular), so d_0(q) = 0. d_0 is the "+
			"substitution x_1 := g followed by the renaming x_k ↦ x_{k−1}, injective on the algebra on x_2, "+
			"…, x_{n+2} (KoszulFaces, FreeAlgebraSubstituteHom, FreeAlgebraEvalUnique), so the substitution "+
			"kills q and x_1 − g divides q (FreeAlgebraMonicLinearDivides)"),
})}

// KoszulCycleDegreeOne — when g is not a zero divisor, if Π_1·q = x_1·q
// is a Moore cycle of degree 1 then x_1 − g divides q.
var KoszulCycleDegreeOne = koszulCycleDegreeOneThm{family.Add(registry.ProofEntry{
	Name: "KoszulCycleDegreeOne",
	Key:  "prop_918e3ca29f604b58",
	Reading: "The one place of the Koszul algebra where g is asked not to be a zero divisor: the " +
		"cycle condition of degree 1 is g·q(g) = 0. With g = 0 every multiple of x_1 is a cycle, and x_1 " +
		"itself is no boundary over a nonzero ring, the boundaries of degree 1 being multiples of x_1².",
	Deps: []registry.EntryLike{
		KoszulBoundaryOfProduct,
		KoszulFacesHom,
		KoszulFaces,
		free_algebra.FreeAlgebraNoVariables,
		free_algebra.FreeAlgebraConstHom,
		free_algebra.FreeAlgebraMonicLinearDivides,
		free_algebra.FreeAlgebraSubstituteHom,
		free_algebra.FreeAlgebraEvalUnique,
		ring_homomorphism.MapMul,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀g:A. ∀q:U.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"comm_ring_on(R)",
			"g ∈ R.carrier",
			"∀a:A. a ∈ R.carrier ∧ R.mul(g, a) = R.zero ⇒ a = R.zero",
			"q ∈ universe_algebra(R, koszul_names⟨U:U⟩(1))",
			"koszul_face(R, g, 1, 0, universe_algebra_ring(R, 𝕌⟨A:U⟩).mul(koszul_product(R, 1), q)) = " +
				"universe_algebra_ring(R, 𝕌⟨A:U⟩).zero",
		},
		Conclusion: "∃q':U. " +
			"    q' ∈ universe_algebra(R, koszul_names⟨U:U⟩(1)) ∧ " +
			"    q = " +
			"    universe_algebra_ring(R, 𝕌⟨A:U⟩).mul(universe_algebra_ring(R, 𝕌⟨A:U⟩).sub( " +
			"            universe_algebra_var(R, koszul_name⟨U:U⟩(1)), universe_algebra_const⟨U:U⟩(R, g)), " +
			"        q')",
	},
		"d_0 keeps products and sends Π_1 to the constant g (KoszulBoundaryOfProduct), and q to a "+
			"member of the degree-0 algebra, the constant of some a ∈ R.carrier "+
			"(FreeAlgebraNoVariables); so the constant of g·a is zero, g·a = R.zero as the constants are "+
			"injective on the carrier, and a = R.zero as g is no zero divisor. So d_0 kills q, and d_0 "+
			"out of degree 1 being the substitution x_1 := g (KoszulFaces, FreeAlgebraSubstituteHom, "+
			"FreeAlgebraEvalUnique), x_1 − g divides q (FreeAlgebraMonicLinearDivides)"),
})}

// KoszulPreimage — for q of degree n + 1, v = −Π_{n+2}·s_0(q) is a Moore
// term of degree n + 2 with d_0 v = Π_{n+1}·(x_1 − g)·q.
var KoszulPreimage = koszulPreimageThm{family.Add(registry.ProofEntry{
	Name: "KoszulPreimage",
	Key:  "prop_2ffb9a94f3084c17",
	Reading: "s_0(q) is q with every index raised by one, q(x_2, …, x_{n+2}). " +
		"By KoszulCycleDivisible in degree at least 2, and by KoszulCycleDegreeOne " +
		"in degree 1 when g is no zero divisor, every Moore cycle of degree n + 1 " +
		"is Π_{n+1}·(x_1 − g)·q, so this closed form makes it a Moore boundary.",
	Deps: []registry.EntryLike{
		KoszulMooreTerms,
		KoszulBoundaryOfProduct,
		KoszulDegeneraciesHom,
		KoszulFacesHom,
		KoszulSimplicial,
		KoszulProductRegular,
		simplicial_set.FaceDegeneracyEqual,
		ring_homomorphism.MapMul,
		ring_homomorphism.AdditiveHomomorphism,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀g:A. ∀n:num. ∀q:U.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"comm_ring_on(R)",
			"g ∈ R.carrier",
			"q ∈ universe_algebra(R, koszul_names⟨U:U⟩(n + 1))",
		},
		Conclusion: "universe_algebra_ring(R, 𝕌⟨A:U⟩).neg(universe_algebra_ring(R, 𝕌⟨A:U⟩).mul( " +
			"        koszul_product(R, n + 2), koszul_degeneracy(R, 0, q))) ∈ " +
			"moore_terms(universe_algebra_module(R), koszul_simplicial_set⟨U:U⟩(R, g), n + 2) ∧ " +
			"koszul_face(R, " +
			"    g, " +
			"    n + 2, " +
			"    0, " +
			"    universe_algebra_ring(R, 𝕌⟨A:U⟩).neg(universe_algebra_ring(R, 𝕌⟨A:U⟩).mul( " +
			"            koszul_product(R, n + 2), koszul_degeneracy(R, 0, q)))) = " +
			"universe_algebra_ring(R, 𝕌⟨A:U⟩).mul(universe_algebra_ring(R, 𝕌⟨A:U⟩).mul( " +
			"        koszul_product(R, n + 1), " +
			"        universe_algebra_ring(R, 𝕌⟨A:U⟩).sub(universe_algebra_var(R, koszul_name⟨U:U⟩(1)), " +
			"            universe_algebra_const⟨U:U⟩(R, g))), " +
			"    q)",
	},
		"v is Π_{n+2} times the negation of s_0(q), a member of the algebra of degree n + 2 "+
			"(KoszulDegeneraciesHom), so a Moore term (KoszulMooreTerms); d_0 keeps products and negation "+
			"(KoszulFacesHom), sends Π_{n+2} to (g − x_1)·Π_{n+1} (KoszulBoundaryOfProduct) and s_0(q) to q "+
			"(FaceDegeneracyEqual at KoszulSimplicial), so d_0 v = −(g − x_1)·Π_{n+1}·q = Π_{n+1}·(x_1 − g)·q"),
})}

// KoszulDegreeZero — the Moore boundaries of degree 0 are the constants
// of the multiples of g, and the augmentation reads the degree-0 algebra
// modulo them onto R/(g).
var KoszulDegreeZero = koszulDegreeZeroThm{family.Add(registry.ProofEntry{
	Name: "KoszulDegreeZero",
	Key:  "prop_a589ee91529bb56b",
	Reading: "No hypothesis on g beyond lying in R's carrier, which is load-bearing: " +
		"off it ideal_span of {g} is the whole type. The degree-0 conjuncts of a " +
		"resolution hold for every such g, only exactness in degree 1 asking g to be no " +
		"zero divisor. At g = 0 the boundaries are the constant 0 and the quotient is R; " +
		"at a unit g they are every constant and the quotient is the zero ring.",
	Deps: []registry.EntryLike{
		chain_complex.BoundariesDef,
		simplicial_module.MooreComplexDef,
		KoszulMooreTerms,
		KoszulBoundaryOfProduct,
		KoszulSimplicial,
		koszulAugmentationDef,
		KoszulQuotientDef,
		KoszulProjectionDef,
		free_algebra.FreeAlgebraNoVariables,
		free_algebra.FreeAlgebraEvalConst,
		free_algebra.FreeAlgebraConstHom,
		quotient_group.InLeftCosets,
		quotient_ring.CosetEqIff,
		ring_ideal.SpanIdeal,
		ring_ideal.SpanInsert,
		simplicial_set.FaceDegeneracyEqual,
		simplicial_ring.UniverseAlgebraModuleDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀g:A.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"comm_ring_on(R)",
			"g ∈ R.carrier",
		},
		Conclusion: "boundaries( " +
			"    moore_complex(universe_algebra_module(R), koszul_simplicial_set⟨U:U⟩(R, g)), 0) = " +
			"{universe_algebra_const⟨U:U⟩(R, R.mul(g, a)) | a:A | a ∈ R.carrier} ∧ " +
			"image(koszul_augmentation(R, g), universe_algebra(R, koszul_names⟨U:U⟩(0))) = " +
			"koszul_quotient(R, g).carrier ∧ " +
			"(∀u v:U. " +
			"    u ∈ universe_algebra(R, koszul_names⟨U:U⟩(0)) ∧ " +
			"    v ∈ universe_algebra(R, koszul_names⟨U:U⟩(0)) ⇒ " +
			"    (koszul_augmentation(R, g, u) = koszul_augmentation(R, g, v) ⇔ " +
			"        universe_algebra_module(R).add(u, universe_algebra_module(R).neg(v)) ∈ " +
			"        boundaries(moore_complex(universe_algebra_module(R), koszul_simplicial_set⟨U:U⟩(R, g)), " +
			"            0)))",
	},
		"the Moore terms of degree 1 are the multiples x_1·q (KoszulMooreTerms), and d_0 sends "+
			"x_1·q to g·d_0(q) (KoszulBoundaryOfProduct), where d_0(q) runs over every constant as "+
			"q runs over the degree-1 algebra, d_0 s_0 being the identity (FaceDegeneracyEqual at "+
			"KoszulSimplicial) and the degree-0 algebra the constants (FreeAlgebraNoVariables); so "+
			"the boundaries are the constants of the multiples of g. The augmentation sends the "+
			"constant a to a + (g) (FreeAlgebraEvalConst), onto the cosets (InLeftCosets); a + (g) "+
			"= b + (g) exactly when a − b is in the ideal (CosetEqIff, SpanIdeal), the multiples "+
			"of g (SpanInsert at ∅), and the constants keep the difference (FreeAlgebraConstHom)"),
})}

// KoszulAcyclic — when g is not a zero divisor, the Koszul algebra of g
// is a polynomial resolution of R/(g).
var KoszulAcyclic = koszulAcyclicThm{family.Add(registry.ProofEntry{
	Name: "KoszulAcyclic",
	Key:  "prop_abdeea6e6da34b28",
	Reading: "That g is no zero divisor is read in degree 1 only, through KoszulCycleDegreeOne; " +
		"every other conjunct holds for every g. At a unit g the algebra resolves the zero ring; " +
		"over the zero ring every algebra is one point and every conjunct holds.",
	Deps: []registry.EntryLike{
		simplicial_ring.PolynomialResolution,
		simplicial_module.AcyclicAugmentation,
		KoszulAugmented,
		KoszulPolynomialAlgebra,
		simplicial_ring.PolynomialAlgebraSimplicialModule,
		KoszulDegreeZero,
		KoszulMooreTerms,
		KoszulCycleDivisible,
		KoszulCycleDegreeOne,
		KoszulPreimage,
		simplicial_module.MooreComplexChain,
		simplicial_module.MooreComplexDef,
		chain_complex.CyclesDef,
		chain_complex.BoundariesDef,
		chain_complex.BoundariesSubsetCycles,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀g:A.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"comm_ring_on(R)",
			"g ∈ R.carrier",
			"∀a:A. a ∈ R.carrier ∧ R.mul(g, a) = R.zero ⇒ a = R.zero",
		},
		Conclusion: "polynomial_resolution(R, " +
			"    koszul_names⟨U:U⟩, " +
			"    koszul_face(R, g), " +
			"    λn:num. koszul_degeneracy(R), " +
			"    koszul_quotient(R, g), " +
			"    koszul_projection(R, g), " +
			"    koszul_augmentation(R, g))",
	},
		"unfold PolynomialResolution and AcyclicAugmentation: the augmented algebra is "+
			"KoszulAugmented and its simplicial module PolynomialAlgebraSimplicialModule at "+
			"KoszulPolynomialAlgebra; the degree-0 conjuncts are KoszulDegreeZero. In degree n + 1 a "+
			"Moore boundary is a cycle (BoundariesSubsetCycles at MooreComplexChain); a Moore cycle is "+
			"Π_{n+1}·q (KoszulMooreTerms) with x_1 − g dividing q — KoszulCycleDivisible for n ≥ 1, "+
			"KoszulCycleDegreeOne at n = 0 — so Π_{n+1}·(x_1 − g)·q', d_0 of a Moore term (KoszulPreimage)"),
})}
