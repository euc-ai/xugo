// resolution_comparison.go — maps and homotopies between polynomial
// simplicial algebras over one ring, built one degree at a time. A map
// defined up to degree n extends to degree n + 1: on a generator that is
// a degeneracy of a generator below, the value is that degeneracy of the
// value already assigned, the same for every way of presenting it; on a
// nondegenerate generator it is a filler, in the target, of the sphere
// the faces already assigned determine; and an algebra map out of a free
// algebra is fixed by its values on the generators. A homotopy is built
// the same way, a nondegenerate generator filling a prism. So every
// augmented polynomial simplicial algebra maps into a resolution over a
// given map of the augmentation targets, any two maps agreeing after the
// target's augmentation are homotopic, and two resolutions of one
// algebra are homotopy equivalent over its identity.

package resolution_comparison

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/simplicial_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/chain_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/free_algebra"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/simplicial/kan_complex"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_homotopy"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_module"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_set"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Maps and homotopies up to a degree, and the nondegenerate generators
// ---------------------------------------------------------------------------

// PartialSimplicialAlgebraMap — `partial_simplicial_algebra_map(R, X, d,
// s, Y, d', s', n, F)`: between two polynomial simplicial algebras over
// R, F is a simplicial algebra map up to degree n — every F(k) with
// k ≤ n an algebra map over R from the free algebra on X(k) to the free
// algebra on Y(k), commuting with every face from degree k + 1 and every
// degeneracy into degree k + 1 for k + 1 ≤ n.
var PartialSimplicialAlgebraMap = partialSimplicialAlgebraMapThm{family.DefineStructure(registry.DefEntry{
	Name:  "PartialSimplicialAlgebraMap",
	Key:   "prop_eb0e3f79bdacf2e9",
	Const: "partial_simplicial_algebra_map",
	Type: "ring_ops(A) → " +
		"(num → set(U)) → " +
		"(num → num → U → U) → " +
		"(num → num → U → U) → " +
		"(num → set(U)) → " +
		"(num → num → U → U) → " +
		"(num → num → U → U) → " +
		"num → " +
		"(num → U → U) → " +
		"bool",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀X:(num → set(U)). " +
			"∀d s:(num → num → U → U). " +
			"∀Y:(num → set(U)). " +
			"∀d' s':(num → num → U → U). " +
			"∀n:num. " +
			"∀F:(num → U → U). " +
			"    partial_simplicial_algebra_map(R, X, d, s, Y, d', s', n, F) ⇔ " +
			"    polynomial_simplicial_algebra(R, X, d, s) ∧ " +
			"    polynomial_simplicial_algebra(R, Y, d', s') ∧ " +
			"    (∀k:num. k ≤ n ⇒ universe_algebra_homomorphism(R, X(k), Y(k), F(k))) ∧ " +
			"    (∀k i:num. ∀u:U. " +
			"        u ∈ universe_algebra(R, X(k + 1)) ∧ k + 1 ≤ n ∧ i ≤ k + 1 ⇒ " +
			"        F(k, d(k + 1, i, u)) = d'(k + 1, i, F(k + 1, u))) ∧ " +
			"    (∀k i:num. ∀u:U. " +
			"        u ∈ universe_algebra(R, X(k)) ∧ k + 1 ≤ n ∧ i ≤ k ⇒ " +
			"        F(k + 1, s(k, i, u)) = s'(k, i, F(k, u)))",
	},
	Reading: "At n = 0 the predicate asks only that F(0) be an algebra map from the " +
		"free algebra on X(0) to the free algebra on Y(0): no identity reads a face out of " +
		"degree 0. F(k) is read only for k ≤ n and only on the free algebra on X(k): a " +
		"function agreeing with F there is a partial map up to n as well, and an extension to " +
		"degree n + 1 chooses F(n + 1) freely. A simplicial algebra map is a partial map up " +
		"to every degree, and partial maps that agree below their degrees assemble into one.",
})}

// PartialSimplicialAlgebraHomotopy —
// `partial_simplicial_algebra_homotopy(R, X, d, s, Y, d', s', F, G, n,
// H)`: between two simplicial algebra maps F and G of polynomial
// simplicial algebras over R, H is a simplicial algebra homotopy from F
// to G up to degree n — every H(k, j) with j ≤ k ≤ n an algebra map over
// R from the free algebra on X(k) to the free algebra on Y(k + 1), with
// May's identities of simplicial_homotopy wherever every component they
// read lies in degree n or below.
var PartialSimplicialAlgebraHomotopy = partialSimplicialAlgebraHomotopyThm{family.DefineStructure(registry.DefEntry{
	Name:  "PartialSimplicialAlgebraHomotopy",
	Key:   "prop_dc9763c1afde34ac",
	Const: "partial_simplicial_algebra_homotopy",
	Type: "ring_ops(A) → " +
		"(num → set(U)) → " +
		"(num → num → U → U) → " +
		"(num → num → U → U) → " +
		"(num → set(U)) → " +
		"(num → num → U → U) → " +
		"(num → num → U → U) → " +
		"(num → U → U) → " +
		"(num → U → U) → " +
		"num → " +
		"(num → num → U → U) → " +
		"bool",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀X:(num → set(U)). " +
			"∀d s:(num → num → U → U). " +
			"∀Y:(num → set(U)). " +
			"∀d' s':(num → num → U → U). " +
			"∀F G:(num → U → U). " +
			"∀n:num. " +
			"∀H:(num → num → U → U). " +
			"    partial_simplicial_algebra_homotopy(R, X, d, s, Y, d', s', F, G, n, H) ⇔ " +
			"    simplicial_algebra_map(R, X, d, s, Y, d', s', F) ∧ " +
			"    simplicial_algebra_map(R, X, d, s, Y, d', s', G) ∧ " +
			"    (∀k j:num. k ≤ n ∧ j ≤ k ⇒ universe_algebra_homomorphism(R, X(k), Y(k + 1), H(k, j))) ∧ " +
			"    (∀k:num. ∀u:U. " +
			"        u ∈ universe_algebra(R, X(k)) ∧ k ≤ n ⇒ d'(k + 1, 0, H(k, 0, u)) = F(k, u)) ∧ " +
			"    (∀k:num. ∀u:U. " +
			"        u ∈ universe_algebra(R, X(k)) ∧ k ≤ n ⇒ d'(k + 1, k + 1, H(k, k, u)) = G(k, u)) ∧ " +
			"    (∀k i j:num. ∀u:U. " +
			"        u ∈ universe_algebra(R, X(k + 1)) ∧ k + 1 ≤ n ∧ i < j ∧ j ≤ k + 1 ⇒ " +
			"        d'(k + 2, i, H(k + 1, j, u)) = H(k, j - 1, d(k + 1, i, u))) ∧ " +
			"    (∀k j:num. ∀u:U. " +
			"        u ∈ universe_algebra(R, X(k)) ∧ k ≤ n ∧ j < k ⇒ " +
			"        d'(k + 1, j + 1, H(k, j + 1, u)) = d'(k + 1, j + 1, H(k, j, u))) ∧ " +
			"    (∀k i j:num. ∀u:U. " +
			"        u ∈ universe_algebra(R, X(k + 1)) ∧ k + 1 ≤ n ∧ j + 1 < i ∧ i ≤ k + 2 ⇒ " +
			"        d'(k + 2, i, H(k + 1, j, u)) = H(k, j, d(k + 1, i - 1, u))) ∧ " +
			"    (∀k i j:num. ∀u:U. " +
			"        u ∈ universe_algebra(R, X(k)) ∧ k + 1 ≤ n ∧ i ≤ j ∧ j ≤ k ⇒ " +
			"        s'(k + 1, i, H(k, j, u)) = H(k + 1, j + 1, s(k, i, u))) ∧ " +
			"    (∀k i j:num. ∀u:U. " +
			"        u ∈ universe_algebra(R, X(k)) ∧ k + 1 ≤ n ∧ j < i ∧ i ≤ k + 1 ⇒ " +
			"        s'(k + 1, i, H(k, j, u)) = H(k + 1, j, s(k, i - 1, u)))",
	},
	Reading: "F and G are whole simplicial algebra maps: a homotopy is built between two maps " +
		"already in hand, and its degree-n components read F and G in degree n only. At n = 0 the " +
		"predicate asks one algebra map H(0, 0) into degree 1 whose 0-th face is F(0) and whose " +
		"1-st face is G(0). H(k, j) is read for j ≤ k ≤ n and on the free algebra on X(k) only.",
})}

// partialSimplicialAlgebraHomotopyPrismDef —
// `partial_simplicial_algebra_homotopy_prism(R, X, d, s, Y, d', s', F, G,
// n, H, u, j, w)`: w(0), …, w(j − 1) are the first j simplices of the
// prism over the (n + 1)-simplex u that extends H one degree — (n + 2)-
// simplices of the target meeting every identity May's homotopy asks of
// the components H(n + 1, l, u), l < j, that reads only F and G in
// degree n + 1, H in degree n and w(0), …, w(j − 1): the 0-th face of
// w(0) is F(n + 1, u), the last face of w(n + 1) is G(n + 1, u), the
// faces below l of w(l) and those above l + 1 are H in degree n at the
// faces of u, and w(l) and w(l + 1) share their (l + 1)-th face.
var partialSimplicialAlgebraHomotopyPrismDef = partialSimplicialAlgebraHomotopyPrismDefThm{family.Define(registry.DefEntry{
	Name:  "partialSimplicialAlgebraHomotopyPrismDef",
	Key:   "prop_3d78f759d8bb1f9",
	Const: "partial_simplicial_algebra_homotopy_prism",
	Type: "ring_ops(A) → " +
		"(num → set(U)) → " +
		"(num → num → U → U) → " +
		"(num → num → U → U) → " +
		"(num → set(U)) → " +
		"(num → num → U → U) → " +
		"(num → num → U → U) → " +
		"(num → U → U) → " +
		"(num → U → U) → " +
		"num → " +
		"(num → num → U → U) → " +
		"U → " +
		"num → " +
		"(num → U) → " +
		"bool",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀X:(num → set(U)). " +
			"∀d s:(num → num → U → U). " +
			"∀Y:(num → set(U)). " +
			"∀d' s':(num → num → U → U). " +
			"∀F G:(num → U → U). " +
			"∀n:num. " +
			"∀H:(num → num → U → U). " +
			"∀u:U. " +
			"∀j:num. " +
			"∀w:(num → U). " +
			"    partial_simplicial_algebra_homotopy_prism(R, X, d, s, Y, d', s', F, G, n, H, u, j, w) ⇔ " +
			"    (∀l:num. l < j ⇒ w(l) ∈ universe_algebra(R, Y(n + 2))) ∧ " +
			"    (0 < j ⇒ d'(n + 2, 0, w(0)) = F(n + 1, u)) ∧ " +
			"    (n + 1 < j ⇒ d'(n + 2, n + 2, w(n + 1)) = G(n + 1, u)) ∧ " +
			"    (∀i l:num. i < l ∧ l < j ⇒ d'(n + 2, i, w(l)) = H(n, l - 1, d(n + 1, i, u))) ∧ " +
			"    (∀l:num. l + 1 < j ⇒ d'(n + 2, l + 1, w(l + 1)) = d'(n + 2, l + 1, w(l))) ∧ " +
			"    (∀i l:num. l < j ∧ l + 1 < i ∧ i ≤ n + 2 ⇒ d'(n + 2, i, w(l)) = H(n, l, d(n + 1, i - 1, u)))",
	},
	Reading: "The prefix is read for j ≤ n + 2; at j = n + 2 it is the whole prism, the values " +
		"the components H(n + 1, 0, u), …, H(n + 1, n + 1, u) of an extension take. At j = 0 nothing " +
		"is asked. The (j + 1)-th face of w(j) is not among the conditions on the prefix of length j + " +
		"1 when j ≤ n: it is left open when w(j) is chosen, and d_{j+1} w(j + 1) = d_{j+1} w(j) then " +
		"gives w(j + 1) that face, so w(j) fills a horn missing it; w(n + 1) has every face fixed and " +
		"fills a sphere. At n = 1, over u in degree 2 and with the faces listed d_0, …, d_3 and · a " +
		"face left free: w(0) = (F(2, u), ·, H(1, 0, d_1 u), H(1, 0, d_2 u)), w(1) = (H(1, 0, d_0 u), " +
		"d_1 w(0), ·, H(1, 1, d_2 u)), w(2) = (H(1, 1, d_0 u), H(1, 1, d_1 u), d_2 w(1), G(2, u)).",
})}

// nondegenerateGeneratorDef — `nondegenerate_generator(R, X, s, n, u)`:
// u is the variable of a name of X(n) and, when n is m + 1, no degeneracy
// s(m, j) of the variable of a name of X(m) — a generator of degree n
// that is not a degeneracy of a generator. Every generator of degree 0 is
// one.
var nondegenerateGeneratorDef = nondegenerateGeneratorDefThm{family.Define(registry.DefEntry{
	Name:  "nondegenerateGeneratorDef",
	Key:   "prop_f96c663bed7c7780",
	Const: "nondegenerate_generator",
	Type:  "ring_ops(A) → (num → set(U)) → (num → num → U → U) → num → U → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀X:(num → set(U)). ∀s:(num → num → U → U). ∀n:num. ∀u:U. " +
			"    nondegenerate_generator(R, X, s, n, u) ⇔ " +
			"    u ∈ image(universe_algebra_var(R), X(n)) ∧ " +
			"    (∀m j:num. ∀v:U. " +
			"        n = m + 1 ∧ j ≤ m ∧ v ∈ image(universe_algebra_var(R), X(m)) ⇒ ¬(u = s(m, j, v)))",
	},
	Reading: "The generators are the variables, members of the algebra, and the condition is on " +
		"them, not on the names: a name is any member of U. Only degeneracies of generators are " +
		"excluded; a degeneracy keeps generators (polynomial_simplicial_algebra), and over a nonzero " +
		"ring a generator that is a degeneracy of any simplex is a degeneracy of a generator, a " +
		"degeneracy carrying the variables one-to-one to variables. Over the zero ring every variable is " +
		"the one point, so above degree 0 no generator is nondegenerate where the degree below has a name.",
})}

// ---------------------------------------------------------------------------
// Statement fragments
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// A map, one degree at a time
// ---------------------------------------------------------------------------

// PartialMapZero — when the target's augmentation is onto, an algebra
// map in degree 0 carries the source's augmentation to the target's
// along a ring map g over R.
var PartialMapZero = partialMapZeroThm{family.Add(registry.ProofEntry{
	Name: "PartialMapZero",
	Key:  "prop_7c241e812e7b9262",
	Reading: "Of the target's acyclicity only the degree-0 image is read, and of image(ε', " +
		"target's degree 0) = S'.carrier only ⊇: the value at each generator is a preimage, and " +
		"no face is read. g(f(a)) = f'(a) is load-bearing: FreeAlgebraEvalUnique compares ε' ∘ " +
		"F(0) with g ∘ ε as ring maps, ε' being one from the augmented target, and they agree " +
		"on the constants exactly because g ∘ f = f' on R's carrier — g is a map of algebras " +
		"over R. With S' the zero ring every member of the target's degree 0 is a preimage.",
	Deps: []registry.EntryLike{
		PartialSimplicialAlgebraMap,
		simplicial_ring.AugmentedPolynomialAlgebra,
		simplicial_ring.UniverseAlgebraEvalDef,
		simplicial_ring.UniverseAlgebraHomomorphismDef,
		free_algebra.FreeAlgebraEvalHom,
		free_algebra.FreeAlgebraEvalConst,
		free_algebra.FreeAlgebraEvalVar,
		free_algebra.FreeAlgebraConstHom,
		free_algebra.FreeAlgebraEvalUnique,
		ring_homomorphism.MapIn,
		simplicial_ring.UniverseEmbeddingHost,
		functions.InverseOnIn,
		functions.InverseOnRight,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀X:(num → set(U)). " +
			"∀d s:(num → num → U → U). " +
			"∀Y:(num → set(U)). " +
			"∀d' s':(num → num → U → U). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀ε:(U → B). " +
			"∀S':ring_ops(C). " +
			"∀f':(A → C). " +
			"∀ε':(U → C). " +
			"∀g:(B → C).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"augmented_polynomial_algebra(R, X, d, s, S, f, ε)",
			"augmented_polynomial_algebra(R, Y, d', s', S', f', ε')",
			"image(ε', universe_algebra(R, Y(0))) = S'.carrier",
			"ring_homomorphism(S, S', g)",
			"∀a:A. a ∈ R.carrier ⇒ g(f(a)) = f'(a)",
		},
		Conclusion: "∃F:(num → U → U). " +
			"    partial_simplicial_algebra_map(R, X, d, s, Y, d', s', 0, F) ∧ " +
			"    (∀x:U. x ∈ universe_algebra(R, X(0)) ⇒ ε'(F(0, x)) = g(ε(x)))",
	},
		"for each name x of X(0), g(ε(var x)) lies in the carrier of S' (ε and g are ring maps, MapIn), "+
			"hence in image(ε', universe_algebra(R, Y(0))). Take p_x = inverse_on(universe_algebra(R, "+
			"Y(0)), ε', g(ε(universe_algebra_var(R, x)))); it lies in the target algebra and ε'(p_x) = "+
			"g(ε(var x)) (InverseOnIn, InverseOnRight). F(0) := the evaluation of the free algebra on X(0) "+
			"in the ring universe_algebra_ring(R, Y(0)) with the constants as coefficients and x ↦ p_x is "+
			"an algebra map (FreeAlgebraEvalHom at FreeAlgebraConstHom, FreeAlgebraEvalConst). ε' ∘ F(0) "+
			"and g ∘ ε are ring maps from the free algebra on X(0) to S' agreeing on the constants, both "+
			"f', and on the variables (FreeAlgebraEvalVar), so they agree (FreeAlgebraEvalUnique)"),
})}

// PartialMapFacesFill — under a map up to degree n into a resolution
// that carries the augmentation along g, the images under F(n) of the
// faces of any (n + 1)-simplex of the source are the faces of an
// (n + 1)-simplex of the target.
var PartialMapFacesFill = partialMapFacesFillThm{family.Add(registry.ProofEntry{
	Name: "PartialMapFacesFill",
	Key:  "prop_aeb692f6fb011faf",
	Reading: "This is the value a nondegenerate generator takes, a filler of the sphere " +
		"the faces already assigned determine. Above degree 1 the sphere is compatible by " +
		"the face identities of F and fills by the target's acyclicity in positive degrees. " +
		"In degree 1 the sphere is two vertices with nothing to be compatible, and the " +
		"hypotheses ε' ∘ F(0) = g ∘ ε and ε d_0 = ε d_1 give them one image under ε', which " +
		"is what the degree-0 conjunct of acyclicity fills; g is read nowhere else.",
	Deps: []registry.EntryLike{
		PartialSimplicialAlgebraMap,
		simplicial_ring.PolynomialResolution,
		simplicial_ring.AugmentedPolynomialAlgebra,
		simplicial_module.SphereFillsInAcyclic,
		simplicial_module.EdgeFillsInAcyclic,
		simplicial_set.FaceFace,
		simplicial_set.FaceIn,
	},
	Build: family.Card(PartialSimplicialAlgebraMap.Statement(Statement{
		Binders: "∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀ε:(U → B). " +
			"∀S':ring_ops(C). " +
			"∀f':(A → C). " +
			"∀ε':(U → C). " +
			"∀g:(B → C). " +
			"∀u:U.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"augmented_polynomial_algebra(R, X, d, s, S, f, ε)",
			"polynomial_resolution(R, Y, d', s', S', f', ε')",
			"∀x:U. x ∈ universe_algebra(R, X(0)) ⇒ ε'(F(0, x)) = g(ε(x))",
			"u ∈ universe_algebra(R, X(n + 1))",
		},
		Conclusion: "∃w:U. " +
			"    w ∈ universe_algebra(R, Y(n + 1)) ∧ " +
			"    (∀i:num. i ≤ n + 1 ⇒ d'(n + 1, i, w) = F(n, d(n + 1, i, u)))",
	}),
		"n = 0: ε'(F(0, d_0 u)) = g(ε(d_0 u)) = g(ε(d_1 u)) = ε'(F(0, d_1 u)) by the "+
			"augmentation, so EdgeFillsInAcyclic gives the edge. n = m + 1: y(i) := F(m + 1, d(m "+
			"+ 2, i, u)) is a compatible sphere of (m + 1)-simplices — d'_i y(j) = F(m, d_i d_j "+
			"u) = F(m, d_{j−1} d_i u) = d'_{j−1} y(i) for i < j by the face identities of F and "+
			"FaceFace — and SphereFillsInAcyclic at the target's acyclic augmentation fills it"),
})}

// DegenerateGeneratorWellDefined — under a map up to degree n, a simplex
// of degree n + 1 presented as two degeneracies s_i(u) = s_j(v) of
// simplices of degree n has one value s'_i F(u) = s'_j F(v).
var DegenerateGeneratorWellDefined = degenerateGeneratorWellDefinedThm{family.Add(registry.ProofEntry{
	Name: "DegenerateGeneratorWellDefined",
	Key:  "prop_a24578445058ce64",
	Reading: "u and v are any simplices of degree n, generators or not: the value a " +
		"degenerate generator takes in degree n + 1, s'_j of the value at the generator it is " +
		"a degeneracy of, does not depend on the presentation. Only the identities of F with " +
		"the degeneracies into degree n are read, and none in degree 0, where s_0 is one-to-one.",
	Deps: []registry.EntryLike{
		PartialSimplicialAlgebraMap,
		simplicial_set.FaceDegeneracyBelow,
		simplicial_set.FaceDegeneracyAbove,
		simplicial_set.FaceDegeneracyEqual,
		simplicial_set.FaceDegeneracyNext,
		simplicial_set.DegeneracyDegeneracy,
		simplicial_set.FaceIn,
	},
	Build: family.Card(PartialSimplicialAlgebraMap.Statement(Statement{
		Binders: "∀i j:num. ∀u v:U.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"i ≤ n",
			"j ≤ n",
			"u ∈ universe_algebra(R, X(n))",
			"v ∈ universe_algebra(R, X(n))",
			"s(n, i, u) = s(n, j, v)",
		},
		Conclusion: "s'(n, i, F(n, u)) = s'(n, j, F(n, v))",
	}),
		"i = j: u = d_i s_i u = d_i s_i v = v (FaceDegeneracyEqual). i < j, so n = m + 1: u = d_i s_j v "+
			"= s_{j−1} d_i v (FaceDegeneracyBelow) and v = d_{j+1} s_i u = s_i d_j u (FaceDegeneracyAbove); "+
			"with z := d_i v, d_j u = d_j s_{j−1} z = z (FaceDegeneracyNext), so u = s_{j−1} z and v = s_i "+
			"z. F moves across the degeneracies out of degree m, so the two values are s'_i s'_{j−1} F(m, "+
			"z) and s'_j s'_i F(m, z), equal by DegeneracyDegeneracy; i > j is symmetric"),
})}

// DegenerateGeneratorFaces — under a map up to degree n, the degeneracy
// s'_j F(v) has the faces that F in degree n assigns to the faces of
// s_j(v): the value a degenerate generator takes meets the face
// identities.
var DegenerateGeneratorFaces = degenerateGeneratorFacesThm{family.Add(registry.ProofEntry{
	Name: "DegenerateGeneratorFaces",
	Key:  "prop_3674db084bea3217",
	Reading: "For i ∈ {j, j + 1} no identity of F is read; otherwise F's face identity out of degree " +
		"n and its degeneracy identity into degree n are, so at n = 0 the card is d_0 s_0 = d_1 s_0 = id.",
	Deps: []registry.EntryLike{
		PartialSimplicialAlgebraMap,
		simplicial_set.FaceDegeneracyBelow,
		simplicial_set.FaceDegeneracyAbove,
		simplicial_set.FaceDegeneracyEqual,
		simplicial_set.FaceDegeneracyNext,
		simplicial_set.FaceIn,
		simplicial_set.DegeneracyIn,
	},
	Build: family.Card(PartialSimplicialAlgebraMap.Statement(Statement{
		Binders: "∀i j:num. ∀v:U.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"j ≤ n",
			"i ≤ n + 1",
			"v ∈ universe_algebra(R, X(n))",
		},
		Conclusion: "d'(n + 1, i, s'(n, j, F(n, v))) = F(n, d(n + 1, i, s(n, j, v)))",
	}),
		"i = j and i = j + 1: both sides are F(n, v) (FaceDegeneracyEqual, FaceDegeneracyNext in the "+
			"target and in the source). i < j, so n = m + 1: d'_i s'_j = s'_{j−1} d'_i in the target and d_i "+
			"s_j = s_{j−1} d_i in the source (FaceDegeneracyBelow), and F moves across d_i out of degree n "+
			"and across s_{j−1} into it by its identities; i > j + 1 the same with FaceDegeneracyAbove"),
})}

// PartialMapExtends — a map up to degree n into a resolution that carries
// the augmentation along g extends to a map up to degree n + 1 agreeing
// with it up to degree n.
var PartialMapExtends = partialMapExtendsThm{family.Add(registry.ProofEntry{
	Name: "PartialMapExtends",
	Key:  "prop_bd50392cde755215",
	Reading: "The hypotheses are what the induction carries: the map up to degree n and its " +
		"compatibility with the augmentations in degree 0, read only to fill the edges in degree 1. " +
		"The source need not be a resolution; that its degeneracies carry generators to generators, " +
		"part of polynomial_simplicial_algebra, is what lets a degenerate generator take a forced value.",
	Deps: []registry.EntryLike{
		PartialSimplicialAlgebraMap,
		PartialMapFacesFill,
		DegenerateGeneratorWellDefined,
		DegenerateGeneratorFaces,
		nondegenerateGeneratorDef,
		simplicial_ring.PolynomialSimplicialAlgebra,
		simplicial_ring.UniverseAlgebraEvalDef,
		simplicial_ring.UniverseAlgebraHomomorphismDef,
		free_algebra.FreeAlgebraEvalHom,
		free_algebra.FreeAlgebraEvalConst,
		free_algebra.FreeAlgebraEvalVar,
		free_algebra.FreeAlgebraConstHom,
		free_algebra.FreeAlgebraEvalUnique,
		simplicial_ring.UniverseEmbeddingHost,
	},
	Build: family.Card(PartialSimplicialAlgebraMap.Statement(Statement{
		Binders: "∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀ε:(U → B). " +
			"∀S':ring_ops(C). " +
			"∀f':(A → C). " +
			"∀ε':(U → C). " +
			"∀g:(B → C).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"augmented_polynomial_algebra(R, X, d, s, S, f, ε)",
			"polynomial_resolution(R, Y, d', s', S', f', ε')",
			"∀x:U. x ∈ universe_algebra(R, X(0)) ⇒ ε'(F(0, x)) = g(ε(x))",
		},
		Conclusion: "∃F':(num → U → U). " +
			"    partial_simplicial_algebra_map(R, X, d, s, Y, d', s', n + 1, F') ∧ " +
			"    (∀k:num. ∀u:U. k ≤ n ∧ u ∈ universe_algebra(R, X(k)) ⇒ F'(k, u) = F(k, u))",
	}),
		"F'(k) := F(k) for k ≤ n. On a name x of X(n + 1) put θ(x) := s'(n, j, F(n, var y)) when "+
			"var x = s(n, j, var y) for some j ≤ n and name y of X(n), any such pair "+
			"(DegenerateGeneratorWellDefined), and otherwise — var x a nondegenerate generator — a "+
			"filler of the faces F(n, d(n + 1, i, var x)) (PartialMapFacesFill); F'(n + 1) is the "+
			"evaluation with values θ and the constants as coefficients, an algebra map "+
			"(FreeAlgebraEvalHom, FreeAlgebraEvalConst). The face identities into degree n hold on the "+
			"generators — DegenerateGeneratorFaces at a degenerate one, the filler at a nondegenerate "+
			"one — and the degeneracy identities out of degree n hold on the generators, s(n, j, var "+
			"y) being a generator by the closure in polynomial_simplicial_algebra and its value s'(n, "+
			"j, F(n, var y)) by DegenerateGeneratorWellDefined; both sides of each are algebra maps, "+
			"so they agree on the free algebras (FreeAlgebraEvalUnique)"),
})}

// PartialMapsAssemble — maps up to every degree, each agreeing with the
// one before it below that one's degree, assemble along the diagonal into
// a simplicial algebra map.
var PartialMapsAssemble = partialMapsAssembleThm{family.Add(registry.ProofEntry{
	Name: "PartialMapsAssemble",
	Key:  "prop_f9f64bab116a0506",
	Reading: "Only the agreement Φ(k + 1, k) = Φ(k, k) on degree k is " +
		"read; the hypothesis for every n ≥ k is more than the assembly needs.",
	Deps: []registry.EntryLike{
		PartialSimplicialAlgebraMap,
		simplicial_ring.SimplicialAlgebraMap,
		simplicial_ring.PolynomialSimplicialAlgebra,
		simplicial_set.SimplicialMap,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀X:(num → set(U)). " +
			"∀d s:(num → num → U → U). " +
			"∀Y:(num → set(U)). " +
			"∀d' s' Φ:(num → num → U → U).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"∀n:num. partial_simplicial_algebra_map(R, X, d, s, Y, d', s', n, Φ(n))",
			"∀n k:num. ∀u:U. k ≤ n ∧ u ∈ universe_algebra(R, X(k)) ⇒ Φ(n + 1, k, u) = Φ(n, k, u)",
		},
		Conclusion: "simplicial_algebra_map(R, X, d, s, Y, d', s', λk:num. Φ(k, k))",
	},
		"by induction Φ(n, k) = Φ(k, k) on the free algebra on X(k) for k ≤ n; the identities of "+
			"the diagonal between degrees k and k + 1 are those of Φ(k + 1), whose component in degree "+
			"k is Φ(k, k) there, and the two polynomial simplicial algebras are part of Φ(0)'s predicate"),
})}

// ComparisonMapExists — an augmented polynomial simplicial algebra maps
// into a resolution over every map g of algebras over R between the
// augmentation targets: some simplicial algebra map F has ε' ∘ F(0) =
// g ∘ ε.
var ComparisonMapExists = comparisonMapExistsThm{family.Add(registry.ProofEntry{
	Name: "ComparisonMapExists",
	Key:  "prop_52d5ef9ddf35edc0",
	Reading: "The source is only augmented: what makes it free enough is that its degeneracies carry " +
		"generators to generators, part of polynomial_simplicial_algebra. The target's acyclicity is " +
		"used whole — ε' onto in degree 0, the degree-0 kernel for the edges in degree 1, the Moore " +
		"complex exact above. With the source constant, X(n) = X(0) and every face and degeneracy the " +
		"identity, every generator above degree 0 is degenerate and F(n) is the n-fold degeneracy of F(0).",
	Deps: []registry.EntryLike{
		PartialMapZero,
		PartialMapExtends,
		PartialMapsAssemble,
		simplicial_ring.PolynomialResolution,
		simplicial_ring.AugmentedPolynomialAlgebra,
		simplicial_module.AcyclicAugmentation,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀X:(num → set(U)). " +
			"∀d s:(num → num → U → U). " +
			"∀Y:(num → set(U)). " +
			"∀d' s':(num → num → U → U). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀ε:(U → B). " +
			"∀S':ring_ops(C). " +
			"∀f':(A → C). " +
			"∀ε':(U → C). " +
			"∀g:(B → C).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"augmented_polynomial_algebra(R, X, d, s, S, f, ε)",
			"polynomial_resolution(R, Y, d', s', S', f', ε')",
			"ring_homomorphism(S, S', g)",
			"∀a:A. a ∈ R.carrier ⇒ g(f(a)) = f'(a)",
		},
		Conclusion: "∃F:(num → U → U). " +
			"    simplicial_algebra_map(R, X, d, s, Y, d', s', F) ∧ " +
			"    (∀x:U. x ∈ universe_algebra(R, X(0)) ⇒ ε'(F(0, x)) = g(ε(x)))",
	},
		"PartialMapZero starts a sequence of partial maps (ε' onto S'.carrier is a conjunct "+
			"of the acyclic augmentation), PartialMapExtends continues it by recursion on the "+
			"degree, each step chosen by ε and agreeing with the last below its degree, so ε' ∘ "+
			"F(0) = g ∘ ε persists; PartialMapsAssemble takes the diagonal (Iyengar, "+
			"André–Quillen homology of commutative algebras: a map out of a simplicial algebra "+
			"free on degeneracy-closed generators lifts through a resolution)"),
})}

// MapDeterminedByNondegenerateGenerators — two simplicial algebra maps
// out of a polynomial simplicial algebra that agree on its nondegenerate
// generators agree on every simplex.
var MapDeterminedByNondegenerateGenerators = mapDeterminedByNondegenerateGeneratorsThm{family.Add(registry.ProofEntry{
	Name: "MapDeterminedByNondegenerateGenerators",
	Key:  "prop_4ec722c60443b0ea",
	Reading: "Every generator of degree 0 is nondegenerate, so the hypothesis " +
		"includes agreement on the generators of degree 0. A degenerate generator " +
		"s_j(v) takes s'_j of the value at v under both maps, which is why the values " +
		"elsewhere are forced: the source is free on its nondegenerate generators.",
	Deps: []registry.EntryLike{
		nondegenerateGeneratorDef,
		simplicial_ring.SimplicialAlgebraMap,
		simplicial_ring.PolynomialSimplicialAlgebra,
		simplicial_set.MapDegeneracy,
		free_algebra.FreeAlgebraEvalUnique,
		simplicial_ring.UniverseEmbeddingHost,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀X:(num → set(U)). " +
			"∀d s:(num → num → U → U). " +
			"∀Y:(num → set(U)). " +
			"∀d' s':(num → num → U → U). " +
			"∀F G:(num → U → U). " +
			"∀n:num. " +
			"∀u:U.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"simplicial_algebra_map(R, X, d, s, Y, d', s', F)",
			"simplicial_algebra_map(R, X, d, s, Y, d', s', G)",
			"∀m:num. ∀v:U. nondegenerate_generator(R, X, s, m, v) ⇒ F(m, v) = G(m, v)",
			"u ∈ universe_algebra(R, X(n))",
		},
		Conclusion: "F(n, u) = G(n, u)",
	},
		"induction on n: in degree 0 the two algebra maps agree on the constants and on "+
			"the generators, so on the free algebra (FreeAlgebraEvalUnique); in degree n + "+
			"1 a generator is nondegenerate, or s(n, j, v) with v a generator of degree n, "+
			"where F(n + 1, s(n, j, v)) = s'(n, j, F(n, v)) = s'(n, j, G(n, v)) = G(n + 1, "+
			"s(n, j, v)) (MapDegeneracy and the induction), and FreeAlgebraEvalUnique again"),
})}

// ---------------------------------------------------------------------------
// A homotopy, one degree at a time
// ---------------------------------------------------------------------------

// PartialHomotopyZero — two simplicial algebra maps into a polynomial
// simplicial algebra whose degree-0 fibres under ε' are the cosets of the
// Moore boundaries, and which agree after ε' in degree 0, are joined in
// degree 0 by an algebra map into the edges.
var PartialHomotopyZero = partialHomotopyZeroThm{family.Add(registry.ProofEntry{
	Name: "PartialHomotopyZero",
	Key:  "prop_805a75508f97fca9",
	Reading: "Of the target's acyclicity only the degree-0 kernel is asked, as " +
		"acyclic_augmentation states it, and of it only one direction is read, ε'(p) = ε'(q) " +
		"⇒ p − q ∈ d'_0(moore_terms(1)): F(0, var x) and G(0, var x) have one image under ε', " +
		"so their difference is d'_0 of a Moore 1-simplex, which makes an edge between them. " +
		"ε' is an arbitrary function, neither a ring map nor onto. With ε' constant the " +
		"kernel condition says every difference is a Moore boundary. The edge w_x = v + s'_0 " +
		"G(0, var x) has d'_0 = F and d'_1 = G: it runs from F to G, May's convention at n = 0.",
	Deps: []registry.EntryLike{
		PartialSimplicialAlgebraHomotopy,
		simplicial_ring.SimplicialAlgebraMap,
		simplicial_ring.PolynomialSimplicialAlgebra,
		simplicial_ring.UniverseAlgebraEvalDef,
		simplicial_module.MooreComplexDef,
		simplicial_module.MooreTermsDef,
		chain_complex.BoundariesDef,
		simplicial_set.FaceDegeneracyEqual,
		simplicial_set.FaceDegeneracyNext,
		module_homomorphism.HomAdd,
		free_algebra.FreeAlgebraEvalHom,
		free_algebra.FreeAlgebraEvalVar,
		free_algebra.FreeAlgebraEvalUnique,
		simplicial_ring.UniverseEmbeddingHost,
		simplicial_ring.PolynomialAlgebraSimplicialModule,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀X:(num → set(U)). " +
			"∀d s:(num → num → U → U). " +
			"∀Y:(num → set(U)). " +
			"∀d' s':(num → num → U → U). " +
			"∀F G:(num → U → U). " +
			"∀ε':(U → C).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"simplicial_algebra_map(R, X, d, s, Y, d', s', F)",
			"simplicial_algebra_map(R, X, d, s, Y, d', s', G)",
			"∀p q:U. " +
				"    p ∈ universe_algebra(R, Y(0)) ∧ q ∈ universe_algebra(R, Y(0)) ⇒ " +
				"    (ε'(p) = ε'(q) ⇔ " +
				"        universe_algebra_module(R).add(p, universe_algebra_module(R).neg(q)) ∈ " +
				"        boundaries( " +
				"            moore_complex(universe_algebra_module(R), polynomial_simplicial_set(R, Y, d', s')), " +
				"            0))",
			"∀u:U. u ∈ universe_algebra(R, X(0)) ⇒ ε'(F(0, u)) = ε'(G(0, u))",
		},
		Conclusion: "∃H:(num → num → U → U). " +
			"    partial_simplicial_algebra_homotopy(R, X, d, s, Y, d', s', F, G, 0, H)",
	},
		"for a name x of X(0), F(0, var x) − G(0, var x) = d'_0 v with v a Moore 1-simplex, "+
			"d'_1 v = 0 (BoundariesDef at MooreComplexDef, MooreTermsDef), and w_x := v + s'_0 "+
			"G(0, var x) has d'_0 w_x = F(0, var x) and d'_1 w_x = G(0, var x), the faces "+
			"additive and d'_i s'_0 the identity (FaceDegeneracyEqual, FaceDegeneracyNext) — "+
			"EdgeFillsInAcyclic's construction; H(0, 0) is the evaluation with values w_x, an "+
			"algebra map into degree 1 (FreeAlgebraEvalHom), and d'_0 H(0, 0), F(0) and d'_1 "+
			"H(0, 0), G(0) are algebra maps agreeing on the generators (FreeAlgebraEvalUnique)"),
})}

// DegenerateGeneratorHomotopyWellDefined — under a homotopy up to degree
// n, a simplex of degree n + 1 presented as two degeneracies s_i(u) =
// s_k(v) of simplices of degree n has one value of the j-th homotopy
// component: s'_i H(j − 1)(u) where i < j and s'_{i+1} H(j)(u) where
// j ≤ i, read through either presentation.
var DegenerateGeneratorHomotopyWellDefined = degenerateGeneratorHomotopyWellDefinedThm{family.Add(registry.ProofEntry{
	Name: "DegenerateGeneratorHomotopyWellDefined",
	Key:  "prop_7978f2ea38d5bda8",
	Reading: "The two branches are the values May's degeneracy identities force on s_i(u): s'_i " +
		"h_{j−1} = h_j s_i for i < j and s'_{i+1} h_j = h_j s_i for j ≤ i. u and v are any simplices " +
		"of degree n; only the degeneracy identities of H into degree n are read, and none at n = 0, " +
		"where s_0 is one-to-one. At n = 1, s_0 y = s_1 y' forces y = y' = s_0 z, and the values at " +
		"j = 1 are s_0 s_1 H(0, 0, z) and s_2 s_0 H(0, 0, z), equal by s_0 s_1 = s_2 s_0.",
	Deps: []registry.EntryLike{
		PartialSimplicialAlgebraHomotopy,
		DegenerateGeneratorWellDefined,
		simplicial_set.FaceDegeneracyBelow,
		simplicial_set.FaceDegeneracyAbove,
		simplicial_set.FaceDegeneracyEqual,
		simplicial_set.FaceDegeneracyNext,
		simplicial_set.DegeneracyDegeneracy,
	},
	Build: family.Card(PartialSimplicialAlgebraHomotopy.Statement(Statement{
		Binders: "∀i k j:num. ∀u v:U.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"i ≤ n",
			"k ≤ n",
			"j ≤ n + 1",
			"u ∈ universe_algebra(R, X(n))",
			"v ∈ universe_algebra(R, X(n))",
			"s(n, i, u) = s(n, k, v)",
		},
		Conclusion: "COND(i < j, s'(n + 1, i, H(n, j - 1, u)), s'(n + 1, i + 1, H(n, j, u))) = " +
			"COND(k < j, s'(n + 1, k, H(n, j - 1, v)), s'(n + 1, k + 1, H(n, j, v)))",
	}),
		"i = k: u = v by FaceDegeneracyEqual. i < k, so n = m + 1: as in DegenerateGeneratorWellDefined "+
			"u = s_{k−1} z and v = s_i z with z := d_i v. In each of the cases j ≤ i, i < j ≤ k and k < j, "+
			"the degeneracy identities of H between degrees m and n carry both values to two composites of "+
			"two degeneracies of the target applied to H(m, ·, z) — s'_{i+1} s'_k and s'_{k+1} s'_{i+1} at "+
			"H(m, j, z); s'_i s'_k and s'_{k+1} s'_i at H(m, j − 1, z); s'_i s'_{k−1} and s'_k s'_i at H(m, "+
			"j − 2, z) — equal by DegeneracyDegeneracy; i > k is symmetric"),
})}

// PartialHomotopyPrismStart — under a homotopy up to degree n, every
// (n + 1)-simplex u of the source has the first simplex of its prism:
// an (n + 2)-simplex of the target with 0-th face F(n + 1, u) and faces
// i ≥ 2 the homotopy in degree n at the faces of u.
var PartialHomotopyPrismStart = partialHomotopyPrismStartThm{family.Add(registry.ProofEntry{
	Name: "PartialHomotopyPrismStart",
	Key:  "prop_15cbd396843d22cf",
	Reading: "w(0) fills the horn Λ^{n+2}_1: its 1-st face is left to w(1). A horn fills " +
		"in every simplicial module, so the target need only be a polynomial simplicial " +
		"algebra, part of the simplicial algebra map F; no acyclicity is read. The horn is " +
		"compatible using only d_0 h_0 = F and d_a h_0 = h_0 d_{a−1} (a ≥ 2) in degree n; at " +
		"n = 0 its one compatibility is d_0 H(0, 0, d_1 u) = F(0, d_1 u) = d_1 F(1, u).",
	Deps: []registry.EntryLike{
		PartialSimplicialAlgebraHomotopy,
		partialSimplicialAlgebraHomotopyPrismDef,
		simplicial_ring.SimplicialAlgebraMap,
		simplicial_ring.PolynomialAlgebraSimplicialModule,
		simplicial_module.HornFillerExists,
		kan_complex.KanFill,
		simplicial_set.FaceFamilyDef,
		simplicial_set.FacesCompatibleDef,
		simplicial_set.FacesFillerDef,
		kan_complex.HornFacesMember,
		simplicial_set.FaceFace,
		simplicial_set.MapFace,
	},
	Build: family.Card(PartialSimplicialAlgebraHomotopy.Statement(Statement{
		Binders: "∀u:U.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"u ∈ universe_algebra(R, X(n + 1))",
		},
		Conclusion: "∃z:U. " +
			"    partial_simplicial_algebra_homotopy_prism(R, X, d, s, Y, d', s', F, G, n, H, u, 1, λl:num. z)",
	}),
		"the faces y(0) := F(n + 1, u) and y(i) := H(n, 0, d(n + 1, i − 1, u)) for 2 ≤ i ≤ n + 2 "+
			"form a horn missing face 1, compatible: d'_0 y(b) = F(n, d_{b−1} u) = d'_{b−1} y(0) by the "+
			"0-th face identity of H in degree n and MapFace for F, and for 2 ≤ a < b, d'_a y(b) = H(n − "+
			"1, 0, d_{a−1} d_{b−1} u) = d'_{b−1} y(a) by the identity of H with the faces above j + 1 "+
			"and FaceFace. The target's underlying simplicial module (PolynomialAlgebraSimplicialModule) "+
			"is a Kan complex (HornFillerExists), so the horn fills (KanFill)"),
})}

// PartialHomotopyPrismStep — under a homotopy up to degree n into a
// resolution, a prefix w(0), …, w(j − 1) of the prism over u with
// 1 ≤ j ≤ n + 1 extends by one simplex w(j): for j ≤ n by filling a
// horn, for j = n + 1 by filling a sphere.
var PartialHomotopyPrismStep = partialHomotopyPrismStepThm{family.Add(registry.ProofEntry{
	Name: "PartialHomotopyPrismStep",
	Key:  "prop_580b1634798b5005",
	Reading: "Any prefix extends, not only one built by this card: the faces of w(j) are read " +
		"off the prefix and H. For j ≤ n they leave the (j + 1)-th face free, a horn the Kan " +
		"property of the target fills; for j = n + 1 they fix every face, a sphere of (n + " +
		"1)-simplices that only the exactness of the target's Moore complex in degree n + 1 fills. " +
		"The augmentation of the target is not read. The prefix is read only through the conditions " +
		"on w(j − 1), and for the pair of faces (j − 1, j), j ≥ 2, through those on w(j − 2); H's " +
		"shared-face identity d_l h_l = d_l h_{l−1} in degree n is load-bearing. At j = n + 1 the " +
		"pair (n + 1, n + 2) closes by d_{n+2} w(n) = H(n, n, d_{n+1} u) and d_{n+1} h_n = G.",
	Deps: []registry.EntryLike{
		PartialSimplicialAlgebraHomotopy,
		partialSimplicialAlgebraHomotopyPrismDef,
		simplicial_ring.PolynomialResolution,
		simplicial_ring.PolynomialAlgebraSimplicialModule,
		simplicial_module.HornFillerExists,
		simplicial_module.SphereFillsInAcyclic,
		kan_complex.KanFill,
		simplicial_set.FaceFamilyDef,
		simplicial_set.FacesCompatibleDef,
		simplicial_set.FacesFillerDef,
		kan_complex.HornFacesMember,
		simplicial_set.FaceFace,
		simplicial_set.MapFace,
	},
	Build: family.Card(PartialSimplicialAlgebraHomotopy.Statement(Statement{
		Binders: "∀S':ring_ops(C). ∀f':(A → C). ∀ε':(U → C). ∀u:U. ∀j:num. ∀w:(num → U).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"polynomial_resolution(R, Y, d', s', S', f', ε')",
			"u ∈ universe_algebra(R, X(n + 1))",
			"0 < j",
			"j ≤ n + 1",
			"partial_simplicial_algebra_homotopy_prism(R, X, d, s, Y, d', s', F, G, n, H, u, j, w)",
		},
		Conclusion: "∃z:U. " +
			"    partial_simplicial_algebra_homotopy_prism(R, " +
			"        X, " +
			"        d, " +
			"        s, " +
			"        Y, " +
			"        d', " +
			"        s', " +
			"        F, " +
			"        G, " +
			"        n, " +
			"        H, " +
			"        u, " +
			"        j + 1, " +
			"        λl:num. COND(l = j, z, w(l)))",
	}),
		"the faces of w(j) are y(i) := H(n, j − 1, d(n + 1, i, u)) for i < j, y(j) := d'(n + 2, "+
			"j, w(j − 1)), and y(i) := H(n, j, d(n + 1, i − 1, u)) for j + 1 < i ≤ n + 2, with y(n "+
			"+ 2) := G(n + 1, u) when j = n + 1. They are compatible: pairs inside one block by "+
			"FaceFace and the face identities of H in degree n, pairs with y(j) by FaceFace at w(j "+
			"− 1), its faces as the prefix fixes them, and d'_j H(n, j, ·) = d'_j H(n, j − 1, ·) in "+
			"degree n; y(n + 2) by the last face identity of H in degree n and MapFace for G. For j "+
			"≤ n the face j + 1 is missing and the horn fills (HornFillerExists, KanFill); for j = "+
			"n + 1 the sphere fills by SphereFillsInAcyclic at the target's acyclic augmentation"),
})}

// PartialHomotopyPrismFills — under a homotopy up to degree n into a
// resolution, every (n + 1)-simplex u of the source has a whole prism
// over it: (n + 2)-simplices w(0), …, w(n + 1) of the target with the
// faces May's identities ask of the homotopy components at u.
var PartialHomotopyPrismFills = partialHomotopyPrismFillsThm{family.Add(registry.ProofEntry{
	Name: "PartialHomotopyPrismFills",
	Key:  "prop_ed2eb4b0f94a0cfa",
	Reading: "The order w(0), …, w(n + 1) matters: each w(j) with j ≤ n fills the horn " +
		"Λ^{n+2}_{j+1}, its (j + 1)-th face left to w(j + 1), and the last, w(n + 1), fills a sphere, by " +
		"the exactness of the target's Moore complex in degree n + 1. This is the value a nondegenerate " +
		"generator takes under the homotopy. Only the last simplex reads acyclicity: into a target that " +
		"is merely a polynomial simplicial algebra every prism fills but for its final sphere.",
	Deps: []registry.EntryLike{
		PartialSimplicialAlgebraHomotopy,
		partialSimplicialAlgebraHomotopyPrismDef,
		PartialHomotopyPrismStart,
		PartialHomotopyPrismStep,
	},
	Build: family.Card(PartialSimplicialAlgebraHomotopy.Statement(Statement{
		Binders: "∀S':ring_ops(C). ∀f':(A → C). ∀ε':(U → C). ∀u:U.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"polynomial_resolution(R, Y, d', s', S', f', ε')",
			"u ∈ universe_algebra(R, X(n + 1))",
		},
		Conclusion: "∃w:(num → U). " +
			"    partial_simplicial_algebra_homotopy_prism(R, X, d, s, Y, d', s', F, G, n, H, u, n + 2, w)",
	}),
		"induction on j: PartialHomotopyPrismStart gives a prefix of length 1, "+
			"and PartialHomotopyPrismStep extends a prefix of length j to one of "+
			"length j + 1 for 1 ≤ j ≤ n + 1; the prefix of length n + 2 is the prism"),
})}

// PartialHomotopyExtends — a homotopy up to degree n between two maps
// into a resolution extends to a homotopy up to degree n + 1 agreeing
// with it up to degree n.
var PartialHomotopyExtends = partialHomotopyExtendsThm{family.Add(registry.ProofEntry{
	Name: "PartialHomotopyExtends",
	Key:  "prop_ef65ba54f2870a1",
	Reading: "The hypotheses are what the induction carries, the homotopy up to degree n " +
		"between two whole maps, and the target's acyclicity in positive degrees; the source " +
		"need not be a resolution, its degeneracies carrying generators to generators being " +
		"what lets a degenerate generator take forced values. At a degenerate generator the " +
		"forced values meet every face identity of degree n + 1 by the simplicial identities " +
		"and H's identities between degrees n − 1 and n alone; at a nondegenerate one all n " +
		"+ 2 components come from one prism, consecutive components sharing a face.",
	Deps: []registry.EntryLike{
		PartialSimplicialAlgebraHomotopy,
		PartialHomotopyPrismFills,
		partialSimplicialAlgebraHomotopyPrismDef,
		DegenerateGeneratorHomotopyWellDefined,
		nondegenerateGeneratorDef,
		simplicial_ring.PolynomialSimplicialAlgebra,
		simplicial_ring.UniverseAlgebraEvalDef,
		free_algebra.FreeAlgebraEvalHom,
		free_algebra.FreeAlgebraEvalConst,
		free_algebra.FreeAlgebraEvalVar,
		free_algebra.FreeAlgebraEvalUnique,
		simplicial_set.FaceDegeneracyBelow,
		simplicial_set.FaceDegeneracyAbove,
		simplicial_set.DegeneracyDegeneracy,
		simplicial_set.MapFace,
		simplicial_set.MapDegeneracy,
		simplicial_ring.UniverseEmbeddingHost,
	},
	Build: family.Card(PartialSimplicialAlgebraHomotopy.Statement(Statement{
		Binders: "∀S':ring_ops(C). ∀f':(A → C). ∀ε':(U → C).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"polynomial_resolution(R, Y, d', s', S', f', ε')",
		},
		Conclusion: "∃H':(num → num → U → U). " +
			"    partial_simplicial_algebra_homotopy(R, X, d, s, Y, d', s', F, G, n + 1, H') ∧ " +
			"    (∀k j:num. ∀u:U. k ≤ n ∧ j ≤ k ∧ u ∈ universe_algebra(R, X(k)) ⇒ H'(k, j, u) = H(k, j, u))",
	}),
		"H'(k) := H(k) for k ≤ n. On a name x of X(n + 1) with var x = s(n, i, var y) for a name y "+
			"of X(n), H'(n + 1, j) takes s'(n + 1, i, H(n, j − 1, var y)) for i < j and s'(n + 1, i + "+
			"1, H(n, j, var y)) for j ≤ i, any presentation (DegenerateGeneratorHomotopyWellDefined); "+
			"these meet the face identities by the simplicial identities and those of H, F and G "+
			"below. On a nondegenerate generator var x the values H'(n + 1, j, var x) are the "+
			"simplices w(j) of a prism over var x (PartialHomotopyPrismFills), whose conditions are "+
			"the identities of degree n + 1 at var x. Each H'(n + 1, j) is the evaluation with these "+
			"values, an algebra map (FreeAlgebraEvalHom, FreeAlgebraEvalConst), and every identity of "+
			"degree n + 1 is between algebra maps agreeing on the generators (FreeAlgebraEvalUnique)"),
})}

// PartialHomotopiesAssemble — homotopies up to every degree between two
// maps, each agreeing with the one before it below that one's degree,
// assemble along the diagonal into a simplicial algebra homotopy.
var PartialHomotopiesAssemble = partialHomotopiesAssembleThm{family.Add(registry.ProofEntry{
	Name: "PartialHomotopiesAssemble",
	Key:  "prop_eea6dc50e7f1f75c",
	Reading: "Only the agreement Ψ(k + 1, k, ·) = Ψ(k, k, ·) on degree k is " +
		"read; the hypothesis for every n ≥ k is more than the assembly needs.",
	Deps: []registry.EntryLike{
		PartialSimplicialAlgebraHomotopy,
		simplicial_ring.SimplicialAlgebraHomotopy,
		simplicial_homotopy.SimplicialHomotopy,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀X:(num → set(U)). " +
			"∀d s:(num → num → U → U). " +
			"∀Y:(num → set(U)). " +
			"∀d' s':(num → num → U → U). " +
			"∀F G:(num → U → U). " +
			"∀Ψ:(num → num → num → U → U).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"∀n:num. partial_simplicial_algebra_homotopy(R, X, d, s, Y, d', s', F, G, n, Ψ(n))",
			"∀n k j:num. ∀u:U. " +
				"    k ≤ n ∧ j ≤ k ∧ u ∈ universe_algebra(R, X(k)) ⇒ Ψ(n + 1, k, j, u) = Ψ(n, k, j, u)",
		},
		Conclusion: "simplicial_algebra_homotopy(R, X, d, s, Y, d', s', F, G, λk:num. Ψ(k, k))",
	},
		"by induction Ψ(n, k, j) = Ψ(k, k, j) on the free algebra on X(k) for j ≤ k ≤ n; every "+
			"identity of SimplicialHomotopy reads two consecutive degrees k and k + 1, where it is "+
			"an identity of Ψ(k + 1) whose components in degree k are those of the diagonal"),
})}

// ComparisonHomotopyExists — two simplicial algebra maps from a
// polynomial simplicial algebra into a resolution that agree after the
// resolution's augmentation in degree 0 are joined by a simplicial
// algebra homotopy.
var ComparisonHomotopyExists = comparisonHomotopyExistsThm{family.Add(registry.ProofEntry{
	Name: "ComparisonHomotopyExists",
	Key:  "prop_6e59208f3bf8ca97",
	Reading: "The source carries no augmentation: F and G need only agree after ε' on the " +
		"degree-0 algebra, ε' ∘ F(0) = ε' ∘ G(0), which is weaker than both carrying one " +
		"augmentation of the source along one map g. The homotopy runs from F to G; the hypothesis " +
		"is symmetric, so swapping the maps gives one from G to F, and homotopies exist both ways. " +
		"The degree-0 hypothesis and the kernel conjunct are read once, in degree 0; every higher " +
		"degree reads only the target's Kan property and the exactness of its Moore complex in " +
		"degree n + 1, so ε' onto, ε' a ring map and any augmentation of the source go unread there.",
	Deps: []registry.EntryLike{
		PartialHomotopyZero,
		PartialHomotopyExtends,
		PartialHomotopiesAssemble,
		simplicial_ring.PolynomialResolution,
		simplicial_module.AcyclicAugmentation,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀X:(num → set(U)). " +
			"∀d s:(num → num → U → U). " +
			"∀Y:(num → set(U)). " +
			"∀d' s':(num → num → U → U). " +
			"∀F G:(num → U → U). " +
			"∀S':ring_ops(C). " +
			"∀f':(A → C). " +
			"∀ε':(U → C).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"simplicial_algebra_map(R, X, d, s, Y, d', s', F)",
			"simplicial_algebra_map(R, X, d, s, Y, d', s', G)",
			"polynomial_resolution(R, Y, d', s', S', f', ε')",
			"∀u:U. u ∈ universe_algebra(R, X(0)) ⇒ ε'(F(0, u)) = ε'(G(0, u))",
		},
		Conclusion: "∃H:(num → num → U → U). simplicial_algebra_homotopy(R, X, d, s, Y, d', s', F, G, H)",
	},
		"PartialHomotopyZero at the degree-0 conjunct of the acyclic augmentation "+
			"starts a sequence of partial homotopies, PartialHomotopyExtends continues "+
			"it by recursion on the degree, each step chosen by ε and agreeing with the "+
			"last below its degree, and PartialHomotopiesAssemble takes the diagonal"),
})}

// ---------------------------------------------------------------------------
// Composites, and the comparison of two resolutions
// ---------------------------------------------------------------------------

// SimplicialAlgebraMapIdentity — the identity of a polynomial simplicial
// algebra is a simplicial algebra map.
var SimplicialAlgebraMapIdentity = simplicialAlgebraMapIdentityThm{family.Add(registry.ProofEntry{
	Name: "SimplicialAlgebraMapIdentity",
	Key:  "prop_ad3580d7b13dd8ca",
	Reading: "The universe hypothesis is not needed: the face " +
		"conjunct of polynomial_simplicial_algebra already makes " +
		"every free algebra on X(n) a ring, the target of d(n + 1, 0).",
	Deps: []registry.EntryLike{
		simplicial_ring.SimplicialAlgebraMap,
		simplicial_ring.PolynomialSimplicialAlgebra,
		simplicial_ring.UniverseAlgebraHomomorphismDef,
		simplicial_set.MapIdentity,
	},
	Build: family.Card(simplicial_ring.PolynomialSimplicialAlgebra.Statement(Statement{
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
		},
		Conclusion: "simplicial_algebra_map(R, X, d, s, X, d, s, λn:num. λu:U. u)",
	}),
		"the identity is a simplicial map of the free algebras (MapIdentity) and in each "+
			"degree the identity of a ring fixing the constants; the free algebra on X(n) is a "+
			"ring, as the target of the algebra map d(n + 1, 0) of polynomial_simplicial_algebra"),
})}

// SimplicialAlgebraMapCompose — the composite of two simplicial algebra
// maps is one.
var SimplicialAlgebraMapCompose = simplicialAlgebraMapComposeThm{family.Add(registry.ProofEntry{
	Name: "SimplicialAlgebraMapCompose",
	Key:  "prop_4b5185d4275d4c44",
	Deps: []registry.EntryLike{
		simplicial_ring.SimplicialAlgebraMap,
		simplicial_ring.UniverseAlgebraHomomorphismDef,
		simplicial_set.MapCompose,
	},
	Build: family.Card(simplicial_ring.SimplicialAlgebraMap.Statement(Statement{
		Binders: "∀Z:(num → set(U)). ∀d'' s'':(num → num → U → U). ∀G:(num → U → U).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"simplicial_algebra_map(R, Y, d', s', Z, d'', s'', G)",
		},
		Conclusion: "simplicial_algebra_map(R, X, d, s, Z, d'', s'', λn:num. λu:U. G(n, F(n, u)))",
	}),
		"the composite is a simplicial map (MapCompose); in each degree a "+
			"composite of ring homomorphisms is one, and each fixes the constants"),
})}

// SimplicialAlgebraMapAugmentationAt — a simplicial algebra map that
// carries one augmentation to another along g in degree 0 does so in
// every degree, the augmentations read through the 0-th faces.
var SimplicialAlgebraMapAugmentationAt = simplicialAlgebraMapAugmentationAtThm{family.Add(registry.ProofEntry{
	Name: "SimplicialAlgebraMapAugmentationAt",
	Key:  "prop_9bb3852e48520607",
	Reading: "No augmentation is asked to be a ring map or to coequalize the faces: the identity " +
		"is read off the 0-th faces, through which augmentation_at is defined, and F commutes with them.",
	Deps: []registry.EntryLike{
		simplicial_ring.SimplicialAlgebraMap,
		simplicial_ring.AugmentationAtDef,
		simplicial_set.MapFace,
		simplicial_set.FaceIn,
	},
	Build: family.Card(simplicial_ring.SimplicialAlgebraMap.Statement(Statement{
		Binders: "∀ε:(U → B). ∀ε':(U → C). ∀g:(B → C). ∀n:num. ∀u:U.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"∀x:U. x ∈ universe_algebra(R, X(0)) ⇒ ε'(F(0, x)) = g(ε(x))",
			"u ∈ universe_algebra(R, X(n))",
		},
		Conclusion: "augmentation_at(d', ε', n, F(n, u)) = g(augmentation_at(d, ε, n, u))",
	}),
		"induction on n: augmentation_at(d', ε', n + 1, F(n + 1, u)) = augmentation_at(d', "+
			"ε', n, d'(n + 1, 0, F(n + 1, u))) = augmentation_at(d', ε', n, F(n, d(n + 1, 0, "+
			"u))) (AugmentationAtDef, MapFace), and d(n + 1, 0, u) lies in degree n (FaceIn)"),
})}

// ComparisonMapHomotopyInverse — a simplicial algebra map between two
// resolutions of one algebra that carries one augmentation to the other
// has a homotopy inverse doing the same: both composites are homotopic to
// the identities.
var ComparisonMapHomotopyInverse = comparisonMapHomotopyInverseThm{family.Add(registry.ProofEntry{
	Name: "ComparisonMapHomotopyInverse",
	Key:  "prop_e5e41caca95e23fb",
	Reading: "Both resolutions are of the one R-algebra S through the one structure " +
		"map f. The homotopies are May homotopies in one direction, from the composites " +
		"to the identities, as ComparisonHomotopyExists gives one for any ordered pair " +
		"of maps agreeing after the augmentation; a consumer wanting them from the " +
		"identities to the composites takes them from ComparisonHomotopyExists directly.",
	Deps: []registry.EntryLike{
		ComparisonMapExists,
		ComparisonHomotopyExists,
		SimplicialAlgebraMapCompose,
		SimplicialAlgebraMapIdentity,
		simplicial_ring.PolynomialResolution,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀X:(num → set(U)). " +
			"∀d s:(num → num → U → U). " +
			"∀Y:(num → set(U)). " +
			"∀d' s':(num → num → U → U). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀ε ε':(U → B). " +
			"∀F:(num → U → U).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"polynomial_resolution(R, X, d, s, S, f, ε)",
			"polynomial_resolution(R, Y, d', s', S, f, ε')",
			"simplicial_algebra_map(R, X, d, s, Y, d', s', F)",
			"∀u:U. u ∈ universe_algebra(R, X(0)) ⇒ ε'(F(0, u)) = ε(u)",
		},
		Conclusion: "∃G:(num → U → U). ∃H K:(num → num → U → U). " +
			"    simplicial_algebra_map(R, Y, d', s', X, d, s, G) ∧ " +
			"    (∀v:U. v ∈ universe_algebra(R, Y(0)) ⇒ ε(G(0, v)) = ε'(v)) ∧ " +
			"    simplicial_algebra_homotopy(R, " +
			"        X, " +
			"        d, " +
			"        s, " +
			"        X, " +
			"        d, " +
			"        s, " +
			"        λn:num. λu:U. G(n, F(n, u)), " +
			"        «identity», " +
			"        H) ∧ " +
			"    simplicial_algebra_homotopy(R, " +
			"        Y, " +
			"        d', " +
			"        s', " +
			"        Y, " +
			"        d', " +
			"        s', " +
			"        λn:num. λv:U. F(n, G(n, v)), " +
			"        «identity», " +
			"        K)",
	},
		"G from ComparisonMapExists with the second resolution as source, the first as "+
			"target and g the identity of S, a ring map over R; G ∘ F and F ∘ G are simplicial "+
			"algebra maps (SimplicialAlgebraMapCompose) keeping the augmentations, so "+
			"ComparisonHomotopyExists joins each to the identity (SimplicialAlgebraMapIdentity)"),
})}

// ComparisonHomotopyEquivalence — two resolutions of one algebra are
// homotopy equivalent over its identity: simplicial algebra maps both
// ways that keep the augmentations, both composites homotopic to the
// identities.
var ComparisonHomotopyEquivalence = comparisonHomotopyEquivalenceThm{family.Add(registry.ProofEntry{
	Name: "ComparisonHomotopyEquivalence",
	Key:  "prop_94ddd06ed66f5d9c",
	Reading: "Both resolutions are of the one R-algebra S through the one structure map " +
		"f; the maps are algebra maps over R, so the equivalence is one of simplicial " +
		"R-algebras over S. The homotopies are May homotopies in one direction, from the " +
		"composites to the identities, as ComparisonHomotopyExists gives one for any " +
		"ordered pair of maps agreeing after the augmentation; a consumer wanting them from " +
		"the identities to the composites takes them from ComparisonHomotopyExists directly.",
	Deps: []registry.EntryLike{
		ComparisonMapExists,
		ComparisonMapHomotopyInverse,
		simplicial_ring.PolynomialResolution,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀X:(num → set(U)). " +
			"∀d s:(num → num → U → U). " +
			"∀Y:(num → set(U)). " +
			"∀d' s':(num → num → U → U). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀ε ε':(U → B).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"polynomial_resolution(R, X, d, s, S, f, ε)",
			"polynomial_resolution(R, Y, d', s', S, f, ε')",
		},
		Conclusion: "∃F G:(num → U → U). ∃H K:(num → num → U → U). " +
			"    simplicial_algebra_map(R, X, d, s, Y, d', s', F) ∧ " +
			"    simplicial_algebra_map(R, Y, d', s', X, d, s, G) ∧ " +
			"    (∀u:U. u ∈ universe_algebra(R, X(0)) ⇒ ε'(F(0, u)) = ε(u)) ∧ " +
			"    (∀v:U. v ∈ universe_algebra(R, Y(0)) ⇒ ε(G(0, v)) = ε'(v)) ∧ " +
			"    simplicial_algebra_homotopy(R, " +
			"        X, " +
			"        d, " +
			"        s, " +
			"        X, " +
			"        d, " +
			"        s, " +
			"        λn:num. λu:U. G(n, F(n, u)), " +
			"        «identity», " +
			"        H) ∧ " +
			"    simplicial_algebra_homotopy(R, " +
			"        Y, " +
			"        d', " +
			"        s', " +
			"        Y, " +
			"        d', " +
			"        s', " +
			"        λn:num. λv:U. F(n, G(n, v)), " +
			"        «identity», " +
			"        K)",
	},
		"F from ComparisonMapExists with g the identity of S, and ComparisonMapHomotopyInverse at F"),
})}
