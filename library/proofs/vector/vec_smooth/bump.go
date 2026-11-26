// bump.go — functions that are 1 on one ball and 0 outside a larger one,
// and partitions of unity on a compact set, all smooth. They are built
// from one function of one variable, 0 up to 0 and e^(−1/t) after, which
// has derivatives of every order although it is not analytic at 0.

package vec_smooth

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_exp_log"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean_topology"
	"github.com/euc-ai/xugo/library/registry"
)

// FlatFunctionSmooth — the function 0 for t ≤ 0 and e^(−1/t) for t > 0
// has derivatives of every order on ℝ.
var FlatFunctionSmooth = flatFunctionSmoothThm{family.Add(registry.ProofEntry{
	Name: "FlatFunctionSmooth",
	Key:  "prop_2158d33a65baffc5",
	Reading: "Every derivative is 0 at 0 and on the negative reals; the " +
		"function is the standard example of one that is smooth and not analytic.",
	Deps: []registry.EntryLike{real_exp_log.ExpDerivative, real_exp_log.ExpLowerBound},
	Build: family.Card(
		"∃D:(num → real → real). "+
			"    D(0) = (λt:real. COND(&0 < t, exp(-(&1 / t)), &0)) ∧ "+
			"    ∀k:num. ∀t:real. real_derivative_at(D(k), t, D(k + 1)(t))",
		"take D(k)(t) = pₖ(1/t)·e^(−1/t) for t > 0 and 0 otherwise, with p₀ = 1 and "+
			"pₖ₊₁(u) = u²·(pₖ(u) − pₖ'(u)) polynomials; for t ≠ 0 the derivative is the "+
			"product and chain rules (real_exp_log.ExpDerivative); at 0 the difference "+
			"quotient of D(k) is 0 on the left and (1/t)·pₖ(1/t)·e^(−1/t) on the right, "+
			"which tends to 0 because e^u outgrows every power of u (ExpLowerBound)"),
})}

// BumpFunction — a smooth function on ℝⁿ that is 1 on the closed ball of
// radius r about c, 0 at distance R or more from c, and between 0 and 1.
var BumpFunction = bumpFunctionThm{family.Add(registry.ProofEntry{
	Name: "BumpFunction",
	Key:  "prop_175cebf814ac09d1",
	Reading: "r < R is load-bearing: a function equal to 1 and to 0 at " +
		"the same distance is no function, and the gap is what the smooth " +
		"transition fills. At n = 0, ℝ⁰ is {0} and the constant 1 serves.",
	Deps: []registry.EntryLike{
		FlatFunctionSmooth,
		SmoothComposeReal,
		SmoothReciprocal,
		SmoothMul,
		SmoothAdd,
		SmoothSub,
		SmoothCoordinate,
		SmoothConst,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀c:(num → real). ∀r R:real.",
		Hypotheses: []string{
			"vec⟨n⟩(c)",
			"&0 < r",
			"r < R",
		},
		Conclusion: "∃φ:((num → real) → real). " +
			"    vec_smooth_on⟨n⟩({u:num → real | vec⟨n⟩(u)}, φ) ∧ " +
			"    (∀x:(num → real). &0 ≤ φ(x) ∧ φ(x) ≤ &1) ∧ " +
			"    (∀x:(num → real). vec⟨n⟩(x) ∧ ‖x - c‖_n ≤ r ⇒ φ(x) = &1) ∧ " +
			"    ∀x:(num → real). vec⟨n⟩(x) ∧ R ≤ ‖x - c‖_n ⇒ φ(x) = &0",
	},
		"with e the flat function and q(x) = Σ_{i<n} (x(i) − c(i))², a polynomial in the "+
			"coordinates and so smooth, φ = e(R² − q)/(e(R² − q) + e(q − r²)): the denominator has no "+
			"zero, one of the two arguments being positive (SmoothReciprocal), each e(…) is smooth "+
			"(FlatFunctionSmooth, SmoothComposeReal), and q ≤ r² kills the second term, R² ≤ q the first"),
})}

// SmoothPartitionOfUnity — a compact set of ℝⁿ covered by open sets has a
// smooth partition of unity subordinate to the cover: finitely many smooth
// functions, nonnegative, each with compact support in a member of the
// cover, summing to at most 1 everywhere and to 1 on the compact set.
var SmoothPartitionOfUnity = smoothPartitionOfUnityThm{family.Add(registry.ProofEntry{
	Name: "SmoothPartitionOfUnity",
	Key:  "prop_692bae50becd4026",
	Reading: "K = ∅ is met by N = 0, and then c may be empty. The sum is at most " +
		"1 off K as well, which is what lets a chapter above extend the pieces by 0.",
	Deps: []registry.EntryLike{
		BumpFunction,
		SmoothMul,
		SmoothSub,
		SmoothConst,
		euclidean_topology.OpenIff,
		CompactlySupportedInDef,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀K:((num → real) → bool). ∀c:(((num → real) → bool) → bool).",
		Hypotheses: []string{
			"compact_in(euclidean_topology(n), K)",
			"c ⊆ euclidean_topology(n)",
			"K ⊆ ⋃c",
		},
		Conclusion: "∃N:num. ∃ψ:(num → (num → real) → real). " +
			"    (∀i:num. " +
			"        i < N ⇒ " +
			"        vec_smooth_on⟨n⟩({u:num → real | vec⟨n⟩(u)}, ψ(i)) ∧ " +
			"        (∀x:(num → real). &0 ≤ ψ(i)(x)) ∧ " +
			"        ∃u:set(num → real). u ∈ c ∧ vec_compactly_supported_in⟨n⟩(u, ψ(i))) ∧ " +
			"    (∀x:(num → real). vec⟨n⟩(x) ⇒ Σ_{i<N} ψ(i)(x) ≤ &1) ∧ " +
			"    ∀x:(num → real). x ∈ K ⇒ Σ_{i<N} ψ(i)(x) = &1",
	},
		"about each point of K a ball of radius 3r lies in a member of c (euclidean_topology.OpenIff); "+
			"a bump φ, 1 on the ball of radius r and 0 from 2r (BumpFunction), has compact support in that "+
			"member, the closed ball of radius 2r; the open balls of radius r cover K, finitely many do, "+
			"φ₀, …, φ_{N−1}; ψᵢ = φᵢ·Π_{j<i}(1 − φⱼ) are smooth and nonnegative with ψᵢ's support inside "+
			"φᵢ's, and Σ_{i<N} ψᵢ = 1 − Π_{j<N}(1 − φⱼ) lies in ⟦0, 1⟧ and is 1 wherever some φⱼ is"),
})}

// SmoothPartitionOfUnityOpen — two open sets covering an open set have
// a subordinate smooth partition with supports closed in that open set.
var SmoothPartitionOfUnityOpen = smoothPartitionOfUnityOpenThm{family.Add(registry.ProofEntry{
	Name: "SmoothPartitionOfUnityOpen",
	Key:  "prop_fcb6853e3ed0e09a",
	Deps: []registry.EntryLike{
		SmoothPartitionOfUnity,
		SmoothSum,
		SmoothLocal,
		SmoothReciprocal,
		SmoothMul,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀U V W:set(num → real).",
		Hypotheses: []string{
			"V ∈ euclidean_topology(n)",
			"W ∈ euclidean_topology(n)",
			"U = V ∪ W",
		},
		Conclusion: "∃φ ψ:((num → real) → real). " +
			"    vec_smooth_on⟨n⟩(U, φ) ∧ " +
			"    vec_smooth_on⟨n⟩(U, ψ) ∧ " +
			"    (∀x:(num → real). x ∈ U ⇒ &0 ≤ φ(x) ∧ &0 ≤ ψ(x) ∧ φ(x) + ψ(x) = &1) ∧ " +
			"    closure(subtopology(euclidean_topology(n), U), {x:num → real | x ∈ U ∧ φ(x) ≠ &0}) ⊆ V ∧ " +
			"    closure(subtopology(euclidean_topology(n), U), {x:num → real | x ∈ U ∧ ψ(x) ≠ &0}) ⊆ W",
	},
		"Choose a compact exhaustion of U with successive sets contained in the interiors of the "+
			"next. On each compact annulus use SmoothPartitionOfUnity with pieces supported both in "+
			"V or W and in a slightly larger annulus; the resulting family is locally finite in U. "+
			"Add the V-pieces and the W-pieces, then divide by their everywhere positive sum "+
			"(SmoothReciprocal, SmoothMul). Local finiteness gives smoothness (SmoothSum, "+
			"SmoothLocal) and keeps each relative support inside its designated open set."),
})}
