package smooth_projection_bundle

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_topology"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/topology/projection_bundle"
	"github.com/euc-ai/xugo/library/proofs/vector/determinant"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

// RealifiedDeterminant — the real determinant of a complex matrix's realification is the
// squared modulus of its complex determinant.
var RealifiedDeterminant = realifiedDeterminantThm{family.Add(registry.ProofEntry{
	Name: "RealifiedDeterminant",
	Key:  "prop_f52e2e30a8043679",
	Deps: []registry.EntryLike{
		determinant.DeterminantMultiplicative,
		determinant.DeterminantTriangular,
	},
	Build: family.Card("∀k:num. ∀M:(num → num → complex). "+
		"    determinant(real_ring, "+
		"        2 * k, "+
		"        λi:num. λj:num. "+
		"            COND(nat_mod(i, 2) = 0, "+
		"                COND(nat_mod(j, 2) = 0, "+
		"                    re(M(nat_div(i, 2), nat_div(j, 2))), "+
		"                    -im(M(nat_div(i, 2), nat_div(j, 2)))), "+
		"                COND(nat_mod(j, 2) = 0, "+
		"                    im(M(nat_div(i, 2), nat_div(j, 2))), "+
		"                    re(M(nat_div(i, 2), nat_div(j, 2)))))) = "+
		"    |determinant(complex_ring, k, M)| ^ 2",
		"The realification interleaves coordinates, 2a the real and 2a+1 the imaginary part of the a-th "+
			"complex coordinate, so it is the matrix of z ↦ Mz on ℂ^k read as ℝ^(2k). Reduce M to triangular "+
			"form by complex row operations: each acts on the realification by a real matrix of determinant "+
			"|c|² for the scalar c it multiplies the determinant by (DeterminantMultiplicative). Then scale "+
			"each row a with M_aa ≠ 0 by the unit conj(M_aa)/|M_aa|, which leaves the realified determinant "+
			"unchanged and makes the diagonal real: the realification is then triangular with diagonal "+
			"|M_aa|, |M_aa| (DeterminantTriangular), and a zero diagonal entry makes both sides 0."),
	Reading: "The interleaved layout differs from the block layout [[re M, −im " +
		"M], [im M, re M]] by a permutation similarity, so the classical identity " +
		"holds as stated. At k = 0 both sides are the empty determinant, 1.",
})}

// SmoothNormalizedInverse — a normalized inverse of a smooth map between smooth Hermitian
// projections on an open set of ℝ^d has smooth entries.
var SmoothNormalizedInverse = smoothNormalizedInverseThm{family.Add(registry.ProofEntry{
	Name: "SmoothNormalizedInverse",
	Key:  "prop_5a0754d23ee4e4a5",
	Deps: []registry.EntryLike{
		vec_smooth.SmoothMatrixInverse,
		RealifiedDeterminant,
		vec_smooth.SmoothMul,
		vec_smooth.SmoothSum,
	},
	Build: family.Card(Statement{
		Binders: "∀d r q:num. " +
			"∀U:set(num → real). " +
			"∀P Q M V:((num → real) → num → num → complex). " +
			"∀k l:num.",
		Hypotheses: []string{
			"U ∈ euclidean_topology(d)",
			"∀i j:num. " +
				"    i < r ∧ j < r ⇒ " +
				"    vec_smooth_on⟨d⟩(U, λx:(num → real). re(P(x, i, j))) ∧ " +
				"    vec_smooth_on⟨d⟩(U, λx:(num → real). im(P(x, i, j)))",
			"∀i j:num. " +
				"    i < q ∧ j < q ⇒ " +
				"    vec_smooth_on⟨d⟩(U, λx:(num → real). re(Q(x, i, j))) ∧ " +
				"    vec_smooth_on⟨d⟩(U, λx:(num → real). im(Q(x, i, j)))",
			"∀i j:num. " +
				"    i < q ∧ j < r ⇒ " +
				"    vec_smooth_on⟨d⟩(U, λx:(num → real). re(M(x, i, j))) ∧ " +
				"    vec_smooth_on⟨d⟩(U, λx:(num → real). im(M(x, i, j)))",
			"∀x:(num → real). ∀i j:num. " +
				"    x ∈ U ∧ i < r ∧ j < r ⇒ " +
				"    P(x, i, j) = complex_conj(P(x, j, i)) ∧ " +
				"    module_sum(complex_add, " +
				"        complex_of_real(&0), " +
				"        {c:num | c < r}, " +
				"        λc:num. P(x, i, c) * P(x, c, j)) = " +
				"    P(x, i, j)",
			"∀x:(num → real). ∀i j:num. " +
				"    x ∈ U ∧ i < q ∧ j < q ⇒ " +
				"    Q(x, i, j) = complex_conj(Q(x, j, i)) ∧ " +
				"    module_sum(complex_add, " +
				"        complex_of_real(&0), " +
				"        {c:num | c < q}, " +
				"        λc:num. Q(x, i, c) * Q(x, c, j)) = " +
				"    Q(x, i, j)",
			"∀x:(num → real). ∀i j:num. " +
				"    x ∈ U ∧ i < q ∧ j < r ⇒ " +
				"    module_sum(complex_add, " +
				"        complex_of_real(&0), " +
				"        {a:num | a < q}, " +
				"        λa:num. " +
				"            Q(x, i, a) * " +
				"            module_sum(complex_add, " +
				"                complex_of_real(&0), " +
				"                {b:num | b < r}, " +
				"                λb:num. M(x, a, b) * P(x, b, j))) = " +
				"    M(x, i, j)",
			"∀x:(num → real). ∀i j:num. " +
				"    x ∈ U ∧ i < r ∧ j < q ⇒ " +
				"    module_sum(complex_add, " +
				"        complex_of_real(&0), " +
				"        {a:num | a < r}, " +
				"        λa:num. " +
				"            P(x, i, a) * " +
				"            module_sum(complex_add, " +
				"                complex_of_real(&0), " +
				"                {b:num | b < q}, " +
				"                λb:num. V(x, a, b) * Q(x, b, j))) = " +
				"    V(x, i, j)",
			"projection_inverse_on(U, (r, P), (q, Q), M, V)",
			"k < r",
			"l < q",
		},
		Conclusion: "vec_smooth_on⟨d⟩(U, λx:(num → real). re(V(x, k, l))) ∧ " +
			"vec_smooth_on⟨d⟩(U, λx:(num → real). im(V(x, k, l)))",
	},
		"Write A = M*M + I_r − P. Since QM = M and Q is Hermitian, AV = M*Q = M*; and A is invertible at "+
			"each point, since Av = 0 forces Mv = 0 and v = Pv (P a Hermitian projection), so v = VMv = 0. "+
			"Hence V = A⁻¹M*. The realified 2r × 2r matrix of A has smooth entries and determinant |det A|² "+
			"≠ 0 (RealifiedDeterminant), so SmoothMatrixInverse makes the real and imaginary parts of A⁻¹ "+
			"smooth, and V's entries are finite sums of products of them with M's (SmoothMul, SmoothSum)."),
	Reading: "The clause VM = P of projection_inverse_on, with P a Hermitian " +
		"projection, is what makes M*M + I − P invertible; Q's smoothness is never " +
		"used. Smoothness is local on the open U, so V's values off U do not matter.",
})}

// SmoothBundleContinuous — a smooth projection bundle is a continuous projection bundle.
var SmoothBundleContinuous = smoothBundleContinuousThm{family.Add(registry.ProofEntry{
	Name: "SmoothBundleContinuous",
	Key:  "prop_fcdc5bdb0b216341",
	Deps: []registry.EntryLike{
		smooth_manifold.FunctionContinuous,
		projection_bundle.ProjectionDef,
		complex_topology.ContinuousIffParts,
	},
	Build: family.Card(Statement{
		Binders: "∀n r:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P:(A → num → num → complex).",
		Hypotheses: []string{"smooth_projection_bundle(n, r, T, 𝒜, P)"},
		Conclusion: "continuous_projection_bundle(T, (r, P))",
	},
		"The manifold gives is_topology(T), and the vanishing and Hermitian idempotent "+
			"clauses of ProjectionDef are those of SmoothProjectionDef. FunctionContinuous "+
			"makes the real and imaginary parts of each entry continuous, so each entry is "+
			"continuous into complex_topology (complex_topology.ContinuousIffParts)."),
	Reading: "Every clause of continuous_projection_bundle is a clause of " +
		"smooth_projection_bundle except continuity, and is_topology(T) comes from the manifold.",
})}
