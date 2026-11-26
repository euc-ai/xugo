// Fiber slices transform covariantly and a fixed fiber partition gives smooth coordinate integrals.

package form_integral

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/manifold/differential_form"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/real/lebesgue_riemann"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_form"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_integral"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var FiberSliceForm = fiberSliceFormThm{family.Add(registry.ProofEntry{
	Name: "FiberSliceForm",
	Key:  "prop_388c622e9065fac1",
	Reading: "No orientation or compactness is needed to form a slice. Arbitrary matrix tails are " +
		"discarded by the block frame; all fiber components are normalized, including incompatible charts.",
	Deps: []registry.EntryLike{
		fiberSliceDef,
		smooth_manifold.ProductCompatibleChart,
		differential_form.FormOnDef,
		vec_form.FormOnDef,
		vec_form.PullbackDef,
	},
	Build: family.Card(Statement{
		Binders: "∀n m k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀ω:(prod(set(prod(A, B)), prod(A, B) → num → real) → (num → real) → (num → num → real) → real). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀y:(num → real). " +
			"∀P:(num → num → real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"smooth_manifold⟨m⟩(S, ℬ)",
			"manifold_form_on⟨n + m⟩(product_topology(T, S), smooth_product_atlas⟨n, m⟩(𝒜, ℬ), k + m, ω)",
		},
		Conclusion: "manifold_form_on⟨m⟩(S, ℬ, m, manifold_fiber_slice⟨n, m⟩(T, 𝒜, S, ℬ, k, ω, c, y, P))",
	},
		"On valid base chart data, restrict the smooth product coefficients to the fixed base "+
			"point and insert the fixed horizontal columns. Alternation and multilinearity in the "+
			"vertical columns give a top fiber form, and product transitions with identity on the "+
			"base give its overlap equations. For invalid base data the slice is the whole zero form."),
})}

var FiberSliceBaseChange = fiberSliceBaseChangeThm{family.Add(registry.ProofEntry{
	Name: "FiberSliceBaseChange",
	Key:  "prop_9663c77c2bf97d64",
	Reading: "The equality is of whole normalized fiber forms, not only of their values in positive " +
		"charts. It uses the open base overlap, where the transition and its derivative are defined.",
	Deps: []registry.EntryLike{
		fiberSliceDef,
		smooth_manifold.ProductCompatibleChart,
		differential_form.FormOnDef,
		vec_form.PullbackDef,
		vec_smooth.JacobianChain,
	},
	Build: family.Card(Statement{
		Binders: "∀n m k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀ω:(prod(set(prod(A, B)), prod(A, B) → num → real) → (num → real) → (num → num → real) → real). " +
			"∀c e:prod(set(A), A → num → real). " +
			"∀y:(num → real). " +
			"∀P:(num → num → real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"smooth_manifold⟨m⟩(S, ℬ)",
			"manifold_form_on⟨n + m⟩(product_topology(T, S), smooth_product_atlas⟨n, m⟩(𝒜, ℬ), k + m, ω)",
			"compatible_chart⟨n⟩(T, 𝒜, c)",
			"compatible_chart⟨n⟩(T, 𝒜, e)",
			"y ∈ «overlap»(c, e)",
		},
		Conclusion: "manifold_fiber_slice⟨n, m⟩(T, 𝒜, S, ℬ, k, ω, c, y, P) = " +
			"manifold_fiber_slice⟨n, m⟩(T, " +
			"    𝒜, " +
			"    S, " +
			"    ℬ, " +
			"    k, " +
			"    ω, " +
			"    e, " +
			"    «transition»(c, e, y), " +
			"    matrix_mul(n, vec_jacobian_matrix⟨n, n⟩(«transition»(c, e), y), P))",
	},
		"Apply the product-form transition equation between the two base charts paired with each "+
			"fixed fiber chart. Its Jacobian is block diagonal with the base transition Jacobian and "+
			"the fiber identity. Multiplication by the horizontal-then-vertical frame gives the "+
			"stated transformed horizontal matrix; outside the fiber chart both sides are zero."),
})}

var FiberIntegralCoordinate = fiberIntegralCoordinateThm{family.Add(registry.ProofEntry{
	Name: "FiberIntegralCoordinate",
	Key:  "prop_686cd859ac01ffb7",
	Reading: "The fiber partition is independent of the base parameters. Its " +
		"coordinate supports are fixed compact sets inside the assigned fiber charts; this " +
		"uniform localization, not pointwise compactness alone, permits differentiation " +
		"under integration. The displayed integrand agrees with the normalized slice " +
		"coefficient on m-vectors, which is exactly the domain read by vec_integral.",
	Deps: []registry.EntryLike{
		FiberIntegralDef,
		fiberSliceDef,
		FiberSliceForm,
		IntegralByPartition,
		chartIntegralDef,
		vec_integral.IntegralCongruence,
		differential_form.WeightDef,
		differential_form.SupportClosed,
		smooth_manifold.PartitionOfUnityDef,
	},
	Build: family.Card(Statement{
		Binders: "∀n m k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀ω:(prod(set(prod(A, B)), prod(A, B) → num → real) → (num → real) → (num → num → real) → real). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀y:(num → real). " +
			"∀P:(num → num → real). " +
			"∀N:num. " +
			"∀d:(num → prod(set(B), B → num → real)). " +
			"∀ψ:(num → B → real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"oriented_manifold⟨m⟩(S, ℬ)",
			"compact_in(S, ⋃S)",
			"manifold_form_on⟨n + m⟩(product_topology(T, S), smooth_product_atlas⟨n, m⟩(𝒜, ℬ), k + m, ω)",
			"compatible_chart⟨n⟩(T, 𝒜, c)",
			"y ∈ «chart image»(c)",
			"manifold_integral_partition⟨m⟩(S, ℬ, ⋃S, N, d, ψ)",
		},
		Conclusion: "manifold_fiber_integral⟨n, m⟩(T, 𝒜, S, ℬ, k, ω)(c, y, P) = " +
			"Σ_{i<N} vec_integral⟨m⟩(λz:(num → real). ψ(i, inverse_on(fst(d(i)), snd(d(i)), z)) * ω(«product chart»(c, d(i)), «product coordinates»(y, z), «fiber frame»(P, matrix_identity(real_ring, m))))",
	},
		"Every slice support is a closed subset of the compact fiber carrier, so the "+
			"fixed partition of that carrier computes its integral. Expand the weighted chart "+
			"coefficient at the identity matrix to obtain the displayed Euclidean integrals. "+
			"The same partition works for every base point and every horizontal matrix."),
})}

var FiberIntegralForm = fiberIntegralFormThm{family.Add(registry.ProofEntry{
	Name: "FiberIntegralForm",
	Key:  "prop_43dd7fd0368041e3",
	Reading: "The base may be noncompact and unoriented. No compact support in the " +
		"base is needed. Compactness of the entire fiber supplies a fixed finite partition " +
		"and hence the local uniform support needed by the parameter-integral argument. " +
		"These compact coordinate supports are independent of both the base point and the " +
		"horizontal frame, so extension across fiber-chart boundaries is jointly smooth.",
	Deps: []registry.EntryLike{
		FiberIntegralCoordinate,
		FiberSliceBaseChange,
		IntegralPartitionExists,
		IntegralAdd,
		IntegralScale,
		differential_form.FormOnDef,
		vec_form.FormOnDef,
		vec_smooth.SmoothParameterIntegral,
		vec_smooth.SmoothLocal,
		lebesgue_riemann.LebesgueIntegralInterval,
		vec_integral.IntegralSplit,
	},
	Build: family.Card(Statement{
		Binders: "∀n m k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀ω:(prod(set(prod(A, B)), prod(A, B) → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"oriented_manifold⟨m⟩(S, ℬ)",
			"compact_in(S, ⋃S)",
			"manifold_form_on⟨n + m⟩(product_topology(T, S), smooth_product_atlas⟨n, m⟩(𝒜, ℬ), k + m, ω)",
		},
		Conclusion: "manifold_form_on⟨n⟩(T, 𝒜, k, manifold_fiber_integral⟨n, m⟩(T, 𝒜, S, ℬ, k, ω))",
	},
		"Choose one finite positive-chart partition of the compact fiber. On a base chart its "+
			"localized coefficients are jointly smooth and vanish outside fixed compact fiber "+
			"coordinate sets; enclose each in a box and iterate SmoothParameterIntegral after "+
			"affine changes of the integration intervals. Integrating the finite minor expansion "+
			"gives a smooth degree-k form, and FiberSliceBaseChange gives its base overlap law."),
})}
