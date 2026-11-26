// The smooth Sard theorem separates critical points by the order to
// which their derivatives vanish, then descends in the source dimension.

package vec_critical_point

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_taylor"
	"github.com/euc-ai/xugo/library/proofs/topology/countability"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean_topology"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_null"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

// SmoothSard — the critical values of a smooth map on a Euclidean open
// set form a null set.
var SmoothSard = smoothSardThm{family.Add(registry.ProofEntry{
	Name: "SmoothSard",
	Key:  "prop_e3a67679b41ce190",
	Reading: "When m = 0 there are no critical points. Where a first partial is nonzero, m = " +
		"1 also leaves no critical points, so CompactNullSlices is used only for m ≥ 2 with " +
		"positive slice dimension m - 1; for n = 0 < m the image has at most one point and is null.",
	Deps: []registry.EntryLike{
		vec_null.NullEmpty, vec_null.NullSubset, vec_null.NullCountableUnion,
		vec_null.LowerDimensionalImageNull, vec_null.CompactNullSlices,
		vec_smooth.SmoothInverseFunction, vec_smooth.SmoothMapCompose, vec_smooth.SmoothPartial,
		vec_smooth.JacobianDerivative, vec_smooth.ContinuouslyDifferentiableLocallyLipschitz,
		real_taylor.TaylorLagrange, euclidean_topology.EuclideanSecondCountable,
		countability.SecondCountableSubtopology, countability.SecondCountableImpLindelof,
	},
	Build: family.Card(Statement{
		Binders: "∀n m:num. ∀U:set(num → real). ∀f:((num → real) → (num → real)).",
		Hypotheses: []string{
			"U ∈ euclidean_topology(n)",
			"vec_smooth_map_on⟨n, m⟩(U, f)",
		},
		Conclusion: "vec_null_set⟨m⟩(image(f, {x:num → real | x ∈ U ∧ vec_critical_point⟨n, m⟩(f, x)}))",
	},
		"Induct on n, treating m = 0 by the absence of critical points and n < m by "+
			"LowerDimensionalImageNull and ContinuouslyDifferentiableLocallyLipschitz. Where a first "+
			"partial is nonzero, SmoothInverseFunction straightens that coordinate; compact pieces of the "+
			"critical-value set have null slices by the induction hypothesis, so CompactNullSlices "+
			"applies. Between successive derivative-vanishing strata, a nonzero differential of a higher "+
			"partial cuts out a smooth hypersurface, reducing n by one. On a stratum vanishing through "+
			"order r with m(r+1) > n, TaylorLagrange along segments inside a fixed compact neighbourhood "+
			"gives a uniform O(‖h‖^(r+1)) bound and cube subdivision makes its image null. SmoothPartial, "+
			"SmoothMapCompose and JacobianDerivative identify the derivatives after these changes of "+
			"coordinates; second countability supplies countable local covers, assembled by NullSubset "+
			"and NullCountableUnion. This is the smooth theorem, not the finite-regularity threshold."),
})}
