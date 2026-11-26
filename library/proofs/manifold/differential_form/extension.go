// Extension by zero is smooth when the support is closed in the ambient manifold,
// recovers a form supported in the open subset from its restriction, and is additive.
// A wedge whose second factor is supported in an open subset is the extension by zero
// of the wedge of the restrictions; when that factor ω is also closed, extending β ∧ ω
// from the subset gives a form whose exterior derivative extends dβ ∧ ω.

package differential_form

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/topology/function_support"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_form"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var ExtendZeroForm = extendZeroFormThm{family.Add(registry.ProofEntry{
	Name: "ExtendZeroForm",
	Key:  "prop_440ac917ba30291c",
	Reading: "Subspace closedness of the support is automatic but is not " +
		"enough. Closedness in the ambient manifold makes its complement an " +
		"open neighbourhood of every point across the extension boundary.",
	Deps: []registry.EntryLike{
		ExtendZeroDef,
		FormOnDef,
		SupportDef,
		smooth_manifold.ChartRestrict,
		smooth_manifold.OpenCompatibleChart,
		vec_form.FormLocal,
		function_support.SupportOutside,
	},
	Build: family.Card(Statement{
		Binders: "∀n k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀U:set(A). " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"U ∈ T",
			"manifold_form_on⟨n⟩(subtopology(T, U), open_submanifold_atlas⟨n⟩(T, 𝒜, U), k, ω)",
			"closed_in(T, manifold_form_support⟨n⟩(subtopology(T, U), open_submanifold_atlas⟨n⟩(T, 𝒜, U), ω))",
		},
		Conclusion: "manifold_form_on⟨n⟩(T, 𝒜, k, manifold_form_extend_zero⟨n⟩(T, 𝒜, U, ω))",
	},
		"In each ambient chart, the extended component is locally the restricted-chart form "+
			"over U and identically zero off the closed submanifold support. These open regions "+
			"cover the coordinate image, so FormLocal gives smoothness. Transition compatibility "+
			"follows on U from the source form and off its support from zero values."),
})}

var ExtendZeroRestrict = extendZeroRestrictThm{family.Add(registry.ProofEntry{
	Name: "ExtendZeroRestrict",
	Key:  "prop_3bd8004c56575c67",
	Reading: "This literal restriction identity requires no support condition. It does not " +
		"assert that the intermediate ambient family is smooth without the hypotheses of " +
		"ExtendZeroForm. A compatible submanifold chart has domain contained in U, so its restricted " +
		"chart pair is literally the original pair; normalization settles all remaining arguments.",
	Deps: []registry.EntryLike{
		ExtendZeroDef,
		RestrictDef,
		FormOnDef,
		smooth_manifold.OpenCompatibleChart,
	},
	Build: family.Card(Statement{
		Binders: "∀n k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀U:set(A). " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"U ∈ T",
			"manifold_form_on⟨n⟩(subtopology(T, U), open_submanifold_atlas⟨n⟩(T, 𝒜, U), k, ω)",
		},
		Conclusion: "manifold_form_restrict⟨n⟩(T, 𝒜, U, manifold_form_extend_zero⟨n⟩(T, 𝒜, U, ω)) = ω",
	},
		"A chart compatible with the submanifold already has domain contained in U, "+
			"so restricting its chart pair again does nothing and extension recovers its "+
			"component. Every incompatible submanifold component vanishes on both sides."),
})}

var RestrictExtendZero = restrictExtendZeroThm{family.Add(registry.ProofEntry{
	Name: "RestrictExtendZero",
	Key:  "prop_d331b9d81871471f",
	Reading: "The support condition carries the identity off U, where the extension is zero by " +
		"definition; only the nonzero locus lying in U is used, not its closure. U ∈ T is load-bearing " +
		"as well: the restricted chart needs an open domain to lie in the open-submanifold atlas (on " +
		"ℝ, a bump supported on [−1, 1] with U = [−1, 1] fails at the identity chart). Closedness of " +
		"the support is not needed, since ω is already a form on the ambient manifold.",
	Deps: []registry.EntryLike{
		ExtendZeroDef,
		RestrictDef,
		FormOnDef,
		SupportDef,
		smooth_manifold.ChartRestrict,
		smooth_manifold.OpenCompatibleChart,
		vec_smooth.SmoothSubset,
		vec_smooth.PartialDerivativeLocal,
		vec_form.PullbackIdentity,
		function_support.SupportOutside,
	},
	Build: family.Card(Statement{
		Binders: "∀n k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀U:set(A). " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"manifold_form_on⟨n⟩(T, 𝒜, k, ω)",
			"U ∈ T",
			"manifold_form_support⟨n⟩(T, 𝒜, ω) ⊆ U",
		},
		Conclusion: "manifold_form_extend_zero⟨n⟩(T, 𝒜, U, manifold_form_restrict⟨n⟩(T, 𝒜, U, ω)) = ω",
	},
		"At a compatible chart and a coordinate point of its part in U, the chart restricted to U is "+
			"a submanifold chart (its transitions are the original ones on smaller open sets) and carries "+
			"ω's own component, by overlap compatibility with a transition that is the identity near the "+
			"point. At a coordinate point of the chart outside U the base point lies off the support, "+
			"where ω vanishes; off the coordinate image and at incompatible charts both sides are zero."),
})}

// WedgeRestrictExtendZero — when ω is supported in an open set U, the
// wedge φ ∧ ω is the extension by zero of the wedge of the restrictions
// of φ and ω to U: the support of φ ∧ ω lies in that of ω, hence in U, so
// φ ∧ ω is the extension of its restriction, and restriction preserves
// the wedge.
var WedgeRestrictExtendZero = wedgeRestrictExtendZeroThm{family.Add(registry.ProofEntry{
	Name: "WedgeRestrictExtendZero",
	Key:  "prop_85fae2fd05428b84",
	Build: family.Theorem(Statement{
		Binders: "∀n p q:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀U:set(A). " +
			"∀φ ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"manifold_form_on⟨n⟩(T, 𝒜, p, φ)",
			"manifold_form_on⟨n⟩(T, 𝒜, q, ω)",
			"U ∈ T",
			"manifold_form_support⟨n⟩(T, 𝒜, ω) ⊆ U",
		},
		Conclusion: "manifold_form_wedge⟨n⟩(T, 𝒜, p, q, φ, ω) = " +
			"manifold_form_extend_zero⟨n⟩(T, " +
			"    𝒜, " +
			"    U, " +
			"    manifold_form_wedge⟨n⟩(subtopology(T, U), " +
			"        open_submanifold_atlas⟨n⟩(T, 𝒜, U), " +
			"        p, " +
			"        q, " +
			"        manifold_form_restrict⟨n⟩(T, 𝒜, U, φ), " +
			"        manifold_form_restrict⟨n⟩(T, 𝒜, U, ω)))",
	},
		func(
			a *Argument,
			n, p, q *Expr[Nat],
			T *Expr[Set[Set[A]]],
			𝒜 *Expr[Set[Prod[Set[A], Fun2[A, Nat, Real]]]],
			U *Expr[Set[A]],
			φ, ω *Expr[Fun3[Prod[Set[A], Fun2[A, Nat, Real]], Fun[Nat, Real], Fun2[Nat, Nat, Real], Real]],
			φForm, ωForm, open, support Fact,
		) {
			wedge := a.TermAs[Fun3[Prod[Set[A], Fun2[A, Nat, Real]], Fun[Nat, Real], Fun2[Nat, Nat, Real], Real]](
				"manifold_form_wedge⟨n⟩(T, 𝒜, p, q, φ, ω)")
			wedgeForm := a.Have(
				"φ ∧ ω is a (p + q)-form",
				"manifold_form_on⟨n⟩(T, 𝒜, p + q, manifold_form_wedge⟨n⟩(T, 𝒜, p, q, φ, ω))",
				By(φForm, ωForm, WedgeForm))
			wedgeSupport := a.Have(
				"the support of φ ∧ ω lies in that of ω, hence in U",
				"manifold_form_support⟨n⟩(T, 𝒜, manifold_form_wedge⟨n⟩(T, 𝒜, p, q, φ, ω)) ⊆ U",
				BySets(support, WedgeSupport.At(n, p, q, T, 𝒜, φ, ω)))
			a.Show(
				"φ ∧ ω is the extension of its restriction, the wedge of the restrictions",
				By(
					wedgeForm,
					open,
					wedgeSupport,
					φForm,
					ωForm,
					RestrictExtendZero.At(n, a.TermAs[Nat]("p + q"), T, 𝒜, U, wedge),
					RestrictionWedge.At(n, p, q, T, 𝒜, U, φ, ω)))
		}),
})}

// ExtendZeroAdd — extension by zero takes the sum of two families to the
// sum of their extensions: at a compatible chart and a coordinate of its
// part in U both sides read ω + η at the chart restricted to U, and
// everywhere else both are zero.
var ExtendZeroAdd = extendZeroAddThm{family.Add(registry.ProofEntry{
	Name: "ExtendZeroAdd",
	Key:  "prop_b2150cf6889f6827",
	Build: family.Theorem("∀n:num. "+
		"∀T:set(set(A)). "+
		"∀𝒜:set(prod(set(A), A → num → real)). "+
		"∀U:set(A). "+
		"∀ω η:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). "+
		"    manifold_form_extend_zero⟨n⟩(T, "+
		"        𝒜, "+
		"        U, "+
		"        λc:prod(set(A), A → num → real). λy:(num → real). λP:(num → num → real). "+
		"            ω(c, y, P) + η(c, y, P)) = "+
		"    λc:prod(set(A), A → num → real). λy:(num → real). λP:(num → num → real). "+
		"        manifold_form_extend_zero⟨n⟩(T, 𝒜, U, ω)(c, y, P) + "+
		"        manifold_form_extend_zero⟨n⟩(T, 𝒜, U, η)(c, y, P)",
		func(
			a *Argument,
			n *Expr[Nat],
			T *Expr[Set[Set[A]]],
			𝒜 *Expr[Set[Prod[Set[A], Fun2[A, Nat, Real]]]],
			U *Expr[Set[A]],
			ω, η *Expr[Fun3[Prod[Set[A], Fun2[A, Nat, Real]], Fun[Nat, Real], Fun2[Nat, Nat, Real], Real]],
		) {
			a.Do(Funext(), Simp(Fwd(ExtendZeroDef)))
			a.FixAs[Prod[Set[A], Fun2[A, Nat, Real]]]("c")
			a.FixAs[Fun[Nat, Real]]("y")
			a.FixAs[Fun2[Nat, Nat, Real]]("P")
			a.Cases(a.Term("compatible_chart⟨n⟩(T, 𝒜, c) ∧ y ∈ image(snd(c), fst(c) ∩ U)"))
			a.When(
				"c is a compatible chart and y a coordinate of its part in U",
				func(b *Argument, inside Fact) {
					b.Show(
						"both sides read ω + η at the chart restricted to U",
						By(inside))
				})
			a.Otherwise(
				"c is not a compatible chart, or y is no coordinate of its part in U",
				func(b *Argument, outside Fact) {
					b.Show(
						"both sides are zero, and &0 + &0 = &0",
						By(outside, real_ring.AddRightId.At(b.TermAs[Real]("&0"))))
				})
		}),
})}

var ExtendZeroSupport = extendZeroSupportThm{family.Add(registry.ProofEntry{
	Name: "ExtendZeroSupport",
	Key:  "prop_465a4f0cf1c8dd3a",
	Deps: []registry.EntryLike{
		ExtendZeroDef,
		SupportDef,
		smooth_manifold.ChartRestrict,
		smooth_manifold.OpenCompatibleChart,
		function_support.SupportExtendZero,
	},
	Build: family.Card(Statement{
		Binders: "∀n k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀U:set(A). " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"U ∈ T",
			"manifold_form_on⟨n⟩(subtopology(T, U), open_submanifold_atlas⟨n⟩(T, 𝒜, U), k, ω)",
			"closed_in(T, manifold_form_support⟨n⟩(subtopology(T, U), open_submanifold_atlas⟨n⟩(T, 𝒜, U), ω))",
		},
		Conclusion: "manifold_form_support⟨n⟩(T, 𝒜, manifold_form_extend_zero⟨n⟩(T, 𝒜, U, ω)) = " +
			"manifold_form_support⟨n⟩(subtopology(T, U), open_submanifold_atlas⟨n⟩(T, 𝒜, U), ω)",
	},
		"Inside U, restricted ambient charts and the source compatible charts detect exactly "+
			"the same nonzero base points. Outside U the extension is zero. SupportExtendZero "+
			"gives equality because the submanifold support is already closed in the ambient space."),
})}

var ExtendZeroExteriorDerivative = extendZeroExteriorDerivativeThm{family.Add(registry.ProofEntry{
	Name: "ExtendZeroExteriorDerivative",
	Key:  "prop_74e58d43966d530f",
	Deps: []registry.EntryLike{
		ExtendZeroDef,
		ExteriorDerivativeDef,
		ExtendZeroForm,
		ExteriorDerivativeSupport,
		FormOnDef,
		vec_smooth.PartialDerivativeLocal,
	},
	Build: family.Card(Statement{
		Binders: "∀n k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀U:set(A). " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"U ∈ T",
			"manifold_form_on⟨n⟩(subtopology(T, U), open_submanifold_atlas⟨n⟩(T, 𝒜, U), k, ω)",
			"closed_in(T, manifold_form_support⟨n⟩(subtopology(T, U), open_submanifold_atlas⟨n⟩(T, 𝒜, U), ω))",
		},
		Conclusion: "manifold_exterior_derivative⟨n⟩(T, " +
			"    𝒜, " +
			"    k, " +
			"    manifold_form_extend_zero⟨n⟩(T, 𝒜, U, ω)) = " +
			"manifold_form_extend_zero⟨n⟩(T, " +
			"    𝒜, " +
			"    U, " +
			"    manifold_exterior_derivative⟨n⟩(subtopology(T, U), open_submanifold_atlas⟨n⟩(T, 𝒜, U), k, ω))",
	},
		"On U the restricted and ambient coordinate maps agree locally, so exterior "+
			"differentiation commutes with the extension formula there. On the open complement "+
			"of the original support both sides are zero: locality handles the ambient "+
			"derivative and ExteriorDerivativeSupport handles the source derivative. These "+
			"regions cover the carrier, and normalization settles the remaining arguments."),
})}

// ExtendZeroWedgeClosed — for a closed q-form ω supported in an open set
// U and a k-form β on U, the extension by zero of β ∧ ω from U is a
// (k + q)-form on the manifold, and its exterior derivative is the
// extension by zero of dβ ∧ ω: ω restricted to U is closed, so d(β ∧ ω)
// = dβ ∧ ω on U; the support of β ∧ ω lies in that of ω, a closed set
// inside U, so it is closed in the manifold, and extension by zero then
// keeps the degree and commutes with d.
var ExtendZeroWedgeClosed = extendZeroWedgeClosedThm{family.Add(registry.ProofEntry{
	Name: "ExtendZeroWedgeClosed",
	Key:  "prop_eefafc016305d36b",
	Build: family.Theorem(Statement{
		Binders: "∀n k q:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀U:set(A). " +
			"∀β ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"U ∈ T",
			"manifold_form_on⟨n⟩(T, 𝒜, q, ω)",
			"manifold_exterior_derivative⟨n⟩(T, 𝒜, q, ω) = «zero family»",
			"manifold_form_support⟨n⟩(T, 𝒜, ω) ⊆ U",
			"manifold_form_on⟨n⟩(subtopology(T, U), «U atlas», k, β)",
		},
		Conclusion: "manifold_form_on⟨n⟩(T, " +
			"    𝒜, " +
			"    k + q, " +
			"    manifold_form_extend_zero⟨n⟩(T, 𝒜, U, «β ∧ ω on U»)) ∧ " +
			"manifold_exterior_derivative⟨n⟩(T, " +
			"    𝒜, " +
			"    k + q, " +
			"    manifold_form_extend_zero⟨n⟩(T, 𝒜, U, «β ∧ ω on U»)) = " +
			"manifold_form_extend_zero⟨n⟩(T, " +
			"    𝒜, " +
			"    U, " +
			"    manifold_form_wedge⟨n⟩(subtopology(T, U), " +
			"        «U atlas», " +
			"        k + 1, " +
			"        q, " +
			"        manifold_exterior_derivative⟨n⟩(subtopology(T, U), «U atlas», k, β), " +
			"        «ω on U»))",
		Abbrev: Abbrev{
			{Name: "U atlas", Text: "open_submanifold_atlas⟨n⟩(T, 𝒜, U)"},
			{Name: "ω on U", Text: "manifold_form_restrict⟨n⟩(T, 𝒜, U, ω)"},
			{Name: "β ∧ ω on U", Text: "manifold_form_wedge⟨n⟩(subtopology(T, U), " +
				"    «U atlas», " +
				"    k, " +
				"    q, " +
				"    β, " +
				"    «ω on U»)"},
		},
	},
		func(
			a *Argument,
			n, k, q *Expr[Nat],
			T *Expr[Set[Set[A]]],
			𝒜 *Expr[Set[Prod[Set[A], Fun2[A, Nat, Real]]]],
			U *Expr[Set[A]],
			β, ω *Expr[Fun3[Prod[Set[A], Fun2[A, Nat, Real]], Fun[Nat, Real], Fun2[Nat, Nat, Real], Real]],
			open, ωForm, ωClosed, support, βForm Fact,
		) {
			uTop := a.TermAs[Set[Set[A]]]("subtopology(T, U)")
			uAtlas := a.TermAs[Set[Prod[Set[A], Fun2[A, Nat, Real]]]]("«U atlas»")
			ωU := a.TermAs[Fun3[Prod[Set[A], Fun2[A, Nat, Real]], Fun[Nat, Real], Fun2[Nat, Nat, Real], Real]](
				"«ω on U»")
			βωU := a.TermAs[Fun3[Prod[Set[A], Fun2[A, Nat, Real]], Fun[Nat, Real], Fun2[Nat, Nat, Real], Real]](
				"«β ∧ ω on U»")
			smooth := a.Have(
				"the manifold is smooth",
				"smooth_manifold⟨n⟩(T, 𝒜)",
				By(ωForm, FormOnDef))
			ωUForm := a.Have(
				"ω restricts to a q-form on U",
				"manifold_form_on⟨n⟩(subtopology(T, U), «U atlas», q, «ω on U»)",
				By(ωForm, open, FormRestrict))
			ωUClosed := a.Have(
				"and the restriction is closed, the zero family restricting to itself",
				"manifold_exterior_derivative⟨n⟩(subtopology(T, U), «U atlas», q, «ω on U») = «zero family»",
				By(
					ωForm,
					open,
					ωClosed,
					RestrictionZero.At(n, T, 𝒜, U),
					RestrictionExteriorDerivative.At(n, q, T, 𝒜, U, ω)))
			βωUForm := a.Have(
				"β ∧ ω is a (k + q)-form on U",
				"manifold_form_on⟨n⟩(subtopology(T, U), «U atlas», k + q, «β ∧ ω on U»)",
				By(βForm, ωUForm, WedgeForm))
			derivative := a.Have(
				"ω being closed on U, d(β ∧ ω) = dβ ∧ ω there",
				"manifold_exterior_derivative⟨n⟩(subtopology(T, U), «U atlas», k + q, «β ∧ ω on U») = "+
					"manifold_form_wedge⟨n⟩(subtopology(T, U), "+
					"    «U atlas», "+
					"    k + 1, "+
					"    q, "+
					"    manifold_exterior_derivative⟨n⟩(subtopology(T, U), «U atlas», k, β), "+
					"    «ω on U»)",
				By(βForm, ωUForm, ωUClosed, ExteriorDerivativeWedgeClosed.At(n, k, q, uTop, uAtlas, β, ωU)))
			inSupport := a.Have(
				"the support of β ∧ ω lies in the support of ω",
				"manifold_form_support⟨n⟩(subtopology(T, U), «U atlas», «β ∧ ω on U») ⊆ "+
					"manifold_form_support⟨n⟩(T, 𝒜, ω)",
				BySets(
					ωForm,
					open,
					WedgeSupport.At(n, k, q, uTop, uAtlas, β, ωU),
					SupportRestrict.At(n, q, T, 𝒜, U, ω)))
			topology := a.Have(
				"T is a topology",
				"is_topology(T)",
				By(smooth, smooth_manifold.ManifoldDef))
			closedInU := a.Have(
				"the support of β ∧ ω is closed in U",
				"closed_in(subtopology(T, U), "+
					"    manifold_form_support⟨n⟩(subtopology(T, U), «U atlas», «β ∧ ω on U»))",
				By(topological_space.SubtopologyTopology.Read(topology), SupportClosed))
			ωSupportClosed := a.Have(
				"the support of ω is closed",
				"closed_in(T, manifold_form_support⟨n⟩(T, 𝒜, ω))",
				By(topology, SupportClosed))
			closed := a.Have(
				"closed in U and inside the closed support of ω, which lies in U, it is closed in the manifold",
				"closed_in(T, manifold_form_support⟨n⟩(subtopology(T, U), «U atlas», «β ∧ ω on U»))",
				By(
					closedInU,
					ωSupportClosed,
					inSupport,
					support,
					topological_space.ClosedInSubtopologyInsideClosed.Read(topology).At(
						U,
						a.TermAs[Set[A]]("manifold_form_support⟨n⟩(subtopology(T, U), «U atlas», «β ∧ ω on U»)"),
						a.TermAs[Set[A]]("manifold_form_support⟨n⟩(T, 𝒜, ω)"))))
			a.Show(
				"extension by zero keeps the degree and commutes with d",
				By(
					smooth,
					open,
					βωUForm,
					closed,
					derivative,
					ExtendZeroForm.At(n, a.TermAs[Nat]("k + q"), T, 𝒜, U, βωU),
					ExtendZeroExteriorDerivative.At(n, a.TermAs[Nat]("k + q"), T, 𝒜, U, βωU)))
		}),
})}
