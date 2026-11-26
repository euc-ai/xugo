// The degree carriers are modules, and a covering atlas determines
// their normalized coordinate families uniquely.

package differential_form

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_form"
	"github.com/euc-ai/xugo/library/registry"
)

var FormModule = formModuleThm{family.Add(registry.ProofEntry{
	Name: "FormModule",
	Key:  "prop_178f411faace769f",
	Deps: []registry.EntryLike{
		FormModuleDef,
		FormOnDef,
		function_module.FunctionModuleDef,
		vec_form.FormModule,
		vec_form.PullbackLinear,
	},
	Build: family.Card(Statement{
		Binders:    "∀n k:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)).",
		Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)"},
		Conclusion: "module_on(real_ring, manifold_form_module⟨n⟩(T, 𝒜, k))",
	},
		"The three nested function modules give pointwise operations on chart families. "+
			"Each compatible-chart carrier is a Euclidean form module and transition pullbacks "+
			"are linear, so the overlap equations are preserved by addition and scaling. Zero "+
			"values on incompatible charts are preserved as well, giving the restricted module."),
})}

// FormModulePointwise — the degree-k module's carrier is the set of k-forms,
// its zero the zero family, and its addition, negation and scaling act on
// the real values chart by chart, point by point and matrix by matrix: the
// module unfolds to the k-forms cut out of three nested function modules
// over the real ring.
var FormModulePointwise = formModulePointwiseThm{family.Add(registry.ProofEntry{
	Name: "FormModulePointwise",
	Key:  "prop_776920467d8c7128",
	Reading: "No hypothesis is needed: the operations are those of the " +
		"three nested function modules over the real ring, total on every chart " +
		"family, and the restriction only replaces the carrier by the k-forms.",
	Build: family.Theorem("∀n k:num. "+
		"∀T:set(set(A)). "+
		"∀𝒜:set(prod(set(A), A → num → real)). "+
		"∀a:real. "+
		"∀α β:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). "+
		"    manifold_form_module⟨n⟩(T, 𝒜, k).carrier = "+
		"    {ω:prod(set(A), A → num → real) → (num → real) → (num → num → real) → real | "+
		"        manifold_form_on⟨n⟩(T, 𝒜, k, ω)} ∧ "+
		"    manifold_form_module⟨n⟩(T, 𝒜, k).zero = «zero family» ∧ "+
		"    manifold_form_module⟨n⟩(T, 𝒜, k).add(α, β) = "+
		"    (λc:prod(set(A), A → num → real). λy:(num → real). λP:(num → num → real). "+
		"        α(c, y, P) + β(c, y, P)) ∧ "+
		"    manifold_form_module⟨n⟩(T, 𝒜, k).neg(α) = "+
		"    (λc:prod(set(A), A → num → real). λy:(num → real). λP:(num → num → real). -α(c, y, P)) ∧ "+
		"    manifold_form_module⟨n⟩(T, 𝒜, k).smul(a, α) = "+
		"    (λc:prod(set(A), A → num → real). λy:(num → real). λP:(num → num → real). a * α(c, y, P))",
		func(
			arg *Argument,
			n, k *Expr[Nat],
			T *Expr[Set[Set[A]]],
			𝒜 *Expr[Set[Prod[Set[A], Fun2[A, Nat, Real]]]],
			a *Expr[Real],
			α, β *Expr[Fun3[Prod[Set[A], Fun2[A, Nat, Real]], Fun[Nat, Real], Fun2[Nat, Nat, Real], Real]],
		) {
			arg.Do(
				Simp(Fwd(FormModuleDef)),
				SplitConjAll(
					Case(
						"the restriction keeps the k-forms as the carrier",
						Refl(),
					),
					Case(
						"the lifted zero is the real zero at every chart, point and matrix",
						Funext(),
						Simp(Fwd(function_module.FunZeroDef)),
						Basic(),
					),
					Case(
						"the lifted addition adds the two values at every chart, point and matrix",
						Funext(),
						Simp(Fwd(function_module.FunAddDef)),
						Basic(),
					),
					Case(
						"the lifted negation negates the value at every chart, point and matrix",
						Funext(),
						Simp(Fwd(function_module.FunNegDef)),
						Basic(),
					),
					Case(
						"the lifted scaling multiplies the value by a at every chart, point and matrix",
						Funext(),
						Simp(Fwd(function_module.FunSmulDef)),
						Basic(),
					),
				),
			)
		}),
})}

// FormAdd — the sum of two k-forms is a k-form: the k-forms are the
// carrier of a real module, closed under its addition, and that addition
// is the pointwise sum.
var FormAdd = formAddThm{family.Add(registry.ProofEntry{
	Name: "FormAdd",
	Key:  "prop_161a42ef06b08a00",
	Build: family.Theorem(Statement{
		Binders: "∀n k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀α β:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"manifold_form_on⟨n⟩(T, 𝒜, k, α)",
			"manifold_form_on⟨n⟩(T, 𝒜, k, β)",
		},
		Conclusion: "manifold_form_on⟨n⟩(T, " +
			"    𝒜, " +
			"    k, " +
			"    λc:prod(set(A), A → num → real). λy:(num → real). λP:(num → num → real). " +
			"        α(c, y, P) + β(c, y, P))",
	},
		func(
			a *Argument,
			n, k *Expr[Nat],
			T *Expr[Set[Set[A]]],
			𝒜 *Expr[Set[Prod[Set[A], Fun2[A, Nat, Real]]]],
			α, β *Expr[Fun3[Prod[Set[A], Fun2[A, Nat, Real]], Fun[Nat, Real], Fun2[Nat, Nat, Real], Real]],
			αForm, βForm Fact,
		) {
			formModule := a.Have(
				"the k-forms are a real module",
				"module_on(real_ring, manifold_form_module⟨n⟩(T, 𝒜, k))",
				By(αForm, FormOnDef, FormModule))
			sumIn := a.Have(
				"α + β is a vector of the module of k-forms",
				"manifold_form_module⟨n⟩(T, 𝒜, k).add(α, β) ∈ manifold_form_module⟨n⟩(T, 𝒜, k).carrier",
				By(αForm, βForm, FormModulePointwise, group.MulIn.Read(module.AddGroupOn.Read(formModule))))
			a.Show(
				"the module sum is the pointwise sum",
				By(a.Simplified(sumIn, Fwd(FormModulePointwise))))
		}),
})}

var FormAboveDimension = formAboveDimensionThm{family.Add(registry.ProofEntry{
	Name: "FormAboveDimension",
	Key:  "prop_e4784c986b2d047b",
	Deps: []registry.EntryLike{FormOnDef, vec_form.FormAboveDimension},
	Build: family.Card(Statement{
		Binders: "∀n k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{"manifold_form_on⟨n⟩(T, 𝒜, k, ω)", "n < k"},
		Conclusion: "ω = «zero family»",
	},
		"On each compatible chart the degree exceeds the Euclidean dimension, so "+
			"FormAboveDimension gives the zero component. Incompatible components are "+
			"zero by definition, and function extensionality gives the global zero family."),
})}

var FormExt = formExtThm{family.Add(registry.ProofEntry{
	Name: "FormExt",
	Key:  "prop_dd93b5bb83dd204a",
	Reading: "The atlas cover determines every compatible component. Coordinate-image " +
		"normalization and incompatible-chart normalization are both needed for literal equality " +
		"of the full families. On an empty manifold every degree has exactly the zero family.",
	Deps: []registry.EntryLike{
		FormOnDef,
		smooth_manifold.AtlasDef,
		smooth_manifold.AtlasMemberCompatible,
	},
	Build: family.Card(Statement{
		Binders: "∀n k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀ω η:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"manifold_form_on⟨n⟩(T, 𝒜, k, ω)",
			"manifold_form_on⟨n⟩(T, 𝒜, k, η)",
			"∀c:prod(set(A), A → num → real). c ∈ 𝒜 ⇒ ω(c) = η(c)",
		},
		Conclusion: "ω = η",
	},
		"At a point in any compatible chart choose an original chart containing the "+
			"corresponding base point. The two overlap equations express both values as pullbacks "+
			"of their equal original components. Coordinate-image and incompatible-chart "+
			"normalization settle all remaining arguments, giving literal family equality."),
})}

var FormAtlasExtension = formAtlasExtensionThm{family.Add(registry.ProofEntry{
	Name: "FormAtlasExtension",
	Key:  "prop_75c8d27c15911a65",
	Reading: "The supplied family is constrained only at original atlas members. Its other " +
		"components may be arbitrary; the extended form is zero on all incompatible charts and " +
		"outside each compatible coordinate image. Covering is essential to existence and uniqueness.",
	Deps: []registry.EntryLike{
		FormOnDef,
		FormExt,
		smooth_manifold.CompatibleTransition,
		smooth_manifold.AtlasDef,
		vec_form.FormLocal,
		vec_form.PullbackForm,
		vec_form.PullbackCompose,
		vec_form.FormRestrict,
	},
	Build: family.Card(Statement{
		Binders: "∀n k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀h:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"∀c:prod(set(A), A → num → real). c ∈ 𝒜 ⇒ vec_form_on⟨n⟩(«chart image»(c), k, h(c))",
			"∀c d:prod(set(A), A → num → real). " +
				"    c ∈ 𝒜 ∧ d ∈ 𝒜 ⇒ " +
				"    normalize_on(«overlap»(c, d), λP:(num → num → real). &0, h(c)) = " +
				"    vec_form_pullback⟨n, n⟩(«overlap»(c, d), k, «transition»(c, d), h(d))",
		},
		Conclusion: "∃ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"    manifold_form_on⟨n⟩(T, 𝒜, k, ω) ∧ " +
			"    (∀c:prod(set(A), A → num → real). c ∈ 𝒜 ⇒ ω(c) = h(c)) ∧ " +
			"    (∀η:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"        manifold_form_on⟨n⟩(T, 𝒜, k, η) ∧ " +
			"        (∀c:prod(set(A), A → num → real). c ∈ 𝒜 ⇒ η(c) = h(c)) ⇒ " +
			"        η = ω)",
	},
		"For each compatible-chart point choose an original chart containing its inverse "+
			"image and pull back that component locally. The supplied overlap equations and "+
			"PullbackCompose make this independent of the chosen chart; FormLocal then gives "+
			"a Euclidean form on the full coordinate image after normalization. The same "+
			"transition calculation proves compatibility, and FormExt gives uniqueness."),
})}

var FormRestrict = formRestrictThm{family.Add(registry.ProofEntry{
	Name: "FormRestrict",
	Key:  "prop_4b6927df761af04f",
	Deps: []registry.EntryLike{
		RestrictDef,
		FormOnDef,
		smooth_manifold.OpenSubmanifold,
		smooth_manifold.OpenCompatibleChart,
	},
	Build: family.Card(Statement{
		Binders: "∀n k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀U:set(A). " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{"manifold_form_on⟨n⟩(T, 𝒜, k, ω)", "U ∈ T"},
		Conclusion: "manifold_form_on⟨n⟩(subtopology(T, U), " +
			"    open_submanifold_atlas⟨n⟩(T, 𝒜, U), " +
			"    k, " +
			"    manifold_form_restrict⟨n⟩(T, 𝒜, U, ω))",
	},
		"OpenCompatibleChart identifies the submanifold's compatible charts with "+
			"precisely the original compatible charts whose domains lie in U. Their "+
			"components and overlap equations are unchanged; every other chart is zeroed "+
			"by the restriction. OpenSubmanifold supplies the underlying manifold."),
})}

var RestrictionCompose = restrictionComposeThm{family.Add(registry.ProofEntry{
	Name: "RestrictionCompose",
	Key:  "prop_29c97614b4db21dd",
	Reading: "Restriction retains whole components for every originally compatible chart " +
		"with domain in the open subset, including charts outside the original atlas. " +
		"OpenCompatibleChart identifies these with exactly the submanifold's compatible charts.",
	Deps: []registry.EntryLike{RestrictDef, FormRestrict, smooth_manifold.OpenCompatibleChart},
	Build: family.Card(Statement{
		Binders: "∀n k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀U V:set(A). " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{"manifold_form_on⟨n⟩(T, 𝒜, k, ω)", "U ∈ T", "V ∈ T", "V ⊆ U"},
		Conclusion: "manifold_form_restrict⟨n⟩(subtopology(T, U), " +
			"    open_submanifold_atlas⟨n⟩(T, 𝒜, U), " +
			"    V, " +
			"    manifold_form_restrict⟨n⟩(T, 𝒜, U, ω)) = " +
			"manifold_form_restrict⟨n⟩(T, 𝒜, V, ω)",
	},
		"OpenCompatibleChart makes both operations retain exactly the compatible charts "+
			"with domain in V. Such charts already lie in U, so their original components "+
			"survive both restrictions; every other component is zero on both sides."),
})}
