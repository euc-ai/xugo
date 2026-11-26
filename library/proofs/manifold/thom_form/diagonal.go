package thom_form

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/manifold/de_rham"
	"github.com/euc-ai/xugo/library/proofs/manifold/de_rham_betti"
	"github.com/euc-ai/xugo/library/proofs/manifold/de_rham_cover"
	"github.com/euc-ai/xugo/library/proofs/manifold/de_rham_kunneth"
	"github.com/euc-ai/xugo/library/proofs/manifold/differential_form"
	"github.com/euc-ai/xugo/library/proofs/manifold/form_integral"
	"github.com/euc-ai/xugo/library/proofs/manifold/manifold_diagonal"
	"github.com/euc-ai/xugo/library/proofs/manifold/manifold_embedding"
	"github.com/euc-ai/xugo/library/proofs/manifold/riemannian"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_form"
	"github.com/euc-ai/xugo/library/registry"
)

var DiagonalFormExists = diagonalFormExistsThm{family.Add(registry.ProofEntry{
	Name: "DiagonalFormExists",
	Key:  "prop_ea4ef58565a30489",
	Deps: []registry.EntryLike{
		riemannian.CompactMetricExists,
		manifold_embedding.CompactTubularRetraction,
		ThomCompactSupport,
		ThomFiberIntegral,
		manifold_diagonal.DiagonalNeighbourhood,
		manifold_diagonal.DiagonalNeighbourhoodCohomology,
	},
	Reading: "The odd-rank construction uses compact support in the extra vertical coordinate " +
		"and a compact base slice; it does not invoke Poincaré duality or odd Euler vanishing.",
	Build: family.Card(
		Statement{
			Binders:    "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)).",
			Hypotheses: []string{"oriented_manifold⟨n⟩(T, 𝒜)", "compact_in(T, ⋃T)"},
			Conclusion: "∃η:(prod(set(prod(A, A)), prod(A, A) → num → real) → " +
				"        (num → real) → " +
				"        (num → num → real) → " +
				"        real). " +
				"    manifold_diagonal_form⟨n⟩(T, 𝒜, η)",
		},
		"Transport a compact vertical Thom form through a tangent-disk diagonal chart and extend "+
			"by zero. Even positive rank uses angular transgression; odd rank is obtained by applying "+
			"the even construction on M×R, restricting to M×{0}, then integrating the extra vertical "+
			"coordinate; rank zero is the normalized characteristic function of the open diagonal. "+
			"The R fiber is not compact, so manifold_fiber_integral's laws do not apply to that last "+
			"integral: it is a compactly supported integral in the R coordinate, taken chartwise."),
})}

var DiagonalEulerForm = diagonalEulerFormThm{family.Add(registry.ProofEntry{
	Name: "DiagonalEulerForm",
	Key:  "prop_f4c2272f10df3933",
	Deps: []registry.EntryLike{
		manifold_embedding.CompactTubularRetraction,
		ThomSupportInEmbeddedDisk,
		RadialCutoffExists,
		ThomClosed,
		ThomFiberIntegral,
		ThomZeroSection,
		manifold_diagonal.DiagonalFiberIntegral,
		manifold_diagonal.DiagonalNeighbourhoodCohomology,
	},
	Build: family.Card(
		Statement{
			Binders: "∀n:num. " +
				"∀T:set(set(A)). " +
				"∀𝒜:set(prod(set(A), A → num → real)). " +
				"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
				"∀m:num.",
			Hypotheses: []string{
				"oriented_manifold⟨n⟩(T, 𝒜)",
				"riemannian_metric⟨n⟩(T, 𝒜, g)",
				"n = 2 * m + 2",
				"compact_in(T, ⋃T)",
			},
			Conclusion: "∃η:(prod(set(prod(A, A)), prod(A, A) → num → real) → " +
				"        (num → real) → " +
				"        (num → num → real) → " +
				"        real). " +
				"    manifold_diagonal_form⟨n⟩(T, 𝒜, η) ∧ " +
				"    manifold_form_pullback⟨n, 2 * n⟩(T, " +
				"        𝒜, " +
				"        product_topology(T, T), " +
				"        smooth_product_atlas⟨n, n⟩(𝒜, 𝒜), " +
				"        n, " +
				"        (λx:A. (x, x)), " +
				"        η) = " +
				"    riemannian_euler_form⟨n⟩(T, 𝒜, g)",
		},
		"Choose a tubular diagonal chart and a cutoff supported strictly inside its tangent "+
			"disk. Transport U, extend by zero, and use Δ=Φ∘s₀ for the Euler restriction."),
})}

// chartsOn and formOn are the phantoms of an atlas of a manifold whose points
// have type X and of a coordinate family of forms on it.
type (
	chartsOn[X TypePhantom] = Set[Prod[Set[X], Fun2[X, Nat, Real]]]
	formOn[X TypePhantom]   = Fun3[Prod[Set[X], Fun2[X, Nat, Real]], Fun[Nat, Real], Fun2[Nat, Nat, Real], Real]
)

// DiagonalReproducing — integrating the second-factor pullback of a closed form
// against a diagonal form over the fiber gives back its de Rham class. On the open
// neighbourhood W of supp η the two pullbacks of α have one class. In degree zero
// they are equal, so π₂*α ∧ η = π₁*α ∧ η; in degree k + 1 their difference is dβ on
// W, and β ∧ η extended by zero is a global γ with π₂*α ∧ η = π₁*α ∧ η + dγ. The
// projection formula and π₊η = 1 return α from π₁*α ∧ η, and π₊ commutes with d.
var DiagonalReproducing = diagonalReproducingThm{family.Add(registry.ProofEntry{
	Name: "DiagonalReproducing",
	Key:  "prop_f13ba68e2537eb3d",
	Build: family.Sections(
		Statement{
			Binders: "∀n:num. " +
				"∀T:set(set(A)). " +
				"∀𝒜:set(prod(set(A), A → num → real)). " +
				"∀η:(prod(set(prod(A, A)), prod(A, A) → num → real) → (num → real) → (num → num → real) → real). " +
				"∀p:num. " +
				"∀α:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
			Hypotheses: []string{
				"manifold_diagonal_form⟨n⟩(T, 𝒜, η)",
				"α ∈ cocycles(de_rham_complex⟨n⟩(T, 𝒜), p)",
			},
			Conclusion: "de_rham_class⟨n⟩(T, 𝒜, p, «π₊»(p, «π₂*α ∧ η»(p))) = de_rham_class⟨n⟩(T, 𝒜, p, α)",
			Abbrev: Abbrev{
				{Name: "W topology", Text: "subtopology(product_topology(T, T), W)"},
				{Name: "W atlas", Text: "open_submanifold_atlas⟨2 * n⟩(product_topology(T, T), " +
					"    smooth_product_atlas⟨n, n⟩(𝒜, 𝒜), " +
					"    W)"},
				{Name: "π₁*α", Text: "λk:num. " +
					"    manifold_form_pullback⟨2 * n, n⟩(product_topology(T, T), " +
					"        smooth_product_atlas⟨n, n⟩(𝒜, 𝒜), " +
					"        T, " +
					"        𝒜, " +
					"        k, " +
					"        fst, " +
					"        α)"},
				{Name: "π₂*α", Text: "λk:num. " +
					"    manifold_form_pullback⟨2 * n, n⟩(product_topology(T, T), " +
					"        smooth_product_atlas⟨n, n⟩(𝒜, 𝒜), " +
					"        T, " +
					"        𝒜, " +
					"        k, " +
					"        snd, " +
					"        α)"},
				{Name: "π₁*α on W", Text: "λk:num. " +
					"    manifold_form_pullback⟨2 * n, n⟩(«W topology», «W atlas», T, 𝒜, k, fst, α)"},
				{Name: "π₂*α on W", Text: "λk:num. " +
					"    manifold_form_pullback⟨2 * n, n⟩(«W topology», «W atlas», T, 𝒜, k, snd, α)"},
				{Name: "π₁*α ∧ η", Text: "λk:num. " +
					"    manifold_form_wedge⟨2 * n⟩(product_topology(T, T), " +
					"        smooth_product_atlas⟨n, n⟩(𝒜, 𝒜), " +
					"        k, " +
					"        n, " +
					"        «π₁*α»(k), " +
					"        η)"},
				{Name: "π₂*α ∧ η", Text: "λk:num. " +
					"    manifold_form_wedge⟨2 * n⟩(product_topology(T, T), " +
					"        smooth_product_atlas⟨n, n⟩(𝒜, 𝒜), " +
					"        k, " +
					"        n, " +
					"        «π₂*α»(k), " +
					"        η)"},
				{Name: "η on W", Text: "manifold_form_restrict⟨2 * n⟩(product_topology(T, T), " +
					"    smooth_product_atlas⟨n, n⟩(𝒜, 𝒜), " +
					"    W, " +
					"    η)"},
				{Name: "π₊", Text: "λk:num. " +
					"λω:(prod(set(prod(A, A)), prod(A, A) → num → real) → (num → real) → (num → num → real) → real). " +
					"    manifold_fiber_integral⟨n, n⟩(T, 𝒜, T, 𝒜, k, ω)"},
				{Name: "d on W", Text: "λk:num. " +
					"λω:(prod(set(prod(A, A)), prod(A, A) → num → real) → (num → real) → (num → num → real) → real). " +
					"    manifold_exterior_derivative⟨2 * n⟩(«W topology», «W atlas», k, ω)"},
				{Name: "d on M × M", Text: "λk:num. " +
					"λω:(prod(set(prod(A, A)), prod(A, A) → num → real) → (num → real) → (num → num → real) → real). " +
					"    manifold_exterior_derivative⟨2 * n⟩(product_topology(T, T), " +
					"        smooth_product_atlas⟨n, n⟩(𝒜, 𝒜), " +
					"        k, " +
					"        ω)"},
				{Name: "· ∧ η on W", Text: "λk:num. " +
					"λω:(prod(set(prod(A, A)), prod(A, A) → num → real) → (num → real) → (num → num → real) → real). " +
					"    manifold_form_wedge⟨2 * n⟩(«W topology», «W atlas», k, n, ω, «η on W»)"},
				{Name: "· ∧ η extended", Text: "λk:num. " +
					"λω:(prod(set(prod(A, A)), prod(A, A) → num → real) → (num → real) → (num → num → real) → real). " +
					"    manifold_form_extend_zero⟨2 * n⟩(product_topology(T, T), " +
					"        smooth_product_atlas⟨n, n⟩(𝒜, 𝒜), " +
					"        W, " +
					"        «· ∧ η on W»(k, ω))"},
			},
		},
		func(ctx *Script, headline string) *GoalStackNode {
			pullbackOnW := ctx.Lemma(Statement{
				Binders: "∀n:num. " +
					"∀T:set(set(A)). " +
					"∀𝒜:set(prod(set(A), A → num → real)). " +
					"∀η:(prod(set(prod(A, A)), prod(A, A) → num → real) → (num → real) → (num → num → real) → real). " +
					"∀W:set(prod(A, A)). " +
					"∀f:(prod(A, A) → A). " +
					"∀p:num. " +
					"∀α:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
				Hypotheses: []string{
					"W ∈ product_topology(T, T)",
					"manifold_form_support⟨2 * n⟩(product_topology(T, T), smooth_product_atlas⟨n, n⟩(𝒜, 𝒜), η) ⊆ W",
					"manifold_form_on⟨2 * n⟩(product_topology(T, T), smooth_product_atlas⟨n, n⟩(𝒜, 𝒜), n, η)",
					"smooth_manifold_map⟨2 * n, n⟩(product_topology(T, T), smooth_product_atlas⟨n, n⟩(𝒜, 𝒜), T, 𝒜, f)",
					"α ∈ cocycles(de_rham_complex⟨n⟩(T, 𝒜), p)",
				},
				Conclusion: "smooth_manifold_map⟨2 * n, n⟩(«W topology», «W atlas», T, 𝒜, f) ∧ " +
					"manifold_form_on⟨2 * n⟩(«W topology», «W atlas», p, «f*α on W») ∧ " +
					"«d on W»(p, «f*α on W») = " +
					"(λc:prod(set(prod(A, A)), prod(A, A) → num → real). λy:(num → real). λP:(num → num → real). " +
					"    &0) ∧ " +
					"«f*α ∧ η» = «· ∧ η extended»(p, «f*α on W»)",
				Abbrev: Abbrev{
					{Name: "f*α", Text: "manifold_form_pullback⟨2 * n, n⟩(product_topology(T, T), " +
						"    smooth_product_atlas⟨n, n⟩(𝒜, 𝒜), " +
						"    T, " +
						"    𝒜, " +
						"    p, " +
						"    f, " +
						"    α)"},
					{Name: "f*α on W", Text: "manifold_form_pullback⟨2 * n, n⟩(«W topology», " +
						"    «W atlas», " +
						"    T, " +
						"    𝒜, " +
						"    p, " +
						"    f, " +
						"    α)"},
					{Name: "f*α ∧ η", Text: "manifold_form_wedge⟨2 * n⟩(product_topology(T, T), " +
						"    smooth_product_atlas⟨n, n⟩(𝒜, 𝒜), " +
						"    p, " +
						"    n, " +
						"    «f*α», " +
						"    η)"},
				},
			}, func(
				a *Argument,
				n *Expr[Nat],
				T *Expr[Set[Set[A]]],
				𝒜 *Expr[chartsOn[A]],
				η *Expr[formOn[Prod[A, A]]],
				W *Expr[Set[Prod[A, A]]],
				f *Arrow[Prod[A, A], A],
				p *Expr[Nat],
				α *Expr[formOn[A]],
				open, support, ηForm, fSmooth, cocycle Fact,
			) {
				twoN := a.TermAs[Nat]("2 * n")
				productTop := a.TermAs[Set[Set[Prod[A, A]]]]("product_topology(T, T)")
				productAtlas := a.TermAs[chartsOn[Prod[A, A]]]("smooth_product_atlas⟨n, n⟩(𝒜, 𝒜)")
				wTop := a.TermAs[Set[Set[Prod[A, A]]]]("«W topology»")
				wAtlas := a.TermAs[chartsOn[Prod[A, A]]]("«W atlas»")
				fα := a.TermAs[formOn[Prod[A, A]]]("«f*α»")
				fαOnW := a.TermAs[formOn[Prod[A, A]]]("«f*α on W»")
				inclusion := a.Have(
					"the inclusion of W in M × M is smooth",
					"smooth_manifold_map⟨2 * n, 2 * n⟩(«W topology», "+
						"    «W atlas», "+
						"    product_topology(T, T), "+
						"    smooth_product_atlas⟨n, n⟩(𝒜, 𝒜), "+
						"    identity_map)",
					By(fSmooth, smooth_manifold.SmoothMapDef, open, smooth_manifold.SmoothOpenInclusion))
				fOnW := a.Have(
					"so f restricts to a smooth map on W",
					"smooth_manifold_map⟨2 * n, n⟩(«W topology», «W atlas», T, 𝒜, f)",
					By(
						inclusion,
						fSmooth,
						smooth_manifold.SmoothMapCompose.At(twoN, twoN, n, wTop, wAtlas, productTop, productAtlas, T, 𝒜,
							a.TermAs[Fun[Prod[A, A], Prod[A, A]]]("identity_map"), f),
						functions.ComposeIdentity.At(f)))
				onW := a.Have(
					"(f*α)|W, the pullback of α along f on W, is a closed p-form there",
					"manifold_form_on⟨2 * n⟩(«W topology», «W atlas», p, «f*α on W») ∧ "+
						"«d on W»(p, «f*α on W») = "+
						"(λc:prod(set(prod(A, A)), prod(A, A) → num → real). λy:(num → real). λP:(num → num → real). &0)",
					By(
						fOnW,
						cocycle,
						de_rham.PullbackCocycle.At(twoN, n, p, wTop, wAtlas, T, 𝒜, f, α),
						de_rham.CocycleClosedForm.At(twoN, wTop, wAtlas, p, fαOnW)))
				wedge := a.Have(
					"f*α ∧ η is the extension by zero of its part on W, the wedge of the restrictions",
					"«f*α ∧ η» = «· ∧ η extended»(p, «f*α on W»)",
					By(
						cocycle,
						fSmooth,
						ηForm,
						open,
						support,
						de_rham.CocycleClosedForm.At(n, T, 𝒜, p, α),
						differential_form.PullbackForm.At(twoN, n, p, productTop, productAtlas, T, 𝒜, f, α),
						differential_form.WedgeRestrictExtendZero.At(twoN, p, n, productTop, productAtlas, W, fα, η),
						differential_form.RestrictionPullback.At(twoN, n, p, productTop, productAtlas, T, 𝒜, W, f, α)))
				a.Show(
					"f restricts to W, where f*α is a closed p-form, and f*α ∧ η extends its part on W by zero",
					By(fOnW, onW, wedge))
			})

			return ctx.Theorem(headline, func(
				a *Argument,
				n *Expr[Nat],
				T *Expr[Set[Set[A]]],
				𝒜 *Expr[chartsOn[A]],
				η *Expr[formOn[Prod[A, A]]],
				p *Expr[Nat],
				α *Expr[formOn[A]],
				diagonal, cocycle Fact,
			) {
				parts := a.Conjuncts(
					a.Unfolded(diagonal, DiagonalFormDef),
					"M is oriented",
					"M is compact",
					"η is an n-cocycle of M × M",
					"η integrates to one over the fiber",
					"η is supported in an open W on which the two projections agree in cohomology")
				oriented, compact, ηCocycle, unit := parts[0], parts[1], parts[2], parts[3]
				W, neighbourhood := a.UnpackAs[Set[Prod[A, A]]](parts[4], "W")
				nearDiagonal := a.Conjuncts(
					neighbourhood,
					"W is open",
					"the support of η lies in W",
					"the two projections agree in cohomology on W")
				open, support, agree := nearDiagonal[0], nearDiagonal[1], nearDiagonal[2]

				twoN := a.TermAs[Nat]("2 * n")
				productTop := a.TermAs[Set[Set[Prod[A, A]]]]("product_topology(T, T)")
				productAtlas := a.TermAs[chartsOn[Prod[A, A]]]("smooth_product_atlas⟨n, n⟩(𝒜, 𝒜)")
				wTop := a.TermAs[Set[Set[Prod[A, A]]]]("«W topology»")
				wAtlas := a.TermAs[chartsOn[Prod[A, A]]]("«W atlas»")
				first := a.TermAs[Fun[Prod[A, A], A]]("fst")
				second := a.TermAs[Fun[Prod[A, A], A]]("snd")

				two := a.Have(
					"M × M has dimension n + n",
					"2 * n = n + n",
					ByArith())
				smooth := a.Have(
					"M is smooth",
					"smooth_manifold⟨n⟩(T, 𝒜)",
					By(oriented, form_integral.OrientedManifoldDef))
				projections := a.Conjuncts(
					a.Have(
						"both projections M × M → M are smooth",
						"smooth_manifold_map⟨2 * n, n⟩(product_topology(T, T), "+
							"    smooth_product_atlas⟨n, n⟩(𝒜, 𝒜), "+
							"    T, "+
							"    𝒜, "+
							"    fst) ∧ "+
							"smooth_manifold_map⟨2 * n, n⟩(product_topology(T, T), "+
							"    smooth_product_atlas⟨n, n⟩(𝒜, 𝒜), "+
							"    T, "+
							"    𝒜, "+
							"    snd)",
						By(smooth, two, smooth_manifold.SmoothProductProjections)),
					"the first projection is smooth",
					"the second projection is smooth")
				firstSmooth, secondSmooth := projections[0], projections[1]
				αParts := a.Conjuncts(
					a.Have(
						"α is a closed p-form",
						"manifold_form_on⟨n⟩(T, 𝒜, p, α) ∧ "+
							"manifold_exterior_derivative⟨n⟩(T, 𝒜, p, α) = "+
							"(λc:prod(set(A), A → num → real). λy:(num → real). λP:(num → num → real). &0)",
						By(cocycle, de_rham.CocycleClosedForm)),
					"α is a p-form",
					"α is closed")
				αForm, αClosed := αParts[0], αParts[1]
				ηParts := a.Conjuncts(
					a.Have(
						"η is a closed n-form on M × M",
						"manifold_form_on⟨2 * n⟩(product_topology(T, T), smooth_product_atlas⟨n, n⟩(𝒜, 𝒜), n, η) ∧ "+
							"«d on M × M»(n, η) = "+
							"(λc:prod(set(prod(A, A)), prod(A, A) → num → real). λy:(num → real). λP:(num → num → real). &0)",
						By(ηCocycle, de_rham.CocycleClosedForm)),
					"η is an n-form",
					"η is closed")
				ηForm, ηClosed := ηParts[0], ηParts[1]
				firstParts := a.Conjuncts(
					GroupPremises(
						open, support, ηForm, firstSmooth, cocycle, At(pullbackOnW, n, T, 𝒜, η, W, first, p, α)),
					"the first projection restricts to a smooth map on W",
					"π₁*α is a p-form on W",
					"π₁*α is closed on W",
					"π₁*α ∧ η is the extension by zero of its part on W")
				firstOnW, firstFormOnW, firstClosedOnW, firstExtended :=
					firstParts[0], firstParts[1], firstParts[2], firstParts[3]
				secondParts := a.Conjuncts(
					GroupPremises(
						open, support, ηForm, secondSmooth, cocycle, At(pullbackOnW, n, T, 𝒜, η, W, second, p, α)),
					"so does the second projection",
					"π₂*α is a p-form on W",
					"π₂*α is closed on W",
					"π₂*α ∧ η is the extension by zero of its part on W")
				secondOnW, secondFormOnW, secondClosedOnW, secondExtended :=
					secondParts[0], secondParts[1], secondParts[2], secondParts[3]
				classes := a.Have(
					"on W the two pullbacks of α have one class",
					"de_rham_class⟨2 * n⟩(«W topology», «W atlas», p, «π₁*α on W»(p)) = "+
						"de_rham_class⟨2 * n⟩(«W topology», «W atlas», p, «π₂*α on W»(p))",
					By(
						agree.At(p, a.Term("de_rham_class⟨n⟩(T, 𝒜, p, α)")),
						αForm,
						αClosed,
						firstOnW,
						secondOnW,
						de_rham.ClassMember.At(n, T, 𝒜, p, α),
						de_rham.PullbackClass.At(twoN, n, wTop, wAtlas, T, 𝒜, p, first, α),
						de_rham.PullbackClass.At(twoN, n, wTop, wAtlas, T, 𝒜, p, second, α)))
				ηHorizontal := a.TermAs[Nat]("0")
				reproduce := a.Have(
					"η is purely vertical, of degree 0 + n, so the "+
						"projection formula and π₊η = 1 return α from π₁*α ∧ η",
					"«π₊»(p, «π₁*α ∧ η»(p)) = α",
					By(
						smooth,
						oriented,
						compact,
						αForm,
						ηForm,
						two,
						unit,
						form_integral.FiberIntegralProjectionFormula.At(n, n, T, 𝒜, T, 𝒜, p, ηHorizontal, α, η),
						nat_arith.AddZero.At(p),
						nat_arith.AddLeftZeroClause.At(n),
						differential_form.WedgeUnit.At(n, p, T, 𝒜, α)))

				a.Cases(a.Term("p = 0"))
				a.When(
					"in degree zero the two pullbacks agree on W, so the two wedges agree",
					func(b *Argument, zero Fact) {
						b.Do(zero.Rw())
						equal := b.Have(
							"the classes of closed 0-forms on W agree only when the forms do",
							"«π₁*α on W»(0) = «π₂*α on W»(0)",
							By(
								classes,
								firstFormOnW,
								secondFormOnW,
								firstClosedOnW,
								secondClosedOnW,
								de_rham.ClassEqualZero.At(twoN, wTop, wAtlas,
									b.TermAs[formOn[Prod[A, A]]]("«π₁*α on W»(0)"), b.TermAs[formOn[Prod[A, A]]]("«π₂*α on W»(0)"))))
						b.Show(
							"π₂*α ∧ η = π₁*α ∧ η, which integrates to α",
							By(reproduce, firstExtended, secondExtended, equal))
					})
				a.Otherwise(
					"in degree k + 1 the two pullbacks differ on W by dβ, and β ∧ η extends to M × M",
					func(b *Argument, nonzero Fact) {
						k, successor := b.ObtainAs[Nat](
							"p is k + 1 for some k",
							"∃k:num. p = k + 1",
							By(nonzero, nat_arith.NonzeroIsSucc.At(p)))
						b.Do(successor.Rw())
						firstK := b.TermAs[formOn[Prod[A, A]]]("«π₁*α on W»(k + 1)")
						secondK := b.TermAs[formOn[Prod[A, A]]]("«π₂*α on W»(k + 1)")
						β, primitive := b.ObtainAs[formOn[Prod[A, A]]](
							"on W the two pullbacks differ by dβ for a k-form β",
							"∃β:(prod(set(prod(A, A)), prod(A, A) → num → real) → (num → real) → (num → num → real) → real). "+
								"    manifold_form_on⟨2 * n⟩(«W topology», «W atlas», k, β) ∧ "+
								"    «d on W»(k, β) = "+
								"    (λc:prod(set(prod(A, A)), prod(A, A) → num → real). λy:(num → real). λP:(num → num → real). "+
								"        «π₂*α on W»(k + 1, c, y, P) - «π₁*α on W»(k + 1, c, y, P))",
							By(
								classes,
								firstFormOnW,
								secondFormOnW,
								firstClosedOnW,
								secondClosedOnW,
								de_rham.ClassEqualSucc.At(twoN, wTop, wAtlas, k, secondK, firstK)))
						βParts := b.Conjuncts(
							primitive,
							"β is a k-form on W",
							"dβ is π₂*α − π₁*α on W")
						βForm, βDerivative := βParts[0], βParts[1]
						dβ := b.TermAs[formOn[Prod[A, A]]]("«d on W»(k, β)")
						γ := b.TermAs[formOn[Prod[A, A]]]("«· ∧ η extended»(k, β)")
						sumOnW := b.Have(
							"so π₂*α = π₁*α + dβ on W",
							"«π₂*α on W»(k + 1) = "+
								"(λc:prod(set(prod(A, A)), prod(A, A) → num → real). λy:(num → real). λP:(num → num → real). "+
								"    «π₁*α on W»(k + 1, c, y, P) + «d on W»(k, β, c, y, P))",
							βDerivative.Rw(),
							Funext(),
							ByArith())
						split := b.Have(
							"on W, (π₁*α + dβ) ∧ η = π₁*α ∧ η + dβ ∧ η",
							"«· ∧ η on W»(k + 1, "+
								"    λc:prod(set(prod(A, A)), prod(A, A) → num → real). λy:(num → real). λP:(num → num → real). "+
								"        «π₁*α on W»(k + 1, c, y, P) + «d on W»(k, β, c, y, P)) = "+
								"(λc:prod(set(prod(A, A)), prod(A, A) → num → real). λy:(num → real). λP:(num → num → real). "+
								"    «· ∧ η on W»(k + 1, «π₁*α on W»(k + 1), c, y, P) + "+
								"    «· ∧ η on W»(k + 1, «d on W»(k, β), c, y, P))",
							By(
								firstFormOnW,
								βForm,
								ηForm,
								open,
								differential_form.ExteriorDerivativeForm.At(twoN, k, wTop, wAtlas, β),
								differential_form.FormRestrict.At(twoN, n, productTop, productAtlas, W, η),
								differential_form.WedgeAddLeft.At(twoN, b.TermAs[Nat]("k + 1"), n, wTop, wAtlas, firstK, dβ,
									b.TermAs[formOn[Prod[A, A]]]("«η on W»"))))
						extension := b.Conjuncts(
							GroupPremises(
								open,
								ηForm,
								ηClosed,
								support,
								βForm,
								differential_form.ExtendZeroWedgeClosed.At(twoN, k, n, productTop, productAtlas, W, β, η)),
							"β ∧ η extends by zero to a (k + n)-form γ on M × M",
							"and dγ is the extension by zero of dβ ∧ η")
						γForm, γDerivative := extension[0], extension[1]
						exact := b.Have(
							"on M × M, π₂*α ∧ η = π₁*α ∧ η + dγ",
							"«π₂*α ∧ η»(k + 1) = "+
								"(λc:prod(set(prod(A, A)), prod(A, A) → num → real). λy:(num → real). λP:(num → num → real). "+
								"    «π₁*α ∧ η»(k + 1, c, y, P) + «d on M × M»(k + n, «· ∧ η extended»(k, β), c, y, P))",
							CalcEq(
								Leg(
									b.Term("«· ∧ η extended»(k + 1, «π₂*α on W»(k + 1))"),
									"π₂*α ∧ η is the extension by zero of its part on W",
									By(secondExtended)),
								Leg(
									b.Term("«· ∧ η extended»(k + 1, "+
										"    λc:prod(set(prod(A, A)), prod(A, A) → num → real). λy:(num → real). λP:(num → num → real). "+
										"        «π₁*α on W»(k + 1, c, y, P) + «d on W»(k, β, c, y, P))"),
									"on W, π₂*α = π₁*α + dβ",
									sumOnW.Rw()),
								Leg(
									b.Term("manifold_form_extend_zero⟨2 * n⟩(product_topology(T, T), "+
										"    smooth_product_atlas⟨n, n⟩(𝒜, 𝒜), "+
										"    W, "+
										"    λc:prod(set(prod(A, A)), prod(A, A) → num → real). λy:(num → real). λP:(num → num → real). "+
										"        «· ∧ η on W»(k + 1, «π₁*α on W»(k + 1), c, y, P) + "+
										"        «· ∧ η on W»(k + 1, «d on W»(k, β), c, y, P))"),
									"the wedge with η on W is additive in its first factor",
									split.Rw()),
								Leg(
									b.Term(
										"λc:prod(set(prod(A, A)), prod(A, A) → num → real). λy:(num → real). λP:(num → num → real). "+
											"    «· ∧ η extended»(k + 1, «π₁*α on W»(k + 1), c, y, P) + "+
											"    «· ∧ η extended»(k + 1, «d on W»(k, β), c, y, P)"),
									"extension by zero is additive",
									Simp(Fwd(differential_form.ExtendZeroAdd))),
								Leg(
									b.Term(
										"λc:prod(set(prod(A, A)), prod(A, A) → num → real). λy:(num → real). λP:(num → num → real). "+
											"    «π₁*α ∧ η»(k + 1, c, y, P) + «· ∧ η extended»(k + 1, «d on W»(k, β), c, y, P)"),
									"the first summand is π₁*α ∧ η, the extension by zero of its part on W",
									firstExtended.RwRev()),
								FinalLeg(
									"and the second is dγ",
									γDerivative.RwRev())))
						degree := b.Have(
							"dγ has degree k + n + 1, which is k + 1 + n",
							"k + n + 1 = k + 1 + n",
							ByArith())
						summandForms := b.Have(
							"π₁*α ∧ η and dγ are (k + 1 + n)-forms",
							"manifold_form_on⟨2 * n⟩(product_topology(T, T), "+
								"    smooth_product_atlas⟨n, n⟩(𝒜, 𝒜), "+
								"    k + 1 + n, "+
								"    «π₁*α ∧ η»(k + 1)) ∧ "+
								"manifold_form_on⟨2 * n⟩(product_topology(T, T), "+
								"    smooth_product_atlas⟨n, n⟩(𝒜, 𝒜), "+
								"    k + 1 + n, "+
								"    «d on M × M»(k + n, «· ∧ η extended»(k, β)))",
							By(
								degree,
								firstSmooth,
								αForm,
								ηForm,
								γForm,
								differential_form.PullbackForm.At(
									twoN, n, b.TermAs[Nat]("k + 1"), productTop, productAtlas, T, 𝒜, first, α),
								differential_form.WedgeForm.At(twoN, b.TermAs[Nat]("k + 1"), n, productTop, productAtlas,
									b.TermAs[formOn[Prod[A, A]]]("«π₁*α»(k + 1)"), η),
								differential_form.ExteriorDerivativeForm.At(
									twoN, b.TermAs[Nat]("k + n"), productTop, productAtlas, γ)))
						integrated := b.Have(
							"π₊(π₂*α ∧ η) = π₊(π₁*α ∧ η) + π₊(dγ), fiber integration being additive",
							"«π₊»(k + 1, «π₂*α ∧ η»(k + 1)) = "+
								"(λc:prod(set(A), A → num → real). λy:(num → real). λP:(num → num → real). "+
								"    «π₊»(k + 1, «π₁*α ∧ η»(k + 1), c, y, P) + "+
								"    «π₊»(k + 1, «d on M × M»(k + n, «· ∧ η extended»(k, β)), c, y, P))",
							exact.Rw(),
							By(
								smooth,
								oriented,
								compact,
								two,
								summandForms,
								form_integral.FiberIntegralAdd.At(n, n, b.TermAs[Nat]("k + 1"), T, 𝒜, T, 𝒜,
									b.TermAs[formOn[Prod[A, A]]]("«π₁*α ∧ η»(k + 1)"),
									b.TermAs[formOn[Prod[A, A]]]("«d on M × M»(k + n, «· ∧ η extended»(k, β))"))))
						commute := b.Have(
							"π₊ commutes with d",
							"manifold_exterior_derivative⟨n⟩(T, 𝒜, k, «π₊»(k, «· ∧ η extended»(k, β))) = "+
								"«π₊»(k + 1, «d on M × M»(k + n, «· ∧ η extended»(k, β)))",
							By(
								smooth,
								oriented,
								compact,
								two,
								γForm,
								form_integral.FiberIntegralExteriorDerivative.At(n, n, k, T, 𝒜, T, 𝒜, γ)))
						integratedγForm := b.Have(
							"π₊γ is a k-form on M",
							"manifold_form_on⟨n⟩(T, 𝒜, k, «π₊»(k, «· ∧ η extended»(k, β)))",
							By(
								smooth,
								oriented,
								compact,
								two,
								γForm,
								form_integral.FiberIntegralForm.At(n, n, k, T, 𝒜, T, 𝒜, γ)))
						b.Show(
							"so π₊(π₂*α ∧ η) = α + d(π₊γ), which is cohomologous to α",
							integrated.Rw(),
							reproduce.Rw(),
							commute.RwRev(),
							By(
								αForm,
								αClosed,
								integratedγForm,
								de_rham.ClassAddExact.At(n, k, T, 𝒜, α, b.TermAs[formOn[A]]("«π₊»(k, «· ∧ η extended»(k, β))"))))
					})
			})
		}),
})}

var IntegralPairingRepresentatives = integralPairingRepresentativesThm{family.Add(registry.ProofEntry{
	Name: "IntegralPairingRepresentatives",
	Key:  "prop_491002b458325b05",
	Deps: []registry.EntryLike{pairingDef, form_integral.ManifoldStokes},
	Build: family.Card(
		Statement{
			Binders: "∀n:num. " +
				"∀T:set(set(A)). " +
				"∀𝒜:set(prod(set(A), A → num → real)). " +
				"∀p q:num. " +
				"∀α β:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
			Hypotheses: []string{
				"oriented_manifold⟨n⟩(T, 𝒜)",
				"compact_in(T, ⋃T)",
				"p + q = n",
				"α ∈ cocycles(de_rham_complex⟨n⟩(T, 𝒜), p)",
				"β ∈ cocycles(de_rham_complex⟨n⟩(T, 𝒜), q)",
			},
			Conclusion: "de_rham_integral_pairing⟨n⟩(T, " +
				"    𝒜, " +
				"    p, " +
				"    q, " +
				"    de_rham_class⟨n⟩(T, 𝒜, p, α), " +
				"    de_rham_class⟨n⟩(T, 𝒜, q, β)) = " +
				"manifold_form_integral⟨n⟩(T, 𝒜, manifold_form_wedge⟨n⟩(T, 𝒜, p, q, α, β))",
		},
		"Changing a closed representative by an exact form changes the top "+
			"wedge by an exact form. Compact Stokes makes its integral zero."),
})}

var DiagonalPairingNondegenerate = diagonalPairingNondegenerateThm{family.Add(registry.ProofEntry{
	Name: "DiagonalPairingNondegenerate",
	Key:  "prop_40919ed4fe037373",
	Deps: []registry.EntryLike{
		DiagonalFormExists,
		DiagonalReproducing,
		de_rham_kunneth.CompactManifoldKunneth,
		IntegralPairingRepresentatives,
	},
	Build: family.Card(
		Statement{
			Binders: "∀n:num. " +
				"∀T:set(set(A)). " +
				"∀𝒜:set(prod(set(A), A → num → real)). " +
				"∀p q:num. " +
				"∀s:set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
			Hypotheses: []string{
				"oriented_manifold⟨n⟩(T, 𝒜)",
				"compact_in(T, ⋃T)",
				"p + q = n",
				"s ∈ de_rham_cohomology_module⟨n⟩(T, 𝒜, p).carrier",
				"∀t:set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
					"    t ∈ de_rham_cohomology_module⟨n⟩(T, 𝒜, q).carrier ⇒ " +
					"    de_rham_integral_pairing⟨n⟩(T, 𝒜, p, q, s, t) = &0",
			},
			Conclusion: "s = de_rham_cohomology_module⟨n⟩(T, 𝒜, p).zero",
		},
		"Expand a diagonal form by Künneth and apply the reproducing identity. Each coefficient "+
			"is an integral pairing against the complementary-degree factor, and all vanish."),
})}

var DiagonalTrace = diagonalTraceThm{family.Add(registry.ProofEntry{
	Name: "DiagonalTrace",
	Key:  "prop_bc87ce88989d08e2",
	Deps: []registry.EntryLike{
		DiagonalDegreeTrace,
		de_rham_kunneth.CompactManifoldKunneth,
		de_rham_cover.CompactManifoldFiniteCohomology,
	},
	Reading: "The sign (−1)^p comes from moving a degree-p second-factor form " +
		"past a degree-p first-factor form: (−1)^(p²)=(−1)^p, in every dimension.",
	Build: family.Card(
		Statement{
			Binders: "∀n:num. " +
				"∀T:set(set(A)). " +
				"∀𝒜:set(prod(set(A), A → num → real)). " +
				"∀η:(prod(set(prod(A, A)), prod(A, A) → num → real) → (num → real) → (num → num → real) → real).",
			Hypotheses: []string{"manifold_diagonal_form⟨n⟩(T, 𝒜, η)"},
			Conclusion: "manifold_form_integral⟨n⟩(T, " +
				"    𝒜, " +
				"    manifold_form_pullback⟨n, 2 * n⟩(T, " +
				"        𝒜, " +
				"        product_topology(T, T), " +
				"        smooth_product_atlas⟨n, n⟩(𝒜, 𝒜), " +
				"        n, " +
				"        (λx:A. (x, x)), " +
				"        η)) = " +
				"de_rham_euler⟨n⟩(T, 𝒜)",
		},
		"A Künneth expansion of η expresses the identity in degree p as rank-one "+
			"operators with sign (−1)^p. Their traces are the corresponding integrals. "+
			"Summing with alternating signs gives the integral of the diagonal pullback."),
})}

var GaussBonnetChernZero = gaussBonnetChernZeroThm{family.Add(registry.ProofEntry{
	Name: "GaussBonnetChernZero",
	Key:  "prop_16bf8a681f340441",
	Deps: []registry.EntryLike{riemannian.EulerZeroDimension, de_rham_betti.EulerDef},
	Build: family.Card(
		Statement{
			Binders: "∀n:num. " +
				"∀T:set(set(A)). " +
				"∀𝒜:set(prod(set(A), A → num → real)). " +
				"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real).",
			Hypotheses: []string{
				"n = 0",
				"oriented_manifold⟨n⟩(T, 𝒜)",
				"riemannian_metric⟨n⟩(T, 𝒜, g)",
				"compact_in(T, ⋃T)",
			},
			Conclusion: "manifold_form_integral⟨n⟩(T, 𝒜, riemannian_euler_form⟨n⟩(T, 𝒜, g)) = " +
				"de_rham_euler⟨n⟩(T, 𝒜)",
		},
		"A compact zero-manifold is a finite discrete set. The empty Pfaffian is one at each "+
			"point, and only degree-zero cohomology contributes, with dimension the number of points."),
})}

var GaussBonnetChern = gaussBonnetChernThm{family.Add(registry.ProofEntry{
	Name: "GaussBonnetChern",
	Key:  "prop_530a853a80680efb",
	Deps: []registry.EntryLike{DiagonalEulerForm, DiagonalTrace, GaussBonnetChernZero},
	Build: family.Card(
		Statement{
			Binders: "∀n:num. " +
				"∀T:set(set(A)). " +
				"∀𝒜:set(prod(set(A), A → num → real)). " +
				"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
				"∀m:num.",
			Hypotheses: []string{
				"oriented_manifold⟨n⟩(T, 𝒜)",
				"riemannian_metric⟨n⟩(T, 𝒜, g)",
				"n = 2 * m",
				"compact_in(T, ⋃T)",
			},
			Conclusion: "manifold_form_integral⟨n⟩(T, 𝒜, riemannian_euler_form⟨n⟩(T, 𝒜, g)) = " +
				"de_rham_euler⟨n⟩(T, 𝒜)",
		},
		"For m=0 use the finite zero-manifold calculation. In positive even "+
			"dimension take the diagonal Euler form and apply its trace identity."),
})}

var PoincareDuality = poincareDualityThm{family.Add(registry.ProofEntry{
	Name: "PoincareDuality",
	Key:  "prop_7c0c66be0ca0c3a1",
	Deps: []registry.EntryLike{
		IntegralPairingRepresentatives,
		DiagonalPairingNondegenerate,
		de_rham_cover.CompactManifoldFiniteCohomology,
	},
	Reading: "Both degrees are explicit with p + q=n, avoiding natural " +
		"- number subtraction outside its valid range. The target consists " +
		"of linear functionals normalized to zero off the cohomology carrier.",
	Build: family.Card(
		Statement{
			Binders:    "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀p q:num.",
			Hypotheses: []string{"oriented_manifold⟨n⟩(T, 𝒜)", "compact_in(T, ⋃T)", "p + q = n"},
			Conclusion: "module_isomorphism(real_ring, " +
				"    de_rham_cohomology_module⟨n⟩(T, 𝒜, p), " +
				"    hom_module(real_ring, de_rham_cohomology_module⟨n⟩(T, 𝒜, q), regular_module(real_ring)), " +
				"    de_rham_duality_map⟨n⟩(T, 𝒜, p, q))",
		},
		"Stokes gives a bilinear pairing; the diagonal argument makes it nondegenerate in each "+
			"slot. Finite dimensionality turns the injection into the full dual into an isomorphism."),
})}

var OddEulerZero = oddEulerZeroThm{family.Add(registry.ProofEntry{
	Name: "OddEulerZero",
	Key:  "prop_ce033100886f4437",
	Deps: []registry.EntryLike{PoincareDuality, de_rham_betti.EulerDef},
	Build: family.Card(
		Statement{
			Binders:    "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀m:num.",
			Hypotheses: []string{"oriented_manifold⟨n⟩(T, 𝒜)", "compact_in(T, ⋃T)", "n = 2 * m + 1"},
			Conclusion: "de_rham_euler⟨n⟩(T, 𝒜) = &0",
		},
		"Poincaré duality equates complementary Betti numbers. In odd dimension the "+
			"paired terms have opposite signs and the finite alternating sum vanishes."),
})}

var EulerMetricIndependent = eulerMetricIndependentThm{family.Add(registry.ProofEntry{
	Name: "EulerMetricIndependent",
	Key:  "prop_ef2fc58bf4bdb219",
	Deps: []registry.EntryLike{
		vec_form.PfaffianCurvatureClosed,
		de_rham.HomotopyOperator,
		riemannian.EulerZeroDimension,
	},
	Reading: "Compactness is not needed. The connection on the cylinder is the " +
		"interpolated connection on the pulled-back rank-n tangent bundle, not the " +
		"Levi-Civita connection of its (n + 1) - dimensional tangent bundle.",
	Build: family.Card(
		Statement{
			Binders: "∀n:num. " +
				"∀T:set(set(A)). " +
				"∀𝒜:set(prod(set(A), A → num → real)). " +
				"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
				"∀m:num. " +
				"∀h:(prod(set(A), A → num → real) → (num → real) → num → num → real).",
			Hypotheses: []string{
				"oriented_manifold⟨n⟩(T, 𝒜)",
				"riemannian_metric⟨n⟩(T, 𝒜, g)",
				"n = 2 * m",
				"riemannian_metric⟨n⟩(T, 𝒜, h)",
			},
			Conclusion: "de_rham_class⟨n⟩(T, 𝒜, n, riemannian_euler_form⟨n⟩(T, 𝒜, g)) = " +
				"de_rham_class⟨n⟩(T, 𝒜, n, riemannian_euler_form⟨n⟩(T, 𝒜, h))",
		},
		"Interpolate the positive metrics and compare their orthonormal frame connections "+
			"on the cylinder. The curvature Pfaffian is closed there, so the homotopy operator "+
			"gives an exact difference of the endpoint Euler forms; rank zero is immediate."),
})}
