// lindeberg_feller.go — the central limit theorems for rows of independent variables, from the
// martingale central limit theorem at the rows' natural filtrations.

package central_limit

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/measure/borel_function"
	"github.com/euc-ai/xugo/library/proofs/measure/event_integral"
	"github.com/euc-ai/xugo/library/proofs/measure/integral_convergence"
	"github.com/euc-ai/xugo/library/proofs/measure/measurable_function"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_integral"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	"github.com/euc-ai/xugo/library/proofs/probability/filtration"
	"github.com/euc-ai/xugo/library/proofs/probability/independence"
	"github.com/euc-ai/xugo/library/proofs/probability/lindeberg_bound"
	"github.com/euc-ai/xugo/library/proofs/probability/martingale/martingale"
	"github.com/euc-ai/xugo/library/proofs/probability/probability_space"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_rpow"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/sets/sigma_algebra"
	"github.com/euc-ai/xugo/library/registry"
)

// LindebergFeller — the Lindeberg–Feller central limit theorem: when the rows of a
// triangular array are independent, centred and square-integrable, their variances sum to 1
// in the limit and their Lindeberg sums vanish, the row sums converge weakly to the standard
// normal distribution. Each row is a martingale difference row for its natural filtration,
// F(n, k) the σ-algebra the variables before k generate: independence makes the conditional
// mean of ξ(n, k) its mean 0 and its conditional variance its second moment, a constant
// (IndependentFamilyCondExp). Constants whose row sums tend to 1 converge to 1 in measure, and
// MartingaleCentralLimit concludes.
var LindebergFeller = lindebergFellerThm{family.Add(registry.ProofEntry{
	Name: "LindebergFeller",
	Key:  "prop_11dcbb494854de",
	Reading: "Row n has its own length K(n), and the rows are not asked to be related to each " +
		"other. independent_variable_family carries the probability space and the measurability of " +
		"each variable. The variables being centred, a variance here is the second moment E[ξ(n, k)²].",
	Build: family.Sections(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀K:(num → num). " +
			"∀ξ:(num → num → A → real).",
		Hypotheses: []string{
			"∀n:num. independent_variable_family(Ω, S, μ, {k:num | k < K(n)}, ξ(n))",
			"∀n k:num. " +
				"    k < K(n) ⇒ " +
				"    expectation(Ω, S, μ, ξ(n, k)) = &0 ∧ real_integrable(Ω, S, μ, λx:A. ξ(n, k, x) * ξ(n, k, x))",
			"(λn:num. real_sum({k:num | k < K(n)}, λk:num. variance(Ω, S, μ, ξ(n, k)))) ⟶ &1",
			"∀ε:real. &0 < ε ⇒ (λn:num. lindeberg_sum(Ω, S, μ, K(n), ξ(n), ε)) ⟶ &0",
		},
		Conclusion: "weakly_converges(real_topology, " +
			"    λn:num. pushforward_measure(Ω, μ, λx:A. real_sum({k:num | k < K(n)}, λk:num. ξ(n, k, x))), " +
			"    normal_distribution(&0, &1))",
		Abbrev: Abbrev{
			{Name: "naturalFiltration", Text: "λn:num. λk:num. " +
				"    sigma_join(Ω, " +
				"        λj:num. pullback_sigma(Ω, ξ(n, j), borel_sets(real_topology)), " +
				"        {j:num | j < k ∧ j < K(n)})"},
			{Name: "secondMoment", Text: "λn:num. λk:num. λx:A. " +
				"    expectation(Ω, S, μ, λy:A. ξ(n, k, y) * ξ(n, k, y))"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		// Constants whose values converge converge in measure: from some N on the event where
		// they are ε away from the limit is empty.
		constantsInMeasure := ctx.Lemma(Statement{
			Binders:    "∀Ω:set(A). ∀μ:(set(A) → extended_nonneg_real). ∀a:(num → real). ∀l:real.",
			Hypotheses: []string{"μ(∅) = &0", "a ⟶ l"},
			Conclusion: "converges_in_measure(Ω, μ, λn:num. λx:A. a(n), λx:A. l)",
		}, func(
			arg *Argument,
			Ω *Expr[Set[A]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			a *Arrow[Nat, Real],
			l *Expr[Real],
			emptyMeasure, limit Fact,
		) {
			arg.Show(
				"for every ε and δ, from some N on the event ε < |a(n) − l| is empty",
				Simp(Fwd(integral_convergence.ConvergesInMeasureDef)),
				Derive(func(b *Argument) {
					b.FixAs[Real]("ε")
					b.FixAs[Real]("δ")
					positive := b.Assume()
					N, close := b.ObtainAs[Nat](
						"from some N on a(n) is within ε of l",
						"∃N:num. ∀n:num. N ≤ n ⇒ |a(n) - l| < ε",
						By(limit, positive, real_sequences.RealConvergesToDef.At(a, l)))
					b.Show(
						"past N the event is empty, of measure 0",
						Witness(N),
						Derive(func(c *Argument) {
							n := c.FixAs[Nat]("n")
							past := c.Assume()
							within := c.Have(
								"a(n) is within ε of l",
								"¬(ε < |a(n) - l|)",
								ByArith(At(close, n), past))
							empty := c.Have(
								"so no point is in the event",
								"{x:A | x ∈ Ω ∧ ε < |a(n) - l|} = ∅",
								BySets(within))
							c.Show(
								"μ(∅) = 0 lies below δ",
								By(
									emptyMeasure,
									empty,
									extended_nonneg_real.ZeroLe.At(c.TermAs[ExtendedNonnegReal]("extended_of_real(δ)"))))
						}))
				}))
		})
		// A row of independent centred square-integrable variables is a martingale difference row
		// for its natural filtration, the conditional variances being the second moments.
		naturalRow := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). " +
				"∀S:set(set(A)). " +
				"∀μ:(set(A) → extended_nonneg_real). " +
				"∀K:num. " +
				"∀X:(num → A → real).",
			Hypotheses: []string{
				"independent_variable_family(Ω, S, μ, {k:num | k < K}, X)",
				"∀k:num. " +
					"    k < K ⇒ expectation(Ω, S, μ, X(k)) = &0 ∧ real_integrable(Ω, S, μ, λx:A. X(k, x) * X(k, x))",
			},
			Conclusion: "martingale_difference_row(Ω, " +
				"    S, " +
				"    μ, " +
				"    λk:num. sigma_join(Ω, «pullbacks», {j:num | j < k ∧ j < K}), " +
				"    K, " +
				"    X, " +
				"    λk:num. λx:A. expectation(Ω, S, μ, λy:A. X(k, y) * X(k, y)))",
			Abbrev: Abbrev{
				{Name: "pullbacks", Text: "λj:num. pullback_sigma(Ω, X(j), borel_sets(real_topology))"},
			},
		}, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			K *Expr[Nat],
			X *Arrow2[Nat, A, Real],
			independent, centred Fact,
		) {
			row := a.TermAs[Set[Nat]]("{k:num | k < K}")
			pullbacks := a.TermAs[Fun[Nat, Set[Set[A]]]]("«pullbacks»")
			line := a.TermAs[Set[Real]]("𝕌")
			borel := a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")
			identity := a.TermAs[Fun[Real, Real]]("λu:real. u")
			natural := a.TermAs[Fun[Nat, Set[Set[A]]]](
				"λk:num. sigma_join(Ω, «pullbacks», {j:num | j < k ∧ j < K})")
			family := a.Have(
				"the space is a probability, and below K each X(i) is measurable",
				"probability_on(Ω, S, μ) ∧ (∀i:num. i < K ⇒ real_measurable(Ω, S, X(i)))",
				By(independent, independence.IndependentVariableFamilyMeasurable.At(Ω, S, μ, row, X)))
			pulledBack := a.Have(
				"so below K the σ-algebra each X(i) pulls back lies in S",
				"∀i:num. i < K ⇒ pullback_sigma(Ω, X(i), borel_sets(real_topology)) ⊆ S",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("i")
					below := b.Assume()
					b.Show(
						"S makes X(i) measurable, so it holds the least σ-algebra that does",
						By(family, below, borel_function.RealPullbackSigma.At(Ω, b.TermAs[Fun[A, Real]]("X(i)"))))
				}))
			space := a.Have(
				"S is a σ-algebra of subsets of Ω",
				"sigma_algebra_on(Ω, S) ∧ S ⊆ {s:set(A) | s ⊆ Ω}",
				By(
					family,
					probability_space.ProbabilityOnDef.At(Ω, S, μ),
					measure_space.MeasureOn.At(Ω, S, μ),
					sigma_algebra.SigmaAlgebraOnDef.At(Ω, S)))
			generated := a.Have(
				"each natural σ-algebra is generated inside S by the σ-algebras of the variables before k",
				"∀k:num. "+
					"    sigma_algebra_on(Ω, sigma_join(Ω, «pullbacks», {j:num | j < k ∧ j < K})) ∧ "+
					"    sigma_join(Ω, «pullbacks», {j:num | j < k ∧ j < K}) ⊆ S ∧ "+
					"    ⋃image(«pullbacks», {j:num | j < k ∧ j < K}) ⊆ "+
					"    sigma_join(Ω, «pullbacks», {j:num | j < k ∧ j < K})",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("k")
					before := b.TermAs[Set[Nat]]("{j:num | j < k ∧ j < K}")
					generators := b.TermAs[Set[Set[A]]]("⋃image(«pullbacks», {j:num | j < k ∧ j < K})")
					inS := b.Have(
						"the generators lie in S",
						"⋃image(«pullbacks», {j:num | j < k ∧ j < K}) ⊆ S",
						BySets(pulledBack))
					subsets := b.Have(
						"so they are subsets of Ω",
						"⋃image(«pullbacks», {j:num | j < k ∧ j < K}) ⊆ {s:set(A) | s ⊆ Ω}",
						BySets(inS, space))
					b.Show(
						"the σ-algebra they generate is the least one containing them",
						By(
							inS,
							space,
							subsets,
							sigma_algebra.SigmaJoinDef.At(Ω, pullbacks, before),
							sigma_algebra.GeneratedSigmaAlgebra.At(Ω, generators),
							sigma_algebra.GeneratedSigmaLeast.At(Ω, generators, S)))
				}))
			increasing := a.Have(
				"the natural σ-algebras increase",
				"∀k:num. "+
					"    sigma_join(Ω, «pullbacks», {j:num | j < k ∧ j < K}) ⊆ "+
					"    sigma_join(Ω, «pullbacks», {j:num | j < k + 1 ∧ j < K})",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("k")
					before := b.TermAs[Set[Nat]]("{j:num | j < k ∧ j < K}")
					upTo := b.TermAs[Set[Nat]]("{j:num | j < k + 1 ∧ j < K}")
					below := b.Have(
						"an index below k is below k + 1",
						"∀j:num. j < k ⇒ j < k + 1",
						ByArith())
					indices := b.Have(
						"so the indices before k are among those before k + 1",
						"{j:num | j < k ∧ j < K} ⊆ {j:num | j < k + 1 ∧ j < K}",
						BySets(below))
					generators := b.Have(
						"and the generators grow",
						"⋃image(«pullbacks», {j:num | j < k ∧ j < K}) ⊆ ⋃image(«pullbacks», {j:num | j < k + 1 ∧ j < K})",
						By(
							indices,
							set_image.ImageSubset.At(pullbacks, before, upTo),
							set_order.SubsetUnions.At(
								b.TermAs[Set[Set[Set[A]]]]("image(«pullbacks», {j:num | j < k ∧ j < K})"),
								b.TermAs[Set[Set[Set[A]]]]("image(«pullbacks», {j:num | j < k + 1 ∧ j < K})"))))
					next := b.TermAs[Set[Set[A]]]("sigma_join(Ω, «pullbacks», {j:num | j < k + 1 ∧ j < K})")
					b.Show(
						"the σ-algebra before k is generated inside the one before k + 1",
						By(
							At(generated, b.TermAs[Nat]("k + 1")),
							generators,
							sigma_algebra.SigmaJoinDef.At(Ω, pullbacks, before),
							set_order.SubsetTrans.At(
								b.TermAs[Set[Set[A]]]("⋃image(«pullbacks», {j:num | j < k ∧ j < K})"),
								b.TermAs[Set[Set[A]]]("⋃image(«pullbacks», {j:num | j < k + 1 ∧ j < K})"),
								next),
							sigma_algebra.GeneratedSigmaLeast.At(
								Ω, b.TermAs[Set[Set[A]]]("⋃image(«pullbacks», {j:num | j < k ∧ j < K})"), next)))
				}))
			borelLine := a.Have(
				"the identity and the square are Borel on the line",
				"real_measurable(𝕌, borel_sets(real_topology), λu:real. u) ∧ "+
					"real_measurable(𝕌, borel_sets(real_topology), λu:real. u * u)",
				By(
					borel_function.LineBorelSigmaAlgebra,
					measurable_function.RealMeasurableSquare.At(line, borel, identity),
					borel_function.RealMeasurableIdentity))
			clauses := a.Have(
				"below K each X(k) is a martingale difference for the natural "+
					"filtration, with conditional variance its second moment",
				Statement{
					Binders:    "∀k:num.",
					Hypotheses: []string{"k < K"},
					Conclusion: "real_measurable(Ω, sigma_join(Ω, «pullbacks», {j:num | j < k + 1 ∧ j < K}), X(k)) ∧ " +
						"is_cond_exp(Ω, S, μ, sigma_join(Ω, «pullbacks», {j:num | j < k ∧ j < K}), X(k), λx:A. &0) ∧ " +
						"is_cond_exp(Ω, " +
						"    S, " +
						"    μ, " +
						"    sigma_join(Ω, «pullbacks», {j:num | j < k ∧ j < K}), " +
						"    λx:A. X(k, x) * X(k, x), " +
						"    λx:A. expectation(Ω, S, μ, λy:A. X(k, y) * X(k, y)))",
				},
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]("k")
					inRow := b.Assume()
					before := b.TermAs[Set[Nat]]("{j:num | j < k ∧ j < K}")
					upTo := b.TermAs[Set[Nat]]("{j:num | j < k + 1 ∧ j < K}")
					variable := b.TermAs[Fun[A, Real]]("X(k)")
					own := b.TermAs[Set[Set[A]]]("pullback_sigma(Ω, X(k), borel_sets(real_topology))")
					next := b.TermAs[Set[Set[A]]]("sigma_join(Ω, «pullbacks», {j:num | j < k + 1 ∧ j < K})")
					order := b.Have(
						"k lies below k + 1 and not below itself",
						"k < k + 1 ∧ ¬(k < k)",
						ByArith())
					indices := b.Have(
						"k is in the row and among the indices before k + 1, not before k",
						"k ∈ {j:num | j < k + 1 ∧ j < K} ∧ "+
							"k ∈ {k:num | k < K} ∧ "+
							"k ∉ {j:num | j < k ∧ j < K} ∧ "+
							"{j:num | j < k ∧ j < K} ⊆ {k:num | k < K}",
						BySets(inRow, order))
					inside := b.Have(
						"the σ-algebra X(k) pulls back lies in the natural one before k + 1",
						"pullback_sigma(Ω, X(k), borel_sets(real_topology)) ⊆ "+
							"sigma_join(Ω, «pullbacks», {j:num | j < k + 1 ∧ j < K})",
						By(
							At(generated, b.TermAs[Nat]("k + 1")),
							indices,
							set_image.FunInImage.At(pullbacks, upTo, k),
							set_order.MemberSubsetUnions.At(
								b.TermAs[Set[Set[Set[A]]]]("image(«pullbacks», {j:num | j < k + 1 ∧ j < K})"), own),
							set_order.SubsetTrans.At(
								own, b.TermAs[Set[Set[A]]]("⋃image(«pullbacks», {j:num | j < k + 1 ∧ j < K})"), next)))
					measurable := b.Have(
						"so X(k), measurable for the σ-algebra it pulls back, is measurable for it",
						"real_measurable(Ω, sigma_join(Ω, «pullbacks», {j:num | j < k + 1 ∧ j < K}), X(k))",
						By(
							inside,
							borel_function.RealPullbackSigma.At(Ω, variable),
							measurable_function.RealMeasurableSourceMono.At(Ω, own, next, variable)))
					integrable := b.Have(
						"X(k) is measurable with integrable square on a probability space, so it is integrable",
						"real_integrable(Ω, S, μ, X(k))",
						By(
							At(centred, k),
							inRow,
							family,
							probability_space.SquareIntegrableIntegrable.At(Ω, S, μ, variable)))
					mean := b.Have(
						"independent of the variables before it, X(k) has its mean 0 as conditional mean",
						"is_cond_exp(Ω, S, μ, sigma_join(Ω, «pullbacks», {j:num | j < k ∧ j < K}), X(k), λx:A. &0)",
						By(
							At(centred, k),
							inRow,
							borelLine,
							indices,
							integrable,
							independent,
							independence.IndependentFamilyCondExp.At(Ω, S, μ, row, before, X, k, identity)))
					b.Show(
						"and its second moment as conditional variance",
						By(
							At(centred, k),
							inRow,
							borelLine,
							indices,
							measurable,
							independent,
							mean,
							independence.IndependentFamilyCondExp.At(
								Ω, S, μ, row, before, X, k, b.TermAs[Fun[Real, Real]]("λu:real. u * u"))))
				}))
			a.Show(
				"the natural σ-algebras form a filtration inside S, "+
					"along which the row is a martingale difference row",
				By(
					increasing,
					clauses,
					generated,
					family,
					martingale.MartingaleDifferenceRowDef.At(
						Ω,
						S,
						μ,
						natural,
						K,
						X,
						a.TermAs[Fun2[Nat, A, Real]]("λk:num. λx:A. expectation(Ω, S, μ, λy:A. X(k, y) * X(k, y))")),
					filtration.FiltrationDef.At(Ω, S, natural),
					probability_space.ProbabilityOnDef.At(Ω, S, μ),
					measure_space.MeasureOn.At(Ω, S, μ)))
		})
		return ctx.Theorem(headline, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			K *Arrow[Nat, Nat],
			ξ *Arrow2[Nat, Nat, Fun[A, Real]],
			independent, centred, variances, lindeberg Fact,
		) {
			space := a.Have(
				"independence carries a probability space",
				"probability_on(Ω, S, μ) ∧ μ(∅) = &0",
				By(
					At(independent, a.TermAs[Nat]("0")),
					independence.IndependentVariableFamilyMeasurable.At(
						Ω, S, μ, a.TermAs[Set[Nat]]("{k:num | k < K(0)}"), a.TermAs[Fun2[Nat, A, Real]]("ξ(0)")),
					probability_space.ProbabilityOnDef.At(Ω, S, μ),
					measure_space.MeasureOn.At(Ω, S, μ)))
			moments := a.Have(
				"the variance of a centred variable is its second moment",
				Statement{
					Binders:    "∀n k:num.",
					Hypotheses: []string{"k < K(n)"},
					Conclusion: "expectation(Ω, S, μ, λy:A. ξ(n, k, y) * ξ(n, k, y)) = variance(Ω, S, μ, ξ(n, k))",
				},
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					k := b.FixAs[Nat]("k")
					inRow := b.Assume()
					less := b.Have(
						"ξ(n, k) less its mean 0 is ξ(n, k)",
						"(λx:A. "+
							"    (ξ(n, k, x) - expectation(Ω, S, μ, ξ(n, k))) * "+
							"    (ξ(n, k, x) - expectation(Ω, S, μ, ξ(n, k)))) = "+
							"(λx:A. ξ(n, k, x) * ξ(n, k, x))",
						Funext(),
						ByArith(At(centred, n, k), inRow))
					b.Show(
						"by the definition of the variance",
						By(less, probability_space.VarianceDef.At(Ω, S, μ, b.TermAs[Fun[A, Real]]("ξ(n, k)"))))
				}))
			rowSums := a.Have(
				"so the row sums of second moments are those of the variances",
				"(λn:num. Σ_{k<K(n)} expectation(Ω, S, μ, λy:A. ξ(n, k, y) * ξ(n, k, y))) = "+
					"(λn:num. Σ_{k<K(n)} variance(Ω, S, μ, ξ(n, k)))",
				Funext(),
				Derive(func(b *Argument) {
					b.FixAs[Nat]("n")
					b.Show(
						"term by term",
						By(
							moments,
							real_sum.Congruence.At(
								b.TermAs[Set[Nat]]("{k:num | k < K(n)}"),
								b.TermAs[Fun[Nat, Real]]("λk:num. expectation(Ω, S, μ, λy:A. ξ(n, k, y) * ξ(n, k, y))"),
								b.TermAs[Fun[Nat, Real]]("λk:num. variance(Ω, S, μ, ξ(n, k))"))))
				}))
			limit := a.Have(
				"and tend to 1",
				"(λn:num. Σ_{k<K(n)} expectation(Ω, S, μ, λy:A. ξ(n, k, y) * ξ(n, k, y))) ⟶ &1",
				By(rowSums, variances))
			rows := a.Have(
				"each row is a martingale difference row for its natural filtration",
				"∀n:num. martingale_difference_row(Ω, S, μ, «naturalFiltration»(n), K(n), ξ(n), «secondMoment»(n))",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					b.Show(
						"its variables are independent, centred and square-integrable",
						By(
							At(centred, n),
							At(independent, n),
							At(naturalRow, Ω, S, μ, b.TermAs[Nat]("K(n)"), b.TermAs[Fun2[Nat, A, Real]]("ξ(n)"))))
				}))
			inMeasure := a.Have(
				"the conditional variances are constants whose row "+
					"sums tend to 1, so they converge to 1 in measure",
				"converges_in_measure(Ω, "+
					"    μ, "+
					"    λn:num. λx:A. Σ_{k<K(n)} expectation(Ω, S, μ, λy:A. ξ(n, k, y) * ξ(n, k, y)), "+
					"    λx:A. &1)",
				By(
					limit,
					space,
					At(
						constantsInMeasure,
						Ω,
						μ,
						a.TermAs[Fun[Nat, Real]]("λn:num. Σ_{k<K(n)} expectation(Ω, S, μ, λy:A. ξ(n, k, y) * ξ(n, k, y))"),
						a.TermAs[Real]("&1"))))
			a.Show(
				"MartingaleCentralLimit along the natural filtrations",
				By(
					rows,
					lindeberg,
					space,
					inMeasure,
					MartingaleCentralLimit.At(
						Ω,
						S,
						μ,
						a.TermAs[Fun3[Nat, Nat, Set[A], Bool]]("«naturalFiltration»"),
						K,
						ξ,
						a.TermAs[Fun3[Nat, Nat, A, Real]]("«secondMoment»"))))
		})
	}),
})}

// Lyapunov — Lyapunov's central limit theorem: the rows of LindebergFeller, with the row sums
// of the absolute moments of order 2 + δ tending to 0 in place of the Lindeberg condition.
// Where ε < |u|, u² ≤ ε^(−δ)·|u|^(2 + δ), the power splitting as u²·|u|^δ and ε^δ < |u|^δ;
// elsewhere the cut square is 0. So each Lindeberg term is at most ε^(−δ) times the moment of
// order 2 + δ, the Lindeberg sum lies between 0 and ε^(−δ) times the Lyapunov sum, it tends to
// 0, and LindebergFeller concludes.
var Lyapunov = lyapunovThm{family.Add(registry.ProofEntry{
	Name: "Lyapunov",
	Key:  "prop_e3e39b13a5d1fdd1",
	Reading: "δ is fixed and positive. The moments of order 2 + δ are " +
		"asked to be finite beside their row sums tending to 0, an expectation " +
		"of a function that is not integrable being read at its default.",
	Build: family.Sections(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀K:(num → num). " +
			"∀ξ:(num → num → A → real). " +
			"∀δ:real.",
		Hypotheses: []string{
			"∀n:num. independent_variable_family(Ω, S, μ, {k:num | k < K(n)}, ξ(n))",
			"∀n k:num. " +
				"    k < K(n) ⇒ " +
				"    expectation(Ω, S, μ, ξ(n, k)) = &0 ∧ real_integrable(Ω, S, μ, λx:A. ξ(n, k, x) * ξ(n, k, x))",
			"(λn:num. real_sum({k:num | k < K(n)}, λk:num. variance(Ω, S, μ, ξ(n, k)))) ⟶ &1",
			"&0 < δ",
			"∀n k:num. k < K(n) ⇒ real_integrable(Ω, S, μ, λx:A. real_rpow(|ξ(n, k, x)|, &2 + δ))",
			"(λn:num. " +
				"    real_sum({k:num | k < K(n)}, " +
				"        λk:num. expectation(Ω, S, μ, λx:A. real_rpow(|ξ(n, k, x)|, &2 + δ)))) ⟶ " +
				"&0",
		},
		Conclusion: "weakly_converges(real_topology, " +
			"    λn:num. pushforward_measure(Ω, μ, λx:A. real_sum({k:num | k < K(n)}, λk:num. ξ(n, k, x))), " +
			"    normal_distribution(&0, &1))",
		Abbrev: Abbrev{
			{Name: "lyapunovSum", Text: "λn:num. " +
				"    Σ_{k<K(n)} expectation(Ω, S, μ, λx:A. real_rpow(|ξ(n, k, x)|, &2 + δ))"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		// Where ε < |u| the square of u is at most ε^(−δ)·|u|^(2 + δ), and elsewhere the cut
		// square is 0.
		cutSquare := ctx.Lemma(Statement{
			Binders:    "∀ε δ u:real.",
			Hypotheses: []string{"&0 < ε", "&0 < δ"},
			Conclusion: "&0 ≤ COND(ε < |u|, u * u, &0) ∧ " +
				"COND(ε < |u|, u * u, &0) ≤ real_rpow(ε, -δ) * real_rpow(|u|, &2 + δ)",
		}, func(a *Argument, ε, δ, u *Expr[Real], positive, positiveδ Fact) {
			two := a.TermAs[Real]("&2")
			size := a.TermAs[Real]("|u|")
			a.Cases(a.Term("ε < |u|"))
			a.When(
				"on the event the cut square is u²",
				func(b *Argument, beyond Fact) {
					split := b.Have(
						"the power splits as u²·|u|^δ",
						"real_rpow(|u|, &2 + δ) = u * u * real_rpow(|u|, δ)",
						ByArith(
							beyond,
							positive,
							real_rpow.RpowAdd.At(size, two, δ),
							real_rpow.RpowNat.At(size, b.TermAs[Nat]("2")),
							real_pow.AbsPow.At(u, b.TermAs[Nat]("2")),
							real_sgn_abs.AbsFixedIffNonneg.At(b.TermAs[Real]("real_pow(u, 2)")),
							real_sgn_abs.AbsNonneg.At(u),
							real_order_ring.SquareNonneg.At(u)))
					below := b.TermAs[Real]("real_rpow(ε, δ)")
					nonnegative := b.Have(
						"ε is not negative",
						"&0 ≤ ε",
						ByArith(positive))
					powers := b.Have(
						"ε^δ is positive and below |u|^δ, and ε^(−δ) is its inverse",
						"real_rpow(ε, δ) < real_rpow(|u|, δ) ∧ "+
							"&0 < real_rpow(ε, δ) ∧ "+
							"real_rpow(ε, -δ) = real_inv(real_rpow(ε, δ))",
						By(
							nonnegative,
							beyond,
							positive,
							positiveδ,
							real_rpow.RpowLessBase.At(ε, size, δ),
							real_rpow.RpowPositive.At(ε, δ),
							real_rpow.RpowNeg.At(ε, δ)))
					inverse := b.Have(
						"so ε^δ is not 0 and its inverse is positive",
						"real_rpow(ε, δ) ≠ &0 ∧ &0 < real_inv(real_rpow(ε, δ))",
						ByArith(powers, real_order_field.InvPos.At(below)))
					gap := b.Have(
						"|u|^δ exceeds ε^δ",
						"&0 < real_rpow(|u|, δ) - real_rpow(ε, δ)",
						ByArith(powers))
					ratio := b.Have(
						"so ε^(−δ)·|u|^δ is at least 1",
						"&1 ≤ real_rpow(ε, -δ) * real_rpow(|u|, δ)",
						ByArith(
							gap,
							inverse,
							powers,
							real_order_ring.MulPos.At(
								b.TermAs[Real]("real_inv(real_rpow(ε, δ))"), b.TermAs[Real]("real_rpow(|u|, δ) - real_rpow(ε, δ)")),
							real_construction.MulLeftInverse.At(below)))
					square := b.Have(
						"u² is not negative",
						"&0 ≤ u * u",
						ByArith(real_order_ring.SquareNonneg.At(u)))
					scaled := b.Have(
						"the cut square is u², and ε^(−δ)·|u|^(2 + δ) is ε^(−δ) times u²·|u|^δ",
						"real_rpow(ε, -δ) * real_rpow(|u|, &2 + δ) = real_rpow(ε, -δ) * (u * u * real_rpow(|u|, δ)) ∧ "+
							"COND(ε < |u|, u * u, &0) = u * u",
						By(split, beyond))
					regrouped := b.Have(
						"which is u² times ε^(−δ)·|u|^δ",
						"COND(ε < |u|, u * u, &0) = u * u ∧ "+
							"real_rpow(ε, -δ) * real_rpow(|u|, &2 + δ) = u * u * (real_rpow(ε, -δ) * real_rpow(|u|, δ))",
						ByArith(scaled))
					b.Show(
						"u² is at most u² times a factor of at least 1",
						ByArith(
							ratio,
							regrouped,
							square,
							real_order_ring.LessEqMulLeft.At(
								b.TermAs[Real]("u * u"),
								b.TermAs[Real]("&1"),
								b.TermAs[Real]("real_rpow(ε, -δ) * real_rpow(|u|, δ)"))))
				})
			a.Otherwise(
				"off the event the cut square is 0, below a product of powers",
				func(b *Argument, within Fact) {
					b.Show(
						"real powers are not negative",
						ByArith(
							within,
							real_rpow.RpowNonneg.At(ε, b.TermAs[Real]("-δ")),
							real_rpow.RpowNonneg.At(size, b.TermAs[Real]("&2 + δ"))))
				})
		})
		// The Lindeberg term of a square-integrable variable is at most ε^(−δ) times its moment of
		// order 2 + δ: integrate cutSquare, the cut to the tail event being integrable.
		lindebergTerm := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). " +
				"∀S:set(set(A)). " +
				"∀μ:(set(A) → extended_nonneg_real). " +
				"∀X:(A → real). " +
				"∀ε δ:real.",
			Hypotheses: []string{
				"probability_on(Ω, S, μ)",
				"real_measurable(Ω, S, X)",
				"real_integrable(Ω, S, μ, λx:A. X(x) * X(x))",
				"real_integrable(Ω, S, μ, λx:A. real_rpow(|X(x)|, &2 + δ))",
				"&0 < ε",
				"&0 < δ",
			},
			Conclusion: "&0 ≤ event_integral(Ω, S, μ, {x:A | ε < |X(x)|}, λx:A. X(x) * X(x)) ∧ " +
				"event_integral(Ω, S, μ, {x:A | ε < |X(x)|}, λx:A. X(x) * X(x)) ≤ " +
				"real_rpow(ε, -δ) * expectation(Ω, S, μ, λx:A. real_rpow(|X(x)|, &2 + δ))",
		}, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			X *Arrow[A, Real],
			ε, δ *Expr[Real],
			probability, measurable, square, moment, positive, positiveδ Fact,
		) {
			factor := a.TermAs[Real]("real_rpow(ε, -δ)")
			power := a.TermAs[Fun[A, Real]]("λx:A. real_rpow(|X(x)|, &2 + δ)")
			cut := a.TermAs[Fun[A, Real]]("λx:A. COND(x ∈ {x:A | ε < |X(x)|}, X(x) * X(x), &0)")
			space := a.Have(
				"a probability is a measure on a σ-algebra",
				"measure_on(Ω, S, μ) ∧ sigma_algebra_on(Ω, S)",
				By(
					probability,
					probability_space.ProbabilityOnDef.At(Ω, S, μ),
					measure_space.MeasureOn.At(Ω, S, μ)))
			tail := a.Have(
				"the tail event is measurable, |X| being measurable",
				"{x:A | x ∈ Ω ∧ ε < |X(x)|} ∈ S",
				By(
					space,
					measurable,
					measurable_function.RealMeasurableAbs.At(Ω, S, X),
					measurable_function.RealMeasurableIffRay.At(Ω, S, a.TermAs[Fun[A, Real]]("λx:A. |X(x)|"))))
			onCarrier := a.Have(
				"on Ω the cut to the tail event is the cut to {ε < |X|}",
				Statement{
					Binders:    "∀x:A.",
					Hypotheses: []string{"x ∈ Ω"},
					Conclusion: "COND(x ∈ {x:A | x ∈ Ω ∧ ε < |X(x)|}, X(x) * X(x), &0) = " +
						"COND(x ∈ {x:A | ε < |X(x)|}, X(x) * X(x), &0)",
				},
				BySets())
			integrable := a.Have(
				"the cut square and ε^(−δ)·|X|^(2 + δ) are integrable",
				"real_integrable(Ω, S, μ, λx:A. COND(x ∈ {x:A | ε < |X(x)|}, X(x) * X(x), &0)) ∧ "+
					"real_integrable(Ω, S, μ, λx:A. real_rpow(ε, -δ) * real_rpow(|X(x)|, &2 + δ))",
				By(
					onCarrier,
					space,
					tail,
					square,
					moment,
					event_integral.IntegrableOnEvent.At(
						Ω,
						S,
						μ,
						a.TermAs[Set[A]]("{x:A | x ∈ Ω ∧ ε < |X(x)|}"),
						a.TermAs[Fun[A, Real]]("λx:A. X(x) * X(x)")),
					measure_integral.RealIntegrableEqOn.At(
						Ω,
						S,
						μ,
						a.TermAs[Fun[A, Real]]("λx:A. COND(x ∈ {x:A | x ∈ Ω ∧ ε < |X(x)|}, X(x) * X(x), &0)"),
						cut),
					measure_integral.IntegrableScale.At(Ω, S, μ, power, factor)))
			pointwise := a.Have(
				"pointwise the cut square lies between 0 and ε^(−δ)·|X|^(2 + δ)",
				Statement{
					Binders:    "∀x:A.",
					Hypotheses: []string{"x ∈ Ω"},
					Conclusion: "&0 ≤ COND(x ∈ {x:A | ε < |X(x)|}, X(x) * X(x), &0) ∧ " +
						"COND(x ∈ {x:A | ε < |X(x)|}, X(x) * X(x), &0) ≤ real_rpow(ε, -δ) * real_rpow(|X(x)|, &2 + δ)",
				},
				Derive(func(b *Argument) {
					b.FixAs[A]("x")
					b.Assume()
					b.Show(
						"cutSquare at X(x)",
						By(positive, positiveδ, At(cutSquare, ε, δ, b.TermAs[Real]("X(x)"))))
				}))
			a.Show(
				"the integral of the cut square is the Lindeberg term, between 0 and ε^(−δ) times the moment",
				By(
					pointwise,
					space,
					integrable,
					event_integral.EventIntegralDef.At(
						Ω, S, μ, a.TermAs[Set[A]]("{x:A | ε < |X(x)|}"), a.TermAs[Fun[A, Real]]("λx:A. X(x) * X(x)")),
					measure_integral.IntegralNonneg.At(Ω, S, μ, cut),
					measure_integral.IntegralMono.At(
						Ω, S, μ, cut, a.TermAs[Fun[A, Real]]("λx:A. real_rpow(ε, -δ) * real_rpow(|X(x)|, &2 + δ)")),
					measure_integral.IntegralScale.At(Ω, S, μ, power, factor),
					probability_space.ExpectationDef.At(Ω, S, μ, power)))
		})
		return ctx.Theorem(headline, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			K *Arrow[Nat, Nat],
			ξ *Arrow2[Nat, Nat, Fun[A, Real]],
			δ *Expr[Real],
			independent, centred, variances, positiveδ, moments, lyapunov Fact,
		) {
			measurable := a.Have(
				"each ξ(n, k) is measurable",
				"∀n k:num. k < K(n) ⇒ real_measurable(Ω, S, ξ(n, k))",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					b.FixAs[Nat]("k")
					inRow := b.Assume()
					b.Show(
						"by the independence of row n",
						By(
							At(independent, n),
							inRow,
							independence.IndependentVariableFamilyMeasurable.At(
								Ω, S, μ, b.TermAs[Set[Nat]]("{k:num | k < K(n)}"), b.TermAs[Fun2[Nat, A, Real]]("ξ(n)"))))
				}))
			probability := a.Have(
				"independence carries a probability space",
				"probability_on(Ω, S, μ)",
				By(
					At(independent, a.TermAs[Nat]("0")),
					independence.IndependentVariableFamilyMeasurable.At(
						Ω, S, μ, a.TermAs[Set[Nat]]("{k:num | k < K(0)}"), a.TermAs[Fun2[Nat, A, Real]]("ξ(0)"))))
			squeezed := a.Have(
				"each Lindeberg sum lies between 0 and ε^(−δ) times the Lyapunov sum",
				Statement{
					Binders:    "∀ε:real.",
					Hypotheses: []string{"&0 < ε"},
					Conclusion: "∀n:num. " +
						"    &0 ≤ lindeberg_sum(Ω, S, μ, K(n), ξ(n), ε) ∧ " +
						"    lindeberg_sum(Ω, S, μ, K(n), ξ(n), ε) ≤ real_rpow(ε, -δ) * «lyapunovSum»(n)",
				},
				Derive(func(b *Argument) {
					ε := b.FixAs[Real]("ε")
					positive := b.Assume()
					n := b.FixAs[Nat]("n")
					row := b.TermAs[Set[Nat]]("{k:num | k < K(n)}")
					term := b.TermAs[Fun[Nat, Real]](
						"λk:num. event_integral(Ω, S, μ, {x:A | ε < |ξ(n, k, x)|}, λx:A. ξ(n, k, x) * ξ(n, k, x))")
					moment := b.TermAs[Fun[Nat, Real]](
						"λk:num. expectation(Ω, S, μ, λx:A. real_rpow(|ξ(n, k, x)|, &2 + δ))")
					factor := b.TermAs[Real]("real_rpow(ε, -δ)")
					terms := b.Have(
						"each term lies between 0 and ε^(−δ) times its moment",
						Statement{
							Binders:    "∀k:num.",
							Hypotheses: []string{"k ∈ {k:num | k < K(n)}"},
							Conclusion: "&0 ≤ " +
								"event_integral(Ω, S, μ, {x:A | ε < |ξ(n, k, x)|}, λx:A. ξ(n, k, x) * ξ(n, k, x)) ∧ " +
								"event_integral(Ω, S, μ, {x:A | ε < |ξ(n, k, x)|}, λx:A. ξ(n, k, x) * ξ(n, k, x)) ≤ " +
								"real_rpow(ε, -δ) * expectation(Ω, S, μ, λx:A. real_rpow(|ξ(n, k, x)|, &2 + δ))",
						},
						Derive(func(c *Argument) {
							k := c.FixAs[Nat]("k")
							inRow := c.Assume()
							c.Show(
								"lindebergTerm at ξ(n, k)",
								By(
									At(centred, n, k),
									At(measurable, n, k),
									At(moments, n, k),
									positiveδ,
									positive,
									inRow,
									probability,
									At(lindebergTerm, Ω, S, μ, c.TermAs[Fun[A, Real]]("ξ(n, k)"), ε, δ)))
						}))
					b.Show(
						"sum the terms over the row",
						By(
							terms,
							lindeberg_bound.LindebergSumDef.At(
								Ω, S, μ, b.TermAs[Nat]("K(n)"), b.TermAs[Fun2[Nat, A, Real]]("ξ(n)"), ε),
							num_segment.FiniteBelowStrict.At(b.TermAs[Nat]("K(n)")),
							real_sum.Nonneg.At(row, term),
							real_sum.Monotone.At(
								row,
								term,
								b.TermAs[Fun[Nat, Real]](
									"λk:num. real_rpow(ε, -δ) * expectation(Ω, S, μ, λx:A. real_rpow(|ξ(n, k, x)|, &2 + δ))")),
							real_sum.ScalarLeft.At(factor, moment, row)))
				}))
			lindeberg := a.Have(
				"so the Lindeberg sums tend to 0",
				"∀ε:real. &0 < ε ⇒ (λn:num. lindeberg_sum(Ω, S, μ, K(n), ξ(n), ε)) ⟶ &0",
				Derive(func(b *Argument) {
					ε := b.FixAs[Real]("ε")
					positive := b.Assume()
					upper := b.TermAs[Fun[Nat, Real]]("λn:num. real_rpow(ε, -δ) * «lyapunovSum»(n)")
					scaled := b.Have(
						"ε^(−δ) times the Lyapunov sums tends to ε^(−δ)·0 = 0",
						"(λn:num. real_rpow(ε, -δ) * «lyapunovSum»(n)) ⟶ &0",
						ByArith(
							lyapunov,
							real_sequences.LimitScale.At(
								b.TermAs[Fun[Nat, Real]]("«lyapunovSum»"),
								b.TermAs[Real]("&0"),
								b.TermAs[Real]("real_rpow(ε, -δ)"))))
					b.Show(
						"squeezed between 0 and it",
						By(
							At(squeezed, ε),
							positive,
							scaled,
							real_sequences.LimitConst.At(b.TermAs[Real]("&0")),
							real_sequences.LimitSqueeze.At(
								b.TermAs[Fun[Nat, Real]]("λn:num. &0"),
								b.TermAs[Fun[Nat, Real]]("λn:num. lindeberg_sum(Ω, S, μ, K(n), ξ(n), ε)"),
								upper,
								b.TermAs[Real]("&0"),
								b.TermAs[Nat]("0"))))
				}))
			a.Show(
				"LindebergFeller",
				By(centred, independent, lindeberg, variances, LindebergFeller.At(Ω, S, μ, K, ξ)))
		})
	}),
})}
