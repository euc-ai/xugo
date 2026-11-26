package lebesgue_riemann

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/measure/event_integral"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_integral"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/real/lebesgue_integral"
	"github.com/euc-ai/xugo/library/proofs/real/lebesgue_measure"
	"github.com/euc-ai/xugo/library/proofs/real/real_continuous"
	"github.com/euc-ai/xugo/library/proofs/real/real_integral"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_topology"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/sigma_algebra"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// LebesgueIntegralInterval — a function continuous on ⟦a, b⟧ and zero off
// it is Lebesgue integrable, with its Riemann integral over ⟦a, b⟧ for
// Lebesgue integral.
var LebesgueIntegralInterval = lebesgueIntegralIntervalThm{family.Add(registry.ProofEntry{
	Name: "LebesgueIntegralInterval",
	Key:  "prop_aee2132729813e26",
	Reading: "Continuity is asked within ⟦a, b⟧ only: f " +
		"may jump at a or b. At a = b both integrals are 0.",
	Build: family.Sections(Statement{
		Binders: "∀f:(real → real). ∀a b:real.",
		Hypotheses: []string{
			"a ≤ b",
			"real_continuous_on(⟦a, b⟧, f)",
			"∀x:real. x ∉ ⟦a, b⟧ ⇒ f(x) = &0",
		},
		Conclusion: "lebesgue_integrable(f) ∧ lebesgue_integral(f) = real_integral(f, a, b)",
		Abbrev: Abbrev{
			{Name: "indicator", Text: "λE:set(real). λd:real. «cut»(E, λx:real. d)"},
			{Name: "event", Text: "λE:set(real). λv:(real → real). " +
				"    event_integral(𝕌, «lebesgueSets», lebesgue_outer_measure, E, v)"},
			{Name: "partition", Text: "λa:real. λb:real. λn:num. λp:(num → real). " +
				"    p(0) = a ∧ p(n + 1) = b ∧ (∀i:num. i ≤ n ⇒ p(i) ≤ p(i + 1))"},
			{Name: "riemannSum", Text: "λf:(real → real). λn:num. λp:(num → real). λt:(num → real). " +
				"    Σ_{i∈0 .. n} f(t(i)) * (p(i + 1) - p(i))"},
			{Name: "cell", Text: "λi:num. ⟬p(i), p(i + 1)⟧"},
			{Name: "width", Text: "λi:num. p(i + 1) - p(i)"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		measurableExtension := ctx.Lemma(Statement{
			Binders: "∀f:(real → real). ∀a b:real.",
			Hypotheses: []string{
				"real_continuous_on(⟦a, b⟧, f)",
				"∀x:real. x ∉ ⟦a, b⟧ ⇒ f(x) = &0",
			},
			Conclusion: "lebesgue_measurable_function(f)",
			Abbrev: Abbrev{
				{Name: "relativeTopology", Text: "subtopology(real_topology, ⟦a, b⟧)"},
				{Name: "relativeRay", Text: "{x:real | x ∈ ⟦a, b⟧ ∧ c < f(x)}"},
				{Name: "relativePreimage", Text: "preimage_on(⋃«relativeTopology», f, {y:real | c < y})"},
			},
		}, func(arg *Argument, f *Arrow[Real, Real], a, b *Expr[Real], cont, outside Fact) {
			line := arg.TermAs[Set[Real]]("𝕌")
			sets := arg.TermAs[Set[Set[Real]]]("«lebesgueSets»")
			interval := arg.TermAs[Set[Real]]("⟦a, b⟧")
			realTopology := arg.TermAs[Set[Set[Real]]]("real_topology")
			relativeTopology := arg.TermAs[Set[Set[Real]]]("«relativeTopology»")
			continuousMap := arg.Have(
				"f is continuous from the interval subspace",
				"continuous_map(«relativeTopology», real_topology, f)",
				By(cont, real_continuous.ContinuousOnIffMap.At(f, interval)))
			relativeCarrier := arg.Have(
				"the interval is the carrier of its subspace",
				"⋃«relativeTopology» = ⟦a, b⟧",
				Simp(Fwd(topological_space.SubtopologySpace), Fwd(real_topology.RealSpace)),
				BySets())
			levels := MakeProp(arg.Term("∀c:real. lebesgue_measurable({x:real | c < f(x)})"))
			arg.Do(Suffices(
				levels,
				"f is Lebesgue measurable when every upper level set {x | c < f(x)} is measurable",
				Simp(Fwd(lebesgue_integral.LebesgueMeasurableFunctionDef)),
				By(ResidentHyp(levels))))
			c := arg.FixAs[Real]("c")
			preimage := arg.TermAs[Set[Real]]("«relativePreimage»")
			v, relativeOpen := arg.ObtainAs[Set[Real]](
				"an ambient open set cuts out the relative preimage",
				"∃v:set(real). «relativePreimage» = v ∩ ⟦a, b⟧ ∧ v ∈ real_topology",
				By(
					continuousMap,
					real_topology.RayAboveOpen.At(c),
					continuous.ContinuousMap.At(relativeTopology, realTopology, f),
					topological_space.OpenInSubtopology.At(realTopology, interval, preimage)))
			open := arg.Conjuncts(
				relativeOpen,
				"the relative preimage is the intersection",
				"v is open in the line")
			relative := arg.Have(
				"the relative upper level set is that intersection",
				"«relativeRay» = v ∩ ⟦a, b⟧",
				BySets(relativeCarrier, open[0]))
			members := arg.Have(
				"the open set and the interval are both measurable",
				"v ∈ «lebesgueSets» ∧ ⟦a, b⟧ ∈ «lebesgueSets»",
				BySets(
					open[1],
					lebesgue_measure.MeasurableOpen.At(v),
					lebesgue_measure.MeasurableClosedInterval.At(a, b)))
			relativeMeasurable := arg.Have(
				"their intersection is measurable",
				"«relativeRay» ∈ «lebesgueSets»",
				By(
					relative,
					members,
					lebesgue_measure.LebesgueSigmaAlgebra,
					sigma_algebra.SigmaFiniteOperations.At(line, sets)))
			arg.Cases(arg.TermAs[Bool]("c < &0"))
			arg.When(
				"a negative threshold includes the complement of the interval",
				func(d *Argument, negative Fact) {
					ray := d.Have(
						"the full level set adds the complement",
						"{x:real | c < f(x)} = «relativeRay» ∪ (𝕌 ∖ ⟦a, b⟧)",
						BySets(outside, negative))
					complement := d.Have(
						"the complement is measurable",
						"(𝕌 ∖ ⟦a, b⟧) ∈ «lebesgueSets»",
						By(members, lebesgue_measure.LebesgueSigmaAlgebra, sigma_algebra.SigmaAlgebraOnDef.At(line, sets)))
					union := d.Have(
						"the full level set is a union of measurable sets",
						"(«relativeRay» ∪ (𝕌 ∖ ⟦a, b⟧)) ∈ «lebesgueSets»",
						By(
							relativeMeasurable,
							complement,
							lebesgue_measure.LebesgueSigmaAlgebra,
							sigma_algebra.SigmaFiniteOperations.At(line, sets)))
					d.Show(
						"the upper level set is Lebesgue measurable",
						Simp(Fwd(ray)),
						BySets(union))
				})
			arg.Otherwise(
				"a nonnegative threshold includes only points in the interval",
				func(d *Argument, nonnegative Fact) {
					ray := d.Have(
						"the full level set equals the relative one",
						"{x:real | c < f(x)} = «relativeRay»",
						BySets(outside, nonnegative))
					d.Show(
						"the relative level set is measurable",
						Simp(Fwd(ray)),
						BySets(relativeMeasurable))
				})
		})

		integrableIndicator := ctx.Lemma(Statement{
			Binders:    "∀E:set(real). ∀c:real.",
			Hypotheses: []string{"lebesgue_measurable(E)", "lebesgue_outer_measure(E) ≠ extended_infinity"},
			Conclusion: "real_integrable(𝕌, «lebesgueSets», lebesgue_outer_measure, «indicator»(E, c))",
		}, func(arg *Argument, E *Expr[Set[Real]], c *Expr[Real], measurable, finite Fact) {
			line := arg.TermAs[Set[Real]]("𝕌")
			sets := arg.TermAs[Set[Set[Real]]]("«lebesgueSets»")
			mass := arg.TermAs[Fun[Set[Real], extended_nonneg_real.ExtendedNonnegReal]](
				"lebesgue_outer_measure")
			event := arg.Have(
				"E is in the Lebesgue sigma algebra",
				"E ∈ «lebesgueSets»",
				BySets(measurable))
			arg.Show(
				"the cut of a constant to a set of finite measure is integrable",
				By(
					event,
					finite,
					lebesgue_measure.LebesgueMeasureOn,
					measure_integral.IntegrableIndicator.At(line, sets, mass, E, c)))
		})

		cellMass := ctx.Lemma(Statement{
			Binders:    "∀a b:real.",
			Hypotheses: []string{"a ≤ b"},
			Conclusion: "lebesgue_measurable(⟬a, b⟧) ∧ " +
				"lebesgue_outer_measure(⟬a, b⟧) = extended_of_real(b - a)",
		}, func(arg *Argument, a, b *Expr[Real], ordered Fact) {
			arg.Show(
				"a half-open interval is measurable and has the same length as the closed interval",
				SplitConj(
					Case(
						"the cell is the intersection of two measurable rays",
						Derive(func(d *Argument) {
							split := d.Have(
								"the two endpoint inequalities describe the cell",
								"⟬a, b⟧ = {x:real | a < x} ∩ {x:real | x ≤ b}",
								BySets())
							rays := d.Have(
								"both rays lie in the Lebesgue sigma algebra",
								"{x:real | a < x} ∈ «lebesgueSets» ∧ {x:real | x ≤ b} ∈ «lebesgueSets»",
								BySets(lebesgue_measure.MeasurableHalfLine.At(a), lebesgue_measure.MeasurableAtMost.At(b)))
							cell := d.Have(
								"their intersection is in the Lebesgue sigma algebra",
								"⟬a, b⟧ ∈ «lebesgueSets»",
								By(
									split,
									rays,
									lebesgue_measure.LebesgueSigmaAlgebra,
									sigma_algebra.SigmaFiniteOperations.At(
										d.TermAs[Set[Real]]("𝕌"), d.TermAs[Set[Set[Real]]]("«lebesgueSets»"))))
							d.Show(
								"the cell is Lebesgue measurable",
								BySets(cell))
						})),
					Case(
						"the open and closed intervals give the same length",
						Derive(func(d *Argument) {
							inside := d.Have(
								"the half-open cell is between the open and closed intervals",
								"⟬a, b⟭ ⊆ ⟬a, b⟧ ∧ ⟬a, b⟧ ⊆ ⟦a, b⟧",
								BySets(real_order_ring.LessEqOfLessThan))
							opened := d.TermAs[Set[Real]]("⟬a, b⟭")
							cell := d.TermAs[Set[Real]]("⟬a, b⟧")
							closed := d.TermAs[Set[Real]]("⟦a, b⟧")
							d.Show(
								"monotonicity gives the common length",
								By(
									ordered,
									inside,
									lebesgue_measure.OuterMeasureMono.At(opened, cell),
									lebesgue_measure.OuterMeasureMono.At(cell, closed),
									lebesgue_measure.OuterMeasureOpenInterval.At(a, b),
									lebesgue_measure.OuterMeasureClosedInterval.At(a, b),
									extended_nonneg_real.LeAntisym))
						}))))
		})

		cellBounds := ctx.Lemma(Statement{
			Binders: "∀f:(real → real). ∀a b l u:real.",
			Hypotheses: []string{
				"a ≤ b",
				"real_integrable(𝕌, «lebesgueSets», lebesgue_outer_measure, f)",
				"∀x:real. x ∈ ⟬a, b⟧ ⇒ l ≤ f(x) ∧ f(x) ≤ u",
			},
			Conclusion: "l * (b - a) ≤ «event»(⟬a, b⟧, f) ∧ «event»(⟬a, b⟧, f) ≤ u * (b - a)",
		}, func(
			arg *Argument,
			f *Arrow[Real, Real],
			a, b, l, u *Expr[Real],
			ordered, integrable, bounds Fact,
		) {
			line := arg.TermAs[Set[Real]]("𝕌")
			sets := arg.TermAs[Set[Set[Real]]]("«lebesgueSets»")
			mass := arg.TermAs[Fun[Set[Real], extended_nonneg_real.ExtendedNonnegReal]](
				"lebesgue_outer_measure")
			E := arg.TermAs[Set[Real]]("⟬a, b⟧")
			width := arg.TermAs[Real]("b - a")
			data := arg.Conjuncts(
				GroupPremises(ordered, At(cellMass, a, b)),
				"the cell is Lebesgue measurable",
				"the cell has its length as mass")
			event := arg.Have(
				"the cell is in the Lebesgue sigma algebra",
				"⟬a, b⟧ ∈ «lebesgueSets»",
				BySets(data[0]))
			finite := arg.Have(
				"the cell has finite mass",
				"lebesgue_outer_measure(⟬a, b⟧) ≠ extended_infinity",
				By(Normalized, data[1], extended_nonneg_real.OfRealNotInfinity.At(width)))
			nonnegative := arg.Have(
				"the width is nonnegative",
				"&0 ≤ b - a",
				ByArith(ordered))
			length := arg.Have(
				"reading the cell mass as a real number gives the width",
				"extended_to_real(lebesgue_outer_measure(⟬a, b⟧)) = b - a",
				By(Normalized, data[1], nonnegative, extended_nonneg_real.ToRealOfReal.At(width)))
			cut := arg.TermAs[Fun[Real, Real]]("«cut»(⟬a, b⟧, f)")
			lower := arg.TermAs[Fun[Real, Real]]("«indicator»(⟬a, b⟧, l)")
			upper := arg.TermAs[Fun[Real, Real]]("«indicator»(⟬a, b⟧, u)")
			cutIntegrable := arg.Have(
				"f cut to the cell is integrable",
				"real_integrable(𝕌, «lebesgueSets», lebesgue_outer_measure, «cut»(⟬a, b⟧, f))",
				By(
					event,
					integrable,
					lebesgue_measure.LebesgueSigmaAlgebra,
					event_integral.IntegrableOnEvent.At(line, sets, mass, E, f)))
			lowerIntegrable := arg.Have(
				"the lower constant cut to the cell is integrable",
				"real_integrable(𝕌, «lebesgueSets», lebesgue_outer_measure, «indicator»(⟬a, b⟧, l))",
				By(data[0], finite, At(integrableIndicator, E, l)))
			upperIntegrable := arg.Have(
				"the upper constant cut to the cell is integrable",
				"real_integrable(𝕌, «lebesgueSets», lebesgue_outer_measure, «indicator»(⟬a, b⟧, u))",
				By(data[0], finite, At(integrableIndicator, E, u)))
			below := arg.Have(
				"the lower indicator bounds the cut from below",
				"∀x:real. x ∈ 𝕌 ⇒ «indicator»(⟬a, b⟧, l, x) ≤ «cut»(⟬a, b⟧, f, x)",
				BySets(bounds, real_order_ring.LessEqRefl))
			above := arg.Have(
				"the upper indicator bounds the cut from above",
				"∀x:real. x ∈ 𝕌 ⇒ «cut»(⟬a, b⟧, f, x) ≤ «indicator»(⟬a, b⟧, u, x)",
				BySets(bounds, real_order_ring.LessEqRefl))
			fCut := event_integral.EventIntegralDef.At(line, sets, mass, E, f)
			arg.Show(
				"integrate the pointwise bounds and evaluate the constants",
				SplitConj(
					Case(
						"integrating the lower constant gives the lower bound",
						By(
							lowerIntegrable,
							cutIntegrable,
							below,
							length,
							event,
							lebesgue_measure.LebesgueMeasureOn,
							measure_integral.IntegralMono.At(line, sets, mass, lower, cut),
							event_integral.EventIntegralDef.At(line, sets, mass, E, arg.TermAs[Fun[Real, Real]]("λx:real. l")),
							event_integral.EventIntegralConst.At(line, sets, mass, E, l),
							fCut)),
					Case(
						"integrating the upper constant gives the upper bound",
						By(
							upperIntegrable,
							cutIntegrable,
							above,
							length,
							event,
							lebesgue_measure.LebesgueMeasureOn,
							measure_integral.IntegralMono.At(line, sets, mass, cut, upper),
							event_integral.EventIntegralDef.At(line, sets, mass, E, arg.TermAs[Fun[Real, Real]]("λx:real. u")),
							event_integral.EventIntegralConst.At(line, sets, mass, E, u),
							fCut))))
		})

		meanTag := ctx.Lemma(Statement{
			Binders: "∀f:(real → real). ∀a b:real.",
			Hypotheses: []string{
				"a ≤ b",
				"real_continuous_on(⟦a, b⟧, f)",
				"real_integrable(𝕌, «lebesgueSets», lebesgue_outer_measure, f)",
			},
			Conclusion: "∃t:real. a ≤ t ∧ t ≤ b ∧ «event»(⟬a, b⟧, f) = f(t) * (b - a)",
			Abbrev: Abbrev{
				{Name: "average", Text: "«event»(⟬a, b⟧, f) / (b - a)"},
			},
		}, func(arg *Argument, f *Arrow[Real, Real], a, b *Expr[Real], ordered, cont, integrable Fact) {
			m, minSpec := arg.ObtainAs[Real](
				"f attains a minimum on the closed cell",
				"∃m:real. a ≤ m ∧ m ≤ b ∧ (∀y:real. a ≤ y ∧ y ≤ b ⇒ f(m) ≤ f(y))",
				By(ordered, cont, real_continuous.ExtremeValueMin.At(f, a, b)))
			M, maxSpec := arg.ObtainAs[Real](
				"f attains a maximum on the closed cell",
				"∃M:real. a ≤ M ∧ M ≤ b ∧ (∀y:real. a ≤ y ∧ y ≤ b ⇒ f(y) ≤ f(M))",
				By(ordered, cont, real_continuous.ExtremeValueMax.At(f, a, b)))
			minimum := arg.Conjuncts(
				minSpec,
				"the minimum point is at or above a",
				"the minimum point is at or below b",
				"f(m) is the minimum")
			maximum := arg.Conjuncts(
				maxSpec,
				"the maximum point is at or above a",
				"the maximum point is at or below b",
				"f(M) is the maximum")
			bounds := arg.Have(
				"the closed-cell extrema bound f on the half-open cell",
				"∀x:real. x ∈ ⟬a, b⟧ ⇒ f(m) ≤ f(x) ∧ f(x) ≤ f(M)",
				BySets(minimum[2], maximum[2], real_order_ring.LessEqOfLessThan))
			bracket := arg.Have(
				"the same extrema bound the cell integral after scaling by the width",
				"f(m) * (b - a) ≤ «event»(⟬a, b⟧, f) ∧ «event»(⟬a, b⟧, f) ≤ f(M) * (b - a)",
				By(ordered, integrable, bounds, At(cellBounds, f, a, b, f.Apply(m), f.Apply(M))))
			different := arg.Unless(
				arg.TermAs[Bool]("a = b"),
				"a zero-width cell has zero integral",
				Derive(func(d *Argument) {
					equal := d.Hyp("a = b")
					d.Take(a)
					d.Show(
						"the left endpoint is a tag",
						ByArith(equal, bracket))
				}))
			positive := arg.Have(
				"the width is positive",
				"&0 < b - a",
				ByArith(ordered, different))
			integral := arg.TermAs[Real]("«event»(⟬a, b⟧, f)")
			width := arg.TermAs[Real]("b - a")
			average := arg.TermAs[Real]("«average»")
			between := arg.Have(
				"the average lies between the extreme values",
				"f(m) ≤ «average» ∧ «average» ≤ f(M)",
				By(
					positive,
					bracket,
					real_order_field.LessEqDivMulLeft.At(f.Apply(m), integral, width),
					real_order_field.LessEqDivMulRight.At(integral, f.Apply(M), width)))
			inside := arg.Have(
				"both extrema occur in the closed cell",
				"m ∈ ⟦a, b⟧ ∧ M ∈ ⟦a, b⟧",
				BySets(minimum[0], minimum[1], maximum[0], maximum[1]))
			interval := arg.TermAs[Set[Real]]("⟦a, b⟧")
			values := arg.Have(
				"the values of f on the closed cell form an interval",
				"real_interval(image(f, ⟦a, b⟧))",
				By(ordered, cont, real_continuous.ValuesInterval.At(f, a, b)))
			extremes := arg.Have(
				"both extreme values are values of f on the closed cell",
				"f(m) ∈ image(f, ⟦a, b⟧) ∧ f(M) ∈ image(f, ⟦a, b⟧)",
				By(inside, set_image.FunInImage.At(f, interval, m), set_image.FunInImage.At(f, interval, M)))
			filled := arg.Unfolded(values, real_topology.RealIntervalDef)
			averageValue := arg.Have(
				"the average lies between two values of f, so it is a value",
				"«average» ∈ image(f, ⟦a, b⟧)",
				By(filled.At(f.Apply(m), average, f.Apply(M)), extremes, between))
			z, attained := arg.ObtainAs[Real](
				"f attains the average at a tag in the closed cell",
				"∃z:real. z ∈ ⟦a, b⟧ ∧ f(z) = «average»",
				By(set_basic.InImage.At(f, interval, average), averageValue))
			tag := arg.Conjuncts(
				attained,
				"the tag is in the cell",
				"its value is the average")
			arg.Take(z)
			arg.Show(
				"multiply the tag value by the width to recover the integral",
				By(tag[0], tag[1], positive, real_order_field.EqDivMulLeft.At(f.Apply(z), integral, width)))
		})

		singletonIntegral := ctx.Lemma("∀f:(real → real). ∀a:real. «event»(⟦a, a⟧, f) = &0",
			func(arg *Argument, f *Arrow[Real, Real], a *Expr[Real]) {
				line := arg.TermAs[Set[Real]]("𝕌")
				sets := arg.TermAs[Set[Set[Real]]]("«lebesgueSets»")
				mass := arg.TermAs[Fun[Set[Real], extended_nonneg_real.ExtendedNonnegReal]](
					"lebesgue_outer_measure")
				E := arg.TermAs[Set[Real]]("⟦a, a⟧")
				singleton := arg.Have(
					"the zero-width closed interval is a singleton",
					"⟦a, a⟧ = {a}",
					BySets(real_order_ring.LessEqSplit, real_order_ring.LessThanAsym, real_order_ring.LessEqRefl))
				constant := arg.Have(
					"on the singleton f has the constant value f(a)",
					"∀x:real. x ∈ 𝕌 ∧ x ∈ ⟦a, a⟧ ⇒ f(x) = f(a)",
					BySets(singleton))
				arg.Show(
					"the integral of that constant over a set of mass zero is zero",
					By(
						singleton,
						lebesgue_measure.MeasurableClosedInterval.At(a, a),
						constant,
						lebesgue_measure.LebesgueMeasureOn,
						lebesgue_measure.OuterMeasureSingleton.At(a),
						extended_nonneg_real.ToRealZero,
						real_ring.MulRightZero.At(f.Apply(a)),
						event_integral.EventIntegralConst.At(line, sets, mass, E, f.Apply(a)),
						event_integral.EventIntegralEqOn.At(
							line, sets, mass, E, f, arg.TermAs[Fun[Real, Real]]("λx:real. f(a)"))))
			})

		taggedSum := ctx.Lemma(Statement{
			Binders: "∀f:(real → real). ∀a b:real. ∀n:num. ∀p t:(num → real).",
			Hypotheses: []string{
				"real_integrable(𝕌, «lebesgueSets», lebesgue_outer_measure, f)",
				"«partition»(a, b, n, p)",
				"∀i:num. i ≤ n ⇒ «event»(«cell»(i), f) = f(t(i)) * «width»(i)",
			},
			Conclusion: "«riemannSum»(f, n, p, t) = «event»(⟦a, b⟧, f)",
			Abbrev: Abbrev{
				{Name: "prefix", Text: "λi:num. «event»(⟦a, p(i)⟧, f)"},
			},
		}, func(arg *Argument, f *Arrow[Real, Real], a, b *Expr[Real], n *Expr[Nat],
			p, t *Arrow[Nat, Real], integrable, partition, cellTags Fact) {
			partitionFacts := arg.Conjuncts(
				partition,
				"the left endpoint is a",
				"the right endpoint is b",
				"the partition points increase")
			items := arg.Have(
				"each tagged term is the change in the cumulative integral",
				"∀i:num. i ∈ 0 .. n ⇒ f(t(i)) * «width»(i) = «prefix»(i + 1) - «prefix»(i)",
				Derive(func(d *Argument) {
					i := d.FixAs[Nat]("i")
					index := d.Assume()
					within := d.Have(
						"i indexes a cell",
						"i ≤ n",
						By(index, num_segment.MembershipFromZero.At(i, n)))
					bounds := d.Have(
						"the cell endpoints are ordered inside the original interval",
						"a ≤ p(i) ∧ p(i) ≤ p(i + 1) ∧ p(i + 1) ≤ b",
						By(within, partition, real_integral.PartitionPiecesInInterval.At(a, b, n, p, i)))
					split := d.Have(
						"the next prefix is the disjoint union of the previous prefix and the cell",
						"⟦a, p(i + 1)⟧ = ⟦a, p(i)⟧ ∪ «cell»(i) ∧ ⟦a, p(i)⟧ ∩ «cell»(i) = ∅",
						Derive(func(e *Argument) {
							points := e.Have(
								"the two pieces separate at p(i)",
								"∀x:real. "+
									"    ((a ≤ x ∧ x ≤ p(i + 1)) ⇔ (a ≤ x ∧ x ≤ p(i)) ∨ (p(i) < x ∧ x ≤ p(i + 1))) ∧ "+
									"    ¬((a ≤ x ∧ x ≤ p(i)) ∧ (p(i) < x ∧ x ≤ p(i + 1)))",
								ByArith(bounds))
							e.Show(
								"apply the interval membership formulas",
								BySets(points))
						}))
					earlier := d.TermAs[Set[Real]]("⟦a, p(i)⟧")
					cell := d.TermAs[Set[Real]]("«cell»(i)")
					l := p.Apply(i)
					r := p.Apply(d.TermAs[Nat]("i + 1"))
					measurable := d.Have(
						"the prefix and the cell are measurable",
						"⟦a, p(i)⟧ ∈ «lebesgueSets» ∧ «cell»(i) ∈ «lebesgueSets»",
						BySets(bounds, lebesgue_measure.MeasurableClosedInterval.At(a, l), At(cellMass, l, r)))
					add := d.Have(
						"adjoining the cell adds its integral",
						"«prefix»(i + 1) = «prefix»(i) + «event»(«cell»(i), f)",
						By(
							split,
							measurable,
							integrable,
							lebesgue_measure.LebesgueMeasureOn,
							event_integral.EventIntegralUnion.At(
								d.TermAs[Set[Real]]("𝕌"),
								d.TermAs[Set[Set[Real]]]("«lebesgueSets»"),
								d.TermAs[Fun[Set[Real], extended_nonneg_real.ExtendedNonnegReal]]("lebesgue_outer_measure"),
								earlier,
								cell,
								f)))
					d.Show(
						"the tag represents that cell integral",
						ByArith(cellTags.At(i), within, add))
				}))
			difference := arg.Have(
				"the tagged sum telescopes to the difference of the endpoint integrals",
				"«riemannSum»(f, n, p, t) = «event»(⟦a, b⟧, f) - «event»(⟦a, a⟧, f)",
				By(
					items,
					partitionFacts[0],
					partitionFacts[1],
					real_sum.Congruence.At(arg.TermAs[Set[Nat]]("0 .. n"),
						arg.TermAs[Fun[Nat, Real]]("λi:num. f(t(i)) * «width»(i)"),
						arg.TermAs[Fun[Nat, Real]]("λi:num. «prefix»(i + 1) - «prefix»(i)")),
					real_sum.TelescopeUp.At(arg.TermAs[Nat]("0"), n, arg.TermAs[Fun[Nat, Real]]("«prefix»")),
					nat_order.ZeroLessEq.At(n)))
			arg.Show(
				"the initial singleton contributes zero",
				ByArith(difference, At(singletonIntegral, f, a)))
		})

		exactIntegral := ctx.Lemma(Statement{
			Binders: "∀f:(real → real). ∀a b I:real.",
			Hypotheses: []string{
				"a ≤ b",
				"real_integrable(𝕌, «lebesgueSets», lebesgue_outer_measure, f)",
				"real_continuous_on(⟦a, b⟧, f)",
				"real_has_integral(f, a, b, I)",
			},
			Conclusion: "«event»(⟦a, b⟧, f) = I",
			Abbrev: Abbrev{
				{Name: "finePartition", Text: "λa:real. " +
					"λb:real. " +
					"λδ:real. " +
					"λn:num. " +
					"λp:(num → real). " +
					"λt:(num → real). " +
					"    p(0) = a ∧ " +
					"    p(n + 1) = b ∧ " +
					"    (∀i:num. i ≤ n ⇒ p(i) ≤ t(i) ∧ t(i) ≤ p(i + 1) ∧ p(i + 1) - p(i) < δ)"},
			},
		}, func(
			arg *Argument,
			f *Arrow[Real, Real],
			a, b, I *Expr[Real],
			ordered, integrable, cont, riemann Fact,
		) {
			near := arg.Have(
				"the two integrals differ by less than every positive tolerance",
				"∀ε:real. &0 < ε ⇒ |«event»(⟦a, b⟧, f) - I| < ε",
				Derive(func(d *Argument) {
					d.FixAs[Real]("ε")
					tolerance := d.Assume()
					δ, mesh := d.ObtainAs[Real](
						"the tolerance determines a mesh bound for Riemann sums",
						"∃δ:real. "+
							"    &0 < δ ∧ "+
							"    (∀n:num. ∀p t:(num → real). "+
							"        «finePartition»(a, b, δ, n, p, t) ⇒ |«riemannSum»(f, n, p, t) - I| < ε)",
						By(tolerance, riemann, real_integral.RealHasIntegralDef.At(f, a, b, I)))
					control := d.Conjuncts(
						mesh,
						"the mesh bound is positive",
						"fine sums approximate the Riemann integral")
					n, p, q, fine := d.Obtain3As[Nat, Fun[Nat, Real], Fun[Nat, Real]](
						"there is a partition of that mesh",
						"∃n:num. ∃p q:(num → real). «finePartition»(a, b, δ, n, p, q)",
						By(ordered, control[0], real_integral.FinePartitionExists.At(a, b, δ)))
					partition := d.Have(
						"the partition points increase and span the interval",
						"«partition»(a, b, n, p)",
						By(fine, real_integral.FinePartitionIsPartition.At(a, b, δ, n, p, q)))
					tagExists := d.Have(
						"each cell has a tag that represents its Lebesgue integral",
						"∀i:num. i ≤ n ⇒ ∃z:real. p(i) ≤ z ∧ z ≤ p(i + 1) ∧ «event»(«cell»(i), f) = f(z) * «width»(i)",
						Derive(func(e *Argument) {
							i := e.FixAs[Nat]("i")
							index := e.Assume()
							endpoints := e.Have(
								"the cell endpoints are ordered in the interval",
								"a ≤ p(i) ∧ p(i) ≤ p(i + 1) ∧ p(i + 1) ≤ b",
								By(index, partition, real_integral.PartitionPiecesInInterval.At(a, b, n, p, i)))
							subset := e.Have(
								"the closed cell is inside the original interval",
								"⟦p(i), p(i + 1)⟧ ⊆ ⟦a, b⟧",
								BySets(
									endpoints,
									real_order_ring.LessEqSplit,
									real_order_ring.LessThanTrans,
									real_order_ring.LessEqOfLessThan))
							cellCont := e.Have(
								"f is continuous on the closed cell",
								"real_continuous_on(⟦p(i), p(i + 1)⟧, f)",
								By(
									cont,
									subset,
									real_continuous.ContinuousOnSubset.At(f,
										e.TermAs[Set[Real]]("⟦a, b⟧"), e.TermAs[Set[Real]]("⟦p(i), p(i + 1)⟧"))))
							e.Show(
								"use the integral mean-value tag for this cell",
								By(
									endpoints,
									cellCont,
									integrable,
									At(meanTag, f, e.TermAs[Real]("p(i)"), e.TermAs[Real]("p(i + 1)"))))
						}))
					t, tags := d.ObtainAs[Fun[Nat, Real]](
						"choose those tags for the partition",
						"∃t:(num → real). ∀i:num. "+
							"    i ≤ n ⇒ p(i) ≤ t(i) ∧ t(i) ≤ p(i + 1) ∧ «event»(«cell»(i), f) = f(t(i)) * «width»(i)",
						By(tagExists))
					retagged := d.Have(
						"the new tags still lie within the cells and the mesh is unchanged",
						"«finePartition»(a, b, δ, n, p, t)",
						By(fine, tags))
					exact := d.Have(
						"the new tagged sum equals the interval integral",
						"«riemannSum»(f, n, p, t) = «event»(⟦a, b⟧, f)",
						By(integrable, partition, tags, At(taggedSum, f, a, b, n, p, t)))
					d.Show(
						"this exact sum is within the prescribed tolerance",
						By(exact, retagged, control[1].At(n, p, t)))
				}))
			difference := arg.TermAs[Real]("«event»(⟦a, b⟧, f) - I")
			arg.Show(
				"a nonnegative difference smaller than itself when positive must be zero",
				ByArith(
					near.At(arg.TermAs[Real]("|«event»(⟦a, b⟧, f) - I|")),
					real_sgn_abs.AbsNonneg.At(difference),
					real_sgn_abs.AbsVanishes.At(difference)))
		})

		return ctx.Theorem(headline, func(
			arg *Argument,
			f *Arrow[Real, Real],
			a, b *Expr[Real],
			ordered, cont, zero Fact,
		) {
			line := arg.TermAs[Set[Real]]("𝕌")
			sets := arg.TermAs[Set[Set[Real]]]("«lebesgueSets»")
			mass := arg.TermAs[Fun[Set[Real], extended_nonneg_real.ExtendedNonnegReal]](
				"lebesgue_outer_measure")
			interval := arg.TermAs[Set[Real]]("⟦a, b⟧")
			measurable := arg.Have(
				"the continuous function extended by zero is Lebesgue measurable",
				"lebesgue_measurable_function(f)",
				By(cont, zero, At(measurableExtension, f, a, b)))
			I, riemann := arg.ObtainAs[Real](
				"continuity gives a Riemann integral on the interval",
				"∃I:real. real_has_integral(f, a, b, I)",
				By(ordered, cont, real_integral.ContinuousIntegrable.At(f, a, b)))
			B, bounded := arg.ObtainAs[Real](
				"f is bounded on the interval",
				"∃B:real. ∀x:real. a ≤ x ∧ x ≤ b ⇒ |f(x)| ≤ B",
				By(riemann, real_integral.IntegrableBounded.At(f, a, b, I)))
			indicator := arg.TermAs[Fun[Real, Real]]("«indicator»(⟦a, b⟧, B)")
			finiteBound := arg.Have(
				"the bounding indicator is integrable because the interval has finite length",
				"real_integrable(𝕌, «lebesgueSets», lebesgue_outer_measure, «indicator»(⟦a, b⟧, B))",
				By(
					ordered,
					lebesgue_measure.MeasurableClosedInterval.At(a, b),
					lebesgue_measure.OuterMeasureClosedInterval.At(a, b),
					extended_nonneg_real.OfRealNotInfinity.At(arg.TermAs[Real]("b - a")),
					At(integrableIndicator, interval, B)))
			dominated := arg.Have(
				"the bounding indicator dominates |f| on the whole line",
				"∀x:real. x ∈ 𝕌 ⇒ |f(x)| ≤ «indicator»(⟦a, b⟧, B, x)",
				BySets(zero, bounded, real_sgn_abs.AbsOfZero, real_order_ring.LessEqRefl))
			integrable := arg.Have(
				"f is integrable for Lebesgue measure",
				"real_integrable(𝕌, «lebesgueSets», lebesgue_outer_measure, f)",
				By(
					measurable,
					finiteBound,
					dominated,
					lebesgue_integral.MeasurableFunctionIffRealMeasurable.At(f),
					measure_integral.IntegrableDominated.At(line, sets, mass, f, indicator)))
			exact := arg.Have(
				"the interval integral agrees with the Riemann value",
				"«event»(⟦a, b⟧, f) = I",
				By(ordered, integrable, cont, riemann, At(exactIntegral, f, a, b, I)))
			sameCut := arg.Have(
				"cutting f to its support leaves it equal to f",
				"«cut»(⟦a, b⟧, f) = f",
				Funext(),
				BySets(zero))
			whole := arg.Have(
				"the interval integral is therefore the integral on the whole line",
				"«event»(⟦a, b⟧, f) = measure_integral(𝕌, «lebesgueSets», lebesgue_outer_measure, f)",
				By(sameCut, event_integral.EventIntegralDef.At(line, sets, mass, interval, f)))
			arg.Show(
				"the Lebesgue integral equals the Riemann integral",
				SplitConj(
					Case(
						"f is Lebesgue integrable",
						By(integrable, lebesgue_integral.LebesgueIntegrableIff.At(f))),
					Case(
						"both integrals have the common value I",
						By(
							exact,
							whole,
							riemann,
							lebesgue_integral.LebesgueIntegralEq.At(f),
							real_integral.HasIntegralValue.At(f, a, b, I)))))
		})
	}),
})}
