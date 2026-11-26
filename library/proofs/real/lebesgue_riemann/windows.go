package lebesgue_riemann

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/measure/measurable_function"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_integral"
	"github.com/euc-ai/xugo/library/proofs/measure/nonneg_integral"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/real/lebesgue_integral"
	"github.com/euc-ai/xugo/library/proofs/real/lebesgue_measure"
	"github.com/euc-ai/xugo/library/proofs/real/real_archimedean"
	"github.com/euc-ai/xugo/library/proofs/real/real_continuous"
	"github.com/euc-ai/xugo/library/proofs/real/real_integral"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_topology"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// LebesgueNonnegIntegralOnInterval — an embedded nonnegative continuous
// function cut to a closed interval integrates to its embedded Riemann
// value.
var LebesgueNonnegIntegralOnInterval = lebesgueNonnegIntegralOnIntervalThm{family.Add(registry.ProofEntry{
	Name: "LebesgueNonnegIntegralOnInterval",
	Key:  "prop_f1564aeec1db2728",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀l u:real.",
		Hypotheses: []string{
			"l ≤ u",
			"real_continuous_on(⟦l, u⟧, f)",
			"∀x:real. x ∈ ⟦l, u⟧ ⇒ &0 ≤ f(x)",
		},
		Conclusion: "extended_measurable(𝕌, «lebesgueSets», «embeddedCut») ∧ " +
			"nonneg_integral(𝕌, «lebesgueSets», lebesgue_outer_measure, «embeddedCut») = " +
			"extended_of_real(real_integral(f, l, u))",
		Abbrev: Abbrev{
			{Name: "embeddedCut", Text: "λx:real. extended_of_real(«cut»(⟦l, u⟧, f, x))"},
		},
	}, func(a *Argument, f *Arrow[Real, Real], l, u *Expr[Real], ordered, cont, nonneg Fact) {
		line := a.TermAs[Set[Real]]("𝕌")
		sets := a.TermAs[Set[Set[Real]]]("«lebesgueSets»")
		mass := a.TermAs[Fun[Set[Real], extended_nonneg_real.ExtendedNonnegReal]]("lebesgue_outer_measure")
		s := a.TermAs[Set[Real]]("⟦l, u⟧")
		cut := a.TermAs[Fun[Real, Real]]("«cut»(⟦l, u⟧, f)")
		continuous := a.Have(
			"continuity within the interval is unchanged by the cut",
			"real_continuous_on(⟦l, u⟧, «cut»(⟦l, u⟧, f))",
			Simp(Fwd(real_continuous.RealContinuousOnDef)),
			Derive(func(b *Argument) {
				b.FixAs[Real]("c")
				center := b.Assume()
				b.FixAs[Real]("ε")
				tolerance := b.Assume()
				δ, radius := b.ObtainAs[Real](
					"choose the radius for f at the center within the interval",
					"∃δ:real. &0 < δ ∧ ∀x:real. x ∈ ⟦l, u⟧ ∧ |x - c| < δ ⇒ |f(x) - f(c)| < ε",
					By(tolerance, center, cont, real_continuous.RealContinuousOnDef.At(s, f)))
				b.Take(δ)
				b.Show(
					"the radius for f serves for the cut",
					SplitConj(
						Case(
							"the radius is positive",
							By(radius)),
						Case(
							"both values of the cut are the values of f on the interval",
							Derive(func(d *Argument) {
								d.FixAs[Real]("x")
								inside := d.Assume()
								d.Show(
									"the radius controls the cut",
									By(center, radius, inside))
							}))))
			}))
		outside := a.Have(
			"the cut vanishes outside the interval",
			"∀x:real. x ∉ ⟦l, u⟧ ⇒ «cut»(⟦l, u⟧, f, x) = &0",
			Derive(func(b *Argument) {
				b.FixAs[Real]("x")
				offInterval := b.Assume()
				b.Show(
					"the cut takes its zero branch there",
					ByArith(offInterval))
			}))
		nonnegative := a.Have(
			"the cut is either a nonnegative value of f or zero",
			"∀x:real. &0 ≤ «cut»(⟦l, u⟧, f, x)",
			Derive(func(b *Argument) {
				b.FixAs[Real]("x")
				b.Cases(b.TermAs[Bool]("x ∈ ⟦l, u⟧"))
				b.When(
					"inside the interval the cut is the value of f",
					func(d *Argument, inside Fact) {
						d.Show(
							"which is nonnegative there",
							ByArith(nonneg, inside))
					})
				b.Otherwise(
					"outside the interval the cut is zero",
					func(d *Argument, offInterval Fact) {
						d.Show(
							"and zero is nonnegative",
							ByArith(offInterval))
					})
			}))
		integral := a.Have(
			"the interval theorem identifies the real integral of the cut",
			"real_integrable(𝕌, «lebesgueSets», lebesgue_outer_measure, «cut»(⟦l, u⟧, f)) ∧ "+
				"measure_integral(𝕌, «lebesgueSets», lebesgue_outer_measure, «cut»(⟦l, u⟧, f)) = "+
				"real_integral(«cut»(⟦l, u⟧, f), l, u)",
			By(
				outside,
				continuous,
				ordered,
				LebesgueIntegralInterval.At(cut, l, u),
				lebesgue_integral.LebesgueIntegrableIff.At(cut),
				lebesgue_integral.LebesgueIntegralEq.At(cut)))
		agreement := a.Have(
			"the cut has the same Riemann integral as f on the interval",
			"real_integral(«cut»(⟦l, u⟧, f), l, u) = real_integral(f, l, u)",
			Derive(func(b *Argument) {
				values := b.Have(
					"the cut and f agree between the ordered endpoints",
					"∀x:real. min(l, u) ≤ x ∧ x ≤ max(l, u) ⇒ «cut»(⟦l, u⟧, f, x) = f(x)",
					Derive(func(d *Argument) {
						d.FixAs[Real]("x")
						between := d.Assume()
						d.Show(
							"the cut retains f inside the interval",
							ByArith(between, ordered))
					}))
				b.Show(
					"pointwise agreement gives equal Riemann integrals",
					By(values, real_integral.IntegralCongruence.At(cut, f, l, u)))
			}))
		a.Show(
			"the embedded cut is measurable and its integral is the embedded Riemann value",
			By(
				nonnegative,
				agreement,
				integral,
				lebesgue_measure.LebesgueSigmaAlgebra,
				measure_integral.RealIntegrableDef.At(line, sets, mass, cut),
				measurable_function.ExtendedMeasurableOfReal.At(line, sets, cut),
				measure_integral.IntegralNonnegEmbedding.At(line, sets, mass, cut)))
	}),
})}

// LebesgueNonnegIntegralByWindows — increasing closed intervals covering the
// line give the nonnegative integral as the supremum of their Riemann integrals.
var LebesgueNonnegIntegralByWindows = lebesgueNonnegIntegralByWindowsThm{family.Add(registry.ProofEntry{
	Name: "LebesgueNonnegIntegralByWindows",
	Key:  "prop_14a0b941edab1b45",
	Build: family.Sections(Statement{
		Binders: "∀f:(real → real). ∀l u:(num → real).",
		Hypotheses: []string{
			"∀x:real. &0 ≤ f(x)",
			"∀n:num. l(n) ≤ u(n) ∧ real_continuous_on(⟦l(n), u(n)⟧, f)",
			"∀n:num. l(n + 1) ≤ l(n) ∧ u(n) ≤ u(n + 1)",
			"∀x:real. ∃n:num. x ∈ ⟦l(n), u(n)⟧",
		},
		Conclusion: "nonneg_integral(𝕌, " +
			"    «lebesgueSets», " +
			"    lebesgue_outer_measure, " +
			"    λx:real. extended_of_real(f(x))) = " +
			"extended_sup(image(λn:num. extended_of_real(real_integral(f, l(n), u(n))), 𝕌))",
	}, func(ctx *Script, headline string) *GoalStackNode {
		return ctx.Theorem(headline, func(
			a *Argument,
			f *Arrow[Real, Real],
			l, u *Arrow[Nat, Real],
			nonneg, windows, nested, covering Fact,
		) {
			line := a.TermAs[Set[Real]]("𝕌")
			sets := a.TermAs[Set[Set[Real]]]("«lebesgueSets»")
			mass := a.TermAs[Fun[Set[Real], extended_nonneg_real.ExtendedNonnegReal]]("lebesgue_outer_measure")
			F, cutsDefined := a.LetAs[Fun2[Nat, Real, extended_nonneg_real.ExtendedNonnegReal]](
				"F", "λn:num. λx:real. extended_of_real(«cut»(⟦l(n), u(n)⟧, f, x))")
			values := a.Have(
				"each embedded cut is measurable and integrates to the embedded Riemann value",
				"∀n:num. "+
					"    extended_measurable(𝕌, «lebesgueSets», F(n)) ∧ "+
					"    nonneg_integral(𝕌, «lebesgueSets», lebesgue_outer_measure, F(n)) = "+
					"    extended_of_real(real_integral(f, l(n), u(n)))",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					b.Show(
						"apply the interval integral to this term",
						By(cutsDefined, nonneg, windows, At(LebesgueNonnegIntegralOnInterval, f, l.Apply(n), u.Apply(n))))
				}))
			rise := a.Have(
				"the cuts increase as the intervals increase",
				"∀n:num. ∀x:real. x ∈ 𝕌 ⇒ F(n, x) ≤ F(n + 1, x)",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("n")
					b.FixAs[Real]("x")
					b.Assume()
					oldCut := b.TermAs[Real]("«cut»(⟦l(n), u(n)⟧, f, x)")
					newCut := b.TermAs[Real]("«cut»(⟦l(n + 1), u(n + 1)⟧, f, x)")
					order := b.Have(
						"a point retained by the earlier interval is retained by the later one",
						"«cut»(⟦l(n), u(n)⟧, f, x) ≤ «cut»(⟦l(n + 1), u(n + 1)⟧, f, x)",
						ByArith(nonneg, nested))
					b.Show(
						"embedding preserves the order",
						By(Normalized, cutsDefined, order, extended_nonneg_real.OfRealMono.At(oldCut, newCut)))
				}))
			pointwise := a.Have(
				"the cuts at a point reach the embedded value there",
				"∀x:real. extended_sup(image(λn:num. F(n, x), 𝕌)) = extended_of_real(f(x))",
				Derive(func(b *Argument) {
					x := b.FixAs[Real]("x")
					bound := b.Have(
						"every cut is at most the embedded value",
						"∀n:num. F(n, x) ≤ extended_of_real(f(x))",
						Derive(func(d *Argument) {
							d.FixAs[Nat]("n")
							order := d.Have(
								"the real cut is at most f",
								"«cut»(⟦l(n), u(n)⟧, f, x) ≤ f(x)",
								ByArith(nonneg))
							d.Show(
								"embedding preserves the bound",
								By(
									Normalized,
									cutsDefined,
									order,
									extended_nonneg_real.OfRealMono.At(
										d.TermAs[Real]("«cut»(⟦l(n), u(n)⟧, f, x)"), f.Apply(x))))
						}))
					j, inside := b.ObtainAs[Nat](
						"some interval contains this point",
						"∃j:num. x ∈ ⟦l(j), u(j)⟧",
						By(covering))
					reached := b.Have(
						"that cut retains the value at the point",
						"F(j, x) = extended_of_real(f(x))",
						By(cutsDefined, inside))
					seq := b.TermAs[Fun[Nat, extended_nonneg_real.ExtendedNonnegReal]]("λn:num. F(n, x)")
					value := b.TermAs[extended_nonneg_real.ExtendedNonnegReal]("extended_of_real(f(x))")
					b.Show(
						"the supremum is the attained upper bound",
						By(
							bound,
							reached,
							extended_nonneg_real.SupSequenceUpper.At(seq, j),
							extended_nonneg_real.SupSequenceLeast.At(seq, value),
							extended_nonneg_real.LeAntisym.At(
								b.TermAs[extended_nonneg_real.ExtendedNonnegReal](
									"extended_sup(image(λn:num. F(n, x), 𝕌))"), value)))
				}))
			convergence := a.Have(
				"monotone convergence passes the pointwise supremum through integration",
				"nonneg_integral(𝕌, "+
					"    «lebesgueSets», "+
					"    lebesgue_outer_measure, "+
					"    λx:real. extended_sup(image(λn:num. F(n, x), 𝕌))) = "+
					"extended_sup(image(λn:num. nonneg_integral(𝕌, «lebesgueSets», lebesgue_outer_measure, F(n)), 𝕌))",
				By(
					rise,
					values,
					lebesgue_measure.LebesgueMeasureOn,
					nonneg_integral.MonotoneConvergence.At(line, sets, mass, F)))
			limit := a.Have(
				"the pointwise limit is the embedded function",
				"(λx:real. extended_sup(image(λn:num. F(n, x), 𝕌))) = (λx:real. extended_of_real(f(x)))",
				Funext(),
				By(pointwise))
			sequence := a.Have(
				"the two sequences of integral values agree term by term",
				"(λn:num. nonneg_integral(𝕌, «lebesgueSets», lebesgue_outer_measure, F(n))) = "+
					"(λn:num. extended_of_real(real_integral(f, l(n), u(n))))",
				Funext(),
				By(values))
			a.Show(
				"substitute the limit and interval values into monotone convergence",
				By(convergence, sequence, limit))
		})
	}),
})}

// LebesgueNonnegIntegralBySymmetricWindows — for a nonnegative f continuous on
// the line and a step w > 0, the nonnegative integral of f over the line is
// the supremum of its Riemann integrals over the windows ⟦m − w·n, m + w·n⟧
// about any centre m. Each window is ordered and f is continuous on it, the
// windows grow with n, and a point within some whole number of steps of m
// lies in one of them (Archimedean), so LebesgueNonnegIntegralByWindows applies.
var LebesgueNonnegIntegralBySymmetricWindows = lebesgueNonnegIntegralBySymmetricWindowsThm{family.Add(registry.ProofEntry{
	Name: "LebesgueNonnegIntegralBySymmetricWindows",
	Key:  "prop_76b71ca2b0d47e49",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀m w:real.",
		Hypotheses: []string{
			"&0 < w",
			"∀x:real. &0 ≤ f(x)",
			"real_continuous_on(𝕌, f)",
		},
		Conclusion: "nonneg_integral(𝕌, " +
			"    «lebesgueSets», " +
			"    lebesgue_outer_measure, " +
			"    λx:real. extended_of_real(f(x))) = " +
			"extended_sup(image(λn:num. extended_of_real(real_integral(f, m - w * &n, m + w * &n)), 𝕌))",
	}, func(a *Argument, f *Arrow[Real, Real], m, w *Expr[Real], positive, nonneg, continuous Fact) {
		line := a.TermAs[Set[Real]]("𝕌")
		lower := a.TermAs[Fun[Nat, Real]]("λn:num. m - w * &n")
		upper := a.TermAs[Fun[Nat, Real]]("λn:num. m + w * &n")
		ordered := a.Have(
			"each window is ordered, and f is continuous on it",
			"∀n:num. m - w * &n ≤ m + w * &n ∧ real_continuous_on(⟦m - w * &n, m + w * &n⟧, f)",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				window := b.TermAs[Set[Real]]("⟦m - w * &n, m + w * &n⟧")
				order := b.Have(
					"the radius w·n is nonnegative",
					"m - w * &n ≤ m + w * &n",
					ByArith(positive, real_order_ring.NumNonneg.At(n)))
				b.Show(
					"f is continuous on the line, hence on the window",
					By(
						order,
						continuous,
						set_order.SubsetUniv.At(window),
						real_continuous.ContinuousOnSubset.At(f, line, window)))
			}))
		growing := a.Have(
			"the radius grows with n",
			"∀n:num. m - w * &(n + 1) ≤ m - w * &n ∧ m + w * &n ≤ m + w * &(n + 1)",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				b.Show(
					"the next radius adds the positive step w",
					ByArith(positive, real_construction.OfNumAdd.At(n, b.TermAs[Nat]("1"))))
			}))
		covers := a.Have(
			"the windows cover the line",
			"∀x:real. ∃n:num. x ∈ ⟦m - w * &n, m + w * &n⟧",
			Derive(func(b *Argument) {
				x := b.FixAs[Real]("x")
				n, radius := b.ObtainAs[Nat](
					"some whole number of steps w passes the distance from x to m",
					"∃j:num. |x - m| < &j * w",
					By(positive, real_archimedean.Archimedean.At(w, b.TermAs[Real]("|x - m|"))))
				b.Take(n)
				b.Show(
					"so x lies between the endpoints",
					ByArith(
						radius,
						real_topology.ClosedIntervalMembership.At(
							x, b.TermAs[Real]("m - w * &j"), b.TermAs[Real]("m + w * &j"))))
			}))
		a.Show(
			"the windows are increasing closed intervals covering the line",
			By(nonneg, ordered, growing, covers, LebesgueNonnegIntegralByWindows.At(f, lower, upper)))
	}),
})}

// LebesgueIntegralByWindows — a nonnegative f continuous on the line whose Riemann
// integrals over increasing closed windows covering the line converge to L
// is integrable for the Lebesgue measure, with integral L. Its nonnegative
// integral is the supremum of the window values (LebesgueNonnegIntegralByWindows);
// those are nonnegative and increase, a larger window adding two nonnegative
// end pieces, so their supremum is their limit L (SupSequenceOfReal). Being
// measurable (ContinuousLebesgueMeasurable) with that finite nonnegative
// integral, f is integrable, and its integral is the real L.
var LebesgueIntegralByWindows = lebesgueIntegralByWindowsThm{family.Add(registry.ProofEntry{
	Name: "LebesgueIntegralByWindows",
	Key:  "prop_9efebdadf9046448",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀l u:(num → real). ∀L:real.",
		Hypotheses: []string{
			"∀x:real. &0 ≤ f(x)",
			"real_continuous_on(𝕌, f)",
			"∀n:num. l(n) ≤ u(n)",
			"∀n:num. l(n + 1) ≤ l(n) ∧ u(n) ≤ u(n + 1)",
			"∀x:real. ∃n:num. x ∈ ⟦l(n), u(n)⟧",
			"(λn:num. real_integral(f, l(n), u(n))) ⟶ L",
		},
		Conclusion: "real_integrable(𝕌, «lebesgueSets», lebesgue_outer_measure, f) ∧ " +
			"measure_integral(𝕌, «lebesgueSets», lebesgue_outer_measure, f) = L",
	}, func(
		a *Argument,
		f *Arrow[Real, Real],
		l, u *Arrow[Nat, Real],
		L *Expr[Real],
		nonneg, continuous, ordered, nested, covering, limit Fact,
	) {
		line := a.TermAs[Set[Real]]("𝕌")
		sets := a.TermAs[Set[Set[Real]]]("«lebesgueSets»")
		mass := a.TermAs[Fun[Set[Real], extended_nonneg_real.ExtendedNonnegReal]]("lebesgue_outer_measure")
		values := a.TermAs[Fun[Nat, Real]]("λn:num. real_integral(f, l(n), u(n))")
		onWindows := a.Have(
			"each window is ordered, and f is continuous on it",
			"∀n:num. l(n) ≤ u(n) ∧ real_continuous_on(⟦l(n), u(n)⟧, f)",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				window := b.TermAs[Set[Real]]("⟦l(n), u(n)⟧")
				b.Show(
					"f is continuous on the line, hence on the window",
					By(
						ordered.At(n),
						continuous,
						set_order.SubsetUniv.At(window),
						real_continuous.ContinuousOnSubset.At(f, line, window)))
			}))
		sup := a.Have(
			"the nonnegative integral of f is the supremum of its window values",
			"nonneg_integral(𝕌, «lebesgueSets», lebesgue_outer_measure, λx:real. extended_of_real(f(x))) = "+
				"extended_sup(image(λn:num. extended_of_real(real_integral(f, l(n), u(n))), 𝕌))",
			By(nonneg, onWindows, nested, covering, LebesgueNonnegIntegralByWindows.At(f, l, u)))
		piece := a.Have(
			"over an ordered interval f has a nonnegative integral",
			"∀p q:real. p ≤ q ⇒ &0 ≤ real_integral(f, p, q)",
			Derive(func(b *Argument) {
				p := b.FixAs[Real]("p")
				q := b.FixAs[Real]("q")
				order := b.Assume()
				interval := b.TermAs[Set[Real]]("⟦p, q⟧")
				onInterval := b.Have(
					"f is continuous on the interval",
					"real_continuous_on(⟦p, q⟧, f)",
					By(
						continuous,
						set_order.SubsetUniv.At(interval),
						real_continuous.ContinuousOnSubset.At(f, line, interval)))
				b.Show(
					"it has its integral there, and a nonnegative function a nonnegative one",
					By(
						order,
						onInterval,
						nonneg,
						real_integral.ContinuousHasIntegral.At(f, p, q),
						real_integral.RiemannIntegralNonneg.At(f, p, q, b.TermAs[Real]("real_integral(f, p, q)"))))
			}))
		monotone := a.Have(
			"the window values are nonnegative and increasing",
			"(∀n:num. &0 ≤ real_integral(f, l(n), u(n))) ∧ "+
				"(∀n:num. real_integral(f, l(n), u(n)) ≤ real_integral(f, l(n + 1), u(n + 1)))",
			SplitConj(
				Case(
					"each window is ordered",
					Derive(func(b *Argument) {
						n := b.FixAs[Nat]("n")
						b.Show(
							"so its value is nonnegative",
							By(ordered.At(n), piece.At(l.Apply(n), u.Apply(n))))
					})),
				Case(
					"the next window adds two nonnegative end pieces",
					Derive(func(b *Argument) {
						n := b.FixAs[Nat]("n")
						next := b.TermAs[Nat]("n + 1")
						bigger := b.TermAs[Set[Real]]("⟦l(n + 1), u(n + 1)⟧")
						onBigger := b.Have(
							"f is continuous on the larger window",
							"real_continuous_on(⟦l(n + 1), u(n + 1)⟧, f)",
							By(
								continuous,
								set_order.SubsetUniv.At(bigger),
								real_continuous.ContinuousOnSubset.At(f, line, bigger)))
						order := b.Have(
							"the windows nest",
							"l(n + 1) ≤ l(n) ∧ l(n) ≤ u(n) ∧ u(n) ≤ u(n + 1)",
							By(ordered.At(n), nested.At(n)))
						b.Show(
							"the larger window splits at l(n) and u(n), and its end pieces are nonnegative",
							ByArith(
								order,
								piece.At(l.Apply(next), l.Apply(n)),
								piece.At(u.Apply(n), u.Apply(next)),
								real_integral.IntegralAdditive.At(
									f, l.Apply(next), u.Apply(next), l.Apply(next), l.Apply(n), u.Apply(n)),
								real_integral.IntegralAdditive.At(
									f, l.Apply(next), u.Apply(next), l.Apply(next), u.Apply(n), u.Apply(next)),
								onBigger))
					}))))
		limitNonneg := a.Have(
			"the limit of nonnegative values is nonnegative",
			"&0 ≤ L",
			By(limit, monotone, real_sequences.BoundLessEqLimit.At(values, L, a.TermAs[Real]("&0"))))
		embedded := a.Have(
			"so the supremum of the increasing values is their limit, and the nonnegative integral is L",
			"nonneg_integral(𝕌, «lebesgueSets», lebesgue_outer_measure, λx:real. extended_of_real(f(x))) = "+
				"extended_of_real(L)",
			By(sup, monotone, limitNonneg, limit, extended_nonneg_real.SupSequenceOfReal.At(values, L)))
		size := a.Have(
			"f is its own size",
			"(λx:real. extended_of_real(|f(x)|)) = (λx:real. extended_of_real(f(x)))",
			Funext(),
			Derive(func(b *Argument) {
				x := b.FixAs[Real]("x")
				b.Show(
					"f(x) is nonnegative",
					By(Normalized, nonneg.At(x), real_sgn_abs.AbsFixedIffNonneg.At(f.Apply(x))))
			}))
		integrable := a.Have(
			"measurable with a finite nonnegative integral, f is integrable",
			"real_integrable(𝕌, «lebesgueSets», lebesgue_outer_measure, f)",
			By(
				size,
				embedded,
				continuous,
				extended_nonneg_real.OfRealNotInfinity.At(L),
				lebesgue_integral.ContinuousLebesgueMeasurable.At(f),
				measure_integral.RealIntegrableDef.At(line, sets, mass, f)))
		a.Show(
			"and its integral is the real value L of its nonnegative integral",
			By(
				integrable,
				nonneg,
				embedded,
				limitNonneg,
				measure_integral.IntegralOfNonneg.At(line, sets, mass, f),
				extended_nonneg_real.ToRealOfReal.At(L)))
	}),
})}

// LebesgueIntegralByCenteredWindows — a nonnegative f continuous on the line whose
// integrals over ⟦−n, n⟧ converge to L is integrable for the Lebesgue
// measure, with integral L: the windows ⟦−n, n⟧ are ordered, grow with n
// and cover the line (ExistsNumBounds), so LebesgueIntegralByWindows applies.
var LebesgueIntegralByCenteredWindows = lebesgueIntegralByCenteredWindowsThm{family.Add(registry.ProofEntry{
	Name: "LebesgueIntegralByCenteredWindows",
	Key:  "prop_9dfe7623379116cd",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀L:real.",
		Hypotheses: []string{
			"∀x:real. &0 ≤ f(x)",
			"real_continuous_on(𝕌, f)",
			"(λn:num. real_integral(f, -&n, &n)) ⟶ L",
		},
		Conclusion: "real_integrable(𝕌, «lebesgueSets», lebesgue_outer_measure, f) ∧ " +
			"measure_integral(𝕌, «lebesgueSets», lebesgue_outer_measure, f) = L",
	}, func(a *Argument, f *Arrow[Real, Real], L *Expr[Real], nonneg, continuous, limit Fact) {
		ordered := a.Have(
			"each window ⟦−n, n⟧ is ordered",
			"∀n:num. -&n ≤ &n",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				b.Show(
					"n is nonnegative",
					ByArith(real_order_ring.NumNonneg.At(n)))
			}))
		nested := a.Have(
			"the windows grow with n",
			"∀n:num. -&(n + 1) ≤ -&n ∧ &n ≤ &(n + 1)",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				b.Show(
					"n + 1 exceeds n",
					ByArith(real_construction.OfNumAdd.At(n, b.TermAs[Nat]("1"))))
			}))
		covers := a.Have(
			"every real lies in some window",
			"∀x:real. ∃n:num. x ∈ ⟦-&n, &n⟧",
			By(real_archimedean.ExistsNumBounds, real_topology.ClosedIntervalMembership))
		a.Show(
			"so the window integrals give the integral over the line",
			By(
				nonneg,
				continuous,
				ordered,
				nested,
				covers,
				limit,
				LebesgueIntegralByWindows.At(
					f, a.TermAs[Fun[Nat, Real]]("λn:num. -&n"), a.TermAs[Fun[Nat, Real]]("λn:num. &n"), L)))
	}),
})}

// LebesgueNonnegIntegralAffineChange — the change of variables x = p + q·y,
// q > 0, in the nonnegative integral of a nonnegative f continuous on the
// line: q·f(p + q·y) has the nonnegative integral of f. Each is the supremum
// over symmetric windows (LebesgueNonnegIntegralBySymmetricWindows), the
// windows ⟦−n, n⟧ for q·f(p + q·y) and ⟦p − q·n, p + q·n⟧ for f, and the
// affine change on each window (RiemannIntegralAffineChange) gives the two
// the same value.
var LebesgueNonnegIntegralAffineChange = lebesgueNonnegIntegralAffineChangeThm{family.Add(registry.ProofEntry{
	Name: "LebesgueNonnegIntegralAffineChange",
	Key:  "prop_4df47a5a57d4a396",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀p q:real.",
		Hypotheses: []string{
			"&0 < q",
			"∀x:real. &0 ≤ f(x)",
			"real_continuous_on(𝕌, f)",
		},
		Conclusion: "nonneg_integral(𝕌, " +
			"    «lebesgueSets», " +
			"    lebesgue_outer_measure, " +
			"    λy:real. extended_of_real(q * f(p + q * y))) = " +
			"nonneg_integral(𝕌, «lebesgueSets», lebesgue_outer_measure, λx:real. extended_of_real(f(x)))",
	}, func(a *Argument, f *Arrow[Real, Real], p, q *Expr[Real], positive, nonneg, continuous Fact) {
		line := a.TermAs[Set[Real]]("𝕌")
		affine := a.TermAs[Fun[Real, Real]]("λy:real. p + q * y")
		changed := a.TermAs[Fun[Real, Real]]("λy:real. q * f(p + q * y)")
		affineContinuous := a.Have(
			"the affine map is continuous on the line",
			"real_continuous_on(𝕌, λy:real. p + q * y)",
			By(
				real_continuous.ContinuousOnId.At(line),
				real_continuous.ContinuousOnConst.At(p, line),
				real_continuous.ContinuousOnConst.At(q, line),
				real_continuous.ContinuousOnMul.At(
					a.TermAs[Fun[Real, Real]]("λy:real. q"), a.TermAs[Fun[Real, Real]]("λy:real. y"), line),
				real_continuous.ContinuousOnAdd.At(
					a.TermAs[Fun[Real, Real]]("λy:real. p"), a.TermAs[Fun[Real, Real]]("λy:real. q * y"), line)))
		changedContinuous := a.Have(
			"so q·f(p + q·y) is continuous on the line",
			"real_continuous_on(𝕌, λy:real. q * f(p + q * y))",
			By(
				affineContinuous,
				continuous,
				set_basic.InUniv.Inst[Real](),
				real_continuous.ContinuousOnCompose.At(f, affine, line, line),
				functions.ComposeApply.At(f, affine),
				real_continuous.ContinuousOnConst.At(q, line),
				real_continuous.ContinuousOnMul.At(
					a.TermAs[Fun[Real, Real]]("λy:real. q"),
					a.TermAs[Fun[Real, Real]]("f ∘ (λy:real. p + q * y)"),
					line)))
		changedNonneg := a.Have(
			"and nonnegative",
			"∀y:real. &0 ≤ q * f(p + q * y)",
			Derive(func(b *Argument) {
				b.FixAs[Real]("y")
				b.Show(
					"a positive q times a nonnegative value",
					ByArith(positive, nonneg.At(b.TermAs[Real]("p + q * y"))))
			}))
		changedWindows := a.Have(
			"q·f(p + q·y) integrates as the supremum over the windows ⟦−n, n⟧",
			"nonneg_integral(𝕌, "+
				"    «lebesgueSets», "+
				"    lebesgue_outer_measure, "+
				"    λy:real. extended_of_real(q * f(p + q * y))) = "+
				"extended_sup( "+
				"    image(λn:num. extended_of_real(real_integral(λy:real. q * f(p + q * y), -&n, &n)), 𝕌))",
			ByArith(
				changedNonneg,
				changedContinuous,
				real_order_ring.ZeroLessThanOne,
				LebesgueNonnegIntegralBySymmetricWindows.At(changed, a.TermAs[Real]("&0"), a.TermAs[Real]("&1"))))
		windows := a.Have(
			"f integrates as the supremum over the windows ⟦p − q·n, p + q·n⟧",
			"nonneg_integral(𝕌, «lebesgueSets», lebesgue_outer_measure, λx:real. extended_of_real(f(x))) = "+
				"extended_sup(image(λn:num. extended_of_real(real_integral(f, p - q * &n, p + q * &n)), 𝕌))",
			By(positive, nonneg, continuous, LebesgueNonnegIntegralBySymmetricWindows.At(f, p, q)))
		swap := a.Have(
			"the integrand q·f(p + q·y) is f(p + q·y)·q",
			"(λy:real. q * f(p + q * y)) = (λy:real. f(p + q * y) * q)",
			Funext(),
			Derive(func(b *Argument) {
				b.FixAs[Real]("y")
				b.Show(
					"the factors commute",
					ByArith())
			}))
		same := a.Have(
			"on each window the affine change gives the two the same value",
			"(λn:num. extended_of_real(real_integral(λy:real. q * f(p + q * y), -&n, &n))) = "+
				"(λn:num. extended_of_real(real_integral(f, p - q * &n, p + q * &n)))",
			Funext(),
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				lower, upper := b.TermAs[Real]("-&n"), b.TermAs[Real]("&n")
				start, end := b.TermAs[Real]("p + q * -&n"), b.TermAs[Real]("p + q * &n")
				image := b.TermAs[Set[Real]]("⟦p + q * -&n, p + q * &n⟧")
				geometry := b.Have(
					"⟦−n, n⟧ is ordered and the affine map sends it onto ⟦p − q·n, p + q·n⟧",
					"-&n ≤ &n ∧ p + q * -&n ≤ p + q * &n ∧ p + q * -&n = p - q * &n",
					ByArith(positive, real_order_ring.NumNonneg.At(n)))
				change := b.Have(
					"the affine change on the window",
					"real_integral(λy:real. f(p + q * y) * q, -&n, &n) = real_integral(f, p + q * -&n, p + q * &n)",
					By(
						geometry,
						continuous,
						set_order.SubsetUniv.At(image),
						real_continuous.ContinuousOnSubset.At(f, line, image),
						real_order_ring.LessEqRefl,
						real_integral.RiemannIntegralAffineChange.At(f, start, end, p, q, lower, upper)))
				b.Show(
					"so the two window values agree",
					By(swap, change, geometry))
			}))
		a.Show(
			"and so do their suprema",
			By(changedWindows, windows, same))
	}),
})}
