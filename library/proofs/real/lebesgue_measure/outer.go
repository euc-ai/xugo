// outer.go — the outer measure's laws: it is monotone, it lies below the
// total length of every cover and is approached from above by such
// lengths, a set inside an open interval measures at most its length, the
// empty set measures 0, and the measure of a countable union is at most
// the sum of the measures. The approximations conclude through
// extended_nonneg_real.LeOfLeAddPositive, a bound in ⟦0, ∞⟧ that holds up to every e > 0
// holding outright.

package lebesgue_measure

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinal"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/registry"
)

// OuterMeasureMono — a subset has no larger outer measure: every cover
// of t covers s, so the infimum for s runs over more lengths.
var OuterMeasureMono = outerMeasureMonoThm{family.Add(registry.ProofEntry{
	Name: "OuterMeasureMono",
	Key:  "prop_35947205c73c34c3",
	Build: family.Theorem(Statement{
		Binders:    "∀s t:set(real).",
		Hypotheses: []string{"s ⊆ t"},
		Conclusion: "lebesgue_outer_measure(s) ≤ lebesgue_outer_measure(t)",
		Abbrev: Abbrev{
			{Name: "coverLengths", Text: "λu:set(real). " +
				"    {m:extended_nonneg_real | " +
				"        ∃a b:(num → real). " +
				"            (∀x:real. x ∈ u ⇒ ∃n:num. a(n) < x ∧ x < b(n)) ∧ " +
				"            m = extended_series(λn:num. extended_of_real(b(n) - a(n)))}"},
		},
	}, func(arg *Argument, s, t *Expr[Set[Real]], smaller Fact) {
		arg.Do(Unfold(LebesgueOuterMeasureDef))
		covers := arg.Have(
			"a cover of t is a cover of s",
			"«coverLengths»(t) ⊆ «coverLengths»(s)",
			BySets(smaller))
		arg.Show(
			"so the infimum over the covers of s is the smaller",
			By(extended_nonneg_real.InfAntitone, covers))
	}),
})}

// OuterMeasureCoverBound — the outer measure of s lies below the total
// length of every cover of s, that length being one of those the
// infimum runs over.
var OuterMeasureCoverBound = outerMeasureCoverBoundThm{family.Add(registry.ProofEntry{
	Name: "OuterMeasureCoverBound",
	Key:  "prop_239cbe49ab755a1",
	Build: family.Theorem(Statement{
		Binders:    "∀s:set(real). ∀a b:(num → real).",
		Hypotheses: []string{"∀x:real. x ∈ s ⇒ ∃n:num. a(n) < x ∧ x < b(n)"},
		Conclusion: "lebesgue_outer_measure(s) ≤ extended_series(λn:num. extended_of_real(b(n) - a(n)))",
	}, func(arg *Argument, s *Expr[Set[Real]], a, b *Arrow[Nat, Real], covered Fact) {
		arg.Do(Unfold(LebesgueOuterMeasureDef))
		arg.Show(
			"the total length of the cover (a, b) is one of the lengths the infimum runs over",
			By(extended_nonneg_real.InfLower, covered))
	}),
})}

// OuterMeasureCoverApprox — a set of finite outer measure has, for every
// e > 0, a cover of total length at most its outer measure plus e. The
// outer measure is a real r, so λ*(s) + e is the larger real r + e;
// below it lies the length of some cover, the infimum being the greatest
// lower bound.
var OuterMeasureCoverApprox = outerMeasureCoverApproxThm{family.Add(registry.ProofEntry{
	Name: "OuterMeasureCoverApprox",
	Key:  "prop_392aa6879fff9f99",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(real). ∀e:real.",
		Hypotheses: []string{
			"lebesgue_outer_measure(s) ≠ extended_infinity",
			"&0 < e",
		},
		Conclusion: "∃a b:(num → real). " +
			"    (∀x:real. x ∈ s ⇒ ∃n:num. a(n) < x ∧ x < b(n)) ∧ " +
			"    extended_series(λn:num. extended_of_real(b(n) - a(n))) ≤ " +
			"    lebesgue_outer_measure(s) + extended_of_real(e)",
		Abbrev: Abbrev{
			{Name: "coverLengths", Text: "λu:set(real). " +
				"    {m:extended_nonneg_real | " +
				"        ∃a b:(num → real). " +
				"            (∀x:real. x ∈ u ⇒ ∃n:num. a(n) < x ∧ x < b(n)) ∧ " +
				"            m = extended_series(λn:num. extended_of_real(b(n) - a(n)))}"},
		},
	}, func(arg *Argument, s *Expr[Set[Real]], e *Expr[Real], finite, positive Fact) {
		measure := arg.TermAs[extended_nonneg_real.ExtendedNonnegReal]("lebesgue_outer_measure(s)")
		r, value := arg.ObtainAs[Real](
			"the outer measure of s is finite, a nonnegative real r",
			"∃r:real. &0 ≤ r ∧ lebesgue_outer_measure(s) = extended_of_real(r)",
			By(extended_nonneg_real.ExtendedCases.At(measure), finite))
		sum := arg.Have(
			"λ*(s) + e is the real r + e",
			"lebesgue_outer_measure(s) + extended_of_real(e) = extended_of_real(r + e)",
			By(
				Normalized,
				value,
				positive,
				real_order_ring.LessEqOfLessThan,
				extended_nonneg_real.OfRealAdd.At(r, e)))
		above := arg.Have(
			"r + e does not lie below r",
			"¬(extended_of_real(r + e) ≤ extended_of_real(r))",
			ByArith(value, positive, extended_nonneg_real.OfRealLe.At(arg.TermAs[Real]("r + e"), r)))
		strict := arg.Have(
			"so λ*(s) lies strictly below λ*(s) + e",
			"lebesgue_outer_measure(s) < lebesgue_outer_measure(s) + extended_of_real(e)",
			By(value, sum, above, extended_nonneg_real.LtIffNotLe))
		below := arg.Have(
			"the infimum being the greatest lower bound, some cover's length lies below λ*(s) + e",
			"∃y:extended_nonneg_real. "+
				"    y ∈ «coverLengths»(s) ∧ y < lebesgue_outer_measure(s) + extended_of_real(e)",
			By(extended_nonneg_real.InfApprox, strict, LebesgueOuterMeasureDef.At(s)))
		arg.Show(
			"that cover is the one sought",
			By(below, extended_nonneg_real.ExtendedLtDef))
	}),
})}

// OuterMeasureInsideInterval — a set inside an open interval ⟬c, d⟭ has
// outer measure at most d - c. The interval itself, followed by the empty
// intervals ⟬c, c⟭, covers the set, and every partial sum of their lengths
// is d - c.
var OuterMeasureInsideInterval = outerMeasureInsideIntervalThm{family.Add(registry.ProofEntry{
	Name: "OuterMeasureInsideInterval",
	Key:  "prop_7b0f4267bece9d58",
	Build: family.Theorem(Statement{
		Binders:    "∀s:set(real). ∀c d:real.",
		Hypotheses: []string{"s ⊆ ⟬c, d⟭"},
		Conclusion: "lebesgue_outer_measure(s) ≤ extended_of_real(d - c)",
	}, func(a *Argument, s *Expr[Set[Real]], c, d *Expr[Real], inside Fact) {
		covered := a.Have(
			"the first interval, ⟬c, d⟭, holds every point of s",
			"∀x:real. x ∈ s ⇒ ∃n:num. c < x ∧ x < COND(n = 0, d, c)",
			BySets(inside))
		partial := a.Have(
			"every partial sum of the lengths is d - c, the intervals after the first being empty",
			"∀n:num. Σ_{i∈0 .. n} extended_of_real(COND(i = 0, d, c) - c) = extended_of_real(d - c)",
			Derive(func(b *Argument) {
				b.Induct(b.Binder("n"))
				b.Base(
					"the first interval alone has length d - c",
					By(extended_nonneg_real.SumSegmentZero))
				b.Step(
					"the interval at n + 1 is empty and adds nothing",
					func(st *Argument, previous Fact) {
						empty := st.Have(
							"the interval at n + 1 is ⟬c, c⟭, of length 0",
							"COND(n + 1 = 0, d, c) - c = &0",
							ByArith())
						st.Do(Simp(Fwd(nat_arith.Add1), Fwd(extended_nonneg_real.SumSegmentPeel)))
						st.Show(
							"adding a zero length leaves the sum at d - c",
							By(previous, empty, extended_nonneg_real.AddZero))
					})
			}))
		total := a.Have(
			"so the total length of the cover is at most d - c",
			"extended_series(λn:num. extended_of_real(COND(n = 0, d, c) - c)) ≤ extended_of_real(d - c)",
			By(extended_nonneg_real.SeriesLeast, partial, extended_nonneg_real.LeRefl))
		a.Show(
			"and the outer measure lies below that total length",
			By(
				OuterMeasureCoverBound.At(
					s,
					a.TermAs[Fun[Nat, Real]]("λn:num. c"),
					a.TermAs[Fun[Nat, Real]]("λn:num. COND(n = 0, d, c)")),
				covered,
				total,
				extended_nonneg_real.LeTrans))
	}),
})}

// OuterMeasureEmpty — the empty set has outer measure 0: it lies inside
// the empty interval ⟬0, 0⟭, of length 0.
var OuterMeasureEmpty = outerMeasureEmptyThm{family.Add(registry.ProofEntry{
	Name: "OuterMeasureEmpty",
	Key:  "prop_bdeebf3eb7d2a52b",
	Build: family.Theorem("lebesgue_outer_measure(∅) = &0",
		func(a *Argument) {
			inside := a.Have(
				"the empty set lies inside ⟬0, 0⟭",
				"∅ ⊆ ⟬&0, &0⟭",
				BySets())
			bound := a.Have(
				"so its outer measure is at most the length 0 - 0",
				"lebesgue_outer_measure(∅) ≤ extended_of_real(&0 - &0)",
				By(OuterMeasureInsideInterval, inside))
			a.Show(
				"and 0 lies below every outer measure",
				ByArith(
					bound,
					extended_nonneg_real.OfRealNeg.At(a.TermAs[Real]("&0 - &0")),
					extended_nonneg_real.ZeroLe,
					extended_nonneg_real.LeAntisym.At(
						a.TermAs[extended_nonneg_real.ExtendedNonnegReal]("lebesgue_outer_measure(∅)"),
						a.TermAs[extended_nonneg_real.ExtendedNonnegReal]("&0"))))
		}),
})}

// OuterMeasureCountableSubadditive — the outer measure of a countable
// union is at most the sum of the outer measures. It suffices to bound it
// by the sum plus e for every e > 0, and an infinite sum bounds
// everything. When the sum is finite, every A(n) has finite outer
// measure, so it has a cover of total length within e/2^(n+1) of it.
// Listing all these intervals along a bijection σ from the naturals onto
// the pairs of naturals covers the union, and the total length of that
// list is the double series of the lengths, at most the sum of the outer
// measures plus Σ e/2^(n+1) = e.
var OuterMeasureCountableSubadditive = outerMeasureCountableSubadditiveThm{family.Add(registry.ProofEntry{
	Name: "OuterMeasureCountableSubadditive",
	Key:  "prop_f3da7c412a391a96",
	Build: family.Theorem(Statement{
		Binders: "∀A:(num → set(real)).",
		Conclusion: "lebesgue_outer_measure({x:real | ∃n:num. x ∈ A(n)}) ≤ " +
			"extended_series(λn:num. lebesgue_outer_measure(A(n)))",
		Abbrev: Abbrev{
			{Name: "union", Text: "{x:real | ∃n:num. x ∈ A(n)}"},
			{Name: "total", Text: "extended_series(λn:num. lebesgue_outer_measure(A(n)))"},
		},
	}, func(arg *Argument, A *Arrow[Nat, Set[Real]]) {
		union := arg.TermAs[Set[Real]]("«union»")
		measures := arg.TermAs[Fun[Nat, extended_nonneg_real.ExtendedNonnegReal]](
			"λn:num. lebesgue_outer_measure(A(n))")
		approximations := arg.Have(
			"for every e > 0 the outer measure of the union is at most the sum plus e",
			"∀e:real. &0 < e ⇒ lebesgue_outer_measure(«union») ≤ «total» + extended_of_real(e)",
			Derive(func(ep *Argument) {
				e := ep.FixAs[Real]()
				positive := ep.Assume()
				finite := ep.Unless(
					ep.Term("«total» = extended_infinity"),
					"an infinite sum bounds everything",
					Given(func(b *Argument, top Fact) {
						b.Show(
							"the sum plus e is ∞",
							By(top, extended_nonneg_real.AddEqInfinity, extended_nonneg_real.LeInfinity))
					}))
				eachFinite := ep.Have(
					"so every A(n) has finite outer measure: ∞ at n would make the partial sum to n, and the sum, ∞",
					"∀n:num. lebesgue_outer_measure(A(n)) ≠ extended_infinity",
					Derive(func(b *Argument) {
						n := b.FixAs[Nat]("n")
						b.Show(
							"the term at n lies in the partial sum to n, below the finite sum",
							By(
								finite,
								extended_nonneg_real.SeriesPartialLe.At(measures, n),
								extended_nonneg_real.SumEqInfinity.At(measures, b.TermAs[Set[Nat]]("0 .. n")),
								num_segment.Finite,
								num_segment.MembershipFromZero,
								nat_order.LessEqRefl,
								extended_nonneg_real.ExtendedLeDef))
					}))
				covers := ep.Have(
					"each A(n) has a cover of total length within e/2^(n+1) of its outer measure",
					"∀n:num. ∃a b:(num → real). "+
						"    (∀x:real. x ∈ A(n) ⇒ ∃k:num. a(k) < x ∧ x < b(k)) ∧ "+
						"    extended_series(λk:num. extended_of_real(b(k) - a(k))) ≤ "+
						"    lebesgue_outer_measure(A(n)) + extended_of_real(e / &2 ^ (n + 1))",
					Derive(func(b *Argument) {
						n := b.FixAs[Nat]("n")
						b.Show(
							"A(n) has finite outer measure, and e/2^(n+1) is positive",
							ByArith(
								eachFinite.At(n),
								positive,
								OuterMeasureCoverApprox.At(A.Apply(n), b.TermAs[Real]("e / &2 ^ (n + 1)")),
								real_pow.PowPos.At(b.TermAs[Real]("&2"), b.TermAs[Nat]("n + 1"))))
					}))
				choice := ep.Have(
					"witnesses chosen at each n form a pair of sequences",
					Statement{
						Binders:    "∀Q:(num → (num → real) → (num → real) → bool).",
						Hypotheses: []string{"∀n:num. ∃a b:(num → real). Q(n, a, b)"},
						Conclusion: "∃c d:(num → num → real). ∀n:num. Q(n, c(n), d(n))",
					},
					Derive(func(b *Argument) {
						b.Fix()
						each := b.Assume()
						b.Show(
							"Skolemize the witnesses",
							By(each))
					}))
				_, _, chosen := ep.Obtain2As[Fun2[Nat, Nat, Real], Fun2[Nat, Nat, Real]](
					"so there are covers (c(n, k), d(n, k)) of the A(n), one for each n",
					"∃c d:(num → num → real). ∀n:num. "+
						"    (∀x:real. x ∈ A(n) ⇒ ∃k:num. c(n, k) < x ∧ x < d(n, k)) ∧ "+
						"    extended_series(λk:num. extended_of_real(d(n, k) - c(n, k))) ≤ "+
						"    lebesgue_outer_measure(A(n)) + extended_of_real(e / &2 ^ (n + 1))",
					By(
						choice.At(ep.Term(
							"λn:num. λa:(num → real). λb:(num → real). "+
								"    (∀x:real. x ∈ A(n) ⇒ ∃k:num. a(k) < x ∧ x < b(k)) ∧ "+
								"    extended_series(λk:num. extended_of_real(b(k) - a(k))) ≤ "+
								"    lebesgue_outer_measure(A(n)) + extended_of_real(e / &2 ^ (n + 1))")),
						covers))
				enum, bijective := ep.ObtainAs[Fun[Nat, Prod[Nat, Nat]]](
					"the pairs of naturals are listed by a bijection σ from the naturals",
					"∃σ:(num → prod(num, num)). injective_on(𝕌, σ) ∧ image(σ, 𝕌) = 𝕌",
					By(
						cardinal.CardEqSym.At(ep.TermAs[Set[Prod[Nat, Nat]]]("𝕌"), ep.TermAs[Set[Nat]]("𝕌")),
						cardinal.PairNumBijection,
						cardinal.CardEqDef))
				merged := ep.Have(
					"listed along σ, the intervals cover the union",
					"∀x:real. x ∈ «union» ⇒ ∃k:num. c(fst(σ(k)), snd(σ(k))) < x ∧ x < d(fst(σ(k)), snd(σ(k)))",
					Derive(func(b *Argument) {
						b.FixAs[Real]("x")
						inUnion := b.Assume()
						n, inA := b.UnpackAs[Nat](inUnion, "n")
						_, holds := b.ObtainAs[Nat](
							"x lies in an interval of the cover of A(n)",
							"∃j:num. c(n, j) < x ∧ x < d(n, j)",
							By(chosen.At(n), inA))
						place := b.TermAs[Prod[Nat, Nat]]("(n, j)")
						k, hits := b.ObtainAs[Nat](
							"σ lists the pair (n, j) at some place k",
							"∃k:num. (n, j) = σ(k)",
							By(bijective, set_image.InRange.At(enum, place), set_basic.InUniv))
						b.Take(k)
						b.Do(hits.RwRev())
						b.Show(
							"the interval listed at k is the one at (n, j)",
							By(holds, pairs.Fst, pairs.Snd))
					}))
				covered := ep.Have(
					"so the outer measure of the union is at most the double series of the lengths",
					"lebesgue_outer_measure(«union») ≤ "+
						"extended_series(λm:num. extended_series(λk:num. extended_of_real(d(m, k) - c(m, k))))",
					By(
						OuterMeasureCoverBound.At(
							union,
							ep.TermAs[Fun[Nat, Real]]("λk:num. c(fst(σ(k)), snd(σ(k)))"),
							ep.TermAs[Fun[Nat, Real]]("λk:num. d(fst(σ(k)), snd(σ(k)))")),
						merged,
						extended_nonneg_real.SeriesPairing.At(
							ep.TermAs[Fun2[Nat, Nat, extended_nonneg_real.ExtendedNonnegReal]](
								"λm:num. λk:num. extended_of_real(d(m, k) - c(m, k))"),
							enum),
						bijective))
				termwise := ep.Have(
					"each inner series lies below the outer measure of A(m) plus e/2^(m+1)",
					"extended_series(λm:num. extended_series(λk:num. extended_of_real(d(m, k) - c(m, k)))) ≤ "+
						"extended_series(λm:num. lebesgue_outer_measure(A(m)) + extended_of_real(e / &2 ^ (m + 1)))",
					By(extended_nonneg_real.SeriesMono, chosen))
				ep.Show(
					"and that series is the sum plus Σ e/2^(m+1), which is e",
					By(
						termwise,
						covered,
						positive,
						extended_nonneg_real.SeriesAdd.At(
							measures,
							ep.TermAs[Fun[Nat, extended_nonneg_real.ExtendedNonnegReal]](
								"λm:num. extended_of_real(e / &2 ^ (m + 1))")),
						extended_nonneg_real.SeriesGeometric.At(e),
						real_order_ring.LessEqOfLessThan,
						extended_nonneg_real.LeTrans))
			}))
		arg.Show(
			"so it is at most the sum itself",
			By(extended_nonneg_real.LeOfLeAddPositive, approximations))
	}),
})}
