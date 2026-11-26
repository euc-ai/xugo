// simple.go — the integral of the nonnegative simple functions on a measure
// space. The measure is additive on finitely many disjoint measurable sets,
// and that is what lets a simple function's integral be computed on any
// finite measurable partition of Ω on whose pieces the function is
// constant: the partition cuts each level set of the function into
// measurable pieces, and each piece meets one level set only.

package measure_simple

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/measure/measurable_function"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/sigma_algebra"
	"github.com/euc-ai/xugo/library/registry"
)

// SimpleLevelSets — each level set of a simple function is measurable: s
// is y exactly where it is at least y and at most y, and both of those sets
// are measurable for a measurable function.
var SimpleLevelSets = simpleLevelSetsThm{family.Add(registry.ProofEntry{
	Name: "SimpleLevelSets",
	Key:  "prop_ffab3335ec3aee8f",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀s:(A → real). ∀y:real.",
		Hypotheses: []string{
			"sigma_algebra_on(Ω, S)",
			"measure_simple(Ω, S, s)",
		},
		Conclusion: "{x:A | x ∈ Ω ∧ s(x) = y} ∈ S",
	}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]], s *Arrow[A, Real], y *Expr[Real],
		sigma, simple Fact) {
		parts := a.Conjuncts(
			a.Unfolded(simple, NonnegSimpleDef),
			"s is measurable",
			"s takes finitely many values on Ω",
			"s is nonnegative on Ω")
		twoSided := a.Have(
			"s is y exactly where it is at least y and at most y",
			"{x:A | x ∈ Ω ∧ s(x) = y} = {x:A | x ∈ Ω ∧ y ≤ s(x)} ∩ {x:A | x ∈ Ω ∧ s(x) ≤ y}",
			BySets(real_construction.LessEqAntisym))
		a.Show(
			"both sets are measurable, s being measurable, and so is their intersection",
			By(
				twoSided,
				sigma,
				parts[0],
				sigma_algebra.SigmaFiniteOperations.At(Ω, S),
				measurable_function.RealMeasurableAtLeast.At(Ω, S, s, y),
				measurable_function.RealMeasurableAtMost.At(Ω, S, s, y)))
	}),
})}

// SimpleIntegralPartition — a function constant on each piece of a finite
// measurable partition of Ω has, as its simple integral, the sum over the
// pieces of the value there times the piece's measure. The partition cuts
// each level set {s = y} into the measurable pieces {s = y} ∩ P(j), each
// P(j) or empty, and the measure adds over them; exchanging the two finite
// sums, the level sets cut P(j) into P(j) itself, at the value c(j), and
// empty pieces elsewhere.
var SimpleIntegralPartition = simpleIntegralPartitionThm{family.Add(registry.ProofEntry{
	Name: "SimpleIntegralPartition",
	Key:  "prop_a97a08182b0f308c",
	Build: family.Theorem(measure_space.MeasureOn.Statement(Statement{
		Binders: "∀s:(A → real). ∀k:set(B). ∀P:(B → set(A)). ∀c:(B → real).",
		Hypotheses: []string{
			"finite(k)",
			"∀j:B. j ∈ k ⇒ P(j) ∈ S",
			"∀i j:B. i ∈ k ∧ j ∈ k ∧ i ≠ j ⇒ disjoint(P(i), P(j))",
			"∀x:A. x ∈ Ω ⇒ ∃j:B. j ∈ k ∧ x ∈ P(j)",
			"∀j:B. ∀x:A. j ∈ k ∧ x ∈ P(j) ⇒ s(x) = c(j)",
		},
		Conclusion: "measure_simple_integral(Ω, μ, s) = Σ_{j∈k} extended_of_real(c(j)) * μ(P(j))",
	}), func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		measure Fact,
		s *Arrow[A, Real],
		k *Expr[Set[B]],
		P *Arrow[B, Set[A]],
		c *Arrow[B, Real],
		finite, measurable, disjoint, cover, constant Fact,
	) {
		laws := a.Conjuncts(
			a.Unfolded(measure, measure_space.MeasureOn),
			"the measurable sets form a sigma algebra",
			"the empty set has measure zero",
			"countable disjoint unions have the series of their measures")
		sigma, emptyMass := laws[0], laws[1]
		inside := a.Have(
			"each piece lies in Ω, a measurable set",
			"∀j:B. j ∈ k ⇒ P(j) ⊆ Ω",
			BySets(
				measurable,
				a.Conjuncts(
					a.Unfolded(sigma, sigma_algebra.SigmaAlgebraOnDef),
					"the measurable sets lie in Ω",
					"Ω is measurable",
					"relative complements are measurable",
					"countable unions are measurable")[0]))
		values := a.Have(
			"on Ω, s takes only values c takes on k",
			"image(s, Ω) ⊆ image(c, k)",
			BySets(constant, cover))
		finiteValues := a.Have(
			"so s takes finitely many values on Ω",
			"finite(image(s, Ω))",
			By(finite, values, finite_set.FiniteSubset, finite_set.FiniteImage))
		cut := a.Have(
			"the pieces cut each level set of s into measurable pieces, over which the measure adds",
			"∀y:real. μ({x:A | x ∈ Ω ∧ s(x) = y}) = Σ_{j∈k} μ({x:A | x ∈ Ω ∧ s(x) = y} ∩ P(j))",
			Derive(func(b *Argument) {
				b.FixAs[Real]("y")
				pieces := b.Have(
					"each cut piece is P(j) or empty, so measurable",
					"∀j:B. j ∈ k ⇒ {x:A | x ∈ Ω ∧ s(x) = y} ∩ P(j) ∈ S",
					Derive(func(d *Argument) {
						d.FixAs[B]("j")
						inK := d.Assume()
						d.Cases(d.Term("c(j) = y"))
						d.When(
							"where c(j) is y, the piece is all of P(j)",
							func(e *Argument, hit Fact) {
								whole := e.Have(
									"P(j) lies in Ω, and s is y on it",
									"{x:A | x ∈ Ω ∧ s(x) = y} ∩ P(j) = P(j)",
									BySets(constant, inK, hit, inside))
								e.Show(
									"which is measurable",
									By(whole, inK, measurable))
							})
						d.Otherwise(
							"elsewhere the piece is empty",
							func(e *Argument, miss Fact) {
								empty := e.Have(
									"s is c(j), not y, on P(j)",
									"{x:A | x ∈ Ω ∧ s(x) = y} ∩ P(j) = ∅",
									BySets(constant, inK, miss))
								e.Show(
									"which is measurable",
									By(empty, sigma, sigma_algebra.SigmaFiniteOperations.At(Ω, S)))
							})
					}))
				apart := b.Have(
					"the cut pieces are disjoint, as the pieces are",
					Statement{
						Binders: "∀i j:B.",
						Hypotheses: []string{
							"i ∈ k",
							"j ∈ k",
							"i ≠ j",
						},
						Conclusion: "disjoint({x:A | x ∈ Ω ∧ s(x) = y} ∩ P(i), {x:A | x ∈ Ω ∧ s(x) = y} ∩ P(j))",
					},
					BySets(disjoint))
				union := b.Have(
					"and they make up the level set, the pieces covering Ω",
					"⋃image(λj:B. {x:A | x ∈ Ω ∧ s(x) = y} ∩ P(j), k) = {x:A | x ∈ Ω ∧ s(x) = y}",
					BySets(cover))
				b.Show(
					"the measure adds over finitely many disjoint measurable sets",
					By(
						union,
						measure,
						finite,
						pieces,
						apart,
						measure_space.MeasureFiniteAdditive.At(
							Ω,
							S,
							μ,
							b.TermAs[Fun[B, Set[A]]]("λj:B. {x:A | x ∈ Ω ∧ s(x) = y} ∩ P(j)"),
							k)))
			}))
		scaled := a.Have(
			"and each term of the integral splits along the pieces",
			"∀y:real. "+
				"    extended_of_real(y) * μ({x:A | x ∈ Ω ∧ s(x) = y}) = "+
				"    Σ_{j∈k} extended_of_real(y) * μ({x:A | x ∈ Ω ∧ s(x) = y} ∩ P(j))",
			Derive(func(b *Argument) {
				y := b.FixAs[Real]("y")
				b.Show(
					"the factor y moves through the finite sum",
					By(
						finite,
						cut.At(y),
						extended_nonneg_real.SumScale.At(
							b.TermAs[ExtendedNonnegReal]("extended_of_real(y)"),
							b.TermAs[Fun[B, ExtendedNonnegReal]]("λj:B. μ({x:A | x ∈ Ω ∧ s(x) = y} ∩ P(j))"),
							k)))
			}))
		a.Do(Unfold(SimpleIntegralDef), Simp(Fwd(scaled)))
		perPiece := a.Have(
			"on the piece P(j) only the level set at c(j) contributes, and it meets P(j) in all of P(j)",
			Statement{
				Binders:    "∀j:B.",
				Hypotheses: []string{"j ∈ k"},
				Conclusion: "Σ_{y∈image(s, Ω)} extended_of_real(y) * μ({x:A | x ∈ Ω ∧ s(x) = y} ∩ P(j)) = " +
					"extended_of_real(c(j)) * μ(P(j))",
			},
			Derive(func(b *Argument) {
				b.FixAs[B]("j")
				inK := b.Assume()
				pieces := b.Have(
					"s is c(j) on P(j), which lies in Ω, so P(j) lies in the level set at c(j) and misses every other",
					"{x:A | x ∈ Ω ∧ s(x) = c(j)} ∩ P(j) = P(j) ∧ "+
						"(∀y:real. y ≠ c(j) ⇒ {x:A | x ∈ Ω ∧ s(x) = y} ∩ P(j) = ∅)",
					BySets(constant, inK, inside))
				silent := b.Have(
					"so every other value contributes 0",
					"∀y:real. y ≠ c(j) ⇒ extended_of_real(y) * μ({x:A | x ∈ Ω ∧ s(x) = y} ∩ P(j)) = &0",
					By(pieces, emptyMass, extended_nonneg_real.MulZero))
				b.Cases(b.Term("c(j) ∈ image(s, Ω)"))
				b.When(
					"c(j) is a value of s: its term is the whole sum",
					func(d *Argument, taken Fact) {
						rest := d.Have(
							"the other values add up to 0",
							"Σ_{y∈delete(image(s, Ω), c(j))} extended_of_real(y) * μ({x:A | x ∈ Ω ∧ s(x) = y} ∩ P(j)) = &0",
							By(silent, extended_nonneg_real.ExtendedSumZero, set_basic.InDelete))
						peel := d.Have(
							"the sum is the term at c(j) and the sum over the other values",
							"extended_of_real(c(j)) * μ({x:A | x ∈ Ω ∧ s(x) = c(j)} ∩ P(j)) + "+
								"Σ_{y∈delete(image(s, Ω), c(j))} extended_of_real(y) * μ({x:A | x ∈ Ω ∧ s(x) = y} ∩ P(j)) = "+
								"Σ_{y∈image(s, Ω)} extended_of_real(y) * μ({x:A | x ∈ Ω ∧ s(x) = y} ∩ P(j))",
							Unfold(extended_nonneg_real.ExtendedSumDef),
							By(
								finiteValues,
								taken,
								monoidal.Delete.Read(extended_nonneg_real.MonoidalAdd).At(
									d.TermAs[Set[Real]]("image(s, Ω)"),
									d.TermAs[Fun[Real, ExtendedNonnegReal]](
										"λy:real. extended_of_real(y) * μ({x:A | x ∈ Ω ∧ s(x) = y} ∩ P(j))"),
									d.TermAs[Real]("c(j)"))))
						d.Show(
							"so the sum is c(j) times the measure of P(j)",
							By(peel, rest, pieces, extended_nonneg_real.AddZero))
					})
				b.Otherwise(
					"c(j) is no value of s: P(j) is empty, and every term is 0",
					func(d *Argument, missed Fact) {
						zero := d.Have(
							"every value of s differs from c(j), so the sum is 0",
							"Σ_{y∈image(s, Ω)} extended_of_real(y) * μ({x:A | x ∈ Ω ∧ s(x) = y} ∩ P(j)) = &0",
							By(missed, silent, extended_nonneg_real.ExtendedSumZero))
						empty := d.Have(
							"a point of P(j) would lie in Ω and be sent to c(j)",
							"P(j) = ∅",
							BySets(missed, constant, inK, inside))
						d.Show(
							"so both sides are 0",
							By(zero, empty, emptyMass, extended_nonneg_real.MulZero))
					})
			}))
		swapped := a.Have(
			"the two finite sums exchange",
			"Σ_{y∈image(s, Ω)} (Σ_{j∈k} extended_of_real(y) * μ({x:A | x ∈ Ω ∧ s(x) = y} ∩ P(j))) = "+
				"Σ_{j∈k} (Σ_{y∈image(s, Ω)} extended_of_real(y) * μ({x:A | x ∈ Ω ∧ s(x) = y} ∩ P(j)))",
			Unfold(extended_nonneg_real.ExtendedSumDef),
			By(finite, finiteValues, monoidal.Swap.Read(extended_nonneg_real.MonoidalAdd)))
		collected := a.Have(
			"and each piece contributes its value times its measure",
			"Σ_{j∈k} (Σ_{y∈image(s, Ω)} extended_of_real(y) * μ({x:A | x ∈ Ω ∧ s(x) = y} ∩ P(j))) = "+
				"Σ_{j∈k} extended_of_real(c(j)) * μ(P(j))",
			Unfold(extended_nonneg_real.ExtendedSumDef),
			By(perPiece, monoidal.Congruence.Read(extended_nonneg_real.MonoidalAdd)))
		a.Show(
			"exchanging the sums and collecting each piece gives the sum over the partition",
			By(swapped, collected))
	}),
})}

// SimpleIntegralIndicator — for c ≥ 0, c times the indicator of a
// measurable set E is a simple function, and its integral is c times the
// measure of E. E and the rest of Ω partition Ω, indexed by whether a point
// lies in E; the function is c on the one and 0 on the other, and 0 times
// the measure of the rest is 0.
var SimpleIntegralIndicator = simpleIntegralIndicatorThm{family.Add(registry.ProofEntry{
	Name: "SimpleIntegralIndicator",
	Key:  "prop_c9f345379e6e5783",
	Build: family.Theorem(measure_space.MeasureOn.Statement(Statement{
		Binders: "∀E:set(A). ∀c:real.",
		Hypotheses: []string{
			"E ∈ S",
			"&0 ≤ c",
		},
		Conclusion: "measure_simple(Ω, S, «indicator») ∧ " +
			"measure_simple_integral(Ω, μ, «indicator») = extended_of_real(c) * μ(E)",
		Abbrev: Abbrev{
			{Name: "indicator", Text: "λx:A. COND(x ∈ E, c, &0)"},
		},
	}), func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		measure Fact,
		E *Expr[Set[A]],
		c *Expr[Real],
		measurable, nonnegC Fact,
	) {
		laws := a.Conjuncts(
			a.Unfolded(measure, measure_space.MeasureOn),
			"the measurable sets form a sigma algebra",
			"the empty set has measure zero",
			"countable disjoint unions have the series of their measures")
		sigma := laws[0]
		indicator := a.TermAs[Fun[A, Real]]("«indicator»")
		values := a.Have(
			"the function takes only the values c and 0",
			"image(«indicator», Ω) ⊆ {c, &0}",
			BySets())
		nonneg := a.Have(
			"and both are nonnegative",
			"∀x:A. x ∈ Ω ⇒ &0 ≤ COND(x ∈ E, c, &0)",
			Derive(func(b *Argument) {
				b.FixAs[A]("x")
				b.Assume()
				b.Cases(b.Term("x ∈ E"))
				b.When(
					"on E the value is c",
					func(d *Argument, in Fact) {
						d.Show(
							"which is nonnegative",
							By(in, nonnegC))
					})
				b.Otherwise(
					"off E the value is 0",
					func(d *Argument, out Fact) {
						d.Show(
							"which is nonnegative",
							By(out, real_order_ring.LessEqRefl))
					})
			}))
		simple := a.Have(
			"so the function is simple: measurable, finitely valued and nonnegative on Ω",
			"measure_simple(Ω, S, «indicator»)",
			Unfold(NonnegSimpleDef),
			By(
				sigma,
				measurable,
				values,
				nonneg,
				measurable_function.RealMeasurableIndicator.At(Ω, S, E, c),
				finite_set.FiniteSubset,
				finite_set.FiniteRules))
		twoPieces := a.Have(
			"two pieces are finitely many",
			"finite({⊤, ⊥})",
			By(finite_set.FiniteRules))
		piecesMeasurable := a.Have(
			"E and the rest of Ω are measurable",
			"∀b:bool. b ∈ {⊤, ⊥} ⇒ COND(b, E, Ω ∖ E) ∈ S",
			By(measurable, sigma, sigma_algebra.SigmaAlgebraOnDef.At(Ω, S)))
		apart := a.Have(
			"they are disjoint",
			"∀i j:bool. i ∈ {⊤, ⊥} ∧ j ∈ {⊤, ⊥} ∧ i ≠ j ⇒ disjoint(COND(i, E, Ω ∖ E), COND(j, E, Ω ∖ E))",
			BySets())
		cover := a.Have(
			"and every point of Ω lies in one of them",
			"∀x:A. x ∈ Ω ⇒ ∃b:bool. b ∈ {⊤, ⊥} ∧ x ∈ COND(b, E, Ω ∖ E)",
			BySets())
		constant := a.Have(
			"the function is c on E and 0 off it",
			"∀b:bool. ∀x:A. b ∈ {⊤, ⊥} ∧ x ∈ COND(b, E, Ω ∖ E) ⇒ COND(x ∈ E, c, &0) = COND(b, c, &0)",
			BySets())
		partitioned := a.Have(
			"so the integral is the sum over the two pieces",
			"measure_simple_integral(Ω, μ, «indicator») = "+
				"Σ_{b∈{⊤, ⊥}} extended_of_real(COND(b, c, &0)) * μ(COND(b, E, Ω ∖ E))",
			By(
				measure,
				twoPieces,
				piecesMeasurable,
				apart,
				cover,
				constant,
				SimpleIntegralPartition.At(
					Ω,
					S,
					μ,
					indicator,
					a.TermAs[Set[Bool]]("{⊤, ⊥}"),
					a.TermAs[Fun[Bool, Set[A]]]("λb:bool. COND(b, E, Ω ∖ E)"),
					a.TermAs[Fun[Bool, Real]]("λb:bool. COND(b, c, &0)"))))
		evaluated := a.Have(
			"the piece E contributes c times its measure, the rest 0",
			"Σ_{b∈{⊤, ⊥}} extended_of_real(COND(b, c, &0)) * μ(COND(b, E, Ω ∖ E)) = extended_of_real(c) * μ(E)",
			Simp(
				Fwd(extended_nonneg_real.SumClauses),
				Fwd(finite_set.FiniteRules),
				Fwd(set_basic.InInsert),
				Fwd(set_basic.NotInEmpty)),
			By(extended_nonneg_real.MulComm, extended_nonneg_real.MulZero, extended_nonneg_real.AddZero))
		a.Show(
			"the function is simple, with that integral",
			By(simple, partitioned, evaluated))
	}),
})}

// SimpleIntegralScale — scaling a simple function by c ≥ 0 scales its
// integral by c. The level sets of s partition Ω, c·s being c·y on the one
// at y; c·y splits as c times y, both being nonnegative, and the factor c
// leaves the finite sum.
var SimpleIntegralScale = simpleIntegralScaleThm{family.Add(registry.ProofEntry{
	Name: "SimpleIntegralScale",
	Key:  "prop_4cb147c26bf071a7",
	Build: family.Theorem(measure_space.MeasureOn.Statement(Statement{
		Binders: "∀s:(A → real). ∀c:real.",
		Hypotheses: []string{
			"measure_simple(Ω, S, s)",
			"&0 ≤ c",
		},
		Conclusion: "measure_simple_integral(Ω, μ, λx:A. c * s(x)) = " +
			"extended_of_real(c) * measure_simple_integral(Ω, μ, s)",
	}), func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		measure Fact,
		s *Arrow[A, Real],
		c *Expr[Real],
		simple, nonnegC Fact,
	) {
		laws := a.Conjuncts(
			a.Unfolded(measure, measure_space.MeasureOn),
			"the measurable sets form a sigma algebra",
			"the empty set has measure zero",
			"countable disjoint unions have the series of their measures")
		sigma := laws[0]
		parts := a.Conjuncts(
			a.Unfolded(simple, NonnegSimpleDef),
			"s is measurable",
			"s takes finitely many values on Ω",
			"s is nonnegative on Ω")
		levels := a.Have(
			"the level sets of s are measurable",
			"∀y:real. y ∈ image(s, Ω) ⇒ {x:A | x ∈ Ω ∧ s(x) = y} ∈ S",
			By(sigma, simple, SimpleLevelSets))
		apart := a.Have(
			"they are disjoint",
			Statement{
				Binders: "∀i j:real.",
				Hypotheses: []string{
					"i ∈ image(s, Ω)",
					"j ∈ image(s, Ω)",
					"i ≠ j",
				},
				Conclusion: "disjoint({x:A | x ∈ Ω ∧ s(x) = i}, {x:A | x ∈ Ω ∧ s(x) = j})",
			},
			BySets())
		cover := a.Have(
			"and they cover Ω",
			"∀x:A. x ∈ Ω ⇒ ∃y:real. y ∈ image(s, Ω) ∧ x ∈ {x:A | x ∈ Ω ∧ s(x) = y}",
			BySets())
		constant := a.Have(
			"on the level set at y, c·s is c·y",
			"∀y:real. ∀x:A. y ∈ image(s, Ω) ∧ x ∈ {x:A | x ∈ Ω ∧ s(x) = y} ⇒ c * s(x) = c * y",
			BySets())
		factored := a.Have(
			"c·y splits as c times y, both being nonnegative",
			Statement{
				Binders:    "∀y:real.",
				Hypotheses: []string{"y ∈ image(s, Ω)"},
				Conclusion: "extended_of_real(c * y) * μ({x:A | x ∈ Ω ∧ s(x) = y}) = " +
					"extended_of_real(c) * (extended_of_real(y) * μ({x:A | x ∈ Ω ∧ s(x) = y}))",
			},
			By(
				parts[2],
				nonnegC,
				set_basic.InImage,
				extended_nonneg_real.OfRealMul,
				extended_nonneg_real.MulAssoc))
		a.Show(
			"the integral of c·s, computed on the level sets of s",
			CalcEq(
				Leg(
					a.TermAs[ExtendedNonnegReal](
						"Σ_{y∈image(s, Ω)} extended_of_real(c * y) * μ({x:A | x ∈ Ω ∧ s(x) = y})"),
					"c·s is c·y on the level set of s at y",
					By(
						measure,
						parts[1],
						levels,
						apart,
						cover,
						constant,
						SimpleIntegralPartition.At(
							Ω,
							S,
							μ,
							a.TermAs[Fun[A, Real]]("λx:A. c * s(x)"),
							a.TermAs[Set[Real]]("image(s, Ω)"),
							a.TermAs[Fun[Real, Set[A]]]("λy:real. {x:A | x ∈ Ω ∧ s(x) = y}"),
							a.TermAs[Fun[Real, Real]]("λy:real. c * y")))),
				Leg(
					a.TermAs[ExtendedNonnegReal](
						"Σ_{y∈image(s, Ω)} extended_of_real(c) * (extended_of_real(y) * μ({x:A | x ∈ Ω ∧ s(x) = y}))"),
					"each term splits off the factor c",
					Unfold(extended_nonneg_real.ExtendedSumDef),
					By(factored, monoidal.Congruence.Read(extended_nonneg_real.MonoidalAdd))),
				Leg(
					a.TermAs[ExtendedNonnegReal](
						"extended_of_real(c) * Σ_{y∈image(s, Ω)} extended_of_real(y) * μ({x:A | x ∈ Ω ∧ s(x) = y})"),
					"which leaves the finite sum",
					By(parts[1], extended_nonneg_real.SumScale)),
				FinalLeg(
					"the sum left is the integral of s",
					By(SimpleIntegralDef))))
	}),
})}

// SimpleScale — a nonnegative multiple of a simple function is simple:
// measurable as a multiple of a measurable function, nonnegative on Ω, and
// finitely valued there, its values being c times those of s.
var SimpleScale = simpleScaleThm{family.Add(registry.ProofEntry{
	Name: "SimpleScale",
	Key:  "prop_1418910bcba346d7",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀s:(A → real). ∀c:real.",
		Hypotheses: []string{
			"sigma_algebra_on(Ω, S)",
			"measure_simple(Ω, S, s)",
			"&0 ≤ c",
		},
		Conclusion: "measure_simple(Ω, S, λx:A. c * s(x))",
	}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]], s *Arrow[A, Real], c *Expr[Real],
		sigma, simple, nonnegC Fact) {
		parts := a.Conjuncts(
			a.Unfolded(simple, NonnegSimpleDef),
			"s is measurable",
			"s takes finitely many values on Ω",
			"s is nonnegative on Ω")
		nonneg := a.Have(
			"c·s is nonnegative on Ω",
			"∀x:A. x ∈ Ω ⇒ &0 ≤ c * s(x)",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				inΩ := b.Assume()
				b.Show(
					"a product of two nonnegative numbers",
					ByArith(nonnegC, inΩ, parts[2].At(x)))
			}))
		values := a.Have(
			"the values of c·s on Ω are c times values of s",
			"image(λx:A. c * s(x), Ω) ⊆ image(λy:real. c * y, image(s, Ω))",
			BySets())
		a.Show(
			"so c·s is simple",
			By(
				sigma,
				parts[0],
				parts[1],
				nonneg,
				values,
				NonnegSimpleDef,
				measurable_function.RealMeasurableScale.At(Ω, S, s, c),
				finite_set.FiniteImage.At(
					a.TermAs[Fun[Real, Real]]("λy:real. c * y"), a.TermAs[Set[Real]]("image(s, Ω)")),
				finite_set.FiniteSubset))
	}),
})}

// SimplePairsFinite — two simple functions take finitely many pairs of
// values together on Ω: each takes finitely many values there
// (finite_set.FiniteImagePair).
var SimplePairsFinite = simplePairsFiniteThm{family.Add(registry.ProofEntry{
	Name: "SimplePairsFinite",
	Key:  "prop_bf16bc63c1a32518",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀s t:(A → real).",
		Hypotheses: []string{
			"measure_simple(Ω, S, s)",
			"measure_simple(Ω, S, t)",
		},
		Conclusion: "finite(image(λx:A. (s(x), t(x)), Ω))",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		s, t *Arrow[A, Real],
		simpleS, simpleT Fact,
	) {
		a.Show(
			"s and t take finitely many values each on Ω",
			By(simpleS, simpleT, NonnegSimpleDef, finite_set.FiniteImagePair.At(s, t, Ω)))
	}),
})}

// SimpleIntegralRefine — a function of two simple functions s and t is
// integrated on their common refinement: the pieces of Ω where s and t take
// a given pair of values, over the finitely many pairs (s, t) takes. The
// pieces are measurable, disjoint and cover Ω, and h(s, t) is h(y, z) on the
// piece at (y, z).
var SimpleIntegralRefine = simpleIntegralRefineThm{family.Add(registry.ProofEntry{
	Name: "SimpleIntegralRefine",
	Key:  "prop_9def3ef4f12e3456",
	Build: family.Theorem(measure_space.MeasureOn.Statement(Statement{
		Binders: "∀s t:(A → real). ∀h:(real → real → real).",
		Hypotheses: []string{
			"measure_simple(Ω, S, s)",
			"measure_simple(Ω, S, t)",
		},
		Conclusion: "measure_simple_integral(Ω, μ, λx:A. h(s(x), t(x))) = " +
			"Σ_{p∈«pairs»} extended_of_real(h(fst(p), snd(p))) * " +
			"μ({x:A | x ∈ Ω ∧ s(x) = fst(p) ∧ t(x) = snd(p)})",
		Abbrev: Abbrev{
			{Name: "pairs", Text: "image(λx:A. (s(x), t(x)), Ω)"},
		},
	}), func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		measure Fact,
		s, t *Arrow[A, Real],
		h *Arrow2[Real, Real, Real],
		simpleS, simpleT Fact,
	) {
		laws := a.Conjuncts(
			a.Unfolded(measure, measure_space.MeasureOn),
			"the measurable sets form a sigma algebra",
			"the empty set has measure zero",
			"countable disjoint unions have the series of their measures")
		sigma := laws[0]
		finitePairs := a.Have(
			"the pairs of values (s, t) takes on Ω are finitely many",
			"finite(«pairs»)",
			By(simpleS, simpleT, SimplePairsFinite.At(Ω, S, s, t)))
		piecesMeasurable := a.Have(
			"each piece is measurable, the intersection of a level set of s and one of t",
			"∀p:prod(real, real). {x:A | x ∈ Ω ∧ s(x) = fst(p) ∧ t(x) = snd(p)} ∈ S",
			Derive(func(b *Argument) {
				b.FixAs[Prod[Real, Real]]("p")
				split := b.Have(
					"the piece at p is where s is fst(p) and t is snd(p)",
					"{x:A | x ∈ Ω ∧ s(x) = fst(p) ∧ t(x) = snd(p)} = "+
						"{x:A | x ∈ Ω ∧ s(x) = fst(p)} ∩ {x:A | x ∈ Ω ∧ t(x) = snd(p)}",
					BySets())
				b.Show(
					"both level sets are measurable",
					By(
						sigma,
						simpleS,
						simpleT,
						split,
						SimpleLevelSets.At(Ω, S, s, b.TermAs[Real]("fst(p)")),
						SimpleLevelSets.At(Ω, S, t, b.TermAs[Real]("snd(p)")),
						sigma_algebra.SigmaFiniteOperations.At(Ω, S)))
			}))
		apart := a.Have(
			"pieces at distinct pairs are disjoint",
			Statement{
				Binders: "∀p q:prod(real, real).",
				Hypotheses: []string{
					"p ∈ «pairs»",
					"q ∈ «pairs»",
					"p ≠ q",
				},
				Conclusion: "disjoint({x:A | x ∈ Ω ∧ s(x) = fst(p) ∧ t(x) = snd(p)}, " +
					"    {x:A | x ∈ Ω ∧ s(x) = fst(q) ∧ t(x) = snd(q)})",
			},
			BySets(pairs.PairEta))
		cover := a.Have(
			"each point of Ω lies in the piece at its own pair of values",
			Statement{
				Binders:    "∀x:A.",
				Hypotheses: []string{"x ∈ Ω"},
				Conclusion: "∃p:prod(real, real). p ∈ «pairs» ∧ x ∈ {x:A | x ∈ Ω ∧ s(x) = fst(p) ∧ t(x) = snd(p)}",
			},
			BySets(pairs.Fst, pairs.Snd))
		constant := a.Have(
			"and on the piece at p the function is h(fst(p), snd(p))",
			Statement{
				Binders: "∀p:prod(real, real). ∀x:A.",
				Hypotheses: []string{
					"p ∈ «pairs»",
					"x ∈ {x:A | x ∈ Ω ∧ s(x) = fst(p) ∧ t(x) = snd(p)}",
				},
				Conclusion: "h(s(x), t(x)) = h(fst(p), snd(p))",
			},
			BySets())
		a.Show(
			"so the integral is computed on the pieces",
			By(
				measure,
				finitePairs,
				piecesMeasurable,
				apart,
				cover,
				constant,
				SimpleIntegralPartition.At(
					Ω,
					S,
					μ,
					a.TermAs[Fun[A, Real]]("λx:A. h(s(x), t(x))"),
					a.TermAs[Set[Prod[Real, Real]]]("«pairs»"),
					a.TermAs[Fun[Prod[Real, Real], Set[A]]](
						"λp:prod(real, real). {x:A | x ∈ Ω ∧ s(x) = fst(p) ∧ t(x) = snd(p)}"),
					a.TermAs[Fun[Prod[Real, Real], Real]]("λp:prod(real, real). h(fst(p), snd(p))"))))
	}),
})}

// SimpleIntegralMono — the simple integral is monotone. On the common
// refinement of s and t both integrals are sums over the pairs of values
// (y, z) the two take together on Ω, with y and with z as the coefficient
// of one piece; each pair is taken at some point of Ω, where
// y = s(x) ≤ t(x) = z, so the sums compare term by term.
var SimpleIntegralMono = simpleIntegralMonoThm{family.Add(registry.ProofEntry{
	Name: "SimpleIntegralMono",
	Key:  "prop_908f9ccd84869100",
	Build: family.Theorem(measure_space.MeasureOn.Statement(Statement{
		Binders: "∀s t:(A → real).",
		Hypotheses: []string{
			"measure_simple(Ω, S, s)",
			"measure_simple(Ω, S, t)",
			"∀x:A. x ∈ Ω ⇒ s(x) ≤ t(x)",
		},
		Conclusion: "measure_simple_integral(Ω, μ, s) ≤ measure_simple_integral(Ω, μ, t)",
		Abbrev: Abbrev{
			{Name: "pairs", Text: "image(λx:A. (s(x), t(x)), Ω)"},
			{Name: "piece", Text: "λp:prod(real, real). {x:A | x ∈ Ω ∧ s(x) = fst(p) ∧ t(x) = snd(p)}"},
		},
	}), func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		measure Fact,
		s, t *Arrow[A, Real],
		simpleS, simpleT, below Fact,
	) {
		sRefined := a.Have(
			"the integral of s, on the common refinement",
			"measure_simple_integral(Ω, μ, s) = Σ_{p∈«pairs»} extended_of_real(fst(p)) * μ(«piece»(p))",
			By(
				measure,
				simpleS,
				simpleT,
				SimpleIntegralRefine.At(Ω, S, μ, s, t, a.TermAs[Fun2[Real, Real, Real]]("λy:real. λz:real. y"))))
		tRefined := a.Have(
			"and the integral of t",
			"measure_simple_integral(Ω, μ, t) = Σ_{p∈«pairs»} extended_of_real(snd(p)) * μ(«piece»(p))",
			By(
				measure,
				simpleS,
				simpleT,
				SimpleIntegralRefine.At(Ω, S, μ, s, t, a.TermAs[Fun2[Real, Real, Real]]("λy:real. λz:real. z"))))
		termwise := a.Have(
			"on each piece the coefficient of s is at most that of t",
			Statement{
				Binders:    "∀p:prod(real, real).",
				Hypotheses: []string{"p ∈ «pairs»"},
				Conclusion: "extended_of_real(fst(p)) * μ(«piece»(p)) ≤ extended_of_real(snd(p)) * μ(«piece»(p))",
			},
			Derive(func(b *Argument) {
				b.FixAs[Prod[Real, Real]]("p")
				taken := b.Assume()
				x, at := b.ObtainAs[A](
					"p is the pair of values of s and t at some point x of Ω",
					"∃x:A. p = (s(x), t(x)) ∧ x ∈ Ω",
					By(taken, set_basic.InImage))
				ordered := b.Have(
					"so fst(p) = s(x) ≤ t(x) = snd(p), and t(x) is nonnegative",
					"fst(p) ≤ snd(p) ∧ &0 ≤ snd(p)",
					By(
						simpleT,
						below.At(x),
						at,
						NonnegSimpleDef.At(Ω, S, t),
						pairs.Fst.At(s.Apply(x), t.Apply(x)),
						pairs.Snd.At(s.Apply(x), t.Apply(x))))
				b.Show(
					"the measure of the piece multiplies the two coefficients in order",
					By(
						ordered,
						extended_nonneg_real.OfRealLe.At(b.TermAs[Real]("fst(p)"), b.TermAs[Real]("snd(p)")),
						extended_nonneg_real.MulLeMono.At(
							b.TermAs[ExtendedNonnegReal]("extended_of_real(fst(p))"),
							b.TermAs[ExtendedNonnegReal]("extended_of_real(snd(p))"),
							b.TermAs[ExtendedNonnegReal]("μ(«piece»(p))")),
						extended_nonneg_real.MulComm))
			}))
		a.Show(
			"so the sums compare term by term",
			By(
				sRefined,
				tRefined,
				termwise,
				simpleS,
				simpleT,
				SimplePairsFinite.At(Ω, S, s, t),
				extended_nonneg_real.SumMono.At(
					a.TermAs[Fun[Prod[Real, Real], ExtendedNonnegReal]](
						"λp:prod(real, real). extended_of_real(fst(p)) * μ(«piece»(p))"),
					a.TermAs[Fun[Prod[Real, Real], ExtendedNonnegReal]](
						"λp:prod(real, real). extended_of_real(snd(p)) * μ(«piece»(p))"),
					a.TermAs[Set[Prod[Real, Real]]]("«pairs»"))))
	}),
})}

// SimpleAdd — the sum of two simple functions is simple: measurable as a sum
// of measurable functions, nonnegative on Ω, and finitely valued there, each
// of its values being y + z for one of the finitely many pairs of values
// (y, z) the two take together.
var SimpleAdd = simpleAddThm{family.Add(registry.ProofEntry{
	Name: "SimpleAdd",
	Key:  "prop_37a992a2f70b8806",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀s t:(A → real).",
		Hypotheses: []string{
			"sigma_algebra_on(Ω, S)",
			"measure_simple(Ω, S, s)",
			"measure_simple(Ω, S, t)",
		},
		Conclusion: "measure_simple(Ω, S, λx:A. s(x) + t(x))",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		s, t *Arrow[A, Real],
		sigma, simpleS, simpleT Fact,
	) {
		partsS := a.Conjuncts(
			a.Unfolded(simpleS, NonnegSimpleDef),
			"s is measurable",
			"s takes finitely many values on Ω",
			"s is nonnegative on Ω")
		partsT := a.Conjuncts(
			a.Unfolded(simpleT, NonnegSimpleDef),
			"t is measurable",
			"t takes finitely many values on Ω",
			"t is nonnegative on Ω")
		pairsFinite := a.Have(
			"s and t take finitely many pairs of values together on Ω",
			"finite(image(λx:A. (s(x), t(x)), Ω))",
			By(simpleS, simpleT, SimplePairsFinite.At(Ω, S, s, t)))
		reached := a.Have(
			"the value of s + t at a point x of Ω is y + z for the pair (y, z) of values at x",
			Statement{
				Binders:    "∀x:A.",
				Hypotheses: []string{"x ∈ Ω"},
				Conclusion: "s(x) + t(x) ∈ " +
					"image(λp:prod(real, real). fst(p) + snd(p), image(λx:A. (s(x), t(x)), Ω))",
			},
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				inΩ := b.Assume()
				b.Show(
					"the pair at x is (s(x), t(x))",
					By(
						inΩ,
						set_basic.InImage.At(
							b.TermAs[Fun[Prod[Real, Real], Real]]("λp:prod(real, real). fst(p) + snd(p)"),
							b.TermAs[Set[Prod[Real, Real]]]("image(λx:A. (s(x), t(x)), Ω)"),
							b.TermAs[Real]("s(x) + t(x)")),
						set_image.FunInImage.At(b.TermAs[Fun[A, Prod[Real, Real]]]("λx:A. (s(x), t(x))"), Ω, x),
						pairs.Fst,
						pairs.Snd))
			}))
		values := a.Have(
			"so s + t takes its values on Ω among the sums of those pairs",
			"image(λx:A. s(x) + t(x), Ω) ⊆ "+
				"image(λp:prod(real, real). fst(p) + snd(p), image(λx:A. (s(x), t(x)), Ω))",
			By(reached, set_image.ImageSubsetIff))
		measurableSum := a.Have(
			"s + t is measurable",
			"real_measurable(Ω, S, λx:A. s(x) + t(x))",
			By(sigma, partsS[0], partsT[0], measurable_function.RealMeasurableAdd.At(Ω, S, s, t)))
		finiteSum := a.Have(
			"it takes finitely many values on Ω",
			"finite(image(λx:A. s(x) + t(x), Ω))",
			By(pairsFinite, values, finite_set.FiniteImage, finite_set.FiniteSubset))
		nonnegSum := a.Have(
			"and it is nonnegative on Ω",
			"∀x:A. x ∈ Ω ⇒ &0 ≤ s(x) + t(x)",
			By(partsS[2], partsT[2], real_order_ring.AddNonneg))
		a.Show(
			"so s + t is simple",
			By(measurableSum, finiteSum, nonnegSum, NonnegSimpleDef))
	}),
})}

// SimpleIntegralAdd — the simple integral is additive. On the common
// refinement of s and t the integral of s + t is a sum over the pairs of
// values (y, z) with coefficient y + z on each piece; that coefficient
// splits into y and z, both nonnegative, and the sum separates into the
// integrals of s and of t on the same refinement.
var SimpleIntegralAdd = simpleIntegralAddThm{family.Add(registry.ProofEntry{
	Name: "SimpleIntegralAdd",
	Key:  "prop_251e67cc655e2b42",
	Build: family.Theorem(measure_space.MeasureOn.Statement(Statement{
		Binders: "∀s t:(A → real).",
		Hypotheses: []string{
			"measure_simple(Ω, S, s)",
			"measure_simple(Ω, S, t)",
		},
		Conclusion: "measure_simple_integral(Ω, μ, λx:A. s(x) + t(x)) = " +
			"measure_simple_integral(Ω, μ, s) + measure_simple_integral(Ω, μ, t)",
		Abbrev: Abbrev{
			{Name: "pairs", Text: "image(λx:A. (s(x), t(x)), Ω)"},
			{Name: "piece", Text: "λp:prod(real, real). {x:A | x ∈ Ω ∧ s(x) = fst(p) ∧ t(x) = snd(p)}"},
		},
	}), func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		measure Fact,
		s, t *Arrow[A, Real],
		simpleS, simpleT Fact,
	) {
		split := a.Have(
			"on each piece the coefficient y + z splits into y and z",
			Statement{
				Binders:    "∀p:prod(real, real).",
				Hypotheses: []string{"p ∈ «pairs»"},
				Conclusion: "extended_of_real(fst(p) + snd(p)) * μ(«piece»(p)) = " +
					"extended_of_real(fst(p)) * μ(«piece»(p)) + extended_of_real(snd(p)) * μ(«piece»(p))",
			},
			Derive(func(b *Argument) {
				b.FixAs[Prod[Real, Real]]("p")
				taken := b.Assume()
				x, at := b.ObtainAs[A](
					"p is the pair of values of s and t at some point x of Ω",
					"∃x:A. p = (s(x), t(x)) ∧ x ∈ Ω",
					By(taken, set_basic.InImage))
				nonneg := b.Have(
					"so both of its values are nonnegative",
					"&0 ≤ fst(p) ∧ &0 ≤ snd(p)",
					By(
						simpleS,
						simpleT,
						at,
						NonnegSimpleDef.At(Ω, S, s),
						NonnegSimpleDef.At(Ω, S, t),
						pairs.Fst.At(s.Apply(x), t.Apply(x)),
						pairs.Snd.At(s.Apply(x), t.Apply(x))))
				b.Show(
					"the embedding adds them, and the measure of the piece distributes",
					By(
						nonneg,
						extended_nonneg_real.OfRealAdd.At(b.TermAs[Real]("fst(p)"), b.TermAs[Real]("snd(p)")),
						extended_nonneg_real.MulComm,
						extended_nonneg_real.MulAddDistrib.At(
							b.TermAs[ExtendedNonnegReal]("μ(«piece»(p))"),
							b.TermAs[ExtendedNonnegReal]("extended_of_real(fst(p))"),
							b.TermAs[ExtendedNonnegReal]("extended_of_real(snd(p))"))))
			}))
		a.Show(
			"the integral of s + t, computed on the common refinement",
			CalcEq(
				Leg(
					a.TermAs[ExtendedNonnegReal](
						"Σ_{p∈«pairs»} extended_of_real(fst(p) + snd(p)) * μ(«piece»(p))"),
					"s + t is y + z on the piece where s is y and t is z",
					By(
						measure,
						simpleS,
						simpleT,
						At(
							SimpleIntegralRefine, Ω, S, μ, s, t, a.TermAs[Fun2[Real, Real, Real]]("λy:real. λz:real. y + z")))),
				Leg(
					a.TermAs[ExtendedNonnegReal](
						"Σ_{p∈«pairs»} (extended_of_real(fst(p)) * μ(«piece»(p)) + extended_of_real(snd(p)) * μ(«piece»(p)))"),
					"each coefficient splits",
					Unfold(extended_nonneg_real.ExtendedSumDef),
					By(split, monoidal.Congruence.Read(extended_nonneg_real.MonoidalAdd))),
				Leg(
					a.TermAs[ExtendedNonnegReal](
						"Σ_{p∈«pairs»} extended_of_real(fst(p)) * μ(«piece»(p)) + "+
							"Σ_{p∈«pairs»} extended_of_real(snd(p)) * μ(«piece»(p))"),
					"and the finite sum separates",
					By(simpleS, simpleT, SimplePairsFinite.At(Ω, S, s, t), extended_nonneg_real.SumAdd)),
				FinalLeg(
					"into the integrals of s and of t on the same refinement",
					By(
						measure,
						simpleS,
						simpleT,
						SimpleIntegralRefine.At(Ω, S, μ, s, t, a.TermAs[Fun2[Real, Real, Real]]("λy:real. λz:real. y")),
						SimpleIntegralRefine.At(Ω, S, μ, s, t, a.TermAs[Fun2[Real, Real, Real]]("λy:real. λz:real. z"))))))
	}),
})}

// SimpleIntegralRestrict — a simple function s cut down to a measurable set
// E, and 0 off it, is simple, and its integral sums each value y of s times
// the measure of the part of E where s is y. On Ω the restriction exceeds a
// negative level everywhere and any other level on E where s does, so it is
// measurable; its values are 0 and those of s. Its level sets in Ω, indexed
// by 0 and the values of s, partition Ω; off 0 the level set at y is
// {s = y} ∩ E, and the value 0 contributes nothing.
var SimpleIntegralRestrict = simpleIntegralRestrictThm{family.Add(registry.ProofEntry{
	Name: "SimpleIntegralRestrict",
	Key:  "prop_4c96c827e6deb690",
	Build: family.Theorem(measure_space.MeasureOn.Statement(Statement{
		Binders: "∀s:(A → real). ∀E:set(A).",
		Hypotheses: []string{
			"measure_simple(Ω, S, s)",
			"E ∈ S",
		},
		Conclusion: "measure_simple(Ω, S, «restricted») ∧ " +
			"measure_simple_integral(Ω, μ, «restricted») = " +
			"Σ_{y∈image(s, Ω)} extended_of_real(y) * μ({x:A | x ∈ Ω ∧ s(x) = y} ∩ E)",
		Abbrev: Abbrev{
			{Name: "restricted", Text: "λx:A. COND(x ∈ E, s(x), &0)"},
			{Name: "level", Text: "λy:real. {x:A | x ∈ Ω ∧ COND(x ∈ E, s(x), &0) = y}"},
			{Name: "values", Text: "insert(&0, image(s, Ω))"},
		},
	}), func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		measure Fact,
		s *Arrow[A, Real],
		E *Expr[Set[A]],
		simple, measurable Fact,
	) {
		laws := a.Conjuncts(
			a.Unfolded(measure, measure_space.MeasureOn),
			"the measurable sets form a sigma algebra",
			"the empty set has measure zero",
			"countable disjoint unions have the series of their measures")
		sigma := laws[0]
		parts := a.Conjuncts(
			a.Unfolded(simple, NonnegSimpleDef),
			"s is measurable",
			"s takes finitely many values on Ω",
			"s is nonnegative on Ω")
		restricted := a.TermAs[Fun[A, Real]]("«restricted»")
		nonneg := a.Have(
			"the restriction is nonnegative on Ω, s being so",
			"∀x:A. x ∈ Ω ⇒ &0 ≤ COND(x ∈ E, s(x), &0)",
			By(parts[2], real_order_ring.LessEqRefl))
		above := a.Have(
			"every upper ray of s is measurable",
			"∀t:real. {x:A | x ∈ Ω ∧ t < s(x)} ∈ S",
			By(sigma, parts[0], measurable_function.RealMeasurableIffRay.At(Ω, S, s)))
		rays := a.Have(
			"every upper ray of the restriction is measurable",
			"∀d:real. {x:A | x ∈ Ω ∧ d < COND(x ∈ E, s(x), &0)} ∈ S",
			Derive(func(b *Argument) {
				d := b.FixAs[Real]("d")
				b.Cases(b.Term("d < &0"))
				b.When(
					"a negative level the restriction exceeds on all of Ω",
					func(c *Argument, negative Fact) {
						everywhere := c.Have(
							"it is nonnegative on Ω, so above d",
							"∀x:A. x ∈ Ω ⇒ d < COND(x ∈ E, s(x), &0)",
							Derive(func(e *Argument) {
								x := e.FixAs[A]("x")
								inΩ := e.Assume()
								e.Show(
									"0 ≤ the value, and d < 0",
									ByArith(negative, inΩ, nonneg.At(x)))
							}))
						whole := c.Have(
							"so the ray is the carrier",
							"{x:A | x ∈ Ω ∧ d < COND(x ∈ E, s(x), &0)} = Ω",
							BySets(everywhere))
						c.Show(
							"which is measurable",
							By(whole, sigma, sigma_algebra.SigmaAlgebraOnDef.At(Ω, S)))
					})
				b.Otherwise(
					"any other level it exceeds on E where s does",
					func(c *Argument, notNegative Fact) {
						cut := c.Have(
							"the restriction exceeds d exactly on E where s exceeds d",
							"{x:A | x ∈ Ω ∧ d < COND(x ∈ E, s(x), &0)} = E ∩ {x:A | x ∈ Ω ∧ d < s(x)}",
							BySets(notNegative))
						c.Show(
							"the intersection of two measurable sets",
							By(cut, measurable, above.At(d), sigma, sigma_algebra.SigmaFiniteOperations.At(Ω, S)))
					})
			}))
		measurableCut := a.Have(
			"so the restriction is measurable",
			"real_measurable(Ω, S, «restricted»)",
			By(sigma, rays, measurable_function.RealMeasurableIffRay.At(Ω, S, restricted)))
		cutValues := a.Have(
			"on Ω the restriction takes the value 0 and values of s",
			"image(«restricted», Ω) ⊆ «values»",
			BySets())
		simpleCut := a.Have(
			"so the restriction is simple",
			"measure_simple(Ω, S, «restricted»)",
			By(
				parts[1],
				measurableCut,
				nonneg,
				cutValues,
				NonnegSimpleDef,
				finite_set.FiniteSubset,
				finite_set.FiniteRules))
		finiteValues := a.Have(
			"0 and the values of s are finitely many",
			"finite(«values»)",
			By(parts[1], finite_set.FiniteRules))
		levelsMeasurable := a.Have(
			"the level sets of the restriction are measurable, it being simple",
			"∀y:real. «level»(y) ∈ S",
			By(sigma, simpleCut, SimpleLevelSets))
		apart := a.Have(
			"distinct level sets are disjoint",
			"∀i j:real. i ≠ j ⇒ disjoint(«level»(i), «level»(j))",
			BySets())
		cover := a.Have(
			"and the level sets at 0 and the values of s cover Ω",
			"∀x:A. x ∈ Ω ⇒ ∃y:real. y ∈ «values» ∧ x ∈ «level»(y)",
			BySets())
		partitioned := a.Have(
			"so the integral of the restriction is computed on its level sets",
			"measure_simple_integral(Ω, μ, «restricted») = Σ_{y∈«values»} extended_of_real(y) * μ(«level»(y))",
			By(
				measure,
				finiteValues,
				levelsMeasurable,
				apart,
				cover,
				SimpleIntegralPartition.At(
					Ω,
					S,
					μ,
					restricted,
					a.TermAs[Set[Real]]("«values»"),
					a.TermAs[Fun[Real, Set[A]]]("«level»"),
					a.TermAs[Fun[Real, Real]]("λy:real. y"))))
		termwise := a.Have(
			"off 0 the level set at y is the part of E where s is y, and at 0 both terms are 0",
			"∀y:real. "+
				"    extended_of_real(y) * μ(«level»(y)) = extended_of_real(y) * μ({x:A | x ∈ Ω ∧ s(x) = y} ∩ E)",
			Derive(func(b *Argument) {
				b.FixAs[Real]("y")
				b.Cases(b.Term("y = &0"))
				b.When(
					"at 0 both terms vanish",
					func(c *Argument, zero Fact) {
						c.Do(zero.Rw())
						zeroValue := c.TermAs[ExtendedNonnegReal]("&0")
						cutMeasure := c.TermAs[ExtendedNonnegReal]("μ(«level»(&0))")
						partMeasure := c.TermAs[ExtendedNonnegReal]("μ({x:A | x ∈ Ω ∧ s(x) = &0} ∩ E)")
						c.Show(
							"0 times any measure is 0",
							By(
								extended_nonneg_real.MulComm.At(zeroValue, cutMeasure),
								extended_nonneg_real.MulComm.At(zeroValue, partMeasure),
								extended_nonneg_real.MulZero.At(cutMeasure),
								extended_nonneg_real.MulZero.At(partMeasure)))
					})
				b.Otherwise(
					"off 0 the two sets agree",
					func(c *Argument, nonzero Fact) {
						same := c.Have(
							"the restriction is y ≠ 0 exactly on the part of E where s is y",
							"«level»(y) = {x:A | x ∈ Ω ∧ s(x) = y} ∩ E",
							BySets(nonzero))
						c.Show(
							"so the terms agree",
							By(same))
					})
			}))
		zeroValue := a.TermAs[ExtendedNonnegReal]("&0")
		zeroPart := a.TermAs[ExtendedNonnegReal]("μ({x:A | x ∈ Ω ∧ s(x) = &0} ∩ E)")
		sum := a.TermAs[ExtendedNonnegReal](
			"Σ_{y∈image(s, Ω)} extended_of_real(y) * μ({x:A | x ∈ Ω ∧ s(x) = y} ∩ E)")
		dropZero := a.Have(
			"the value 0 adds nothing to the sum",
			"Σ_{y∈«values»} extended_of_real(y) * μ({x:A | x ∈ Ω ∧ s(x) = y} ∩ E) = "+
				"Σ_{y∈image(s, Ω)} extended_of_real(y) * μ({x:A | x ∈ Ω ∧ s(x) = y} ∩ E)",
			Simp(Fwd(extended_nonneg_real.SumClauses)),
			By(
				extended_nonneg_real.MulComm.At(zeroValue, zeroPart),
				extended_nonneg_real.MulZero.At(zeroPart),
				extended_nonneg_real.AddComm.At(zeroValue, sum),
				extended_nonneg_real.AddZero.At(sum)))
		a.Do(Simp(Fwd(partitioned), Fwd(termwise), Fwd(dropZero)))
		a.Show(
			"the restriction is simple, with that integral",
			By(simpleCut))
	}),
})}

// IntegerPartSimple — the integer part of a bounded measurable function,
// divided by a positive constant, is a simple function: it is a multiple of
// a measurable function, its values on Ω lie among the j/c with j at most
// the bound, and none is negative.
var IntegerPartSimple = integerPartSimpleThm{family.Add(registry.ProofEntry{
	Name: "IntegerPartSimple",
	Key:  "prop_a1f248901093272",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀h:(A → real). ∀k:(A → num). ∀M:num. ∀c:real.",
		Hypotheses: []string{
			"sigma_algebra_on(Ω, S)",
			"real_measurable(Ω, S, h)",
			"∀x:A. x ∈ Ω ⇒ &k(x) ≤ h(x) ∧ h(x) < &k(x) + &1",
			"∀x:A. x ∈ Ω ⇒ h(x) ≤ &M",
			"&0 < c",
		},
		Conclusion: "measure_simple(Ω, S, «quotient»)",
		Abbrev: Abbrev{
			{Name: "quotient", Text: "λx:A. &k(x) / c"},
			{Name: "grid", Text: "image(λj:num. &j / c, {j:num | j ≤ M})"},
		},
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		h *Arrow[A, Real],
		k *Arrow[A, Nat],
		M *Expr[Nat],
		c *Expr[Real],
		sigma, measurable, integerPart, bounded, positive Fact,
	) {
		quotient := a.Have(
			"dividing by c is multiplying by 1/c",
			"«quotient» = (λx:A. real_inv(c) * &k(x))",
			Funext(),
			ByArith())
		measurableQuotient := a.Have(
			"x ↦ k(x)/c is measurable, a multiple of the measurable integer part",
			"real_measurable(Ω, S, «quotient»)",
			By(
				Normalized,
				sigma,
				measurable,
				integerPart,
				quotient,
				measurable_function.RealMeasurableIntegerPart.At(Ω, S, h, k),
				measurable_function.RealMeasurableScale.At(
					Ω, S, a.TermAs[Fun[A, Real]]("λx:A. &k(x)"), a.TermAs[Real]("real_inv(c)"))))
		atMostM := a.Have(
			"no integer part on Ω exceeds M",
			"∀x:A. x ∈ Ω ⇒ k(x) ≤ M",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				inΩ := b.Assume()
				below := b.Have(
					"k(x) ≤ h(x) ≤ M",
					"&k(x) ≤ &M",
					ByArith(inΩ, integerPart.At(x), bounded.At(x)))
				b.Show(
					"so k(x) ≤ M in ℕ",
					By(below, real_construction.OfNumLessEq.At(k.Apply(x), M)))
			}))
		values := a.Have(
			"so the values on Ω lie among the j/c with j ≤ M",
			"image(«quotient», Ω) ⊆ «grid»",
			BySets(atMostM))
		finite := a.Have(
			"finitely many of them, the image of a finite segment",
			"finite(image(«quotient», Ω))",
			By(
				values,
				finite_set.FiniteSubset.At(
					a.TermAs[Set[Real]]("image(«quotient», Ω)"), a.TermAs[Set[Real]]("«grid»")),
				finite_set.FiniteImage.At(
					a.TermAs[Fun[Nat, Real]]("λj:num. &j / c"), a.TermAs[Set[Nat]]("{j:num | j ≤ M}")),
				num_segment.FiniteBelow.At(M)))
		nonnegative := a.Have(
			"and none of them negative",
			"∀x:A. x ∈ Ω ⇒ &0 ≤ &k(x) / c",
			Derive(func(b *Argument) {
				b.FixAs[A]("x")
				b.Assume()
				b.Show(
					"an integer part over a positive c",
					ByArith(positive))
			}))
		a.Show(
			"a measurable function with finitely many values on Ω, none negative",
			By(measurableQuotient, finite, nonnegative, NonnegSimpleDef))
	}),
})}
