// value_theorems.go — what continuity carries: a function continuous on a
// connected set maps it onto a connected set, and one continuous on a
// compact set onto a compact set; on ⟦a, b⟧ these are the intermediate
// value theorem and the extreme value theorem, and by the first, through the
// ordered-field law, a function continuous and injective on an interval is
// strictly monotone there.

package real_continuous

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/ordered_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ordered_instance"
	"github.com/euc-ai/xugo/library/proofs/real/real_topology"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/topology/compact"
	"github.com/euc-ai/xugo/library/proofs/topology/connected"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Images of connected and compact sets
// ---------------------------------------------------------------------------

// ContinuousImageConnected — a function continuous on a connected set of
// reals maps it onto a connected set. Continuity on s makes f a
// continuous map from the subspace s, in which s is connected as it is
// in the line, and a continuous map carries a connected set onto a
// connected set.
var ContinuousImageConnected = continuousImageConnectedThm{family.Add(registry.ProofEntry{
	Name: "ContinuousImageConnected",
	Key:  "prop_a2e8de26fc1be266",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀s:set(real).",
		Hypotheses: []string{
			"real_continuous_on(s, f)",
			"connected_in(s)",
		},
		Conclusion: "connected_in(image(f, s))",
	},
		func(a *Argument, f *Arrow[Real, Real], s *Expr[Set[Real]], given Fact) {
			parts := a.Conjuncts(
				given,
				"f is continuous on s",
				"s is connected")
			line := a.TermAs[Set[Set[Real]]]("real_topology")
			subspace := a.TermAs[Set[Set[Real]]]("subtopology(s)")
			mapping := a.Have(
				"f is a continuous map from the subspace s to the line",
				"continuous_map(subtopology(s), real_topology, f)",
				By(ContinuousOnIffMap.At(f, s), parts[0]))
			inSubspace := a.Have(
				"s is connected in the subspace s, as it is in the line",
				"connected_in(subtopology(s), s)",
				By(connected.ConnectedInSubtopology.At(line, s, s), set_order.SubsetRefl.At(s), parts[1]))
			a.Show(
				"so its image is connected",
				By(continuous.ImageConnected.At(subspace, line, f, s), mapping, inSubspace))
		}),
})}

// ContinuousImageCompact — a function continuous on a compact set of
// reals maps it onto a compact set: ContinuousImageConnected with
// compactness in place of connectedness.
var ContinuousImageCompact = continuousImageCompactThm{family.Add(registry.ProofEntry{
	Name: "ContinuousImageCompact",
	Key:  "prop_65ad08fd830b12ad",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀s:set(real).",
		Hypotheses: []string{
			"real_continuous_on(s, f)",
			"compact_in(s)",
		},
		Conclusion: "compact_in(image(f, s))",
	},
		func(a *Argument, f *Arrow[Real, Real], s *Expr[Set[Real]], given Fact) {
			parts := a.Conjuncts(
				given,
				"f is continuous on s",
				"s is compact")
			line := a.TermAs[Set[Set[Real]]]("real_topology")
			subspace := a.TermAs[Set[Set[Real]]]("subtopology(s)")
			mapping := a.Have(
				"f is a continuous map from the subspace s to the line",
				"continuous_map(subtopology(s), real_topology, f)",
				By(ContinuousOnIffMap.At(f, s), parts[0]))
			a.Show(
				"s being compact in the line and so in the subspace s, its image is compact",
				By(
					continuous.ImageCompact.At(subspace, line, f, s),
					mapping,
					parts[1],
					compact.CompactInOwnSubtopology.At(line, s)))
		}),
})}

// ---------------------------------------------------------------------------
// The intermediate value theorem
// ---------------------------------------------------------------------------

// ContinuousImageInterval — a function continuous on an interval maps it
// onto an interval: on the line the connected sets are the intervals,
// and continuity carries connectedness.
var ContinuousImageInterval = continuousImageIntervalThm{family.Add(registry.ProofEntry{
	Name: "ContinuousImageInterval",
	Key:  "prop_f3dd19cfd087a75f",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀s:set(real).",
		Hypotheses: []string{
			"real_continuous_on(s, f)",
			"real_interval(s)",
		},
		Conclusion: "real_interval(image(f, s))",
	},
		func(a *Argument, f *Arrow[Real, Real], s *Expr[Set[Real]], given Fact) {
			parts := a.Conjuncts(
				given,
				"f is continuous on s",
				"s is an interval")
			connected := a.Have(
				"an interval is connected",
				"connected_in(s)",
				By(real_topology.IntervalConnected.At(s), parts[1]))
			image := a.Have(
				"so its image under f is connected",
				"connected_in(image(f, s))",
				By(ContinuousImageConnected.At(f, s), parts[0], connected))
			a.Show(
				"and a connected set of reals is an interval",
				By(real_topology.ConnectedImpInterval.At(a.TermAs[Set[Real]]("image(f, s)")), image))
		}),
})}

// ValuesInterval — the values of a function continuous on ⟦a, b⟧ form an
// interval holding f(a) and f(b). ⟦a, b⟧ is an interval — a real between
// two of its points lies between a and b — continuity carries it onto an
// interval, and its ends give the values f(a) and f(b). Both forms of the
// intermediate value theorem read it.
var ValuesInterval = valuesIntervalThm{family.Add(registry.ProofEntry{
	Name: "ValuesInterval",
	Key:  "prop_9aa40742dacc35ec",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀a b:real.",
		Hypotheses: []string{
			"a ≤ b",
			"real_continuous_on(⟦a, b⟧, f)",
		},
		Conclusion: "real_interval(image(f, ⟦a, b⟧)) ∧ f(a) ∈ image(f, ⟦a, b⟧) ∧ f(b) ∈ image(f, ⟦a, b⟧)",
	},
		func(arg *Argument, f *Arrow[Real, Real], a, b *Expr[Real], given Fact) {
			parts := arg.Conjuncts(
				given,
				"a ≤ b",
				"f is continuous on ⟦a, b⟧")
			segmentSet := arg.TermAs[Set[Real]]("⟦a, b⟧")
			isInterval := arg.Have(
				"⟦a, b⟧ is an interval: a real between two of its points lies between a and b",
				"real_interval(⟦a, b⟧)",
				Unfold(real_topology.RealIntervalDef),
				Derive(func(c *Argument) {
					c.FixAs[Real]("x")
					c.FixAs[Real]("t")
					c.FixAs[Real]("z")
					held := c.Conjuncts(
						c.Assume(),
						"x lies in ⟦a, b⟧",
						"z lies in ⟦a, b⟧",
						"x ≤ t",
						"t ≤ z")
					ends := c.Have(
						"x and z lie between a and b",
						"a ≤ x ∧ z ≤ b",
						BySets(held[0], held[1]))
					between := c.Have(
						"so t does",
						"a ≤ t ∧ t ≤ b",
						ByArith(ends, held[2], held[3]))
					c.Show(
						"so t lies in ⟦a, b⟧",
						BySets(between))
				}))
			imageInterval := arg.Have(
				"so its image is an interval",
				"real_interval(image(f, ⟦a, b⟧))",
				By(ContinuousImageInterval.At(f, segmentSet), parts[1], isInterval))
			aIn := arg.Have(
				"a lies in ⟦a, b⟧",
				"a ∈ ⟦a, b⟧",
				BySets(real_order_ring.LessEqRefl.At(a), parts[0]))
			bIn := arg.Have(
				"and so does b",
				"b ∈ ⟦a, b⟧",
				BySets(real_order_ring.LessEqRefl.At(b), parts[0]))
			faIn := arg.Have(
				"f(a) is a value on ⟦a, b⟧",
				"f(a) ∈ image(f, ⟦a, b⟧)",
				By(set_image.FunInImage.At(f, segmentSet, a), aIn))
			fbIn := arg.Have(
				"and so is f(b)",
				"f(b) ∈ image(f, ⟦a, b⟧)",
				By(set_image.FunInImage.At(f, segmentSet, b), bIn))
			arg.Show(
				"the values form an interval holding f(a) and f(b)",
				By(imageInterval, faIn, fbIn))
		}),
})}

// IntermediateValue — a function continuous on ⟦a, b⟧ takes every value
// between f(a) and f(b): its values form an interval holding both, so
// every y between them is a value, taken at some point of ⟦a, b⟧.
var IntermediateValue = intermediateValueThm{family.Add(registry.ProofEntry{
	Name: "IntermediateValue",
	Key:  "prop_8d12d2519ca72feb",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀a b y:real.",
		Hypotheses: []string{
			"a ≤ b",
			"real_continuous_on(⟦a, b⟧, f)",
			"f(a) ≤ y",
			"y ≤ f(b)",
		},
		Conclusion: "∃x:real. a ≤ x ∧ x ≤ b ∧ f(x) = y",
	},
		func(arg *Argument, f *Arrow[Real, Real], a, b, y *Expr[Real], given Fact) {
			parts := arg.Conjuncts(
				given,
				"a ≤ b",
				"f is continuous on ⟦a, b⟧",
				"f(a) ≤ y",
				"y ≤ f(b)")
			values := arg.Conjuncts(
				arg.Have(
					"the values on ⟦a, b⟧ form an interval holding f(a) and f(b)",
					"real_interval(image(f, ⟦a, b⟧)) ∧ f(a) ∈ image(f, ⟦a, b⟧) ∧ f(b) ∈ image(f, ⟦a, b⟧)",
					By(ValuesInterval.At(f, a, b), parts[0], parts[1])),
				"the values form an interval",
				"f(a) is a value",
				"f(b) is a value")
			between := arg.Unfolded(values[0], real_topology.RealIntervalDef)
			yIn := arg.Have(
				"y lies between f(a) and f(b), so it is a value",
				"y ∈ image(f, ⟦a, b⟧)",
				By(between.At(f.Apply(a), y, f.Apply(b)), values[1], values[2], parts[2], parts[3]))
			x, attained := arg.ObtainAs[Real](
				"the value y is taken at a point x of ⟦a, b⟧",
				"∃x:real. y = f(x) ∧ x ∈ ⟦a, b⟧",
				By(set_basic.InImage.At(f, arg.TermAs[Set[Real]]("⟦a, b⟧"), y), yIn))
			arg.Take(x)
			arg.Show(
				"x lies between a and b, and f(x) = y",
				BySets(attained))
		}),
})}

// IntermediateValueDecreasing — the same when f(b) ≤ y ≤ f(a): the
// interval of values holds f(b) and f(a) alike, so it holds every value
// between them whichever end is the larger.
var IntermediateValueDecreasing = intermediateValueDecreasingThm{family.Add(registry.ProofEntry{
	Name: "IntermediateValueDecreasing",
	Key:  "prop_d3d4dc005ea4fabf",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀a b y:real.",
		Hypotheses: []string{
			"a ≤ b",
			"real_continuous_on(⟦a, b⟧, f)",
			"f(b) ≤ y",
			"y ≤ f(a)",
		},
		Conclusion: "∃x:real. a ≤ x ∧ x ≤ b ∧ f(x) = y",
	},
		func(arg *Argument, f *Arrow[Real, Real], a, b, y *Expr[Real], given Fact) {
			parts := arg.Conjuncts(
				given,
				"a ≤ b",
				"f is continuous on ⟦a, b⟧",
				"f(b) ≤ y",
				"y ≤ f(a)")
			values := arg.Conjuncts(
				arg.Have(
					"the values on ⟦a, b⟧ form an interval holding f(a) and f(b)",
					"real_interval(image(f, ⟦a, b⟧)) ∧ f(a) ∈ image(f, ⟦a, b⟧) ∧ f(b) ∈ image(f, ⟦a, b⟧)",
					By(ValuesInterval.At(f, a, b), parts[0], parts[1])),
				"the values form an interval",
				"f(a) is a value",
				"f(b) is a value")
			between := arg.Unfolded(values[0], real_topology.RealIntervalDef)
			yIn := arg.Have(
				"y lies between f(b) and f(a), so it is a value",
				"y ∈ image(f, ⟦a, b⟧)",
				By(between.At(f.Apply(b), y, f.Apply(a)), values[2], values[1], parts[2], parts[3]))
			x, attained := arg.ObtainAs[Real](
				"the value y is taken at a point x of ⟦a, b⟧",
				"∃x:real. y = f(x) ∧ x ∈ ⟦a, b⟧",
				By(set_basic.InImage.At(f, arg.TermAs[Set[Real]]("⟦a, b⟧"), y), yIn))
			arg.Take(x)
			arg.Show(
				"x lies between a and b, and f(x) = y",
				BySets(attained))
		}),
})}

// ---------------------------------------------------------------------------
// A continuous injective function is strictly monotone: the ordered-field law at ℝ
// ---------------------------------------------------------------------------

// ContinuousInjectiveMonotone — a function continuous and injective on an interval of ℝ is strictly
// increasing or strictly decreasing there: it is the instance at ℝ of the ordered-field law
// ordered_field.IntermediateValueInjectiveMonotone. Between two points a < b of the interval, f is
// continuous on ⟦a, b⟧, so it takes every value y strictly between f(a) and f(b) at a point of
// ⟦a, b⟧ (IntermediateValue where the end values rise, IntermediateValueDecreasing where they
// fall), and that point is neither end, where f takes f(a) and f(b) instead of y. The law asks
// nothing more of ℝ, whose carrier is the whole line.
var ContinuousInjectiveMonotone = continuousInjectiveMonotoneThm{family.Add(registry.ProofEntry{
	Name: "ContinuousInjectiveMonotone",
	Key:  "prop_1e65327476a03130",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀s:set(real).",
		Hypotheses: []string{
			"real_interval(s)",
			"real_continuous_on(s, f)",
			"injective_on(s, f)",
		},
		Conclusion: "real_strictly_increasing_on(s, f) ∨ real_strictly_decreasing_on(s, f)",
	}, func(
		arg *Argument,
		f *Arrow[Real, Real],
		s *Expr[Set[Real]],
		interval, continuous, injective Fact,
	) {
		between := arg.Unfolded(interval, real_topology.RealIntervalDef)
		intermediate := arg.Have(
			"f takes, strictly between two points a < b of s, every value strictly between f(a) and f(b)",
			Statement{
				Binders: "∀a b y:real.",
				Hypotheses: []string{
					"a ∈ s",
					"b ∈ s",
					"a < b",
					"f(a) < y ∧ y < f(b) ∨ f(b) < y ∧ y < f(a)",
				},
				Conclusion: "∃x:real. x ∈ s ∧ a < x ∧ x < b ∧ f(x) = y",
			},
			Derive(func(d *Argument) {
				a := d.FixAs[Real]("a")
				b := d.FixAs[Real]("b")
				y := d.FixAs[Real]("y")
				given := d.Conjuncts(
					d.Assume(),
					"a lies in s",
					"b lies in s",
					"a lies below b",
					"y lies strictly between f(a) and f(b)")
				onSegment := d.Have(
					"f is continuous on ⟦a, b⟧, which the interval s contains",
					"real_continuous_on(⟦a, b⟧, f)",
					By(
						continuous,
						ContinuousOnSubset.At(f, s, d.TermAs[Set[Real]]("⟦a, b⟧")),
						d.Have(
							"⟦a, b⟧ lies in s",
							"⟦a, b⟧ ⊆ s",
							BySets(given[0], given[1], between))))
				x, attained := d.ObtainAs[Real](
					"the intermediate value theorem gives y at a point x of ⟦a, b⟧",
					"∃x:real. a ≤ x ∧ x ≤ b ∧ f(x) = y",
					given[3].SplitDisj(
						LeftHolds(
							"f(a) < y < f(b): the end values rise",
							Given(func(e *Argument, rising Fact) {
								e.Show(
									"so f takes y on ⟦a, b⟧, by the intermediate value theorem",
									By(given[2], rising, onSegment, IntermediateValue.At(f, a, b, y), real_order_ring.LessEqOfLessThan))
							})),
						RightHolds(
							"f(b) < y < f(a): the end values fall",
							Given(func(e *Argument, falling Fact) {
								e.Show(
									"so f takes y on ⟦a, b⟧, by its form for falling end values",
									By(
										given[2],
										falling,
										onSegment,
										IntermediateValueDecreasing.At(f, a, b, y),
										real_order_ring.LessEqOfLessThan))
							}))))
				d.Take(x)
				d.Show(
					"x lies in the interval s, and is neither end, where f takes f(a) and f(b) instead of y",
					By(
						attained,
						given[0],
						given[1],
						given[3],
						between.At(a, x, b),
						real_order_ring.LessEqSplit.At(a, x),
						real_order_ring.LessEqSplit.At(x, b),
						real_order_ring.LessThanIrrefl.At(y)))
			}))
		monotone := arg.Have(
			"f is injective on s and takes its intermediate values there, "+
				"so the ordered-field law at ℝ makes it strictly monotone",
			"(∀x y:real. x ∈ s ∧ y ∈ s ∧ x < y ⇒ f(x) < f(y)) ∨ "+
				"(∀x y:real. x ∈ s ∧ y ∈ s ∧ x < y ⇒ f(y) < f(x))",
			By(
				ordered_field.IntermediateValueInjectiveMonotone.Read(real_ordered_instance.RealOrderedField).At(
					f, s),
				set_order.SubsetUniv.At(s),
				set_basic.InUniv,
				injective,
				intermediate))
		arg.Show(
			"that is, f is strictly increasing or strictly decreasing on s",
			Simp(Fwd(RealStrictlyIncreasingOnDef), Fwd(RealStrictlyDecreasingOnDef)),
			By(monotone))
	}),
})}

// ---------------------------------------------------------------------------
// The extreme value theorem
// ---------------------------------------------------------------------------

// ValuesCompact — the values of a function continuous on ⟦a, b⟧ form a
// non-empty compact set: ⟦a, b⟧ is compact, continuity carries
// compactness, and f(a) is a value. Both forms of the extreme value
// theorem read it.
var ValuesCompact = valuesCompactThm{family.Add(registry.ProofEntry{
	Name: "ValuesCompact",
	Key:  "prop_76d74d0fb174526d",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀a b:real.",
		Hypotheses: []string{
			"a ≤ b",
			"real_continuous_on(⟦a, b⟧, f)",
		},
		Conclusion: "compact_in(image(f, ⟦a, b⟧)) ∧ image(f, ⟦a, b⟧) ≠ ∅",
	},
		func(arg *Argument, f *Arrow[Real, Real], a, b *Expr[Real], given Fact) {
			parts := arg.Conjuncts(
				given,
				"a ≤ b",
				"f is continuous on ⟦a, b⟧")
			segmentSet := arg.TermAs[Set[Real]]("⟦a, b⟧")
			compact := arg.Have(
				"the values on ⟦a, b⟧ form a compact set, ⟦a, b⟧ being compact",
				"compact_in(«values»)",
				By(
					ContinuousImageCompact.At(f, segmentSet),
					parts[1],
					real_topology.ClosedIntervalCompact.At(a, b)))
			aIn := arg.Have(
				"a lies in ⟦a, b⟧",
				"a ∈ ⟦a, b⟧",
				BySets(real_order_ring.LessEqRefl.At(a), parts[0]))
			faValue := arg.Have(
				"so f(a) is a value",
				"f(a) ∈ «values»",
				By(set_image.FunInImage.At(f, segmentSet, a), aIn))
			nonEmpty := arg.Have(
				"and there are values",
				"«values» ≠ ∅",
				// Pinned at the reals: Go's Simp does not adapt a rule's type
				// letter. The set closer alone would hunt a witness inside the
				// image; f(a) is named.
				Simp(Rev(set_basic.MemberNotEmpty.Inst[Real]())),
				Derive(func(c *Argument) {
					c.Take(f.Apply(a))
					c.Show(
						"f(a) is one",
						By(faValue))
				}))
			arg.Show(
				"a non-empty compact set of values",
				By(compact, nonEmpty))
		}),
})}

// ExtremeValueMax — a function continuous on ⟦a, b⟧ takes a greatest
// value there: its values form a non-empty compact set, which holds its
// supremum — the value at some point x of ⟦a, b⟧, and at least every
// other value.
var ExtremeValueMax = extremeValueMaxThm{family.Add(registry.ProofEntry{
	Name: "ExtremeValueMax",
	Key:  "prop_8abff0d083573f39",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀a b:real.",
		Hypotheses: []string{
			"a ≤ b",
			"real_continuous_on(⟦a, b⟧, f)",
		},
		Conclusion: "∃x:real. a ≤ x ∧ x ≤ b ∧ (∀y:real. a ≤ y ∧ y ≤ b ⇒ f(y) ≤ f(x))",
	},
		func(arg *Argument, f *Arrow[Real, Real], a, b *Expr[Real], given Fact) {
			parts := arg.Conjuncts(
				given,
				"a ≤ b",
				"f is continuous on ⟦a, b⟧")
			segmentSet := arg.TermAs[Set[Real]]("⟦a, b⟧")
			valuesHeld := arg.Conjuncts(
				arg.Have(
					"the values on ⟦a, b⟧ form a non-empty compact set",
					"compact_in(«values») ∧ «values» ≠ ∅",
					By(ValuesCompact.At(f, a, b), parts[0], parts[1])),
				"the values form a compact set",
				"and there are values")
			compact, nonEmpty := valuesHeld[0], valuesHeld[1]
			greatest := arg.Conjuncts(
				arg.Have(
					"a non-empty compact set holds its supremum, its greatest element",
					"sup(«values») ∈ «values» ∧ (∀z:real. z ∈ «values» ⇒ z ≤ sup(«values»))",
					By(real_topology.SupCompactAttained.At(arg.TermAs[Set[Real]]("«values»")), compact, nonEmpty)),
				"the supremum is a value",
				"every value is at most the supremum")
			x, attained := arg.ObtainAs[Real](
				"the supremum is the value at a point x of ⟦a, b⟧",
				"∃x:real. sup(«values») = f(x) ∧ x ∈ ⟦a, b⟧",
				By(set_basic.InImage.At(f, segmentSet, arg.TermAs[Real]("sup(«values»)")), greatest[0]))
			at := arg.Conjuncts(
				attained,
				"the supremum is f(x)",
				"x lies in ⟦a, b⟧")
			arg.Take(x)
			arg.Do(SplitConj(
				Case(
					"x lies between a and b",
					BySets(at[1])),
				Case(
					"and no value on ⟦a, b⟧ exceeds f(x)",
					Derive(func(c *Argument) {
						y := c.FixAs[Real]()
						between := c.Assume()
						yIn := c.Have(
							"y lies in ⟦a, b⟧",
							"y ∈ ⟦a, b⟧",
							BySets(between))
						value := c.Have(
							"so f(y) is a value",
							"f(y) ∈ «values»",
							By(set_image.FunInImage.At(f, segmentSet, y), yIn))
						capped := c.Have(
							"f(y) is at most the supremum",
							"f(y) ≤ sup(«values»)",
							By(greatest[1].At(f.Apply(y)), value))
						c.Show(
							"at most the supremum, which is f(x)",
							ByArith(capped, at[0]))
					})),
			))
		}),
})}

// ExtremeValueMin — a function continuous on ⟦a, b⟧ takes a least value
// there: ExtremeValueMax's mirror, the values' infimum in place of their
// supremum.
var ExtremeValueMin = extremeValueMinThm{family.Add(registry.ProofEntry{
	Name: "ExtremeValueMin",
	Key:  "prop_7f92b2b830451bc2",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀a b:real.",
		Hypotheses: []string{
			"a ≤ b",
			"real_continuous_on(⟦a, b⟧, f)",
		},
		Conclusion: "∃x:real. a ≤ x ∧ x ≤ b ∧ (∀y:real. a ≤ y ∧ y ≤ b ⇒ f(x) ≤ f(y))",
	},
		func(arg *Argument, f *Arrow[Real, Real], a, b *Expr[Real], given Fact) {
			parts := arg.Conjuncts(
				given,
				"a ≤ b",
				"f is continuous on ⟦a, b⟧")
			segmentSet := arg.TermAs[Set[Real]]("⟦a, b⟧")
			valuesHeld := arg.Conjuncts(
				arg.Have(
					"the values on ⟦a, b⟧ form a non-empty compact set",
					"compact_in(«values») ∧ «values» ≠ ∅",
					By(ValuesCompact.At(f, a, b), parts[0], parts[1])),
				"the values form a compact set",
				"and there are values")
			compact, nonEmpty := valuesHeld[0], valuesHeld[1]
			least := arg.Conjuncts(
				arg.Have(
					"a non-empty compact set holds its infimum, its least element",
					"inf(«values») ∈ «values» ∧ (∀z:real. z ∈ «values» ⇒ inf(«values») ≤ z)",
					By(real_topology.InfCompactAttained.At(arg.TermAs[Set[Real]]("«values»")), compact, nonEmpty)),
				"the infimum is a value",
				"every value is at least the infimum")
			x, attained := arg.ObtainAs[Real](
				"the infimum is the value at a point x of ⟦a, b⟧",
				"∃x:real. inf(«values») = f(x) ∧ x ∈ ⟦a, b⟧",
				By(set_basic.InImage.At(f, segmentSet, arg.TermAs[Real]("inf(«values»)")), least[0]))
			at := arg.Conjuncts(
				attained,
				"the infimum is f(x)",
				"x lies in ⟦a, b⟧")
			arg.Take(x)
			arg.Do(SplitConj(
				Case(
					"x lies between a and b",
					BySets(at[1])),
				Case(
					"and no value on ⟦a, b⟧ falls below f(x)",
					Derive(func(c *Argument) {
						y := c.FixAs[Real]()
						between := c.Assume()
						yIn := c.Have(
							"y lies in ⟦a, b⟧",
							"y ∈ ⟦a, b⟧",
							BySets(between))
						value := c.Have(
							"so f(y) is a value",
							"f(y) ∈ «values»",
							By(set_image.FunInImage.At(f, segmentSet, y), yIn))
						floored := c.Have(
							"f(y) is at least the infimum",
							"inf(«values») ≤ f(y)",
							By(least[1].At(f.Apply(y)), value))
						c.Show(
							"at least the infimum, which is f(x)",
							ByArith(floored, at[0]))
					})),
			))
		}),
})}
