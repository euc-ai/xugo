// chords.go — convexity read through the slopes of chords: the
// three-chord lemma, and its converse.

package real_convex

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/registry"
)

// ConvexChordSlopes — the three-chord lemma: for x < y < z with x and z
// in a set where f is convex, the chord from x to y is no steeper than
// the chord from x to z, and that one no steeper than the chord from y
// to z. The point y is z weighted by t = (y − x)/(z − x) and x by 1 − t,
// so convexity puts f(y) below the chord from x to z; each slope
// inequality is that bound with its positive denominator cleared.
var ConvexChordSlopes = convexChordSlopesThm{family.Add(registry.ProofEntry{
	Name: "ConvexChordSlopes",
	Key:  "prop_6b4d5091a1485a7d",
	Build: family.Theorem(Statement{
		Binders: "∀f:real → real. ∀s:set(real). ∀x y z:real.",
		Hypotheses: []string{
			"real_convex_on(s, f)",
			"x ∈ s",
			"z ∈ s",
			"x < y",
			"y < z",
		},
		Conclusion: "(f(y) - f(x)) / (y - x) ≤ (f(z) - f(x)) / (z - x) ∧ " +
			"(f(z) - f(x)) / (z - x) ≤ (f(z) - f(y)) / (z - y)",
	}, func(a *Argument, f *Arrow[Real, Real], s *Expr[Set[Real]], x, y, z *Expr[Real],
		convex, xIn, zIn, xy, yz Fact) {
		chord := a.Unfolded(convex, RealConvexOnDef)
		t := a.TermAs[Real]("(y - x) / (z - x)")
		weight := a.Have(
			"the weight t lies in ⟦0, 1⟧, since 0 < y − x < z − x",
			"&0 ≤ (y - x) / (z - x) ∧ (y - x) / (z - x) ≤ &1",
			ByArith(
				xy,
				yz,
				real_order_field.LessEqDivMulLeft.At(
					a.TermAs[Real]("&0"), a.TermAs[Real]("y - x"), a.TermAs[Real]("z - x")),
				real_order_field.LessEqDivMulRight.At(
					a.TermAs[Real]("y - x"), a.TermAs[Real]("&1"), a.TermAs[Real]("z - x"))),
		)
		point := a.Have(
			"y is z weighted by t and x by 1 − t",
			"(y - x) / (z - x) * z + (&1 - (y - x) / (z - x)) * x = y",
			ByArith(xy, yz),
		)
		below := a.Have(
			"convexity puts f(y) below the chord from x to z",
			"f(y) ≤ (y - x) / (z - x) * f(z) + (&1 - (y - x) / (z - x)) * f(x)",
			By(chord.At(z, x, t), zIn, xIn, weight, point),
		)
		a.Show(
			"the bound, divided by y − x and compared with the chord from y to z",
			ByArith(
				below,
				xy,
				yz,
				real_order_field.LessEqDivMulRight.At(
					a.TermAs[Real]("f(y) - f(x)"), a.TermAs[Real]("(f(z) - f(x)) / (z - x)"), a.TermAs[Real]("y - x")),
				real_order_field.LessEqDivMulLeft.At(
					a.TermAs[Real]("(f(z) - f(x)) / (z - x)"), a.TermAs[Real]("f(z) - f(y)"), a.TermAs[Real]("z - y"))),
		)
	}),
})}

// ConvexIffChordSlopes — a function is convex on a set exactly when, for
// x < y < z with x and z in the set, the chord from x to y is no steeper
// than the chord from y to z. Forward, it is the three-chord lemma. Back,
// clearing the two positive denominators turns the slope inequality into
// the chord bound (z − x)·f(y) ≤ (z − y)·f(x) + (y − x)·f(z), which holds
// with y at either end as well; read at the ends of the segment from x to
// y and its point t·x + (1 − t)·y, and divided by its length, it is
// convexity.
var ConvexIffChordSlopes = convexIffChordSlopesThm{family.Add(registry.ProofEntry{
	Name: "ConvexIffChordSlopes",
	Key:  "prop_722860b7fb300c82",
	Build: family.Theorem(
		"∀f:real → real. ∀s:set(real). "+
			"    real_convex_on(s, f) ⇔ "+
			"    (∀x y z:real. "+
			"        x ∈ s ∧ z ∈ s ∧ x < y ∧ y < z ⇒ (f(y) - f(x)) / (y - x) ≤ (f(z) - f(y)) / (z - y))",
		func(a *Argument, f *Arrow[Real, Real], s *Expr[Set[Real]]) {
			a.Iff()
			a.Forward(
				"the three-chord lemma, its outer two slopes compared",
				func(b *Argument, convex Fact) {
					x := b.FixAs[Real]()
					y := b.FixAs[Real]()
					z := b.FixAs[Real]()
					points := b.Assume()
					b.Show(
						"the slope from x to y is at most that from x to z, which is at most that from y to z",
						ByArith(ConvexChordSlopes.At(f, s, x, y, z), convex, points),
					)
				})
			a.Backward(
				"slopes that increase put the graph below every chord",
				func(b *Argument, slopes Fact) {
					chord := b.Have(
						"between two points of s, the graph lies below the chord",
						"∀x y z:real. x ∈ s ∧ z ∈ s ∧ x ≤ y ∧ y ≤ z ⇒ (z - x) * f(y) ≤ (z - y) * f(x) + (y - x) * f(z)",
						Derive(func(c *Argument) {
							x := c.FixAs[Real]()
							y := c.FixAs[Real]()
							z := c.FixAs[Real]()
							given := c.Conjuncts(
								c.Assume(),
								"x lies in s",
								"z lies in s",
								"x ≤ y",
								"y ≤ z")
							xy := c.Assuming(
								c.Term("x < y"),
								"at y = x both sides are (z − x)·f(x)",
								Given(func(d *Argument, notLess Fact) {
									same := d.Have(
										"y is x",
										"x = y",
										ByArith(notLess, given[2]))
									d.Show(
										"the chord bound at its left end",
										same.Rw(),
										ByArith())
								}))
							yz := c.Assuming(
								c.Term("y < z"),
								"at y = z both sides are (z − x)·f(z)",
								Given(func(d *Argument, notLess Fact) {
									same := d.Have(
										"y is z",
										"y = z",
										ByArith(notLess, given[3]))
									d.Show(
										"the chord bound at its right end",
										same.Rw(),
										ByArith())
								}))
							partly := c.Have(
								"the slopes compared at x < y < z, with y − x cleared",
								"f(y) - f(x) ≤ (f(z) - f(y)) / (z - y) * (y - x)",
								ByArith(
									slopes.At(x, y, z),
									given[0],
									given[1],
									xy,
									yz,
									real_order_field.LessEqDivMulRight.At(
										c.TermAs[Real]("f(y) - f(x)"), c.TermAs[Real]("(f(z) - f(y)) / (z - y)"), c.TermAs[Real]("y - x"))),
							)
							c.Show(
								"with z − y cleared as well, the slope inequality is the chord bound",
								ByArith(
									partly,
									yz,
									real_order_field.LessEqDivMulLeft.At(
										c.TermAs[Real]("f(y) - f(x)"), c.TermAs[Real]("(f(z) - f(y)) * (y - x)"), c.TermAs[Real]("z - y"))),
							)
						}),
					)
					b.Do(Unfold(RealConvexOnDef))
					x := b.FixAs[Real]()
					y := b.FixAs[Real]()
					b.FixAs[Real]("t")
					given := b.Conjuncts(
						b.Assume(),
						"x lies in s",
						"y lies in s",
						"t is nonnegative",
						"t is at most 1")
					point := b.TermAs[Real]("t * x + (&1 - t) * y")
					b.Cases(b.Term("x < y"))
					b.When(
						"x < y: the point lies on the segment from x to y",
						func(c *Argument, xy Fact) {
							weak := c.Have(
								"x is at most y",
								"x ≤ y",
								ByArith(xy))
							between := c.Have(
								"the point lies between x and y",
								"x ≤ t * x + (&1 - t) * y ∧ t * x + (&1 - t) * y ≤ y",
								ByArith(weak, given[2], given[3]),
							)
							c.Show(
								"the chord bound at the point, divided by y − x",
								ByArith(chord.At(x, point, y), given[0], given[1], between, xy),
							)
						})
					b.Otherwise(
						"y ≤ x: the point lies on the segment from y to x",
						func(c *Argument, notLess Fact) {
							distinct := c.Unless(
								c.Term("x = y"),
								"x = y: the point is x itself",
								Given(func(d *Argument, same Fact) {
									d.Do(same.Rw())
									collapse := d.Have(
										"the point is y",
										"t * y + (&1 - t) * y = y",
										ByArith())
									d.Show(
										"f at the point is f(y), and so is the right side",
										ByArith(collapse))
								}))
							yx := c.Have(
								"y lies strictly below x",
								"y < x",
								ByArith(notLess, distinct))
							between := c.Have(
								"the point lies between y and x",
								"y ≤ t * x + (&1 - t) * y ∧ t * x + (&1 - t) * y ≤ x",
								ByArith(notLess, given[2], given[3]),
							)
							c.Show(
								"the chord bound at the point, divided by x − y",
								ByArith(chord.At(y, point, x), given[1], given[0], between, yx),
							)
						})
				})
		}),
})}
