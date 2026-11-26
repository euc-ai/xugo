// refinement.go — a sign table refined by one more polynomial: on an
// interval where its derivative keeps one sign, a polynomial over a real
// closed field vanishes at most once, and the point where it may vanish
// splits the interval into parts of known sign.

package parametric_sign_table

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/ordered_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/polynomial_sign_table"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/real_closed_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_parity"
	"github.com/euc-ai/xugo/library/registry"
)

// GapSplit — let p be a polynomial over a real closed field whose derivative
// has one sign σ ≠ 0 on a convex set S, every point of which lies inside an
// interval within S whose ends give p the signs L and R. Then some point z
// of S splits it: p has the sign L below z (R when L = 0) and the sign R
// above z (L when R = 0), and at z it vanishes when L and R are opposite and
// nonzero, keeping the sign below z otherwise. Across any interval inside S
// p changes by the sign σ, so a root of p in S has L = −σ and R = σ, two
// roots are one, and away from a root the sign of p is an end sign. S is a
// convex set rather than an interval with two ends in F because
// MonotoneRefinement splits every open cell, the two rays among them: a ray
// has no end in F, and p takes its far sign only beyond a point chosen for
// each x, so each point of S need only lie in some interval inside S whose
// ends give p the signs L and R.
var GapSplit = gapSplitThm{family.Add(registry.ProofEntry{
	Name: "GapSplit",
	Key:  "prop_8761f91cf7eca526",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). ∀lt:(A → A → bool). ∀p:(num → A). ∀S:set(A). ∀σ L R:int.",
		Hypotheses: []string{
			"real_closed_field(F, lt)",
			"polynomial_over(F.carrier, p)",
			"S ⊆ F.carrier",
			"S ≠ ∅",
			"∀x y z:A. x ∈ S ∧ y ∈ S ∧ z ∈ F.carrier ∧ lt(x, z) ∧ lt(z, y) ⇒ z ∈ S",
			"¬(σ = &0)",
			"∀x:A. x ∈ S ⇒ ordered_sign(F, lt, polynomial_eval(polynomial_derivative(p), x)) = σ",
			"∀x:A. " +
				"    x ∈ S ⇒ " +
				"    ∃a b:A. " +
				"        a ∈ F.carrier ∧ " +
				"        b ∈ F.carrier ∧ " +
				"        lt(a, x) ∧ " +
				"        lt(x, b) ∧ " +
				"        (∀y:A. y ∈ F.carrier ∧ lt(a, y) ∧ lt(y, b) ⇒ y ∈ S) ∧ " +
				"        ordered_sign(F, lt, polynomial_eval(p, a)) = L ∧ " +
				"        ordered_sign(F, lt, polynomial_eval(p, b)) = R",
		},
		Conclusion: "∃z:A. " +
			"    z ∈ S ∧ " +
			"    ordered_sign(F, lt, polynomial_eval(p, z)) = «split»(L, R) ∧ " +
			"    (∀x:A. x ∈ S ∧ lt(x, z) ⇒ ordered_sign(F, lt, polynomial_eval(p, x)) = «below»(L, R)) ∧ " +
			"    (∀x:A. x ∈ S ∧ lt(z, x) ⇒ ordered_sign(F, lt, polynomial_eval(p, x)) = «above»(L, R))",
	}, func(
		a *Argument,
		F *Expr[FieldOps[A]],
		lt *Arrow2[A, A, Bool],
		p *Arrow[Nat, A],
		S *Expr[Set[A]],
		σ, L, R *Expr[Int],
		closed, poly, within, inhabited, convex, nonzeroSlope, slope, ends Fact,
	) {
		ordered := real_closed_field.OrderedFieldOn.Read(closed)
		ring := field.RingOn.Read(ordered_field.FieldOn.Read(ordered))
		transitive := ordered_field.Transitive.Read(ordered).AsFact()
		comparable := ordered_field.Trichotomy.Read(ordered).AsFact()
		signValues := ordered_field.SignValues.Read(ordered).AsFact()
		values := a.Have(
			"p takes its values in F",
			"∀x:A. x ∈ F.carrier ⇒ polynomial_eval(p, x) ∈ F.carrier",
			By(poly, polynomial_evaluation.EvalIn.Read(ring)))
		unchanged := a.Have(
			"subtracting zero keeps the sign",
			"∀y:A. y ∈ F.carrier ⇒ ordered_sign(F, lt, y - F.zero) = ordered_sign(F, lt, y)",
			Derive(func(b *Argument) {
				y := b.FixAs[A]("y")
				ym := b.MemberOf[on.Any](y, b.Assume())
				b.Show(
					"y − 0 = y",
					By(
						Normalized,
						b.Have(
							"y − 0 = y",
							"y - F.zero = y",
							ByArith(ring, ym))))
			}))
		monotone := a.Have(
			"across every interval inside S, p changes by the sign σ",
			Statement{
				Binders: "∀u v:A.",
				Hypotheses: []string{
					"u ∈ F.carrier",
					"v ∈ F.carrier",
					"lt(u, v)",
					"∀y:A. y ∈ F.carrier ∧ lt(u, y) ∧ lt(y, v) ⇒ y ∈ S",
				},
				Conclusion: "ordered_sign(F, lt, polynomial_eval(p, v) - polynomial_eval(p, u)) = σ",
			},
			Derive(func(b *Argument) {
				u := b.FixAs[A]("u")
				v := b.FixAs[A]("v")
				given := b.Conjuncts(
					b.Assume(),
					"u lies in F",
					"v lies in F",
					"u lies below v",
					"the interval between u and v lies in S")
				between := b.Have(
					"the derivative has the sign σ strictly between u and v",
					Statement{
						Binders: "∀z:A.",
						Hypotheses: []string{
							"z ∈ F.carrier",
							"lt(u, z)",
							"lt(z, v)",
						},
						Conclusion: "ordered_sign(F, lt, polynomial_eval(polynomial_derivative(p), z)) = σ",
					},
					By(given[3], slope))
				b.Show(
					"by the mean value theorem",
					By(
						real_closed_field.DerivativeSignMonotone.Read(closed).AsFact().At(p, u, v, σ),
						poly,
						given[0],
						given[1],
						given[2],
						between))
			}))
		zero := a.MemberOf[on.Any](a.TermAs[A]("F.zero"), comm_ring.ZeroIn.Read(ring))
		flat := a.Have(
			"zero minus zero has the sign zero",
			"ordered_sign(F, lt, F.zero - F.zero) = &0",
			By(
				Normalized,
				a.Have(
					"0 − 0 = 0",
					"F.zero - F.zero = F.zero",
					ByArith(ring, zero)),
				zero,
				signValues.At(zero)))
		roots := a.Have(
			"a root of p in S forces L = −σ and R = σ",
			"∀x:A. x ∈ S ∧ polynomial_eval(p, x) = F.zero ⇒ L = -σ ∧ R = σ",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				given := b.Conjuncts(
					b.Assume(),
					"x lies in S",
					"p vanishes at x")
				xIn := b.Have(
					"x lies in F",
					"x ∈ F.carrier",
					BySets(given[0], within))
				aPoint, bPoint, around := b.Unpack2As[A, A](GroupPremises(given[0], ends.At(x)), "a", "b")
				end := b.Conjuncts(
					around,
					"a lies in F",
					"b lies in F",
					"a lies below x",
					"x lies below b",
					"the interval between a and b lies in S",
					"p has the sign L at a",
					"p has the sign R at b")
				leftPart := b.Have(
					"the interval between a and x lies in S",
					"∀y:A. y ∈ F.carrier ∧ lt(a, y) ∧ lt(y, x) ⇒ y ∈ S",
					By(end[4], end[3], transitive, xIn, end[1]))
				rightPart := b.Have(
					"the interval between x and b lies in S",
					"∀y:A. y ∈ F.carrier ∧ lt(x, y) ∧ lt(y, b) ⇒ y ∈ S",
					By(end[4], end[2], transitive, xIn, end[0]))
				rise := b.Have(
					"from a to the root x, p changes by the sign σ",
					"ordered_sign(F, lt, F.zero - polynomial_eval(p, a)) = σ",
					By(monotone.At(aPoint, x), end[0], xIn, end[2], leftPart, given[1]))
				fall := b.Have(
					"and from the root x to b",
					"ordered_sign(F, lt, polynomial_eval(p, b) - F.zero) = σ",
					By(monotone.At(x, bPoint), xIn, end[1], end[3], rightPart, given[1]))
				pa := b.MemberOf[on.Any](
					b.TermAs[A]("polynomial_eval(p, a)"), GroupPremises(end[0], values.At(aPoint)))
				negated := b.Have(
					"0 − p(a) = −p(a)",
					"F.zero - polynomial_eval(p, a) = -polynomial_eval(p, a)",
					ByArith(ring, pa))
				endSigns := b.Have(
					"so −L = σ and R = σ",
					"-L = σ ∧ R = σ",
					By(
						rise,
						fall,
						negated,
						ordered_field.SignNeg.Read(ordered).At(pa),
						unchanged.At(b.TermAs[A]("polynomial_eval(p, b)")),
						values.At(aPoint),
						values.At(bPoint),
						end[0],
						end[1],
						end[5],
						end[6]))
				b.Show(
					"L = −σ and R = σ",
					ByArith(endSigns))
			}))
		unique := a.Have(
			"p vanishes at most once in S",
			"∀x y:A. x ∈ S ∧ y ∈ S ∧ polynomial_eval(p, x) = F.zero ∧ polynomial_eval(p, y) = F.zero ⇒ x = y",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				y := b.FixAs[A]("y")
				given := b.Conjuncts(
					b.Assume(),
					"x lies in S",
					"y lies in S",
					"p vanishes at x",
					"p vanishes at y")
				xIn := b.Have(
					"x lies in F",
					"x ∈ F.carrier",
					BySets(given[0], within))
				yIn := b.Have(
					"y lies in F",
					"y ∈ F.carrier",
					BySets(given[1], within))
				b.Cases(b.TermAs[Bool]("lt(x, y)"))
				b.When(
					"x below y: p would change by the sign σ ≠ 0 between two zeros",
					func(c *Argument, xy Fact) {
						between := c.Have(
							"the interval between x and y lies in S",
							"∀z:A. z ∈ F.carrier ∧ lt(x, z) ∧ lt(z, y) ⇒ z ∈ S",
							By(convex, given[0], given[1]))
						c.Show(
							"σ would be the sign of zero",
							By(monotone.At(x, y), xIn, yIn, xy, between, given[2], given[3], flat, nonzeroSlope))
					})
				b.Otherwise(
					"x not below y",
					func(c *Argument, notXY Fact) {
						c.Cases(c.TermAs[Bool]("lt(y, x)"))
						c.When(
							"y below x: likewise",
							func(d *Argument, yx Fact) {
								between := d.Have(
									"the interval between y and x lies in S",
									"∀z:A. z ∈ F.carrier ∧ lt(y, z) ∧ lt(z, x) ⇒ z ∈ S",
									By(convex, given[0], given[1]))
								d.Show(
									"σ would be the sign of zero",
									By(monotone.At(y, x), xIn, yIn, yx, between, given[2], given[3], flat, nonzeroSlope))
							})
						c.Otherwise(
							"neither below the other",
							func(d *Argument, notYX Fact) {
								d.Show(
									"comparability makes them one point",
									By(notXY, notYX, comparable.At(x, y), xIn, yIn))
							})
					})
			}))
		belowSign := a.Have(
			"a point of S with no root of p at or below it in S has the sign L, when L is not zero",
			Statement{
				Binders: "∀x:A.",
				Hypotheses: []string{
					"x ∈ S",
					"¬(L = &0)",
					"∀y:A. y ∈ S ∧ ordered_le(lt, y, x) ⇒ polynomial_eval(p, y) ≠ F.zero",
				},
				Conclusion: "ordered_sign(F, lt, polynomial_eval(p, x)) = L",
			},
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				given := b.Conjuncts(
					b.Assume(),
					"x lies in S",
					"L is not zero",
					"p has no root in S at or below x")
				xIn := b.Have(
					"x lies in F",
					"x ∈ F.carrier",
					BySets(given[0], within))
				aPoint, bPoint, around := b.Unpack2As[A, A](GroupPremises(given[0], ends.At(x)), "a", "b")
				end := b.Conjuncts(
					around,
					"a lies in F",
					"b lies in F",
					"a lies below x",
					"x lies below b",
					"the interval between a and b lies in S",
					"p has the sign L at a",
					"p has the sign R at b")
				rootFree := b.Have(
					"p has no root from a to x",
					Statement{
						Binders: "∀y:A.",
						Hypotheses: []string{
							"y ∈ F.carrier",
							"ordered_le(lt, a, y)",
							"ordered_le(lt, y, x)",
						},
						Conclusion: "polynomial_eval(p, y) ≠ F.zero",
					},
					Derive(func(c *Argument) {
						y := c.FixAs[A]("y")
						point := c.Conjuncts(
							c.Assume(),
							"y lies in F",
							"a is at or below y",
							"y is at or below x")
						c.Cases(c.TermAs[Bool]("y = a"))
						c.When(
							"at a, p has the nonzero sign L",
							func(d *Argument, atA Fact) {
								d.Show(
									"so p does not vanish at a",
									By(
										atA,
										end[5],
										given[1],
										signValues.At(d.TermAs[A]("polynomial_eval(p, a)")),
										values.At(aPoint),
										end[0]))
							})
						c.Otherwise(
							"past a, y lies in S at or below x",
							func(d *Argument, pastA Fact) {
								yS := d.Have(
									"y lies between a and b, so in S",
									"y ∈ S",
									By(
										end[4].At(y),
										point[0],
										point[1],
										point[2],
										pastA,
										ordered_field.OrderedLeDef.At(lt, aPoint, y),
										ordered_field.OrderedLeDef.At(lt, y, x),
										transitive.At(y, x, bPoint),
										xIn,
										end[1],
										end[3]))
								d.Show(
									"and p has no root there",
									By(given[2].At(y), yS, point[2]))
							})
					}))
				b.Show(
					"p has one sign from a to x",
					By(
						real_closed_field.RootFreeIntervalSign.Read(closed).AsFact().At(p, aPoint, x),
						poly,
						end[0],
						xIn,
						end[2],
						rootFree,
						end[5]))
			}))
		aboveSign := a.Have(
			"a point of S with no root of p at or above it in S has the sign R, when R is not zero",
			Statement{
				Binders: "∀x:A.",
				Hypotheses: []string{
					"x ∈ S",
					"¬(R = &0)",
					"∀y:A. y ∈ S ∧ ordered_le(lt, x, y) ⇒ polynomial_eval(p, y) ≠ F.zero",
				},
				Conclusion: "ordered_sign(F, lt, polynomial_eval(p, x)) = R",
			},
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				given := b.Conjuncts(
					b.Assume(),
					"x lies in S",
					"R is not zero",
					"p has no root in S at or above x")
				xIn := b.Have(
					"x lies in F",
					"x ∈ F.carrier",
					BySets(given[0], within))
				aPoint, bPoint, around := b.Unpack2As[A, A](GroupPremises(given[0], ends.At(x)), "a", "b")
				end := b.Conjuncts(
					around,
					"a lies in F",
					"b lies in F",
					"a lies below x",
					"x lies below b",
					"the interval between a and b lies in S",
					"p has the sign L at a",
					"p has the sign R at b")
				rootFree := b.Have(
					"p has no root from x to b",
					Statement{
						Binders: "∀y:A.",
						Hypotheses: []string{
							"y ∈ F.carrier",
							"ordered_le(lt, x, y)",
							"ordered_le(lt, y, b)",
						},
						Conclusion: "polynomial_eval(p, y) ≠ F.zero",
					},
					Derive(func(c *Argument) {
						y := c.FixAs[A]("y")
						point := c.Conjuncts(
							c.Assume(),
							"y lies in F",
							"x is at or below y",
							"y is at or below b")
						c.Cases(c.TermAs[Bool]("y = b"))
						c.When(
							"at b, p has the nonzero sign R",
							func(d *Argument, atB Fact) {
								d.Show(
									"so p does not vanish at b",
									By(
										atB,
										end[6],
										given[1],
										signValues.At(d.TermAs[A]("polynomial_eval(p, b)")),
										values.At(bPoint),
										end[1]))
							})
						c.Otherwise(
							"before b, y lies in S at or above x",
							func(d *Argument, beforeB Fact) {
								yS := d.Have(
									"y lies between a and b, so in S",
									"y ∈ S",
									By(
										end[4].At(y),
										point[0],
										point[1],
										point[2],
										beforeB,
										ordered_field.OrderedLeDef.At(lt, x, y),
										ordered_field.OrderedLeDef.At(lt, y, bPoint),
										transitive.At(aPoint, x, y),
										xIn,
										end[0],
										end[2]))
								d.Show(
									"and p has no root there",
									By(given[2].At(y), yS, point[1]))
							})
					}))
				b.Show(
					"p has one sign from x to b",
					By(
						real_closed_field.RootFreeIntervalSign.Read(closed).AsFact().At(p, x, bPoint),
						poly,
						xIn,
						end[1],
						end[3],
						rootFree,
						end[6]))
			}))
		cPoint, cS := a.ObtainAs[A](
			"a point c of S",
			"∃c:A. c ∈ S",
			BySets(inhabited))
		cIn := a.Have(
			"c lies in F",
			"c ∈ F.carrier",
			BySets(cS, within))
		a0, b0, around0 := a.Unpack2As[A, A](GroupPremises(cS, ends.At(cPoint)), "a₀", "b₀")
		end0 := a.Conjuncts(
			around0,
			"a₀ lies in F",
			"b₀ lies in F",
			"a₀ lies below c",
			"c lies below b₀",
			"the interval between a₀ and b₀ lies in S",
			"p has the sign L at a₀",
			"p has the sign R at b₀")
		ab0 := a.Have(
			"a₀ lies below b₀",
			"lt(a₀, b₀)",
			By(transitive.At(a0, cPoint, b0), end0[0], end0[1], cIn, end0[2], end0[3]))
		notBothZero := a.Have(
			"p changes between a₀ and b₀, so L and R are not both zero",
			"¬(L = &0 ∧ R = &0)",
			Derive(func(b *Argument) {
				zeros := b.SupposeNot()
				b.Show(
					"else p would vanish at both and change by the sign of zero",
					By(
						zeros,
						monotone.At(a0, b0),
						end0[0],
						end0[1],
						ab0,
						end0[4],
						end0[5],
						end0[6],
						signValues.At(b.TermAs[A]("polynomial_eval(p, a₀)")),
						signValues.At(b.TermAs[A]("polynomial_eval(p, b₀)")),
						values.At(a0),
						values.At(b0),
						flat,
						nonzeroSlope))
			}))
		a.Cases(a.TermAs[Bool]("L = -R ∧ ¬(L = &0)"))
		a.When(
			"opposite nonzero end signs: p has its one root in S",
			func(b *Argument, opposed Fact) {
				nonzeroEnds := b.Have(
					"R is not zero and differs from L",
					"¬(R = &0) ∧ ¬(L = R)",
					ByArith(opposed))
				z, root := b.ObtainAs[A](
					"a root z of p strictly between a₀ and b₀",
					"∃z:A. z ∈ F.carrier ∧ lt(a₀, z) ∧ lt(z, b₀) ∧ polynomial_eval(p, z) = F.zero",
					By(
						real_closed_field.OppositeSignsRoot.Read(closed).AsFact().At(p, a0, b0),
						poly,
						end0[0],
						end0[1],
						ab0,
						opposed,
						nonzeroEnds,
						end0[5],
						end0[6],
						signValues.At(b.TermAs[A]("polynomial_eval(p, a₀)")),
						signValues.At(b.TermAs[A]("polynomial_eval(p, b₀)")),
						values.At(a0),
						values.At(b0)))
				zParts := b.Conjuncts(
					root,
					"z lies in F",
					"a₀ lies below z",
					"z lies below b₀",
					"p vanishes at z")
				zS := b.Have(
					"z lies in S",
					"z ∈ S",
					By(end0[4].At(z), zParts[0], zParts[1], zParts[2]))
				below := b.Have(
					"below z, p has the sign L",
					"∀x:A. x ∈ S ∧ lt(x, z) ⇒ ordered_sign(F, lt, polynomial_eval(p, x)) = «below»(L, R)",
					Derive(func(c *Argument) {
						x := c.FixAs[A]("x")
						given := c.Conjuncts(
							c.Assume(),
							"x lies in S",
							"x lies below z")
						xIn := c.Have(
							"x lies in F",
							"x ∈ F.carrier",
							BySets(given[0], within))
						noRoot := c.Have(
							"the one root z lies above x",
							"∀y:A. y ∈ S ∧ ordered_le(lt, y, x) ⇒ polynomial_eval(p, y) ≠ F.zero",
							Derive(func(d *Argument) {
								y := d.FixAs[A]("y")
								point := d.Conjuncts(
									d.Assume(),
									"y lies in S",
									"y is at or below x")
								yIn := d.Have(
									"y lies in F",
									"y ∈ F.carrier",
									BySets(point[0], within))
								d.Show(
									"a root at y would be z, which lies above x",
									By(
										unique.At(y, z),
										point[0],
										zS,
										zParts[3],
										point[1],
										given[1],
										ordered_field.OrderedLeDef.At(lt, y, x),
										transitive.At(y, x, z),
										ordered_field.Irreflexive.Read(ordered).AsFact().At(z),
										yIn,
										xIn,
										zParts[0]))
							}))
						c.Show(
							"so it has the nonzero sign L",
							By(belowSign.At(x), given[0], opposed, noRoot))
					}))
				above := b.Have(
					"above z, p has the sign R",
					"∀x:A. x ∈ S ∧ lt(z, x) ⇒ ordered_sign(F, lt, polynomial_eval(p, x)) = «above»(L, R)",
					Derive(func(c *Argument) {
						x := c.FixAs[A]("x")
						given := c.Conjuncts(
							c.Assume(),
							"x lies in S",
							"z lies below x")
						xIn := c.Have(
							"x lies in F",
							"x ∈ F.carrier",
							BySets(given[0], within))
						noRoot := c.Have(
							"the one root z lies below x",
							"∀y:A. y ∈ S ∧ ordered_le(lt, x, y) ⇒ polynomial_eval(p, y) ≠ F.zero",
							Derive(func(d *Argument) {
								y := d.FixAs[A]("y")
								point := d.Conjuncts(
									d.Assume(),
									"y lies in S",
									"x is at or below y")
								yIn := d.Have(
									"y lies in F",
									"y ∈ F.carrier",
									BySets(point[0], within))
								d.Show(
									"a root at y would be z, which lies below x",
									By(
										unique.At(y, z),
										point[0],
										zS,
										zParts[3],
										point[1],
										given[1],
										ordered_field.OrderedLeDef.At(lt, x, y),
										transitive.At(z, x, y),
										ordered_field.Irreflexive.Read(ordered).AsFact().At(z),
										yIn,
										xIn,
										zParts[0]))
							}))
						c.Show(
							"so it has the nonzero sign R",
							By(aboveSign.At(x), given[0], nonzeroEnds, noRoot))
					}))
				b.Take(z)
				b.Show(
					"z is the root that splits S",
					By(
						zS,
						opposed,
						below,
						above,
						zParts[3],
						signValues.At(b.TermAs[A]("polynomial_eval(p, z)")),
						values.At(z),
						zParts[0]))
			})
		a.Otherwise(
			"otherwise p has no root in S and one sign on all of it",
			func(b *Argument, notOpposed Fact) {
				noRoot := b.Have(
					"a root would force opposite nonzero end signs",
					"∀y:A. y ∈ S ⇒ polynomial_eval(p, y) ≠ F.zero",
					Derive(func(c *Argument) {
						y := c.FixAs[A]("y")
						yS := c.Assume()
						root := c.SupposeNot()
						endSigns := c.Have(
							"L = −σ and R = σ",
							"L = -σ ∧ R = σ",
							By(roots.At(y), yS, root))
						c.Show(
							"which are opposite and nonzero",
							ByArith(endSigns, nonzeroSlope, notOpposed))
					}))
				leftSign := b.Have(
					"every point of S has the sign L, or R when L is zero",
					"∀x:A. x ∈ S ⇒ ordered_sign(F, lt, polynomial_eval(p, x)) = «below»(L, R)",
					Derive(func(c *Argument) {
						x := c.FixAs[A]("x")
						xS := c.Assume()
						c.Cases(c.TermAs[Bool]("L = &0"))
						c.When(
							"L is zero, so R is not",
							func(d *Argument, leftZero Fact) {
								d.Show(
									"x has the sign R",
									By(aboveSign.At(x), xS, leftZero, notBothZero, noRoot))
							})
						c.Otherwise(
							"L is not zero",
							func(d *Argument, leftNonzero Fact) {
								d.Show(
									"x has the sign L",
									By(belowSign.At(x), xS, leftNonzero, noRoot))
							})
					}))
				rightSign := b.Have(
					"every point of S has the sign R, or L when R is zero",
					"∀x:A. x ∈ S ⇒ ordered_sign(F, lt, polynomial_eval(p, x)) = «above»(L, R)",
					Derive(func(c *Argument) {
						x := c.FixAs[A]("x")
						xS := c.Assume()
						c.Cases(c.TermAs[Bool]("R = &0"))
						c.When(
							"R is zero, so L is not",
							func(d *Argument, rightZero Fact) {
								d.Show(
									"x has the sign L",
									By(belowSign.At(x), xS, rightZero, notBothZero, noRoot))
							})
						c.Otherwise(
							"R is not zero",
							func(d *Argument, rightNonzero Fact) {
								d.Show(
									"x has the sign R",
									By(aboveSign.At(x), xS, rightNonzero, noRoot))
							})
					}))
				b.Take(cPoint)
				b.Show(
					"any point of S splits it",
					By(cS, notOpposed, leftSign, rightSign))
			})
	}),
})}

// MonotoneRefinement — a sign table of a family f of m + 1 polynomials over
// a real closed field whose last member is the derivative p′ ≠ 0 of a
// polynomial p refines to a sign table of p followed by the first m members,
// once the signs P(a) of p at the cuts and its signs L and R far to the left
// and right are known. On each open cell p′ keeps one nonzero sign, so
// GapSplit splits the cell at a point z(a), the root of p there when its end
// signs are opposite; the new cuts are z(0) < r(0) < z(1) < … < r(q − 1) <
// z(q), and on the new cells 4a, 4a + 1, 4a + 2 and 4a + 3 p has the sign
// below z(a), at z(a), above z(a) and at r(a), while the other members keep
// their signs on the old cells 2a and 2a + 1.
var MonotoneRefinement = monotoneRefinementThm{family.Add(registry.ProofEntry{
	Name: "MonotoneRefinement",
	Key:  "prop_49f2b75fa4395214",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). " +
			"∀lt:(A → A → bool). " +
			"∀m:num. " +
			"∀p:(num → A). " +
			"∀f G:(num → num → A). " +
			"∀q:num. " +
			"∀r:(num → A). " +
			"∀t:(num → num → int). " +
			"∀P:(num → int). " +
			"∀L R:int.",
		Hypotheses: []string{
			"real_closed_field(F, lt)",
			"polynomial_over(F.carrier, p)",
			"polynomial_family_sign_table(F, lt, suc(m), f, q, r, t)",
			"f(m) = polynomial_derivative(p)",
			"polynomial_derivative(p) ≠ vec_zero(F.zero)",
			"G(0) = p",
			"∀i:num. i < m ⇒ G(suc(i)) = f(i)",
			"∀a:num. a < q ⇒ ordered_sign(F, lt, polynomial_eval(p, r(a))) = P(a)",
			"∃b:A. " +
				"    b ∈ F.carrier ∧ " +
				"    (∀x:A. x ∈ F.carrier ∧ lt(x, b) ⇒ ordered_sign(F, lt, polynomial_eval(p, x)) = L)",
			"∃b:A. " +
				"    b ∈ F.carrier ∧ " +
				"    (∀x:A. x ∈ F.carrier ∧ lt(b, x) ⇒ ordered_sign(F, lt, polynomial_eval(p, x)) = R)",
		},
		Conclusion: "∃s:(num → A). " +
			"    polynomial_family_sign_table(F, lt, suc(m), G, 2 * q + 1, s, «refined»(q, t, P, L, R))",
	}, func(
		a *Argument,
		F *Expr[FieldOps[A]],
		lt *Arrow2[A, A, Bool],
		m *Expr[Nat],
		p *Arrow[Nat, A],
		f, G *Arrow[Nat, Fun[Nat, A]],
		q *Expr[Nat],
		r *Arrow[Nat, A],
		t *Arrow2[Nat, Nat, Int],
		P *Arrow[Nat, Int],
		L, R *Expr[Int],
		closed, poly, table, derivative, slopeNonzero, first, others, cutSigns, farLeft, farRight Fact,
	) {
		ordered := real_closed_field.OrderedFieldOn.Read(closed)
		ring := field.RingOn.Read(ordered_field.FieldOn.Read(ordered))
		transitive := ordered_field.Transitive.Read(ordered).AsFact()
		comparable := ordered_field.Trichotomy.Read(ordered).AsFact()
		parts := a.Conjuncts(
			a.Unfolded(table, polynomial_sign_table.PolynomialFamilySignTableDef),
			"the cuts increase in the carrier",
			"every cell is nonempty",
			"each member keeps the sign t(j, i) on cell j")
		nonempty, rows := parts[1], parts[2]
		cutsIn := a.Conjuncts(
			a.Unfolded(parts[0], ordered_field.IncreasingCutsDef),
			"the cuts lie in the carrier",
			"the cuts increase")[0]
		lastIndex := a.Have(
			"m indexes the last member",
			"m < suc(m)",
			ByArith())
		lastOver := a.Have(
			"the last member p′ is a polynomial over F",
			"polynomial_over(F.carrier, f(m))",
			By(derivative, poly, polynomial.DerivativeOverCarrier.Read(ring).At(p)))
		slopes := a.Have(
			"on each open cell p′ has a nonzero sign, being no zero polynomial",
			"∀a:num. a ≤ q ⇒ ¬(t(2 * a, m) = &0)",
			Derive(func(b *Argument) {
				aIndex := b.FixAs[Nat]("a")
				aLe := b.Assume()
				flat := b.Have(
					"suppose p′ had the sign zero on cell 2a",
					"t(2 * a, m) = &0",
					By(b.SupposeNot()))
				b.Show(
					"then p′ would be the zero polynomial",
					By(
						polynomial_sign_table.VanishingOnOpenCell.At(F, lt, b.TermAs[Nat]("suc(m)"), f, q, r, t, m, aIndex),
						ordered,
						table,
						lastIndex,
						lastOver,
						aLe,
						flat,
						derivative,
						slopeNonzero))
			}))
		slopeSign := a.Have(
			"on the open cell 2a, p′ has the sign t(2a, m)",
			Statement{
				Binders: "∀a:num. ∀x:A.",
				Hypotheses: []string{
					"a ≤ q",
					"x ∈ polynomial_sign_cell(F, lt, q, r, 2 * a)",
				},
				Conclusion: "ordered_sign(F, lt, polynomial_eval(polynomial_derivative(p), x)) = t(2 * a, m)",
			},
			Derive(func(b *Argument) {
				b.FixAs[Nat]("a")
				x := b.FixAs[A]("x")
				given := b.Conjuncts(
					b.Assume(),
					"a indexes an open cell",
					"x lies in it")
				index := b.Have(
					"2a is a cell index",
					"2 * a ≤ 2 * q",
					ByArith(given[0]))
				b.Show(
					"the last member is p′",
					By(rows.At(b.TermAs[Nat]("2 * a"), m, x), index, lastIndex, given[1], derivative))
			}))
		ω1, leftFar := a.UnpackAs[A](farLeft, "ω₁")
		leftBound := a.Conjuncts(
			leftFar,
			"ω₁ lies in F",
			"below ω₁, p has the sign L")
		ω2, rightFar := a.UnpackAs[A](farRight, "ω₂")
		rightBound := a.Conjuncts(
			rightFar,
			"ω₂ lies in F",
			"above ω₂, p has the sign R")
		leftEnds := a.Have(
			"below each point of an open cell lies a point where p has the cell's left end sign",
			Statement{
				Binders: "∀a:num. ∀x:A.",
				Hypotheses: []string{
					"a ≤ q",
					"x ∈ polynomial_sign_cell(F, lt, q, r, 2 * a)",
				},
				Conclusion: "∃y:A. " +
					"    y ∈ F.carrier ∧ " +
					"    lt(y, x) ∧ " +
					"    (a = 0 ∨ y = r(a - 1)) ∧ " +
					"    ordered_sign(F, lt, polynomial_eval(p, y)) = «leftSign»(P, L, a)",
			},
			Derive(func(b *Argument) {
				aIndex := b.FixAs[Nat]("a")
				x := b.FixAs[A]("x")
				given := b.Conjuncts(
					b.Assume(),
					"a indexes an open cell",
					"x lies in it")
				xOpen := b.Have(
					"x lies above the cell's lower cut, if any",
					"x ∈ F.carrier ∧ (a = 0 ∨ lt(r(a - 1), x))",
					By(given[1], given[0], polynomial_sign_table.OpenCellMember.At(F, lt, q, r, aIndex, x)))
				b.Cases(b.TermAs[Bool]("a = 0"))
				b.When(
					"the left ray: a point below both x and ω₁ has the sign L",
					func(d *Argument, firstCell Fact) {
						_, below := d.ObtainAs[A](
							"a point y below x and below ω₁",
							"∃y:A. y ∈ F.carrier ∧ lt(y, x) ∧ lt(y, ω₁)",
							Derive(func(g *Argument) {
								g.Cases(g.TermAs[Bool]("lt(x, ω₁)"))
								g.When(
									"x lies below ω₁: go below x",
									func(h *Argument, xLow Fact) {
										y, yBelow := h.ObtainAs[A](
											"a point y below x",
											"∃y:A. y ∈ F.carrier ∧ lt(y, x)",
											By(xOpen, ordered_field.NoEndpoints.Read(ordered)))
										h.Take(y)
										h.Show(
											"by transitivity",
											By(yBelow, xLow, xOpen, leftBound[0], transitive.At(y, x, ω1)))
									})
								g.Otherwise(
									"x lies at or above ω₁: go below ω₁",
									func(h *Argument, xHigh Fact) {
										y, yBelow := h.ObtainAs[A](
											"a point y below ω₁",
											"∃y:A. y ∈ F.carrier ∧ lt(y, ω₁)",
											By(leftBound[0], ordered_field.NoEndpoints.Read(ordered)))
										h.Take(y)
										h.Show(
											"by trichotomy and transitivity",
											By(Normalized, yBelow, xHigh, xOpen, leftBound[0], comparable.At(x, ω1), transitive.At(y, ω1, x)))
									})
							}))
						d.Show(
							"that point has the far-left sign L",
							By(below, firstCell, leftBound[1]))
					})
				b.Otherwise(
					"a later cell: its lower cut r(a − 1)",
					func(d *Argument, laterCell Fact) {
						index := d.Have(
							"a − 1 is a cut index",
							"a - 1 < q",
							ByArith(laterCell, given[0]))
						d.Take(d.TermAs[A]("r(a - 1)"))
						d.Show(
							"where p has the sign P(a − 1)",
							By(xOpen, laterCell, index, cutSigns.At(d.TermAs[Nat]("a - 1")), cutsIn.At(d.TermAs[Nat]("a - 1"))))
					})
			}))
		rightEnds := a.Have(
			"above each point of an open cell lies a point where p has the cell's right end sign",
			Statement{
				Binders: "∀a:num. ∀x:A.",
				Hypotheses: []string{
					"a ≤ q",
					"x ∈ polynomial_sign_cell(F, lt, q, r, 2 * a)",
				},
				Conclusion: "∃y:A. " +
					"    y ∈ F.carrier ∧ " +
					"    lt(x, y) ∧ " +
					"    (a = q ∨ y = r(a)) ∧ " +
					"    ordered_sign(F, lt, polynomial_eval(p, y)) = «rightSign»(q, P, R, a)",
			},
			Derive(func(b *Argument) {
				aIndex := b.FixAs[Nat]("a")
				x := b.FixAs[A]("x")
				given := b.Conjuncts(
					b.Assume(),
					"a indexes an open cell",
					"x lies in it")
				xOpen := b.Have(
					"x lies below the cell's upper cut, if any",
					"x ∈ F.carrier ∧ (a = q ∨ lt(x, r(a)))",
					By(given[1], given[0], polynomial_sign_table.OpenCellMember.At(F, lt, q, r, aIndex, x)))
				b.Cases(b.TermAs[Bool]("a = q"))
				b.When(
					"the right ray: a point above both x and ω₂ has the sign R",
					func(d *Argument, lastCell Fact) {
						_, above := d.ObtainAs[A](
							"a point y above x and above ω₂",
							"∃y:A. y ∈ F.carrier ∧ lt(x, y) ∧ lt(ω₂, y)",
							Derive(func(g *Argument) {
								g.Cases(g.TermAs[Bool]("lt(ω₂, x)"))
								g.When(
									"x lies above ω₂: go above x",
									func(h *Argument, xHigh Fact) {
										y, yAbove := h.ObtainAs[A](
											"a point y above x",
											"∃y:A. y ∈ F.carrier ∧ lt(x, y)",
											By(xOpen, ordered_field.NoEndpoints.Read(ordered)))
										h.Take(y)
										h.Show(
											"by transitivity",
											By(yAbove, xHigh, xOpen, rightBound[0], transitive.At(ω2, x, y)))
									})
								g.Otherwise(
									"x lies at or below ω₂: go above ω₂",
									func(h *Argument, xLow Fact) {
										y, yAbove := h.ObtainAs[A](
											"a point y above ω₂",
											"∃y:A. y ∈ F.carrier ∧ lt(ω₂, y)",
											By(rightBound[0], ordered_field.NoEndpoints.Read(ordered)))
										h.Take(y)
										h.Show(
											"by trichotomy and transitivity",
											By(Normalized, yAbove, xLow, xOpen, rightBound[0], comparable.At(x, ω2), transitive.At(x, ω2, y)))
									})
							}))
						d.Show(
							"that point has the far-right sign R",
							By(above, lastCell, rightBound[1]))
					})
				b.Otherwise(
					"an earlier cell: its upper cut r(a)",
					func(d *Argument, earlierCell Fact) {
						index := d.Have(
							"a is a cut index",
							"a < q",
							ByArith(earlierCell, given[0]))
						d.Take(r.Apply(aIndex))
						d.Show(
							"where p has the sign P(a)",
							By(xOpen, earlierCell, index, cutSigns.At(aIndex), cutsIn.At(aIndex)))
					})
			}))
		_, splitterDef := a.LetAs[Fun2[Nat, A, Bool]](
			"splits",
			"λa:num. λz:A. "+
				"    z ∈ polynomial_sign_cell(F, lt, q, r, 2 * a) ∧ "+
				"    ordered_sign(F, lt, polynomial_eval(p, z)) = "+
				"    «split»(«leftSign»(P, L, a), «rightSign»(q, P, R, a)) ∧ "+
				"    (∀x:A. "+
				"        x ∈ polynomial_sign_cell(F, lt, q, r, 2 * a) ∧ lt(x, z) ⇒ "+
				"        ordered_sign(F, lt, polynomial_eval(p, x)) = "+
				"        «below»(«leftSign»(P, L, a), «rightSign»(q, P, R, a))) ∧ "+
				"    (∀x:A. "+
				"        x ∈ polynomial_sign_cell(F, lt, q, r, 2 * a) ∧ lt(z, x) ⇒ "+
				"        ordered_sign(F, lt, polynomial_eval(p, x)) = "+
				"        «above»(«leftSign»(P, L, a), «rightSign»(q, P, R, a)))")
		gaps := a.Have(
			"in each open cell a point z splits the signs of p",
			"∀a:num. a ≤ q ⇒ ∃z:A. splits(a, z)",
			Derive(func(b *Argument) {
				aIndex := b.FixAs[Nat]("a")
				aLe := b.Assume()
				cell := b.TermAs[Set[A]]("polynomial_sign_cell(F, lt, q, r, 2 * a)")
				within := b.Have(
					"the cell lies in the carrier",
					"polynomial_sign_cell(F, lt, q, r, 2 * a) ⊆ F.carrier",
					Simp(Fwd(polynomial_sign_table.SignCellDef)),
					BySets())
				index := b.Have(
					"2a is a cell index",
					"2 * a ≤ 2 * q",
					ByArith(aLe))
				inhabited := b.Have(
					"the cell is not empty",
					"polynomial_sign_cell(F, lt, q, r, 2 * a) ≠ ∅",
					By(nonempty.At(b.TermAs[Nat]("2 * a")), index))
				convex := b.Have(
					"the cell is convex",
					Statement{
						Binders: "∀x y z:A.",
						Hypotheses: []string{
							"x ∈ polynomial_sign_cell(F, lt, q, r, 2 * a)",
							"y ∈ polynomial_sign_cell(F, lt, q, r, 2 * a)",
							"z ∈ F.carrier",
							"lt(x, z)",
							"lt(z, y)",
						},
						Conclusion: "z ∈ polynomial_sign_cell(F, lt, q, r, 2 * a)",
					},
					Derive(func(d *Argument) {
						x := d.FixAs[A]("x")
						y := d.FixAs[A]("y")
						z := d.FixAs[A]("z")
						given := d.Conjuncts(
							d.Assume(),
							"x lies in the cell",
							"y lies in the cell",
							"z lies in the carrier",
							"x lies below z",
							"z lies below y")
						d.Show(
							"by OpenCellConvex",
							By(
								polynomial_sign_table.OpenCellConvex.At(F, lt, q, r, aIndex, x, y, z),
								ordered,
								cutsIn,
								aLe,
								given[0],
								given[1],
								given[2],
								ordered_field.OrderedLeDef.At(lt, x, z),
								ordered_field.OrderedLeDef.At(lt, z, y),
								given[3],
								given[4]))
					}))
				ends := b.Have(
					"every point of the cell lies inside an interval within it whose ends give p the cell's end signs",
					Statement{
						Binders: "∀x:A.",
						Hypotheses: []string{
							"x ∈ polynomial_sign_cell(F, lt, q, r, 2 * a)",
						},
						Conclusion: "∃u v:A. " +
							"    u ∈ F.carrier ∧ " +
							"    v ∈ F.carrier ∧ " +
							"    lt(u, x) ∧ " +
							"    lt(x, v) ∧ " +
							"    (∀y:A. " +
							"        y ∈ F.carrier ∧ lt(u, y) ∧ lt(y, v) ⇒ y ∈ polynomial_sign_cell(F, lt, q, r, 2 * a)) ∧ " +
							"    ordered_sign(F, lt, polynomial_eval(p, u)) = «leftSign»(P, L, a) ∧ " +
							"    ordered_sign(F, lt, polynomial_eval(p, v)) = «rightSign»(q, P, R, a)",
					},
					Derive(func(d *Argument) {
						x := d.FixAs[A]("x")
						xIn := d.Assume()
						u, lowEnd := d.UnpackAs[A](GroupPremises(aLe, xIn, leftEnds.At(aIndex, x)), "u")
						v, highEnd := d.UnpackAs[A](GroupPremises(aLe, xIn, rightEnds.At(aIndex, x)), "v")
						lows := d.Conjuncts(
							lowEnd,
							"u lies in F",
							"u lies below x",
							"u is the lower cut, if any",
							"p has the left end sign at u")
						highs := d.Conjuncts(
							highEnd,
							"v lies in F",
							"x lies below v",
							"v is the upper cut, if any",
							"p has the right end sign at v")
						inside := d.Have(
							"the interval between u and v lies in the cell",
							"∀y:A. y ∈ F.carrier ∧ lt(u, y) ∧ lt(y, v) ⇒ y ∈ polynomial_sign_cell(F, lt, q, r, 2 * a)",
							Derive(func(g *Argument) {
								y := g.FixAs[A]("y")
								point := g.Conjuncts(
									g.Assume(),
									"y lies in F",
									"u lies below y",
									"y lies below v")
								g.Show(
									"y lies above the lower cut and below the upper one",
									By(
										polynomial_sign_table.OpenCellMember.At(F, lt, q, r, aIndex, y),
										aLe,
										point[0],
										point[1],
										point[2],
										lows[2],
										highs[2]))
							}))
						d.Take(u)
						d.Take(v)
						d.Show(
							"u and v are such ends",
							By(lows[0], highs[0], lows[1], highs[1], inside, lows[3], highs[3]))
					}))
				b.Show(
					"by GapSplit, p′ having the nonzero sign t(2a, m) on the cell",
					splitterDef.Rw(),
					By(
						GapSplit.At(
							F,
							lt,
							p,
							cell,
							b.TermAs[Int]("t(2 * a, m)"),
							b.TermAs[Int]("«leftSign»(P, L, a)"),
							b.TermAs[Int]("«rightSign»(q, P, R, a)")),
						closed,
						poly,
						within,
						inhabited,
						convex,
						slopes.At(aIndex),
						aLe,
						slopeSign,
						ends))
			}))
		_, chosen := a.ObtainAs[Fun[Nat, A]](
			"choose the splitting point z(a) of every open cell",
			"∃z:(num → A). ∀a:num. a ≤ q ⇒ splits(a, z(a))",
			By(gaps))
		splits := a.Have(
			"so z(a) splits the signs of p on the open cell 2a",
			Statement{
				Binders: "∀a:num.",
				Hypotheses: []string{
					"a ≤ q",
				},
				Conclusion: "z(a) ∈ polynomial_sign_cell(F, lt, q, r, 2 * a) ∧ " +
					"ordered_sign(F, lt, polynomial_eval(p, z(a))) = " +
					"«split»(«leftSign»(P, L, a), «rightSign»(q, P, R, a)) ∧ " +
					"(∀x:A. " +
					"    x ∈ polynomial_sign_cell(F, lt, q, r, 2 * a) ∧ lt(x, z(a)) ⇒ " +
					"    ordered_sign(F, lt, polynomial_eval(p, x)) = " +
					"    «below»(«leftSign»(P, L, a), «rightSign»(q, P, R, a))) ∧ " +
					"(∀x:A. " +
					"    x ∈ polynomial_sign_cell(F, lt, q, r, 2 * a) ∧ lt(z(a), x) ⇒ " +
					"    ordered_sign(F, lt, polynomial_eval(p, x)) = " +
					"    «above»(«leftSign»(P, L, a), «rightSign»(q, P, R, a)))",
			},
			Derive(func(b *Argument) {
				aIndex := b.FixAs[Nat]("a")
				aLe := b.Assume()
				b.Show(
					"unfold what splits says at a",
					By(b.Simplified(GroupPremises(aLe, chosen.At(aIndex)), Fwd(splitterDef))))
			}))
		splitBounds := a.Have(
			"each splitting point lies in its open cell, above the lower cut and below the upper one",
			"∀c:num. c ≤ q ⇒ z(c) ∈ F.carrier ∧ (c = 0 ∨ lt(r(c - 1), z(c))) ∧ (c = q ∨ lt(z(c), r(c)))",
			Derive(func(b *Argument) {
				c := b.FixAs[Nat]("c")
				cLe := b.Assume()
				b.Show(
					"z(c) lies in the open cell 2c",
					By(splits.At(c), cLe, polynomial_sign_table.OpenCellMember.At(F, lt, q, r, c, b.TermAs[A]("z(c)"))))
			}))
		cuts, cutsDef := a.LetAs[Fun[Nat, A]](
			"s", "λc:num. COND(nat_mod(c, 2) = 0, z(nat_div(c, 2)), r(nat_div(c, 2)))")
		evenCut := a.Have(
			"the even new cuts are the splitting points",
			"∀c:num. s(2 * c) = z(c)",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("c")
				halves := b.Have(
					"2c is even with half c",
					"nat_mod(2 * c, 2) = 0 ∧ nat_div(2 * c, 2) = c",
					ByArith())
				b.Show(
					"s picks z at an even index",
					cutsDef.Rw(),
					By(Normalized, halves))
			}))
		oddCut := a.Have(
			"the odd new cuts are the old cuts",
			"∀c:num. s(2 * c + 1) = r(c)",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("c")
				halves := b.Have(
					"2c + 1 is odd with half c",
					"nat_mod(2 * c + 1, 2) = 1 ∧ nat_div(2 * c + 1, 2) = c ∧ ¬(1 = 0)",
					ByArith())
				b.Show(
					"s picks r at an odd index",
					cutsDef.Rw(),
					By(halves))
			}))
		newIn := a.Have(
			"the new cuts lie in the carrier",
			"∀c:num. c < 2 * q + 1 ⇒ s(c) ∈ F.carrier",
			Derive(func(b *Argument) {
				c := b.FixAs[Nat]("c")
				bound := b.Have(
					"c is at most 2q",
					"c ≤ 2 * q",
					ByArith(b.Assume()))
				b.Do(GroupPremises(bound, nat_parity.DoubleOrSucDoubleBelow.At(q, c)).SplitDisj(
					LeftHolds(
						"an even new cut is a splitting point",
						Given(func(d *Argument, even Fact) {
							h, shape := d.UnpackAs[Nat](even, "h")
							d.Show(
								"z(h) lies in the carrier",
								By(Normalized, shape, evenCut.At(h), splitBounds.At(h)))
						})),
					RightHolds(
						"an odd new cut is an old cut",
						Given(func(d *Argument, odd Fact) {
							h, index := d.UnpackAs[Nat](odd, "h")
							d.Show(
								"r(h) lies in the carrier",
								By(Normalized, index, oddCut.At(h), cutsIn.At(h)))
						}))))
			}))
		consecutive := a.Have(
			"each new cut lies below the next",
			"∀c:num. suc(c) < 2 * q + 1 ⇒ lt(s(c), s(suc(c)))",
			Derive(func(b *Argument) {
				c := b.FixAs[Nat]("c")
				cLt := b.Assume()
				bound := b.Have(
					"c is at most 2q",
					"c ≤ 2 * q",
					ByArith(cLt))
				b.Do(GroupPremises(bound, nat_parity.DoubleOrSucDoubleBelow.At(q, c)).SplitDisj(
					LeftHolds(
						"z(h) lies below r(h)",
						Given(func(d *Argument, even Fact) {
							h, shape := d.UnpackAs[Nat](even, "h")
							index := d.Have(
								"h is an old cut index and the next new cut has index 2h + 1",
								"h ≤ q ∧ ¬(h = q) ∧ suc(c) = 2 * h + 1",
								ByArith(cLt, shape))
							d.Show(
								"the splitting point lies below the cut above it",
								By(shape, index, evenCut.At(h), oddCut.At(h), splitBounds.At(h)))
						})),
					RightHolds(
						"r(h) lies below z(h + 1)",
						Given(func(d *Argument, odd Fact) {
							h, shape := d.UnpackAs[Nat](odd, "h")
							next := d.TermAs[Nat]("h + 1")
							index := d.Have(
								"c = 2h + 1 and the next new cut has index 2(h + 1)",
								"c = 2 * h + 1 ∧ suc(c) = 2 * (h + 1) ∧ h + 1 ≤ q ∧ ¬(h + 1 = 0) ∧ h + 1 - 1 = h",
								ByArith(cLt, shape))
							d.Show(
								"the cut lies below the splitting point above it",
								By(index, oddCut.At(h), evenCut.At(next), splitBounds.At(next)))
						}))))
			}))
		newCuts := a.Have(
			"so the new cuts increase in the carrier",
			"increasing_cuts(F, lt, 2 * q + 1, s)",
			By(GroupPremises(
				newIn,
				consecutive,
				ordered_field.ConsecutiveIncreasing.Read(ordered).At(a.TermAs[Nat]("2 * q + 1"), cuts))))
		newNonempty := a.Have(
			"every new cell is nonempty",
			"∀j:num. j ≤ 2 * (2 * q + 1) ⇒ polynomial_sign_cell(F, lt, 2 * q + 1, s, j) ≠ ∅",
			Derive(func(b *Argument) {
				j := b.FixAs[Nat]("j")
				bound := b.Assume()
				b.Show(
					"increasing cuts have nonempty cells",
					By(
						polynomial_sign_table.SignCellsNonempty.At(F, lt, b.TermAs[Nat]("2 * q + 1"), cuts, j),
						ordered,
						newCuts,
						bound))
			}))
		member := a.Have(
			"a later G(i) is f(i − 1)",
			"∀i:num. i < suc(m) ∧ ¬(i = 0) ⇒ i - 1 < suc(m) ∧ G(i) = f(i - 1)",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("i")
				given := b.Conjuncts(
					b.Assume(),
					"i indexes a member",
					"i is not 0")
				index := b.Have(
					"i − 1 indexes one of the first m members of f, and i is its successor",
					"i - 1 < m ∧ i - 1 < suc(m) ∧ suc(i - 1) = i",
					ByArith(given[0], given[1]))
				b.Show(
					"G(suc(i − 1)) = f(i − 1)",
					By(Normalized, others.At(b.TermAs[Nat]("i - 1")), index))
			}))
		gapRow := a.Have(
			"on an open old cell a later G(i) keeps the sign of its old row",
			Statement{
				Binders: "∀c i:num. ∀x:A.",
				Hypotheses: []string{
					"c ≤ q",
					"i < suc(m)",
					"¬(i = 0)",
					"x ∈ polynomial_sign_cell(F, lt, q, r, 2 * c)",
				},
				Conclusion: "ordered_sign(F, lt, polynomial_eval(G(i), x)) = t(2 * c, i - 1)",
			},
			Derive(func(b *Argument) {
				b.FixAs[Nat]("c")
				i := b.FixAs[Nat]("i")
				x := b.FixAs[A]("x")
				given := b.Conjuncts(
					b.Assume(),
					"c indexes an open cell",
					"i indexes a member",
					"i is not 0",
					"x lies in the open cell 2c")
				index := b.Have(
					"2c is an old cell index",
					"2 * c ≤ 2 * q",
					ByArith(given[0]))
				b.Show(
					"G(i) is f(i − 1)",
					By(
						rows.At(b.TermAs[Nat]("2 * c"), b.TermAs[Nat]("i - 1"), x),
						member.At(i),
						given[1],
						given[2],
						given[3],
						index))
			}))
		cutRow := a.Have(
			"at an old cut a later G(i) keeps the sign of its old row",
			Statement{
				Binders: "∀c i:num.",
				Hypotheses: []string{
					"c < q",
					"i < suc(m)",
					"¬(i = 0)",
				},
				Conclusion: "ordered_sign(F, lt, polynomial_eval(G(i), r(c))) = t(2 * c + 1, i - 1)",
			},
			Derive(func(b *Argument) {
				c := b.FixAs[Nat]("c")
				i := b.FixAs[Nat]("i")
				given := b.Conjuncts(
					b.Assume(),
					"c is an old cut index",
					"i indexes a member",
					"i is not 0")
				index := b.Have(
					"2c + 1 is an old cell index",
					"2 * c + 1 ≤ 2 * q",
					ByArith(given[0]))
				atCut := b.Have(
					"r(c) lies in the old cut cell 2c + 1",
					"r(c) ∈ polynomial_sign_cell(F, lt, q, r, 2 * c + 1)",
					By(polynomial_sign_table.CutCellMember.At(F, lt, q, r, c, r.Apply(c)), given[0], cutsIn.At(c)))
				b.Show(
					"G(i) is f(i − 1)",
					By(
						rows.At(b.TermAs[Nat]("2 * c + 1"), b.TermAs[Nat]("i - 1"), r.Apply(c)),
						member.At(i),
						given[1],
						given[2],
						index,
						atCut))
			}))
		newRows := a.Have(
			"each G(i) has the sign «refined»(q, t, P, L, R, j, i) on the new cell j",
			Statement{
				Binders: "∀j i:num. ∀x:A.",
				Hypotheses: []string{
					"j ≤ 2 * (2 * q + 1)",
					"i < suc(m)",
					"x ∈ polynomial_sign_cell(F, lt, 2 * q + 1, s, j)",
				},
				Conclusion: "ordered_sign(F, lt, polynomial_eval(G(i), x)) = «refined»(q, t, P, L, R, j, i)",
			},
			Derive(func(b *Argument) {
				b.FixAs[Nat]("j")
				i := b.FixAs[Nat]("i")
				x := b.FixAs[A]("x")
				given := b.Conjuncts(
					b.Assume(),
					"j is a new cell index",
					"i indexes a member",
					"x lies in the new cell j")
				c, cDef := b.LetAs[Nat]("c", "nat_div(j, 4)")
				_, eDef := b.LetAs[Nat]("e", "nat_mod(j, 4)")
				parts := b.Have(
					"j = 4c + e with e < 4, and c indexes an open old cell",
					"j = 4 * c + e ∧ e < 4 ∧ c ≤ q",
					ByArith(given[0], cDef, eDef))
				lastOrNot := b.Have(
					"c is the last open old cell or an earlier one",
					"c = q ∨ c < q",
					ByArith(parts))
				b.Cases(b.TermAs[Bool]("e = 0"))
				b.When(
					"e = 0: the new open cell between the cut below and z(c)",
					func(d *Argument, e0 Fact) {
						index := d.Have(
							"j = 2 · 2c, and 2c is an open new cell index below the last",
							"j = 2 * (2 * c) ∧ "+
								"2 * c ≤ 2 * q + 1 ∧ "+
								"¬(2 * c = 2 * q + 1) ∧ "+
								"(2 * c = 0 ⇔ c = 0) ∧ "+
								"(c = 0 ∨ 2 * c - 1 = 2 * (c - 1) + 1) ∧ "+
								"2 * c + nat_div(e, 3) = 2 * c",
							ByArith(parts, e0))
						xOpen := d.Have(
							"x lies above the new cut below it and below s(2c) = z(c)",
							"x ∈ F.carrier ∧ (2 * c = 0 ∨ lt(s(2 * c - 1), x)) ∧ (2 * c = 2 * q + 1 ∨ lt(x, s(2 * c)))",
							By(
								given[2],
								index,
								polynomial_sign_table.OpenCellMember.At(
									F, lt, d.TermAs[Nat]("2 * q + 1"), cuts, d.TermAs[Nat]("2 * c"), x)))
						belowSplit := d.Have(
							"x lies below z(c)",
							"lt(x, z(c))",
							By(xOpen, index, evenCut.At(c)))
						position := d.Have(
							"so x lies in the old open cell 2c",
							"x ∈ polynomial_sign_cell(F, lt, q, r, 2 * c)",
							Derive(func(g *Argument) {
								lower := g.Have(
									"x lies above the old cut r(c − 1), if any",
									"c = 0 ∨ lt(r(c - 1), x)",
									By(xOpen, index, oddCut.At(g.TermAs[Nat]("c - 1"))))
								upper := g.Have(
									"x lies below z(c), which lies below the old cut r(c), if any",
									"c = q ∨ lt(x, r(c))",
									By(
										belowSplit,
										splitBounds.At(c),
										parts,
										lastOrNot,
										xOpen,
										cutsIn.At(c),
										transitive.At(x, g.TermAs[A]("z(c)"), r.Apply(c))))
								g.Show(
									"by the open cell's reading",
									By(polynomial_sign_table.OpenCellMember.At(F, lt, q, r, c, x), parts, xOpen, lower, upper))
							}))
						d.Cases(d.TermAs[Bool]("i = 0"))
						d.When(
							"p has the sign below z(c)",
							func(g *Argument, isP Fact) {
								g.Show(
									"by the split of the open cell 2c",
									By(isP, first, e0, position, belowSplit, splits.At(c), parts))
							})
						d.Otherwise(
							"a later member keeps the sign of its old row",
							func(g *Argument, later Fact) {
								g.Show(
									"on the old open cell 2c",
									By(later, e0, index, gapRow.At(c, i, x), parts, given[1], position))
							})
					})
				b.Otherwise(
					"e ≠ 0",
					func(d *Argument, notE0 Fact) {
						d.Cases(d.TermAs[Bool]("e = 1"))
						d.When(
							"e = 1: the new cut z(c)",
							func(g *Argument, e1 Fact) {
								index := g.Have(
									"j = 2 · 2c + 1, a new cut index",
									"j = 2 * (2 * c) + 1 ∧ 2 * c < 2 * q + 1 ∧ ¬(1 = 0) ∧ 2 * c + nat_div(e, 3) = 2 * c",
									ByArith(parts, e1))
								atSplit := g.Have(
									"x is s(2c) = z(c)",
									"x = z(c)",
									By(
										Normalized,
										given[2],
										index,
										polynomial_sign_table.CutCellMember.At(
											F, lt, g.TermAs[Nat]("2 * q + 1"), cuts, g.TermAs[Nat]("2 * c"), x),
										evenCut.At(c)))
								splitIn := g.Have(
									"z(c) lies in the old open cell 2c",
									"z(c) ∈ polynomial_sign_cell(F, lt, q, r, 2 * c)",
									By(splits.At(c), parts))
								g.Cases(g.TermAs[Bool]("i = 0"))
								g.When(
									"p has the split sign at z(c)",
									func(h *Argument, isP Fact) {
										h.Show(
											"by the split of the open cell 2c",
											By(isP, first, e1, index, atSplit, splits.At(c), parts))
									})
								g.Otherwise(
									"a later member keeps the sign of its old row",
									func(h *Argument, later Fact) {
										h.Show(
											"on the old open cell 2c",
											By(later, e1, index, atSplit, gapRow.At(c, i, h.TermAs[A]("z(c)")), parts, given[1], splitIn))
									})
							})
						d.Otherwise(
							"e ≠ 0, 1",
							func(g *Argument, notE1 Fact) {
								g.Cases(g.TermAs[Bool]("e = 2"))
								g.When(
									"e = 2: the new open cell between z(c) and the cut above",
									func(h *Argument, e2 Fact) {
										index := h.Have(
											"j = 2(2c + 1), an open new cell index",
											"j = 2 * (2 * c + 1) ∧ "+
												"2 * c + 1 ≤ 2 * q + 1 ∧ "+
												"(2 * c + 1 = 2 * q + 1 ⇔ c = q) ∧ "+
												"¬(2 * c + 1 = 0) ∧ "+
												"2 * c + 1 - 1 = 2 * c ∧ "+
												"¬(2 = 0) ∧ "+
												"¬(2 = 1) ∧ "+
												"2 * c + nat_div(e, 3) = 2 * c",
											ByArith(parts, e2))
										xOpen := h.Have(
											"x lies above s(2c) = z(c) and below the new cut above it",
											"x ∈ F.carrier ∧ "+
												"(2 * c + 1 = 0 ∨ lt(s(2 * c + 1 - 1), x)) ∧ "+
												"(2 * c + 1 = 2 * q + 1 ∨ lt(x, s(2 * c + 1)))",
											By(
												given[2],
												index,
												polynomial_sign_table.OpenCellMember.At(
													F, lt, h.TermAs[Nat]("2 * q + 1"), cuts, h.TermAs[Nat]("2 * c + 1"), x)))
										aboveSplit := h.Have(
											"x lies above z(c)",
											"lt(z(c), x)",
											By(xOpen, index, evenCut.At(c)))
										position := h.Have(
											"so x lies in the old open cell 2c",
											"x ∈ polynomial_sign_cell(F, lt, q, r, 2 * c)",
											Derive(func(w *Argument) {
												lower := w.Have(
													"x lies above z(c), which lies above the old cut r(c − 1), if any",
													"c = 0 ∨ lt(r(c - 1), x)",
													By(
														aboveSplit,
														splitBounds.At(c),
														parts,
														xOpen,
														cutsIn.At(w.TermAs[Nat]("c - 1")),
														w.Have(
															"c = 0 ∨ c - 1 < q",
															"c = 0 ∨ c - 1 < q",
															ByArith(parts)),
														transitive.At(w.TermAs[A]("r(c - 1)"), w.TermAs[A]("z(c)"), x)))
												upper := w.Have(
													"x lies below the old cut r(c), if any",
													"c = q ∨ lt(x, r(c))",
													By(xOpen, index, oddCut.At(c)))
												w.Show(
													"by the open cell's reading",
													By(polynomial_sign_table.OpenCellMember.At(F, lt, q, r, c, x), parts, xOpen, lower, upper))
											}))
										h.Cases(h.TermAs[Bool]("i = 0"))
										h.When(
											"p has the sign above z(c)",
											func(w *Argument, isP Fact) {
												w.Show(
													"by the split of the open cell 2c",
													By(isP, first, e2, index, position, aboveSplit, splits.At(c), parts))
											})
										h.Otherwise(
											"a later member keeps the sign of its old row",
											func(w *Argument, later Fact) {
												w.Show(
													"on the old open cell 2c",
													By(later, e2, index, gapRow.At(c, i, x), parts, given[1], position))
											})
									})
								g.Otherwise(
									"e = 3: the new cut r(c)",
									func(h *Argument, notE2 Fact) {
										index := h.Have(
											"e = 3, and j = 2(2c + 1) + 1 names the old cut r(c)",
											"e = 3 ∧ "+
												"j = 2 * (2 * c + 1) + 1 ∧ "+
												"2 * c + 1 < 2 * q + 1 ∧ "+
												"c < q ∧ "+
												"¬(3 = 0) ∧ "+
												"¬(3 = 1) ∧ "+
												"¬(3 = 2) ∧ "+
												"2 * c + nat_div(e, 3) = 2 * c + 1",
											ByArith(parts, notE0, notE1, notE2, given[0], cDef))
										atCut := h.Have(
											"x is s(2c + 1) = r(c)",
											"x = r(c)",
											By(
												given[2],
												index,
												polynomial_sign_table.CutCellMember.At(
													F, lt, h.TermAs[Nat]("2 * q + 1"), cuts, h.TermAs[Nat]("2 * c + 1"), x),
												oddCut.At(c)))
										h.Cases(h.TermAs[Bool]("i = 0"))
										h.When(
											"p has the sign P(c) at r(c)",
											func(w *Argument, isP Fact) {
												w.Show(
													"the sign of p at the old cut",
													By(isP, first, index, atCut, cutSigns.At(c)))
											})
										h.Otherwise(
											"a later member keeps the sign of its old row",
											func(w *Argument, later Fact) {
												w.Show(
													"at the old cut r(c)",
													By(later, index, atCut, cutRow.At(c, i), given[1]))
											})
									})
							})
					})
			}))
		a.Take(cuts)
		a.Show(
			"the new cuts carry a sign table of G",
			Simp(Fwd(polynomial_sign_table.PolynomialFamilySignTableDef)),
			By(newCuts, newNonempty, newRows))
	}),
})}
