package quadratic_twist

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/finite_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/scheme/closed_point"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// TwistSolutionBijection — the coordinate change (X, Y) ↦ (eX, e²Y) maps the
// points of k² on the curve with the twisted coefficients one-to-one onto the
// points on y² = e·f(x), for f(x) = x³ + ax + b. The curve equations at (X, Y)
// and at (eX, e²Y) are one another multiplied by e⁴ (the twisted coefficients
// are a·e⁻² and b·e⁻³); e ≠ 0 cancels from the coordinates of two points with
// one image, and a point (x, y) of y² = e·f(x) is the image of (e⁻¹x, e⁻²y).
var TwistSolutionBijection = twistSolutionBijectionThm{family.Add(registry.ProofEntry{
	Name: "TwistSolutionBijection",
	Key:  "prop_fc435fcd235e22a9",
	Build: family.Sections(Statement{
		Binders: "∀k:field_on(A). ∀a b e:A.",
		Hypotheses: []string{
			"a ∈ k.carrier",
			"b ∈ k.carrier",
			"e ∈ k.carrier",
			"e ≠ k.zero",
		},
		Conclusion: "injective_on(«twisted», «scale») ∧ " +
			"image(«scale», «twisted») = " +
			"{z:prod(A, A) | " +
			"    fst(z) ∈ k.carrier ∧ " +
			"    snd(z) ∈ k.carrier ∧ " +
			"    snd(z) * snd(z) = e * (fst(z) * (fst(z) * fst(z)) + a * fst(z) + b)}",
		Abbrev: Abbrev{
			{Name: "twisted", Text: "{z:prod(A, A) | " +
				"    fst(z) ∈ k.carrier ∧ " +
				"    snd(z) ∈ k.carrier ∧ " +
				"    snd(z) * snd(z) = " +
				"    fst(z) * (fst(z) * fst(z)) + " +
				"    fst(twist_coefficients(k, a, b, e)) * fst(z) + " +
				"    snd(twist_coefficients(k, a, b, e))}"},
			{Name: "scale", Text: "λz:prod(A, A). (e * fst(z), e * e * snd(z))"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		rescaled := ctx.Lemma(Statement{
			Binders: "∀k:field_on(A). ∀a b e x y:A.",
			Hypotheses: []string{
				"a ∈ k.carrier",
				"b ∈ k.carrier",
				"e ∈ k.carrier",
				"e ≠ k.zero",
				"x ∈ k.carrier",
				"y ∈ k.carrier",
			},
			Conclusion: "y * y = " +
				"x * (x * x) + fst(twist_coefficients(k, a, b, e)) * x + snd(twist_coefficients(k, a, b, e)) ⇔ " +
				"e * e * y * (e * e * y) = e * (e * x * (e * x * (e * x)) + a * (e * x) + b)",
		}, func(arg *Argument, k Fact, a, b, e, x, y *Expr[A], aIn, bIn, eIn, eNonzero, xIn, yIn Fact) {
			arg.Iff()
			arg.Forward(
				"multiply the twisted equation by e⁴, its coefficients written out as a·e⁻² and b·e⁻³",
				func(c *Argument, twisted Fact) {
					written := c.Simplified(twisted, Fwd(twistCoefficientsDef), Fwd(pairs.Fst), Fwd(pairs.Snd))
					c.Show(
						"e·e⁻¹ = 1 cancels from every monomial",
						ByArith(k, Scaled(c.TermAs[A]("e * e * e * e"), written), aIn, bIn, eIn, eNonzero, xIn, yIn))
				})
			arg.Backward(
				"multiply the scaled equation by e⁻⁴ and write out the twisted coefficients",
				func(c *Argument, scaled Fact) {
					c.Show(
						"e·e⁻¹ = 1 cancels from every monomial",
						Simp(Fwd(twistCoefficientsDef), Fwd(pairs.Fst), Fwd(pairs.Snd)),
						ByArith(
							k,
							Scaled(c.TermAs[A]("k.inv(e) * k.inv(e) * k.inv(e) * k.inv(e)"), scaled),
							aIn,
							bIn,
							eIn,
							eNonzero,
							xIn,
							yIn))
				})
		})
		return ctx.Theorem(headline, func(
			arg *Argument,
			k Fact,
			a, b, e *Expr[A],
			aIn, bIn, eIn, eNonzero Fact,
		) {
			ring := field.RingOn.Read(k)
			arg.Show(
				"the scaling is one-to-one on the twisted curve and carries it onto y² = e·f(x)",
				SplitConj(
					Case(
						"two points of the twisted curve with one image agree, as e ≠ 0 cancels from each coordinate",
						Unfold(functions.InjectiveOnDef),
						Derive(func(c *Argument) {
							u := c.FixAs[Prod[A, A]]("u")
							v := c.FixAs[Prod[A, A]]("v")
							given := c.Conjuncts(
								c.Assume(),
								"u lies on the twisted curve",
								"so does v",
								"u and v have one image")
							onU := c.Conjuncts(
								given[0],
								"the first coordinate of u lies in k",
								"so does its second",
								"the twisted equation at u")
							onV := c.Conjuncts(
								given[1],
								"the first coordinate of v lies in k",
								"so does its second",
								"the twisted equation at v")
							scaled := c.Simplified(given[2], Fwd(pairs.PairEq))
							parts := c.Have(
								"e ≠ 0 cancels from e·fst(u) = e·fst(v) and from e²·snd(u) = e²·snd(v)",
								"fst(u) = fst(v) ∧ snd(u) = snd(v)",
								ByArith(k, eNonzero, eIn, onU[0], onU[1], onV[0], onV[1], scaled))
							c.Show(
								"a pair is its two coordinates",
								By(parts, pairs.PairEta.At(u), pairs.PairEta.At(v)))
						})),
					Case(
						"the image and y² = e·f(x) have the same points",
						Simp(Fwd(set_basic.Extension)),
						Derive(func(c *Argument) {
							c.FixAs[Prod[A, A]]("p")
							c.Iff()
							c.Forward(
								"the image of a point u of the twisted curve lies on y² = e·f(x)",
								func(d *Argument, inImage Fact) {
									_, preimage := d.UnpackAs[Prod[A, A]](d.Simplified(inImage, Fwd(set_basic.InImage)), "u")
									given := d.Conjuncts(
										preimage,
										"p is the image of u",
										"u lies on the twisted curve")
									onU := d.Conjuncts(
										given[1],
										"the first coordinate of u lies in k",
										"so does its second",
										"the twisted equation at u")
									scaledAtU := d.Have(
										"the twisted equation at u, multiplied by e⁴",
										"e * e * snd(u) * (e * e * snd(u)) = "+
											"e * (e * fst(u) * (e * fst(u) * (e * fst(u))) + a * (e * fst(u)) + b)",
										By(
											aIn,
											bIn,
											eIn,
											eNonzero,
											onU[0],
											onU[1],
											onU[2],
											Read(rescaled, k).At(a, b, e, d.TermAs[A]("fst(u)"), d.TermAs[A]("snd(u)"))))
									d.Show(
										"so p, which is (e·fst(u), e²·snd(u)), lies on it, its coordinates being products in k",
										given[0].Rw(),
										By(scaledAtU, eIn, onU[0], onU[1], comm_ring.MulIn.Read(ring), pairs.Fst, pairs.Snd))
								})
							c.Backward(
								"a point of y² = e·f(x) is the image of its coordinates scaled by e⁻¹ and e⁻²",
								func(d *Argument, onScaled Fact) {
									given := d.Conjuncts(
										onScaled,
										"the first coordinate of p lies in k",
										"so does its second",
										"p lies on y² = e·f(x)")
									X, XDef := d.LetAs[A]("X", "k.inv(e) * fst(p)")
									Y, YDef := d.LetAs[A]("Y", "k.inv(e) * k.inv(e) * snd(p)")
									inK := d.Have(
										"X and Y are products in k",
										"X ∈ k.carrier ∧ Y ∈ k.carrier",
										By(XDef, YDef, eIn, given[0], given[1], field.InvIn.Read(k), comm_ring.MulIn.Read(ring)))
									back := d.Have(
										"scaling X by e and Y by e² returns the coordinates of p",
										"e * X = fst(p) ∧ e * e * Y = snd(p)",
										ByArith(k, eNonzero, XDef, YDef, eIn, given[0], given[1]))
									twisted := d.Have(
										"so (X, Y) lies on the twisted curve",
										"Y * Y = "+
											"X * (X * X) + fst(twist_coefficients(k, a, b, e)) * X + snd(twist_coefficients(k, a, b, e))",
										By(aIn, bIn, eIn, eNonzero, inK, back, given[2], Read(rescaled, k).At(a, b, e, X, Y)))
									d.Show(
										"p is the image of (X, Y)",
										Simp(Fwd(set_basic.InImage)),
										Witness(d.TermAs[Prod[A, A]]("(X, Y)")),
										By(Normalized, back, inK, twisted, pairs.Fst, pairs.Snd, pairs.PairEta))
								})
						})),
				))
		})
	}),
})}

// AffineSolutionsPairing — over a finite field with 2 ≠ 0 and a nonsquare e,
// the equations y² = f(x₀) and y² = e·f(x₀) have two solutions between them,
// for f(x) = x³ + ax + b: f(x₀) lies in k, and an element and its twist by a
// nonsquare have two square roots between them
// (finite_field.SquareRootsWithTwistTotalTwo).
var AffineSolutionsPairing = affineSolutionsPairingThm{family.Add(registry.ProofEntry{
	Name: "AffineSolutionsPairing",
	Key:  "prop_cc4032842aa2673",
	Build: family.Theorem(Statement{
		Binders: "∀k:field_on(A). ∀a b e x₀:A.",
		Hypotheses: []string{
			"finite(k.carrier)",
			"k.one + k.one ≠ k.zero",
			"a ∈ k.carrier",
			"b ∈ k.carrier",
			"e ∈ k.carrier",
			"e ≠ k.zero",
			"¬∃z:A. z ∈ k.carrier ∧ z * z = e",
			"x₀ ∈ k.carrier",
		},
		Conclusion: "card({z:A | z ∈ k.carrier ∧ z * z = x₀ * (x₀ * x₀) + a * x₀ + b}) + " +
			"card({z:A | z ∈ k.carrier ∧ z * z = e * (x₀ * (x₀ * x₀) + a * x₀ + b)}) = " +
			"2",
	}, func(
		arg *Argument,
		k Fact,
		a, b, e, x0 *Expr[A],
		finite, two, aIn, bIn, eIn, eNonzero, eNoRoot, xIn Fact,
	) {
		ring := field.RingOn.Read(k)
		times, plus := comm_ring.MulIn.Read(ring), comm_ring.AddIn.Read(ring)
		am := arg.MemberOf[on.Any](a, aIn)
		bm := arg.MemberOf[on.Any](b, bIn)
		xm := arg.MemberOf[on.Any](x0, xIn)
		// f(x₀) = x₀·(x₀·x₀) + a·x₀ + b, an element of k by the ring's closure laws
		value := plus.At(plus.At(times.At(xm, times.At(xm, xm)), times.At(am, xm)), bm)
		arg.Show(
			"f(x₀) and its twist e·f(x₀) have two square roots between them, e having none",
			By(
				finite,
				two,
				eNonzero,
				eNoRoot,
				finite_field.SquareRootsWithTwistTotalTwo.Read(k).At(arg.MemberOf[on.Any](e, eIn), value)))
	}),
})}

var TwistCountSum = twistCountSumThm{family.Add(registry.ProofEntry{
	Name: "TwistCountSum",
	Key:  "prop_4bfafc6d36f1205d",
	Deps: []registry.EntryLike{
		twistCoefficientsDef,
		AffineSolutionsPairing,
		TwistSolutionBijection,
		cardinality.CardEqBijection,
	},
	Reading: "",
	Build: family.Card(Statement{
		Binders: "∀k:field_on(A). ∀a b e:A.",
		Hypotheses: []string{
			"finite(k.carrier)",
			"k.one + k.one ≠ k.zero",
			"a ∈ k.carrier",
			"b ∈ k.carrier",
			"e ∈ k.carrier",
			"e ≠ k.zero",
			"¬∃z:A. z ∈ k.carrier ∧ z * z = e",
		},
		Conclusion: "affine_solution_count(field_ring(k), a, b) + " +
			"affine_solution_count(field_ring(k), " +
			"    fst(twist_coefficients(k, a, b, e)), " +
			"    snd(twist_coefficients(k, a, b, e))) = " +
			"2 * card(k.carrier)",
	},
		"Count the fibers over x₀ in the finite set k. AffineSolutionsPairing "+
			"gives two solutions in each paired fiber; TwistSolutionBijection "+
			"identifies the twisted-coefficient solution set with the scaled equation."),
})}

var TwistTrace = twistTraceThm{family.Add(registry.ProofEntry{
	Name: "TwistTrace",
	Key:  "prop_fe2f292208e65849",
	Deps: []registry.EntryLike{twistCoefficientsDef, TwistCountSum, closed_point.PointCountAffine},
	Reading: "This numerical trace identity applies to every model through " +
		"PointCountAffine. Coefficient images on another HOL carrier are compared " +
		"by the induced bijection of coordinate pairs inside the lower-bound proof.",
	Build: family.Card(Statement{
		Binders: "∀k:field_on(A). ∀a b e:A.",
		Hypotheses: []string{
			"finite(k.carrier)",
			"k.one + k.one ≠ k.zero",
			"a ∈ k.carrier",
			"b ∈ k.carrier",
			"e ∈ k.carrier",
			"e ≠ k.zero",
			"¬∃z:A. z ∈ k.carrier ∧ z * z = e",
		},
		Conclusion: "int_of_num(card(k.carrier)) - " +
			"int_of_num(affine_solution_count(field_ring(k), " +
			"        fst(twist_coefficients(k, a, b, e)), " +
			"        snd(twist_coefficients(k, a, b, e)))) = " +
			"-(int_of_num(card(k.carrier)) - int_of_num(affine_solution_count(field_ring(k), a, b)))",
	},
		"Subtract TwistCountSum from 2q in the integers. By PointCountAffine, q minus an "+
			"affine solution count is exactly q+1 minus the rational count of any model; thus the "+
			"two coefficient traces have opposite signs without choosing a public twisted model."),
})}
