// frobenius.go — the Frobenius tensor of a coefficient function on E×F: its sum grouped
// into rows, and its kernel, trivial when the orders on E are distinct.

package rational_point_bound

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/finite_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/valuation_order"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/regular_point"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/registry"
)

// FrobeniusCoefficient — a coefficient function with values in k, a field of s²
// elements: at a pair of E×F its value lies in k, and so does the s-th power of that
// value, whose s-th power is the value again.
var FrobeniusCoefficient = frobeniusCoefficientThm{family.Add(registry.ProofEntry{
	Name: "FrobeniusCoefficient",
	Key:  "prop_1b12c93fb8b87ba5",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k E F:set(A). ∀s:num. ∀d:(prod(A, A) → A). ∀x y:A.",
		Hypotheses: []string{
			"subfield(M, k)",
			"finite(k)",
			"card(k) = s * s",
			"∀p:prod(A, A). p ∈ set_cross(E, F) ⇒ d(p) ∈ k",
			"x ∈ E",
			"y ∈ F",
		},
		Conclusion: "d((x, y)) ∈ k ∧ «sPower»(d((x, y))) ∈ k ∧ «sPower»(«sPower»(d((x, y)))) = d((x, y))",
		Abbrev: Abbrev{
			{Name: "sPower", Text: "λz:A. monoid_pow(M.mul, M.one, z, s)"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k, E, F *Expr[Set[A]],
		s *Expr[Nat],
		d *Arrow[Prod[A, A], A],
		x, y *Expr[A],
		subfield, finiteK, square, coefficients, xIn, yIn Fact,
	) {
		pair := a.TermAs[Prod[A, A]]("(x, y)")
		inK := a.Have(
			"(x, y) lies in E×F, so its coefficient lies in k",
			"d((x, y)) ∈ k",
			By(xIn, yIn, coefficients.At(pair), set_product.InCross.At(E, F, x, y)))
		frobenius := a.Conjuncts(
			GroupPremises(subfield, finiteK, square, finite_field.SquareFieldFrobenius.Read(M).At(k, s)),
			"the s-th power is a Frobenius map of M",
			"and on k it is an involution")
		a.Show(
			"the involution acts on the coefficient",
			By(inK, frobenius[1].At(d.Apply(pair))))
	}),
})}

// FrobeniusTensorRows — the sum of the terms d(p)·(fst(p)·snd(p)^s) over E×F,
// grouped by rows. Write σ for the s-th power, a ring endomorphism of M and an
// involution of k: the row g(x) = Σ_y σ(d(x, y))·y has σ(g(x)) = Σ_y d(x, y)·σ(y),
// so the whole sum is Σ_x x·σ(g(x)).
var FrobeniusTensorRows = frobeniusTensorRowsThm{family.Add(registry.ProofEntry{
	Name: "FrobeniusTensorRows",
	Key:  "prop_807f684ca317a16c",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k E F:set(A). ∀s:num. ∀d:(prod(A, A) → A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"finite(k)",
			"card(k) = s * s",
			"finite(E)",
			"finite(F)",
			"E ⊆ M.carrier",
			"F ⊆ M.carrier",
			"∀p:prod(A, A). p ∈ set_cross(E, F) ⇒ d(p) ∈ k",
		},
		Conclusion: "module_sum(M.add, " +
			"    M.zero, " +
			"    set_cross(E, F), " +
			"    λp:prod(A, A). d(p) * (fst(p) * «sPower»(snd(p)))) = " +
			"module_sum(M.add, M.zero, E, λx:A. x * «sPower»(«row»(x)))",
		Abbrev: Abbrev{
			{Name: "sPower", Text: "λz:A. monoid_pow(M.mul, M.one, z, s)"},
			{Name: "row", Text: "λx:A. module_sum(M.add, M.zero, F, λy:A. «sPower»(d((x, y))) * y)"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k, E, F *Expr[Set[A]],
		s *Expr[Nat],
		d *Arrow[Prod[A, A], A],
		subfield, finiteK, square, finiteE, finiteF, EIn, FIn, coefficients Fact,
	) {
		ring := field.RingOn.Read(M)
		regular := module.RegularModuleOn.Read(ring)
		ops := a.TermAs[RingOps[A]]("field_ring(M)")
		power := a.TermAs[Fun[A, A]]("«sPower»")
		add := a.TermAs[Op[A]]("M.add")
		zero := a.TermAs[A]("M.zero")
		frobenius := a.Conjuncts(
			GroupPremises(subfield, finiteK, square, finite_field.SquareFieldFrobenius.Read(M).At(k, s)),
			"the s-th power is a Frobenius map of M",
			"and on k it is an involution")[0]
		powerMap := a.Have(
			"the s-th power is a ring endomorphism of M",
			"ring_homomorphism(field_ring(M), field_ring(M), «sPower»)",
			By(
				frobenius,
				ring_homomorphism.RingHomCongruence.At(
					ops, ops, a.TermAs[Fun[A, A]]("frobenius_power(field_ring(M), s)"), power),
				finite_field.FrobeniusPowerDef))
		powerOfSum := a.Have(
			"the s-th power maps a sum over F to the sum of the powers",
			Statement{
				Binders: "∀G:(A → A).",
				Hypotheses: []string{
					"∀y:A. y ∈ F ⇒ G(y) ∈ M.carrier",
				},
				Conclusion: "«sPower»(module_sum(M.add, M.zero, F, G)) = " +
					"module_sum(M.add, M.zero, F, λy:A. «sPower»(G(y)))",
			},
			Derive(func(b *Argument) {
				G := b.FixAs[Fun[A, A]]("G")
				summands := b.Assume()
				b.Show(
					"the power map is additive and keeps zero",
					By(
						summands,
						finiteF,
						module.ModuleSumMonoidHomomorphism.Read(comm_ring.AddMonoidOn.Read(ring)).AsFact().At(
							add,
							zero,
							power,
							F,
							G),
						ring_homomorphism.MapZero.Read(powerMap),
						ring_homomorphism.MapAdd.Read(powerMap)))
			}))
		memberships := a.Have(
			"the coordinates, the coefficient and the powers of the coefficient and of y lie in M",
			Statement{
				Binders: "∀x y:A.",
				Hypotheses: []string{
					"x ∈ E",
					"y ∈ F",
				},
				Conclusion: "x ∈ M.carrier ∧ " +
					"y ∈ M.carrier ∧ " +
					"d((x, y)) ∈ M.carrier ∧ " +
					"«sPower»(d((x, y))) ∈ M.carrier ∧ " +
					"«sPower»(y) ∈ M.carrier",
			},
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				y := b.FixAs[A]("y")
				both := b.Assume()
				b.Show(
					"k, E and F lie in M, and M is closed under the power map",
					BySets(
						b.Simplified(GroupPremises(
							subfield,
							finiteK,
							square,
							coefficients,
							both,
							FrobeniusCoefficient.Read(M).At(k, E, F, s, d, x, y))),
						both,
						EIn,
						FIn,
						subfield,
						field.SubfieldSubset.At(a.TermAs[FieldOps[A]]("M"), k),
						ring_homomorphism.MapIn.Read(powerMap).AsFact().At(y)))
			}))
		rowPower := a.Have(
			"the power of a row is the sum of the coefficients times the powers of F",
			"∀x:A. x ∈ E ⇒ «sPower»(«row»(x)) = module_sum(M.add, M.zero, F, λy:A. d((x, y)) * «sPower»(y))",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				xIn := b.Assume()
				entries := b.Have(
					"the power of an entry of the row is the coefficient times the power of y",
					Statement{
						Binders: "∀y:A.",
						Hypotheses: []string{
							"y ∈ F",
						},
						Conclusion: "«sPower»(d((x, y))) * y ∈ M.carrier ∧ " +
							"«sPower»(«sPower»(d((x, y))) * y) = d((x, y)) * «sPower»(y)",
					},
					Derive(func(c *Argument) {
						y := c.FixAs[A]("y")
						yIn := c.Assume()
						twice := c.Simplified(GroupPremises(
							subfield,
							finiteK,
							square,
							coefficients,
							xIn,
							yIn,
							FrobeniusCoefficient.Read(M).At(k, E, F, s, d, x, y)))
						c.Show(
							"the power map is multiplicative, and the involution undoes the power of the coefficient",
							By(
								xIn,
								yIn,
								memberships.At(x, y),
								twice,
								ring_homomorphism.MapMul.Read(powerMap).AsFact().At(c.TermAs[A]("«sPower»(d((x, y)))"), y),
								comm_ring.MulIn.Read(ring)))
					}))
				b.Show(
					"take the power of the sum, then of each entry",
					CalcEq(
						Leg(
							b.TermAs[A]("module_sum(M.add, M.zero, F, λy:A. «sPower»(«sPower»(d((x, y))) * y))"),
							"the power map passes through the sum of the row",
							By(powerOfSum.At(b.TermAs[Fun[A, A]]("λy:A. «sPower»(d((x, y))) * y")), entries)),
						FinalLeg(
							"the power of each entry is the coefficient times the power of y",
							By(
								entries,
								module.ModuleSumCongruence.At(
									add,
									zero,
									F,
									b.TermAs[Fun[A, A]]("λy:A. «sPower»(«sPower»(d((x, y))) * y)"),
									b.TermAs[Fun[A, A]]("λy:A. d((x, y)) * «sPower»(y)"))))))
			}))
		rowTerm := a.Have(
			"multiplying a row's power by x distributes x over the entries",
			Statement{
				Binders: "∀x:A.",
				Hypotheses: []string{
					"x ∈ E",
				},
				Conclusion: "x * «sPower»(«row»(x)) = " +
					"module_sum(M.add, M.zero, F, λy:A. d((x, y)) * (x * «sPower»(y)))",
			},
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				xIn := b.Assume()
				regrouped := b.Have(
					"each entry regroups",
					Statement{
						Binders: "∀y:A.",
						Hypotheses: []string{
							"y ∈ F",
						},
						Conclusion: "d((x, y)) * «sPower»(y) ∈ M.carrier ∧ " +
							"x * (d((x, y)) * «sPower»(y)) = d((x, y)) * (x * «sPower»(y))",
					},
					Derive(func(c *Argument) {
						y := c.FixAs[A]("y")
						yIn := c.Assume()
						facts := c.Have(
							"x, the coefficient and the power of y lie in M",
							"x ∈ M.carrier ∧ d((x, y)) ∈ M.carrier ∧ «sPower»(y) ∈ M.carrier",
							By(xIn, yIn, memberships.At(x, y)))
						regroup := c.Have(
							"multiplication is commutative and associative",
							"x * (d((x, y)) * «sPower»(y)) = d((x, y)) * (x * «sPower»(y))",
							ByArith(M, facts))
						c.Show(
							"the product lies in M, and x regroups into it",
							By(facts, comm_ring.MulIn.Read(ring), regroup))
					}))
				xInM := b.Have(
					"x lies in M",
					"x ∈ M.carrier",
					BySets(xIn, EIn))
				b.Show(
					"x distributes over the power of the row, written as a sum",
					CalcEq(
						Leg(
							b.TermAs[A]("x * module_sum(M.add, M.zero, F, λy:A. d((x, y)) * «sPower»(y))"),
							"write out the power of the row",
							By(xIn, rowPower.At(x))),
						Leg(
							b.TermAs[A]("module_sum(M.add, M.zero, F, λy:A. x * (d((x, y)) * «sPower»(y)))"),
							"a multiple of a sum is the sum of the multiples",
							By(
								xInM,
								regrouped,
								finiteF,
								module.ModuleSumSmul.Read(regular).AsFact().At(
									F, x, b.TermAs[Fun[A, A]]("λy:A. d((x, y)) * «sPower»(y)")))),
						FinalLeg(
							"each multiple regroups",
							By(
								regrouped,
								module.ModuleSumCongruence.At(
									add,
									zero,
									F,
									b.TermAs[Fun[A, A]]("λy:A. x * (d((x, y)) * «sPower»(y))"),
									b.TermAs[Fun[A, A]]("λy:A. d((x, y)) * (x * «sPower»(y))"))))))
			}))
		termsIn := a.Have(
			"every term of the double sum lies in M",
			"∀x y:A. x ∈ E ∧ y ∈ F ⇒ d((x, y)) * (x * «sPower»(y)) ∈ M.carrier",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				y := b.FixAs[A]("y")
				both := b.Assume()
				b.Show(
					"M is closed under multiplication",
					By(both, memberships.At(x, y), comm_ring.MulIn.Read(ring)))
			}))
		crossed := a.Simplified(
			GroupPremises(
				finiteE,
				finiteF,
				termsIn,
				module.ModuleSumCross.Read(regular).AsFact().At(
					E, F, a.TermAs[Fun2[A, A, A]]("λx:A. λy:A. d((x, y)) * (x * «sPower»(y))"))),
			Fwd(pairs.PairEta))
		a.Show(
			"the sum over E×F is the double sum, and each inner sum is x times the power of its row",
			By(
				crossed,
				finiteE,
				finiteF,
				termsIn,
				rowTerm,
				module.ModuleSumCongruence.At(
					add,
					zero,
					E,
					a.TermAs[Fun[A, A]]("λx:A. x * «sPower»(«row»(x))"),
					a.TermAs[Fun[A, A]]("λx:A. module_sum(M.add, M.zero, F, λy:A. d((x, y)) * (x * «sPower»(y)))"))))
	}),
})}

// FrobeniusTensorInjectivity — the Frobenius tensor has trivial kernel: a coefficient
// function with values in k on E×F and tensor zero vanishes on E×F, when the orders on
// E are distinct and a < s. Group the sum into the rows of FrobeniusTensorRows: the
// terms x·σ(g(x)) have orders v(x) + s·v(g(x)), and these are pairwise different on the
// nonzero rows, since the orders on E are different and lie within a < s of one
// another. A nonzero row would then leave a nonzero sum (DistinctOrdersSumNonzero), so
// all rows vanish, and independence of F makes d vanish.
var FrobeniusTensorInjectivity = frobeniusTensorInjectivityThm{family.Add(registry.ProofEntry{
	Name: "FrobeniusTensorInjectivity",
	Key:  "prop_70858d60bafae960",
	Reading: "The bound a<s concerns every pole order, not merely the cardinality " +
		"of the basis. The tensor reads a coefficient function on E×F alone, so the " +
		"kernel is stated there: the values on E×F vanish, and nothing is said off it.",
	Build: family.Sections(Statement{
		Binders: "∀L:field_on(A). " +
			"∀k A₀ A₁ A₀₁:set(A). " +
			"∀t:A. " +
			"∀P:prod(set(A), set(A)). " +
			"∀a b s:num. " +
			"∀E F:set(A). " +
			"∀d:(prod(A, A) → A). " +
			"∀p:prod(A, A).",
		Hypotheses: []string{
			"«rbCurve»",
			"finite(k)",
			"«rbPoint»(P)",
			"card(k) = s * s",
			"finite(E)",
			"finite(F)",
			"module_basis(«rbScalars», «rbPoles»(a), E)",
			"module_basis(«rbScalars», «rbPoles»(b), F)",
			"a < s",
			"injective_on(E, «rbOrder»)",
			"∀q:prod(A, A). q ∈ set_cross(E, F) ⇒ d(q) ∈ k",
			"«rbTensor»(d) = L.zero",
			"p ∈ set_cross(E, F)",
		},
		Conclusion: "d(p) = L.zero",
		Abbrev: Abbrev{
			{Name: "sPower", Text: "λz:A. monoid_pow(L.mul, L.one, z, s)"},
			{Name: "row", Text: "λx:A. module_sum(L.add, L.zero, F, λy:A. «sPower»(d((x, y))) * y)"},
			{Name: "term", Text: "λx:A. x * «sPower»(«row»(x))"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		// Two integers within r of each other and below zero that agree modulo m > r
		// are equal: a nonzero multiple of m is out of reach of their difference.
		sameResidue := ctx.Lemma(Statement{
			Binders: "∀r m x y u w:int.",
			Hypotheses: []string{
				"&0 ≤ r",
				"r < m",
				"-r ≤ x",
				"x ≤ &0",
				"-r ≤ y",
				"y ≤ &0",
				"x + m * u = y + m * w",
			},
			Conclusion: "x = y",
		}, func(
			arg *Argument,
			r, m, x, y, u, w *Expr[Int],
			nonnegative, below, xLow, xHigh, yLow, yHigh, equal Fact,
		) {
			arg.Cases(arg.TermAs[Bool]("u < w"))
			arg.When(
				"m·(w − u) is at least m, more than the gap of x and y",
				func(b *Argument, lesser Fact) {
					step := b.Have(
						"the integers u and w differ by at least one",
						"u + &1 ≤ w",
						ByArith(lesser))
					b.Show(
						"the product of m with that gap is out of reach",
						ByArith(step, nonnegative, below, xLow, xHigh, yLow, yHigh, equal))
				})
			arg.Otherwise(
				"u is not below w",
				func(b *Argument, notLesser Fact) {
					b.Cases(b.TermAs[Bool]("w < u"))
					b.When(
						"m·(u − w) is at least m, more than the gap of x and y",
						func(e *Argument, greater Fact) {
							step := e.Have(
								"the integers u and w differ by at least one",
								"w + &1 ≤ u",
								ByArith(greater))
							e.Show(
								"the product of m with that gap is out of reach",
								ByArith(step, nonnegative, below, xLow, xHigh, yLow, yHigh, equal))
						})
					b.Otherwise(
						"u and w are equal, so the common multiple cancels",
						func(e *Argument, notGreater Fact) {
							same := e.Have(
								"neither of u and w is below the other",
								"u = w",
								ByArith(notLesser, notGreater))
							e.Show(
								"cancel the common multiple",
								ByArith(same, equal))
						})
				})
		})
		return ctx.Theorem(headline,
			func(
				arg *Argument,
				L field.FieldFact[on.L],
				k, A0, A1, A01 *Expr[Set[A]],
				t *Expr[A],
				P *Expr[_LatticePair],
				a, b, s *Expr[Nat],
				E, F *Expr[Set[A]],
				curve, finiteK, point, size, finiteE, finiteF, basisE, basisF, aBelow, distinctOrders Fact,
				d *Arrow[Prod[A, A], A],
				p *Expr[Prod[A, A]],
				coefficients, vanishes, inCross Fact,
			) {
				ring := field.RingOn.Read(L)
				zero := arg.TermAs[A]("L.zero")
				constants := arg.Have(
					"k is a subfield of L, lying in it",
					"subfield(L, k) ∧ k ⊆ L.carrier",
					By(
						GroupPremises(curve, algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, t)),
						field.SubfieldSubset.At(arg.TermAs[FieldOps[A]]("L"), k)))
				poleE := arg.Conjuncts(
					GroupPremises(
						curve, point, basisE, regular_point.PoleBasisInField.Read(L).At(k, A0, A1, A01, t, P, a, E)),
					"E lies in L",
					"E misses zero",
					"E is independent")
				poleF := arg.Conjuncts(
					GroupPremises(
						curve, point, basisF, regular_point.PoleBasisInField.Read(L).At(k, A0, A1, A01, t, P, b, F)),
					"F lies in L",
					"F misses zero",
					"F is independent")
				ops := arg.TermAs[RingOps[A]]("field_ring(L)")
				order := arg.TermAs[Fun[A, Int]]("«rbOrder»")
				valuation := arg.Have(
					"the order at the regular point is a valuation of L",
					"valuation_order(field_ring(L), «rbOrder»)",
					By(arg.Simplified(GroupPremises(
						curve, point, regular_point.RegularPointOrderAndFiltration.Read(L).At(k, A0, A1, A01, t, P)))))
				laws := arg.Unfolded(valuation, valuation_order.ValuationOrderDef)
				pointsOfE := arg.Have(
					"each point of E is a nonzero element of L and a pole function",
					"∀x:A. x ∈ E ⇒ x ∈ L.carrier ∧ x ≠ L.zero ∧ x ∈ «rbPoles»(a).carrier",
					BySets(poleE[0], poleE[1], basisE, linear_independence.BasisInCarrier))
				frobenius := arg.Conjuncts(
					GroupPremises(constants, finiteK, size, finite_field.SquareFieldFrobenius.Read(L).At(k, s)),
					"the s-th power is a Frobenius map of L",
					"and on k it is an involution")[0]
				powerZero := arg.Have(
					"the s-th power keeps zero",
					"«sPower»(L.zero) = L.zero",
					By(ring_homomorphism.MapZero.Read(frobenius), finite_field.FrobeniusPowerDef.At(ops, s, zero)))
				split := arg.Have(
					"the tensor of d is the sum of its rows' terms, which therefore vanishes",
					"module_sum(L.add, L.zero, E, «term») = L.zero",
					By(
						vanishes,
						constants,
						finiteK,
						size,
						finiteE,
						finiteF,
						poleE[0],
						poleF[0],
						coefficients,
						FrobeniusTensorRows.Read(L).At(k, E, F, s, d),
						frobeniusTensorDef.At(ops, E, F, s, d)))
				rowIn := arg.Have(
					"each row lies in L",
					"∀x:A. x ∈ E ⇒ «row»(x) ∈ L.carrier",
					Derive(func(e *Argument) {
						x := e.FixAs[A]("x")
						xInE := e.Assume()
						summands := e.Have(
							"each summand of the row lies in L",
							"∀y:A. y ∈ F ⇒ «sPower»(d((x, y))) * y ∈ L.carrier",
							Derive(func(f *Argument) {
								y := f.FixAs[A]("y")
								yIn := f.Assume()
								parts := f.Have(
									"the coefficient's power lies in k, inside L, and y lies in L",
									"«sPower»(d((x, y))) ∈ L.carrier ∧ y ∈ L.carrier",
									BySets(
										f.Simplified(GroupPremises(
											constants,
											finiteK,
											size,
											coefficients,
											xInE,
											yIn,
											FrobeniusCoefficient.Read(L).At(k, E, F, s, d, x, y))),
										yIn,
										poleF[0],
										constants))
								f.Show(
									"L is closed under multiplication",
									By(parts, comm_ring.MulIn.Read(ring)))
							}))
						e.Show(
							"L is closed under finite sums",
							By(finiteF, summands, module.ModuleSumInMonoid.Read(comm_ring.AddMonoidOn.Read(ring))))
					}))
				termsIn := arg.Have(
					"each term lies in L",
					"∀x:A. x ∈ E ⇒ «term»(x) ∈ L.carrier",
					Derive(func(e *Argument) {
						x := e.FixAs[A]("x")
						xIn := e.Assume()
						e.Show(
							"L is closed under powers and products",
							By(
								rowIn.At(x),
								pointsOfE.At(x),
								xIn,
								comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ring)),
								comm_ring.MulIn.Read(ring)))
					}))
				orderFormula := arg.Have(
					"a nonzero row gives a nonzero term, of the order of x plus s times the order of the row",
					Statement{
						Binders: "∀x:A.",
						Hypotheses: []string{
							"x ∈ E",
							"«row»(x) ≠ L.zero",
						},
						Conclusion: "«term»(x) ≠ L.zero ∧ «rbOrder»(«term»(x)) = «rbOrder»(x) + &s * «rbOrder»(«row»(x))",
					},
					Derive(func(e *Argument) {
						x := e.FixAs[A]("x")
						both := e.Conjuncts(
							e.Assume(),
							"x lies in E",
							"the row at x is nonzero")
						row := e.TermAs[A]("«row»(x)")
						rowInL := e.Have(
							"the row lies in L",
							"«row»(x) ∈ L.carrier",
							By(rowIn.At(x), both[0]))
						power := e.Have(
							"the power of the row is nonzero, of s times its order",
							"«sPower»(«row»(x)) ≠ L.zero ∧ «rbOrder»(«sPower»(«row»(x))) = &s * «rbOrder»(«row»(x))",
							By(valuation, both[1], rowInL, valuation_order.PowerOrder.Read(L).AsFact().At(order, row, s)))
						powered := e.TermAs[A]("«sPower»(«row»(x))")
						e.Show(
							"the order adds on a product of nonzero elements",
							ByArith(
								L,
								laws.At(x, powered),
								pointsOfE.At(x),
								both[0],
								power,
								rowInL,
								comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ring)).AsFact().At(row, s),
								field.MulEqZeroOn.Read(L).AsFact().At(x, powered)))
					}))
				coefficientRow := arg.Have(
					"a nonzero coefficient makes its row nonzero",
					"∀x y:A. x ∈ E ∧ y ∈ F ∧ d((x, y)) ≠ L.zero ⇒ «row»(x) ≠ L.zero",
					Derive(func(e *Argument) {
						x := e.FixAs[A]("x")
						y := e.FixAs[A]("y")
						hyps := e.Conjuncts(
							e.Assume(),
							"x lies in E",
							"y lies in F",
							"the coefficient is nonzero")
						vanishing := e.SupposeNot()
						inK := e.Have(
							"the powers of the coefficients of the row lie in k",
							"∀z:A. z ∈ F ⇒ «sPower»(d((x, z))) ∈ k",
							Derive(func(f *Argument) {
								z := f.FixAs[A]("z")
								zInF := f.Assume()
								f.Show(
									"the power of a coefficient stays in k",
									By(f.Simplified(GroupPremises(
										constants,
										finiteK,
										size,
										coefficients,
										hyps[0],
										zInF,
										FrobeniusCoefficient.Read(L).At(k, E, F, s, d, x, z)))))
							}))
						killed := e.Have(
							"F is independent, so the power of the coefficient vanishes",
							"«sPower»(d((x, y))) = L.zero",
							By(
								poleF[2].At(e.TermAs[Fun[A, A]]("λz:A. «sPower»(d((x, z)))"), y),
								finiteF,
								inK,
								vanishing,
								hyps[1]))
						e.Show(
							"the involution would make the coefficient the power of zero",
							By(
								e.Simplified(GroupPremises(
									constants,
									finiteK,
									size,
									coefficients,
									hyps[0],
									hyps[1],
									FrobeniusCoefficient.Read(L).At(k, E, F, s, d, x, y))),
								hyps[2],
								killed,
								powerZero))
					}))
				termRow := arg.Have(
					"a nonzero term has a nonzero row, the power of zero being zero",
					"∀x:A. x ∈ E ∧ «term»(x) ≠ L.zero ⇒ «row»(x) ≠ L.zero",
					Derive(func(e *Argument) {
						x := e.FixAs[A]("x")
						both := e.Assume()
						vanishing := e.SupposeNot()
						xInL := e.Have(
							"x lies in L",
							"x ∈ L.carrier",
							BySets(both, poleE[0]))
						e.Show(
							"x times zero is zero",
							By(vanishing, powerZero, both, xInL, comm_ring.MulRightZeroOn.Read(ring).AsFact().At(x)))
					}))
				bounds := arg.Have(
					"orders on E lie between −a and 0",
					"∀x:A. x ∈ E ⇒ -int_of_num(a) ≤ «rbOrder»(x) ∧ «rbOrder»(x) ≤ int_of_num(0)",
					Derive(func(e *Argument) {
						x := e.FixAs[A]("x")
						xIn := e.Assume()
						e.Show(
							"a nonzero function of the a-th pole space has order between −a and 0",
							By(
								curve,
								point,
								pointsOfE.At(x),
								xIn,
								regular_point.PoleOrderBounds.Read(L).At(k, A0, A1, A01, t, P, a, x)))
					}))
				injectiveE := arg.Unfolded(distinctOrders, functions.InjectiveOnDef)
				rowOrders := arg.Have(
					"terms of nonzero rows and of equal order come from one point of E",
					Statement{
						Binders: "∀x₁ x₂:A.",
						Hypotheses: []string{
							"x₁ ∈ E",
							"x₂ ∈ E",
							"«row»(x₁) ≠ L.zero",
							"«row»(x₂) ≠ L.zero",
							"«rbOrder»(«term»(x₁)) = «rbOrder»(«term»(x₂))",
						},
						Conclusion: "x₁ = x₂",
					},
					Derive(func(e *Argument) {
						x1 := e.FixAs[A]("x₁")
						x2 := e.FixAs[A]("x₂")
						h := e.Conjuncts(
							e.Assume(),
							"x₁ lies in E",
							"x₂ lies in E",
							"the row at x₁ is nonzero",
							"the row at x₂ is nonzero",
							"the two terms have one order")
						one := e.Have(
							"compare the two order formulas",
							"«rbOrder»(x₁) + &s * «rbOrder»(«row»(x₁)) = «rbOrder»(x₂) + &s * «rbOrder»(«row»(x₂))",
							By(orderFormula.At(x1), orderFormula.At(x2), h[0], h[1], h[2], h[3], h[4]))
						gaps := e.Have(
							"as integers, a is at least 0 and below s",
							"0 ≤ int_of_num(a) ∧ a < int_of_num(s)",
							ByArith(aBelow))
						same := e.Have(
							"s exceeds the gap of the two orders, so the two orders agree",
							"«rbOrder»(x₁) = «rbOrder»(x₂)",
							By(
								At(
									sameResidue,
									e.TermAs[Int]("a"),
									e.TermAs[Int]("s"),
									e.TermAs[Int]("«rbOrder»(x₁)"),
									e.TermAs[Int]("«rbOrder»(x₂)"),
									e.TermAs[Int]("«rbOrder»(«row»(x₁))"),
									e.TermAs[Int]("«rbOrder»(«row»(x₂))")),
								gaps,
								bounds.At(x1),
								bounds.At(x2),
								h[0],
								h[1],
								one))
						e.Show(
							"the order is injective on E",
							By(injectiveE.At(x1, x2), h[0], h[1], same))
					}))
				support := arg.Have(
					"the order of the terms is injective on the nonzero terms",
					"injective_on({x:A | x ∈ E ∧ «term»(x) ≠ L.zero}, λx:A. «rbOrder»(«term»(x)))",
					Unfold(functions.InjectiveOnDef),
					Derive(func(e *Argument) {
						x := e.FixAs[A]("x")
						y := e.FixAs[A]("y")
						both := e.Assume()
						e.Show(
							"nonzero terms have nonzero rows",
							By(rowOrders.At(x, y), termRow.At(x), termRow.At(y), both))
					}))
				nonzero := arg.SupposeNot()
				corners := arg.Have(
					"p lies in E×F through its coordinates",
					"fst(p) ∈ E ∧ snd(p) ∈ F",
					By(inCross, set_product.InCrossProjections.At(E, F, p)))
				x := arg.TermAs[A]("fst(p)")
				y := arg.TermAs[A]("snd(p)")
				termNonzero := arg.Have(
					"the term of fst(p) is nonzero",
					"«term»(fst(p)) ≠ L.zero",
					By(orderFormula.At(x), corners, coefficientRow.At(x, y), nonzero, pairs.PairEta.At(p)))
				arg.Show(
					"a sum of terms of different orders, not all zero, is nonzero, yet the sum vanishes",
					By(
						valuation_order.DistinctOrdersSumNonzero.Read(ring).AsFact().At(
							order, E, arg.TermAs[Fun[A, A]]("«term»"), x),
						valuation,
						finiteE,
						termsIn,
						corners,
						termNonzero,
						support,
						split))
			})
	}),
})}
