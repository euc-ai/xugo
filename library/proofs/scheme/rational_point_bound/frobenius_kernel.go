// frobenius_kernel.go — the nonzero tensor that vanishes off P: the s-th power of a
// twisted sum, the poles of the entries, a nonzero relation among the entries, and the
// tensor's values under the swap.

package rational_point_bound

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/finite_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/regular_point"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/registry"
)

// FrobeniusTwistSum — over values in a field k of s² elements, the s-th power of a sum
// of terms c * (u * v^s) is the sum of the terms c^s * (u^s * v). The s-th power map is
// a ring endomorphism of M, so it takes the sum term by term, and an involution of k,
// so it undoes the double power of v.
var FrobeniusTwistSum = frobeniusTwistSumThm{family.Add(registry.ProofEntry{
	Name: "FrobeniusTwistSum",
	Key:  "prop_48a22094c70787fa",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀s:num. ∀I:set(D). ∀c u v:(D → A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"finite(k)",
			"card(k) = s * s",
			"finite(I)",
			"∀p:D. p ∈ I ⇒ c(p) ∈ k ∧ u(p) ∈ k ∧ v(p) ∈ k",
		},
		Conclusion: "«pow»(module_sum(M.add, M.zero, I, λp:D. c(p) * (u(p) * «pow»(v(p))))) = " +
			"module_sum(M.add, M.zero, I, «swapped»)",
		Abbrev: Abbrev{
			{Name: "pow", Text: "λz:A. monoid_pow(M.mul, M.one, z, s)"},
			{Name: "twisted", Text: "λp:D. «pow»(c(p)) * («pow»(u(p)) * «pow»(«pow»(v(p))))"},
			{Name: "swapped", Text: "λp:D. «pow»(c(p)) * («pow»(u(p)) * v(p))"},
		},
	},
		func(
			arg *Argument,
			M field.FieldFact[on.M],
			k *Expr[Set[A]],
			s *Expr[Nat],
			I *Expr[Set[D]],
			c, u, v *Arrow[D, A],
			subfield, finiteK, size, finiteIndex, values Fact,
		) {
			frobenius := arg.Conjuncts(
				GroupPremises(subfield, finiteK, size, finite_field.SquareFieldFrobenius.Read(M).At(k, s)),
				"the s-th power map is a ring endomorphism of M",
				"and an involution of k")
			endomorphism, involution := frobenius[0], frobenius[1]
			kInM := arg.Have(
				"k lies in M",
				"k ⊆ M.carrier",
				By(subfield, field.SubfieldSubset.At(arg.TermAs[FieldOps[A]]("M"), k)))
			factors := arg.Have(
				"the factors of a term lie in M, and the involution undoes the double power of v",
				Statement{
					Binders:    "∀p:D.",
					Hypotheses: []string{"p ∈ I"},
					Conclusion: "c(p) ∈ M.carrier ∧ " +
						"u(p) ∈ M.carrier ∧ " +
						"«pow»(v(p)) ∈ M.carrier ∧ " +
						"«pow»(«pow»(v(p))) = v(p)",
				},
				Derive(func(b *Argument) {
					p := b.FixAs[D]("p")
					inIndex := b.Assume()
					constant := b.Have(
						"the three values lie in k",
						"c(p) ∈ k ∧ u(p) ∈ k ∧ v(p) ∈ k",
						By(inIndex, values.At(p)))
					twice := b.Have(
						"so do the powers of v, of which the second is v",
						"«pow»(v(p)) ∈ k ∧ «pow»(«pow»(v(p))) = v(p)",
						By(constant, involution.At(v.Apply(p))))
					b.Show(
						"and k lies in M",
						BySets(kInM, constant, twice))
				}))
			twisted := arg.Simplified(
				ring_homomorphism.RingMapProductSum.Read(endomorphism).At(
					I, c, u, arg.TermAs[Fun[D, A]]("λp:D. «pow»(v(p))")),
				Fwd(finite_field.FrobeniusPowerDef))
			arg.Show(
				"the power of the sum is the sum of the powers, and each term is then the swapped one",
				CalcEq(
					Leg(
						arg.TermAs[A]("module_sum(M.add, M.zero, I, «twisted»)"),
						"the endomorphism takes the sum term by term",
						By(finiteIndex, factors, twisted)),
					FinalLeg(
						"the involution undoes the double power of v",
						By(
							factors,
							module.ModuleSumCongruence.At(
								arg.TermAs[Op[A]]("M.add"),
								arg.TermAs[A]("M.zero"),
								I,
								arg.TermAs[Fun[D, A]]("«twisted»"),
								arg.TermAs[Fun[D, A]]("«swapped»"))))))
		}),
})}

// FrobeniusEntryPoles — a pair of basis members, with poles of order at most a and b,
// has s-th powers with poles of order at most s * a and s * b, and each of the two
// products the Frobenius sums twist has poles of order at most the sum of its factors'.
var FrobeniusEntryPoles = frobeniusEntryPolesThm{family.Add(registry.ProofEntry{
	Name: "FrobeniusEntryPoles",
	Key:  "prop_922a3c0d7a72392",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). " +
			"∀k A₀ A₁ A₀₁:set(A). " +
			"∀t:A. " +
			"∀P:prod(set(A), set(A)). " +
			"∀a b s:num. " +
			"∀E F:set(A). " +
			"∀p:prod(A, A).",
		Hypotheses: []string{
			"«rbCurve»",
			"«rbPoint»(P)",
			"E ⊆ «rbPoles»(a).carrier",
			"F ⊆ «rbPoles»(b).carrier",
			"p ∈ set_cross(E, F)",
		},
		Conclusion: "fst(p) ∈ «rbPoles»(a).carrier ∧ " +
			"snd(p) ∈ «rbPoles»(b).carrier ∧ " +
			"«pow»(fst(p)) ∈ «rbPoles»(s * a).carrier ∧ " +
			"«pow»(snd(p)) ∈ «rbPoles»(s * b).carrier ∧ " +
			"«pow»(fst(p)) * snd(p) ∈ «rbPoles»(s * a + b).carrier ∧ " +
			"fst(p) * «pow»(snd(p)) ∈ «rbPoles»(a + s * b).carrier",
		Abbrev: Abbrev{
			{Name: "pow", Text: "λz:A. monoid_pow(L.mul, L.one, z, s)"},
		},
	},
		func(
			arg *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			P *Expr[_LatticePair],
			a, b, s *Expr[Nat],
			E, F *Expr[Set[A]],
			p *Expr[Prod[A, A]],
			curve, point, inE, inF, pair Fact,
		) {
			first, second := arg.TermAs[A]("fst(p)"), arg.TermAs[A]("snd(p)")
			firstPower, secondPower := arg.TermAs[A]("«pow»(fst(p))"), arg.TermAs[A]("«pow»(snd(p))")
			coordinates := arg.Have(
				"the coordinates of p lie in the spaces of E and F",
				"fst(p) ∈ «rbPoles»(a).carrier ∧ snd(p) ∈ «rbPoles»(b).carrier",
				By(inE, inF, pair, set_product.InCrossProjections.At(E, F, p), set_basic.SubsetDef))
			powers := arg.Have(
				"the s-th powers multiply the orders of the poles by s",
				"«pow»(fst(p)) ∈ «rbPoles»(s * a).carrier ∧ «pow»(snd(p)) ∈ «rbPoles»(s * b).carrier",
				By(
					curve,
					point,
					coordinates,
					regular_point.PolePowerBudget.Read(L).At(k, A0, A1, A01, t, P, a, s, first),
					regular_point.PolePowerBudget.Read(L).At(k, A0, A1, A01, t, P, b, s, second)))
			arg.Show(
				"and the two products add them",
				By(
					curve,
					point,
					coordinates,
					powers,
					regular_point.PoleProductBudget.Read(L).At(
						k, A0, A1, A01, t, P, arg.TermAs[Nat]("s * a"), b, firstPower, second),
					regular_point.PoleProductBudget.Read(L).At(
						k, A0, A1, A01, t, P, a, arg.TermAs[Nat]("s * b"), first, secondPower)))
		}),
})}

// FrobeniusSwapEvaluation — for constant coefficients the tensor has poles of
// order at most a + s * b, and at a regular point Q other than P the s-th power of
// its value is the value of the swap. Functions with poles only at P are regular at
// Q, where the evaluation is a ring map to k fixing k and so keeping sums, products
// and powers: both sums evaluate term by term, the tensor to the sum of c(p) * (x *
// y^s) over the values and the swap to the sum of c(p)^s * (x^s * y). The s-th power
// takes the first sum to the second (FrobeniusTwistSum).
var FrobeniusSwapEvaluation = frobeniusSwapEvaluationThm{family.Add(registry.ProofEntry{
	Name: "FrobeniusSwapEvaluation",
	Key:  "prop_bfba6bedcba7d070",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). " +
			"∀k A₀ A₁ A₀₁:set(A). " +
			"∀t:A. " +
			"∀P:prod(set(A), set(A)). " +
			"∀a b s:num. " +
			"∀E F:set(A). " +
			"∀c:(prod(A, A) → A).",
		Hypotheses: []string{
			"«rbCurve»",
			"finite(k)",
			"«rbPoint»(P)",
			"card(k) = s * s",
			"finite(E)",
			"finite(F)",
			"E ⊆ «rbPoles»(a).carrier",
			"F ⊆ «rbPoles»(b).carrier",
			"∀p:prod(A, A). c(p) ∈ k",
		},
		Conclusion: "«rbTensor»(c) ∈ «rbPoles»(a + s * b).carrier ∧ " +
			"(∀Q:prod(set(A), set(A)). " +
			"    «rbPoint»(Q) ∧ Q ≠ P ⇒ " +
			"    «pow»(«rbEvaluation»(Q, «rbTensor»(c))) = «rbEvaluation»(Q, «rbSwap»(c)))",
		Abbrev: Abbrev{
			{Name: "pow", Text: "λz:A. monoid_pow(L.mul, L.one, z, s)"},
			{Name: "sum", Text: "module_sum(L.add, L.zero, set_cross(E, F))"},
			{Name: "tensorTerm", Text: "λp:prod(A, A). c(p) * (fst(p) * «pow»(snd(p)))"},
			{Name: "swapTerm", Text: "λp:prod(A, A). «pow»(c(p)) * («pow»(fst(p)) * snd(p))"},
			{Name: "local", Text: "point_local_ring(field_ring(L), A₀, A₁, Q)"},
			{Name: "value", Text: "«rbEvaluation»(Q)"},
			{Name: "imageOfTensor", Text: "λp:prod(A, A). " +
				"    «value»(c(p)) * («value»(fst(p)) * «value»(«pow»(snd(p))))"},
			{Name: "imageOfSwap", Text: "λp:prod(A, A). " +
				"    «value»(«pow»(c(p))) * («value»(«pow»(fst(p))) * «value»(snd(p)))"},
			{Name: "valuedTensor", Text: "λp:prod(A, A). c(p) * («value»(fst(p)) * «pow»(«value»(snd(p))))"},
			{Name: "valuedSwap", Text: "λp:prod(A, A). " +
				"    «pow»(c(p)) * («pow»(«value»(fst(p))) * «value»(snd(p)))"},
		},
	},
		func(
			arg *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			P *Expr[_LatticePair],
			a, b, s *Expr[Nat],
			E, F *Expr[Set[A]],
			c *Arrow[Prod[A, A], A],
			curve, finiteK, point, size, finiteE, finiteF, inE, inF, coefficients Fact,
		) {
			constants := arg.Have(
				"k is a subfield of L",
				"subfield(L, k)",
				By(GroupPremises(curve, algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, t))))
			involution := arg.Conjuncts(
				GroupPremises(constants, finiteK, size, finite_field.SquareFieldFrobenius.Read(L).At(k, s)),
				"the s-th power map is a ring endomorphism of L",
				"and an involution of k")[1]
			add, zero := arg.TermAs[Op[A]]("L.add"), arg.TermAs[A]("L.zero")
			cross := arg.TermAs[Set[Prod[A, A]]]("set_cross(E, F)")
			first, second := arg.TermAs[Fun[Prod[A, A], A]]("fst"), arg.TermAs[Fun[Prod[A, A], A]]("snd")
			tensorTerm := arg.TermAs[Fun[Prod[A, A], A]]("«tensorTerm»")
			finiteCross := arg.Have(
				"the index set is finite",
				"finite(set_cross(E, F))",
				By(finiteE, finiteF, finite_set.FiniteProduct.At(E, F)))
			tensorSum := arg.Have(
				"the tensor is the sum of its terms",
				"«rbTensor»(c) = «sum»(«tensorTerm»)",
				By(frobeniusTensorDef))
			swapSum := arg.Have(
				"the swap is the sum of its terms",
				"«rbSwap»(c) = «sum»(«swapTerm»)",
				By(frobeniusSwapDef))
			factorPoles := arg.Have(
				"the factors of a term have poles of order at most a, "+
					"b, s * a and s * b, their product at most a + s * b",
				Statement{
					Binders:    "∀p:prod(A, A).",
					Hypotheses: []string{"p ∈ set_cross(E, F)"},
					Conclusion: "fst(p) ∈ «rbPoles»(a).carrier ∧ " +
						"snd(p) ∈ «rbPoles»(b).carrier ∧ " +
						"«pow»(fst(p)) ∈ «rbPoles»(s * a).carrier ∧ " +
						"«pow»(snd(p)) ∈ «rbPoles»(s * b).carrier ∧ " +
						"fst(p) * «pow»(snd(p)) ∈ «rbPoles»(a + s * b).carrier",
				},
				arg.ForEach(func(p *Expr[Prod[A, A]]) Action {
					return By(
						curve,
						point,
						inE,
						inF,
						FrobeniusEntryPoles.Read(L).At(k, A0, A1, A01, t, P, a, b, s, E, F, p))
				}))
			poles := arg.Have(
				"the pole space of the tensor is a module over k",
				"module_on(«rbScalars», «rbPoles»(a + s * b))",
				By(
					curve,
					point,
					regular_point.PoleSpaceModule.Read(L).At(k, A0, A1, A01, t, P, arg.TermAs[Nat]("a + s * b"))))
			terms := arg.Have(
				"each term of the tensor scales a member of that space by a constant",
				Statement{
					Binders:    "∀p:prod(A, A).",
					Hypotheses: []string{"p ∈ set_cross(E, F)"},
					Conclusion: "c(p) * (fst(p) * «pow»(snd(p))) ∈ «rbPoles»(a + s * b).carrier",
				},
				Derive(func(d *Argument) {
					p := d.FixAs[Prod[A, A]]("p")
					inCross := d.Assume()
					d.Show(
						"a space is closed under scaling",
						By(
							inCross,
							factorPoles.At(p),
							coefficients.At(p),
							module.SmulIn.Read(poles).AsFact().At(c.Apply(p), d.TermAs[A]("fst(p) * «pow»(snd(p))"))))
				}))
			tensorPoles := arg.Have(
				"so the tensor lies in that space",
				"«rbTensor»(c) ∈ «rbPoles»(a + s * b).carrier",
				tensorSum.Rw(),
				By(finiteCross, terms, poles, module.ModuleSumIn.Read(poles).AsFact().At(cross, tensorTerm)))
			pointOrder := At(Read(regular_point.RegularPointOrderAndFiltration, L), k, A0, A1, A01, t)
			evaluation := arg.Have(
				"at a regular point other than P the s-th power of the tensor's value is the value of the swap",
				Statement{
					Binders:    "∀Q:prod(set(A), set(A)).",
					Hypotheses: []string{"«rbPoint»(Q)", "Q ≠ P"},
					Conclusion: "«pow»(«rbEvaluation»(Q, «rbTensor»(c))) = «rbEvaluation»(Q, «rbSwap»(c))",
				},
				Derive(func(d *Argument) {
					Q := d.FixAs[_LatticePair]("Q")
					where := d.Conjuncts(
						d.Assume(),
						"Q is a regular point",
						"Q is not P")
					other, away := where[0], where[1]
					regularAtQ := d.Have(
						"a function with poles only at P is regular at Q",
						"∀f:A. ∀n:num. f ∈ «rbPoles»(n).carrier ⇒ f ∈ «local»",
						By(other, away, d.Simplified(GroupPremises(curve, point, pointOrder.At(P)))))
					data := d.Conjuncts(
						d.Have(
							"the evaluation at Q, on the local ring",
							"ring_homomorphism(restrict_ring(field_ring(L), «local»), «rbScalars», «value») ∧ "+
								"(∀z:A. z ∈ k ⇒ «value»(z) = z) ∧ "+
								"(∀f:A. f ∈ «local» ⇒ «value»(f) ∈ k)",
							By(d.Simplified(GroupPremises(curve, other, pointOrder.At(Q))))),
						"is a ring map to k",
						"fixes k",
						"and takes its values in k")
					ringMap, fixed, valued := data[0], data[1], data[2]
					constantPoles := d.Have(
						"the zeroth pole space is k",
						"«rbPoles»(0).carrier = k",
						By(curve, point, regular_point.SinglePointPoleFiltration.Read(L).At(k, A0, A1, A01, t, P)))
					constantsAtQ := d.Have(
						"so constants are regular at Q",
						"∀z:A. z ∈ k ⇒ z ∈ «local»",
						Derive(func(e *Argument) {
							z := e.FixAs[A]("z")
							constant := e.Assume()
							inZeroth := e.Have(
								"z lies in the zeroth pole space",
								"z ∈ «rbPoles»(0).carrier",
								By(Normalized, constantPoles, constant))
							e.Show(
								"which is regular at Q",
								By(inZeroth, regularAtQ.At(z, e.TermAs[Nat]("0"))))
						}))
					factors := d.Have(
						"every factor of every term is regular at Q",
						Statement{
							Binders:    "∀p:prod(A, A).",
							Hypotheses: []string{"p ∈ set_cross(E, F)"},
							Conclusion: "c(p) ∈ «local» ∧ " +
								"«pow»(c(p)) ∈ «local» ∧ " +
								"fst(p) ∈ «local» ∧ " +
								"snd(p) ∈ «local» ∧ " +
								"«pow»(fst(p)) ∈ «local» ∧ " +
								"«pow»(snd(p)) ∈ «local»",
						},
						Derive(func(e *Argument) {
							p := e.FixAs[Prod[A, A]]("p")
							inCross := e.Assume()
							poleOrders := e.Simplified(GroupPremises(inCross, factorPoles.At(p)))
							coefficient := c.Apply(p)
							e.Show(
								"the coefficients are constants, the other factors have poles only at P",
								By(
									inCross,
									poleOrders,
									coefficients.At(p),
									involution.At(coefficient),
									constantsAtQ.At(coefficient),
									constantsAtQ.At(e.TermAs[A]("«pow»(c(p))")),
									regularAtQ.At(e.TermAs[A]("fst(p)"), a),
									regularAtQ.At(e.TermAs[A]("snd(p)"), b),
									regularAtQ.At(e.TermAs[A]("«pow»(fst(p))"), e.TermAs[Nat]("s * a")),
									regularAtQ.At(e.TermAs[A]("«pow»(snd(p))"), e.TermAs[Nat]("s * b"))))
						}))
					valuesOfFactors := d.Have(
						"on the factors the evaluation fixes the constants and commutes with the s-th power",
						Statement{
							Binders:    "∀p:prod(A, A).",
							Hypotheses: []string{"p ∈ set_cross(E, F)"},
							Conclusion: "«value»(c(p)) = c(p) ∧ " +
								"«value»(«pow»(c(p))) = «pow»(c(p)) ∧ " +
								"«value»(«pow»(fst(p))) = «pow»(«value»(fst(p))) ∧ " +
								"«value»(«pow»(snd(p))) = «pow»(«value»(snd(p)))",
						},
						Derive(func(e *Argument) {
							p := e.FixAs[Prod[A, A]]("p")
							inCross := e.Assume()
							coefficient := c.Apply(p)
							left, right := e.TermAs[A]("fst(p)"), e.TermAs[A]("snd(p)")
							isConstant := e.Have(
								"the coefficient and its power are constants",
								"c(p) ∈ k ∧ «pow»(c(p)) ∈ k",
								By(coefficients.At(p), involution.At(coefficient)))
							regularFactors := e.Simplified(GroupPremises(inCross, factors.At(p)))
							e.Show(
								"the evaluation is the identity on k and a ring map on the local ring",
								By(
									inCross,
									isConstant,
									regularFactors,
									fixed.At(coefficient),
									fixed.At(e.TermAs[A]("«pow»(c(p))")),
									ring_homomorphism.RingMapPower.Read(ringMap).AsFact().At(s, left),
									ring_homomorphism.RingMapPower.Read(ringMap).AsFact().At(s, right)))
						}))
					constantFactors := d.Have(
						"the coefficients and the values of the coordinates are constants",
						"∀p:prod(A, A). p ∈ set_cross(E, F) ⇒ c(p) ∈ k ∧ «value»(fst(p)) ∈ k ∧ «value»(snd(p)) ∈ k",
						Derive(func(e *Argument) {
							p := e.FixAs[Prod[A, A]]("p")
							inCross := e.Assume()
							regularFactors := e.Simplified(GroupPremises(inCross, factors.At(p)))
							e.Show(
								"the evaluation takes its values in k",
								By(
									inCross,
									regularFactors,
									coefficients.At(p),
									valued.At(e.TermAs[A]("fst(p)")),
									valued.At(e.TermAs[A]("snd(p)"))))
						}))
					imageOfTensor := d.TermAs[Fun[Prod[A, A], A]]("«imageOfTensor»")
					imageOfSwap := d.TermAs[Fun[Prod[A, A], A]]("«imageOfSwap»")
					valuedTensor := d.TermAs[Fun[Prod[A, A], A]]("«valuedTensor»")
					valuedSwap := d.TermAs[Fun[Prod[A, A], A]]("«valuedSwap»")
					tensorValue := d.Have(
						"a ring map takes the tensor term by term",
						"«value»(«sum»(«tensorTerm»)) = «sum»(«imageOfTensor»)",
						By(
							ringMap,
							finiteCross,
							factors,
							ring_homomorphism.RingMapProductSum.Read(ringMap).At(
								cross, c, first, d.TermAs[Fun[Prod[A, A], A]]("λp:prod(A, A). «pow»(snd(p))"))))
					tensorTerms := d.Have(
						"which fixes the coefficients and commutes with the power of y",
						"«sum»(«imageOfTensor») = «sum»(«valuedTensor»)",
						By(valuesOfFactors, module.ModuleSumCongruence.At(add, zero, cross, imageOfTensor, valuedTensor)))
					swapValue := d.Have(
						"likewise it takes the swap term by term",
						"«value»(«sum»(«swapTerm»)) = «sum»(«imageOfSwap»)",
						By(
							ringMap,
							finiteCross,
							factors,
							ring_homomorphism.RingMapProductSum.Read(ringMap).At(
								cross,
								d.TermAs[Fun[Prod[A, A], A]]("λp:prod(A, A). «pow»(c(p))"),
								d.TermAs[Fun[Prod[A, A], A]]("λp:prod(A, A). «pow»(fst(p))"),
								second)))
					swapTerms := d.Have(
						"which fixes the twisted coefficients and commutes with the power of x",
						"«sum»(«imageOfSwap») = «sum»(«valuedSwap»)",
						By(valuesOfFactors, module.ModuleSumCongruence.At(add, zero, cross, imageOfSwap, valuedSwap)))
					d.Show(
						"evaluate the tensor, take the power, and evaluate the swap back",
						CalcEq(
							Leg(
								d.TermAs[A]("«pow»(«sum»(«valuedTensor»))"),
								"the tensor evaluates term by term",
								By(tensorSum, tensorValue, tensorTerms)),
							Leg(
								d.TermAs[A]("«sum»(«valuedSwap»)"),
								"the s-th power takes that sum to the swapped one, over values in k",
								By(
									constants,
									finiteK,
									size,
									finiteCross,
									constantFactors,
									FrobeniusTwistSum.Read(L).At(
										k,
										s,
										cross,
										c,
										d.TermAs[Fun[Prod[A, A], A]]("λp:prod(A, A). «value»(fst(p))"),
										d.TermAs[Fun[Prod[A, A], A]]("λp:prod(A, A). «value»(snd(p))")))),
							FinalLeg(
								"which is the swap, evaluated term by term",
								By(swapSum, swapValue, swapTerms))))
				}))
			arg.Show(
				"the tensor lies in the pole space, and the power of its value is the value of the swap",
				By(tensorPoles, evaluation))
		}),
})}

// FrobeniusEntryKernel — a constant-coefficient relation among the products x^s y:
// they lie in the space of poles of order at most s * a + b, and the free module on
// the pairs has more dimensions than that space, so the linear map with these
// entries kills a nonzero vector, its coefficients constants, its support finite in
// the pairs. Over the pairs, the value of the map at that vector is the relation.
var FrobeniusEntryKernel = frobeniusEntryKernelThm{family.Add(registry.ProofEntry{
	Name: "FrobeniusEntryKernel",
	Key:  "prop_ae996e48d15a2a8c",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). " +
			"∀k A₀ A₁ A₀₁:set(A). " +
			"∀t:A. " +
			"∀P:prod(set(A), set(A)). " +
			"∀a b s:num. " +
			"∀E F:set(A).",
		Hypotheses: []string{
			"«rbCurve»",
			"«rbPoint»(P)",
			"finite(E)",
			"finite(F)",
			"E ⊆ «rbPoles»(a).carrier",
			"F ⊆ «rbPoles»(b).carrier",
			"card(E) * card(F) > s * a + b + 1",
		},
		Conclusion: "∃d:(prod(A, A) → A). " +
			"    d ∈ finite_supp(L.zero, k, set_cross(E, F)) ∧ " +
			"    (∃q:prod(A, A). d(q) ≠ L.zero) ∧ " +
			"    module_sum(L.add, L.zero, set_cross(E, F), λp:prod(A, A). d(p) * «entry»(p)) = L.zero",
		Abbrev: Abbrev{
			{Name: "pow", Text: "λz:A. monoid_pow(L.mul, L.one, z, s)"},
			{Name: "entry", Text: "λp:prod(A, A). «pow»(fst(p)) * snd(p)"},
			{Name: "target", Text: "«rbPoles»(s * a + b)"},
			{Name: "free", Text: "free_module_record(«rbScalars», set_cross(E, F))"},
			{Name: "lift", Text: "free_lift(L.zero, L.add, L.zero, L.mul, «entry»)"},
			{Name: "kernelTerm", Text: "λp:prod(A, A). d(p) * «entry»(p)"},
		},
	},
		func(
			arg *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			P *Expr[_LatticePair],
			a, b, s *Expr[Nat],
			E, F *Expr[Set[A]],
			curve, point, finiteE, finiteF, inE, inF, large Fact,
		) {
			scalars := arg.TermAs[RingOps[A]]("«rbScalars»")
			inverse := arg.TermAs[Fun[A, A]]("L.inv")
			cross := arg.TermAs[Set[Prod[A, A]]]("set_cross(E, F)")
			add, zero := arg.TermAs[Op[A]]("L.add"), arg.TermAs[A]("L.zero")
			target := arg.TermAs[module_record.ModuleOps[A, A]]("«target»")
			free := arg.TermAs[module_record.ModuleOps[A, Fun[Prod[A, A], A]]]("«free»")
			entry := arg.TermAs[Fun[Prod[A, A], A]]("«entry»")
			lift := arg.TermAs[Fun[Fun[Prod[A, A], A], A]]("«lift»")
			constants := arg.Have(
				"k is a subfield of L",
				"subfield(L, k)",
				By(GroupPremises(curve, algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, t))))
			inTarget := arg.Have(
				"the entries x^s y have poles of order at most s * a + b",
				"∀p:prod(A, A). p ∈ set_cross(E, F) ⇒ «entry»(p) ∈ «target».carrier",
				arg.ForEach(func(p *Expr[Prod[A, A]]) Action {
					return By(
						curve,
						point,
						inE,
						inF,
						FrobeniusEntryPoles.Read(L).At(k, A0, A1, A01, t, P, a, b, s, E, F, p))
				}))
			scalarField := arg.Have(
				"the constants are a field",
				"ring_subfield(«rbScalars», L.inv, «rbScalars».carrier)",
				By(constants, field.SubfieldRingSubfield.Read(L).At(k, k)))
			targetOn := arg.Have(
				"the target of the entries is a module over k",
				"module_on(«rbScalars», «target»)",
				By(
					curve,
					point,
					regular_point.PoleSpaceModule.Read(L).At(k, A0, A1, A01, t, P, arg.TermAs[Nat]("s * a + b"))))
			targetDim := arg.Have(
				"it is finite-dimensional, of dimension at most s * a + b + 1",
				"finite_dimensional(«rbScalars», «target») ∧ module_dim(«rbScalars», «target») ≤ s * a + b + 1",
				By(curve, point, regular_point.SinglePointPoleFiltration.Read(L).At(k, A0, A1, A01, t, P)))
			finiteCross := arg.Have(
				"the pairs are finite",
				"finite(set_cross(E, F))",
				By(finiteE, finiteF, finite_set.FiniteProduct.At(E, F)))
			freeDim := arg.Have(
				"the free module on the pairs has their number as its dimension",
				"module_dim(«rbScalars», «free») = card(E) * card(F)",
				By(
					scalarField,
					finiteCross,
					module_dimension.FreeModuleDim.At(scalars, inverse, cross),
					finiteE,
					finiteF,
					cardinality.CardProduct.At(E, F)))
			freeFinite := arg.Have(
				"its generators are finitely many, so it is finite-dimensional",
				"finite_dimensional(«rbScalars», «free»)",
				By(
					finiteCross,
					free_module.DeltaAtBasis.Read(module.RingOn.Read(targetOn)).At(cross),
					finite_set.FiniteImage.At(
						arg.TermAs[Fun[Prod[A, A], Fun[Prod[A, A], A]]]("delta_at(«rbScalars».zero, «rbScalars».one)"),
						cross),
					module_dimension.FiniteDimensionalDef.At(scalars, free)))
			homomorphism := arg.Have(
				"the entries extend to a homomorphism of the free module into their space",
				"module_homomorphism(«rbScalars», «free», «target», «lift»)",
				By(inTarget, targetOn, free_module.FreeLiftHom.Read(targetOn).At(cross, entry)))
			smaller := arg.Have(
				"the target has the smaller dimension",
				"module_dim(«rbScalars», «target») < module_dim(«rbScalars», «free»)",
				ByArith(large, freeDim, targetDim))
			d, inKernel := arg.ObtainAs[Fun[Prod[A, A], A]](
				"so the homomorphism kills a nonzero vector",
				"∃d:(prod(A, A) → A). "+
					"    d ∈ finite_supp(L.zero, k, set_cross(E, F)) ∧ d ≠ fun_zero ∧ «lift»(d) = L.zero",
				By(
					scalarField,
					homomorphism,
					freeFinite,
					targetDim,
					smaller,
					module_dimension.LinearKernelVector.At(scalars, free, inverse, target, lift)))
			kernel := arg.Conjuncts(
				inKernel,
				"d has finite support in the pairs, with constant values",
				"d is nonzero",
				"the extension kills d")
			member, nonzero, killed := kernel[0], kernel[1], kernel[2]
			support := arg.Simplified(member, Fwd(function_module.FiniteSuppMember))
			terms := arg.Have(
				"each term of the kernel sum lies in the target",
				"∀p:prod(A, A). p ∈ set_cross(E, F) ⇒ d(p) * «entry»(p) ∈ «target».carrier",
				Derive(func(e *Argument) {
					p := e.FixAs[Prod[A, A]]("p")
					inCross := e.Assume()
					e.Show(
						"a space is closed under scaling",
						By(
							inCross,
							inTarget.At(p),
							support,
							module.SmulIn.Read(targetOn).AsFact().At(e.TermAs[A]("d(p)"), e.TermAs[A]("«entry»(p)"))))
				}))
			offSupport := arg.Have(
				"off the support the terms vanish",
				"∀p:prod(A, A). p ∈ set_cross(E, F) ∧ p ∉ fun_support(L.zero, d) ⇒ d(p) * «entry»(p) = L.zero",
				Derive(func(e *Argument) {
					p := e.FixAs[Prod[A, A]]("p")
					where := e.Conjuncts(
						e.Assume(),
						"p is a pair",
						"d vanishes at p")
					vanishes := e.Have(
						"d(p) is zero",
						"d(p) = L.zero",
						BySets(where[1]))
					e.Show(
						"zero scales the entry to zero",
						vanishes.Rw(),
						By(where[0], inTarget.At(p), module.ZeroSmul.Read(targetOn).AsFact().At(e.TermAs[A]("«entry»(p)"))))
				}))
			supportSum := arg.Have(
				"the kernel sum may run over the pairs instead of the support",
				"module_sum(L.add, L.zero, set_cross(E, F), «kernelTerm») = "+
					"module_sum(L.add, L.zero, fun_support(L.zero, d), «kernelTerm»)",
				By(
					finiteCross,
					support,
					terms,
					offSupport,
					module.ModuleSumSupport.Read(targetOn).AsFact().At(
						cross,
						arg.TermAs[Set[Prod[A, A]]]("fun_support(L.zero, d)"),
						arg.TermAs[Fun[Prod[A, A], A]]("«kernelTerm»"))))
			coordinate := arg.Have(
				"a nonzero vector has a nonzero coefficient",
				"∃q:prod(A, A). d(q) ≠ L.zero",
				By(nonzero, function_module.FunZeroDef))
			relation := arg.Have(
				"the value of the map at d is the sum of the terms over the pairs",
				"module_sum(L.add, L.zero, set_cross(E, F), «kernelTerm») = L.zero",
				By(
					supportSum,
					killed,
					free_module.FreeLiftDef.At(zero, add, zero, arg.TermAs[Fun2[A, A, A]]("L.mul"), entry, d)))
			arg.Take(d)
			arg.Show(
				"d is the vector",
				By(support, function_module.FiniteSuppMember.At(zero, k, cross, d), coordinate, relation))
		}),
})}

// FrobeniusSwapKernel — a coefficient function on E×F whose tensor is nonzero, has
// poles of order at most a + s * b, and vanishes at every regular point other than P.
// A nonzero relation d among the products x^s y gives, twisting its coefficients by
// the involution, a coefficient function c = d^s whose swap is the same sum, zero.
// The tensor of c lies in the pole space; it is nonzero because c is nonzero where d
// is, inside E×F, and the tensor has trivial kernel there; and the s-th power of its
// value at a regular point other than P is the value of the swap, zero, so the
// involution makes the value zero.
var FrobeniusSwapKernel = frobeniusSwapKernelThm{family.Add(registry.ProofEntry{
	Name: "FrobeniusSwapKernel",
	Key:  "prop_7c37c24cec2868d8",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). " +
			"∀k A₀ A₁ A₀₁:set(A). " +
			"∀t:A. " +
			"∀P:prod(set(A), set(A)). " +
			"∀a b s:num. " +
			"∀E F:set(A).",
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
			"card(E) * card(F) > s * a + b + 1",
		},
		Conclusion: "∃c:(prod(A, A) → A). " +
			"    c ∈ finite_supp(L.zero, k, set_cross(E, F)) ∧ " +
			"    «rbTensor»(c) ∈ «rbPoles»(a + s * b).carrier ∧ " +
			"    «rbTensor»(c) ≠ L.zero ∧ " +
			"    (∀Q:prod(set(A), set(A)). «rbPoint»(Q) ∧ Q ≠ P ⇒ «rbEvaluation»(Q, «rbTensor»(c)) = L.zero)",
		Abbrev: Abbrev{
			{Name: "pow", Text: "λz:A. monoid_pow(L.mul, L.one, z, s)"},
			{Name: "sum", Text: "module_sum(L.add, L.zero, set_cross(E, F))"},
			{Name: "entry", Text: "λp:prod(A, A). «pow»(fst(p)) * snd(p)"},
			{Name: "kernelTerm", Text: "λp:prod(A, A). d(p) * «entry»(p)"},
			{Name: "swapTerm", Text: "λp:prod(A, A). «pow»(c(p)) * «entry»(p)"},
		},
	},
		func(
			arg *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			P *Expr[_LatticePair],
			a, b, s *Expr[Nat],
			E, F *Expr[Set[A]],
			curve, finiteK, point, size, finiteE, finiteF, basisE, basisF, small, separated, large Fact,
		) {
			ops := arg.TermAs[FieldOps[A]]("L")
			scalars := arg.TermAs[RingOps[A]]("«rbScalars»")
			cross := arg.TermAs[Set[Prod[A, A]]]("set_cross(E, F)")
			add, zero := arg.TermAs[Op[A]]("L.add"), arg.TermAs[A]("L.zero")
			constants := arg.Have(
				"k is a subfield of L",
				"subfield(L, k)",
				By(GroupPremises(curve, algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, t))))
			frobenius := arg.Conjuncts(
				GroupPremises(constants, finiteK, size, finite_field.SquareFieldFrobenius.Read(L).At(k, s)),
				"the s-th power map is a ring endomorphism of L",
				"and an involution of k")
			endomorphism, involution := frobenius[0], frobenius[1]
			inE := arg.Have(
				"E lies in the a-th pole space",
				"E ⊆ «rbPoles»(a).carrier",
				By(
					arg.Unfolded(basisE, linear_independence.ModuleBasisDef),
					linear_independence.IndependentInCarrier.At(
						scalars, arg.TermAs[module_record.ModuleOps[A, A]]("«rbPoles»(a)"), E)))
			inF := arg.Have(
				"F lies in the b-th pole space",
				"F ⊆ «rbPoles»(b).carrier",
				By(
					arg.Unfolded(basisF, linear_independence.ModuleBasisDef),
					linear_independence.IndependentInCarrier.At(
						scalars, arg.TermAs[module_record.ModuleOps[A, A]]("«rbPoles»(b)"), F)))
			_, inKernel := arg.ObtainAs[Fun[Prod[A, A], A]](
				"the products x^s y satisfy a nonzero relation with constant coefficients",
				"∃d:(prod(A, A) → A). "+
					"    d ∈ finite_supp(L.zero, k, set_cross(E, F)) ∧ "+
					"    (∃q:prod(A, A). d(q) ≠ L.zero) ∧ "+
					"    «sum»(λp:prod(A, A). d(p) * «entry»(p)) = L.zero",
				By(
					curve,
					point,
					finiteE,
					finiteF,
					inE,
					inF,
					large,
					FrobeniusEntryKernel.Read(L).At(k, A0, A1, A01, t, P, a, b, s, E, F)))
			kernel := arg.Conjuncts(
				inKernel,
				"d has finite support in the pairs, with constant values",
				"d has a nonzero coefficient",
				"the sum of d's terms is zero")
			member, nonzero, kernelSum := kernel[0], kernel[1], kernel[2]
			support := arg.Simplified(member, Fwd(function_module.FiniteSuppMember))
			zeroPower := arg.Have(
				"the s-th power map keeps zero",
				"«pow»(L.zero) = L.zero",
				By(ring_homomorphism.MapZero.Read(endomorphism), finite_field.FrobeniusPowerDef))
			c, twistDef := arg.LetAs[Fun[Prod[A, A], A]]("c", "λp:prod(A, A). «pow»(d(p))")
			twist := arg.Have(
				"c twists the coefficients of d",
				"∀p:prod(A, A). c(p) = «pow»(d(p))",
				By(Normalized, twistDef))
			constant := arg.Have(
				"the coefficients of d are constants",
				"∀p:prod(A, A). d(p) ∈ k",
				By(support))
			values := arg.Have(
				"c takes constant values",
				"∀p:prod(A, A). c(p) ∈ k",
				Derive(func(e *Argument) {
					p := e.FixAs[Prod[A, A]]("p")
					e.Show(
						"the power of a constant is a constant",
						twist.At(p).Rw(),
						By(constant.At(p), involution.At(e.TermAs[A]("d(p)"))))
				}))
			undone := arg.Have(
				"twisting c gives d back",
				"∀p:prod(A, A). «pow»(c(p)) = d(p)",
				Derive(func(e *Argument) {
					p := e.FixAs[Prod[A, A]]("p")
					e.Show(
						"the power undoes itself on k",
						twist.At(p).Rw(),
						By(constant.At(p), involution.At(e.TermAs[A]("d(p)"))))
				}))
			smallerSupport := arg.Have(
				"where d vanishes so does c, since the power keeps zero",
				"fun_support(L.zero, c) ⊆ fun_support(L.zero, d)",
				BySets(twist, zeroPower))
			cSupport := arg.TermAs[Set[Prod[A, A]]]("fun_support(L.zero, c)")
			dSupport := arg.TermAs[Set[Prod[A, A]]]("fun_support(L.zero, d)")
			inSupport := arg.Have(
				"c has finite support in the pairs, with constant values",
				"c ∈ finite_supp(L.zero, k, set_cross(E, F))",
				By(
					support,
					smallerSupport,
					values,
					function_module.FiniteSuppMember.At(zero, k, cross, c),
					finite_set.FiniteSubset.At(cSupport, dSupport),
					set_order.SubsetTrans.At(cSupport, dSupport, cross)))
			coordinate, nonzeroAt := arg.UnpackAs[Prod[A, A]](nonzero)
			inCross := arg.Have(
				"q lies in E×F, where d is supported",
				"q ∈ set_cross(E, F)",
				BySets(support, nonzeroAt))
			nonzeroThere := arg.Have(
				"so c does not vanish at q",
				"c(q) ≠ L.zero",
				By(undone.At(coordinate), zeroPower, nonzeroAt))
			swapTerm := arg.TermAs[Fun[Prod[A, A], A]]("«swapTerm»")
			swapZero := arg.Have(
				"the swap of c is the kernel sum, so it is zero",
				"«rbSwap»(c) = L.zero",
				CalcEq(
					Leg(
						arg.TermAs[A]("«sum»(«swapTerm»)"),
						"the swap is the sum of its terms",
						By(frobeniusSwapDef)),
					Leg(
						arg.TermAs[A]("«sum»(«kernelTerm»)"),
						"term by term, twisting c gives d back",
						By(
							undone,
							module.ModuleSumCongruence.At(
								add, zero, cross, swapTerm, arg.TermAs[Fun[Prod[A, A], A]]("«kernelTerm»")))),
					FinalLeg(
						"which is zero",
						By(kernelSum))))
			bound := arg.Conjuncts(
				GroupPremises(
					curve,
					finiteK,
					point,
					size,
					finiteE,
					finiteF,
					inE,
					inF,
					values,
					FrobeniusSwapEvaluation.Read(L).At(k, A0, A1, A01, t, P, a, b, s, E, F, c)),
				"the tensor of c has poles of order at most a + s * b",
				"at a regular point other than P the power of its value is the value of the swap")
			tensorPoles, evaluation := bound[0], bound[1]
			tensorNonzero := arg.Have(
				"the tensor has trivial kernel on E×F, and c is nonzero at q there, so the tensor of c is nonzero",
				"«rbTensor»(c) ≠ L.zero",
				By(
					values,
					inCross,
					nonzeroThere,
					GroupPremises(
						curve,
						finiteK,
						point,
						size,
						finiteE,
						finiteF,
						basisE,
						basisF,
						small,
						separated,
						FrobeniusTensorInjectivity.Read(L).At(k, A0, A1, A01, t, P, a, b, s, E, F, c, coordinate))))
			pointOrder := At(Read(regular_point.RegularPointOrderAndFiltration, L), k, A0, A1, A01, t)
			vanishes := arg.Have(
				"at a regular point other than P the tensor of c vanishes",
				"∀Q:prod(set(A), set(A)). «rbPoint»(Q) ∧ Q ≠ P ⇒ «rbEvaluation»(Q, «rbTensor»(c)) = L.zero",
				Derive(func(e *Argument) {
					Q := e.FixAs[_LatticePair]("Q")
					where := e.Conjuncts(
						e.Assume(),
						"Q is a regular point",
						"Q is not P")
					other, away := where[0], where[1]
					valueOfTensor := e.TermAs[A]("«rbEvaluation»(Q, «rbTensor»(c))")
					regularAtQ := e.Have(
						"the tensor is regular at Q",
						"«rbTensor»(c) ∈ point_local_ring(field_ring(L), A₀, A₁, Q)",
						By(other, away, tensorPoles, e.Simplified(GroupPremises(curve, point, pointOrder.At(P)))))
					valueData := e.Have(
						"its value is a constant, and the evaluation keeps zero",
						"«rbEvaluation»(Q, «rbTensor»(c)) ∈ k ∧ «rbEvaluation»(Q, L.zero) = L.zero",
						By(
							regularAtQ,
							constants,
							field.SubfieldZero.At(ops, k),
							e.Simplified(GroupPremises(curve, other, pointOrder.At(Q)))))
					powerZero := e.Have(
						"the power of the value is the value of the swap, zero",
						"«pow»(«rbEvaluation»(Q, «rbTensor»(c))) = L.zero",
						By(evaluation.At(Q), other, away, swapZero, valueData))
					e.Show(
						"so the value is the power of zero, zero",
						By(involution.At(valueOfTensor), valueData, zeroPower, powerZero))
				}))
			arg.Take(c)
			arg.Show(
				"c is the coefficient function",
				By(inSupport, tensorPoles, tensorNonzero, vanishes))
		}),
})}
