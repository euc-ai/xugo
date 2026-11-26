package real_closure

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/ordered_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/real_closed_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_division"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_roots"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/registry"
)

// QuadraticIrreduciblesRealClosed — A Euclidean field is real closed when
// every irreducible polynomial has degree at most two. Linear and
// irreducible quadratic factors keep their sign on a root-free interval;
// degree induction passes this property to every polynomial.
var QuadraticIrreduciblesRealClosed = quadraticIrreduciblesRealClosedThm{family.Add(registry.ProofEntry{
	Name: "QuadraticIrreduciblesRealClosed",
	Key:  "prop_8003658ad8079d7b",
	Build: family.Sections(Statement{
		Binders: "∀F:field_ops(A). ∀lt:(A → A → bool).",
		Hypotheses: []string{
			"euclidean_field(F, lt)",
			"∀q:(num → A). polynomial_irreducible(field_ring(F), q) ⇒ polynomial_degree(q) ≤ 2",
		},
		Conclusion: "real_closed_field(F, lt)",
		Abbrev: Abbrev{
			// The entry binds a field of its own beside the one in scope where it is
			// used, so an implicit component would name two records: it spells the
			// field operations out.
			{
				Name: "rootFreeSignAtDegree",
				Text: "λF:field_ops(A). λlt:(A → A → bool). λa:A. λb:A. λn:num. ∀q:(num → A). " +
					"    polynomial_over(F.zero, F.carrier, q) ∧ " +
					"    polynomial_degree(F.zero, q) = n ∧ " +
					"    polynomial_eval(F.add, F.zero, F.mul, F.one, q, a) ≠ F.zero ∧ " +
					"    polynomial_eval(F.add, F.zero, F.mul, F.one, q, b) ≠ F.zero ∧ " +
					"    (∀x:A. " +
					"        x ∈ F.carrier ∧ lt(a, x) ∧ lt(x, b) ⇒ " +
					"        polynomial_eval(F.add, F.zero, F.mul, F.one, q, x) ≠ F.zero) ⇒ " +
					"    lt(F.zero, " +
					"        F.mul(polynomial_eval(F.add, F.zero, F.mul, F.one, q, a), " +
					"            polynomial_eval(F.add, F.zero, F.mul, F.one, q, b)))",
			},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		commonFactorSign := ctx.Lemma(Statement{
			Binders: "∀F:field_ops(A). ∀lt:(A → A → bool). ∀c u v p q:A.",
			Hypotheses: []string{
				"ordered_field_on(F, lt)",
				"c ∈ F.carrier",
				"u ∈ F.carrier",
				"v ∈ F.carrier",
				"c ≠ F.zero",
				"lt(F.zero, u * v)",
				"p = c * u",
				"q = c * v",
			},
			Conclusion: "lt(F.zero, p * q)",
		}, func(
			arg *Argument,
			F *Expr[FieldOps[A]],
			lt *Arrow2[A, A, Bool],
			ordered ordered_field.OrderedFieldFact[on.F],
			c, u, v *Member[A, on.F],
			cNonzero, positive Fact,
			p, q *Expr[A],
			pValue, qValue Fact,
		) {
			fieldF := ordered_field.FieldOn.Read(ordered)
			ring := field.RingOn.Read(fieldF)
			leadingSquare := arg.Have(
				"The nonzero coefficient has positive square",
				"lt(F.zero, c * c)",
				By(cNonzero, ordered_field.SquarePositive.Read(ordered).At(c)))
			arg.Do(pValue.Rw(), qValue.Rw())
			regroup := arg.Have(
				"The common coefficient regroups into its square",
				"c * u * (c * v) = c * c * (u * v)",
				ByArith(fieldF, c, u, v))
			arg.Do(regroup.Rw())
			arg.Show(
				"A positive coefficient square times a positive product is positive",
				By(
					leadingSquare,
					positive,
					comm_ring.MulIn.Read(ring).At(c, c),
					comm_ring.MulIn.Read(ring).At(u, v),
					ordered_field.MulPositive.Read(ordered).AsFact().At(
						arg.TermAs[A]("c * c"), arg.TermAs[A]("u * v"))))
		})
		completedSquareSign := ctx.Lemma(Statement{
			Binders: "∀F:field_ops(A). ∀lt:(A → A → bool). ∀c h d:A. ∀f:(A → A). ∀x y:A.",
			Hypotheses: []string{
				"euclidean_field(F, lt)",
				"c ∈ F.carrier",
				"h ∈ F.carrier",
				"d ∈ F.carrier",
				"c ≠ F.zero",
				"∀z:A. z ∈ F.carrier ⇒ f(z) = c * ((z - h) * (z - h) - d)",
				"∀z:A. z ∈ F.carrier ⇒ f(z) ≠ F.zero",
				"x ∈ F.carrier",
				"y ∈ F.carrier",
			},
			Conclusion: "lt(F.zero, f(x) * f(y))",
		}, func(
			arg *Argument,
			F *Expr[FieldOps[A]],
			lt *Arrow2[A, A, Bool],
			euclidean ordered_field.EuclideanFieldFact[on.F],
			c, h, d *Member[A, on.F],
			cNonzero Fact,
			f *Arrow[A, A],
			form, rootless Fact,
			x, y *Member[A, on.F],
		) {
			ordered := ordered_field.EuclideanOrderedField.Read(euclidean)
			fieldF := ordered_field.FieldOn.Read(ordered)
			ring := field.RingOn.Read(fieldF)
			noSquare := arg.Have(
				"The offset cannot be a field square",
				"∀r:A. r ∈ F.carrier ⇒ r * r ≠ d",
				Derive(func(a *Argument) {
					r := a.FixAs[A]("r")
					rIn := a.Assume()
					rm := a.MemberOf[on.F](r, rIn)
					denied := a.SupposeNot()
					square := a.Have(
						"Then the offset is the square of r",
						"r * r = d",
						By(denied))
					sum := a.MemberOf[on.F](a.TermAs[A]("h + r"), comm_ring.AddIn.Read(ring).At(h, rm))
					value := a.Have(
						"Translation by the center makes the quadratic vanish",
						"c * ((h + r - h) * (h + r - h) - d) = F.zero",
						ByArith(fieldF, c, d, h, rm, Scaled(c, square)))
					a.Show(
						"This contradicts rootlessness",
						By(sum, rootless.At(sum), form.At(sum), value))
				}))
			zero := arg.MemberOf[on.F](arg.TermAs[A]("F.zero"), comm_ring.ZeroIn.Read(ring))
			negative := arg.Have(
				"The offset is negative",
				"lt(d, F.zero)",
				Derive(func(a *Argument) {
					notPositive := a.Unless(
						a.TermAs[Bool]("lt(F.zero, d)"),
						"A positive offset would be a square",
						Given(func(b *Argument, positive Fact) {
							b.Show(
								"Positive elements are squares, and the offset is none",
								By(Normalized, noSquare, ordered_field.PositiveIsSquare.Read(euclidean).At(d), d, positive))
						}))
					nonzero := a.Unless(
						a.TermAs[Bool]("d = F.zero"),
						"A zero offset would be the square of zero",
						Given(func(b *Argument, dZero Fact) {
							b.Show(
								"Zero squares to zero, and the offset is no square",
								By(Normalized, dZero, noSquare.At(zero), comm_ring.MulLeftZeroOn.Read(ring).At(zero)))
						}))
					a.Show(
						"Trichotomy leaves a negative offset",
						By(notPositive, nonzero, ordered_field.Trichotomy.Read(ordered).At(d, zero)))
				}))
			remainders := arg.Have(
				"Every square minus the offset is positive",
				"∀z:A. z ∈ F.carrier ⇒ (z - h) * (z - h) - d ∈ F.carrier ∧ lt(F.zero, (z - h) * (z - h) - d)",
				Derive(func(a *Argument) {
					z := a.FixAs[A]("z")
					zIn := a.Assume()
					zm := a.MemberOf[on.F](z, zIn)
					displacement := comm_ring.SubIn.Read(ring).At(zm, h)
					square := comm_ring.MulIn.Read(ring).At(displacement, displacement)
					remainder := comm_ring.SubIn.Read(ring).At(square, d)
					above := a.Have(
						"The negative offset lies below the square",
						"lt(d, (z - h) * (z - h))",
						By(
							negative,
							zero,
							d,
							displacement,
							square,
							ordered_field.SquareNonnegative.Read(ordered).At(displacement),
							ordered_field.OrderMixedTransitive.Read(ordered).At(d, zero, square)))
					a.Show(
						"Their difference belongs to the field and is positive",
						By(remainder, above, d, square, ordered_field.SubPositive.Read(ordered).At(d, square)))
				}))
			u, uDef := arg.LetAs[A]("u", "(x - h) * (x - h) - d")
			v, vDef := arg.LetAs[A]("v", "(y - h) * (y - h) - d")
			positive := arg.Have(
				"The two remainders are positive field elements",
				"u ∈ F.carrier ∧ v ∈ F.carrier ∧ lt(F.zero, u) ∧ lt(F.zero, v)",
				By(Normalized, uDef, vDef, x, y, remainders.At(x), remainders.At(y)))
			values := arg.Have(
				"The completed square makes each value c times its remainder",
				"f(x) = c * u ∧ f(y) = c * v",
				By(Normalized, uDef, vDef, x, y, form.At(x), form.At(y)))
			arg.Show(
				"The common nonzero coefficient keeps the positive product of the remainders positive",
				By(
					ordered,
					c,
					cNonzero,
					positive,
					values,
					ordered_field.MulPositive.Read(ordered).AsFact().At(u, v),
					At(commonFactorSign, F, lt, c, u, v, f.Apply(x), f.Apply(y))))
		})
		quadraticSign := ctx.Lemma(Statement{
			Binders: "∀F:field_ops(A). ∀lt:(A → A → bool). ∀a b c:A. ∀f:(A → A). ∀x y:A.",
			Hypotheses: []string{
				"euclidean_field(F, lt)",
				"a ∈ F.carrier",
				"b ∈ F.carrier",
				"c ∈ F.carrier",
				"c ≠ F.zero",
				"∀z:A. z ∈ F.carrier ⇒ f(z) = a + b * z + c * (z * z)",
				"∀z:A. z ∈ F.carrier ⇒ f(z) ≠ F.zero",
				"x ∈ F.carrier",
				"y ∈ F.carrier",
			},
			Conclusion: "lt(F.zero, f(x) * f(y))",
		}, func(
			arg *Argument,
			F *Expr[FieldOps[A]],
			lt *Arrow2[A, A, Bool],
			euclidean ordered_field.EuclideanFieldFact[on.F],
			a, b, c *Member[A, on.F],
			cNonzero Fact,
			f *Arrow[A, A],
			form, rootless Fact,
			x, y *Member[A, on.F],
		) {
			ordered := ordered_field.EuclideanOrderedField.Read(euclidean)
			fieldF := ordered_field.FieldOn.Read(ordered)
			ring := field.RingOn.Read(fieldF)
			fieldValued := arg.Have(
				"Every quadratic value lies in the field",
				"∀z:A. z ∈ F.carrier ⇒ f(z) ∈ F.carrier",
				Derive(func(e *Argument) {
					z := e.FixAs[A]("z")
					zIn := e.Assume()
					zm := e.MemberOf[on.F](z, zIn)
					e.Show(
						"The coefficient formula builds f(z) from field elements",
						By(
							a,
							b,
							c,
							zm,
							form.At(z),
							comm_ring.MulIn.Read(ring).At(zm, zm),
							comm_ring.MulIn.Read(ring).At(b, zm),
							comm_ring.MulIn.Read(ring).AsFact().At(c, e.TermAs[A]("z * z")),
							comm_ring.AddIn.Read(ring).AsFact().At(a, e.TermAs[A]("b * z")),
							comm_ring.AddIn.Read(ring).AsFact().At(e.TermAs[A]("a + b * z"), e.TermAs[A]("c * (z * z)"))))
				}))
			one := arg.MemberOf[on.F](arg.TermAs[A]("F.one"), comm_ring.OneIn.Read(ring))
			two, twoDef := arg.LetAs[A]("two", "F.one + F.one")
			twoData := arg.Have(
				"Two is a positive nonzero field element",
				"two ∈ F.carrier ∧ lt(F.zero, two) ∧ two ≠ F.zero",
				By(
					Normalized,
					twoDef,
					comm_ring.AddIn.Read(ring).At(one, one),
					ordered_field.TwoPositive.Read(ordered),
					ordered_field.TwoNonzero.Read(ordered)))
			den, denDef := arg.LetAs[A]("den", "two * c")
			denominator := arg.Have(
				"Twice the leading coefficient is nonzero",
				"den ∈ F.carrier ∧ den ≠ F.zero",
				By(
					Normalized,
					denDef,
					twoData,
					c,
					cNonzero,
					comm_ring.MulIn.Read(ring).AsFact().At(two, c),
					field.MulEqZeroOn.Read(fieldF).AsFact().At(two, c)))
			h, hDef := arg.LetAs[A]("h", "-b * F.inv(den)")
			hIn := arg.Have(
				"The quadratic center lies in the field",
				"h ∈ F.carrier",
				By(
					Normalized,
					hDef,
					b,
					denominator,
					field.InvIn.Read(fieldF).AsFact().At(den),
					comm_ring.NegIn.Read(ring).At(b),
					comm_ring.MulIn.Read(ring).AsFact().At(arg.TermAs[A]("-b"), arg.TermAs[A]("F.inv(den)"))))
			hm := arg.MemberOf[on.F](h, hIn)
			centerValue := arg.MemberOf[on.F](f.Apply(h), GroupPremises(hm, fieldValued.At(h)))
			d, dDef := arg.LetAs[A]("d", "-f(h) * F.inv(c)")
			dIn := arg.Have(
				"The offset lies in the field",
				"d ∈ F.carrier",
				By(
					Normalized,
					dDef,
					centerValue,
					c,
					field.InvIn.Read(fieldF).At(c),
					comm_ring.NegIn.Read(ring).At(centerValue),
					comm_ring.MulIn.Read(ring).AsFact().At(arg.TermAs[A]("-f(h)"), arg.TermAs[A]("F.inv(c)"))))
			dm := arg.MemberOf[on.F](d, dIn)
			// 2c·h = den·h = −b·(den/den) = −b.
			center := arg.Have(
				"The center cancels the linear term",
				"two * c * h = -b",
				ByArith(fieldF, Scaled(den, hDef), Scaled(h, denDef), denominator, b, c, hm))
			// c·d = −f(h)·(c/c) = −f(h).
			offset := arg.Have(
				"The offset is the negative normalized center value",
				"c * d = -f(h)",
				ByArith(fieldF, Scaled(c, dDef), cNonzero, c, dm, centerValue))
			completed := arg.Have(
				"Completing the square writes f(z) as c((z − h)² − d)",
				"∀z:A. z ∈ F.carrier ⇒ f(z) = c * ((z - h) * (z - h) - d)",
				Derive(func(e *Argument) {
					z := e.FixAs[A]("z")
					zIn := e.Assume()
					zm := e.MemberOf[on.F](z, zIn)
					value := e.Have(
						"The value at z is a + bz + cz²",
						"f(z) = a + b * z + c * (z * z)",
						By(zm, form.At(z)))
					atCenter := e.Have(
						"The value at the center is a + bh + ch²",
						"f(h) = a + b * h + c * (h * h)",
						By(hm, form.At(h)))
					e.Do(value.Rw())
					offsetPolynomial := e.Simplified(offset, Fwd(atCenter))
					e.Show(
						"The center equation removes the remaining mixed term",
						ByArith(
							fieldF,
							a,
							b,
							c,
							dm,
							hm,
							zm,
							twoData,
							Scaled(e.TermAs[A]("z - h"), center),
							Scaled(e.TermAs[A]("c * h * (z - h)"), twoDef),
							offsetPolynomial))
				}))
			arg.Show(
				"A rootless completed square has the same sign at both points",
				By(
					euclidean,
					c,
					hm,
					dm,
					cNonzero,
					completed,
					rootless,
					x,
					y,
					At(completedSquareSign, F, lt, c, h, d, f, x, y)))
		})
		linearSign := ctx.Lemma(Statement{
			Binders: "∀F:field_ops(A). ∀lt:(A → A → bool). ∀k r:A. ∀f:(A → A). ∀x y:A.",
			Hypotheses: []string{
				"ordered_field_on(F, lt)",
				"k ∈ F.carrier",
				"r ∈ F.carrier",
				"k ≠ F.zero",
				"∀z:A. z ∈ F.carrier ⇒ f(z) = k * (z - r)",
				"x ∈ F.carrier",
				"y ∈ F.carrier",
				"lt(x, y)",
				"f(x) ≠ F.zero",
				"f(y) ≠ F.zero",
				"∀z:A. z ∈ F.carrier ∧ lt(x, z) ∧ lt(z, y) ⇒ f(z) ≠ F.zero",
			},
			Conclusion: "lt(F.zero, f(x) * f(y))",
		}, func(
			a *Argument,
			F *Expr[FieldOps[A]],
			lt *Arrow2[A, A, Bool],
			ordered ordered_field.OrderedFieldFact[on.F],
			k, r *Member[A, on.F],
			kNonzero Fact,
			f *Arrow[A, A],
			form Fact,
			x, y *Member[A, on.F],
			below, xNonzero, yNonzero, rootless Fact,
		) {
			fieldF := ordered_field.FieldOn.Read(ordered)
			ring := field.RingOn.Read(fieldF)
			rootExpression := a.Have(
				"The linear factor vanishes at r",
				"k * (r - r) = F.zero",
				ByArith(fieldF, k, r))
			root := a.Have(
				"The value at r is zero",
				"f(r) = F.zero",
				By(Normalized, r, form.At(r), rootExpression))
			outside := a.Have(
				"The root lies outside the interval",
				"lt(r, x) ∨ lt(y, r)",
				By(
					r,
					x,
					y,
					root,
					xNonzero,
					yNonzero,
					rootless.At(r),
					ordered_field.Trichotomy.Read(ordered).At(r, x),
					ordered_field.Trichotomy.Read(ordered).At(r, y)))
			u, uDef := a.LetAs[A]("u", "x - r")
			v, vDef := a.LetAs[A]("v", "y - r")
			valuesIn := a.Have(
				"The two displacements lie in the field",
				"u ∈ F.carrier ∧ v ∈ F.carrier",
				By(
					Normalized,
					uDef,
					vDef,
					x,
					y,
					r,
					comm_ring.SubIn.Read(ring).At(x, r),
					comm_ring.SubIn.Read(ring).At(y, r)))
			positive := a.Have(
				"Their displacement product is positive",
				"lt(F.zero, u * v)",
				outside.SplitDisj(
					LeftHolds(
						"The root lies below the interval",
						Given(func(b *Argument, rootBelow Fact) {
							signs := b.Have(
								"Both displacements are positive",
								"lt(F.zero, u) ∧ lt(F.zero, v)",
								By(
									Normalized,
									uDef,
									vDef,
									x,
									y,
									r,
									below,
									rootBelow,
									ordered_field.Transitive.Read(ordered).At(r, x, y),
									ordered_field.SubPositive.Read(ordered).At(r, x),
									ordered_field.SubPositive.Read(ordered).At(r, y)))
							b.Show(
								"Two positive displacements have positive product",
								By(valuesIn, signs, ordered_field.MulPositive.Read(ordered).AsFact().At(u, v)))
						})),
					RightHolds(
						"The root lies above the interval",
						Given(func(b *Argument, rootAbove Fact) {
							signs := b.Have(
								"Both displacements are negative",
								"lt(u, F.zero) ∧ lt(v, F.zero)",
								By(
									Normalized,
									uDef,
									vDef,
									x,
									y,
									r,
									below,
									rootAbove,
									ordered_field.Transitive.Read(ordered).At(x, y, r),
									ordered_field.SubNegative.Read(ordered).At(x, r),
									ordered_field.SubNegative.Read(ordered).At(y, r)))
							b.Show(
								"Two negative displacements have positive product",
								By(
									valuesIn,
									signs,
									comm_ring.NegIn.Read(ring).AsFact().At(u),
									comm_ring.NegIn.Read(ring).AsFact().At(v),
									ordered_field.MulPositive.Read(ordered).AsFact().At(b.TermAs[A]("-u"), b.TermAs[A]("-v")),
									ordered_field.NegationReversesSign.Read(ordered).AsFact().At(u),
									ordered_field.NegationReversesSign.Read(ordered).AsFact().At(v),
									comm_ring.MulNegNegOn.Read(ring).AsFact().At(u, v)))
						}))))
			values := a.Have(
				"Each endpoint value is k times its displacement",
				"f(x) = k * u ∧ f(y) = k * v",
				By(Normalized, uDef, vDef, x, y, form.At(x), form.At(y)))
			a.Show(
				"The common nonzero coefficient keeps the positive displacement product positive",
				By(
					ordered,
					k,
					kNonzero,
					valuesIn,
					positive,
					values,
					At(commonFactorSign, F, lt, k, u, v, f.Apply(x), f.Apply(y))))
		})
		irreducibleSign := ctx.Lemma(Statement{
			Binders: "∀F:field_ops(A). ∀lt:(A → A → bool). ∀p:(num → A). ∀a b:A.",
			Hypotheses: []string{
				"euclidean_field(F, lt)",
				"polynomial_irreducible(field_ring(F), p)",
				"polynomial_degree(p) ≤ 2",
				"a ∈ F.carrier",
				"b ∈ F.carrier",
				"lt(a, b)",
				"polynomial_eval(p, a) ≠ F.zero",
				"polynomial_eval(p, b) ≠ F.zero",
				"∀x:A. x ∈ F.carrier ∧ lt(a, x) ∧ lt(x, b) ⇒ polynomial_eval(p, x) ≠ F.zero",
			},
			Conclusion: "lt(F.zero, polynomial_eval(p, a) * polynomial_eval(p, b))",
		}, func(
			arg *Argument,
			F *Expr[FieldOps[A]],
			lt *Arrow2[A, A, Bool],
			euclidean ordered_field.EuclideanFieldFact[on.F],
			p *Arrow[Nat, A],
			irreducible, bound Fact,
			a, b *Member[A, on.F],
			below, leftNonzero, rightNonzero, rootless Fact,
		) {
			ordered := ordered_field.EuclideanOrderedField.Read(euclidean)
			fieldF := ordered_field.FieldOn.Read(ordered)
			ring := field.RingOn.Read(fieldF)
			zero := arg.TermAs[A]("F.zero")
			carrier := arg.TermAs[Set[A]]("F.carrier")
			polynomialData := arg.Have(
				"An irreducible polynomial has positive degree",
				"polynomial_over(F.carrier, p) ∧ 0 < polynomial_degree(p)",
				By(
					irreducible,
					polynomial_division.PolynomialIrreducibleDef.At(
						arg.TermAs[module_record.RingOps[A]]("field_ring(F)"), p),
					field.FieldRingDef,
					module_record.RingZeroDef,
					module_record.RingCarrierDef))
			nonzero := arg.Have(
				"A positive-degree polynomial is nonzero",
				"p ≠ vec_zero",
				By(
					Normalized,
					polynomialData,
					polynomial.DegreeVecZero.At(zero),
					nat_order.LessThanIrrefl.At(arg.TermAs[Nat]("0"))))
			coefficients := arg.Have(
				"All coefficients lie in the field and the leading one is nonzero",
				"(∀i:num. p(i) ∈ F.carrier) ∧ p(polynomial_degree(p)) ≠ F.zero",
				By(
					polynomialData,
					nonzero,
					polynomial.CoefficientIn.Inst[A]().At(zero, carrier, p),
					polynomial.DegreeLeading.At(zero, carrier, p)))
			arg.Cases(arg.TermAs[Bool]("polynomial_degree(p) = 1"))
			arg.When(
				"A linear irreducible has one explicit root",
				func(d *Argument, degree Fact) {
					data := d.Have(
						"The two linear coefficients lie in the field and the second is nonzero",
						"p(0) ∈ F.carrier ∧ p(1) ∈ F.carrier ∧ p(1) ≠ F.zero",
						By(Normalized, coefficients, degree))
					parts := d.Conjuncts(
						data,
						"The constant coefficient lies in the field",
						"The linear coefficient lies in the field",
						"The linear coefficient is nonzero")
					constant := d.MemberOf[on.F](p.Apply(d.TermAs[Nat]("0")), parts[0])
					leading := d.MemberOf[on.F](p.Apply(d.TermAs[Nat]("1")), parts[1])
					short := d.Have(
						"The coefficients vanish from index two on",
						"vec⟨suc(1)⟩(p)",
						By(Normalized, polynomialData, degree, polynomial.DegreeVec.At(zero, carrier, p)))
					affine := d.Have(
						"A degree-one polynomial takes the value p(0) + p(1)x",
						"∀x:A. x ∈ F.carrier ⇒ polynomial_eval(p, x) = p(0) + p(1) * x",
						Derive(func(e *Argument) {
							x := e.FixAs[A]("x")
							xIn := e.Assume()
							xm := e.MemberOf[on.F](x, xIn)
							e.Show(
								"Its value is the sum of its two terms",
								By(polynomialData, short, xm, polynomial_evaluation.EvalVecTwo.Read(ring).At(p, xm)))
						}))
					r, rDef := d.LetAs[A]("r", "-p(0) * F.inv(p(1))")
					rIn := d.Have(
						"The linear root lies in the field",
						"r ∈ F.carrier",
						By(
							Normalized,
							rDef,
							data,
							comm_ring.NegIn.Read(ring).At(constant),
							field.InvIn.Read(fieldF).At(leading),
							comm_ring.MulIn.Read(ring).AsFact().At(d.TermAs[A]("-p(0)"), d.TermAs[A]("F.inv(p(1))"))))
					rm := d.MemberOf[on.F](r, rIn)
					factor := d.Have(
						"The linear value is p(1)(x − r)",
						"∀x:A. x ∈ F.carrier ⇒ polynomial_eval(p, x) = p(1) * (x - r)",
						Derive(func(e *Argument) {
							x := e.FixAs[A]("x")
							xIn := e.Assume()
							xm := e.MemberOf[on.F](x, xIn)
							value := e.Have(
								"The value at x is p(0) + p(1)x",
								"polynomial_eval(p, x) = p(0) + p(1) * x",
								By(xm, affine.At(x)))
							e.Show(
								"With r = −p(0)/p(1), p(0) + p(1)x is p(1)(x − r)",
								value.Rw(),
								ByArith(fieldF, data, rm, xm, Scaled(leading, rDef)))
						}))
					d.Show(
						"The linear factor keeps its sign on this root-free interval",
						By(
							ordered,
							data,
							rm,
							a,
							b,
							below,
							leftNonzero,
							rightNonzero,
							rootless,
							factor,
							At(linearSign, F, lt, leading, r, d.TermAs[Fun[A, A]]("λx:A. polynomial_eval(p, x)"), a, b)))
				})
			arg.Otherwise(
				"An irreducible quadratic has no field root",
				func(d *Argument, notLinear Fact) {
					degree := d.Have(
						"The remaining positive degree at most two is two",
						"polynomial_degree(p) = 2",
						ByArith(notLinear, bound, polynomialData))
					data := d.Have(
						"The quadratic coefficients lie in the field and the leading one is nonzero",
						"p(0) ∈ F.carrier ∧ p(1) ∈ F.carrier ∧ p(2) ∈ F.carrier ∧ p(2) ≠ F.zero",
						By(Normalized, coefficients, degree))
					noRoots := d.Have(
						"A field root would make the irreducible polynomial linear",
						"∀x:A. x ∈ F.carrier ⇒ polynomial_eval(p, x) ≠ F.zero",
						Derive(func(e *Argument) {
							x := e.FixAs[A]("x")
							xIn := e.Assume()
							xm := e.MemberOf[on.F](x, xIn)
							denied := e.SupposeNot()
							e.Show(
								"Degrees one and two differ",
								ByArith(
									irreducible,
									degree,
									denied,
									polynomial_roots.IrreducibleRootLinear.Read(integral_domain.FieldIntegralDomain.Read(fieldF)).At(
										p, xm)))
						}))
					short := d.Have(
						"The coefficients vanish from index three on",
						"vec⟨suc(2)⟩(p)",
						By(Normalized, polynomialData, degree, polynomial.DegreeVec.At(zero, carrier, p)))
					value := d.Have(
						"A degree-two polynomial is the sum of its three terms",
						"∀x:A. x ∈ F.carrier ⇒ polynomial_eval(p, x) = p(0) + p(1) * x + p(2) * (x * x)",
						Derive(func(e *Argument) {
							x := e.FixAs[A]("x")
							xIn := e.Assume()
							xm := e.MemberOf[on.F](x, xIn)
							e.Show(
								"Its value is the sum of its three terms",
								By(polynomialData, short, polynomial_evaluation.EvalVecThree.Read(ring).At(p, xm)))
						}))
					d.Show(
						"A rootless quadratic has the same sign at both endpoints",
						By(
							euclidean,
							data,
							value,
							noRoots,
							a,
							b,
							At(
								quadraticSign,
								F,
								lt,
								d.TermAs[A]("p(0)"),
								d.TermAs[A]("p(1)"),
								d.TermAs[A]("p(2)"),
								d.TermAs[Fun[A, A]]("λx:A. polynomial_eval(p, x)"),
								a,
								b)))
				})
		})
		rootFreeSign := ctx.Lemma(Statement{
			Binders: "∀F:field_ops(A). ∀lt:(A → A → bool). ∀a b:A. ∀p:(num → A).",
			Hypotheses: []string{
				"euclidean_field(F, lt)",
				"∀q:(num → A). polynomial_irreducible(field_ring(F), q) ⇒ polynomial_degree(q) ≤ 2",
				"a ∈ F.carrier",
				"b ∈ F.carrier",
				"lt(a, b)",
				"polynomial_over(F.carrier, p)",
				"polynomial_eval(p, a) ≠ F.zero",
				"polynomial_eval(p, b) ≠ F.zero",
				"∀x:A. x ∈ F.carrier ∧ lt(a, x) ∧ lt(x, b) ⇒ polynomial_eval(p, x) ≠ F.zero",
			},
			Conclusion: "lt(F.zero, polynomial_eval(p, a) * polynomial_eval(p, b))",
		}, func(
			arg *Argument,
			F *Expr[FieldOps[A]],
			lt *Arrow2[A, A, Bool],
			euclidean ordered_field.EuclideanFieldFact[on.F],
			bound Fact,
			a, b *Member[A, on.F],
			below Fact,
			p *Arrow[Nat, A],
			over, leftNonzero, rightNonzero, rootless Fact,
		) {
			ordered := ordered_field.EuclideanOrderedField.Read(euclidean)
			fieldF := ordered_field.FieldOn.Read(ordered)
			ring := field.RingOn.Read(fieldF)
			induction := arg.Have(
				"Every root-free polynomial has a positive endpoint product",
				"∀n:num. «rootFreeSignAtDegree»(F, lt, a, b, n)",
				ByInduction(nat_order.StrongInduction,
					Case(
						"The claim at every smaller degree gives it at degree n",
						Derive(func(d *Argument) {
							d.FixAs[Nat]("n")
							smallerDegrees := d.Assume()
							q := d.FixAs[Fun[Nat, A]]("q")
							given := d.Assume()
							data := d.Conjuncts(
								given,
								"The polynomial is over the field",
								"Its degree is n",
								"Its first endpoint value is nonzero",
								"Its second endpoint value is nonzero",
								"It has no root in the interval")
							qOver, degree, left, right, noRoots := data[0], data[1], data[2], data[3], data[4]
							d.Cases(d.TermAs[Bool]("n = 0"))
							d.When(
								"A nonzero constant has a positive square as endpoint product",
								func(e *Argument, nZero Fact) {
									values := e.Have(
										"A constant takes the same field value at both endpoints",
										"polynomial_eval(q, a) ∈ F.carrier ∧ polynomial_eval(q, a) = polynomial_eval(q, b)",
										By(
											qOver,
											a,
											b,
											degree,
											nZero,
											polynomial_evaluation.EvalIn.Read(ring).At(q, a),
											polynomial_evaluation.DegreeZeroEval.Read(ring).At(q, a),
											polynomial_evaluation.DegreeZeroEval.Read(ring).At(q, b)))
									value := e.TermAs[A]("polynomial_eval(q, a)")
									e.Show(
										"Its nonzero value has positive square",
										By(values, left, ordered_field.SquarePositive.Read(ordered).AsFact().At(value)))
								})
							d.Otherwise(
								"A positive-degree polynomial is an irreducible factor times a cofactor of smaller degree",
								func(e *Argument, nNonzero Fact) {
									positiveDegree := e.Have(
										"A nonzero natural degree is positive",
										"0 < polynomial_degree(q)",
										ByArith(nNonzero, degree))
									g, divisor := e.ObtainAs[Fun[Nat, A]](
										"Choose an irreducible factor",
										"∃g:(num → A). polynomial_irreducible(field_ring(F), g) ∧ polynomial_divides(field_ring(F), g, q)",
										By(qOver, positiveDegree, polynomial_division.IrreducibleFactorExists.Read(fieldF).At(q)))
									divisorParts := e.Conjuncts(
										divisor,
										"The factor is irreducible",
										"It divides q")
									irreducible, divides := divisorParts[0], divisorParts[1]
									gData := e.Have(
										"The irreducible factor is a positive-degree polynomial",
										"polynomial_over(F.carrier, g) ∧ 0 < polynomial_degree(g)",
										By(
											irreducible,
											polynomial_division.PolynomialIrreducibleDef.At(
												e.TermAs[module_record.RingOps[A]]("field_ring(F)"), g),
											field.FieldRingDef,
											module_record.RingZeroDef,
											module_record.RingCarrierDef))
									r, factorization := e.ObtainAs[Fun[Nat, A]](
										"Choose the cofactor",
										"∃r:(num → A). polynomial_over(F.carrier, r) ∧ q = polynomial_mul(g, r)",
										By(
											divides,
											polynomial_division.PolynomialDividesDef.At(
												e.TermAs[module_record.RingOps[A]]("field_ring(F)"), g, q),
											field.FieldRingDef))
									factorParts := e.Conjuncts(
										factorization,
										"The cofactor is a polynomial",
										"Their product is q")
									rOver, factors := factorParts[0], factorParts[1]
									evaluated := e.Have(
										"Evaluation takes this factorization to a product",
										"∀x:A. x ∈ F.carrier ⇒ polynomial_eval(q, x) = polynomial_eval(g, x) * polynomial_eval(r, x)",
										Derive(func(f *Argument) {
											x := f.FixAs[A]("x")
											xIn := f.Assume()
											xm := f.MemberOf[on.F](x, xIn)
											f.Show(
												"Evaluation at x is multiplicative",
												By(factors, gData, rOver, xm, polynomial_evaluation.EvalMul.Read(ring).At(g, r, xm)))
										}))
									u, uDef := e.LetAs[A]("u", "polynomial_eval(g, a)")
									v, vDef := e.LetAs[A]("v", "polynomial_eval(g, b)")
									s, sDef := e.LetAs[A]("s", "polynomial_eval(r, a)")
									t, tDef := e.LetAs[A]("t", "polynomial_eval(r, b)")
									members := e.Have(
										"The four factor values belong to the field",
										"u ∈ F.carrier ∧ v ∈ F.carrier ∧ s ∈ F.carrier ∧ t ∈ F.carrier",
										By(
											Normalized,
											uDef,
											vDef,
											sDef,
											tDef,
											gData,
											rOver,
											a,
											b,
											polynomial_evaluation.EvalIn.Read(ring).At(g, a),
											polynomial_evaluation.EvalIn.Read(ring).At(g, b),
											polynomial_evaluation.EvalIn.Read(ring).At(r, a),
											polynomial_evaluation.EvalIn.Read(ring).At(r, b)))
									nonzeros := e.Have(
										"Every factor value at an endpoint is nonzero",
										"u ≠ F.zero ∧ v ≠ F.zero ∧ s ≠ F.zero ∧ t ≠ F.zero",
										By(
											Normalized,
											members,
											uDef,
											vDef,
											sDef,
											tDef,
											a,
											b,
											left,
											right,
											evaluated.At(a),
											evaluated.At(b),
											field.MulEqZeroOn.Read(fieldF).AsFact().At(u, s),
											field.MulEqZeroOn.Read(fieldF).AsFact().At(v, t)))
									factorRootless := e.Have(
										"A root of either factor would be a root of q",
										Statement{
											Binders: "∀x:A.",
											Hypotheses: []string{
												"x ∈ F.carrier",
												"lt(a, x)",
												"lt(x, b)",
											},
											Conclusion: "polynomial_eval(g, x) ≠ F.zero ∧ polynomial_eval(r, x) ≠ F.zero",
										},
										Derive(func(f *Argument) {
											x := f.FixAs[A]("x")
											inside := f.Assume()
											f.Show(
												"A nonzero product has nonzero factors",
												By(
													inside,
													noRoots.At(x),
													evaluated.At(x),
													gData,
													rOver,
													polynomial_evaluation.EvalIn.Read(ring).AsFact().At(g, x),
													polynomial_evaluation.EvalIn.Read(ring).AsFact().At(r, x),
													field.MulEqZeroOn.Read(fieldF).AsFact().At(
														f.TermAs[A]("polynomial_eval(g, x)"), f.TermAs[A]("polynomial_eval(r, x)"))))
										}))
									nonzeroPolynomials := e.Have(
										"Both factors are nonzero polynomials",
										"g ≠ vec_zero ∧ r ≠ vec_zero",
										By(Normalized, uDef, sDef, nonzeros, a, polynomial_evaluation.EvalVecZero.Read(ring).At(a)))
									smaller := e.Have(
										"The cofactor has smaller degree",
										"polynomial_degree(r) < n",
										ByArith(
											gData,
											rOver,
											nonzeroPolynomials,
											degree,
											factors,
											polynomial.DegreeMul.Read(integral_domain.FieldIntegralDomain.Read(fieldF)).At(g, r)))
									factorSign := e.Have(
										"The irreducible factor keeps its sign",
										"lt(F.zero, u * v)",
										By(
											uDef,
											vDef,
											nonzeros,
											euclidean,
											irreducible,
											bound.At(g),
											a,
											b,
											below,
											factorRootless,
											At(irreducibleSign, F, lt, g, a, b)))
									cofactorSign := e.Have(
										"The induction hypothesis applies to the cofactor",
										"lt(F.zero, s * t)",
										By(
											Normalized,
											sDef,
											tDef,
											nonzeros,
											rOver,
											smaller,
											factorRootless,
											smallerDegrees.At(e.TermAs[Nat]("polynomial_degree(r)"), r)))
									endpointValues := e.Have(
										"Each endpoint value is the product of the factor values",
										"polynomial_eval(q, a) = u * s ∧ polynomial_eval(q, b) = v * t",
										By(Normalized, uDef, vDef, sDef, tDef, a, b, evaluated.At(a), evaluated.At(b)))
									endpointParts := e.Conjuncts(
										endpointValues,
										"The value at a is u times s",
										"The value at b is v times t")
									e.Do(endpointParts[0].Rw(), endpointParts[1].Rw())
									regroup := e.Have(
										"The endpoint product regroups by factor",
										"u * s * (v * t) = u * v * (s * t)",
										ByArith(fieldF, members))
									e.Do(regroup.Rw())
									e.Show(
										"The endpoint product is a product of two positive elements",
										By(
											factorSign,
											cofactorSign,
											members,
											comm_ring.MulIn.Read(ring).AsFact().At(u, v),
											comm_ring.MulIn.Read(ring).AsFact().At(s, t),
											ordered_field.MulPositive.Read(ordered).AsFact().At(e.TermAs[A]("u * v"), e.TermAs[A]("s * t"))))
								})
						}))))
			arg.Show(
				"The claim at the degree of p gives the sign",
				By(
					over,
					leftNonzero,
					rightNonzero,
					rootless,
					induction.At(arg.TermAs[Nat]("polynomial_degree(p)"), p)))
		})
		return ctx.Theorem(headline, func(
			arg *Argument,
			F *Expr[FieldOps[A]],
			lt *Arrow2[A, A, Bool],
			euclidean ordered_field.EuclideanFieldFact[on.F],
			bound Fact,
		) {
			ordered := ordered_field.EuclideanOrderedField.Read(euclidean)
			fieldF := ordered_field.FieldOn.Read(ordered)
			ring := field.RingOn.Read(fieldF)
			arg.Do(real_closed_field.RealClosedField.Intro(
				Case(
					"The given field is ordered",
					By(ordered)),
				Case(
					"A polynomial crossing from negative to positive has a root",
					Derive(func(d *Argument) {
						p := d.FixAs[Fun[Nat, A]]("p")
						a := d.FixAs[A]("a")
						b := d.FixAs[A]("b")
						crossing := d.Assume()
						parts := d.Conjuncts(
							crossing,
							"The polynomial is over the field",
							"The left endpoint lies in the field",
							"The right endpoint lies in the field",
							"The left endpoint lies below the right one",
							"The first value is negative",
							"The second value is positive")
						over, below, negative, positive := parts[0], parts[3], parts[4], parts[5]
						am := d.MemberOf[on.F](a, parts[1])
						bm := d.MemberOf[on.F](b, parts[2])
						noRoot := d.SupposeNot()
						rootless := d.Have(
							"No root lies between the endpoints",
							"∀x:A. x ∈ F.carrier ∧ lt(a, x) ∧ lt(x, b) ⇒ polynomial_eval(p, x) ≠ F.zero",
							By(Normalized, noRoot))
						valuesIn := d.Have(
							"Zero and both values belong to the field",
							"F.zero ∈ F.carrier ∧ polynomial_eval(p, a) ∈ F.carrier ∧ polynomial_eval(p, b) ∈ F.carrier",
							By(
								over,
								am,
								bm,
								comm_ring.ZeroIn.Read(ring),
								polynomial_evaluation.EvalIn.Read(ring).At(p, am),
								polynomial_evaluation.EvalIn.Read(ring).At(p, bm)))
						nonzero := d.Have(
							"The crossing values are nonzero",
							"polynomial_eval(p, a) ≠ F.zero ∧ polynomial_eval(p, b) ≠ F.zero",
							By(
								valuesIn,
								negative,
								positive,
								ordered_field.Irreflexive.Read(ordered).AsFact().At(d.TermAs[A]("F.zero"))))
						productPositive := d.Have(
							"Rootlessness makes their product positive",
							"lt(F.zero, polynomial_eval(p, a) * polynomial_eval(p, b))",
							By(euclidean, bound, over, am, bm, below, nonzero, rootless, At(rootFreeSign, F, lt, a, b, p)))
						leftValue, rightValue := d.TermAs[A]("polynomial_eval(p, a)"), d.TermAs[A]("polynomial_eval(p, b)")
						zero := d.TermAs[A]("F.zero")
						d.Show(
							"A positive second value makes this contradict the negative first value",
							By(
								valuesIn,
								negative,
								positive,
								productPositive,
								ordered_field.PositiveMulOrderIff.Read(ordered).AsFact().At(zero, leftValue, rightValue),
								comm_ring.MulLeftZeroOn.Read(ring).AsFact().At(rightValue),
								ordered_field.Transitive.Read(ordered).AsFact().At(zero, leftValue, zero),
								ordered_field.Irreflexive.Read(ordered).AsFact().At(zero)))
					}))))
		})
	}),
})}
