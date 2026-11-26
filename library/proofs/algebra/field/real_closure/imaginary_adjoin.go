package real_closure

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/ordered_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// SquareRootCoordinates — In a Euclidean field the two coordinates of a
// square root of a + ib exist: choose r² = a² + b², w² = 2(r + a), u = w/2,
// and v = b/w when b is nonzero, and use a signed real square when b is zero.
var SquareRootCoordinates = squareRootCoordinatesThm{family.Add(registry.ProofEntry{
	Name: "SquareRootCoordinates",
	Key:  "prop_8b6bd92b2d621935",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). ∀lt:(A → A → bool). ∀a b:A.",
		Hypotheses: []string{
			"euclidean_field(F, lt)",
			"a ∈ F.carrier",
			"b ∈ F.carrier",
		},
		Conclusion: "∃u v:A. " +
			"    u ∈ F.carrier ∧ v ∈ F.carrier ∧ u * u - v * v = a ∧ (F.one + F.one) * (u * v) = b",
	},
		func(
			arg *Argument,
			F *Expr[FieldOps[A]],
			lt *Arrow2[A, A, Bool],
			euclidean ordered_field.EuclideanFieldFact[on.F],
			a, b *Member[A, on.F],
		) {
			ordered := ordered_field.EuclideanOrderedField.Read(euclidean)
			fieldF := ordered_field.FieldOn.Read(ordered)
			ring := field.RingOn.Read(fieldF)
			zero := arg.TermAs[A]("F.zero")
			one := arg.TermAs[A]("F.one")
			zeroIn := arg.MemberOf[on.F](zero, comm_ring.ZeroIn.Read(ring))
			oneIn := arg.MemberOf[on.F](one, comm_ring.OneIn.Read(ring))
			arg.Cases(arg.TermAs[Bool]("b = F.zero"))
			arg.When(
				"A signed real square handles zero imaginary part",
				func(c *Argument, bZero Fact) {
					aNonzero := c.Unless(
						c.TermAs[Bool]("a = F.zero"),
						"Zero has the zero square root",
						Given(func(d *Argument, aZero Fact) {
							d.Take(zero)
							d.Take(zero)
							d.Show(
								"Both coordinates are zero",
								ByArith(fieldF, zeroIn, aZero, bZero, a, b))
						}))
					c.Cases(c.TermAs[Bool]("lt(F.zero, a)"))
					c.When(
						"A positive real part has a real square root",
						func(d *Argument, aPositive Fact) {
							s, root := d.ObtainAs[A](
								"Choose the real coordinate",
								"∃s:A. s ∈ F.carrier ∧ s * s = a",
								By(ordered_field.PositiveIsSquare.Read(euclidean).At(a), aPositive))
							d.Take(s)
							d.Take(zero)
							d.Show(
								"The imaginary coordinate is zero",
								ByArith(fieldF, zeroIn, bZero, a, b, root))
						})
					c.Otherwise(
						"A negative real part has an imaginary square root",
						func(d *Argument, notPositive Fact) {
							negPositive := d.Have(
								"The negative real part is positive",
								"-a ∈ F.carrier ∧ lt(F.zero, -a)",
								By(
									zeroIn,
									notPositive,
									aNonzero,
									a,
									ordered_field.Trichotomy.Read(ordered).At(zeroIn, a),
									ordered_field.NegationReversesSign.Read(ordered).At(a),
									comm_ring.NegIn.Read(ring).At(a)))
							s, root := d.ObtainAs[A](
								"Choose the imaginary coordinate",
								"∃s:A. s ∈ F.carrier ∧ s * s = -a",
								By(ordered_field.PositiveIsSquare.Read(euclidean).AsFact().At(d.TermAs[A]("-a")), negPositive))
							d.Take(zero)
							d.Take(s)
							d.Show(
								"The real coordinate is zero",
								ByArith(fieldF, zeroIn, bZero, a, b, root))
						})
				})
			arg.Otherwise(
				"A nonzero imaginary part has the coordinates u = w/2 and v = b/w",
				func(c *Argument, bNonzero Fact) {
					bSquarePositive := c.Have(
						"A nonzero square is positive",
						"lt(F.zero, b * b)",
						By(bNonzero, ordered_field.SquarePositive.Read(ordered).At(b)))
					d, dDef := c.LetAs[A]("d", "b * b + a * a")
					normIn := c.Have(
						"The two squares and the squared norm belong to the field",
						"a * a ∈ F.carrier ∧ b * b ∈ F.carrier ∧ d ∈ F.carrier",
						By(
							Normalized,
							dDef,
							a,
							b,
							comm_ring.MulIn.Read(ring).At(a, a),
							comm_ring.MulIn.Read(ring).At(b, b),
							comm_ring.AddIn.Read(ring).AsFact().At(c.TermAs[A]("b * b"), c.TermAs[A]("a * a"))))
					normParts := c.Conjuncts(
						normIn,
						"The square of a belongs to the field",
						"The square of b belongs to the field",
						"The squared norm belongs to the field")
					aSquared := c.MemberOf[on.F](c.TermAs[A]("a * a"), normParts[0])
					bSquared := c.MemberOf[on.F](c.TermAs[A]("b * b"), normParts[1])
					dm := c.MemberOf[on.F](d, normParts[2])
					dPositive := c.Have(
						"The squared norm is positive",
						"lt(F.zero, d)",
						By(
							Normalized,
							zeroIn,
							bSquarePositive,
							dDef,
							a,
							normIn,
							ordered_field.SquareNonnegative.Read(ordered).At(a),
							ordered_field.LessThanSelfAddLeft.Read(ordered).At(bSquared, aSquared),
							ordered_field.OrderMixedTransitive.Read(ordered).At(zeroIn, aSquared, dm)))
					r, rRoot := c.ObtainAs[A](
						"Choose the positive norm root",
						"∃r:A. r ∈ F.carrier ∧ lt(F.zero, r) ∧ r * r = d",
						By(dPositive, ordered_field.PositiveSquareRoot.Read(euclidean).At(dm)))
					rData := c.Conjuncts(
						rRoot,
						"The norm root belongs to the field",
						"It is positive",
						"Its square is the squared norm")
					rm := c.MemberOf[on.F](r, rData[0])
					product := c.Have(
						"The conjugate real factors have product b squared",
						"(r + a) * (r - a) = b * b",
						ByArith(fieldF, dDef, a, b, rRoot, normIn))
					factorsIn := c.Have(
						"Both real factors belong to the field",
						"r + a ∈ F.carrier ∧ r - a ∈ F.carrier",
						By(a, rRoot, comm_ring.AddIn.Read(ring).At(rm, a), comm_ring.SubIn.Read(ring).At(rm, a)))
					factorParts := c.Conjuncts(
						factorsIn,
						"The sum belongs to the field",
						"The difference belongs to the field")
					sum := c.MemberOf[on.F](c.TermAs[A]("r + a"), factorParts[0])
					difference := c.MemberOf[on.F](c.TermAs[A]("r - a"), factorParts[1])
					sumPositive := c.Have(
						"The norm root plus a is positive",
						"lt(F.zero, r + a)",
						Derive(func(e *Argument) {
							notNegative := e.Unless(
								e.TermAs[Bool]("lt(a, F.zero)"),
								"For negative a cancel the positive factor r minus a",
								Given(func(f *Argument, aNegative Fact) {
									differencePositive := f.Have(
										"The norm root minus a is positive",
										"lt(F.zero, r - a)",
										By(
											Normalized,
											aNegative,
											a,
											rRoot,
											ordered_field.NegationReversesSign.Read(ordered).At(a),
											comm_ring.NegIn.Read(ring).At(a),
											ordered_field.AddPositive.Read(ordered).AsFact().At(r, f.TermAs[A]("-a")),
											comm_ring.SubAddNegOn.Read(ring).At(rm, a)))
									f.Show(
										"Then r + a is positive, its product with the positive r − a being b²",
										By(
											zeroIn,
											bSquarePositive,
											differencePositive,
											product,
											factorsIn,
											ordered_field.PositiveMulOrderIff.Read(ordered).At(zeroIn, sum, difference),
											comm_ring.MulLeftZeroOn.Read(ring).At(difference)))
								}))
							e.Show(
								"Adding the positive norm root to a nonnegative element is positive",
								By(
									zeroIn,
									notNegative,
									a,
									factorsIn,
									rRoot,
									ordered_field.Trichotomy.Read(ordered).At(zeroIn, a),
									ordered_field.OrderedLeDef.At(lt, zero, a),
									ordered_field.LessThanSelfAddLeft.Read(ordered).At(rm, a),
									ordered_field.OrderMixedTransitive.Read(ordered).At(zeroIn, a, sum)))
						}))
					two, twoDef := c.LetAs[A]("two", "F.one + F.one")
					twoPositive := c.Have(
						"Two is positive",
						"two ∈ F.carrier ∧ lt(F.zero, two)",
						By(
							Normalized,
							twoDef,
							comm_ring.AddIn.Read(ring).At(oneIn, oneIn),
							ordered_field.TwoPositive.Read(ordered)))
					twoData := c.Conjuncts(
						twoPositive,
						"Two belongs to the field",
						"It is positive")
					twom := c.MemberOf[on.F](two, twoData[0])
					twiceSumPositive := c.Have(
						"Twice the positive factor is positive",
						"two * (r + a) ∈ F.carrier ∧ lt(F.zero, two * (r + a))",
						By(
							sumPositive,
							twoPositive,
							factorsIn,
							comm_ring.MulIn.Read(ring).At(twom, sum),
							ordered_field.MulPositive.Read(ordered).At(twom, sum)))
					w, wRoot := c.ObtainAs[A](
						"Choose the second positive square root",
						"∃w:A. w ∈ F.carrier ∧ lt(F.zero, w) ∧ w * w = two * (r + a)",
						By(
							twiceSumPositive,
							ordered_field.PositiveSquareRoot.Read(euclidean).AsFact().At(c.TermAs[A]("two * (r + a)"))))
					wData := c.Conjuncts(
						wRoot,
						"The second root belongs to the field",
						"It is positive",
						"Its square is twice the positive factor")
					wm := c.MemberOf[on.F](w, wData[0])
					nonzero := c.Have(
						"Both denominators are nonzero",
						"two ≠ F.zero ∧ w ≠ F.zero",
						By(Normalized, zeroIn, twoPositive, wRoot, ordered_field.Irreflexive.Read(ordered).At(zeroIn)))
					u, uDef := c.LetAs[A]("u", "w * F.inv(two)")
					v, vDef := c.LetAs[A]("v", "b * F.inv(w)")
					coordinatesIn := c.Have(
						"The two coordinates belong to the field",
						"u ∈ F.carrier ∧ v ∈ F.carrier",
						By(
							Normalized,
							uDef,
							vDef,
							b,
							twoPositive,
							wRoot,
							field.InvIn.Read(fieldF).At(twom),
							field.InvIn.Read(fieldF).At(wm),
							comm_ring.MulIn.Read(ring).AsFact().At(w, c.TermAs[A]("F.inv(two)")),
							comm_ring.MulIn.Read(ring).AsFact().At(b, c.TermAs[A]("F.inv(w)"))))
					// 2uv = 2 · (w/2) · v = wv = w · (b/w) = b.
					coordinateProduct := c.Have(
						"The imaginary coordinate is b",
						"two * (u * v) = b",
						ByArith(
							fieldF,
							Scaled(c.TermAs[A]("two * v"), uDef),
							Scaled(w, vDef),
							b,
							nonzero,
							twoPositive,
							coordinatesIn,
							wData[0]))
					// u² = (w/2)² = w²/4 = 2(r + a)/4 = (r + a)/2.
					uSquare := c.Have(
						"The first coordinate has the required square",
						"u * u = (r + a) * F.inv(two)",
						ByArith(
							fieldF,
							Scaled(c.TermAs[A]("u + w * F.inv(two)"), uDef),
							Scaled(c.TermAs[A]("F.inv(two) * F.inv(two)"), wData[2]),
							nonzero,
							twoPositive,
							coordinatesIn,
							rData[0],
							a,
							wData[0]))
					// v² = (b/w)² = b²/w² = (r + a)(r − a)/(2(r + a)) = (r − a)/2,
					// with b² = (r + a)(r − a) and w² = 2(r + a).
					vSquare := c.Have(
						"The second coordinate has the complementary square",
						"v * v = (r - a) * F.inv(two)",
						ByArith(
							fieldF,
							Scaled(c.TermAs[A]("v + b * F.inv(w)"), vDef),
							Scaled(c.TermAs[A]("(r - a) * (F.inv(two) * (F.inv(w) * F.inv(w)))"), wData[2]),
							Scaled(c.TermAs[A]("F.inv(w) * F.inv(w)"), product),
							nonzero,
							twoPositive,
							coordinatesIn,
							rData[0],
							a,
							b,
							wData[0]))
					// u² − v² = (r + a)/2 − (r − a)/2 = (1 + 1)a/2 = a.
					coordinateDifference := c.Have(
						"The real coordinate is a",
						"u * u - v * v = a",
						ByArith(
							fieldF,
							uSquare,
							vSquare,
							Scaled(c.TermAs[A]("a * F.inv(two)"), twoDef),
							nonzero,
							twoPositive,
							coordinatesIn,
							rData[0],
							a,
							wData[0]))
					c.Take(u)
					c.Take(v)
					c.Show(
						"These coordinates give a square root of a + ib",
						By(coordinatesIn, coordinateDifference, coordinateProduct))
				})
		}),
})}

// ImaginaryAdjoinSquareClosed — Adjoining a square root of minus one to a
// Euclidean subfield produces a square-closed field: write its elements as
// a + ib and solve the two real coordinate equations.
var ImaginaryAdjoinSquareClosed = imaginaryAdjoinSquareClosedThm{family.Add(registry.ProofEntry{
	Name: "ImaginaryAdjoinSquareClosed",
	Key:  "prop_95b605a9a4db106b",
	Build: family.Sections(Statement{
		Binders: "∀M:field_ops(A). ∀K:set(A). ∀lt:(A → A → bool). ∀i:A.",
		Hypotheses: []string{
			"field_on(M)",
			"subfield(M, K)",
			"euclidean_field(restrict_field(M, K), lt)",
			"i ∈ M.carrier",
			"i * i = -M.one",
		},
		Conclusion: "square_closed(M, field_adjoin(M, K, {i}))",
		Abbrev: Abbrev{
			{Name: "withCoordinates", Text: "λM:field_ops(A). λi:A. λa:A. λb:A. M.add(a, M.mul(i, b))"},
			{Name: "withBaseCoordinates", Text: "λM:field_ops(A). λK:set(A). λi:A. " +
				"    {z:A | ∃a b:A. a ∈ K ∧ b ∈ K ∧ z = «withCoordinates»(M, i, a, b)}"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		hasBaseCoordinates := ctx.Lemma(Statement{
			Binders: "∀M:field_ops(A). ∀K:set(A). ∀i u v:A.",
			Hypotheses: []string{
				"u ∈ K",
				"v ∈ K",
			},
			Conclusion: "«withCoordinates»(M, i, u, v) ∈ «withBaseCoordinates»(M, K, i)",
		}, func(arg *Argument, M *Expr[FieldOps[A]], K *Expr[Set[A]], i, u, v *Expr[A], coordinates Fact) {
			arg.Show(
				"The displayed coordinates witness membership",
				By(coordinates))
		})

		baseCoordinatesSubfield := ctx.Lemma(Statement{
			Binders: "∀M:field_ops(A). ∀K:set(A). ∀lt:(A → A → bool). ∀i:A.",
			Hypotheses: []string{
				"field_on(M)",
				"subfield(M, K)",
				"ordered_field_on(restrict_field(M, K), lt)",
				"i ∈ M.carrier",
				"i * i = -M.one",
			},
			Conclusion: "subfield(M, «withBaseCoordinates»(M, K, i))",
		}, func(
			arg *Argument,
			M *Expr[FieldOps[A]],
			fieldM field.FieldFact[on.M],
			K *Expr[Set[A]],
			sub Fact,
			lt *Arrow2[A, A, Bool],
			ordered Fact,
			i *Member[A, on.M],
			iSquared Fact,
		) {
			ring := field.RingOn.Read(fieldM)
			zero := arg.TermAs[A]("M.zero")
			one := arg.TermAs[A]("M.one")
			arg.Show(
				"The elements a + ib satisfy the subfield axioms",
				Simp(Fwd(field.SubfieldDef)),
				SplitConjAll(
					Case(
						"Every a + ib belongs to the ambient field",
						Derive(func(br *Argument) {
							br.Do(Unfold(set_basic.SubsetDef))
							br.FixAs[A]("x")
							inForms := br.Assume()
							a, b, coordinates := br.Unpack2As[A, A](inForms, "a", "b")
							carriers := br.Have(
								"The coordinates belong to the ambient field",
								"a ∈ M.carrier ∧ b ∈ M.carrier",
								BySets(sub, coordinates, field.SubfieldSubset.At(M, K)))
							br.Show(
								"Their linear combination belongs to the ambient field",
								By(
									Normalized,
									i,
									carriers,
									coordinates,
									comm_ring.MulIn.Read(ring).AsFact().At(i, b),
									comm_ring.AddIn.Read(ring).AsFact().At(a, br.TermAs[A]("i * b"))))
						})),
					Case(
						"Zero has two zero coordinates",
						Derive(func(br *Argument) {
							zeroForm := br.Have(
								"Zero is 0 + i0",
								"M.zero = «withCoordinates»(M, i, M.zero, M.zero)",
								ByArith(fieldM, i))
							br.Show(
								"Zero has base coordinates",
								By(zeroForm, sub, field.SubfieldZero.At(M, K), At(hasBaseCoordinates, M, K, i, zero, zero)))
						})),
					Case(
						"One has coordinates one and zero",
						Derive(func(br *Argument) {
							oneForm := br.Have(
								"One is 1 + i0",
								"M.one = «withCoordinates»(M, i, M.one, M.zero)",
								ByArith(fieldM, i))
							br.Show(
								"One has base coordinates",
								By(
									oneForm,
									sub,
									field.SubfieldZero.At(M, K),
									field.SubfieldOne.At(M, K),
									At(hasBaseCoordinates, M, K, i, one, zero)))
						})),
					Case(
						"Addition adds the coordinates",
						Derive(func(br *Argument) {
							br.FixAs[A]("x")
							br.FixAs[A]("y")
							inForms := br.Assume()
							parts := br.Conjuncts(
								inForms,
								"The first summand has base coordinates",
								"The second summand has base coordinates")
							a, b, left := br.Unpack2As[A, A](parts[0], "a", "b")
							c, d, right := br.Unpack2As[A, A](parts[1], "c", "d")
							carriers := br.Have(
								"All four coordinates belong to the ambient field",
								"a ∈ M.carrier ∧ b ∈ M.carrier ∧ c ∈ M.carrier ∧ d ∈ M.carrier",
								BySets(sub, left, right, field.SubfieldSubset.At(M, K)))
							addFormula := br.Have(
								"The sum has the sums of the real and imaginary coordinates",
								"«withCoordinates»(M, i, a, b) + «withCoordinates»(M, i, c, d) = "+
									"«withCoordinates»(M, i, a + c, b + d)",
								ByArith(fieldM, i, carriers))
							br.Show(
								"Both new coordinates lie in the base field",
								By(
									sub,
									left,
									right,
									addFormula,
									field.SubfieldAdd.At(M, K, a, c),
									field.SubfieldAdd.At(M, K, b, d),
									At(hasBaseCoordinates, M, K, i, br.TermAs[A]("a + c"), br.TermAs[A]("b + d"))))
						})),
					Case(
						"Negation negates both coordinates",
						Derive(func(br *Argument) {
							br.FixAs[A]("x")
							inForms := br.Assume()
							a, b, coordinates := br.Unpack2As[A, A](inForms, "a", "b")
							carriers := br.Have(
								"Both coordinates belong to the ambient field",
								"a ∈ M.carrier ∧ b ∈ M.carrier",
								BySets(sub, coordinates, field.SubfieldSubset.At(M, K)))
							negFormula := br.Have(
								"Negation acts on both coordinates",
								"-«withCoordinates»(M, i, a, b) = «withCoordinates»(M, i, -a, -b)",
								ByArith(fieldM, i, carriers))
							br.Show(
								"Both negatives lie in the base field",
								By(
									negFormula,
									sub,
									coordinates,
									field.SubfieldNeg.At(M, K, a),
									field.SubfieldNeg.At(M, K, b),
									At(hasBaseCoordinates, M, K, i, br.TermAs[A]("-a"), br.TermAs[A]("-b"))))
						})),
					Case(
						"Multiplication uses the relation i squared equals minus one",
						Derive(func(br *Argument) {
							br.FixAs[A]("x")
							br.FixAs[A]("y")
							inForms := br.Assume()
							parts := br.Conjuncts(
								inForms,
								"The first factor has base coordinates",
								"The second factor has base coordinates")
							a, b, left := br.Unpack2As[A, A](parts[0], "a", "b")
							c, d, right := br.Unpack2As[A, A](parts[1], "c", "d")
							carriers := br.Have(
								"All four coordinates belong to the ambient field",
								"a ∈ M.carrier ∧ b ∈ M.carrier ∧ c ∈ M.carrier ∧ d ∈ M.carrier",
								BySets(sub, left, right, field.SubfieldSubset.At(M, K)))
							mulFormula := br.Have(
								"The product has coordinates ac minus bd and ad plus bc",
								"«withCoordinates»(M, i, a, b) * «withCoordinates»(M, i, c, d) = "+
									"«withCoordinates»(M, i, a * c - b * d, a * d + b * c)",
								ByArith(fieldM, Scaled(br.TermAs[A]("b * d"), iSquared), i, carriers))
							productCoordinates := br.Have(
								"Both product coordinates lie in the base field",
								"a * c - b * d ∈ K ∧ a * d + b * c ∈ K",
								By(
									fieldM,
									sub,
									left,
									right,
									field.SubfieldMul.At(M, K, a, c),
									field.SubfieldMul.At(M, K, b, d),
									field.SubfieldMul.At(M, K, a, d),
									field.SubfieldMul.At(M, K, b, c),
									field.SubfieldSub.At(M, K, br.TermAs[A]("a * c"), br.TermAs[A]("b * d")),
									field.SubfieldAdd.At(M, K, br.TermAs[A]("a * d"), br.TermAs[A]("b * c"))))
							br.Show(
								"The product has base coordinates",
								By(
									mulFormula,
									productCoordinates,
									left,
									right,
									At(hasBaseCoordinates, M, K, i, br.TermAs[A]("a * c - b * d"), br.TermAs[A]("a * d + b * c"))))
						})),
					Case(
						"Inversion divides the conjugate by the nonzero norm",
						Derive(func(br *Argument) {
							x := br.FixAs[A]("x")
							inForms := br.Assume()
							a, b, coordinates := br.Unpack2As[A, A](inForms, "a", "b")
							carriers := br.Have(
								"Both coordinates belong to the ambient field",
								"a ∈ M.carrier ∧ b ∈ M.carrier",
								BySets(sub, coordinates, field.SubfieldSubset.At(M, K)))
							zeroForm := br.Have(
								"Zero is 0 + i0",
								"«withCoordinates»(M, i, M.zero, M.zero) = M.zero",
								ByArith(fieldM, i))
							br.Cases(br.TermAs[Bool]("x = M.zero"))
							br.When(
								"The inverse of zero is zero",
								func(ca *Argument, xZero Fact) {
									ca.Show(
										"Zero has base coordinates",
										By(
											Normalized,
											xZero,
											zeroForm,
											sub,
											field.InvZeroOn.Read(fieldM),
											field.SubfieldZero.At(M, K),
											At(hasBaseCoordinates, M, K, i, zero, zero)))
								})
							br.Otherwise(
								"A nonzero a + ib has a nonzero norm a² + b²",
								func(ca *Argument, xNonzero Fact) {
									d, dDef := ca.LetAs[A]("d", "a * a + b * b")
									normNonzero := ca.Have(
										"A zero norm would force both coordinates and the element to vanish",
										"d ≠ M.zero",
										By(
											Normalized,
											xNonzero,
											dDef,
											zeroForm,
											ordered,
											coordinates,
											ordered_field.SumSquaresZero.At(ca.TermAs[FieldOps[A]]("restrict_field(M, K)"), lt, a, b),
											field.RestrictFieldDef.At(M, K)))
									normInK := ca.Have(
										"The norm lies in the base field",
										"d ∈ K",
										By(
											Normalized,
											dDef,
											sub,
											coordinates,
											field.SubfieldMul.At(M, K, a, a),
											field.SubfieldMul.At(M, K, b, b),
											field.SubfieldAdd.At(M, K, ca.TermAs[A]("a * a"), ca.TermAs[A]("b * b"))))
									normInM := ca.Have(
										"The norm lies in the ambient field",
										"d ∈ M.carrier",
										BySets(normInK, sub, field.SubfieldSubset.At(M, K)))
									inverseCoordinates := ca.Have(
										"The conjugate divided by the norm has base-field coordinates",
										"a / d ∈ K ∧ -(b / d) ∈ K",
										By(
											fieldM,
											normInK,
											sub,
											coordinates,
											field.SubfieldDiv.At(M, K, a, d),
											field.SubfieldDiv.At(M, K, b, d),
											field.SubfieldNeg.At(M, K, ca.TermAs[A]("b / d"))))
									inverseCarriers := ca.Have(
										"The inverse coordinates lie in the ambient field",
										"a / d ∈ M.carrier ∧ -(b / d) ∈ M.carrier",
										BySets(sub, inverseCoordinates, field.SubfieldSubset.At(M, K)))
									inverse := ca.TermAs[A]("«withCoordinates»(M, i, a / d, -(b / d))")
									elementsInM := ca.Have(
										"The element and its proposed inverse lie in the ambient field",
										"x ∈ M.carrier ∧ «withCoordinates»(M, i, a / d, -(b / d)) ∈ M.carrier",
										By(
											i,
											carriers,
											inverseCarriers,
											coordinates,
											comm_ring.MulIn.Read(ring).AsFact().At(i, b),
											comm_ring.AddIn.Read(ring).AsFact().At(a, ca.TermAs[A]("i * b")),
											comm_ring.MulIn.Read(ring).AsFact().At(i, ca.TermAs[A]("-(b / d)")),
											comm_ring.AddIn.Read(ring).AsFact().At(ca.TermAs[A]("a / d"), ca.TermAs[A]("i * -(b / d)"))))
									// (a/d − i·b/d)(a + ib) = (a² − i²b²)/d = (a² + b²)/d = 1.
									inverseProduct := ca.Have(
										"The proposed inverse times the element is one",
										"«withCoordinates»(M, i, a / d, -(b / d)) * «withCoordinates»(M, i, a, b) = M.one",
										ByArith(
											fieldM,
											normNonzero,
											Scaled(ca.TermAs[A]("M.inv(d)"), dDef),
											Scaled(ca.TermAs[A]("-(b * b / d)"), iSquared),
											normInM,
											i,
											carriers))
									ca.Show(
										"Inverse uniqueness gives the inverse base coordinates",
										By(
											inverseProduct,
											elementsInM,
											inverseCoordinates,
											coordinates,
											field.InvLeftUniqueOn.Read(fieldM).AsFact().At(inverse, x),
											At(hasBaseCoordinates, M, K, i, ca.TermAs[A]("a / d"), ca.TermAs[A]("-(b / d)"))))
								})
						})),
				))
		})

		adjoinHasBaseCoordinates := ctx.Lemma(Statement{
			Binders: "∀M:field_ops(A). ∀K:set(A). ∀lt:(A → A → bool). ∀i:A.",
			Hypotheses: []string{
				"field_on(M)",
				"subfield(M, K)",
				"ordered_field_on(restrict_field(M, K), lt)",
				"i ∈ M.carrier",
				"i * i = -M.one",
			},
			Conclusion: "field_adjoin(M, K, {i}) ⊆ «withBaseCoordinates»(M, K, i)",
		}, func(
			arg *Argument,
			M *Expr[FieldOps[A]],
			fieldM field.FieldFact[on.M],
			K *Expr[Set[A]],
			sub Fact,
			lt *Arrow2[A, A, Bool],
			ordered Fact,
			i *Member[A, on.M],
			iSquared Fact,
		) {
			zero := arg.TermAs[A]("M.zero")
			one := arg.TermAs[A]("M.one")
			containsK := arg.Have(
				"The base field has base coordinates",
				"K ⊆ «withBaseCoordinates»(M, K, i)",
				Unfold(set_basic.SubsetDef),
				Derive(func(br *Argument) {
					x := br.FixAs[A]("x")
					xInK := br.Assume()
					xInM := br.Have(
						"A base-field element lies in the ambient field",
						"x ∈ M.carrier",
						BySets(xInK, sub, field.SubfieldSubset.At(M, K)))
					realForm := br.Have(
						"A real element has zero imaginary coordinate",
						"x = «withCoordinates»(M, i, x, M.zero)",
						ByArith(fieldM, i, xInM))
					br.Show(
						"x has real coordinate x and imaginary coordinate zero",
						By(realForm, xInK, sub, field.SubfieldZero.At(M, K), At(hasBaseCoordinates, M, K, i, x, zero)))
				}))
			imaginaryForm := arg.Have(
				"The generator has coordinates zero and one",
				"i = «withCoordinates»(M, i, M.zero, M.one)",
				ByArith(fieldM, i))
			containsI := arg.Have(
				"The generator i has base coordinates",
				"i ∈ «withBaseCoordinates»(M, K, i)",
				By(
					Normalized,
					imaginaryForm,
					sub,
					field.SubfieldZero.At(M, K),
					field.SubfieldOne.At(M, K),
					At(hasBaseCoordinates, M, K, i, zero, one)))
			arg.Show(
				"The least subfield containing K and i lies inside the elements a + ib",
				By(
					containsK,
					containsI,
					fieldM,
					sub,
					ordered,
					i,
					iSquared,
					At(baseCoordinatesSubfield, M, K, lt, i),
					algebraic_element.AdjoinElementBetween.At(
						M, K, arg.TermAs[Set[A]]("«withBaseCoordinates»(M, K, i)"), i)))
		})

		return ctx.Theorem(headline,
			func(
				arg *Argument,
				M *Expr[FieldOps[A]],
				fieldM field.FieldFact[on.M],
				K *Expr[Set[A]],
				sub Fact,
				lt *Arrow2[A, A, Bool],
				euclidean Fact,
				i *Member[A, on.M],
				iSquared Fact,
			) {
				ordered := ordered_field.EuclideanOrderedField.Read(euclidean)
				arg.Do(Unfold(field.SquareClosedDef))
				arg.FixAs[A]("z")
				inAdjoin := arg.Assume()
				inForms := arg.Have(
					"Every element of K(i) has two base-field coordinates",
					"z ∈ «withBaseCoordinates»(M, K, i)",
					BySets(fieldM, sub, ordered, i, iSquared, inAdjoin, At(adjoinHasBaseCoordinates, M, K, lt, i)))
				a, b, coordinates := arg.Unpack2As[A, A](inForms, "a", "b")
				u, v, roots := arg.Obtain2As[A, A](
					"Choose the two square-root coordinates",
					"∃u v:A. u ∈ K ∧ v ∈ K ∧ u * u - v * v = a ∧ (M.one + M.one) * (u * v) = b",
					By(
						euclidean,
						coordinates,
						SquareRootCoordinates.At(arg.TermAs[FieldOps[A]]("restrict_field(M, K)"), lt, a, b),
						field.RestrictFieldDef.At(M, K)))
				rootParts := arg.Conjuncts(
					roots,
					"The real root coordinate belongs to K",
					"The imaginary root coordinate belongs to K",
					"Their difference of squares is the real part",
					"Their doubled product is the imaginary part")
				adjoin := arg.Have(
					"K(i) is a subfield containing K and i",
					"subfield(M, field_adjoin(M, K, {i})) ∧ K ⊆ field_adjoin(M, K, {i}) ∧ i ∈ field_adjoin(M, K, {i})",
					By(fieldM, i, sub, algebraic_element.AdjoinElementSubfield.At(M, K, i)))
				carriers := arg.Have(
					"The original and root coordinates lie in the ambient field",
					"a ∈ M.carrier ∧ b ∈ M.carrier ∧ u ∈ M.carrier ∧ v ∈ M.carrier",
					BySets(rootParts[0], rootParts[1], sub, coordinates, field.SubfieldSubset.At(M, K)))
				rootCoordinatesInAdjoin := arg.Have(
					"The root coordinates belong to K(i)",
					"u ∈ field_adjoin(M, K, {i}) ∧ v ∈ field_adjoin(M, K, {i})",
					BySets(rootParts[0], rootParts[1], adjoin))
				rootInAdjoin := arg.Have(
					"Their linear combination belongs to K(i)",
					"«withCoordinates»(M, i, u, v) ∈ field_adjoin(M, K, {i})",
					By(
						rootCoordinatesInAdjoin,
						adjoin,
						field.SubfieldMul.At(M, arg.TermAs[Set[A]]("field_adjoin(M, K, {i})"), i, v),
						field.SubfieldAdd.At(M, arg.TermAs[Set[A]]("field_adjoin(M, K, {i})"), u, arg.TermAs[A]("i * v"))))
				square := arg.Have(
					"The two coordinate equations give the required square",
					"«withCoordinates»(M, i, u, v) * «withCoordinates»(M, i, u, v) = «withCoordinates»(M, i, a, b)",
					ByArith(
						fieldM,
						Scaled(arg.TermAs[A]("v * v"), iSquared),
						Scaled(i, rootParts[3]),
						rootParts[2],
						i,
						carriers))
				arg.Take(arg.TermAs[A]("«withCoordinates»(M, i, u, v)"))
				arg.Show(
					"This element of K(i) squares to z",
					By(square, rootInAdjoin, coordinates))
			})
	}),
})}
