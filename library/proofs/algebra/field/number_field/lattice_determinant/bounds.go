package lattice_determinant

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/symmetric_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/int_lattice"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/characteristic_zero"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/vector/determinant"
	"github.com/euc-ai/xugo/library/registry"
)

// DeterminantIntegralEntries — a matrix over the integer image has its
// determinant in the integer image: the image is a commutative ring, and a
// determinant lies in its ring's carrier.
var DeterminantIntegralEntries = determinantIntegralEntriesThm{family.Add(registry.ProofEntry{
	Name: "DeterminantIntegralEntries",
	Key:  "prop_527a8850274d8b52",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀n:num. ∀P:(num → num → A).",
		Hypotheses: []string{
			"characteristic_zero(field_ring(L))",
			"matrix_over(«ℤ», n, P)",
		},
		Conclusion: "determinant(«ℤ», n, P) ∈ integer_image(field_ring(L))",
	}, func(a *Argument, L field.FieldFact[on.L], n *Expr[Nat], P *Mat[A, DimN, DimN], h Fact) {
		subring := a.Have(
			"the integer image is a subring of L",
			"subring(field_ring(L), integer_image(field_ring(L)))",
			By(int_lattice.IntegerRationalImagesStructure.Read(L), h))
		integers := a.Have(
			"so a commutative ring under L's operations",
			"comm_ring_on(«ℤ»)",
			By(
				subring,
				comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(
					a.TermAs[Set[A]]("integer_image(field_ring(L))"))))
		a.Show(
			"the determinant belongs to the integer image",
			By(h, determinant.DeterminantInCarrier.Read(integers)))
	}),
})}

// DeterminantEntryBound — bounded rational entries bound the determinant:
// each Leibniz term has size at most Hⁿ, and there are n! terms.
var DeterminantEntryBound = determinantEntryBoundThm{family.Add(registry.ProofEntry{
	Name: "DeterminantEntryBound",
	Key:  "prop_bfb65bae7ea69579",
	Build: family.Sections(Statement{
		Binders: "∀L:field_on(A). ∀n:num. ∀P:(num → num → A). ∀H:real.",
		Hypotheses: []string{
			"characteristic_zero(field_ring(L))",
			"matrix_over(restrict_ring(field_ring(L), rational_image(L)), n, P)",
			"∀i j:num. i < n ∧ j < n ⇒ |rational_value(L, P(i, j))| ≤ H",
		},
		Conclusion: "|rational_value(L, determinant(restrict_ring(field_ring(L), rational_image(L)), n, P))| ≤ " +
			"real_of_num(factorial(n)) * H ^ n",
	}, func(ctx *Script, headline string) *GoalStackNode {
		productBound := ctx.Lemma(Statement{
			Binders: "∀R:comm_ring_on(A). ∀h:(A → real). ∀f:(num → A). ∀H:real.",
			Hypotheses: []string{
				"h(R.one) = &1",
				"∀u v:A. u ∈ R.carrier ∧ v ∈ R.carrier ⇒ h(u * v) = h(u) * h(v)",
				"∀i:num. f(i) ∈ R.carrier",
			},
			Conclusion: "∀s:set(num). " +
				"    finite(s) ∧ (∀i:num. i ∈ s ⇒ |h(f(i))| ≤ H) ⇒ " +
				"    module_sum(R.mul, R.one, s, f) ∈ R.carrier ∧ " +
				"    |h(module_sum(R.mul, R.one, s, f))| ≤ H ^ card(s)",
		}, func(
			a *Argument,
			R comm_ring.CommRingFact[on.R],
			h *Arrow[A, Real],
			f *Arrow[Nat, A],
			H *Expr[Real],
			assumptions Fact,
		) {
			parts := a.Conjuncts(
				assumptions,
				"h keeps one",
				"h keeps multiplication on the carrier",
				"all factors lie in the carrier")
			oneValue, multiplies, factorsIn := parts[0], parts[1], parts[2]
			a.Show(
				"finite induction bounds every product of bounded factors",
				ByInduction(finite_set.FiniteInductFreshOn,
					Case(
						"the empty product has value one and exponent zero",
						Simp(
							Fwd(module.ModuleSumEmpty),
							Fwd(oneValue),
							Fwd(cardinality.CardClauses.Inst[Nat]()),
							Fwd(real_pow.Pow),
							Fwd(real_sgn_abs.AbsOfNum)),
						By(comm_ring.OneIn.Read(R), real_order_ring.LessEqRefl.At(a.TermAs[Real]("&1")))),
					Case(
						"a fresh factor multiplies the bound by H",
						Derive(func(b *Argument) {
							x := b.FixAs[Nat]("x")
							t := b.FixAs[Set[Nat]]("t")
							induction := b.Assume()
							productT := b.TermAs[A]("module_sum(R.mul, R.one, t, f)")
							fx := f.Apply(x)
							peel := b.Have(
								"the new factor peels off the product",
								"module_sum(R.mul, R.one, insert(x, t), f) = f(x) * module_sum(R.mul, R.one, t, f)",
								By(
									induction,
									factorsIn,
									module.ModuleSumInsertMonoid.Read(comm_ring.MulMonoidOn.Read(R)).At(t, x, f)))
							count := b.Have(
								"the fresh index raises the cardinality by one",
								"card(insert(x, t)) = suc(card(t))",
								By(induction, cardinality.CardClauses))
							absProduct := b.Have(
								"the absolute value factors",
								"|h(module_sum(R.mul, R.one, insert(x, t), f))| = |h(f(x))| * |h(module_sum(R.mul, R.one, t, f))|",
								By(
									multiplies.At(fx, productT),
									factorsIn.At(x),
									peel,
									induction,
									real_sgn_abs.AbsMul.At(h.Apply(fx), h.Apply(productT))))
							mulBound := b.Have(
								"multiply the two nonnegative absolute-value bounds",
								"|h(f(x))| * |h(module_sum(R.mul, R.one, t, f))| ≤ H * H ^ card(t)",
								By(
									induction,
									real_order_ring.LessEqMul2.At(
										b.TermAs[Real]("|h(f(x))|"),
										H,
										b.TermAs[Real]("|h(module_sum(R.mul, R.one, t, f))|"),
										b.TermAs[Real]("H ^ card(t)")),
									real_sgn_abs.AbsNonneg.At(h.Apply(fx)),
									real_sgn_abs.AbsNonneg.At(h.Apply(productT))))
							b.Show(
								"the product stays in the carrier and satisfies the successor-power bound",
								By(
									comm_ring.MulIn.Read(R),
									factorsIn.At(x),
									peel,
									count,
									absProduct,
									mulBound,
									induction,
									real_pow.Pow))
						}))))
		})
		return ctx.Theorem(headline, func(
			a *Argument,
			L field.FieldFact[on.L],
			n *Expr[Nat],
			P *Mat[A, DimN, DimN],
			H *Expr[Real],
			assumptions Fact,
		) {
			parts := a.Conjuncts(
				assumptions,
				"the field has characteristic zero",
				"P is a matrix over the rational image",
				"the entries have absolute value at most H")
			characteristic, matrixOver, entriesBound := parts[0], parts[1], parts[2]
			l := a.TermAs[FieldOps[A]]("L")
			q := a.TermAs[Set[A]]("rational_image(L)")
			r := a.TermAs[comm_ring.RingOps[A]]("restrict_ring(field_ring(L), rational_image(L))")
			indices := a.TermAs[Set[Nat]]("{i:num | i < n}")
			permutations := a.TermAs[Set[symmetric_group.Permutation[Nat]]]("symmetric_group({i:num | i < n})")
			inverse := a.TermAs[Fun[A, Real]]("rational_value(L)")
			rationalSubfield := a.Have(
				"the rational image is a subfield",
				"subfield(L, rational_image(L))",
				By(characteristic_zero.RationalEmbedding.Read(L), characteristic))
			ring := a.Have(
				"the rational image inherits the commutative ring operations",
				"comm_ring_on(restrict_ring(field_ring(L), rational_image(L)))",
				By(
					rationalSubfield,
					comm_ring.ClosedSubsetRingOn.Read(field.RingOn.Read(L)).At(q),
					field.SubfieldDef.At(l, q)))
			entriesIn := a.Have(
				"all entries lie in the rational carrier, including the zero padding",
				"∀i j:num. P(i, j) ∈ rational_image(L)",
				By(matrixOver, determinant.MatrixOverEntries.Read(ring).At(n, P)))
			indexCount := a.Have(
				"the index set is finite with n members",
				"finite({i:num | i < n}) ∧ card({i:num | i < n}) = n",
				By(num_segment.HasSizeBelowStrict.At(n), cardinality.HasSizeDef.At(indices, n)))
			permutationCount := a.Have(
				"the finite permutation group has factorial cardinality",
				"finite(symmetric_group({i:num | i < n})) ∧ card(symmetric_group({i:num | i < n})) = factorial(n)",
				By(
					indexCount,
					symmetric_group.CardSymmetricGroup.At(indices),
					cardinality.HasSizeDef.At(permutations, a.TermAs[Nat]("factorial(card({i:num | i < n}))"))))
			products := a.Let(
				"v",
				a.TermAs[Fun[symmetric_group.Permutation[Nat], A]](
					"λp:permutation(num). "+
						"    module_sum(L.mul, L.one, {i:num | i < n}, λi:num. P(i, permutation_map(p, i)))"))
			units := a.Have(
				"the inverse keeps zero and the signed units",
				"rational_value(L, L.zero) = &0 ∧ rational_value(L, L.one) = &1 ∧ rational_value(L, -L.one) = -&1",
				By(characteristic, characteristic_zero.RationalValueZeroOneNegOne.Read(L)))
			multiplies := a.Have(
				"the inverse keeps multiplication on the rational carrier",
				Statement{
					Binders: "∀u v:A.",
					Hypotheses: []string{
						"u ∈ rational_image(L)",
						"v ∈ rational_image(L)",
					},
					Conclusion: "rational_value(L, u * v) = rational_value(L, u) * rational_value(L, v)",
				},
				By(characteristic, characteristic_zero.RationalValueAddMul.Read(L)))
			productsBound := a.Have(
				"each unsigned Leibniz product has size at most H to the n",
				Statement{
					Binders: "∀p:permutation(num).",
					Hypotheses: []string{
						"p ∈ symmetric_group({i:num | i < n})",
					},
					Conclusion: "v(p) ∈ rational_image(L) ∧ |rational_value(L, v(p))| ≤ H ^ n",
				},
				Derive(func(b *Argument) {
					p := b.FixAs[symmetric_group.Permutation[Nat]]("p")
					inGroup := b.Assume()
					factorsBound := b.Have(
						"every factor uses two indices below n",
						"∀i:num. i ∈ {i:num | i < n} ⇒ |rational_value(L, P(i, permutation_map(p, i)))| ≤ H",
						Derive(func(c *Argument) {
							i := c.FixAs[Nat]("i")
							inIndices := c.Assume()
							c.Show(
								"a permutation preserves the index set",
								BySets(
									entriesBound.At(i, c.TermAs[Nat]("permutation_map(p, i)")),
									inIndices,
									inGroup,
									symmetric_group.SymmetricGroupMapsInto.At(indices, p, i)))
						}))
					factors := b.TermAs[Fun[Nat, A]]("λi:num. P(i, permutation_map(p, i))")
					b.Show(
						"apply the finite product bound at the n matrix indices",
						By(
							ring,
							multiplies,
							entriesIn,
							factorsBound,
							products,
							indexCount,
							units,
							At(productBound, r, inverse, factors, H, indices)))
				}))
			coefficients := a.Let(
				"c",
				a.TermAs[Fun[symmetric_group.Permutation[Nat], A]](
					"λp:permutation(num). COND(permutation_even(n, p), L.one, -L.one)"))
			summands := a.Let(
				"t", a.TermAs[Fun[symmetric_group.Permutation[Nat], A]]("λp:permutation(num). c(p) * v(p)"))
			coefficientsUnit := a.Have(
				"each sign coefficient has absolute rational value one",
				"∀p:permutation(num). c(p) ∈ rational_image(L) ∧ |rational_value(L, c(p))| = &1",
				Derive(func(b *Argument) {
					b.FixAs[symmetric_group.Permutation[Nat]]("p")
					b.Cases(b.Term("permutation_even(n, p)"))
					b.When(
						"p is even, and the coefficient is one",
						func(c *Argument, even Fact) {
							c.Show(
								"one is rational and has absolute value one",
								By(
									comm_ring.OneIn.Read(ring),
									coefficients,
									even,
									units,
									real_sgn_abs.AbsOfNum.At(c.TermAs[Nat]("1"))))
						})
					b.Otherwise(
						"p is odd, and the coefficient is minus one",
						func(c *Argument, odd Fact) {
							c.Show(
								"minus one is rational and has absolute value one",
								By(
									Normalized,
									comm_ring.OneIn.Read(ring),
									comm_ring.NegIn.Read(ring),
									coefficients,
									odd,
									units,
									real_sgn_abs.AbsEven.At(c.TermAs[Real]("&1")),
									real_sgn_abs.AbsOfNum.At(c.TermAs[Nat]("1"))))
						})
				}))
			summandsBound := a.Have(
				"each signed Leibniz term lies in the carrier and has the same bound",
				Statement{
					Binders: "∀p:permutation(num).",
					Hypotheses: []string{
						"p ∈ symmetric_group({i:num | i < n})",
					},
					Conclusion: "t(p) ∈ rational_image(L) ∧ |rational_value(L, t(p))| ≤ H ^ n",
				},
				Derive(func(b *Argument) {
					p := b.FixAs[symmetric_group.Permutation[Nat]]("p")
					inGroup := b.Assume()
					cp, vp := b.TermAs[A]("c(p)"), b.TermAs[A]("v(p)")
					b.Show(
						"multiply by an absolute unit",
						By(
							comm_ring.MulIn.Read(ring),
							multiplies.At(cp, vp),
							productsBound.At(p),
							coefficientsUnit.At(p),
							summands,
							inGroup,
							real_sgn_abs.AbsMul.At(
								b.TermAs[Real]("rational_value(L, c(p))"), b.TermAs[Real]("rational_value(L, v(p))")),
							real_construction.MulLeftId.At(b.TermAs[Real]("|rational_value(L, v(p))|"))))
				}))
			adds := a.Have(
				"the inverse keeps addition on the rational carrier",
				Statement{
					Binders: "∀u v:A.",
					Hypotheses: []string{
						"u ∈ rational_image(L)",
						"v ∈ rational_image(L)",
					},
					Conclusion: "rational_value(L, u + v) = rational_value(L, u) + rational_value(L, v)",
				},
				By(characteristic, characteristic_zero.RationalValueAddMul.Read(L)))
			t := a.TermAs[Fun[symmetric_group.Permutation[Nat], A]]("t")
			realTerms := a.TermAs[Fun[symmetric_group.Permutation[Nat], Real]](
				"λp:permutation(num). rational_value(L, t(p))")
			leibniz := a.Have(
				"the determinant is the finite sum of the signed products",
				"determinant(restrict_ring(field_ring(L), rational_image(L)), n, P) = "+
					"module_sum(L.add, L.zero, symmetric_group({i:num | i < n}), t)",
				By(coefficients, summands, products, determinant.DeterminantDef.At(r, n, P)))
			transported := a.Have(
				"the inverse carries the Leibniz sum to real addition",
				"rational_value(L, determinant(restrict_ring(field_ring(L), rational_image(L)), n, P)) = "+
					"module_sum(real_add, "+
					"    &0, "+
					"    symmetric_group({i:num | i < n}), "+
					"    λp:permutation(num). rational_value(L, t(p)))",
				By(
					adds,
					summandsBound,
					leibniz,
					permutationCount,
					units,
					module.ModuleSumMonoidHomomorphism.Read(comm_ring.AddMonoidOn.Read(ring)).At(
						a.TermAs[Op[Real]]("real_add"), a.TermAs[Real]("&0"), inverse, permutations, t)))
			realSum := a.Have(
				"the rational value of the determinant is a finite real sum",
				"rational_value(L, determinant(restrict_ring(field_ring(L), rational_image(L)), n, P)) = "+
					"sum(symmetric_group({i:num | i < n}), λp:permutation(num). rational_value(L, t(p)))",
				By(transported, permutationCount, real_sum.RealModuleSum.At(realTerms, permutations)))
			a.Show(
				"the triangle bound sums factorial n terms of size at most H to the n",
				By(
					summandsBound,
					realSum,
					permutationCount,
					real_sum.TriangleBound.At(permutations, realTerms, a.TermAs[Real]("H ^ n"))))
		})
	}),
})}
