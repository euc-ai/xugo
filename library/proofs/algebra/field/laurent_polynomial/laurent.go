// laurent.go — Laurent polynomials in t: the powers tⁿ at integer
// exponents, the Laurent ring k[t, 1/t] they lie in, and k[t] or k[1/t]
// holding each by the sign of its exponent; finite sums Σ c(j) · tʲ with
// coefficients in k, added and scaled coefficientwise, placed in k[t] or in
// tⁿ · k[1/t] by their exponents, moved along by a power of t and read as
// polynomials when their exponents are natural numbers; and the
// coefficients of a member of the Laurent ring — its expansion exists, is
// unique when t is transcendental over k, and is k-linear — with the
// polynomials in an element s read among them.

package laurent_polynomial

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_away"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_embed"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_real_lift"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// ---------------------------------------------------------------------------
// The monomials
// ---------------------------------------------------------------------------

// LaurentMonomialOfNum — at a natural exponent n, tⁿ is the n-th power of
// t and t⁻ⁿ the n-th power of inv(t): the two branches of the definition,
// read at &n and at −&n, where at n = 0 the guard takes the first branch
// and both powers are one. Nothing is asked of t or of the operations.
var LaurentMonomialOfNum = laurentMonomialOfNumThm{family.Add(registry.ProofEntry{
	Name: "LaurentMonomialOfNum",
	Key:  "prop_744cf67ef586088e",
	Build: family.Theorem("∀mul:(A → A → A). ∀one:A. ∀inv:(A → A). ∀t:A. ∀n:num. "+
		"    laurent_monomial(mul, one, inv, t, &n) = monoid_pow(mul, one, t, n) ∧ "+
		"    laurent_monomial(mul, one, inv, t, -&n) = monoid_pow(mul, one, inv(t), n)",
		func(
			arg *Argument,
			mul *Arrow2[A, A, A],
			one *Expr[A],
			inv *Arrow[A, A],
			t *Expr[A],
			n *Expr[Nat],
		) {
			arg.Do(Unfold(LaurentMonomialDef), SplitConj(
				Case(
					"at &n the guard &0 ≤ &n holds and num_of_int(&n) = n",
					By(Normalized, int_embed.OfNumRetract.At(n), int_embed.EmbedNonneg.At(n))),
				Case(
					"at −&n the second branch is taken, unless n = 0 where both branches are one",
					Derive(func(b *Argument) {
						b.Cases(b.Term("n = 0"))
						b.When(
							"at n = 0, −&0 = &0 and both powers are the empty product",
							func(c *Argument, zero Fact) {
								c.Show(
									"both branches are then the empty product one",
									zero.Rw(),
									Simp(Fwd(int_real_lift.NegZero), Fwd(int_embed.OfNumRetract), Fwd(comm_monoid.MonoidPowDef)),
									Basic())
							})
						b.Otherwise(
							"for n ≠ 0 the exponent −&n is negative, and −(−&n) = &n",
							func(c *Argument, nonzero Fact) {
								positive := c.Have(
									"n is positive",
									"0 < n",
									ByArith(nonzero))
								negative := c.Have(
									"so −&n lies below &0",
									"¬(0 ≤ -int_of_num(n))",
									ByArith(positive))
								c.Show(
									"the second branch, at num_of_int(&n) = n",
									By(Normalized, negative, int_real_lift.NegNeg.At(c.TermAs[Int]("n")), int_embed.OfNumRetract.At(n)))
							})
					})),
			))
		}),
})}

// LaurentMonomialProduct — the powers of a nonzero t at integer
// exponents are nonzero members of the field and multiply by adding
// exponents.
//
// Every integer is a difference of two naturals, and at a − b the
// monomial is tᵃ · inv(t)ᵇ: the part the two powers share cancels,
// t · inv(t) being one. Two monomials in that form multiply by adding
// the exponents of t and of inv(t) separately, which is the product law
// with no case on the signs. Either branch of the definition is a power
// of t or of inv(t), so every monomial lies in L, and tᵐ · t⁻ᵐ = t⁰ = one
// keeps it off zero.
var LaurentMonomialProduct = laurentMonomialProductThm{family.Add(registry.ProofEntry{
	Name: "LaurentMonomialProduct",
	Key:  "prop_93b40dcfad11934",
	Reading: "t ≠ zero is load-bearing for tᵐ ≠ zero and for the product law, where t · t⁻¹ = t⁰ " +
		"rests on t · inv(t) = one; the three small exponents and membership in L hold at t = zero too.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀t:A.",
		Hypotheses: []string{
			"t ∈ L.carrier",
			"t ≠ L.zero",
		},
		Conclusion: "laurent_monomial(t, &0) = L.one ∧ " +
			"laurent_monomial(t, &1) = t ∧ " +
			"laurent_monomial(t, -&1) = L.inv(t) ∧ " +
			"(∀m n:int. " +
			"    laurent_monomial(t, m) ∈ L.carrier ∧ " +
			"    laurent_monomial(t, m) ≠ L.zero ∧ " +
			"    laurent_monomial(t, m) * laurent_monomial(t, n) = laurent_monomial(t, m + n))",
	},
		func(arg *Argument, L field.FieldFact[on.L], t *Expr[A], h Fact) {
			guard := arg.Conjuncts(
				h,
				"t lies in L",
				"t is not zero")
			tm := arg.MemberOf[on.L](t, guard[0])
			um := field.InvIn.Read(L).At(tm)
			ring := field.RingOn.Read(L)
			monoid := comm_ring.MulMonoidOn.Read(ring)

			small := arg.Have(
				"t⁰, t¹ and t⁻¹ are the powers of t and of inv(t) at 0 and 1",
				"laurent_monomial(t, &0) = L.one ∧ "+
					"laurent_monomial(t, &1) = t ∧ "+
					"laurent_monomial(t, -&1) = L.inv(t)",
				Simp(
					Fwd(LaurentMonomialOfNum),
					Fwd(comm_monoid.MonoidPowDef),
					Fwd(comm_monoid.PowOneOn.Read(monoid)),
					Fwd(field.InvIn.Read(L))),
				Basic())
			unit := arg.Have(
				"t · inv(t) = one, t being a nonzero member of L",
				"t * L.inv(t) = L.one",
				By(field.MulRightInverseOn.Read(L).AsFact().At(t), tm, guard[1]))
			cancel := arg.Have(
				"so their powers are inverse too: tᵏ · inv(t)ᵏ = one",
				"∀k:num. monoid_pow(L.mul, L.one, t, k) * monoid_pow(L.mul, L.one, L.inv(t), k) = L.one",
				arg.ForEach(func(k *Expr[Nat]) Action {
					return By(unit, comm_monoid.PowInverseOn.Read(monoid).At(tm, um, k))
				}))

			difference := arg.Have(
				"tᵃ · inv(t)ᵇ is the Laurent monomial at a − b",
				"∀a b:num. "+
					"    laurent_monomial(t, &a - &b) = "+
					"    monoid_pow(L.mul, L.one, t, a) * monoid_pow(L.mul, L.one, L.inv(t), b)",
				Derive(func(b *Argument) {
					p, q := b.FixAs[Nat](), b.FixAs[Nat]()
					b.Do(nat_order.LessEqTotal.At(p, q).SplitDisj(
						LeftHolds(
							"a ≤ b: with b = a + d, tᵃ cancels inv(t)ᵃ and inv(t)ᵈ is the monomial at −d",
							Given(func(c *Argument, below Fact) {
								d, gap := c.ObtainAs[Nat](
									"b exceeds a by some d",
									"∃d:num. b = a + d",
									By(below, nat_order.LessEqExists.At(q, p)))
								exponent := c.Have(
									"a − (a + d) = −d",
									"a - &(a + d) = -int_of_num(d)",
									ByArith())
								c.Show(
									"tᵃ · inv(t)ᵃ⁺ᵈ = (tᵃ · inv(t)ᵃ) · inv(t)ᵈ = inv(t)ᵈ",
									gap.Rw(),
									exponent.Rw(),
									Simp(Fwd(LaurentMonomialOfNum)),
									ByArith(
										ring,
										tm,
										um,
										Scaled(
											c.TermAs[A]("monoid_pow(L.mul, L.one, t, a)"),
											comm_monoid.PowAddOn.Read(monoid).AsFact().At(um, p, d)),
										Scaled(c.TermAs[A]("monoid_pow(L.mul, L.one, L.inv(t), d)"), cancel.At(p))))
							})),
						RightHolds(
							"b ≤ a: with a = b + d, inv(t)ᵇ cancels tᵇ and tᵈ is the monomial at d",
							Given(func(c *Argument, above Fact) {
								d, gap := c.ObtainAs[Nat](
									"a exceeds b by some d",
									"∃d:num. a = b + d",
									By(above, nat_order.LessEqExists.At(p, q)))
								exponent := c.Have(
									"(b + d) − b = d",
									"b + d - &b = int_of_num(d)",
									ByArith())
								c.Show(
									"tᵇ⁺ᵈ · inv(t)ᵇ = tᵈ · (tᵇ · inv(t)ᵇ) = tᵈ",
									gap.Rw(),
									exponent.Rw(),
									Simp(Fwd(LaurentMonomialOfNum)),
									ByArith(
										ring,
										tm,
										um,
										Scaled(
											c.TermAs[A]("monoid_pow(L.mul, L.one, L.inv(t), b)"),
											comm_monoid.PowAddOn.Read(monoid).AsFact().At(tm, q, d)),
										Scaled(c.TermAs[A]("monoid_pow(L.mul, L.one, t, d)"), cancel.At(q))))
							})),
					))
				}))
			presentation := arg.Have(
				"every integer is a difference of two naturals, its sign deciding which one is zero",
				"∀m:int. ∃a b:num. m = &a - &b",
				arg.ForEach(func(m *Expr[Int]) Action {
					return By(int_embed.Image.At(m), int_real_lift.SubRightZero, int_real_lift.SubLeftZero)
				}))

			member := arg.Have(
				"every tᵐ lies in L, either branch of the definition being a power of t or of inv(t)",
				"∀m:int. laurent_monomial(t, m) ∈ L.carrier",
				Derive(func(b *Argument) {
					b.FixAs[Int]()
					b.Show(
						"L holds every power of t and of inv(t)",
						Unfold(LaurentMonomialDef),
						By(
							comm_monoid.PowIn.Read(monoid).At(tm, b.TermAs[Nat]("num_of_int(m)")),
							comm_monoid.PowIn.Read(monoid).At(um, b.TermAs[Nat]("num_of_int(-m)"))))
				}))
			product := arg.Have(
				"tᵐ · tⁿ = tᵐ⁺ⁿ",
				"∀m n:int. laurent_monomial(t, m) * laurent_monomial(t, n) = laurent_monomial(t, m + n)",
				Derive(func(b *Argument) {
					m, n := b.FixAs[Int](), b.FixAs[Int]()
					p, q, mIs := b.Obtain2As[Nat, Nat](
						"m = a − b",
						"∃a b:num. m = &a - &b",
						By(presentation.At(m)))
					r, s, nIs := b.Obtain2As[Nat, Nat](
						"n = c − d",
						"∃c d:num. n = &c - &d",
						By(presentation.At(n)))
					sum := b.Have(
						"m + n = (a + c) − (b + d)",
						"m + n = int_of_num(a + c) - int_of_num(b + d)",
						ByArith(mIs, nIs, int_embed.OfNumAdd.At(p, r), int_embed.OfNumAdd.At(q, s)))
					b.Show(
						"the powers of t and of inv(t) add separately",
						CalcEq(
							Leg(
								b.Term(
									"(monoid_pow(L.mul, L.one, t, a) * monoid_pow(L.mul, L.one, L.inv(t), b)) * "+
										"(monoid_pow(L.mul, L.one, t, c) * monoid_pow(L.mul, L.one, L.inv(t), d))"),
								"each factor in its difference form",
								By(mIs, nIs, difference.At(p, q), difference.At(r, s))),
							Leg(
								b.Term("monoid_pow(L.mul, L.one, t, a + c) * monoid_pow(L.mul, L.one, L.inv(t), b + d)"),
								"tᵃ · tᶜ = tᵃ⁺ᶜ and inv(t)ᵇ · inv(t)ᵈ = inv(t)ᵇ⁺ᵈ",
								ByArith(
									ring,
									tm,
									um,
									Scaled(
										b.TermAs[A]("monoid_pow(L.mul, L.one, L.inv(t), b) * monoid_pow(L.mul, L.one, L.inv(t), d)"),
										comm_monoid.PowAddOn.Read(monoid).AsFact().At(tm, p, r)),
									Scaled(
										b.TermAs[A]("monoid_pow(L.mul, L.one, t, a + c)"),
										comm_monoid.PowAddOn.Read(monoid).AsFact().At(um, q, s)))),
							Leg(
								b.Term("laurent_monomial(t, &(a + c) - &(b + d))"),
								"the difference form at a + c and b + d",
								By(difference.At(b.TermAs[Nat]("a + c"), b.TermAs[Nat]("b + d")))),
							FinalLeg(
								"whose exponent is m + n",
								By(sum)),
						))
				}))
			nonvanishing := arg.Have(
				"no tᵐ is zero",
				"∀m:int. laurent_monomial(t, m) ≠ L.zero",
				Derive(func(b *Argument) {
					m := b.FixAs[Int]()
					opposite := b.TermAs[Int]("-m")
					inverse := b.Have(
						"tᵐ · t⁻ᵐ = t⁰ = one",
						"laurent_monomial(t, m) * laurent_monomial(t, -m) = L.one",
						By(product.At(m, opposite), int_real_lift.AddRightInverse.At(m), small))
					b.Show(
						"tᵐ = zero would make one = zero · t⁻ᵐ = zero",
						By(
							inverse,
							field.OneNotZeroOn.Read(L),
							comm_ring.MulLeftZeroOn.Read(ring).AsFact().At(b.TermAs[A]("laurent_monomial(t, -m)")),
							member.At(opposite)))
				}))

			arg.Show(
				"the small exponents, and every tᵐ a nonzero member of L multiplying by adding exponents",
				By(small, member, nonvanishing, product))
		}),
})}

// LaurentMonomialInverse — for t a nonzero member of the field, tⁿ and
// t⁻ⁿ are inverse: their product is t⁰ = one, powers of t multiplying by
// adding exponents (LaurentMonomialProduct).
var LaurentMonomialInverse = laurentMonomialInverseThm{family.Add(registry.ProofEntry{
	Name: "LaurentMonomialInverse",
	Key:  "prop_a423332ef81bd186",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀t:A. ∀n:int.",
		Hypotheses: []string{
			"t ∈ L.carrier",
			"t ≠ L.zero",
		},
		Conclusion: "laurent_monomial(t, n) * laurent_monomial(t, -n) = L.one",
	},
		func(arg *Argument, L field.FieldFact[on.L], t *Expr[A], n *Expr[Int], h Fact) {
			guard := arg.Conjuncts(
				h,
				"t lies in L",
				"t is not zero")
			tm := arg.MemberOf[on.L](t, guard[0])
			cancel := arg.Have(
				"n + (−n) = 0",
				"n + -n = &0",
				ByArith())
			arg.Show(
				"tⁿ · t⁻ⁿ = t⁰ = one",
				By(guard[1], cancel, LaurentMonomialProduct.Read(L).At(tm)))
		}),
})}

// ---------------------------------------------------------------------------
// The Laurent ring k[t, 1/t]
// ---------------------------------------------------------------------------

// LaurentRingSubring — for t a nonzero member of the field, the Laurent ring
// k[t, 1/t] is a subring of L holding k, t and inv(t): it is the ring
// away from t over the subring k[t] of L, which holds k and t
// (RingAwaySubring), and t · inv(t) = one puts inv(t) in it.
var LaurentRingSubring = laurentRingSubringThm{family.Add(registry.ProofEntry{
	Name: "LaurentRingSubring",
	Key:  "prop_4f9399e3d2de3384",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t:A.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"t ≠ L.zero",
		},
		Conclusion: "subring(field_ring(L), «laurentRing») ∧ " +
			"k ⊆ «laurentRing» ∧ " +
			"t ∈ «laurentRing» ∧ " +
			"L.inv(t) ∈ «laurentRing»",
	},
		func(arg *Argument, L field.FieldFact[on.L], k *Expr[Set[A]], t *Expr[A], h Fact) {
			hyp := arg.Conjuncts(
				h,
				"k is a subfield of L",
				"t lies in L",
				"t is not zero")
			subK, tInL, nonzero := hyp[0], hyp[1], hyp[2]
			tm := arg.MemberOf[on.L](t, tInL)
			chart := arg.Conjuncts(
				arg.Have(
					"k[t] is a ring holding k and t, inside L",
					"subring(field_ring(L), «polynomials») ∧ "+
						"k ⊆ «polynomials» ∧ "+
						"t ∈ «polynomials» ∧ "+
						"«polynomials» ⊆ field_adjoin(L, k, {t})",
					By(subK, algebraic_element.PolynomialImageRing.Read(L).At(k, tm))),
				"k[t] is a subring of L",
				"k lies in k[t]",
				"t lies in k[t]",
				"k[t] lies in k(t)")
			ringL := arg.TermAs[module_record.RingOps[A]]("field_ring(L)")
			away := arg.Conjuncts(
				arg.Have(
					"the ring away from t over k[t] is a subring of L holding k[t] and every u with t · u = one",
					"«polynomials» ⊆ «laurentRing» ∧ "+
						"subring(field_ring(L), «laurentRing») ∧ "+
						"(∀u:A. u ∈ L.carrier ∧ L.mul(t, u) = L.one ⇒ u ∈ «laurentRing»)",
					By(
						chart[0],
						chart[2],
						field.RingOn.Read(L),
						ring_away.RingAwaySubring.At(ringL, arg.TermAs[Set[A]]("«polynomials»"), t))),
				"k[t] lies in the Laurent ring",
				"the Laurent ring is a subring of L",
				"it holds the inverses of t")
			kIn := arg.Have(
				"k lies in the Laurent ring, through k[t]",
				"k ⊆ «laurentRing»",
				BySets(chart[1], away[0]))
			tIn := arg.Have(
				"so does t",
				"t ∈ «laurentRing»",
				BySets(chart[2], away[0]))
			invIn := arg.Have(
				"and inv(t), as t · inv(t) = one",
				"L.inv(t) ∈ «laurentRing»",
				By(
					nonzero,
					away[2].At(arg.TermAs[A]("L.inv(t)")),
					field.InvIn.Read(L).At(tm),
					field.MulRightInverseOn.Read(L).At(tm)))
			arg.Show(
				"the Laurent ring is a subring of L holding k, t and inv(t)",
				By(away[1], kIn, tIn, invIn))
		}),
})}

// LaurentScalarSubring — for t a nonzero member of the field, k is a subring of
// the Laurent ring k[t, 1/t] under its operations: k lies in the Laurent ring
// (LaurentRingSubring), which is a ring under L's operations, and k, a field
// under them, is a ring under the Laurent ring's.
var LaurentScalarSubring = laurentScalarSubringThm{family.Add(registry.ProofEntry{
	Name: "LaurentScalarSubring",
	Key:  "prop_21e480d5a336016e",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t:A.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"t ≠ L.zero",
		},
		Conclusion: "subring(«laurentRingOps», k)",
	},
		func(a *Argument, L field.FieldFact[on.L], k *Expr[Set[A]], t *Expr[A], h Fact) {
			hyp := a.Conjuncts(
				h,
				"k is a subfield of L",
				"t lies in L",
				"t is not zero")
			subK, tInL, nonzero := hyp[0], hyp[1], hyp[2]
			tm := a.MemberOf[on.L](t, tInL)
			overlap := a.Conjuncts(
				a.Have(
					"the Laurent ring is a subring of L holding k",
					"subring(field_ring(L), «laurentRing») ∧ k ⊆ «laurentRing»",
					By(subK, tInL, nonzero, LaurentRingSubring.Read(L).At(k, tm))),
				"the Laurent ring is a subring of L",
				"it holds k")
			overlapSet := a.TermAs[Set[A]]("«laurentRing»")
			overlapRing := a.Have(
				"the Laurent ring is a commutative ring under L's operations",
				"comm_ring_on(«laurentRingOps»)",
				By(overlap[0], comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(overlapSet)))
			fieldK := a.Have(
				"k is a field under L's operations",
				"field_on(restrict_field(L, k))",
				By(subK, field.SubfieldFieldOn.Read(L).At(k)))
			kRing := a.Have(
				"so k is a commutative ring under the Laurent ring's operations",
				"comm_ring_on(restrict_ring(«laurentRingOps», k))",
				By(
					field.RingOn.Read(fieldK),
					field.FieldRingDef.At(a.TermAs[field.FieldOps[A]]("restrict_field(L, k)")),
					module_record.RestrictRingDef.At(a.TermAs[module_record.RingOps[A]]("«laurentRingOps»"), k)))
			a.Show(
				"k, inside the Laurent ring and a ring under its operations, is a subring of it",
				By(
					overlap[1],
					kRing,
					module_record.RestrictRingDef.At(a.TermAs[module_record.RingOps[A]]("field_ring(L)"), overlapSet),
					comm_ring.SubringRingOn.Read(overlapRing).At(k)))
		}),
})}

// LaurentMonomialInRing — every power of t at an integer exponent lies in the
// Laurent ring k[t, 1/t]: the Laurent ring is a ring holding t and inv(t)
// (LaurentRingSubring), and tⁿ is a power of t for n ≥ 0 and of inv(t) below.
var LaurentMonomialInRing = laurentMonomialInRingThm{family.Add(registry.ProofEntry{
	Name: "LaurentMonomialInRing",
	Key:  "prop_36a705a60a92f515",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t:A. ∀n:int.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"t ≠ L.zero",
		},
		Conclusion: "laurent_monomial(t, n) ∈ «laurentRing»",
	},
		func(
			arg *Argument,
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			t *Expr[A],
			n *Expr[Int],
			given Fact,
		) {
			hyp := arg.Conjuncts(
				given,
				"k is a subfield of L",
				"t lies in L",
				"t is not zero")
			tm := arg.MemberOf[on.L](t, hyp[1])
			overlap := arg.Conjuncts(
				arg.Have(
					"the Laurent ring is a subring of L holding k, t and inv(t)",
					"subring(field_ring(L), «laurentRing») ∧ "+
						"k ⊆ «laurentRing» ∧ "+
						"t ∈ «laurentRing» ∧ "+
						"L.inv(t) ∈ «laurentRing»",
					By(hyp[0], hyp[1], hyp[2], LaurentRingSubring.Read(L).At(k, tm))),
				"the Laurent ring is a subring of L",
				"it holds k",
				"it holds t",
				"it holds inv(t)")
			overlapRing := arg.Have(
				"the Laurent ring is a commutative ring under L's operations",
				"comm_ring_on(restrict_ring(field_ring(L), «laurentRing»))",
				By(
					overlap[0],
					comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(arg.TermAs[Set[A]]("«laurentRing»"))))
			powers := comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(overlapRing))
			arg.Cases(arg.Term("&0 ≤ n"))
			arg.When(
				"for n ≥ 0, tⁿ is a power of t, which the ring k[t, 1/t] holds",
				func(b *Argument, nonnegative Fact) {
					b.Show(
						"the first branch of the definition",
						Unfold(LaurentMonomialDef),
						By(nonnegative, powers, overlap[2]))
				})
			arg.Otherwise(
				"for n < 0, tⁿ is a power of inv(t), which it holds too",
				func(b *Argument, negative Fact) {
					b.Show(
						"the second branch of the definition",
						Unfold(LaurentMonomialDef),
						By(negative, powers, overlap[3]))
				})
		}),
})}

// LaurentMonomialInPolynomials — a power tⁿ at an integer exponent lies in
// k[t] when n ≥ 0 and in k[1/t] when n ≤ 0: it is then a natural power
// of t, or of inv(t), and k[t] and k[1/t] are rings holding their generators
// (PolynomialImageRing).
var LaurentMonomialInPolynomials = laurentMonomialInPolynomialsThm{family.Add(registry.ProofEntry{
	Name: "LaurentMonomialInPolynomials",
	Key:  "prop_fdb8a061bb28f486",
	Reading: "t ≠ zero is not asked: at t = zero both branches " +
		"of the definition are still powers of t and inv(t).",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t:A. ∀n:int.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
		},
		Conclusion: "(&0 ≤ n ⇒ laurent_monomial(t, n) ∈ «polynomials») ∧ " +
			"(n ≤ &0 ⇒ laurent_monomial(t, n) ∈ «inversePolynomials»)",
	},
		func(a *Argument, L field.FieldFact[on.L], k *Expr[Set[A]], t *Expr[A], n *Expr[Int], h Fact) {
			hyp := a.Conjuncts(
				h,
				"k is a subfield of L",
				"t lies in L")
			subK, tInL := hyp[0], hyp[1]
			tm := a.MemberOf[on.L](t, tInL)
			subrings := comm_ring.SubringRingOn.Read(field.RingOn.Read(L))
			ring0 := a.Conjuncts(
				a.Have(
					"k[t] is a ring holding t",
					"comm_ring_on(restrict_ring(field_ring(L), «polynomials»)) ∧ t ∈ «polynomials»",
					By(
						subK,
						algebraic_element.PolynomialImageRing.Read(L).At(k, tm),
						subrings.At(a.TermAs[Set[A]]("«polynomials»")))),
				"k[t] is a ring",
				"t lies in k[t]")
			ring1 := a.Conjuncts(
				a.Have(
					"k[1/t] is a ring holding inv(t)",
					"comm_ring_on(restrict_ring(field_ring(L), «inversePolynomials»)) ∧ "+
						"L.inv(t) ∈ «inversePolynomials»",
					By(
						subK,
						algebraic_element.PolynomialImageRing.Read(L).At(k, field.InvIn.Read(L).At(tm)),
						subrings.At(a.TermAs[Set[A]]("«inversePolynomials»")))),
				"k[1/t] is a ring",
				"inv(t) lies in k[1/t]")
			a.Do(SplitConj(
				Case(
					"for n ≥ 0, tⁿ is a natural power of t, which the ring k[t] holds",
					Derive(func(b *Argument) {
						nonnegative := b.Assume()
						b.Show(
							"the first branch of the definition",
							Unfold(LaurentMonomialDef),
							By(nonnegative, ring0[1], comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ring0[0]))))
					})),
				Case(
					"for n ≤ 0, tⁿ is a natural power of inv(t), which the ring k[1/t] holds",
					Derive(func(b *Argument) {
						// LaurentMonomialOfNum reads tⁿ at a negated natural exponent, so n is first written −N.
						nonpositive := b.Assume()
						negated := b.Have(
							"−n is not negative",
							"&0 ≤ -n",
							ByArith(nonpositive))
						_, natural := b.ObtainAs[Nat](
							"so −n is a natural number N",
							"∃N:num. -n = &N",
							By(negated, int_embed.OfNumExists.At(b.TermAs[Int]("-n"))))
						exponent := b.Have(
							"and n = −N",
							"n = -&N",
							ByArith(natural))
						b.Show(
							"t^(−N) is the N-th power of inv(t)",
							exponent.Rw(),
							Simp(Fwd(LaurentMonomialOfNum)),
							By(ring1[1], comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ring1[0]))))
					})),
			))
		}),
})}

// ---------------------------------------------------------------------------
// Finite sums Σ c(j) · tʲ
// ---------------------------------------------------------------------------

// LaurentTermsInField — for t a nonzero member of the field and
// coefficients c in k, every term c(j) · tʲ lies in L: k lies in L, and
// so does every power of t (LaurentMonomialProduct).
var LaurentTermsInField = laurentTermsInFieldThm{family.Add(registry.ProofEntry{
	Name: "LaurentTermsInField",
	Key:  "prop_961d74f4576fbab6",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t:A. ∀c:(int → A). ∀j:int.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"t ≠ L.zero",
			"∀i:int. c(i) ∈ k",
		},
		Conclusion: "c(j) * laurent_monomial(t, j) ∈ L.carrier",
	},
		func(
			arg *Argument,
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			t *Expr[A],
			c *Arrow[Int, A],
			h Fact,
		) {
			hyp := arg.Conjuncts(
				h,
				"k is a subfield of L",
				"t lies in L",
				"t is not zero",
				"every c(j) lies in k")
			sub, tIn, nonzero, inK := hyp[0], hyp[1], hyp[2], hyp[3]
			tm := arg.MemberOf[on.L](t, tIn)
			inclusion := arg.Unfolded(arg.Have(
				"k lies in L",
				"k ⊆ L.carrier",
				By(sub, field.SubfieldSubset)), set_basic.SubsetDef)
			inL := arg.Have(
				"so every c(j) lies in L",
				"∀j:int. c(j) ∈ L.carrier",
				By(inclusion, inK))
			powers := arg.Have(
				"every power of t lies in L",
				"∀j:int. laurent_monomial(t, j) ∈ L.carrier",
				By(nonzero, LaurentMonomialProduct.Read(L).At(tm)))
			arg.Show(
				"each term is a product of two members of L",
				By(inL, powers, comm_ring.MulIn.Read(field.RingOn.Read(L))))
		}),
})}

// LaurentSumOverSuperset — for t a nonzero member of the field and
// coefficients c in k, the sum of the c(j) · tʲ over a finite S holding
// the support of c is the sum over the support: off the support a term is
// zero times a power of t, which is zero.
var LaurentSumOverSuperset = laurentSumOverSupersetThm{family.Add(registry.ProofEntry{
	Name: "LaurentSumOverSuperset",
	Key:  "prop_592d1f58ca8aff9d",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t:A. ∀c:(int → A). ∀S:set(int).",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"t ≠ L.zero",
			"finite(S)",
			"fun_support(L.zero, c) ⊆ S",
			"∀j:int. c(j) ∈ k",
		},
		Conclusion: "module_sum(L.add, L.zero, S, λj:int. c(j) * laurent_monomial(t, j)) = " +
			"module_sum(L.add, L.zero, fun_support(L.zero, c), λj:int. c(j) * laurent_monomial(t, j))",
	},
		func(
			arg *Argument,
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			t *Expr[A],
			c *Arrow[Int, A],
			S *Expr[Set[Int]],
			h Fact,
		) {
			hyp := arg.Conjuncts(
				h,
				"k is a subfield of L",
				"t lies in L",
				"t is not zero",
				"S is finite",
				"S holds the support of c",
				"every c(j) lies in k")
			sub, tIn, nonzero, finS, holds, inK := hyp[0], hyp[1], hyp[2], hyp[3], hyp[4], hyp[5]
			tm := arg.MemberOf[on.L](t, tIn)
			ring := field.RingOn.Read(L)
			powers := arg.Have(
				"every power of t lies in L",
				"∀j:int. laurent_monomial(t, j) ∈ L.carrier",
				By(nonzero, LaurentMonomialProduct.Read(L).At(tm)))
			terms := arg.Have(
				"and so does every term c(j) · tʲ",
				"∀j:int. c(j) * laurent_monomial(t, j) ∈ L.carrier",
				By(sub, tIn, nonzero, inK, Read(LaurentTermsInField, L).At(k, t, c)))
			vanish := arg.Have(
				"off the support a term is zero times a power, which is zero",
				"∀j:int. j ∈ S ∧ j ∉ fun_support(L.zero, c) ⇒ c(j) * laurent_monomial(t, j) = L.zero",
				Derive(func(b *Argument) {
					b.FixAs[Int]()
					zeroCoefficient := b.Have(
						"c(j) is zero",
						"c(j) = L.zero",
						BySets(b.Assume()))
					b.Show(
						"and zero times a power of t is zero",
						zeroCoefficient.Rw(),
						By(powers, comm_ring.MulLeftZeroOn.Read(ring)))
				}))
			arg.Show(
				"so the sum over S is the sum over the support, L being a module over itself",
				By(
					finS,
					holds,
					terms,
					vanish,
					module.ModuleSumSupport.Read(module.RegularModuleOn.Read(ring)).At(
						S,
						arg.TermAs[Set[Int]]("fun_support(L.zero, c)"),
						arg.TermAs[Fun[Int, A]]("λj:int. c(j) * laurent_monomial(t, j)"))))
		}),
})}

// LaurentSumAdd — for t a nonzero member of the field and finitely
// supported coefficients a and b in k, the expansion with coefficients
// a + b is the sum of the two expansions: over the union S of the two
// supports, a finite set holding the support of a + b, each expansion is
// its sum over S (LaurentSumOverSuperset), and over S the terms add.
var LaurentSumAdd = laurentSumAddThm{family.Add(registry.ProofEntry{
	Name: "LaurentSumAdd",
	Key:  "prop_b2ee248793cc167d",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t:A. ∀a b:(int → A).",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"t ≠ L.zero",
			"finite(fun_support(L.zero, a))",
			"finite(fun_support(L.zero, b))",
			"∀j:int. a(j) ∈ k",
			"∀j:int. b(j) ∈ k",
		},
		Conclusion: "module_sum(L.add, " +
			"    L.zero, " +
			"    fun_support(L.zero, λj:int. a(j) + b(j)), " +
			"    λj:int. (a(j) + b(j)) * laurent_monomial(t, j)) = " +
			"module_sum(L.add, L.zero, fun_support(L.zero, a), λj:int. a(j) * laurent_monomial(t, j)) + " +
			"module_sum(L.add, L.zero, fun_support(L.zero, b), λj:int. b(j) * laurent_monomial(t, j))",
		Abbrev: Abbrev{
			{Name: "laurentSumAddSupports", Text: "fun_support(L.zero, a) ∪ fun_support(L.zero, b)"},
		},
	},
		func(
			arg *Argument,
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			t *Expr[A],
			a, b *Arrow[Int, A],
			h Fact,
		) {
			hyp := arg.Conjuncts(
				h,
				"k is a subfield of L",
				"t lies in L",
				"t is not zero",
				"a has finitely many nonzero values",
				"and so has b",
				"the values of a lie in k",
				"and so do those of b")
			sub, tIn, nonzero, finiteA, finiteB, inKA, inKB :=
				hyp[0], hyp[1], hyp[2], hyp[3], hyp[4], hyp[5], hyp[6]
			tm := arg.MemberOf[on.L](t, tIn)
			ring := field.RingOn.Read(L)
			regular := module.RegularModuleOn.Read(ring)
			supportA, supportB :=
				arg.TermAs[Set[Int]]("fun_support(L.zero, a)"), arg.TermAs[Set[Int]]("fun_support(L.zero, b)")
			union := arg.TermAs[Set[Int]]("«laurentSumAddSupports»")
			finite := arg.Have(
				"the union S of the two supports is finite",
				"finite(«laurentSumAddSupports»)",
				By(finiteA, finiteB, finite_set.FiniteUnion.At(supportA, supportB)))
			inclusion := arg.Unfolded(arg.Have(
				"k lies in L",
				"k ⊆ L.carrier",
				By(sub, field.SubfieldSubset)), set_basic.SubsetDef)
			inL := arg.Have(
				"the values of a and b lie in L",
				"∀j:int. a(j) ∈ L.carrier ∧ b(j) ∈ L.carrier",
				By(inclusion, inKA, inKB))
			powers := arg.Have(
				"every power of t lies in L",
				"∀j:int. laurent_monomial(t, j) ∈ L.carrier",
				By(nonzero, LaurentMonomialProduct.Read(L).At(tm)))
			// LaurentTermsInField concludes ∀j; the untyped cites keep it, the typed At wanting the exponent too.
			termsA := arg.Have(
				"the terms of a lie in L",
				"∀j:int. a(j) * laurent_monomial(t, j) ∈ L.carrier",
				By(sub, tIn, nonzero, inKA, Read(LaurentTermsInField, L).At(k, t, a)))
			termsB := arg.Have(
				"and so do those of b",
				"∀j:int. b(j) * laurent_monomial(t, j) ∈ L.carrier",
				By(sub, tIn, nonzero, inKB, Read(LaurentTermsInField, L).At(k, t, b)))
			termA := arg.TermAs[Fun[Int, A]]("λj:int. a(j) * laurent_monomial(t, j)")
			termB := arg.TermAs[Fun[Int, A]]("λj:int. b(j) * laurent_monomial(t, j)")
			overA := arg.Have(
				"over S the expansion of a is its sum over its support",
				"module_sum(L.add, L.zero, «laurentSumAddSupports», λj:int. a(j) * laurent_monomial(t, j)) = "+
					"module_sum(L.add, L.zero, fun_support(L.zero, a), λj:int. a(j) * laurent_monomial(t, j))",
				By(
					sub,
					tIn,
					nonzero,
					finite,
					inKA,
					set_order.SubsetUnion.At(supportA, supportB),
					LaurentSumOverSuperset.Read(L).At(k, tm, a, union)))
			overB := arg.Have(
				"and so is that of b",
				"module_sum(L.add, L.zero, «laurentSumAddSupports», λj:int. b(j) * laurent_monomial(t, j)) = "+
					"module_sum(L.add, L.zero, fun_support(L.zero, b), λj:int. b(j) * laurent_monomial(t, j))",
				By(
					sub,
					tIn,
					nonzero,
					finite,
					inKB,
					set_order.SubsetUnion.At(supportB, supportA),
					LaurentSumOverSuperset.Read(L).At(k, tm, b, union)))
			termwise := arg.Have(
				"over S the two sums add termwise",
				"module_sum(L.add, "+
					"    L.zero, "+
					"    «laurentSumAddSupports», "+
					"    λj:int. a(j) * laurent_monomial(t, j) + b(j) * laurent_monomial(t, j)) = "+
					"module_sum(L.add, L.zero, «laurentSumAddSupports», λj:int. a(j) * laurent_monomial(t, j)) + "+
					"module_sum(L.add, L.zero, «laurentSumAddSupports», λj:int. b(j) * laurent_monomial(t, j))",
				By(finite, termsA, termsB, module.ModuleSumAdd.Read(regular).At(union, termA, termB)))
			distributes := arg.Have(
				"each summed term is a sum of terms",
				"∀j:int. "+
					"    (a(j) + b(j)) * laurent_monomial(t, j) = "+
					"    a(j) * laurent_monomial(t, j) + b(j) * laurent_monomial(t, j)",
				By(inL, powers, comm_ring.RightDistribOn.Read(ring)))
			overS := arg.Have(
				"so over S the summed expansion is the sum of the two",
				"module_sum(L.add, "+
					"    L.zero, "+
					"    «laurentSumAddSupports», "+
					"    λj:int. (a(j) + b(j)) * laurent_monomial(t, j)) = "+
					"module_sum(L.add, L.zero, «laurentSumAddSupports», λj:int. a(j) * laurent_monomial(t, j)) + "+
					"module_sum(L.add, L.zero, «laurentSumAddSupports», λj:int. b(j) * laurent_monomial(t, j))",
				By(
					termwise,
					distributes,
					module.ModuleSumCongruence.At(
						arg.TermAs[Op[A]]("L.add"),
						arg.TermAs[A]("L.zero"),
						union,
						arg.TermAs[Fun[Int, A]]("λj:int. (a(j) + b(j)) * laurent_monomial(t, j)"),
						arg.TermAs[Fun[Int, A]]("λj:int. a(j) * laurent_monomial(t, j) + b(j) * laurent_monomial(t, j)"))))
			vanishing := arg.Have(
				"the summed coefficients vanish off S, zero plus zero being zero",
				"fun_support(L.zero, λj:int. a(j) + b(j)) ⊆ «laurentSumAddSupports»",
				BySets(
					comm_monoid.LeftIdentityOn.Read(comm_ring.AddMonoidOn.Read(ring)),
					comm_ring.ZeroIn.Read(ring)))
			summedInK := arg.Have(
				"and lie in k",
				"∀j:int. a(j) + b(j) ∈ k",
				By(sub, inKA, inKB, field.SubfieldAdd))
			arg.Show(
				"so the summed expansion, its sum over S, is the sum of the two expansions",
				By(
					sub,
					tIn,
					nonzero,
					finite,
					vanishing,
					summedInK,
					overA,
					overB,
					overS,
					LaurentSumOverSuperset.Read(L).At(k, tm, arg.TermAs[Fun[Int, A]]("λj:int. a(j) + b(j)"), union)))
		}),
})}

// LaurentSumScale — for t a nonzero member of the field, finitely
// supported coefficients a in k and c in k, the expansion with
// coefficients c · a is c times the expansion of a: c multiplies through
// the finite sum and regroups with each term, and the support of c · a
// lies in that of a (LaurentSumOverSuperset).
var LaurentSumScale = laurentSumScaleThm{family.Add(registry.ProofEntry{
	Name: "LaurentSumScale",
	Key:  "prop_ea583fc7fe80db5a",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t:A. ∀a:(int → A). ∀c:A.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"t ≠ L.zero",
			"finite(fun_support(L.zero, a))",
			"∀j:int. a(j) ∈ k",
			"c ∈ k",
		},
		Conclusion: "module_sum(L.add, " +
			"    L.zero, " +
			"    fun_support(L.zero, λj:int. c * a(j)), " +
			"    λj:int. c * a(j) * laurent_monomial(t, j)) = " +
			"c * module_sum(L.add, L.zero, fun_support(L.zero, a), λj:int. a(j) * laurent_monomial(t, j))",
	},
		func(
			arg *Argument,
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			t *Expr[A],
			a *Arrow[Int, A],
			c *Expr[A],
			h Fact,
		) {
			hyp := arg.Conjuncts(
				h,
				"k is a subfield of L",
				"t lies in L",
				"t is not zero",
				"a has finitely many nonzero values",
				"they lie in k",
				"and c lies in k")
			sub, tIn, nonzero, finiteA, inK, cIn := hyp[0], hyp[1], hyp[2], hyp[3], hyp[4], hyp[5]
			tm := arg.MemberOf[on.L](t, tIn)
			ring := field.RingOn.Read(L)
			regular := module.RegularModuleOn.Read(ring)
			inclusion := arg.Unfolded(arg.Have(
				"k lies in L",
				"k ⊆ L.carrier",
				By(sub, field.SubfieldSubset)), set_basic.SubsetDef)
			cInL := arg.Have(
				"c lies in L",
				"c ∈ L.carrier",
				By(inclusion, cIn))
			cm := arg.MemberOf[on.L](c, cInL)
			inL := arg.Have(
				"the values of a lie in L",
				"∀j:int. a(j) ∈ L.carrier",
				By(inclusion, inK))
			powers := arg.Have(
				"every power of t lies in L",
				"∀j:int. laurent_monomial(t, j) ∈ L.carrier",
				By(nonzero, LaurentMonomialProduct.Read(L).At(tm)))
			// LaurentTermsInField concludes ∀j; the untyped cite keeps it, the typed At wanting the exponent too.
			terms := arg.Have(
				"and so do the terms of a",
				"∀j:int. a(j) * laurent_monomial(t, j) ∈ L.carrier",
				By(sub, tIn, nonzero, inK, Read(LaurentTermsInField, L).At(k, t, a)))
			support := arg.TermAs[Set[Int]]("fun_support(L.zero, a)")
			term := arg.TermAs[Fun[Int, A]]("λj:int. a(j) * laurent_monomial(t, j)")
			scaled := arg.Have(
				"c times the expansion is the sum of c times each term",
				"c * module_sum(L.add, L.zero, fun_support(L.zero, a), λj:int. a(j) * laurent_monomial(t, j)) = "+
					"module_sum(L.add, L.zero, fun_support(L.zero, a), λj:int. c * (a(j) * laurent_monomial(t, j)))",
				By(
					finiteA,
					terms,
					module.ModuleSumSmul.Read(regular).At(support, arg.MemberOf[on.L](c, cInL), term)))
			regrouped := arg.Have(
				"and each scaled term regroups, the product being associative",
				"∀j:int. c * (a(j) * laurent_monomial(t, j)) = (c * a(j)) * laurent_monomial(t, j)",
				By(cm, inL, powers, comm_monoid.AssocOn.Read(comm_ring.MulMonoidOn.Read(ring))))
			overSupport := arg.Have(
				"so c times the expansion is the sum over the support of a of the scaled terms",
				"c * module_sum(L.add, L.zero, fun_support(L.zero, a), λj:int. a(j) * laurent_monomial(t, j)) = "+
					"module_sum(L.add, L.zero, fun_support(L.zero, a), λj:int. (c * a(j)) * laurent_monomial(t, j))",
				scaled.Rw(),
				By(
					regrouped,
					module.ModuleSumCongruence.At(
						arg.TermAs[Op[A]]("L.add"),
						arg.TermAs[A]("L.zero"),
						support,
						arg.TermAs[Fun[Int, A]]("λj:int. c * (a(j) * laurent_monomial(t, j))"),
						arg.TermAs[Fun[Int, A]]("λj:int. (c * a(j)) * laurent_monomial(t, j)"))))
			scaledInK := arg.Have(
				"the scaled values lie in k",
				"∀j:int. c * a(j) ∈ k",
				By(sub, cIn, inK, field.SubfieldMul))
			vanishing := arg.Have(
				"and vanish where those of a do",
				"fun_support(L.zero, λj:int. c * a(j)) ⊆ fun_support(L.zero, a)",
				BySets(arg.Have(
					"c times zero is zero",
					"c * L.zero = L.zero",
					By(comm_ring.MulRightZeroOn.Read(ring).At(cm)))))
			arg.Show(
				"so the scaled expansion, its sum over the support of a, is c times the expansion",
				By(
					sub,
					tIn,
					nonzero,
					finiteA,
					vanishing,
					scaledInK,
					overSupport,
					LaurentSumOverSuperset.Read(L).At(k, tm, arg.TermAs[Fun[Int, A]]("λj:int. c * a(j)"), support)))
		}),
})}

// LaurentSumInPolynomials — a finite expansion Σ a(j) · tʲ over k lies in k[t]
// when no exponent is negative, and in tⁿ · k[1/t] when none lies above n.
// In the first case each term is a member of k times a power of t, both in
// the ring k[t]; in the second the sum is tⁿ times Σ a(j) · t^(j−n), whose
// terms lie in the ring k[1/t] (LaurentMonomialInPolynomials).
var LaurentSumInPolynomials = laurentSumInPolynomialsThm{family.Add(registry.ProofEntry{
	Name: "LaurentSumInPolynomials",
	Key:  "prop_1188997bda597be6",
	Reading: "Transcendence is not asked: these are the halves of LinePairCoefficients that need " +
		"no uniqueness of expansions. t ≠ zero enters only the second half, through tⁿ · t^(j−n) = tʲ.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t:A. ∀a:(int → A). ∀n:int.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"t ≠ L.zero",
			"finite(fun_support(L.zero, a))",
			"∀j:int. a(j) ∈ k",
		},
		Conclusion: "((∀j:int. a(j) ≠ L.zero ⇒ &0 ≤ j) ⇒ «expansion» ∈ «polynomials») ∧ " +
			"((∀j:int. a(j) ≠ L.zero ⇒ j ≤ n) ⇒ «expansion» ∈ «shiftedInversePolynomials»)",
		Abbrev: Abbrev{
			{Name: "laurentSumLowered", Text: "module_sum(L.add, " +
				"    L.zero, " +
				"    fun_support(L.zero, a), " +
				"    λj:int. a(j) * laurent_monomial(t, j - n))"},
		},
	},
		func(
			arg *Argument,
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			t *Expr[A],
			a *Arrow[Int, A],
			n *Expr[Int],
			h Fact,
		) {
			hyp := arg.Conjuncts(
				h,
				"k is a subfield of L",
				"t lies in L",
				"t is not zero",
				"a has finitely many nonzero values",
				"all of them in k")
			subK, tInL, nonzero, finite, valuesInK := hyp[0], hyp[1], hyp[2], hyp[3], hyp[4]
			tm := arg.MemberOf[on.L](t, tInL)
			ring := field.RingOn.Read(L)
			charts := LaurentMonomialInPolynomials.Read(L)
			support := arg.TermAs[Set[Int]]("fun_support(L.zero, a)")
			subrings := comm_ring.SubringRingOn.Read(ring)
			chart0 := arg.Conjuncts(
				arg.Have(
					"k[t] is a ring holding k",
					"comm_ring_on(restrict_ring(field_ring(L), «polynomials»)) ∧ k ⊆ «polynomials»",
					By(
						subK,
						algebraic_element.PolynomialImageRing.Read(L).At(k, tm),
						subrings.At(arg.TermAs[Set[A]]("«polynomials»")))),
				"k[t] is a ring",
				"k lies in k[t]")
			chart1 := arg.Conjuncts(
				arg.Have(
					"and so is k[1/t]",
					"comm_ring_on(restrict_ring(field_ring(L), «inversePolynomials»)) ∧ k ⊆ «inversePolynomials»",
					By(
						subK,
						algebraic_element.PolynomialImageRing.Read(L).At(k, field.InvIn.Read(L).At(tm)),
						subrings.At(arg.TermAs[Set[A]]("«inversePolynomials»")))),
				"k[1/t] is a ring",
				"k lies in k[1/t]")
			arg.Do(SplitConj(
				Case(
					"with no negative exponent each term lies in the ring k[t], and so does their finite sum",
					Derive(func(b *Argument) {
						natural := b.Assume()
						terms := b.Have(
							"each term a(j) · tʲ lies in k[t]",
							"∀j:int. a(j) ≠ L.zero ⇒ a(j) * laurent_monomial(t, j) ∈ «polynomials»",
							Derive(func(c *Argument) {
								j := c.FixAs[Int]("j")
								nonzeroAt := c.Assume()
								power := c.Have(
									"tʲ lies in k[t], j being at least 0",
									"laurent_monomial(t, j) ∈ «polynomials»",
									By(subK, nonzeroAt, natural.At(j), charts.At(k, tm, j)))
								coefficient := c.Have(
									"a(j) lies in k, inside k[t]",
									"a(j) ∈ «polynomials»",
									By(valuesInK.At(j), chart0[1], set_basic.SubsetDef))
								c.Show(
									"a product of two members of the ring k[t]",
									By(coefficient, power, comm_ring.MulIn.Read(chart0[0])))
							}))
						b.Show(
							"a finite sum of members of k[t]",
							By(
								finite,
								terms,
								module.ModuleSumIn.Read(module.RegularModuleOn.Read(chart0[0])).At(
									support, b.TermAs[Fun[Int, A]]("λj:int. a(j) * laurent_monomial(t, j)"))))
					})),
				Case(
					"with none above n the sum is tⁿ times Σ a(j) · t^(j−n), whose terms lie in the ring k[1/t]",
					Derive(func(b *Argument) {
						bounded := b.Assume()
						lowered := b.TermAs[Fun[Int, A]]("λj:int. a(j) * laurent_monomial(t, j - n)")
						terms := b.Have(
							"each lowered term a(j) · t^(j−n) lies in k[1/t]",
							"∀j:int. a(j) ≠ L.zero ⇒ a(j) * laurent_monomial(t, j - n) ∈ «inversePolynomials»",
							Derive(func(c *Argument) {
								j := c.FixAs[Int]("j")
								nonzeroAt := c.Assume()
								exponent := c.Have(
									"j is at most n, so j − n is at most 0",
									"j - n ≤ &0",
									ByArith(nonzeroAt, bounded.At(j)))
								power := c.Have(
									"and t^(j−n) lies in k[1/t]",
									"laurent_monomial(t, j - n) ∈ «inversePolynomials»",
									By(subK, exponent, charts.At(k, tm, c.TermAs[Int]("j - n"))))
								coefficient := c.Have(
									"a(j) lies in k, inside k[1/t]",
									"a(j) ∈ «inversePolynomials»",
									By(valuesInK.At(j), chart1[1], set_basic.SubsetDef))
								c.Show(
									"a product of two members of the ring k[1/t]",
									By(coefficient, power, comm_ring.MulIn.Read(chart1[0])))
							}))
						loweredIn := b.Have(
							"so their finite sum lies in k[1/t]",
							"«laurentSumLowered» ∈ «inversePolynomials»",
							By(
								finite,
								terms,
								module.ModuleSumIn.Read(module.RegularModuleOn.Read(chart1[0])).At(support, lowered)))

						// tⁿ carries the lowered sum back, through the finite sum and term by term.
						valuesInL := b.Have(
							"the values of a lie in L, as k does",
							"∀j:int. a(j) ∈ L.carrier",
							BySets(subK, field.SubfieldSubset, valuesInK))
						powersInL := b.Have(
							"the powers of t lie in L",
							"∀j:int. laurent_monomial(t, j) ∈ L.carrier",
							By(nonzero, LaurentMonomialProduct.Read(L).At(tm)))
						product := b.Have(
							"and multiply by adding exponents",
							"∀p q:int. laurent_monomial(t, p) * laurent_monomial(t, q) = laurent_monomial(t, p + q)",
							By(nonzero, LaurentMonomialProduct.Read(L).At(tm)))
						loweredInL := b.Have(
							"the lowered terms lie in L",
							"∀j:int. a(j) * laurent_monomial(t, j - n) ∈ L.carrier",
							Derive(func(c *Argument) {
								j := c.FixAs[Int]("j")
								c.Show(
									"a product of two members of L",
									By(valuesInL.At(j), powersInL.At(c.TermAs[Int]("j - n")), comm_ring.MulIn.Read(ring)))
							}))
						termMoves := b.Have(
							"tⁿ times a lowered term is the term",
							"∀j:int. "+
								"    laurent_monomial(t, n) * (a(j) * laurent_monomial(t, j - n)) = a(j) * laurent_monomial(t, j)",
							Derive(func(c *Argument) {
								j := c.FixAs[Int]("j")
								gap := c.TermAs[Int]("j - n")
								exponent := c.Have(
									"n + (j − n) = j",
									"n + (j - n) = j",
									ByArith())
								c.Show(
									"regroup, add the exponents, and read n + (j − n) as j",
									CalcEq(
										Leg(
											c.TermAs[A]("a(j) * (laurent_monomial(t, n) * laurent_monomial(t, j - n))"),
											"regrouped in the commutative ring L",
											ByArith(ring, valuesInL.At(j), powersInL.At(n), powersInL.At(gap))),
										Leg(
											c.TermAs[A]("a(j) * laurent_monomial(t, n + (j - n))"),
											"tⁿ · t^(j−n) = t^(n+(j−n))",
											By(product.At(n, gap))),
										FinalLeg(
											"n + (j − n) = j",
											By(Normalized, exponent)),
									))
							}))
						raised := b.Have(
							"tⁿ · Σ a(j) · t^(j−n) = Σ a(j) · tʲ",
							"laurent_monomial(t, n) * «laurentSumLowered» = «expansion»",
							CalcEq(
								Leg(
									b.TermAs[A](
										"module_sum(L.add, "+
											"    L.zero, "+
											"    fun_support(L.zero, a), "+
											"    λj:int. laurent_monomial(t, n) * (a(j) * laurent_monomial(t, j - n)))"),
									"tⁿ multiplies through the finite sum, L being a module over itself",
									By(
										finite,
										loweredInL,
										powersInL.At(n),
										module.ModuleSumSmul.Read(module.RegularModuleOn.Read(ring)).AsFact().At(
											support, b.TermAs[A]("laurent_monomial(t, n)"), lowered))),
								FinalLeg(
									"each term moves back n places",
									By(termMoves, module.ModuleSumCongruence)),
							))
						b.Show(
							"so the sum is tⁿ times a member of k[1/t]",
							By(
								raised,
								loweredIn,
								set_image.FunInImage.At(
									b.TermAs[Fun[A, A]]("L.mul(laurent_monomial(t, n))"),
									b.TermAs[Set[A]]("«inversePolynomials»"),
									b.TermAs[A]("«laurentSumLowered»"))))
					})),
			))
		}),
})}

// LaurentExpansionShift — an expansion of f multiplied by tᵐ term by
// term is an expansion of tᵐ · f: j ↦ a(j − m) is finitely supported,
// its support the translate of a's by m, with values in k, and tᵐ · f is
// its sum. tᵐ multiplies through the sum (L is a module over itself),
// tᵐ · a(j) · tʲ = a(j) · tʲ⁺ᵐ, and the sum is reindexed along j ↦ j + m,
// one to one.
var LaurentExpansionShift = laurentExpansionShiftThm{family.Add(registry.ProofEntry{
	Name: "LaurentExpansionShift",
	Key:  "prop_4979380e5b74b450",
	Reading: "t ≠ zero is what makes tᵐ · tʲ = tʲ⁺ᵐ at every pair of exponents; transcendence is " +
		"not asked, as the shifted sum is an expansion of tᵐ · f whether or not expansions are unique.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t:A. ∀a:(int → A). ∀f:A. ∀m:int.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"t ≠ L.zero",
			"finite(fun_support(L.zero, a))",
			"∀j:int. a(j) ∈ k",
			"f = «expansion»",
		},
		Conclusion: "finite(fun_support(L.zero, λj:int. a(j - m))) ∧ " +
			"(∀j:int. a(j - m) ∈ k) ∧ " +
			"laurent_monomial(t, m) * f = " +
			"module_sum(L.add, " +
			"    L.zero, " +
			"    fun_support(L.zero, λj:int. a(j - m)), " +
			"    λj:int. a(j - m) * laurent_monomial(t, j))",
	},
		func(
			arg *Argument,
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			t *Expr[A],
			a *Arrow[Int, A],
			f *Expr[A],
			m *Expr[Int],
			h Fact,
		) {
			hyp := arg.Conjuncts(
				h,
				"k is a subfield of L",
				"t lies in L",
				"t is not zero",
				"a has finitely many nonzero values",
				"all of them in k",
				"and f is the sum of the a(j) · tʲ")
			subK, tInL, nonzero, finiteSupport, valuesInK, fIsSum :=
				hyp[0], hyp[1], hyp[2], hyp[3], hyp[4], hyp[5]
			ring := field.RingOn.Read(L)
			regular := module.RegularModuleOn.Read(ring)
			tm := arg.MemberOf[on.L](t, tInL)

			// The translation j ↦ j + m carries the support S of a, one to one, onto the support of j ↦ a(j − m).
			support := arg.TermAs[Set[Int]]("fun_support(L.zero, a)")
			translation := arg.TermAs[Fun[Int, Int]]("λj:int. j + m")
			back := arg.Have(
				"translating by m and back is the identity",
				"∀j:int.(j + m) - m = j",
				ByArith())
			forth := arg.Have(
				"and so is translating back and then by m",
				"∀j:int.(j - m) + m = j",
				ByArith())
			onto := arg.Have(
				"j ↦ j + m carries S onto the support of j ↦ a(j − m)",
				"image(λj:int. j + m, fun_support(L.zero, a)) = fun_support(L.zero, λj:int. a(j - m))",
				BySets(back, forth))
			oneToOne := arg.Have(
				"one to one",
				"injective_on(fun_support(L.zero, a), λj:int. j + m)",
				Unfold(functions.InjectiveOnDef),
				ByArith())
			finiteShifted := arg.Have(
				"so the support of j ↦ a(j − m), the image of the finite S, is finite",
				"finite(fun_support(L.zero, λj:int. a(j - m)))",
				By(finiteSupport, onto, finite_set.FiniteImage.At(translation, support)))
			shiftedInK := arg.Have(
				"the values a(j − m) lie in k",
				"∀j:int. a(j - m) ∈ k",
				By(valuesInK))

			// The terms lie in L, and multiplying one by tᵐ moves it m places up.
			valuesInL := arg.Have(
				"the values of a lie in L, as k does",
				"∀j:int. a(j) ∈ L.carrier",
				BySets(subK, field.SubfieldSubset, valuesInK))
			powersInL := arg.Have(
				"the powers of t lie in L",
				"∀j:int. laurent_monomial(t, j) ∈ L.carrier",
				By(nonzero, LaurentMonomialProduct.Read(L).At(tm)))
			product := arg.Have(
				"and multiply by adding exponents",
				"∀p q:int. laurent_monomial(t, p) * laurent_monomial(t, q) = laurent_monomial(t, p + q)",
				By(nonzero, LaurentMonomialProduct.Read(L).At(tm)))
			termsInL := arg.Have(
				"the terms a(j) · tʲ lie in L",
				"∀j:int. a(j) * laurent_monomial(t, j) ∈ L.carrier",
				By(subK, tInL, nonzero, valuesInK, Read(LaurentTermsInField, L).At(k, t, a)))
			shiftedTermsInL := arg.Have(
				"and so do the shifted terms a(j − m) · tʲ",
				"∀j:int. a(j - m) * laurent_monomial(t, j) ∈ L.carrier",
				By(
					subK,
					tInL,
					nonzero,
					shiftedInK,
					Read(LaurentTermsInField, L).At(k, t, arg.TermAs[Fun[Int, A]]("λj:int. a(j - m)"))))
			termMoves := arg.Have(
				"tᵐ times the term at j is the shifted term at j + m",
				"∀j:int. "+
					"    laurent_monomial(t, m) * (a(j) * laurent_monomial(t, j)) = "+
					"    a((j + m) - m) * laurent_monomial(t, j + m)",
				Derive(func(b *Argument) {
					j := b.FixAs[Int]("j")
					b.Show(
						"regroup, add the exponents, and read j as (j + m) − m",
						CalcEq(
							Leg(
								b.TermAs[A]("a(j) * (laurent_monomial(t, j) * laurent_monomial(t, m))"),
								"regrouped in the commutative ring L",
								ByArith(ring, valuesInL.At(j), powersInL.At(j), powersInL.At(m))),
							Leg(
								b.TermAs[A]("a(j) * laurent_monomial(t, j + m)"),
								"tʲ · tᵐ = tʲ⁺ᵐ",
								By(product.At(j, m))),
							FinalLeg(
								"j = (j + m) − m",
								By(back.At(j))),
						))
				}))

			// Through the sum: tᵐ multiplies each term, which moves m places up, and the sum is reindexed along the translation.
			terms := arg.TermAs[Fun[Int, A]]("λj:int. a(j) * laurent_monomial(t, j)")
			shiftedTerms := arg.TermAs[Fun[Int, A]]("λj:int. a(j - m) * laurent_monomial(t, j)")
			tPower := arg.TermAs[A]("laurent_monomial(t, m)")
			sum := arg.Have(
				"tᵐ · f is the sum of the shifted terms over the shifted support",
				"laurent_monomial(t, m) * f = "+
					"module_sum(L.add, "+
					"    L.zero, "+
					"    fun_support(L.zero, λj:int. a(j - m)), "+
					"    λj:int. a(j - m) * laurent_monomial(t, j))",
				CalcEq(
					Leg(
						arg.TermAs[A]("laurent_monomial(t, m) * «expansion»"),
						"f is the sum of the a(j) · tʲ",
						By(fIsSum)),
					Leg(
						arg.TermAs[A](
							"module_sum(L.add, "+
								"    L.zero, "+
								"    fun_support(L.zero, a), "+
								"    λj:int. laurent_monomial(t, m) * (a(j) * laurent_monomial(t, j)))"),
						"tᵐ multiplies through the finite sum, L being a module over itself",
						By(
							finiteSupport,
							termsInL,
							powersInL.At(m),
							module.ModuleSumSmul.Read(regular).AsFact().At(support, tPower, terms))),
					Leg(
						arg.TermAs[A](
							"module_sum(L.add, "+
								"    L.zero, "+
								"    fun_support(L.zero, a), "+
								"    λj:int. a((j + m) - m) * laurent_monomial(t, j + m))"),
						"each term moves m places up",
						By(termMoves, module.ModuleSumCongruence)),
					Leg(
						arg.TermAs[A](
							"module_sum(L.add, "+
								"    L.zero, "+
								"    image(λj:int. j + m, fun_support(L.zero, a)), "+
								"    λj:int. a(j - m) * laurent_monomial(t, j))"),
						"reindexed along the translation, one to one on S",
						By(
							finiteSupport,
							oneToOne,
							shiftedTermsInL,
							module.ModuleSumImage.Read(regular).At(support, translation, shiftedTerms))),
					FinalLeg(
						"the translate of S is the shifted support",
						By(onto)),
				))
			arg.Show(
				"j ↦ a(j − m) is a finitely supported expansion of tᵐ · f in k",
				By(finiteShifted, shiftedInK, sum))
		}),
})}

// LaurentSumAsPolynomial — a Laurent sum whose exponents run along e is
// a polynomial: for e one to one with t^e(m) = sᵐ, and a vanishing off
// the image of e with a ∘ e = p, the support of a is the image of the
// support of p, the two are finite together, and Σ a(j) · tʲ = p(s), the
// sum reindexed along e.
var LaurentSumAsPolynomial = laurentSumAsPolynomialThm{family.Add(registry.ProofEntry{
	Name: "LaurentSumAsPolynomial",
	Key:  "prop_3210ac5cd830ea0d",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀t s:A. ∀e:(num → int). ∀a:(int → A). ∀p:(num → A).",
		Hypotheses: []string{
			"s ∈ L.carrier",
			"∀j:int. a(j) ∈ L.carrier",
			"injective_on(𝕌, e)",
			"∀m:num. laurent_monomial(t, e(m)) = monoid_pow(L.mul, L.one, s, m)",
			"∀m:num. a(e(m)) = p(m)",
			"∀j:int. a(j) ≠ L.zero ⇒ ∃m:num. e(m) = j",
		},
		Conclusion: "(finite(fun_support(L.zero, a)) ⇔ finite(fun_support(L.zero, p))) ∧ " +
			"(finite(fun_support(L.zero, p)) ⇒ «expansion» = polynomial_eval(p, s))",
	},
		func(
			arg *Argument,
			L field.FieldFact[on.L],
			t, s *Expr[A],
			e *Arrow[Nat, Int],
			a *Arrow[Int, A],
			p *Arrow[Nat, A],
			h Fact,
		) {
			hyp := arg.Conjuncts(
				h,
				"s lies in L",
				"so do the values of a",
				"e is one to one",
				"t at e(m) is the m-th power of s",
				"a along e is p",
				"a vanishes off the image of e")
			sInL, aInL, injective, powers, alongE, onImage := hyp[0], hyp[1], hyp[2], hyp[3], hyp[4], hyp[5]
			ring := field.RingOn.Read(L)
			regular := module.RegularModuleOn.Read(ring)
			supportP := arg.TermAs[Set[Nat]]("fun_support(L.zero, p)")
			supports := arg.Have(
				"the support of a is the image under e of the support of p",
				"fun_support(L.zero, a) = image(e, fun_support(L.zero, p))",
				BySets(alongE, onImage))
			oneToOne := arg.Have(
				"e is one to one on the support of p",
				"injective_on(fun_support(L.zero, p), e)",
				By(
					injective,
					functions.InjectiveOnSubset.At(e, supportP, arg.TermAs[Set[Nat]]("𝕌")),
					set_order.SubsetUniv))
			together := arg.Have(
				"an image under a one-to-one map is finite exactly when its source is",
				"finite(fun_support(L.zero, a)) ⇔ finite(fun_support(L.zero, p))",
				By(supports, oneToOne, finite_set.FiniteImageInjEq.At(e, supportP)))
			value := arg.Have(
				"over a finite support the Laurent sum is p(s)",
				"finite(fun_support(L.zero, p)) ⇒ «expansion» = polynomial_eval(p, s)",
				Derive(func(b *Argument) {
					finiteP := b.Assume()
					termsInL := b.Have(
						"the terms along e lie in L",
						"∀m:num. a(e(m)) * laurent_monomial(t, e(m)) ∈ L.carrier",
						By(
							aInL,
							powers,
							sInL,
							comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ring)),
							comm_ring.MulIn.Read(ring)))
					terms := b.TermAs[Fun[Int, A]]("λj:int. a(j) * laurent_monomial(t, j)")
					b.Show(
						"reindex the sum along e and read each term as p(m) · sᵐ",
						CalcEq(
							Leg(
								b.TermAs[A](
									"module_sum(L.add, "+
										"    L.zero, "+
										"    image(e, fun_support(L.zero, p)), "+
										"    λj:int. a(j) * laurent_monomial(t, j))"),
								"the support of a is the image of the support of p",
								By(supports)),
							Leg(
								b.TermAs[A](
									"module_sum(L.add, L.zero, fun_support(L.zero, p), λm:num. a(e(m)) * laurent_monomial(t, e(m)))"),
								"reindexed along e, one to one there",
								By(finiteP, oneToOne, termsInL, module.ModuleSumImage.Read(regular).At(supportP, e, terms))),
							Leg(
								b.TermAs[A](
									"module_sum(L.add, L.zero, fun_support(L.zero, p), λm:num. p(m) * monoid_pow(L.mul, L.one, s, m))"),
								"a(e(m)) = p(m) and t at e(m) is sᵐ",
								By(alongE, powers, module.ModuleSumCongruence)),
							FinalLeg(
								"which is p evaluated at s",
								Unfold(polynomial_evaluation.PolynomialEvalDef)),
						))
				}))
			arg.Show(
				"the supports are finite together, and then the sum is p(s)",
				By(together, value))
		}),
})}

// ---------------------------------------------------------------------------
// The coefficients
// ---------------------------------------------------------------------------

// LaurentChosenExpansion — once f has a finite expansion Σ a(j) · tʲ with
// coefficients in k, its coefficients are those of one: the definition
// chooses among the expansions of f, and a is one it can choose.
var LaurentChosenExpansion = laurentChosenExpansionThm{family.Add(registry.ProofEntry{
	Name: "LaurentChosenExpansion",
	Key:  "prop_d468f55ff0d1b162",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t:A. ∀a:(int → A). ∀f:A.",
		Hypotheses: []string{
			"finite(fun_support(L.zero, a))",
			"∀j:int. a(j) ∈ k",
			"f = «expansion»",
		},
		Conclusion: "finite(fun_support(L.zero, λi:int. laurent_polynomial_coefficient(k, t, f, i))) ∧ " +
			"(∀i:int. laurent_polynomial_coefficient(k, t, f, i) ∈ k) ∧ " +
			"f = «ownExpansion»",
	},
		func(
			arg *Argument,
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			t *Expr[A],
			a *Arrow[Int, A],
			f *Expr[A],
			h Fact,
		) {
			possible := arg.Have(
				"a is an expansion of f of the kind the definition chooses",
				"∃c:(int → A). "+
					"    finite(fun_support(L.zero, c)) ∧ "+
					"    (∀j:int. c(j) ∈ k) ∧ "+
					"    f = module_sum(L.add, L.zero, fun_support(L.zero, c), λj:int. c(j) * laurent_monomial(t, j))",
				Derive(func(b *Argument) {
					b.Take(a)
					b.Show(
						"a itself",
						By(h))
				}))
			arg.Show(
				"so the coefficients the definition chooses, one such expansion "+
					"being possible, have finite support, lie in k and expand f",
				Simp(Fwd(LaurentPolynomialCoefficientDef)),
				By(HilbertDenoted, possible))
		}),
})}

// LaurentShiftToPolynomial — multiplied by tᴺ, a finite expansion
// Σ a(j) tʲ over k whose exponents lie at or above −N is the value at t
// of the polynomial n ↦ a(n − N) over k: tᴺ moves the expansion N places
// up (LaurentExpansionShift), where its exponents are natural numbers, so
// it is a polynomial in t (LaurentSumAsPolynomial along n ↦ &n).
var LaurentShiftToPolynomial = laurentShiftToPolynomialThm{family.Add(registry.ProofEntry{
	Name: "LaurentShiftToPolynomial",
	Key:  "prop_be4b36a70926bd6c",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t:A. ∀a:(int → A). ∀N:num.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"t ≠ L.zero",
			"finite(fun_support(L.zero, a))",
			"∀j:int. a(j) ∈ k",
			"∀j:int. a(j) ≠ L.zero ⇒ -&N ≤ j",
		},
		Conclusion: "polynomial_over(k, λn:num. a(&n - &N)) ∧ " +
			"laurent_monomial(t, &N) * «expansion» = polynomial_eval(λn:num. a(&n - &N), t)",
	},
		func(
			arg *Argument,
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			t *Expr[A],
			a *Arrow[Int, A],
			N *Expr[Nat],
			h Fact,
		) {
			hyp := arg.Conjuncts(
				h,
				"k is a subfield",
				"t lies in L",
				"t is not zero",
				"a has finite support",
				"the coefficients a(j) lie in k",
				"no exponent of the support lies below −N")
			subK, tIn, nonzero, finite, inK, bounded := hyp[0], hyp[1], hyp[2], hyp[3], hyp[4], hyp[5]
			tm := arg.MemberOf[on.L](t, tIn)
			mul, one, inv := arg.TermAs[Op[A]]("L.mul"), arg.TermAs[A]("L.one"), arg.TermAs[Fun[A, A]]("L.inv")

			// Multiplied by tᴺ, the expansion moves N places up.
			shifted := arg.Conjuncts(
				arg.Have(
					"tᴺ times the expansion is the expansion of j ↦ a(j − N), finitely supported in k",
					"finite(fun_support(L.zero, λj:int. a(j - &N))) ∧ "+
						"(∀j:int. a(j - &N) ∈ k) ∧ "+
						"laurent_monomial(t, &N) * «expansion» = "+
						"module_sum(L.add, "+
						"    L.zero, "+
						"    fun_support(L.zero, λj:int. a(j - &N)), "+
						"    λj:int. a(j - &N) * laurent_monomial(t, j))",
					By(
						subK,
						tIn,
						nonzero,
						finite,
						inK,
						LaurentExpansionShift.Read(L).At(k, tm, a, arg.TermAs[A]("«expansion»"), arg.TermAs[Int]("&N")))),
				"j ↦ a(j − N) has finite support",
				"its values lie in k",
				"and its sum is tᴺ times the expansion")

			// Its exponents are natural numbers, so its sum is a polynomial in t.
			valuesInL := arg.Have(
				"the values a(j − N) lie in L, as k does",
				"∀j:int. a(j - &N) ∈ L.carrier",
				BySets(shifted[1], subK, field.SubfieldSubset))
			embedding := arg.Have(
				"the naturals embed in the integers one to one",
				"injective_on(𝕌, λm:num. int_of_num(m))",
				Unfold(functions.InjectiveOnDef),
				By(int_embed.OfNumEq))
			powers := arg.Have(
				"t at a natural exponent m is the m-th power of t",
				"∀m:num. laurent_monomial(t, &m) = monoid_pow(L.mul, L.one, t, m)",
				arg.ForEach(func(m *Expr[Nat]) Action { return By(LaurentMonomialOfNum.At(mul, one, inv, t, m)) }))
			natural := arg.Have(
				"a(j − N) ≠ zero only for j ≥ 0, a natural exponent",
				"∀j:int. a(j - &N) ≠ L.zero ⇒ ∃m:num. &m = j",
				Derive(func(b *Argument) {
					j := b.FixAs[Int]("j")
					nonzeroAt := b.Assume()
					b.Take(b.Term("num_of_int(j)"))
					b.Show(
						"j − N lies at or above −N, so j is the natural number num_of_int(j)",
						ByArith(nonzeroAt, bounded.At(b.TermAs[Int]("j - &N")), int_embed.NumOfIntSection.At(j)))
				}))
			polynomialSum := arg.Conjuncts(
				arg.Have(
					"read along the naturals, the shifted expansion is the polynomial n ↦ a(n − N) at t",
					"(finite(fun_support(L.zero, λj:int. a(j - &N))) ⇔ "+
						"    finite(fun_support(L.zero, λn:num. a(&n - &N)))) ∧ "+
						"(finite(fun_support(L.zero, λn:num. a(&n - &N))) ⇒ "+
						"    module_sum(L.add, "+
						"        L.zero, "+
						"        fun_support(L.zero, λj:int. a(j - &N)), "+
						"        λj:int. a(j - &N) * laurent_monomial(t, j)) = "+
						"    polynomial_eval(λn:num. a(&n - &N), t))",
					By(
						valuesInL,
						embedding,
						powers,
						natural,
						LaurentSumAsPolynomial.Read(L).At(t, tm, arg.TermAs[Fun[Nat, Int]]("λm:num. m"),
							arg.TermAs[Fun[Int, A]]("λj:int. a(j - &N)"), arg.TermAs[Fun[Nat, A]]("λn:num. a(&n - &N)")))),
				"the two supports are finite together",
				"over a finite support the sum is the polynomial's value")
			finiteP := arg.Have(
				"so n ↦ a(n − N) has finite support",
				"finite(fun_support(L.zero, λn:num. a(&n - &N)))",
				By(polynomialSum[0], shifted[0]))
			coefficients := arg.Have(
				"and its values lie in k",
				"∀n:num. a(&n - &N) ∈ k",
				By(inK))
			over := arg.Have(
				"so it is a polynomial over k",
				"polynomial_over(k, λn:num. a(&n - &N))",
				By(
					finiteP,
					coefficients,
					polynomial.PolynomialFiniteSupport.At(
						arg.TermAs[A]("L.zero"), k, arg.TermAs[Fun[Nat, A]]("λn:num. a(&n - &N)"))))
			arg.Show(
				"a polynomial over k, whose value at t is tᴺ times the expansion",
				By(over, shifted[2], polynomialSum[1], finiteP))
		}),
})}

// LaurentCoeffWellDefined — when t is transcendental over k, a finite
// expansion Σ a(j) · tʲ with coefficients in k is the only one: its
// coefficients are the chosen ones. The chosen coefficients c expand f
// too (LaurentChosenExpansion); one power tᴺ turns both expansions into
// polynomials over k with the value tᴺ · f at t, and t being
// transcendental, the two polynomials n ↦ a(n − N) and n ↦ c(n − N) are
// one.
var LaurentCoeffWellDefined = laurentCoeffWellDefinedThm{family.Add(registry.ProofEntry{
	Name: "LaurentCoeffWellDefined",
	Key:  "prop_f437088c70fe6549",
	Reading: "Transcendence is load-bearing: for t a root of x² − 1 over k, one = t⁰ = t² has two " +
		"expansions. The proof lifts both expansions by one power tᴺ to polynomials over k with one " +
		"value tᴺ · f at t, and a polynomial over k is determined by its value at a transcendental t.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t:A. ∀a:(int → A). ∀f:A. ∀i:int.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"¬algebraic_over(L, k, t)",
			"finite(fun_support(L.zero, a))",
			"∀j:int. a(j) ∈ k",
			"f = «expansion»",
		},
		Conclusion: "laurent_polynomial_coefficient(k, t, f, i) = a(i)",
		Abbrev: Abbrev{
			{Name: "laurentCoeffWellDefinedSupports", Text: "fun_support(L.zero, a) ∪ " +
				"fun_support(L.zero, λi:int. laurent_polynomial_coefficient(k, t, f, i))"},
		},
	},
		func(
			arg *Argument,
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			t *Expr[A],
			a *Arrow[Int, A],
			f *Expr[A],
			h Fact,
		) {
			hyp := arg.Conjuncts(
				h,
				"k is a subfield",
				"t lies in L",
				"t is transcendental over k",
				"a has finite support",
				"the coefficients a(j) lie in k",
				"f is the sum of the a(j) tʲ")
			subK, tIn, transcendental, finiteA, inK, expansion := hyp[0], hyp[1], hyp[2], hyp[3], hyp[4], hyp[5]
			tm := arg.MemberOf[on.L](t, tIn)
			nonzero := arg.Have(
				"t, transcendental over k, is not zero",
				"t ≠ L.zero",
				By(subK, transcendental, algebraic_element.TranscendentalInverse.Read(L).At(k, tm)))

			// The coefficients the definition chooses: a witnesses the choice, so they expand f too.
			own := arg.Conjuncts(
				arg.Have(
					"so the coefficients the definition chooses have finite support, lie in k and expand f",
					"finite(fun_support(L.zero, λi:int. laurent_polynomial_coefficient(k, t, f, i))) ∧ "+
						"(∀i:int. laurent_polynomial_coefficient(k, t, f, i) ∈ k) ∧ "+
						"f = «ownExpansion»",
					By(finiteA, inK, expansion, Read(LaurentChosenExpansion, L).At(k, t, a, f))),
				"the chosen coefficients have finite support",
				"they lie in k",
				"f is their sum against the powers of t")

			// One N lifts both expansions to polynomials.
			supportA := arg.TermAs[Set[Int]]("fun_support(L.zero, a)")
			supportC := arg.TermAs[Set[Int]](
				"fun_support(L.zero, λi:int. laurent_polynomial_coefficient(k, t, f, i))")
			N, below := arg.ObtainAs[Nat](
				"the two supports together are finite, so they lie above some −N",
				"∃N:num. ∀j:int. j ∈ «laurentCoeffWellDefinedSupports» ⇒ -&N ≤ j",
				By(
					finiteA,
					own[0],
					finite_set.FiniteUnionImp.At(supportA, supportC),
					int_embed.FiniteIntegersBoundedBelow.At(arg.TermAs[Set[Int]]("«laurentCoeffWellDefinedSupports»"))))
			belowA := arg.Have(
				"no exponent of a lies below −N",
				"∀j:int. a(j) ≠ L.zero ⇒ -&N ≤ j",
				BySets(below))
			belowC := arg.Have(
				"nor of the chosen coefficients",
				"∀j:int. laurent_polynomial_coefficient(k, t, f, j) ≠ L.zero ⇒ -&N ≤ j",
				BySets(below))
			chosenFunction := arg.TermAs[Fun[Int, A]]("λi:int. laurent_polynomial_coefficient(k, t, f, i)")
			liftA := arg.Have(
				"tᴺ f is the value at t of the polynomial n ↦ a(n − N) over k",
				"polynomial_over(k, λn:num. a(&n - &N)) ∧ "+
					"laurent_monomial(t, &N) * «expansion» = polynomial_eval(λn:num. a(&n - &N), t)",
				By(subK, tIn, nonzero, finiteA, inK, belowA, Read(LaurentShiftToPolynomial, L).At(k, t, a, N)))
			liftC := arg.Have(
				"and of the polynomial n ↦ c(n − N) of the chosen coefficients c",
				"polynomial_over(k, λn:num. laurent_polynomial_coefficient(k, t, f, &n - &N)) ∧ "+
					"laurent_monomial(t, &N) * «ownExpansion» = "+
					"polynomial_eval(λn:num. laurent_polynomial_coefficient(k, t, f, &n - &N), t)",
				By(
					subK,
					tIn,
					nonzero,
					own[0],
					own[1],
					belowC,
					Read(LaurentShiftToPolynomial, L).At(k, t, chosenFunction, N)))
			sameValue := arg.Have(
				"both values are tᴺ f",
				"polynomial_eval(λn:num. a(&n - &N), t) = "+
					"polynomial_eval(λn:num. laurent_polynomial_coefficient(k, t, f, &n - &N), t)",
				By(liftA, liftC, expansion, own[2]))
			samePolynomial := arg.Have(
				"t being transcendental over k, the two polynomials are one",
				"(λn:num. a(&n - &N)) = (λn:num. laurent_polynomial_coefficient(k, t, f, &n - &N))",
				By(
					subK,
					transcendental,
					liftA,
					liftC,
					sameValue,
					algebraic_element.EvalInjectiveTranscendental.Read(L).At(
						k,
						tm,
						arg.TermAs[Fun[Nat, A]]("λn:num. a(&n - &N)"),
						arg.TermAs[Fun[Nat, A]]("λn:num. laurent_polynomial_coefficient(k, t, f, &n - &N)"))))
			sameCoefficients := arg.Have(
				"so a(n − N) is the chosen coefficient at n − N, for every n",
				"∀n:num. a(&n - &N) = laurent_polynomial_coefficient(k, t, f, &n - &N)",
				By(Normalized, samePolynomial))

			i := arg.FixAs[Int]("i")
			arg.Cases(arg.Term("a(i) = L.zero ∧ laurent_polynomial_coefficient(k, t, f, i) = L.zero"))
			arg.When(
				"where both vanish they agree",
				func(b *Argument, bothZero Fact) {
					b.Show(
						"both are zero",
						By(bothZero))
				})
			arg.Otherwise(
				"elsewhere i lies above −N, so i is n − N at the natural number n = N + i",
				func(b *Argument, eitherNonzero Fact) {
					above := b.Have(
						"i is at least −N",
						"-&N ≤ i",
						By(eitherNonzero, belowA.At(i), belowC.At(i)))
					back := b.Have(
						"N + i is a natural number n, and n − N = i",
						"&num_of_int(&N + i) - &N = i",
						ByArith(above, int_embed.NumOfIntSection.At(b.TermAs[Int]("&N + i"))))
					b.Show(
						"the polynomials agree at n",
						By(Normalized, back, sameCoefficients.At(b.TermAs[Nat]("num_of_int(&N + i)"))))
				})
		}),
})}

// LaurentExpansion — a member of k[t, 1/t] is the finite sum of its
// coefficients times the powers of t, the coefficients lying in k
// (LaurentExpansionOver reads the sum over any finite set of exponents
// holding them). A power tᴺ carries f to p(t) for a polynomial p over k;
// read at the integers, zero below 0, p is an expansion q of tᴺ · f
// (LaurentSumAsPolynomial along n ↦ &n), and t⁻ᴺ moves it N places down
// to an expansion of t⁻ᴺ · tᴺ · f = f (LaurentExpansionShift). An
// expansion exists, so the chosen coefficients are one
// (LaurentChosenExpansion).
var LaurentExpansion = laurentExpansionThm{family.Add(registry.ProofEntry{
	Name: "LaurentExpansion",
	Key:  "prop_885ed81abde88585",
	Reading: "t ≠ zero suffices: a member of k[t, 1/t] is p(t) · inv(t)ᴺ for a polynomial " +
		"p over k, an expansion the choice in the definition can take; transcendence is " +
		"needed only for uniqueness (LaurentCoeffWellDefined). The coefficients are one " +
		"chosen function, so support, values and sum are those of one expansion.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t f:A.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"t ≠ L.zero",
			"f ∈ «laurentRing»",
		},
		Conclusion: "finite(fun_support(L.zero, λi:int. laurent_polynomial_coefficient(k, t, f, i))) ∧ " +
			"(∀i:int. laurent_polynomial_coefficient(k, t, f, i) ∈ k) ∧ " +
			"f = «ownExpansion»",
	},
		func(arg *Argument, L field.FieldFact[on.L], k *Expr[Set[A]], t, f *Expr[A], hypotheses Fact) {
			parts := arg.Conjuncts(
				hypotheses,
				"k is a subfield of L",
				"t lies in L",
				"t is not zero",
				"f lies in k[t, 1/t]")
			sub, tIn, tNonzero, fIn := parts[0], parts[1], parts[2], parts[3]
			ring := field.RingOn.Read(L)
			tm := arg.MemberOf[on.L](t, tIn)
			mul, one, inv := arg.TermAs[Op[A]]("L.mul"), arg.TermAs[A]("L.one"), arg.TermAs[Fun[A, A]]("L.inv")

			// f in L, and tᴺ · f = p(t) for a polynomial p over k.
			ringL := arg.TermAs[module_record.RingOps[A]]("field_ring(L)")
			away := arg.Conjuncts(
				arg.Have(
					"f lies in L, and some power of t brings it into k[t]",
					"f ∈ L.carrier ∧ (∃n:num. monoid_pow(L.mul, L.one, t, n) * f ∈ «polynomials»)",
					By(ring_away.RingAwayMember.At(ringL, arg.TermAs[Set[A]]("«polynomials»"), t, f), fIn)),
				"f lies in L",
				"some power of t brings f into k[t]")
			fInL := away[0]
			cleared := arg.Unfolded(away[1], algebraic_element.PolynomialImageDef)
			N, p, polynomialForm := arg.Obtain2As[Nat, Fun[Nat, A]](
				"a power tᴺ carries f to the value at t of a polynomial p over k",
				"∃N:num. ∃p:(num → A). "+
					"    polynomial_over(k, p) ∧ monoid_pow(L.mul, L.one, t, N) * f = polynomial_eval(p, t)",
				BySets(cleared))
			form := arg.Conjuncts(
				polynomialForm,
				"p is a polynomial over k",
				"whose value at t is tᴺ · f")
			pSupport := arg.Conjuncts(
				arg.Have(
					"p has finitely many nonzero coefficients, all in k",
					"finite(fun_support(L.zero, p)) ∧ (∀n:num. p(n) ∈ k)",
					By(form[0], polynomial.PolynomialFiniteSupport.At(arg.TermAs[A]("L.zero"), k, p))),
				"p has finitely many nonzero coefficients",
				"all of them in k")

			// Read at the integers, zero below 0, p is an expansion q of tᴺ · f.
			q, qDef := arg.LetAs[Fun[Int, A]]("q", "λj:int. COND(&0 ≤ j, p(num_of_int(j)), L.zero)")
			alongNaturals := arg.Have(
				"at a natural exponent n, q reads p(n)",
				"∀n:num. q(&n) = p(n)",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					b.Show(
						"the guard of q holds at &n, and num_of_int(&n) is n",
						qDef.Rw(),
						By(Normalized, int_embed.OfNumRetract.At(n), int_embed.EmbedNonneg.At(n)))
				}))
			natural := arg.Have(
				"q vanishes below 0, so its exponents are natural numbers",
				"∀j:int. q(j) ≠ L.zero ⇒ ∃n:num. &n = j",
				Derive(func(b *Argument) {
					j := b.FixAs[Int]("j")
					nonzero := b.Assume()
					guard := b.Have(
						"q(j) is not the zero branch, so j ≥ 0",
						"&0 ≤ j",
						By(nonzero, qDef))
					b.Take(b.Term("num_of_int(j)"))
					b.Show(
						"whose embedding is j",
						ByArith(guard, int_embed.NumOfIntSection.At(j)))
				}))
			qInK := arg.Have(
				"every value of q is a coefficient of p or zero, so lies in k",
				"∀j:int. q(j) ∈ k",
				Derive(func(b *Argument) {
					b.FixAs[Int]("j")
					b.Show(
						"both branches of q lie in k",
						By(qDef, sub, field.SubfieldZero, pSupport[1].At(b.TermAs[Nat]("num_of_int(j)"))))
				}))
			qInL := arg.Have(
				"hence in L",
				"∀j:int. q(j) ∈ L.carrier",
				BySets(qInK, sub, field.SubfieldSubset))
			embedding := arg.Have(
				"the naturals embed in the integers one to one",
				"injective_on(𝕌, λn:num. int_of_num(n))",
				Unfold(functions.InjectiveOnDef),
				By(int_embed.OfNumEq))
			powers := arg.Have(
				"t at a natural exponent n is the n-th power of t",
				"∀n:num. laurent_monomial(t, &n) = monoid_pow(L.mul, L.one, t, n)",
				arg.ForEach(func(n *Expr[Nat]) Action { return By(LaurentMonomialOfNum.At(mul, one, inv, t, n)) }))
			polynomialSum := arg.Conjuncts(
				arg.Have(
					"read along the naturals, the expansion of q is the polynomial p at t",
					"(finite(fun_support(L.zero, q)) ⇔ finite(fun_support(L.zero, p))) ∧ "+
						"(finite(fun_support(L.zero, p)) ⇒ "+
						"    module_sum(L.add, L.zero, fun_support(L.zero, q), λj:int. q(j) * laurent_monomial(t, j)) = "+
						"    polynomial_eval(p, t))",
					By(
						qInL,
						embedding,
						powers,
						alongNaturals,
						natural,
						LaurentSumAsPolynomial.Read(L).At(t, tm, arg.TermAs[Fun[Nat, Int]]("λn:num. n"), q, p))),
				"the two supports are finite together",
				"over a finite support the sum is p(t)")
			lifted := arg.Have(
				"and tᴺ · f is the sum of the q(j) · tʲ",
				"laurent_monomial(t, &N) * f = "+
					"module_sum(L.add, L.zero, fun_support(L.zero, q), λj:int. q(j) * laurent_monomial(t, j))",
				By(form[1], polynomialSum[1], pSupport[0], LaurentMonomialOfNum.At(mul, one, inv, t, N)))

			// Multiplied by t⁻ᴺ, the expansion of tᴺ · f moves N places down, to an expansion of f.
			lowered := arg.Conjuncts(
				arg.Have(
					"t⁻ᴺ times it is the expansion of j ↦ q(j + N), finitely supported in k",
					"finite(fun_support(L.zero, λj:int. q(j - -&N))) ∧ "+
						"(∀j:int. q(j - -&N) ∈ k) ∧ "+
						"laurent_monomial(t, -&N) * (laurent_monomial(t, &N) * f) = "+
						"module_sum(L.add, "+
						"    L.zero, "+
						"    fun_support(L.zero, λj:int. q(j - -&N)), "+
						"    λj:int. q(j - -&N) * laurent_monomial(t, j))",
					By(
						sub,
						tIn,
						tNonzero,
						polynomialSum[0],
						pSupport[0],
						qInK,
						lifted,
						LaurentExpansionShift.Read(L).At(
							k, tm, q, arg.TermAs[A]("laurent_monomial(t, &N) * f"), arg.TermAs[Int]("-&N")))),
				"j ↦ q(j + N) has finite support",
				"its values lie in k",
				"and its sum is t⁻ᴺ · tᴺ · f")
			powersInL := arg.Have(
				"the powers of t lie in L",
				"∀j:int. laurent_monomial(t, j) ∈ L.carrier",
				By(tNonzero, LaurentMonomialProduct.Read(L).At(tm)))
			inverse := arg.Have(
				"tᴺ · t⁻ᴺ = one",
				"laurent_monomial(t, &N) * laurent_monomial(t, -&N) = L.one",
				By(tNonzero, LaurentMonomialInverse.Read(L).At(tm, arg.TermAs[Int]("&N"))))
			cancel := arg.Have(
				"so t⁻ᴺ · (tᴺ · f) = f",
				"laurent_monomial(t, -&N) * (laurent_monomial(t, &N) * f) = f",
				ByArith(
					ring,
					powersInL.At(arg.TermAs[Int]("&N")),
					powersInL.At(arg.TermAs[Int]("-&N")),
					fInL,
					Scaled(f, inverse)))
			arg.Show(
				"f has an expansion, so the coefficients the definition chooses are those of one",
				By(
					lowered[0],
					lowered[1],
					lowered[2],
					cancel,
					Read(LaurentChosenExpansion, L).At(k, t, arg.TermAs[Fun[Int, A]]("λj:int. q(j - -&N)"), f)))
		}),
})}

// LaurentCoeffWellDefinedOver — a finite sum Σ c(j) · tʲ with coefficients
// in k, over any finite index set S holding the support of c, has the
// coefficients c: the sum is the one over the support
// (LaurentSumOverSuperset), which LaurentCoeffWellDefined reads.
var LaurentCoeffWellDefinedOver = laurentCoeffWellDefinedOverThm{family.Add(registry.ProofEntry{
	Name: "LaurentCoeffWellDefinedOver",
	Key:  "prop_2ff9371bbc9d6127",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t:A. ∀c:(int → A). ∀S:set(int). ∀f:A. ∀i:int.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"¬algebraic_over(L, k, t)",
			"finite(S)",
			"fun_support(L.zero, c) ⊆ S",
			"∀j:int. c(j) ∈ k",
			"f = module_sum(L.add, L.zero, S, λj:int. c(j) * laurent_monomial(t, j))",
		},
		Conclusion: "laurent_polynomial_coefficient(k, t, f, i) = c(i)",
	},
		func(
			arg *Argument,
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			t *Expr[A],
			c *Arrow[Int, A],
			S *Expr[Set[Int]],
			f *Expr[A],
			i *Expr[Int],
			h Fact,
		) {
			parts := arg.Conjuncts(
				h,
				"k is a subfield of L",
				"t lies in L",
				"t is transcendental over k",
				"S is finite",
				"S holds the support of c",
				"every c(j) lies in k",
				"f is the sum over S")
			sub, tIn, transcendental, finS, holds, inK, sum :=
				parts[0], parts[1], parts[2], parts[3], parts[4], parts[5], parts[6]
			tm := arg.MemberOf[on.L](t, tIn)
			nonzero := arg.Have(
				"t, transcendental over k, is not zero",
				"t ≠ L.zero",
				By(sub, transcendental, algebraic_element.TranscendentalInverse.Read(L).At(k, tm)))
			finite := arg.Have(
				"the support of c is finite",
				"finite(fun_support(L.zero, c))",
				By(finS, holds, finite_set.FiniteSubset.At(arg.TermAs[Set[Int]]("fun_support(L.zero, c)"), S)))
			shrunk := arg.Have(
				"so f is the sum over the support of c",
				"f = module_sum(L.add, L.zero, fun_support(L.zero, c), λj:int. c(j) * laurent_monomial(t, j))",
				By(sum, sub, tIn, nonzero, finS, holds, inK, Read(LaurentSumOverSuperset, L).At(k, t, c, S)))
			arg.Show(
				"which is an expansion LaurentCoeffWellDefined reads",
				By(sub, transcendental, finite, inK, shrunk, LaurentCoeffWellDefined.Read(L).At(k, tm, c, f, i)))
		}),
})}

// LaurentExpansionOver — a member f of k[t, 1/t] is the sum of its
// coefficients times the powers of t over any finite index set S holding
// the support of its coefficients: LaurentExpansion says the sum over the
// support is f, and the sum over S is that sum (LaurentSumOverSuperset).
var LaurentExpansionOver = laurentExpansionOverThm{family.Add(registry.ProofEntry{
	Name: "LaurentExpansionOver",
	Key:  "prop_8022a47a49737c29",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t:A. ∀S:set(int). ∀f:A.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"t ≠ L.zero",
			"f ∈ «laurentRing»",
			"finite(S)",
			"fun_support(L.zero, λi:int. laurent_polynomial_coefficient(k, t, f, i)) ⊆ S",
		},
		Conclusion: "f = " +
			"module_sum(L.add, " +
			"    L.zero, " +
			"    S, " +
			"    λi:int. laurent_polynomial_coefficient(k, t, f, i) * laurent_monomial(t, i))",
	},
		func(
			arg *Argument,
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			t *Expr[A],
			S *Expr[Set[Int]],
			f *Expr[A],
			h Fact,
		) {
			parts := arg.Conjuncts(
				h,
				"k is a subfield of L",
				"t lies in L",
				"t is not zero",
				"f lies in k[t, 1/t]",
				"S is finite",
				"S holds the support of the coefficients of f")
			sub, tIn, nonzero, fIn, finS, holds := parts[0], parts[1], parts[2], parts[3], parts[4], parts[5]
			tm := arg.MemberOf[on.L](t, tIn)
			expansion := arg.Have(
				"the coefficients of f lie in k, and f is the sum of its terms over their support",
				"(∀i:int. laurent_polynomial_coefficient(k, t, f, i) ∈ k) ∧ "+
					"f = "+
					"module_sum(L.add, "+
					"    L.zero, "+
					"    fun_support(L.zero, λi:int. laurent_polynomial_coefficient(k, t, f, i)), "+
					"    λi:int. laurent_polynomial_coefficient(k, t, f, i) * laurent_monomial(t, i))",
				By(sub, nonzero, fIn, LaurentExpansion.Read(L).At(k, tm, f)))
			arg.Show(
				"so the sum over S is the sum over the support, which is f",
				By(
					expansion,
					sub,
					tIn,
					nonzero,
					finS,
					holds,
					Read(LaurentSumOverSuperset, L).At(
						k, t, arg.TermAs[Fun[Int, A]]("λi:int. laurent_polynomial_coefficient(k, t, f, i)"), S)))
		}),
})}

// LaurentCoeffShift — multiplying by tᵐ moves every coefficient m places
// up: the expansion of f by its own coefficients, multiplied by tᵐ term
// by term, is an expansion of tᵐ · f with the coefficient of tʲ⁻ᵐ at j,
// and t being transcendental it is the chosen one.
var LaurentCoeffShift = laurentCoeffShiftThm{family.Add(registry.ProofEntry{
	Name: "LaurentCoeffShift",
	Key:  "prop_5b5f2d99080f880e",
	Reading: "Transcendence enters through uniqueness " +
		"only: the shifted expansion is an expansion of tᵐ · f.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t f:A. ∀m i:int.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"¬algebraic_over(L, k, t)",
			"f ∈ «laurentRing»",
		},
		Conclusion: "laurent_polynomial_coefficient(k, t, laurent_monomial(t, m) * f, i) = " +
			"laurent_polynomial_coefficient(k, t, f, i - m)",
	},
		func(
			arg *Argument,
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			t, f *Expr[A],
			m, i *Expr[Int],
			h Fact,
		) {
			hyp := arg.Conjuncts(
				h,
				"k is a subfield of L",
				"t lies in L",
				"t is transcendental over k",
				"f lies in k[t, 1/t]")
			subK, tInL, transcendental, fIn := hyp[0], hyp[1], hyp[2], hyp[3]
			tm := arg.MemberOf[on.L](t, tInL)
			nonzero := arg.Have(
				"t, transcendental over k, is not zero",
				"t ≠ L.zero",
				By(subK, transcendental, algebraic_element.TranscendentalInverse.Read(L).At(k, tm)))
			expansion := arg.Have(
				"f is the finite sum of its coefficients, which lie in k, times the powers of t",
				"finite(fun_support(L.zero, λj:int. laurent_polynomial_coefficient(k, t, f, j))) ∧ "+
					"(∀j:int. laurent_polynomial_coefficient(k, t, f, j) ∈ k) ∧ "+
					"f = "+
					"module_sum(L.add, "+
					"    L.zero, "+
					"    fun_support(L.zero, λj:int. laurent_polynomial_coefficient(k, t, f, j)), "+
					"    λj:int. laurent_polynomial_coefficient(k, t, f, j) * laurent_monomial(t, j))",
				By(subK, nonzero, fIn, LaurentExpansion.Read(L).At(k, tm, f)))
			coefficients := arg.TermAs[Fun[Int, A]]("λj:int. laurent_polynomial_coefficient(k, t, f, j)")
			shifted := arg.Have(
				"multiplied by tᵐ term by term, j ↦ the coefficient of "+
					"tʲ⁻ᵐ in f is a finitely supported expansion of tᵐ · f in k",
				"finite(fun_support(L.zero, λj:int. laurent_polynomial_coefficient(k, t, f, j - m))) ∧ "+
					"(∀j:int. laurent_polynomial_coefficient(k, t, f, j - m) ∈ k) ∧ "+
					"laurent_monomial(t, m) * f = "+
					"module_sum(L.add, "+
					"    L.zero, "+
					"    fun_support(L.zero, λj:int. laurent_polynomial_coefficient(k, t, f, j - m)), "+
					"    λj:int. laurent_polynomial_coefficient(k, t, f, j - m) * laurent_monomial(t, j))",
				By(subK, tInL, nonzero, expansion, Read(LaurentExpansionShift, L).At(k, t, coefficients, f, m)))
			shiftedCoefficients := arg.TermAs[Fun[Int, A]](
				"λj:int. laurent_polynomial_coefficient(k, t, f, j - m)")
			arg.Show(
				"t being transcendental, that expansion is the chosen "+
					"one, so its coefficient at i is that of tⁱ⁻ᵐ in f",
				By(
					subK,
					transcendental,
					shifted,
					LaurentCoeffWellDefined.Read(L).At(
						k, tm, shiftedCoefficients, arg.TermAs[A]("laurent_monomial(t, m) * f"), i)))
		}),
})}

// LaurentCoeffLinear — each coefficient is a k-linear map from
// k[t, 1/t] to k: over the union of their supports the expansions of f and
// g add to an expansion of f + g, c times the expansion of f is one of
// c · f, and an expansion with coefficients in k is the chosen one.
var LaurentCoeffLinear = laurentCoeffLinearThm{family.Add(registry.ProofEntry{
	Name: "LaurentCoeffLinear",
	Key:  "prop_d74c482d4c21096b",
	Reading: "Additivity holds because expansions are unique: the sum of the expansions " +
		"of f and g is an expansion of f + g, its support inside the union of theirs.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t:A. ∀i:int.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"¬algebraic_over(L, k, t)",
		},
		Conclusion: "module_homomorphism(restrict_ring(field_ring(L), k), " +
			"    restrict_module(regular_module(field_ring(L)), «laurentRing»), " +
			"    restrict_module(regular_module(field_ring(L)), k), " +
			"    λf:A. laurent_polynomial_coefficient(k, t, f, i))",
		Abbrev: Abbrev{
			{Name: "laurentCoeffLinearSupports", Text: "fun_support(L.zero, " +
				"    λj:int. laurent_polynomial_coefficient(k, t, f, j)) ∪ " +
				"fun_support(L.zero, λj:int. laurent_polynomial_coefficient(k, t, g, j))"},
		},
	},
		func(arg *Argument, L field.FieldFact[on.L], k *Expr[Set[A]], t *Expr[A], i *Expr[Int], h Fact) {
			parts := arg.Conjuncts(
				h,
				"k is a subfield of L",
				"t lies in L",
				"t is transcendental over k")
			sub, tIn, transcendental := parts[0], parts[1], parts[2]
			tm := arg.MemberOf[on.L](t, tIn)
			ring := field.RingOn.Read(L)
			regular := module.RegularModuleOn.Read(ring)
			nonzero := arg.Have(
				"t, transcendental over k, is not zero",
				"t ≠ L.zero",
				By(sub, transcendental, algebraic_element.TranscendentalInverse.Read(L).At(k, tm)))
			inclusion := arg.Unfolded(arg.Have(
				"k lies in L",
				"k ⊆ L.carrier",
				By(sub, field.SubfieldSubset)), set_basic.SubsetDef)
			powers := arg.Have(
				"every power of t lies in L",
				"∀j:int. laurent_monomial(t, j) ∈ L.carrier",
				By(nonzero, LaurentMonomialProduct.Read(L).At(tm)))

			// The Laurent ring k[t, 1/t] is a ring of L holding k, so a vector
			// space over k, and so is k.
			overlapSet := arg.TermAs[Set[A]]("«laurentRing»")
			overlap := arg.Conjuncts(
				arg.Have(
					"the Laurent ring is a subring of L holding k, t and inv(t)",
					"subring(field_ring(L), «laurentRing») ∧ "+
						"k ⊆ «laurentRing» ∧ "+
						"t ∈ «laurentRing» ∧ "+
						"L.inv(t) ∈ «laurentRing»",
					By(sub, tIn, nonzero, LaurentRingSubring.Read(L).At(k, tm))),
				"the Laurent ring is a subring of L",
				"it holds k",
				"it holds t",
				"it holds inv(t)")
			vectors := arg.Have(
				"k[t, 1/t] is a vector space over k",
				"module_on(restrict_ring(field_ring(L), k), "+
					"    restrict_module(regular_module(field_ring(L)), «laurentRing»))",
				By(
					sub,
					overlap[0],
					comm_ring.SubringRingOn.Read(ring).At(overlapSet),
					overlap[1],
					field_extension.RingExtensionModuleOn.Read(L).At(k, overlapSet)))
			scalars := arg.Have(
				"and so is k",
				"module_on(restrict_ring(field_ring(L), k), restrict_module(regular_module(field_ring(L)), k))",
				By(sub, set_order.SubsetRefl.At(k), field_extension.ExtensionModuleOn.Read(L).At(k, k)))
			coefficients := arg.Have(
				"the coefficient at i of a member of k[t, 1/t] lies in k",
				"∀f:A. f ∈ «laurentRing» ⇒ laurent_polynomial_coefficient(k, t, f, i) ∈ k",
				arg.ForEach(func(f *Expr[A]) Action {
					return By(sub, nonzero, LaurentExpansion.Read(L).At(k, tm, f))
				}))

			// Additivity: over the union S of the two supports, f + g is the
			// sum of the summed coefficients times the powers of t, so those
			// are its coefficients.
			additive := arg.Have(
				"the coefficient of a sum is the sum of the coefficients",
				Statement{
					Binders: "∀f g:A.",
					Hypotheses: []string{
						"f ∈ «laurentRing»",
						"g ∈ «laurentRing»",
					},
					Conclusion: "laurent_polynomial_coefficient(k, t, f + g, i) = " +
						"laurent_polynomial_coefficient(k, t, f, i) + laurent_polynomial_coefficient(k, t, g, i)",
				},
				Derive(func(b *Argument) {
					f, g := b.FixAs[A](), b.FixAs[A]()
					both := b.Conjuncts(
						b.Assume(),
						"f lies in k[t, 1/t]",
						"and so does g")
					fIn, gIn := both[0], both[1]
					fExpansion := b.Conjuncts(
						b.Have(
							"f has finitely many nonzero coefficients, all in k",
							"finite(fun_support(L.zero, λj:int. laurent_polynomial_coefficient(k, t, f, j))) ∧ "+
								"(∀j:int. laurent_polynomial_coefficient(k, t, f, j) ∈ k)",
							By(sub, nonzero, fIn, LaurentExpansion.Read(L).At(k, tm, f))),
						"the coefficients of f have finite support",
						"they lie in k")
					gExpansion := b.Conjuncts(
						b.Have(
							"and so has g",
							"finite(fun_support(L.zero, λj:int. laurent_polynomial_coefficient(k, t, g, j))) ∧ "+
								"(∀j:int. laurent_polynomial_coefficient(k, t, g, j) ∈ k)",
							By(sub, nonzero, gIn, LaurentExpansion.Read(L).At(k, tm, g))),
						"the coefficients of g have finite support",
						"they lie in k")
					fSupport := b.TermAs[Set[Int]](
						"fun_support(L.zero, λj:int. laurent_polynomial_coefficient(k, t, f, j))")
					gSupport := b.TermAs[Set[Int]](
						"fun_support(L.zero, λj:int. laurent_polynomial_coefficient(k, t, g, j))")
					union := b.TermAs[Set[Int]]("«laurentCoeffLinearSupports»")
					finite := b.Have(
						"so the union S of the two supports is finite",
						"finite(«laurentCoeffLinearSupports»)",
						By(fExpansion[0], gExpansion[0], finite_set.FiniteUnion.At(fSupport, gSupport)))
					fOver := b.Have(
						"f is the sum of its terms over S",
						"f = "+
							"module_sum(L.add, "+
							"    L.zero, "+
							"    «laurentCoeffLinearSupports», "+
							"    λj:int. laurent_polynomial_coefficient(k, t, f, j) * laurent_monomial(t, j))",
						By(
							sub,
							tIn,
							nonzero,
							fIn,
							finite,
							set_order.SubsetUnion.At(fSupport, gSupport),
							Read(LaurentExpansionOver, L).At(k, t, union, f)))
					gOver := b.Have(
						"and g the sum of its terms over S",
						"g = "+
							"module_sum(L.add, "+
							"    L.zero, "+
							"    «laurentCoeffLinearSupports», "+
							"    λj:int. laurent_polynomial_coefficient(k, t, g, j) * laurent_monomial(t, j))",
						By(
							sub,
							tIn,
							nonzero,
							gIn,
							finite,
							set_order.SubsetUnion.At(gSupport, fSupport),
							Read(LaurentExpansionOver, L).At(k, t, union, g)))
					inL := b.Have(
						"the coefficients of both lie in L",
						"∀j:int. "+
							"    laurent_polynomial_coefficient(k, t, f, j) ∈ L.carrier ∧ "+
							"    laurent_polynomial_coefficient(k, t, g, j) ∈ L.carrier",
						By(inclusion, fExpansion[1], gExpansion[1]))
					fCoefficients := b.TermAs[Fun[Int, A]]("λj:int. laurent_polynomial_coefficient(k, t, f, j)")
					gCoefficients := b.TermAs[Fun[Int, A]]("λj:int. laurent_polynomial_coefficient(k, t, g, j)")
					fTerms := b.Have(
						"the terms of f lie in L",
						"∀j:int. laurent_polynomial_coefficient(k, t, f, j) * laurent_monomial(t, j) ∈ L.carrier",
						By(sub, tIn, nonzero, fExpansion[1], Read(LaurentTermsInField, L).At(k, t, fCoefficients)))
					gTerms := b.Have(
						"and so do those of g",
						"∀j:int. laurent_polynomial_coefficient(k, t, g, j) * laurent_monomial(t, j) ∈ L.carrier",
						By(sub, tIn, nonzero, gExpansion[1], Read(LaurentTermsInField, L).At(k, t, gCoefficients)))
					fTerm := b.TermAs[Fun[Int, A]](
						"λj:int. laurent_polynomial_coefficient(k, t, f, j) * laurent_monomial(t, j)")
					gTerm := b.TermAs[Fun[Int, A]](
						"λj:int. laurent_polynomial_coefficient(k, t, g, j) * laurent_monomial(t, j)")
					termwise := b.Have(
						"the two sums over S add termwise",
						"module_sum(L.add, "+
							"    L.zero, "+
							"    «laurentCoeffLinearSupports», "+
							"    λj:int. "+
							"        laurent_polynomial_coefficient(k, t, f, j) * laurent_monomial(t, j) + "+
							"        laurent_polynomial_coefficient(k, t, g, j) * laurent_monomial(t, j)) = "+
							"module_sum(L.add, "+
							"    L.zero, "+
							"    «laurentCoeffLinearSupports», "+
							"    λj:int. laurent_polynomial_coefficient(k, t, f, j) * laurent_monomial(t, j)) + "+
							"module_sum(L.add, "+
							"    L.zero, "+
							"    «laurentCoeffLinearSupports», "+
							"    λj:int. laurent_polynomial_coefficient(k, t, g, j) * laurent_monomial(t, j))",
						By(finite, fTerms, gTerms, module.ModuleSumAdd.Read(regular).At(union, fTerm, gTerm)))
					distributes := b.Have(
						"and each summed term is a sum of coefficients times a power",
						"∀j:int. "+
							"    (laurent_polynomial_coefficient(k, t, f, j) + laurent_polynomial_coefficient(k, t, g, j)) * "+
							"    laurent_monomial(t, j) = "+
							"    laurent_polynomial_coefficient(k, t, f, j) * laurent_monomial(t, j) + "+
							"    laurent_polynomial_coefficient(k, t, g, j) * laurent_monomial(t, j)",
						By(inL, powers, comm_ring.RightDistribOn.Read(ring)))
					summed := b.TermAs[Fun[Int, A]](
						"λj:int. " +
							"    (laurent_polynomial_coefficient(k, t, f, j) + laurent_polynomial_coefficient(k, t, g, j)) * " +
							"    laurent_monomial(t, j)")
					termSums := b.TermAs[Fun[Int, A]](
						"λj:int. " +
							"    laurent_polynomial_coefficient(k, t, f, j) * laurent_monomial(t, j) + " +
							"    laurent_polynomial_coefficient(k, t, g, j) * laurent_monomial(t, j)")
					sum := b.Have(
						"so f + g is the sum over S of the summed coefficients times the powers of t",
						"f + g = "+
							"module_sum(L.add, "+
							"    L.zero, "+
							"    «laurentCoeffLinearSupports», "+
							"    λj:int. "+
							"        (laurent_polynomial_coefficient(k, t, f, j) + "+
							"            laurent_polynomial_coefficient(k, t, g, j)) * "+
							"        laurent_monomial(t, j))",
						By(
							fOver,
							gOver,
							termwise,
							distributes,
							module.ModuleSumCongruence.At(
								b.TermAs[Op[A]]("L.add"), b.TermAs[A]("L.zero"), union, summed, termSums)))
					vanishing := b.Have(
						"the summed coefficients vanish off S, zero plus zero being zero",
						"fun_support(L.zero, "+
							"    λj:int. "+
							"        laurent_polynomial_coefficient(k, t, f, j) + "+
							"        laurent_polynomial_coefficient(k, t, g, j)) ⊆ "+
							"«laurentCoeffLinearSupports»",
						BySets(
							comm_monoid.LeftIdentityOn.Read(comm_ring.AddMonoidOn.Read(ring)),
							comm_ring.ZeroIn.Read(ring)))
					b.Show(
						"and the expansion of f + g over S reads its coefficient at i",
						By(
							sub,
							tIn,
							transcendental,
							finite,
							vanishing,
							fExpansion[1],
							gExpansion[1],
							sum,
							field.SubfieldAdd,
							Read(LaurentCoeffWellDefinedOver, L).At(
								k,
								t,
								b.TermAs[Fun[Int, A]](
									"λj:int. laurent_polynomial_coefficient(k, t, f, j) + laurent_polynomial_coefficient(k, t, g, j)"),
								union,
								b.TermAs[A]("f + g"),
								i)))
				}))

			// Homogeneity: c times the expansion of f is a sum over the same
			// support of the scaled coefficients times the powers of t, so
			// those are the coefficients of c · f.
			homogeneous := arg.Have(
				"the coefficient of c · f is c times that of f",
				Statement{
					Binders: "∀c f:A.",
					Hypotheses: []string{
						"c ∈ k",
						"f ∈ «laurentRing»",
					},
					Conclusion: "laurent_polynomial_coefficient(k, t, c * f, i) = " +
						"c * laurent_polynomial_coefficient(k, t, f, i)",
				},
				Derive(func(b *Argument) {
					c, f := b.FixAs[A](), b.FixAs[A]()
					given := b.Conjuncts(
						b.Assume(),
						"c lies in k",
						"f lies in k[t, 1/t]")
					cIn, fIn := given[0], given[1]
					expansion := b.Conjuncts(
						b.Have(
							"f is the sum over its support of its coefficients, all in k, times the powers of t",
							"finite(fun_support(L.zero, λj:int. laurent_polynomial_coefficient(k, t, f, j))) ∧ "+
								"(∀j:int. laurent_polynomial_coefficient(k, t, f, j) ∈ k) ∧ "+
								"f = "+
								"module_sum(L.add, "+
								"    L.zero, "+
								"    fun_support(L.zero, λj:int. laurent_polynomial_coefficient(k, t, f, j)), "+
								"    λj:int. laurent_polynomial_coefficient(k, t, f, j) * laurent_monomial(t, j))",
							By(sub, nonzero, fIn, LaurentExpansion.Read(L).At(k, tm, f))),
						"the coefficients of f have finite support",
						"they lie in k",
						"f is the sum of its terms")
					cInL := b.Have(
						"c lies in L",
						"c ∈ L.carrier",
						By(inclusion, cIn))
					cm := b.MemberOf[on.L](c, cInL)
					inL := b.Have(
						"the coefficients of f lie in L",
						"∀j:int. laurent_polynomial_coefficient(k, t, f, j) ∈ L.carrier",
						By(inclusion, expansion[1]))
					terms := b.Have(
						"and so do its terms",
						"∀j:int. laurent_polynomial_coefficient(k, t, f, j) * laurent_monomial(t, j) ∈ L.carrier",
						By(
							sub,
							tIn,
							nonzero,
							expansion[1],
							Read(LaurentTermsInField, L).At(
								k, t, b.TermAs[Fun[Int, A]]("λj:int. laurent_polynomial_coefficient(k, t, f, j)"))))
					support := b.TermAs[Set[Int]](
						"fun_support(L.zero, λj:int. laurent_polynomial_coefficient(k, t, f, j))")
					term := b.TermAs[Fun[Int, A]](
						"λj:int. laurent_polynomial_coefficient(k, t, f, j) * laurent_monomial(t, j)")
					scaled := b.Have(
						"c times the sum is the sum of c times each term",
						"c * f = "+
							"module_sum(L.add, "+
							"    L.zero, "+
							"    fun_support(L.zero, λj:int. laurent_polynomial_coefficient(k, t, f, j)), "+
							"    λj:int. c * (laurent_polynomial_coefficient(k, t, f, j) * laurent_monomial(t, j)))",
						By(
							expansion[0],
							expansion[2],
							cInL,
							terms,
							module.ModuleSumSmul.Read(regular).AsFact().At(support, c, term)))
					regrouped := b.Have(
						"and each scaled term regroups, the product being associative",
						"∀j:int. "+
							"    c * (laurent_polynomial_coefficient(k, t, f, j) * laurent_monomial(t, j)) = "+
							"    c * laurent_polynomial_coefficient(k, t, f, j) * laurent_monomial(t, j)",
						By(cm, inL, powers, comm_monoid.AssocOn.Read(comm_ring.MulMonoidOn.Read(ring))))
					sum := b.Have(
						"so c · f is the sum over the support of f of the scaled coefficients times the powers of t",
						"c * f = "+
							"module_sum(L.add, "+
							"    L.zero, "+
							"    fun_support(L.zero, λj:int. laurent_polynomial_coefficient(k, t, f, j)), "+
							"    λj:int. c * laurent_polynomial_coefficient(k, t, f, j) * laurent_monomial(t, j))",
						scaled.Rw(),
						By(
							regrouped,
							module.ModuleSumCongruence.At(b.TermAs[Op[A]]("L.add"), b.TermAs[A]("L.zero"), support,
								b.TermAs[Fun[Int, A]](
									"λj:int. c * (laurent_polynomial_coefficient(k, t, f, j) * laurent_monomial(t, j))"),
								b.TermAs[Fun[Int, A]](
									"λj:int. c * laurent_polynomial_coefficient(k, t, f, j) * laurent_monomial(t, j)"))))
					vanishing := b.Have(
						"the scaled coefficients vanish where those of f do",
						"fun_support(L.zero, λj:int. c * laurent_polynomial_coefficient(k, t, f, j)) ⊆ "+
							"fun_support(L.zero, λj:int. laurent_polynomial_coefficient(k, t, f, j))",
						BySets(b.Have(
							"c times zero is zero",
							"c * L.zero = L.zero",
							By(comm_ring.MulRightZeroOn.Read(ring).At(cm)))))
					b.Show(
						"and the scaled expansion reads the coefficient of c · f at i",
						By(
							sub,
							tIn,
							transcendental,
							expansion[0],
							expansion[1],
							vanishing,
							cIn,
							sum,
							field.SubfieldMul,
							Read(LaurentCoeffWellDefinedOver, L).At(
								k,
								t,
								b.TermAs[Fun[Int, A]]("λj:int. c * laurent_polynomial_coefficient(k, t, f, j)"),
								support,
								b.TermAs[A]("c * f"),
								i)))
				}))

			arg.Show(
				"so the coefficient at i is a k-linear map from k[t, 1/t] to k",
				By(
					vectors,
					scalars,
					coefficients,
					additive,
					homogeneous,
					module_homomorphism.ModuleHomomorphismDef))
		}),
})}

// LaurentMonomialCoefficient — for t transcendental over k, the
// coefficient of tⁱ in tʲ is one when i = j and zero otherwise: tʲ is the
// expansion whose only term is one · tʲ, and the expansion is unique.
var LaurentMonomialCoefficient = laurentMonomialCoefficientThm{family.Add(registry.ProofEntry{
	Name: "LaurentMonomialCoefficient",
	Key:  "prop_11ffadffa99f2968",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t:A. ∀i j:int.",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"¬algebraic_over(L, k, t)",
		},
		Conclusion: "laurent_polynomial_coefficient(k, t, laurent_monomial(t, j), i) = " +
			"COND(i = j, L.one, L.zero)",
	},
		func(arg *Argument, L field.FieldFact[on.L], k *Expr[Set[A]], t *Expr[A], i, j *Expr[Int], h Fact) {
			parts := arg.Conjuncts(
				h,
				"k is a subfield of L",
				"t lies in L",
				"t is transcendental over k")
			sub, tInL, transcendental := parts[0], parts[1], parts[2]
			tm := arg.MemberOf[on.L](t, tInL)
			ring := field.RingOn.Read(L)
			nonzero := arg.Have(
				"t, transcendental over k, is not zero",
				"t ≠ L.zero",
				By(sub, transcendental, algebraic_element.TranscendentalInverse.Read(L).At(k, tm)))
			deltaFunction, delta := arg.LetAs[Fun[Int, A]]("δ", "λm:int. COND(m = j, L.one, L.zero)")
			support := arg.Have(
				"δ is nonzero at j alone",
				"fun_support(L.zero, δ) = {j}",
				BySets(delta, field.OneNotZeroOn.Read(L)))
			finite := arg.Have(
				"so its support is finite",
				"finite(fun_support(L.zero, δ))",
				support.Rw(),
				By(finite_set.FiniteSing.At(j)))
			inK := arg.Have(
				"δ takes its values in k",
				"∀m:int. δ(m) ∈ k",
				By(delta, sub, field.SubfieldZero, field.SubfieldOne))
			power := arg.Have(
				"every power of t lies in L",
				"∀m:int. laurent_monomial(t, m) ∈ L.carrier",
				By(nonzero, LaurentMonomialProduct.Read(L).At(tm)))
			terms := arg.Have(
				"each term δ(m) · tᵐ lies in L",
				"∀m:int. δ(m) * laurent_monomial(t, m) ∈ L.carrier",
				By(sub, tInL, nonzero, inK, Read(LaurentTermsInField, L).At(k, t, deltaFunction)))
			others := arg.Have(
				"no other m lies in {j}",
				"∀m:int. m ∈ {j} ∧ m ≠ j ⇒ δ(m) * laurent_monomial(t, m) = L.zero",
				BySets())
			single := arg.Have(
				"the sum over {j} is its one term",
				"module_sum(L.add, L.zero, {j}, λm:int. δ(m) * laurent_monomial(t, m)) = "+
					"δ(j) * laurent_monomial(t, j)",
				By(
					terms,
					others,
					arg.Have(
						"j lies in {j}",
						"j ∈ {j}",
						BySets()),
					finite_set.FiniteSing.At(j),
					module.ModuleSumSingle.Read(module.RegularModuleOn.Read(ring)).At(
						arg.TermAs[Set[Int]]("{j}"), j, arg.TermAs[Fun[Int, A]]("λm:int. δ(m) * laurent_monomial(t, m)"))))
			expansion := arg.Have(
				"so tʲ is the expansion one · tʲ",
				"laurent_monomial(t, j) = "+
					"module_sum(L.add, L.zero, fun_support(L.zero, δ), λm:int. δ(m) * laurent_monomial(t, m))",
				support.Rw(),
				single.Rw(),
				By(delta, power, comm_monoid.LeftIdentityOn.Read(comm_ring.MulMonoidOn.Read(ring))))
			arg.Show(
				"and by uniqueness of expansions its coefficients are δ",
				By(
					sub,
					transcendental,
					finite,
					inK,
					expansion,
					delta,
					LaurentCoeffWellDefined.Read(L).At(
						k, tm, deltaFunction, arg.TermAs[A]("laurent_monomial(t, j)"), i)))
		}),
})}

// ---------------------------------------------------------------------------
// The polynomials in s among the Laurent polynomials
// ---------------------------------------------------------------------------

// PolynomialImageCoefficients — for t transcendental over k and s with
// sᵐ = t^e(m) along e : ℕ → ℤ with a left inverse d, k[s] is the Laurent
// polynomials in t whose coefficients vanish off the image of e: p(s) is
// the Laurent sum with coefficient p(d(j)) at each j = e(m) and none
// elsewhere, which LaurentCoeffWellDefined reads back, and a Laurent
// polynomial with coefficients only along e is p(s) for p = c ∘ e
// (LaurentSumAsPolynomial both ways).
var PolynomialImageCoefficients = polynomialImageCoefficientsThm{family.Add(registry.ProofEntry{
	Name: "PolynomialImageCoefficients",
	Key:  "prop_10adeb1f0b7ced0c",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀t s:A. ∀e:(num → int). ∀d:(int → num).",
		Hypotheses: []string{
			"subfield(L, k)",
			"t ∈ L.carrier",
			"¬algebraic_over(L, k, t)",
			"s ∈ «laurentRing»",
			"∀m:num. d(e(m)) = m",
			"∀m:num. laurent_monomial(t, e(m)) = monoid_pow(L.mul, L.one, s, m)",
		},
		Conclusion: "polynomial_image(field_ring(L), k, s) = " +
			"{f:A | " +
			"    f ∈ «laurentRing» ∧ " +
			"    (∀i:int. (∀m:num. e(m) ≠ i) ⇒ laurent_polynomial_coefficient(k, t, f, i) = L.zero)}",
	},
		func(
			arg *Argument,
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			t, s *Expr[A],
			e *Arrow[Nat, Int],
			d *Arrow[Int, Nat],
			h Fact,
		) {
			hyp := arg.Conjuncts(
				h,
				"k is a subfield of L",
				"t lies in L",
				"t is transcendental over k",
				"s lies in the Laurent ring",
				"d undoes e",
				"t at e(m) is the m-th power of s")
			subK, tInL, transcendental, sInO, leftInverse, powers :=
				hyp[0], hyp[1], hyp[2], hyp[3], hyp[4], hyp[5]
			tm := arg.MemberOf[on.L](t, tInL)
			nonzero := arg.Have(
				"t, transcendental over k, is not zero",
				"t ≠ L.zero",
				By(subK, transcendental, algebraic_element.TranscendentalInverse.Read(L).At(k, tm)))
			overlap := arg.Conjuncts(
				arg.Have(
					"the Laurent ring is a subring of L holding k, t and inv(t)",
					"subring(field_ring(L), «laurentRing») ∧ "+
						"k ⊆ «laurentRing» ∧ "+
						"t ∈ «laurentRing» ∧ "+
						"L.inv(t) ∈ «laurentRing»",
					By(subK, tInL, nonzero, Read(LaurentRingSubring, L).At(k, t))),
				"the Laurent ring is a subring of L",
				"it holds k",
				"it holds t",
				"it holds inv(t)")
			kInO := overlap[1]
			ringO := arg.Have(
				"the Laurent ring is a commutative ring under L's operations",
				"comm_ring_on(restrict_ring(field_ring(L), «laurentRing»))",
				By(
					overlap[0],
					comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(arg.TermAs[Set[A]]("«laurentRing»"))))
			sInL := arg.Have(
				"s lies in L",
				"s ∈ L.carrier",
				BySets(sInO, comm_ring.SubringSubset.Read(overlap[0])))
			kInL := arg.Have(
				"k lies in L",
				"k ⊆ L.carrier",
				By(subK, field.SubfieldSubset))
			oneToOne := arg.Have(
				"e is one to one, d undoing it",
				"injective_on(𝕌, e)",
				Unfold(functions.InjectiveOnDef),
				By(leftInverse))
			inImage := arg.Have(
				"k[s] is the set of the values at s of the polynomials over k",
				"∀x:A. "+
					"    x ∈ polynomial_image(field_ring(L), k, s) ⇔ "+
					"    ∃p:(num → A). polynomial_over(k, p) ∧ x = polynomial_eval(p, s)",
				Unfold(algebraic_element.PolynomialImageDef),
				SetTac())

			// A polynomial p(s) is the Laurent sum with coefficient p(d(j)) at j = e(m), zero off the image of e.
			polynomials := arg.Have(
				"a polynomial in s is a Laurent polynomial with coefficients only along e",
				Statement{
					Binders: "∀f:A.",
					Hypotheses: []string{
						"f ∈ polynomial_image(field_ring(L), k, s)",
					},
					Conclusion: "f ∈ «laurentRing» ∧ " +
						"(∀i:int. (∀m:num. e(m) ≠ i) ⇒ laurent_polynomial_coefficient(k, t, f, i) = L.zero)",
				},
				Derive(func(b *Argument) {
					f := b.FixAs[A]("f")
					fIn := b.Assume()
					p, written := b.ObtainAs[Fun[Nat, A]](
						"write f as p(s), p a polynomial over k",
						"∃p:(num → A). polynomial_over(k, p) ∧ f = polynomial_eval(p, s)",
						By(fIn, inImage.At(f)))
					pFacts := b.Conjuncts(
						written,
						"p is a polynomial over k",
						"f = p(s)")
					support := b.Conjuncts(
						b.Have(
							"p has finitely many nonzero terms, all in k",
							"finite(fun_support(L.zero, p)) ∧ (∀m:num. p(m) ∈ k)",
							By(pFacts[0], polynomial.PolynomialFiniteSupport.At(b.TermAs[A]("L.zero"), k, p))),
						"finitely many nonzero terms",
						"all of them in k")
					a, aDefined := b.LetAs[Fun[Int, A]]("a", "λj:int. COND(∃m:num. e(m) = j, p(d(j)), L.zero)")
					alongE := b.Have(
						"at e(m), a reads p at d(e(m)) = m",
						"∀m:num. a(e(m)) = p(m)",
						By(aDefined, leftInverse))
					offE := b.Have(
						"off the image of e, a is zero",
						"∀j:int.(∀m:num. e(m) ≠ j) ⇒ a(j) = L.zero",
						By(aDefined))
					onImage := b.Have(
						"so a is nonzero only along e",
						"∀j:int. a(j) ≠ L.zero ⇒ ∃m:num. e(m) = j",
						By(Normalized, offE))
					aInK := b.Have(
						"the values of a lie in k",
						"∀j:int. a(j) ∈ k",
						By(aDefined, support[1], subK, field.SubfieldZero))
					aInL := b.Have(
						"hence in L",
						"∀j:int. a(j) ∈ L.carrier",
						BySets(aInK, kInL))
					laurent := b.Conjuncts(
						b.Have(
							"the Laurent sum of a is p(s), the two supports finite together",
							"(finite(fun_support(L.zero, a)) ⇔ finite(fun_support(L.zero, p))) ∧ "+
								"(finite(fun_support(L.zero, p)) ⇒ «expansion» = polynomial_eval(p, s))",
							By(
								sInL,
								aInL,
								oneToOne,
								powers,
								alongE,
								onImage,
								Read(LaurentSumAsPolynomial, L).At(t, s, e, a, p))),
						"the supports are finite together",
						"over a finite support the sum is p(s)")
					expansion := b.Have(
						"f is the Laurent sum of a",
						"f = «expansion»",
						By(pFacts[1], laurent[1], support[0]))
					coefficients := b.Have(
						"so the coefficients of f are the values of a",
						"∀i:int. laurent_polynomial_coefficient(k, t, f, i) = a(i)",
						By(
							subK,
							tInL,
							transcendental,
							laurent[0],
							support[0],
							aInK,
							expansion,
							LaurentCoeffWellDefined.Read(L).AsFact().At(k, t, a, f)))
					fInO := b.Have(
						"p(s) lies in the Laurent ring, a ring holding k and s",
						"f ∈ «laurentRing»",
						By(
							pFacts[1],
							pFacts[0],
							kInO,
							polynomial.PolynomialOverMono.At(b.TermAs[A]("L.zero"), k, b.TermAs[Set[A]]("«laurentRing»"), p),
							polynomial_evaluation.EvalIn.Read(ringO).At(p, proof.MemberOf(s, sInO))))
					b.Show(
						"f lies in the Laurent ring, its coefficients off e those of a there, zero",
						By(fInO, coefficients, offE))
				}))

			// A Laurent polynomial with coefficients only along e is p(s) for p = c ∘ e.
			laurents := arg.Have(
				"a Laurent polynomial with coefficients only along e is a polynomial in s",
				Statement{
					Binders: "∀f:A.",
					Hypotheses: []string{
						"f ∈ «laurentRing»",
						"∀i:int. (∀m:num. e(m) ≠ i) ⇒ laurent_polynomial_coefficient(k, t, f, i) = L.zero",
					},
					Conclusion: "f ∈ polynomial_image(field_ring(L), k, s)",
				},
				Derive(func(b *Argument) {
					f := b.FixAs[A]("f")
					fFacts := b.Conjuncts(
						b.Assume(),
						"f lies in the Laurent ring",
						"its coefficients vanish off e")
					expansion := b.Conjuncts(
						b.Have(
							"f is the finite sum of its coefficients, which lie in k",
							"finite(fun_support(L.zero, λi:int. laurent_polynomial_coefficient(k, t, f, i))) ∧ "+
								"(∀i:int. laurent_polynomial_coefficient(k, t, f, i) ∈ k) ∧ "+
								"f = «ownExpansion»",
							By(subK, nonzero, fFacts[0], LaurentExpansion.Read(L).At(k, tm, f))),
						"finitely many nonzero coefficients",
						"all of them in k",
						"f is their sum")
					coefficient := b.TermAs[Fun[Int, A]]("λi:int. laurent_polynomial_coefficient(k, t, f, i)")
					p := b.TermAs[Fun[Nat, A]]("λm:num. laurent_polynomial_coefficient(k, t, f, e(m))")
					onImage := b.Have(
						"the coefficients of f are nonzero only along e",
						"∀j:int. laurent_polynomial_coefficient(k, t, f, j) ≠ L.zero ⇒ ∃m:num. e(m) = j",
						By(fFacts[1]))
					inL := b.Have(
						"they lie in L",
						"∀j:int. laurent_polynomial_coefficient(k, t, f, j) ∈ L.carrier",
						BySets(expansion[1], kInL))
					laurent := b.Conjuncts(
						b.Have(
							"the Laurent sum of f's coefficients is p(s) for p = c ∘ e",
							"(finite(fun_support(L.zero, λj:int. laurent_polynomial_coefficient(k, t, f, j))) ⇔ "+
								"    finite(fun_support(L.zero, λm:num. laurent_polynomial_coefficient(k, t, f, e(m))))) ∧ "+
								"(finite(fun_support(L.zero, λm:num. laurent_polynomial_coefficient(k, t, f, e(m)))) ⇒ "+
								"    «ownExpansion» = polynomial_eval(λm:num. laurent_polynomial_coefficient(k, t, f, e(m)), s))",
							By(
								sInL,
								inL,
								oneToOne,
								powers,
								onImage,
								Read(LaurentSumAsPolynomial, L).At(t, s, e, coefficient, p))),
						"the supports are finite together",
						"over a finite support the sum is p(s)")
					finiteP := b.Have(
						"c ∘ e has finitely many nonzero terms",
						"finite(fun_support(L.zero, λm:num. laurent_polynomial_coefficient(k, t, f, e(m))))",
						By(laurent[0], expansion[0]))
					value := b.Have(
						"so f = p(s)",
						"f = polynomial_eval(λm:num. laurent_polynomial_coefficient(k, t, f, e(m)), s)",
						By(expansion[2], laurent[1], finiteP))
					over := b.Have(
						"and p is a polynomial over k",
						"polynomial_over(k, λm:num. laurent_polynomial_coefficient(k, t, f, e(m)))",
						By(finiteP, expansion[1], polynomial.PolynomialFiniteSupport.At(b.TermAs[A]("L.zero"), k, p)))
					b.Show(
						"f is the value at s of a polynomial over k",
						By(over, value, inImage.At(f)))
				}))
			arg.Show(
				"k[s] and the Laurent polynomials with coefficients only along e have the same members",
				BySets(polynomials, laurents))
		}),
})}
