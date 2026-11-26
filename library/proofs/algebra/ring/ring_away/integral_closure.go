// integral_closure.go — inverting an element commutes with the integral
// closure in a field. Both inclusions are one move on a monic equation:
// scaling a root by an element that clears the coefficients keeps the
// equation monic, with coefficients in the smaller ring.

package ring_away

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_roots"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// PolynomialCommonPower — when each coefficient of a polynomial p over L is
// brought into a subring S by some power of an element t of S, one power of
// t brings them all. p vanishes past some index m, so its coefficients are
// the finitely many values it takes up to m, and one exponent serves a finite
// set (CommonPower).
var PolynomialCommonPower = polynomialCommonPowerThm{family.Add(registry.ProofEntry{
	Name: "PolynomialCommonPower",
	Key:  "prop_ccd4b9e65299df19",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S:set(A). ∀t:A. ∀p:(num → A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"t ∈ S",
			"polynomial_over(L.carrier, p)",
			"∀i:num. ∃n:num. monoid_pow(L.mul, L.one, t, n) * p(i) ∈ S",
		},
		Conclusion: "∃n:num. ∀i:num. monoid_pow(L.mul, L.one, t, n) * p(i) ∈ S",
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		S *Expr[Set[A]],
		t *Expr[A],
		p *Arrow[Nat, A],
		subring, tInS, pOver, eachCleared Fact,
	) {
		support := a.Conjuncts(
			a.Unfolded(pOver, polynomial.PolynomialOverDef),
			"p vanishes from some index on",
			"its coefficients lie in L")
		m, vanishes := a.UnpackAs[Nat](support[0], "m")
		past := a.Unfolded(vanishes, vec_space.VecDef)
		upToM := a.TermAs[Set[Nat]]("{i:num | i ≤ m}")
		E, EDef := a.LetAs[Set[A]]("E", "image(p, {i:num | i ≤ m})")
		finiteE := a.Have(
			"the values of p up to m form a finite set E",
			"finite(E)",
			By(EDef, num_segment.FiniteBelow.At(m), finite_set.FiniteImage.At(p, upToM)))
		inL := a.Have(
			"E lies in L",
			"E ⊆ L.carrier",
			By(EDef, support[1], set_image.ImageSubsetIff.At(p, upToM, a.TermAs[Set[A]]("L.carrier"))))
		eachInE := a.Have(
			"a power of t brings each member of E into S",
			"∀e:A. e ∈ E ⇒ ∃n:num. monoid_pow(L.mul, L.one, t, n) * e ∈ S",
			BySets(EDef, eachCleared))
		everyCoefficient := a.Have(
			"every coefficient of p lies in E",
			"∀i:num. p(i) ∈ E",
			Derive(func(b *Argument) {
				i := b.FixAs[Nat]("i")
				b.Cases(b.TermAs[Bool]("i ≤ m"))
				b.When(
					"up to m it is one of the values listed in E",
					func(c *Argument, atMost Fact) {
						c.Show(
							"p(i) is a value of p up to m",
							BySets(atMost, EDef))
					})
				b.Otherwise(
					"past m it is zero, as is p(m)",
					func(c *Argument, beyond Fact) {
						same := c.Have(
							"p(i) = p(m), both zero",
							"p(i) = p(m)",
							ByArith(beyond, past.At(i), past.At(m)))
						c.Show(
							"so it is the value at m",
							BySets(same, EDef, nat_order.LessEqRefl.At(m)))
					})
			}))
		n, common := a.ObtainAs[Nat](
			"from one exponent n on, every power of t brings all of the finite set E into S",
			"∃n:num. ∀k:num. n ≤ k ⇒ ∀e:A. e ∈ E ⇒ monoid_pow(L.mul, L.one, t, k) * e ∈ S",
			By(
				subring,
				tInS,
				finiteE,
				inL,
				eachInE,
				fractional_ideal.SubringSubmodule.Read(L).At(S),
				CommonPower.Read(L).At(S, S, E, t)),
			Named("n"))
		a.Take(n)
		a.Show(
			"so tⁿ brings every coefficient of p into S",
			By(common, everyCoefficient, nat_order.LessEqRefl))
	}),
})}

// IntegralClosureAway — inverting a member t of R commutes with the integral
// closure in K: the closure of R[1/t] is the closure of R with t inverted.
// One way, a monic equation of x over R[1/t] has its coefficients brought
// into R by one power tᴺ (PolynomialCommonPower), so tᴺ·x is integral over R
// (integral_element.ScaledRootIntegral). The other way, tᴺ·x integral over R by a monic q
// makes x = t^(−N)·(tᴺ·x) integral over R[1/t], t^(−N) lying in R[1/t] and
// clearing q into it; at t = zero R[1/t] is all of K, and x is a root of
// X − x over it.
var IntegralClosureAway = integralClosureAwayThm{family.Add(registry.ProofEntry{
	Name: "IntegralClosureAway",
	Reading: "t ∈ R ⊆ K is what the route uses: powers of t clear denominators inside " +
		"R. At t = zero both sides are K, ring_away holding every r with zero·r ∈ R.",
	Key: "prop_9ddfaa4dff1224c1",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀R K:set(A). ∀t:A.",
		Hypotheses: []string{
			"subring(field_ring(L), R)",
			"subfield(L, K)",
			"R ⊆ K",
			"t ∈ R",
		},
		Conclusion: "integral_closure(restrict_ring(field_ring(L), «away»), K) = " +
			"ring_away(restrict_ring(field_ring(L), K), «closure», t)",
		Abbrev: Abbrev{
			{Name: "away", Text: "ring_away(restrict_ring(field_ring(L), K), R, t)"},
			{Name: "closure", Text: "integral_closure(restrict_ring(field_ring(L), R), K)"},
		},
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		R, K *Expr[Set[A]],
		t *Expr[A],
		subringR, subfieldK, rInK, tInR Fact,
	) {
		ring := field.RingOn.Read(L)
		zero := a.TermAs[A]("L.zero")
		carrier := a.TermAs[Set[A]]("L.carrier")
		fieldRing := a.TermAs[RingOps[A]]("field_ring(L)")
		kRing := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), K)")
		away := a.TermAs[Set[A]]("«away»")
		closure := a.TermAs[Set[A]]("«closure»")

		// K, R and R[1/t] are rings under the operations of L.
		subringK := a.Have(
			"K is a subring of L",
			"subring(field_ring(L), K)",
			By(subfieldK, field.SubfieldSubring.Read(L)))
		kInL := a.Have(
			"K lies in L",
			"K ⊆ L.carrier",
			By(comm_ring.SubringSubset.Read(subringK)))
		ringK := a.Have(
			"K is a ring under the operations of L",
			"comm_ring_on(restrict_ring(field_ring(L), K))",
			By(subringK, comm_ring.SubringRingOn.Read(ring).At(K)))
		ringR := a.Have(
			"so is R",
			"comm_ring_on(restrict_ring(field_ring(L), R))",
			By(subringR, comm_ring.SubringRingOn.Read(ring).At(R)))
		rSubK := a.Have(
			"R is a subring of K",
			"subring(restrict_ring(field_ring(L), K), R)",
			By(subringR, rInK, comm_ring.SubringRestrict.At(fieldRing, R, K)))
		awayParts := a.Conjuncts(
			GroupPremises(ringK, rSubK, tInR, RingAwaySubring.At(kRing, R, t)),
			"R lies in R[1/t]",
			"R[1/t] is a subring of K",
			"R[1/t] holds every inverse of t in K")
		subringAway := a.Have(
			"so R[1/t] is a subring of L",
			"subring(field_ring(L), «away»)",
			BySets(
				awayParts[1],
				kInL,
				comm_ring.SubringRingOn.Read(ringK).At(away),
				module_record.RestrictRingTwice.At(fieldRing, K, away),
				comm_ring.SubringRingOn.Read(ring).At(away)))
		ringAway := a.Have(
			"and a ring under the operations of L",
			"comm_ring_on(restrict_ring(field_ring(L), «away»))",
			By(subringAway, comm_ring.SubringRingOn.Read(ring).At(away)))
		tK := a.Have(
			"t lies in K",
			"t ∈ K",
			BySets(tInR, rInK))
		tm := a.MemberOf[on.L](t, a.Have(
			"and in L",
			"t ∈ L.carrier",
			BySets(tK, kInL)))

		forward := a.Have(
			"the closure of R[1/t] lies in the closure of R with t inverted",
			Statement{
				Binders:    "∀x:A.",
				Hypotheses: []string{"x ∈ integral_closure(restrict_ring(field_ring(L), «away»), K)"},
				Conclusion: "x ∈ ring_away(restrict_ring(field_ring(L), K), «closure», t)",
			},
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				member := b.Assume()
				opened := b.Conjuncts(
					b.Have(
						"x lies in K and is integral over R[1/t]",
						"x ∈ K ∧ integral_over(restrict_ring(field_ring(L), «away»), x)",
						BySets(member, integral_element.IntegralClosureDef)),
					"x lies in K",
					"x is integral over R[1/t]")
				xm := b.MemberOf[on.L](x, b.Have(
					"so x lies in L",
					"x ∈ L.carrier",
					BySets(opened[0], kInL)))
				p, relation := b.UnpackAs[Fun[Nat, A]](b.Unfolded(opened[1], integral_element.IntegralOverDef), "p")
				data := b.Conjuncts(
					relation,
					"p is a polynomial over R[1/t]",
					"it is monic",
					"of positive degree",
					"and vanishes at x")
				coefficients := b.Have(
					"every coefficient of p lies in R[1/t]",
					"∀i:num. p(i) ∈ «away»",
					By(data[0], polynomial.PolynomialOverDef))
				eachCleared := b.Have(
					"a power of t brings each coefficient of p into R",
					"∀i:num. ∃n:num. monoid_pow(L.mul, L.one, t, n) * p(i) ∈ R",
					Derive(func(c *Argument) {
						i := c.FixAs[Nat]("i")
						c.Show(
							"p(i) lies in R[1/t], so a power of t brings it into R",
							By(coefficients.At(i), RingAwayMember.At(kRing, R, t, c.TermAs[A]("p(i)"))))
					}))
				overL := b.Have(
					"p is a polynomial over L",
					"polynomial_over(L.carrier, p)",
					By(
						data[0],
						comm_ring.SubringSubset.Read(subringAway),
						polynomial.PolynomialOverMono.At(zero, away, carrier, p)))
				N, cleared := b.ObtainAs[Nat](
					"one power tᴺ brings every coefficient of p into R",
					"∃n:num. ∀i:num. monoid_pow(L.mul, L.one, t, n) * p(i) ∈ R",
					By(subringR, tInR, overL, eachCleared, PolynomialCommonPower.Read(L).At(R, t, p)),
					Named("N"))
				tR := proof.MemberOf(t, tInR)
				integral := b.Have(
					"so tᴺ·x is integral over R",
					"integral_over(restrict_ring(field_ring(L), R), monoid_pow(L.mul, L.one, t, N) * x)",
					By(
						subringR,
						overL,
						data[1],
						data[2],
						data[3],
						cleared,
						comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ringR)).At(tR, N),
						integral_element.ScaledRootIntegral.Read(L).At(
							R, p, b.TermAs[A]("monoid_pow(L.mul, L.one, t, N)"), xm)))
				tKMember := proof.MemberOf(t, tK)
				inK := b.Have(
					"tᴺ·x lies in K",
					"monoid_pow(L.mul, L.one, t, N) * x ∈ K",
					By(comm_ring.MulIn.Read(ringK).At(
						comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ringK)).At(tKMember, N),
						proof.MemberOf(x, opened[0]))))
				inClosure := b.Have(
					"so it lies in the closure of R in K",
					"monoid_pow(L.mul, L.one, t, N) * x ∈ «closure»",
					BySets(inK, integral, integral_element.IntegralClosureDef))
				b.Show(
					"so x lies in the closure of R with t inverted",
					By(opened[0], inClosure, RingAwayMember.At(kRing, closure, t, x)))
			}))

		backward := a.Have(
			"the closure of R with t inverted lies in the closure of R[1/t]",
			Statement{
				Binders:    "∀x:A.",
				Hypotheses: []string{"x ∈ ring_away(restrict_ring(field_ring(L), K), «closure», t)"},
				Conclusion: "x ∈ integral_closure(restrict_ring(field_ring(L), «away»), K)",
			},
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				member := b.Assume()
				opened := b.Conjuncts(
					b.Simplified(member, Fwd(RingAwayMember)),
					"x lies in K",
					"a power of t brings x into the closure of R")
				xm := b.MemberOf[on.L](x, b.Have(
					"so x lies in L",
					"x ∈ L.carrier",
					BySets(opened[0], kInL)))
				N, scaledIn := b.UnpackAs[Nat](opened[1], "N")
				scaledParts := b.Conjuncts(
					b.Have(
						"tᴺ·x lies in K and is integral over R",
						"monoid_pow(L.mul, L.one, t, N) * x ∈ K ∧ "+
							"integral_over(restrict_ring(field_ring(L), R), monoid_pow(L.mul, L.one, t, N) * x)",
						BySets(scaledIn, integral_element.IntegralClosureDef)),
					"tᴺ·x lies in K",
					"tᴺ·x is integral over R")
				q, relation := b.UnpackAs[Fun[Nat, A]](
					b.Unfolded(scaledParts[1], integral_element.IntegralOverDef), "q")
				data := b.Conjuncts(
					relation,
					"q is a polynomial over R",
					"it is monic",
					"of positive degree",
					"and vanishes at tᴺ·x")
				b.Cases(b.TermAs[Bool]("t = L.zero"))
				b.When(
					"at t = zero x lies in R[1/t], and is a root of X − x over it",
					func(c *Argument, isZero Fact) {
						vanishing := c.Have(
							"t¹·x is zero, t being zero",
							"monoid_pow(L.mul, L.one, t, 1) * x = L.zero",
							isZero.Rw(),
							ByArith(L, xm))
						xAway := c.Have(
							"so t brings x into R: x lies in R[1/t]",
							"x ∈ «away»",
							By(opened[0], vanishing, comm_ring.SubringZero.Read(subringR), RingAwayMember.At(kRing, R, t, x)))
						integral := c.Have(
							"x is a root of the monic X − x over R[1/t]",
							"integral_over(restrict_ring(field_ring(L), «away»), x)",
							Unfold(integral_element.IntegralOverDef),
							Witness(c.TermAs[Fun[Nat, A]]("«linear»(x)")),
							ByArith(
								polynomial_roots.LinearFactor.Read(ringAway).At(proof.MemberOf(x, xAway)),
								field.OneNotZeroOn.Read(L)))
						c.Show(
							"so x lies in the closure of R[1/t]",
							BySets(opened[0], integral, integral_element.IntegralClosureDef))
					})
				b.Otherwise(
					"for t ≠ zero, x = t^(−N)·(tᴺ·x), and t^(−N) brings q into R[1/t]",
					func(c *Argument, nonzero Fact) {
						u := c.TermAs[A]("L.inv(t)")
						um := c.MemberOf[on.L](u, field.InvIn.Read(L).At(tm))
						inverse := c.Have(
							"t·t⁻¹ = 1",
							"t * L.inv(t) = L.one",
							By(nonzero, field.MulRightInverseOn.Read(L).At(tm)))
						uAway := c.Have(
							"t⁻¹ lies in K, a subfield, so in R[1/t]",
							"L.inv(t) ∈ «away»",
							By(
								inverse,
								subfieldK,
								tK,
								field.SubfieldInv.At(c.TermAs[FieldOps[A]]("L"), K, t),
								awayParts[2].At(u)))
						uNAway := comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ringAway)).At(
							proof.MemberOf(u, uAway), N)
						clearedAway := c.Have(
							"t^(−N) brings every coefficient of q into R[1/t]",
							"∀i:num. monoid_pow(L.mul, L.one, L.inv(t), N) * q(i) ∈ «away»",
							BySets(
								uAway,
								data[0],
								awayParts[0],
								polynomial.PolynomialOverDef,
								comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ringAway)),
								comm_ring.MulIn.Read(ringAway)))
						overL := c.Have(
							"q is a polynomial over L",
							"polynomial_over(L.carrier, q)",
							By(
								data[0],
								comm_ring.SubringSubset.Read(subringR),
								polynomial.PolynomialOverMono.At(zero, R, carrier, q)))
						scaledM := c.MemberOf[on.L](c.TermAs[A]("monoid_pow(L.mul, L.one, t, N) * x"), c.Have(
							"tᴺ·x lies in L",
							"monoid_pow(L.mul, L.one, t, N) * x ∈ L.carrier",
							BySets(scaledParts[0], kInL)))
						integral := c.Have(
							"so t^(−N)·(tᴺ·x) is integral over R[1/t]",
							"integral_over(restrict_ring(field_ring(L), «away»), "+
								"    monoid_pow(L.mul, L.one, L.inv(t), N) * (monoid_pow(L.mul, L.one, t, N) * x))",
							By(
								subringAway,
								overL,
								data[1],
								data[2],
								data[3],
								uNAway,
								clearedAway,
								integral_element.ScaledRootIntegral.Read(L).At(
									away, q, c.TermAs[A]("monoid_pow(L.mul, L.one, L.inv(t), N)"), scaledM)))
						powersCancel := c.Have(
							"tᴺ·t^(−N) = 1",
							"monoid_pow(L.mul, L.one, t, N) * monoid_pow(L.mul, L.one, L.inv(t), N) = L.one",
							By(inverse, comm_monoid.PowInverseOn.Read(comm_ring.MulMonoidOn.Read(ring)).At(tm, um, N)))
						recovered := c.Have(
							"and t^(−N)·(tᴺ·x) is x",
							"monoid_pow(L.mul, L.one, L.inv(t), N) * (monoid_pow(L.mul, L.one, t, N) * x) = x",
							ByArith(L, tm, um, xm, Scaled(x, powersCancel)))
						c.Show(
							"so x lies in the closure of R[1/t]",
							BySets(opened[0], recovered, integral, integral_element.IntegralClosureDef))
					})
			}))
		a.Show(
			"so the two closures are one set",
			BySets(forward, backward))
	}),
})}
