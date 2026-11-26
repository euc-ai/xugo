// one_and_element.go — a subring S of the field and a member e of it: the
// set S + S·e of the p + q·e with p and q in S, which one and e span over
// S, which is a ring when e² lies in S, and which is free over S on one
// and e when c + d·e vanishes only at c = d = zero.

package fractional_ideal

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/sets/set_algebra"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// SpanOneAndElement — over a subring S of the field, one and a member e of
// the field span S + S · e: one alone spans S (SpanHoldingOne), and a
// further generator adds its multiples (SpanInsert).
var SpanOneAndElement = spanOneAndElementThm{family.Add(registry.ProofEntry{
	Name: "SpanOneAndElement",
	Key:  "prop_4516577bad377228",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S:set(A). ∀e:A.",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"e ∈ L.carrier",
		},
		Conclusion: "module_span(restrict_ring(field_ring(L), S), " +
			"    regular_module(field_ring(L)), " +
			"    {L.one, e}) = " +
			"«oneAndElement»",
	},
		func(a *Argument, L field.FieldFact[on.L], S *Expr[Set[A]], e *Expr[A], h Fact) {
			given := a.Conjuncts(
				h,
				"S is a subring of L",
				"e lies in L")
			subringS, eInL := given[0], given[1]
			one, empty, single := a.TermAs[A]("L.one"), a.TermAs[Set[A]]("∅"), a.TermAs[Set[A]]("{L.one}")
			fieldModule := a.Have(
				"L is a module over S",
				"module_on(restrict_ring(field_ring(L), S), regular_module(field_ring(L)))",
				By(subringS, FieldModuleOn.Read(L).At(S)))
			spanOne := a.Have(
				"one alone spans S",
				"module_span(restrict_ring(field_ring(L), S), regular_module(field_ring(L)), {L.one}) = S",
				By(
					subringS,
					comm_ring.SubringOne.Read(subringS),
					set_order.SingSubset.At(S, one),
					set_algebra.InsertContains.At(empty, one),
					SpanHoldingOne.Read(L).At(S, single)))
			withE := a.Have(
				"e adds its multiples to the span of one",
				"module_span(restrict_ring(field_ring(L), S), regular_module(field_ring(L)), {e, L.one}) = "+
					"{c * e + w | c:A, w:A | c ∈ S ∧ w ∈ S}",
				By(
					spanOne,
					comm_ring.OneIn.Read(field.RingOn.Read(L)),
					set_order.SingSubset.At(a.TermAs[Set[A]]("L.carrier"), one),
					submodule.SpanInsert.Read(fieldModule).At(single, proof.MemberOf(e, eInL))))
			commute := a.Have(
				"in L the two summands commute",
				"∀c w:A. c ∈ S ∧ w ∈ S ⇒ c * e + w = w + c * e",
				Derive(func(b *Argument) {
					b.FixAs[A]("c")
					b.FixAs[A]("w")
					inField := b.Have(
						"c and w lie in L, as S does",
						"c ∈ L.carrier ∧ w ∈ L.carrier",
						BySets(b.Assume(), comm_ring.SubringSubset.Read(subringS)))
					b.Show(
						"the field's sum commutes",
						ByArith(field.RingOn.Read(L), inField, eInL))
				}))
			swap := a.Have(
				"one and e may be listed in either order",
				"{L.one, e} = {e, L.one}",
				Cite(set_algebra.InsertComm))
			a.Show(
				"so the span of one and e is the sums p + q · e",
				swap.Rw(),
				withE.Rw(),
				BySets(commute))
		}),
})}

// RingOneAndElement — S + S·e is a subring of L when e² lies in S: it lies
// in L, holds S, each p being p + zero·e, and e, which is zero + one·e; sums
// and negatives of members are members coefficient by coefficient, and
// (p + q·e)(r + s·e) = (pr + qs·e²) + (ps + qr)·e has its coefficients in
// S. A subset of L holding zero and one and closed under +, − and * is a
// subring of L by definition.
var RingOneAndElement = ringOneAndElementThm{family.Add(registry.ProofEntry{
	Name: "RingOneAndElement",
	Key:  "prop_1498184ab8325da0",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S:set(A). ∀e:A.",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"e ∈ L.carrier",
			"e * e ∈ S",
		},
		Conclusion: "subring(field_ring(L), «oneAndElement») ∧ S ⊆ «oneAndElement» ∧ e ∈ «oneAndElement»",
	},
		func(a *Argument, L field.FieldFact[on.L], S *Expr[Set[A]], e *Expr[A], h Fact) {
			given := a.Conjuncts(
				h,
				"S is a subring of L",
				"e lies in L",
				"e² lies in S")
			subringS, eInL, square := given[0], given[1], given[2]
			ring := field.RingOn.Read(L)
			zero, one := a.TermAs[A]("L.zero"), a.TermAs[A]("L.one")
			sInL := a.Have(
				"S lies in L",
				"S ⊆ L.carrier",
				By(comm_ring.SubringSubset.Read(subringS)))
			zeroIn, oneIn := comm_ring.SubringZero.Read(subringS), comm_ring.SubringOne.Read(subringS)
			addIn, negIn, mulIn :=
				comm_ring.SubringAdd.Read(subringS),
				comm_ring.SubringNeg.Read(subringS),
				comm_ring.SubringMul.Read(subringS)

			// S + S·e is the set of the p + q·e.
			inSet := a.Have(
				"S + S·e is the set of the p + q·e with p and q in S",
				"∀z:A. z ∈ «oneAndElement» ⇔ ∃p q:A. p ∈ S ∧ q ∈ S ∧ z = p + q * e",
				SetTac())
			intoSet := a.Have(
				"so p + q·e lies in it for p and q in S",
				"∀p q:A. p ∈ S ∧ q ∈ S ⇒ p + q * e ∈ «oneAndElement»",
				BySets())

			// S + S·e lies in L and holds S and e.
			setInL := a.Have(
				"S + S·e lies in L, its members p + q·e formed in L",
				"«oneAndElement» ⊆ L.carrier",
				Unfold(set_basic.SubsetDef),
				Derive(func(c *Argument) {
					z := c.FixAs[A]("z")
					_, _, form := c.Obtain2As[A, A](
						"z is p + q·e with p and q in S",
						"∃p q:A. p ∈ S ∧ q ∈ S ∧ z = p + q * e",
						By(inSet.At(z), c.Assume()))
					inL := c.Have(
						"p and q lie in L, as S does",
						"p ∈ L.carrier ∧ q ∈ L.carrier",
						BySets(sInL, form))
					c.Show(
						"so does p + q·e, L being closed under + and *",
						By(Normalized, form, inL, eInL, comm_ring.AddIn.Read(ring), comm_ring.MulIn.Read(ring)))
				}))
			sInSet := a.Have(
				"S lies in S + S·e, each p being p + zero·e",
				"S ⊆ «oneAndElement»",
				Unfold(set_basic.SubsetDef),
				Derive(func(c *Argument) {
					p := c.FixAs[A]("p")
					pIn := c.Assume()
					pInL := c.Have(
						"p lies in L, as S does",
						"p ∈ L.carrier",
						BySets(sInL, pIn))
					plain := c.Have(
						"p is p + zero·e",
						"p + L.zero * e = p",
						ByArith(ring, pInL, eInL))
					c.Show(
						"which lies in S + S·e",
						By(pIn, zeroIn, plain, intoSet.At(p, zero)))
				}))
			eValue := a.Have(
				"e is zero + one·e",
				"L.zero + L.one * e = e",
				ByArith(ring, eInL))
			eInSet := a.Have(
				"so e lies in S + S·e",
				"e ∈ «oneAndElement»",
				By(Normalized, zeroIn, oneIn, eValue, intoSet.At(zero, one)))
			zeroOne := a.Have(
				"and so do zero and one, members of S",
				"L.zero ∈ «oneAndElement» ∧ L.one ∈ «oneAndElement»",
				BySets(sInSet, zeroIn, oneIn))

			// Sums, negatives and products of members of S + S·e are members.
			sums := a.Have(
				"S + S·e is closed under the sum: (p + q·e) + (r + s·e) = (p + r) + (q + s)·e",
				"∀z w:A. z ∈ «oneAndElement» ∧ w ∈ «oneAndElement» ⇒ z + w ∈ «oneAndElement»",
				Derive(func(c *Argument) {
					z, w := c.FixAs[A]("z"), c.FixAs[A]("w")
					both := c.Assume()
					_, _, zForm := c.Obtain2As[A, A](
						"z is p + q·e with p and q in S",
						"∃p q:A. p ∈ S ∧ q ∈ S ∧ z = p + q * e",
						By(inSet.At(z), both))
					_, _, wForm := c.Obtain2As[A, A](
						"and w is r + s·e with r and s in S",
						"∃r s:A. r ∈ S ∧ s ∈ S ∧ w = r + s * e",
						By(inSet.At(w), both))
					inL := c.Have(
						"p, q, r and s lie in L, as S does",
						"p ∈ L.carrier ∧ q ∈ L.carrier ∧ r ∈ L.carrier ∧ s ∈ L.carrier",
						BySets(sInL, zForm, wForm))
					regroup := c.Have(
						"(p + q·e) + (r + s·e) = (p + r) + (q + s)·e",
						"(p + q * e) + (r + s * e) = (p + r) + (q + s) * e",
						ByArith(ring, inL, eInL))
					c.Show(
						"which lies in S + S·e, S being closed under the sum",
						By(zForm, wForm, regroup, addIn, intoSet.At(c.TermAs[A]("p + r"), c.TermAs[A]("q + s"))))
				}))
			negatives := a.Have(
				"and under negation: −(p + q·e) = (−p) + (−q)·e",
				"∀z:A. z ∈ «oneAndElement» ⇒ -z ∈ «oneAndElement»",
				Derive(func(c *Argument) {
					z := c.FixAs[A]("z")
					_, _, zForm := c.Obtain2As[A, A](
						"z is p + q·e with p and q in S",
						"∃p q:A. p ∈ S ∧ q ∈ S ∧ z = p + q * e",
						By(inSet.At(z), c.Assume()))
					inL := c.Have(
						"p and q lie in L, as S does",
						"p ∈ L.carrier ∧ q ∈ L.carrier",
						BySets(sInL, zForm))
					regroup := c.Have(
						"−(p + q·e) = (−p) + (−q)·e",
						"-(p + q * e) = -p + (-q) * e",
						ByArith(ring, inL, eInL))
					c.Show(
						"which lies in S + S·e, S being closed under negation",
						By(zForm, regroup, negIn, intoSet.At(c.TermAs[A]("-p"), c.TermAs[A]("-q"))))
				}))
			products := a.Have(
				"and under the product: (p + q·e)(r + s·e) = (pr + qs·e²) + (ps + qr)·e",
				"∀z w:A. z ∈ «oneAndElement» ∧ w ∈ «oneAndElement» ⇒ z * w ∈ «oneAndElement»",
				Derive(func(c *Argument) {
					z, w := c.FixAs[A]("z"), c.FixAs[A]("w")
					both := c.Assume()
					_, _, zForm := c.Obtain2As[A, A](
						"z is p + q·e with p and q in S",
						"∃p q:A. p ∈ S ∧ q ∈ S ∧ z = p + q * e",
						By(inSet.At(z), both))
					_, _, wForm := c.Obtain2As[A, A](
						"and w is r + s·e with r and s in S",
						"∃r s:A. r ∈ S ∧ s ∈ S ∧ w = r + s * e",
						By(inSet.At(w), both))
					inL := c.Have(
						"p, q, r and s lie in L, as S does",
						"p ∈ L.carrier ∧ q ∈ L.carrier ∧ r ∈ L.carrier ∧ s ∈ L.carrier",
						BySets(sInL, zForm, wForm))
					regroup := c.Have(
						"multiplied out",
						"(p + q * e) * (r + s * e) = (p * r + (q * s) * (e * e)) + (p * s + q * r) * e",
						ByArith(ring, inL, eInL))
					crossed := c.Have(
						"the products of the coefficients lie in S, a ring",
						"p * r ∈ S ∧ q * s ∈ S ∧ p * s ∈ S ∧ q * r ∈ S",
						By(zForm, wForm, mulIn))
					scaled := c.Have(
						"and so does q·s·e², e² lying in S",
						"(q * s) * (e * e) ∈ S",
						By(crossed, square, mulIn))
					coefficientsIn := c.Have(
						"so the two coefficients of the product lie in S",
						"p * r + (q * s) * (e * e) ∈ S ∧ p * s + q * r ∈ S",
						By(crossed, scaled, addIn))
					c.Show(
						"and the product lies in S + S·e",
						By(
							zForm,
							wForm,
							regroup,
							coefficientsIn,
							intoSet.At(c.TermAs[A]("p * r + (q * s) * (e * e)"), c.TermAs[A]("p * s + q * r"))))
				}))
			setSubring := a.Have(
				"a subset of L holding zero and one and closed under +, − and *, S + S·e is a subring of L",
				"subring(field_ring(L), «oneAndElement»)",
				Simp(Fwd(comm_ring.SubringDef)),
				By(setInL, zeroOne, sums, negatives, products))
			a.Show(
				"S + S·e is a subring of L holding S and e",
				By(setSubring, sInSet, eInSet))
		}),
})}

// BasisOneAndElement — S + S·e is free over S on one and e when c + d·e
// vanishes only at c = d = zero. One and e span it (SpanOneAndElement),
// so it is a submodule of L. One is not e, as −one + one·e would vanish
// with the coefficient one; and c · one + d · e is c + d·e, so one and e
// are independent (linear_independence.IndependentPair).
var BasisOneAndElement = basisOneAndElementThm{family.Add(registry.ProofEntry{
	Name: "BasisOneAndElement",
	Key:  "prop_1b30505c4dc3a4af",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S:set(A). ∀e:A.",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"e ∈ L.carrier",
			"∀c d:A. c ∈ S ∧ d ∈ S ∧ c + d * e = L.zero ⇒ c = L.zero ∧ d = L.zero",
		},
		Conclusion: "module_basis(restrict_ring(field_ring(L), S), " +
			"    restrict_module(regular_module(field_ring(L)), «oneAndElement»), " +
			"    {L.one, e}) ∧ " +
			"L.one ≠ e",
	},
		func(a *Argument, L field.FieldFact[on.L], S *Expr[Set[A]], e *Expr[A], h Fact) {
			given := a.Conjuncts(
				h,
				"S is a subring of L",
				"e lies in L",
				"c + d·e vanishes only at c = d = zero")
			subringS, eInL, independence := given[0], given[1], given[2]
			ring := field.RingOn.Read(L)
			ringS := a.Have(
				"S is a ring under the field's operations",
				"comm_ring_on(restrict_ring(field_ring(L), S))",
				By(subringS, comm_ring.SubringRingOn.Read(ring).At(S)))
			one := a.TermAs[A]("L.one")
			pair, set := a.TermAs[Set[A]]("{L.one, e}"), a.TermAs[Set[A]]("«oneAndElement»")
			oneInS := comm_ring.OneIn.Read(ringS)
			fieldModule := a.Have(
				"L is a module over S",
				"module_on(restrict_ring(field_ring(L), S), regular_module(field_ring(L)))",
				By(subringS, FieldModuleOn.Read(L).At(S)))
			oneInL := a.Have(
				"one lies in L",
				"L.one ∈ L.carrier",
				By(comm_ring.OneIn.Read(ring)))
			pairInL := a.Have(
				"one and e lie in L",
				"{L.one, e} ⊆ L.carrier",
				Simp(Fwd(set_order.InsertSubset), Fwd(set_order.EmptySubset)),
				By(oneInL, eInL))
			em := a.MemberOf[on.L](e, eInL)

			// One and e span S + S·e, which is so a submodule of L.
			spans := a.Have(
				"one and e span S + S·e",
				"module_span(restrict_ring(field_ring(L), S), regular_module(field_ring(L)), {L.one, e}) = "+
					"«oneAndElement»",
				By(subringS, SpanOneAndElement.Read(L).At(S, em)))
			setSubmodule := a.Have(
				"so S + S·e, a span, is a submodule of L over S",
				"submodule(restrict_ring(field_ring(L), S), regular_module(field_ring(L)), «oneAndElement»)",
				spans.RwRev(),
				By(pairInL, submodule.SpanSubmodule.Read(fieldModule).At(pair)))

			// One is not e: −one + one·e would vanish with the coefficient one.
			oneNotE := a.Have(
				"one is not e, else −one + one·e would be a vanishing combination with the coefficient one",
				"L.one ≠ e",
				Derive(func(c *Argument) {
					equal := c.SupposeNot()
					vanish := c.Have(
						"−one + one·e would be zero",
						"-L.one + L.one * e = L.zero",
						ByArith(ring, equal, eInL))
					bothZero := c.Have(
						"so one would be zero",
						"-L.one = L.zero ∧ L.one = L.zero",
						By(comm_ring.NegIn.Read(ringS), oneInS, vanish, independence.At(c.TermAs[A]("-L.one"), one)))
					c.Show(
						"but one is not zero",
						By(bothZero, field.OneNotZeroOn.Read(L)))
				}))

			// One and e are independent over S: c · one + d · e is c + d · e.
			combinations := a.Have(
				"so c · one + d · e = zero with c and d in S has c = d = zero",
				"∀c d:A. c ∈ S ∧ d ∈ S ∧ c * L.one + d * e = L.zero ⇒ c = L.zero ∧ d = L.zero",
				Derive(func(b *Argument) {
					c, d := b.FixAs[A]("c"), b.FixAs[A]("d")
					given := b.Conjuncts(
						b.Assume(),
						"c lies in S",
						"so does d",
						"c · one + d · e = zero")
					inL := b.Have(
						"c and d lie in L, as S does",
						"c ∈ L.carrier ∧ d ∈ L.carrier",
						BySets(given[0], given[1], comm_ring.SubringSubset.Read(subringS)))
					plain := b.Have(
						"that is, c + d · e = zero",
						"c + d * e = L.zero",
						ByArith(ring, inL, eInL, given[2]))
					b.Show(
						"so both coefficients vanish",
						By(given[0], given[1], plain, independence.At(c, d)))
				}))
			independent := a.Have(
				"so one and e are independent over S",
				"module_independent(restrict_ring(field_ring(L), S), regular_module(field_ring(L)), {L.one, e})",
				By(
					oneNotE,
					combinations,
					linear_independence.IndependentPair.Read(fieldModule).At(
						proof.MemberOf(one, oneInL), proof.MemberOf(e, eInL))))
			a.Show(
				"independent and spanning the submodule S + S·e, one and e are a basis of it, and one is not e",
				By(
					setSubmodule,
					independent,
					spans,
					oneNotE,
					linear_independence.BasisRestrict.Read(fieldModule).At(set, pair)))
		}),
})}
