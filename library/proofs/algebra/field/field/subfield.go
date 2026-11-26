// subfield.go — subfields of a field on a set: the subsets the field's
// operations never leave, each a field on its own set.

package field

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Subfields
// ---------------------------------------------------------------------------

// SubfieldDef — a subset of F's carrier holding zero and one and closed
// under addition, negation, multiplication and inverse.
var SubfieldDef = subfieldDefThm{family.Define(registry.DefEntry{
	Name:  "SubfieldDef",
	Key:   "prop_6d892d3e4c1948e6",
	Const: "subfield", Type: "field_ops(A) → set(A) → bool",
	Equations: []string{
		"∀F:field_ops(A). ∀k:set(A). " +
			"    subfield(F, k) ⇔ " +
			"    k ⊆ F.carrier ∧ " +
			"    F.zero ∈ k ∧ " +
			"    F.one ∈ k ∧ " +
			"    (∀x y:A. x ∈ k ∧ y ∈ k ⇒ F.add(x, y) ∈ k) ∧ " +
			"    (∀x:A. x ∈ k ⇒ F.neg(x) ∈ k) ∧ " +
			"    (∀x y:A. x ∈ k ∧ y ∈ k ⇒ F.mul(x, y) ∈ k) ∧ " +
			"    (∀x:A. x ∈ k ⇒ F.inv(x) ∈ k)",
	},
})}

// The conditions, each a law a proof cites instead of unfolding the
// definition. They ask nothing of the field, so each spells the
// components.

// SubfieldSubset — a subfield lies in the carrier.
var SubfieldSubset = subfieldSubsetThm{family.Add(registry.ProofEntry{
	Name:  "SubfieldSubset",
	Key:   "prop_36063def1610acdc",
	Build: SubfieldDef.Entry().Conjunct("k ⊆ F.carrier"),
})}

// SubfieldZero — a subfield holds zero.
var SubfieldZero = subfieldZeroThm{family.Add(registry.ProofEntry{
	Name:  "SubfieldZero",
	Key:   "prop_6dc2452b8960793c",
	Build: SubfieldDef.Entry().Conjunct("F.zero ∈ k"),
})}

// SubfieldOne — and one.
var SubfieldOne = subfieldOneThm{family.Add(registry.ProofEntry{
	Name:  "SubfieldOne",
	Key:   "prop_e954f96e1c8af5e6",
	Build: SubfieldDef.Entry().Conjunct("F.one ∈ k"),
})}

// SubfieldAdd — a subfield holds the sum of two of its members.
var SubfieldAdd = subfieldAddThm{family.Add(registry.ProofEntry{
	Name: "SubfieldAdd",
	Key:  "prop_49953689014b9984",
	Build: SubfieldDef.Entry().Conjunct(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ k",
			"y ∈ k",
		},
		Conclusion: "F.add(x, y) ∈ k",
	}),
})}

// SubfieldNeg — the negation of a member.
var SubfieldNeg = subfieldNegThm{family.Add(registry.ProofEntry{
	Name: "SubfieldNeg",
	Key:  "prop_2b8613d142570ed4",
	Build: SubfieldDef.Entry().Conjunct(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ k",
		},
		Conclusion: "F.neg(x) ∈ k",
	}),
})}

// SubfieldMul — the product of two members.
var SubfieldMul = subfieldMulThm{family.Add(registry.ProofEntry{
	Name: "SubfieldMul",
	Key:  "prop_de87b3374b227665",
	Build: SubfieldDef.Entry().Conjunct(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ k",
			"y ∈ k",
		},
		Conclusion: "F.mul(x, y) ∈ k",
	}),
})}

// SubfieldInv — and the inverse of a member.
var SubfieldInv = subfieldInvThm{family.Add(registry.ProofEntry{
	Name: "SubfieldInv",
	Key:  "prop_8499981b2764b8bf",
	Build: SubfieldDef.Entry().Conjunct(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ k",
		},
		Conclusion: "F.inv(x) ∈ k",
	}),
})}

// RingSubfieldDef — k is a field under R's own addition and
// multiplication, with inverse inv. Its division is x * inv(y), which
// field_on asks of any division on k, so a division component would add
// nothing.
var RingSubfieldDef = ringSubfieldDefThm{family.Define(registry.DefEntry{
	Name:  "RingSubfieldDef",
	Key:   "prop_2f9f00512ff3e828",
	Const: "ring_subfield", Type: "ring_ops(A) → (A → A) → set(A) → bool",
	Reading: "Neither k ⊆ R.carrier nor a ring on R.carrier is asked: the predicate speaks of k " +
		"under R's operations alone, and a statement that wants k inside R states k ⊆ R.carrier beside it.",
	Equations: []string{
		"∀R:ring_ops(A). ∀inv:(A → A). ∀k:set(A). " +
			"    ring_subfield(R, inv, k) ⇔ " +
			"    field_on(mk_field(R.add, " +
			"            R.zero, " +
			"            R.neg, " +
			"            R.mul, " +
			"            R.one, " +
			"            R.sub, " +
			"            inv, " +
			"            λx:A. λy:A. R.mul(x, inv(y)), " +
			"            k))",
	},
	Deps: []registry.EntryLike{FieldOn},
})}

// FieldOnRingSubfield — a field on k under R's operations, whatever its
// division, makes k a field under R's operations with the same inverse:
// the ring, the inverse and its laws are the field's, and field_on asks of
// the division only that it be the product by the inverse, which
// x * inv(y) is.
var FieldOnRingSubfield = fieldOnRingSubfieldThm{family.Add(registry.ProofEntry{
	Name: "FieldOnRingSubfield",
	Key:  "prop_2f282b09f731d607",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀inv:(A → A). ∀div:(A → A → A). ∀k:set(A).",
		Hypotheses: []string{
			"field_on(mk_field(R.add, R.zero, R.neg, R.mul, R.one, R.sub, inv, div, k))",
		},
		Conclusion: "ring_subfield(R, inv, k)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			inv *Arrow[A, A],
			div *Arrow2[A, A, A],
			k *Expr[Set[A]],
			field Fact,
		) {
			ring := a.Simplified(RingOn.Read(field), Fwd(FieldRingDef))
			a.Show(
				"the ring on k, the inverse and its laws are the "+
					"field's, and x * inv(y) is the product by the inverse",
				Simp(Fwd(RingSubfieldDef), Fwd(FieldOn), Fwd(FieldRingDef)),
				By(
					ring,
					InvIn.Read(field),
					OneNotZeroOn.Read(field),
					MulLeftInverseOn.Read(field),
					InvZeroOn.Read(field)))
		}),
})}

// RingSubfieldSubring — a field under R's operations lying in R.carrier is
// a subring of R: the field's ring on k holds zero and one and is closed
// under the sum, the negation and the product.
var RingSubfieldSubring = ringSubfieldSubringThm{family.Add(registry.ProofEntry{
	Name: "RingSubfieldSubring",
	Key:  "prop_49e3f7b29f94a5a2",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀inv:(A → A). ∀k:set(A).",
		Hypotheses: []string{
			"k ⊆ R.carrier",
			"ring_subfield(R, inv, k)",
		},
		Conclusion: "subring(R, k)",
	},
		func(a *Argument, R *Expr[RingOps[A]], inv *Arrow[A, A], k *Expr[Set[A]], kInR, subfield Fact) {
			ring := RingOn.Read(a.Unfolded(subfield, RingSubfieldDef))
			a.Show(
				"k lies in R.carrier, and the ring on k holds zero and one "+
					"and is closed under the sum, the negation and the product",
				Simp(Fwd(comm_ring.SubringDef)),
				By(
					kInR,
					comm_ring.ZeroIn.Read(ring),
					comm_ring.OneIn.Read(ring),
					comm_ring.AddIn.Read(ring),
					comm_ring.NegIn.Read(ring),
					comm_ring.MulIn.Read(ring)))
		}),
})}

// RingSubfieldRestrict — whether k is a field under R's operations does not
// depend on R's carrier: restricting R to a set keeps its six operations,
// and the predicate reads those alone.
var RingSubfieldRestrict = ringSubfieldRestrictThm{family.Add(registry.ProofEntry{
	Name: "RingSubfieldRestrict",
	Key:  "prop_422fc75025c8b417",
	Build: family.Theorem("∀R:ring_ops(A). ∀S:set(A). ∀inv:(A → A). ∀k:set(A). "+
		"    ring_subfield(restrict_ring(R, S), inv, k) ⇔ ring_subfield(R, inv, k)",
		func(a *Argument) {
			a.Show(
				"both sides are the field on k that R's six operations make with inv",
				Simp(Fwd(RingSubfieldDef), Fwd(module_record.RestrictRingDef)),
				Basic())
		}),
})}

// ---------------------------------------------------------------------------
// A subfield is a field on its set
// ---------------------------------------------------------------------------

// SubfieldFieldOn — under a field on F.carrier, a subfield is exactly a subset
// of F.carrier that is a field on its own set with the same operations: the
// closure conditions are the subfield's, and every axiom on k is an
// instance of the field's on F.carrier. A subfield is a subset of the ring on F.carrier
// holding zero and one and closed under the sum, the negation and the
// product, so a ring on its own set; it is closed under the inverse by
// its own condition, and each other field axiom is the field's on F.carrier,
// read at members of k.
var SubfieldFieldOn = subfieldFieldOnThm{family.Add(registry.ProofEntry{
	Name: "SubfieldFieldOn",
	Key:  "prop_bd5fc724d7450afa",
	Reading: "The conjunct k ⊆ F.carrier is load-bearing in ⇐: " +
		"field_on(restrict_field(F, k)) alone does not put k inside the ambient field carrier.",
	Build: FieldOn.Law("∀k:set(A). subfield(F, k) ⇔ k ⊆ F.carrier ∧ field_on(restrict_field(F, k))",
		func(a *Argument, field FieldFact[on.F], k *Expr[Set[A]]) {
			a.Iff()
			a.Forward(
				"the closure conditions are the subfield's, and each "+
					"axiom on k is an instance of the field's on F.carrier",
				func(b *Argument, subfield Fact) {
					kInC := b.Have(
						"k lies in F.carrier",
						"k ⊆ F.carrier",
						By(SubfieldSubset, subfield))
					// Each axiom of field_on(k) is had before field_on is unfolded:
					// the unfolding opens the resident field on F.carrier as well, and a
					// fact had before it stays.
					ringOnK := b.Have(
						"k is a commutative ring on its own set: a subset of F.carrier holding "+
							"zero and one, closed under the sum, the negation and the product",
						"comm_ring_on(field_ring(restrict_field(F, k)))",
						Simp(Rev(RestrictFieldRing)),
						By(
							comm_ring.ClosedSubsetRingOn.Read(RingOn.Read(field)).At(k),
							kInC,
							SubfieldZero.Read(subfield),
							SubfieldAdd.Read(subfield),
							SubfieldNeg.Read(subfield),
							SubfieldOne.Read(subfield),
							SubfieldMul.Read(subfield)))
					inverses := b.Have(
						"k holds the inverse of each member",
						"∀x:A. x ∈ k ⇒ F.inv(x) ∈ k",
						By(SubfieldInv, subfield))
					oneNotZero := b.Have(
						"one is not zero, in the field",
						"F.one ≠ F.zero",
						By(OneNotZeroOn.Read(field)))
					// An axiom at members of k is the axiom on F.carrier, read through the
					// inclusion.
					inclusion := b.Unfolded(kInC, set_basic.SubsetDef)
					leftInverse := b.Have(
						"a nonzero member of k has its left inverse, as in F.carrier",
						"∀x:A. x ∈ k ⇒ x ≠ F.zero ⇒ F.inv(x) * x = F.one",
						By(inclusion, MulLeftInverseOn.Read(field)))
					invZero := b.Have(
						"the inverse of zero is zero, in the field",
						"F.inv(F.zero) = F.zero",
						By(InvZeroOn.Read(field)))
					division := b.Have(
						"a quotient of members of k is the product by the inverse, as in F.carrier",
						"∀x y:A. x ∈ k ∧ y ∈ k ⇒ x / y = x * F.inv(y)",
						By(inclusion, DivMulInvOn.Read(field)))
					b.Show(
						"k lies in F.carrier, and field_on(k) unfolded is the ring on k and the five facts after it",
						Unfold(FieldOn),
						By(kInC, ringOnK, inverses, oneNotZero, leftInverse, invZero, division))
				})
			a.Backward(
				"a subset of F.carrier that is a field on its own set "+
					"holds zero and one and is closed under the four operations",
				func(b *Argument, given Fact) {
					parts := b.Conjuncts(
						given,
						"k lies in F.carrier",
						"k is a field on its own set")
					ringOnK := RingOn.Read(parts[1])
					// Unfolded, subfield(F, k) asks the inclusion in hand and the six
					// closure conditions, each k's own.
					b.Do(Unfold(SubfieldDef), SplitConjAll(
						Case(
							"k lies in F.carrier",
							By(parts[0])),
						Case(
							"k holds zero",
							By(comm_ring.ZeroIn.Read(ringOnK))),
						Case(
							"and one",
							By(comm_ring.OneIn.Read(ringOnK))),
						Case(
							"k is closed under the sum",
							By(comm_ring.AddIn.Read(ringOnK))),
						Case(
							"under the negation",
							By(comm_ring.NegIn.Read(ringOnK))),
						Case(
							"under the product",
							By(comm_ring.MulIn.Read(ringOnK))),
						Case(
							"and under the inverse",
							By(InvIn.Read(parts[1]))),
					))
				})
		}),
})}

// SubfieldSubring — a subfield is a subring of the field's ring: a subring
// asks the subfield's conditions but the inverse.
var SubfieldSubring = subfieldSubringThm{family.Add(registry.ProofEntry{
	Name: "SubfieldSubring",
	Key:  "prop_943411013296749a",
	Build: FieldOn.Law(Statement{
		Binders: "∀k:set(A).",
		Hypotheses: []string{
			"subfield(F, k)",
		},
		Conclusion: "subring(field_ring(F), k)",
	},
		func(a *Argument, field FieldFact[on.F], k *Expr[Set[A]], subfield Fact) {
			a.Show(
				"the subring's conditions are the subfield's but the inverse",
				Simp(Fwd(comm_ring.SubringDef)),
				By(
					SubfieldSubset.Read(subfield),
					SubfieldZero.Read(subfield),
					SubfieldOne.Read(subfield),
					SubfieldAdd.Read(subfield),
					SubfieldNeg.Read(subfield),
					SubfieldMul.Read(subfield)))
		}),
})}

// SubfieldCommRing — a subfield is a commutative ring under the field's
// operations: it is a subring of the field's ring, and a subring is a ring
// on its own set.
var SubfieldCommRing = subfieldCommRingThm{family.Add(registry.ProofEntry{
	Name: "SubfieldCommRing",
	Key:  "prop_f0438341f60ebea2",
	Build: FieldOn.Law(Statement{
		Binders: "∀k:set(A).",
		Hypotheses: []string{
			"subfield(F, k)",
		},
		Conclusion: "comm_ring_on(restrict_ring(field_ring(F), k))",
	},
		func(a *Argument, field FieldFact[on.F], k *Expr[Set[A]], subfield Fact) {
			a.Show(
				"k is a subring of F's ring, and a subring is a ring on its own set",
				By(
					subfield,
					SubfieldSubring.Read(field).At(k),
					comm_ring.SubringRingOn.Read(RingOn.Read(field)).At(k)))
		}),
})}

// SubfieldRingSubfield — a subfield is a field under the operations of
// the field's ring, with the field's inverse, on whatever set that ring is
// restricted to: the subfield is a field on its own set with F's
// operations, and ring_subfield reads the ring's operations alone.
var SubfieldRingSubfield = subfieldRingSubfieldThm{family.Add(registry.ProofEntry{
	Name: "SubfieldRingSubfield",
	Key:  "prop_3f9034a04f2a31a4",
	Reading: "S may be any set, and k need not lie in it: restricting F's ring to S " +
		"changes its carrier and keeps its operations, which are all ring_subfield reads.",
	Build: FieldOn.Law(Statement{
		Binders: "∀k S:set(A).",
		Hypotheses: []string{
			"subfield(F, k)",
		},
		Conclusion: "ring_subfield(restrict_ring(field_ring(F), S), F.inv, k)",
	},
		func(a *Argument, field FieldFact[on.F], k, S *Expr[Set[A]], subfield Fact) {
			a.Show(
				"k is a field on its own set under F's operations, which are those of F's ring on S",
				By(
					subfield,
					SubfieldFieldOn.Read(field).At(k),
					RestrictFieldDef.At(a.TermAs[FieldOps[A]]("F"), k),
					FieldOnRingSubfield.At(
						a.TermAs[RingOps[A]]("restrict_ring(field_ring(F), S)"),
						a.TermAs[Fun[A, A]]("F.inv"),
						a.TermAs[Op[A]]("F.div"),
						k)))
		}),
})}

// CarrierSubfield — the carrier is a subfield of its own field: it lies
// in itself, and each closure condition is one of the field's own on F.carrier —
// the ring's for zero, one, the sum, the negation and the product, and
// the field's closure under the inverse.
var CarrierSubfield = carrierSubfieldThm{family.Add(registry.ProofEntry{
	Name: "CarrierSubfield",
	Key:  "prop_fb3bd054cf685c65",
	Build: FieldOn.Law("subfield(F, F.carrier)",
		func(a *Argument, field FieldFact[on.F]) {
			ring := RingOn.Read(field)
			a.Do(Unfold(SubfieldDef), SplitConjAll(
				Case(
					"F.carrier lies in itself",
					By(set_order.SubsetRefl)),
				Case(
					"F.carrier holds zero",
					By(comm_ring.ZeroIn.Read(ring))),
				Case(
					"F.carrier holds one",
					By(comm_ring.OneIn.Read(ring))),
				Case(
					"F.carrier is closed under the sum",
					By(comm_ring.AddIn.Read(ring))),
				Case(
					"F.carrier is closed under the negation",
					By(comm_ring.NegIn.Read(ring))),
				Case(
					"F.carrier is closed under the product",
					By(comm_ring.MulIn.Read(ring))),
				Case(
					"F.carrier is closed under the inverse",
					By(InvIn.Read(field))),
			))
		}),
})}

// FieldRingSubfield — a field's whole carrier is a field under its own
// ring's operations, with its own inverse: those operations and the
// field's inverse and division rebuild the field.
var FieldRingSubfield = fieldRingSubfieldThm{family.Add(registry.ProofEntry{
	Name: "FieldRingSubfield",
	Key:  "prop_a822c5df5575030b",
	Build: FieldOn.Law("ring_subfield(field_ring(F), F.inv, field_ring(F).carrier)",
		func(a *Argument, field FieldFact[on.F]) {
			a.Show(
				"the ring's operations with the inverse and the division rebuild F, a field",
				By(FieldOnRing.Read(field), Where(FieldOnRingSubfield, "div", a.TermAs[Op[A]]("F.div"))))
		}),
})}

// SubfieldSub — a subfield holds the difference of two members. Its
// members lie in F.carrier, where the difference is the sum with the negation,
// and the subfield holds both the negation and the sum.
var SubfieldSub = subfieldSubThm{family.Add(registry.ProofEntry{
	Name: "SubfieldSub",
	Key:  "prop_3ec256ec1dbabb9f",
	Build: FieldOn.Law(Statement{
		Binders: "∀k:set(A). ∀x y:A.",
		Hypotheses: []string{
			"subfield(F, k)",
			"x ∈ k",
			"y ∈ k",
		},
		Conclusion: "x - y ∈ k",
	},
		func(a *Argument, field FieldFact[on.F], k *Expr[Set[A]], x, y *Expr[A], given Fact) {
			parts := a.Conjuncts(
				given,
				"k is a subfield of F.carrier",
				"x lies in k",
				"and so does y")
			subfield, xInK, yInK := parts[0], parts[1], parts[2]
			inC := a.Have(
				"k lies in F.carrier, so x and y do",
				"x ∈ F.carrier ∧ y ∈ F.carrier",
				BySets(SubfieldSubset.Read(subfield), xInK, yInK))
			difference := a.Have(
				"in the ring on F.carrier, x - y is x plus the negation of y",
				"x - y = x + -y",
				By(comm_ring.SubAddNegOn.Read(RingOn.Read(field)), inC))
			a.Show(
				"x + -y is the sum of x and the negation of y, members of k",
				difference.Rw(),
				By(SubfieldAdd.Read(subfield), SubfieldNeg.Read(subfield), xInK, yInK))
		}),
})}

// SubfieldDiv — a subfield holds the quotient of two members. Its members
// lie in F.carrier, where the quotient is the product with the inverse, and
// the subfield holds both the inverse and the product. y = F.zero needs no
// guard, since SubfieldInv has none.
var SubfieldDiv = subfieldDivThm{family.Add(registry.ProofEntry{
	Name: "SubfieldDiv",
	Key:  "prop_183fcbc0faf57f31",
	Build: FieldOn.Law(Statement{
		Binders: "∀k:set(A). ∀x y:A.",
		Hypotheses: []string{
			"subfield(F, k)",
			"x ∈ k",
			"y ∈ k",
		},
		Conclusion: "x / y ∈ k",
	},
		func(a *Argument, field FieldFact[on.F], k *Expr[Set[A]], x, y *Expr[A], given Fact) {
			parts := a.Conjuncts(
				given,
				"k is a subfield of F.carrier",
				"x lies in k",
				"and so does y")
			subfield, xInK, yInK := parts[0], parts[1], parts[2]
			inC := a.Have(
				"k lies in F.carrier, so x and y do",
				"x ∈ F.carrier ∧ y ∈ F.carrier",
				BySets(SubfieldSubset.Read(subfield), xInK, yInK))
			quotient := a.Have(
				"in the field on F.carrier, x / y is x times the inverse of y",
				"x / y = x * F.inv(y)",
				By(DivMulInvOn.Read(field), inC))
			a.Show(
				"x * F.inv(y) is the product of x and the inverse of y, members of k",
				quotient.Rw(),
				By(SubfieldMul.Read(subfield), SubfieldInv.Read(subfield), xInK, yInK))
		}),
})}

// SubfieldPowerIn — a subfield holds the powers of its members: l is a field
// under the operations of M, and its multiplicative monoid holds the powers
// of its members.
var SubfieldPowerIn = subfieldPowerInThm{family.Add(registry.ProofEntry{
	Name: "SubfieldPowerIn",
	Key:  "prop_269931a5ad12b1ef",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀l:set(A). ∀c:A. ∀n:num.",
		Hypotheses: []string{
			"subfield(M, l)",
			"c ∈ l",
		},
		Conclusion: "monoid_pow(M.mul, M.one, c, n) ∈ l",
	},
		func(a *Argument, M FieldFact[on.M], l *Expr[Set[A]], c *Expr[A], n *Expr[Nat], subL, member Fact) {
			restricted := a.Have(
				"l is a field under the operations of M",
				"field_on(restrict_field(M, l))",
				By(subL, SubfieldFieldOn.Read(M).At(l)))
			a.Show(
				"the multiplicative monoid of l holds the powers of its members",
				BySets(member, comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(RingOn.Read(restricted)))))
		}),
})}

// SquareClosedDef — `square_closed(F, k)`: every member of k is the square
// of a member of k.
var SquareClosedDef = squareClosedDefThm{family.Define(registry.DefEntry{
	Name:  "SquareClosedDef",
	Key:   "prop_5088c130ff52bd2e",
	Const: "square_closed", Type: "field_ops(A) → set(A) → bool",
	Equations: []string{
		"∀F:field_ops(A). ∀k:set(A). square_closed(F, k) ⇔ ∀a:A. a ∈ k ⇒ ∃b:A. b ∈ k ∧ F.mul(b, b) = a",
	},
})}

// QuadraticFormula — two being nonzero, a root of a monic quadratic over a
// subfield k lies in k when the discriminant b·b − 4a has a square root s
// there: completing the square factors four times the quadratic as
// (2x + b − s)(2x + b + s), and a vanishing factor gives x = (±s − b)/2.
var QuadraticFormula = quadraticFormulaThm{family.Add(registry.ProofEntry{
	Name: "QuadraticFormula",
	Key:  "prop_237198016108f3d7",
	Build: FieldOn.Law(Statement{
		Binders: "∀k:set(A). ∀a b x:A.",
		Hypotheses: []string{
			"subfield(F, k)",
			"F.one + F.one ≠ F.zero",
			"a ∈ k",
			"b ∈ k",
			"∃s:A. s ∈ k ∧ s * s = b * b - (F.one + F.one) * (F.one + F.one) * a",
			"x ∈ F.carrier",
			"a + b * x + x * x = F.zero",
		},
		Conclusion: "x ∈ k",
	},
		func(
			arg *Argument,
			field FieldFact[on.F],
			k *Expr[Set[A]],
			a, b, x *Expr[A],
			subfield, twoNonzero, aK, bK, root, xIn, vanishes Fact,
		) {
			F := arg.TermAs[FieldOps[A]]("F")
			ring := RingOn.Read(field)
			one := arg.TermAs[A]("F.one")
			two := arg.TermAs[A]("F.one + F.one")
			inverseTwo := arg.TermAs[A]("F.inv(F.one + F.one)")
			s, square := arg.UnpackAs[A](root, "s")
			ambient := arg.Have(
				"the coefficients and the square root lie in the field",
				"a ∈ F.carrier ∧ b ∈ F.carrier ∧ s ∈ F.carrier",
				BySets(aK, bK, square, subfield, SubfieldSubset.At(F, k)))
			productZero := arg.Have(
				"completing the square factors four times the quadratic",
				"((F.one + F.one) * x + b - s) * ((F.one + F.one) * x + b + s) = F.zero",
				ByArith(field, ambient, xIn, vanishes, square))
			factorsIn := arg.Have(
				"both factors belong to the field",
				"(F.one + F.one) * x + b - s ∈ F.carrier ∧ (F.one + F.one) * x + b + s ∈ F.carrier",
				By(
					field,
					ambient,
					xIn,
					comm_ring.OneIn.Read(ring),
					comm_ring.AddIn.Read(ring),
					comm_ring.MulIn.Read(ring),
					comm_ring.SubIn.Read(ring)))
			zeroFactor := arg.Have(
				"a factor vanishes in a field",
				"(F.one + F.one) * x + b - s = F.zero ∨ (F.one + F.one) * x + b + s = F.zero",
				By(
					factorsIn,
					productZero,
					MulEqZeroOn.Read(field).AsFact().At(
						arg.TermAs[A]("(F.one + F.one) * x + b - s"), arg.TermAs[A]("(F.one + F.one) * x + b + s"))))
			twoIn := arg.Have(
				"two belongs to the field",
				"F.one + F.one ∈ F.carrier",
				By(field, comm_ring.OneIn.Read(ring), comm_ring.AddIn.Read(ring)))
			fromFactor := arg.Have(
				"a vanishing factor 2x + b − t with t in k puts the root in k",
				"∀t:A. t ∈ k ∧ (F.one + F.one) * x + b - t = F.zero ⇒ x ∈ k",
				Derive(func(c *Argument) {
					t := c.FixAs[A]("t")
					given := c.Conjuncts(
						c.Assume(),
						"t lies in k",
						"the factor at t vanishes")
					tK, factorZero := given[0], given[1]
					tIn := c.Have(
						"t lies in the field",
						"t ∈ F.carrier",
						BySets(tK, subfield, SubfieldSubset.At(F, k)))
					formula := c.Have(
						"the vanishing factor gives x = (t − b)/2",
						"x = F.inv(F.one + F.one) * (t - b)",
						ByArith(
							field,
							twoNonzero,
							ambient,
							tIn,
							xIn,
							twoIn,
							Scaled(inverseTwo, factorZero),
							Scaled(x, MulLeftInverseOn.Read(field).AsFact().At(two))))
					c.Show(
						"the quadratic formula uses only elements of k",
						By(
							Normalized,
							field,
							formula,
							subfield,
							tK,
							bK,
							SubfieldOne.At(F, k),
							SubfieldAdd.At(F, k, one, one),
							SubfieldInv.At(F, k, two),
							SubfieldSub.Read(field).At(k, t, b),
							SubfieldMul.At(F, k, inverseTwo, c.TermAs[A]("t - b"))))
				}))
			arg.Do(zeroFactor.SplitDisj(
				LeftHolds(
					"the first linear factor gives the root in k",
					Given(func(c *Argument, factorZero Fact) {
						c.Show(
							"the quadratic formula at s puts x in k",
							By(square, factorZero, fromFactor.At(s)))
					})),
				RightHolds(
					"the second linear factor is the first at −s",
					Given(func(c *Argument, factorZero Fact) {
						negated := c.TermAs[A]("-s")
						negatedK := c.Have(
							"−s lies in k",
							"-s ∈ k",
							By(field, subfield, square, SubfieldNeg.At(F, k, s)))
						firstForm := c.Have(
							"the second factor is 2x + b − (−s)",
							"(F.one + F.one) * x + b - -s = F.zero",
							ByArith(field, ambient, xIn, twoIn, factorZero))
						c.Show(
							"the quadratic formula at −s puts x in k",
							By(negatedK, firstForm, fromFactor.At(negated)))
					}))))
		}),
})}

// SubfieldInter — two subfields meet in a subfield: every defining
// condition holds in both sets and hence in their intersection.
var SubfieldInter = subfieldInterThm{family.Add(registry.ProofEntry{
	Name: "SubfieldInter",
	Key:  "prop_2ebc183c2d464a72",
	Build: family.Theorem(Statement{
		Binders:    "∀F:field_ops(A). ∀k l:set(A).",
		Hypotheses: []string{"subfield(F, k)", "subfield(F, l)"},
		Conclusion: "subfield(F, k ∩ l)",
	},
		func(a *Argument, _ *Expr[FieldOps[A]], k, l *Expr[Set[A]], subfields Fact) {
			conditions := a.Unfolded(subfields, SubfieldDef)
			a.Show(
				"each subfield condition holds in both k and l, so in their intersection",
				Simp(Fwd(SubfieldDef)),
				BySets(conditions),
			)
		}),
})}

// SubfieldInters — a nonempty family of subfields meets in a subfield.
// The meet of no subfield is 𝕌, which lies in F.carrier only when F.carrier is 𝕌, so
// the family must not be empty. Every member lies in F.carrier, so the meet of
// the nonempty family does; and each closure condition holds in every
// member, so in the meet.
var SubfieldInters = subfieldIntersThm{family.Add(registry.ProofEntry{
	Name: "SubfieldInters",
	Key:  "prop_1025fcb2f01d7118",
	Reading: "H ≠ ∅ is load-bearing: ⋂∅ is 𝕌, which is a " +
		"subset of F.carrier only when F.carrier is the whole type.",
	Build: family.Theorem(Statement{
		Binders:    "∀F:field_ops(A). ∀H:set(set(A)).",
		Hypotheses: []string{"¬(H = ∅)", "∀k:set(A). k ∈ H ⇒ subfield(F, k)"},
		Conclusion: "subfield(F, ⋂H)",
	},
		func(a *Argument, _ *Expr[FieldOps[A]], H *Expr[Set[Set[A]]], hypotheses Fact) {
			parts := a.Conjuncts(
				hypotheses,
				"H has a member",
				"every member of H is a subfield")
			nonEmpty, subfields := parts[0], parts[1]
			bounded := a.Have(
				"every member of H lies in F.carrier",
				"∀k:set(A). k ∈ H ⇒ k ⊆ F.carrier",
				a.ForEach(func(k *Expr[Set[A]]) Action {
					return By(subfields.At(k), SubfieldSubset)
				}))
			// Only the goal is opened by the definition: an Unfold would open the
			// hypothesis that every member of H is a subfield as well, and each
			// condition below is read in the members through its law.
			a.Do(Simp(Fwd(SubfieldDef)), SplitConjAll(
				Case(
					"⋂H lies in F.carrier, H having a member",
					By(set_order.IntersSubset, nonEmpty, bounded)),
				Case(
					"zero lies in every member of H, so in ⋂H",
					By(set_basic.InInters, subfields, SubfieldZero)),
				Case(
					"and so does one",
					By(set_basic.InInters, subfields, SubfieldOne)),
				Case(
					"two points of ⋂H lie in every member of H, so their sum does",
					By(set_basic.InInters, subfields, SubfieldAdd)),
				Case(
					"so does the negation of a member",
					By(set_basic.InInters, subfields, SubfieldNeg)),
				Case(
					"and the product of two",
					By(set_basic.InInters, subfields, SubfieldMul)),
				Case(
					"and the inverse of a member",
					By(set_basic.InInters, subfields, SubfieldInv)),
			))
		}),
})}

// SubfieldTrans — a subfield of a subfield is a subfield: the inclusions
// compose, and restriction keeps the operations, so l's closure conditions
// are the same in F.
var SubfieldTrans = subfieldTransThm{family.Add(registry.ProofEntry{
	Name: "SubfieldTrans",
	Key:  "prop_997f5abaa18c347f",
	Build: family.Theorem(Statement{
		Binders:    "∀F:field_ops(A). ∀k l:set(A).",
		Hypotheses: []string{"subfield(F, k)", "subfield(restrict_field(F, k), l)"},
		Conclusion: "subfield(F, l)",
	},
		func(a *Argument, _ *Expr[FieldOps[A]], k, l *Expr[Set[A]], hypotheses Fact) {
			parts := a.Conjuncts(
				hypotheses,
				"k is a subfield of F.carrier",
				"l is a subfield of the restriction to k")
			// Unfolded, the restriction's conditions on l read with F's own
			// components, all seven at once; each law would read one of them
			// at restrict_field(F, k).
			inherited := a.Unfolded(parts[1], SubfieldDef)
			lInC := a.Have(
				"l lies in k, which lies in F.carrier",
				"l ⊆ F.carrier",
				By(inherited, SubfieldSubset.Read(parts[0]), set_order.SubsetTrans))
			a.Show(
				"and l's closure conditions in the restriction are its conditions in F",
				Simp(Fwd(SubfieldDef)),
				By(lInC, inherited))
		}),
})}

// SubfieldRestrict — a subfield inside k is a subfield of the restriction
// to k: the carrier inclusion changes, while its closure conditions stay
// the same.
var SubfieldRestrict = subfieldRestrictThm{family.Add(registry.ProofEntry{
	Name: "SubfieldRestrict",
	Key:  "prop_4f95596a0534ab50",
	Reading: "l ⊆ k is load-bearing: two subfields of F.carrier need not be nested, " +
		"and subfield(restrict_field(F, k), l) asks l ⊆ k. Nothing is asked of k beyond it.",
	Build: family.Theorem(Statement{
		Binders:    "∀F:field_ops(A). ∀k l:set(A).",
		Hypotheses: []string{"subfield(F, l)", "l ⊆ k"},
		Conclusion: "subfield(restrict_field(F, k), l)",
	},
		func(a *Argument, _ *Expr[FieldOps[A]], _, _ *Expr[Set[A]], inner, inclusion Fact) {
			conditions := a.Unfolded(inner, SubfieldDef)
			a.Show(
				"l lies in the new carrier k and keeps its closure under the same operations",
				Simp(Fwd(SubfieldDef), Fwd(RestrictFieldDef)),
				By(conditions, inclusion),
			)
		}),
})}

// ---------------------------------------------------------------------------
// Fraction fields
// ---------------------------------------------------------------------------

// FractionFieldCarrierDef — the carrier of R consists of fractions of S: S lies
// in it, and each of its members times some nonzero member of S lies in S.
var FractionFieldCarrierDef = fractionFieldCarrierDefThm{family.Define(registry.DefEntry{
	Name: "FractionFieldCarrierDef",
	Key:  "prop_3a74e7332f490847",
	Reading: "This is the fraction representation inside an already " +
		"supplied field; the field and subring laws are separate hypotheses.",
	Deps:  []registry.EntryLike{},
	Const: "fraction_field_carrier",
	Type:  "ring_ops(A) → set(A) → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:set(A). " +
			"    fraction_field_carrier(R, S) ⇔ " +
			"    S ⊆ R.carrier ∧ (∀z:A. z ∈ R.carrier ⇒ ∃a b:A. a ∈ S ∧ b ∈ S ∧ b ≠ R.zero ∧ R.mul(z, b) = a)",
	},
})}

// FractionFieldCarrierMono — a carrier made of the fractions of X is made of
// the fractions of every Y between X and the carrier: a member's fraction a/b
// with a, b in X has a, b in Y.
var FractionFieldCarrierMono = fractionFieldCarrierMonoThm{family.Add(registry.ProofEntry{
	Name: "FractionFieldCarrierMono",
	Key:  "prop_73323241f0692bd9",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀X Y:set(A).",
		Hypotheses: []string{
			"fraction_field_carrier(R, X)",
			"X ⊆ Y",
			"Y ⊆ R.carrier",
		},
		Conclusion: "fraction_field_carrier(R, Y)",
	}, func(a *Argument, R *Expr[RingOps[A]], X, Y *Expr[Set[A]], fractions, between, inR Fact) {
		a.Show(
			"each fraction of X is the same fraction of Y",
			Simp(Fwd(FractionFieldCarrierDef)),
			BySets(a.Unfolded(fractions, FractionFieldCarrierDef), between, inR))
	}),
})}
