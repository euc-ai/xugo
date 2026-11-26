// subring.go — subrings of a ring on a set: the subsets the ring's
// operations never leave, each a ring on its own set.

package comm_ring

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Subrings
// ---------------------------------------------------------------------------

// SubringDef — a subset of R's carrier holding zero and one and closed
// under addition, negation and multiplication.
var SubringDef = subringDefThm{family.Define(registry.DefEntry{
	Name:  "SubringDef",
	Key:   "prop_8df50f1478d5e716",
	Const: "subring", Type: "ring_ops(A) → set(A) → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:set(A). " +
			"    subring(R, S) ⇔ " +
			"    S ⊆ R.carrier ∧ " +
			"    R.zero ∈ S ∧ " +
			"    R.one ∈ S ∧ " +
			"    (∀x y:A. x ∈ S ∧ y ∈ S ⇒ R.add(x, y) ∈ S) ∧ " +
			"    (∀x:A. x ∈ S ⇒ R.neg(x) ∈ S) ∧ " +
			"    (∀x y:A. x ∈ S ∧ y ∈ S ⇒ R.mul(x, y) ∈ S)",
	},
})}

// The conditions, each a law a proof cites instead of unfolding the
// definition. They ask nothing of the ring, so each spells the
// components.

// SubringSubset — a subring lies in the carrier.
var SubringSubset = subringSubsetThm{family.Add(registry.ProofEntry{
	Name:  "SubringSubset",
	Key:   "prop_916ae26899c1841c",
	Build: SubringDef.Entry().Conjunct("S ⊆ R.carrier"),
})}

// SubringZero — a subring holds zero.
var SubringZero = subringZeroThm{family.Add(registry.ProofEntry{
	Name:  "SubringZero",
	Key:   "prop_e41bb9266134b60b",
	Build: SubringDef.Entry().Conjunct("R.zero ∈ S"),
})}

// SubringOne — and one.
var SubringOne = subringOneThm{family.Add(registry.ProofEntry{
	Name:  "SubringOne",
	Key:   "prop_d0a71b9c81c89018",
	Build: SubringDef.Entry().Conjunct("R.one ∈ S"),
})}

// SubringAdd — a subring holds the sum of two of its members.
var SubringAdd = subringAddThm{family.Add(registry.ProofEntry{
	Name: "SubringAdd",
	Key:  "prop_da5468853c4cc0f8",
	Build: SubringDef.Entry().Conjunct(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ S",
			"y ∈ S",
		},
		Conclusion: "R.add(x, y) ∈ S",
	}),
})}

// SubringNeg — the negation of a member.
var SubringNeg = subringNegThm{family.Add(registry.ProofEntry{
	Name: "SubringNeg",
	Key:  "prop_2d7caaaf29f400eb",
	Build: SubringDef.Entry().Conjunct(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ S",
		},
		Conclusion: "R.neg(x) ∈ S",
	}),
})}

// SubringMul — and the product of two members.
var SubringMul = subringMulThm{family.Add(registry.ProofEntry{
	Name: "SubringMul",
	Key:  "prop_83ae580c66f3e57d",
	Build: SubringDef.Entry().Conjunct(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ S",
			"y ∈ S",
		},
		Conclusion: "R.mul(x, y) ∈ S",
	}),
})}

// SubringRestrict — a subring of R lying in T is a subring of R restricted
// to T: restriction keeps R's operations, so the zero, the one and the
// closure conditions read as they did, and T is the carrier S lies in.
var SubringRestrict = subringRestrictThm{family.Add(registry.ProofEntry{
	Name: "SubringRestrict",
	Key:  "prop_95ec1b1da5804add",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀S T:set(A).",
		Hypotheses: []string{
			"subring(R, S)",
			"S ⊆ T",
		},
		Conclusion: "subring(restrict_ring(R, T), S)",
	},
		func(a *Argument, R *Expr[RingOps[A]], S, T *Expr[Set[A]], subring, inT Fact) {
			a.Show(
				"the conditions on S are those of R, and S lies in the carrier T",
				By(
					subring,
					inT,
					SubringDef.At(R, S),
					SubringDef.At(a.TermAs[RingOps[A]]("restrict_ring(R, T)"), S)))
		}),
})}

// ---------------------------------------------------------------------------
// A subring is a ring on its set
// ---------------------------------------------------------------------------

// SubringRingOn — under a ring on R.carrier, a subring is exactly a subset
// of R.carrier that is a ring on its own set with the same operations:
// the closure conditions are the subring's, and every axiom on S is an
// instance of the ring's on R.carrier (ClosedSubsetRingOn); a ring on S
// holds zero and one and is closed under its operations by its own
// closure laws.
var SubringRingOn = subringRingOnThm{family.Add(registry.ProofEntry{
	Name: "SubringRingOn",
	Key:  "prop_145ebb7855923f8",
	Reading: "The conjunct S ⊆ R.carrier is load-bearing in ⇐: " +
		"comm_ring_on(restrict_ring(R, S)) alone does not put S inside the ambient carrier.",
	Build: CommRingOn.Law("∀S:set(A). "+
		"    subring(R, S) ⇔ S ⊆ R.carrier ∧ comm_ring_on(restrict_ring(R, S))",
		func(a *Argument, ring CommRingFact[on.R], S *Expr[Set[A]]) {
			a.Iff()
			a.Forward(
				"S lies in R.carrier, holds zero and one and is closed under "+
					"the three operations, so the ring's laws restrict to it",
				func(b *Argument, subring Fact) {
					closed := b.Unfolded(subring, SubringDef)
					b.Show(
						"S lies in R.carrier, and is a ring on its own set",
						By(closed, ClosedSubsetRingOn.Read(ring).At(S)))
				})
			a.Backward(
				"a ring on S holds zero and one and is closed under its operations",
				func(b *Argument, given Fact) {
					parts := b.Conjuncts(
						given,
						"S lies in R.carrier",
						"S is a ring on its own set")
					b.Do(Unfold(SubringDef), SplitConjAll(
						Case(
							"S lies in R.carrier",
							By(parts[0])),
						Case(
							"S holds zero",
							By(ZeroIn.Read(parts[1]))),
						Case(
							"and one",
							By(OneIn.Read(parts[1]))),
						Case(
							"S is closed under the sum",
							By(AddIn.Read(parts[1]))),
						Case(
							"under the negation",
							By(NegIn.Read(parts[1]))),
						Case(
							"and under the product",
							By(MulIn.Read(parts[1]))),
					))
				})
		}),
})}

// CarrierSubring — the carrier is a subring of its own ring: it lies in
// itself, and each closure condition is one of the ring's own.
var CarrierSubring = carrierSubringThm{family.Add(registry.ProofEntry{
	Name: "CarrierSubring",
	Key:  "prop_1ea4fee31d00ec4f",
	Build: CommRingOn.Law("subring(R, R.carrier)",
		func(a *Argument, ring CommRingFact[on.R]) {
			a.Do(Unfold(SubringDef), SplitConjAll(
				Case(
					"R.carrier lies in itself",
					By(set_order.SubsetRefl)),
				Case(
					"R.carrier holds zero",
					By(ZeroIn.Read(ring))),
				Case(
					"R.carrier holds one",
					By(OneIn.Read(ring))),
				Case(
					"R.carrier is closed under the sum",
					By(AddIn.Read(ring))),
				Case(
					"R.carrier is closed under the negation",
					By(NegIn.Read(ring))),
				Case(
					"R.carrier is closed under the product",
					By(MulIn.Read(ring))),
			))
		}),
})}
