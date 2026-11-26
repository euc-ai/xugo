package ideal_factorization

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/registry"
)

// ComaximalDecomposition — comaximal ideals write one as a member of each:
// the span of their union is the ring, which holds one, and that span is
// the set of element sums.
var ComaximalDecomposition = comaximalDecompositionThm{family.Add(registry.ProofEntry{
	Name: "ComaximalDecomposition",
	Key:  "prop_6bed5f9e42f04781",
	Build: family.Theorem(Statement{
		Binders: "∀c:comm_ring_on(A). ∀I J:set(A).",
		Hypotheses: []string{
			"ring_ideal(c, I)",
			"ring_ideal(c, J)",
			"ideal_span(c, I ∪ J) = c.carrier",
		},
		Conclusion: "∃u v:A. u ∈ I ∧ v ∈ J ∧ c.one = u + v",
	}, func(a *Argument, c comm_ring.CommRingFact[on.C], I, J *Expr[Set[A]], h Fact) {
		a.Show(
			"one lies in the span of the union, which is the set of element sums",
			BySets(comm_ring.OneIn.Read(c), h, ring_ideal.SpanUnionIdeals.Read(c).At(I, J)))
	}),
})}

// ComaximalIntersectionIsProduct — comaximal ideals meet in their product:
// write one as an element sum and multiply it by an element of the intersection.
var ComaximalIntersectionIsProduct = comaximalIntersectionIsProductThm{family.Add(registry.ProofEntry{
	Name: "ComaximalIntersectionIsProduct",
	Key:  "prop_6c9c1651e61c0395",
	Build: family.Theorem(Statement{
		Binders: "∀c:comm_ring_on(A). ∀I J:set(A).",
		Hypotheses: []string{
			"ring_ideal(c, I)",
			"ring_ideal(c, J)",
			"ideal_span(c, I ∪ J) = c.carrier",
		},
		Conclusion: "I ∩ J = ideal_mul(c, I, J)",
	}, func(a *Argument, c comm_ring.CommRingFact[on.C], I, J *Expr[Set[A]], h Fact) {
		parts := a.Conjuncts(
			h,
			"I is an ideal",
			"J is an ideal",
			"the union generates the ring")
		idealI, idealJ, comaximal := parts[0], parts[1], parts[2]
		ops := a.TermAs[RingOps[A]]("c")
		u, v, decomposition := a.Obtain2As[A, A](
			"decompose one into a member of each ideal",
			"∃u v:A. u ∈ I ∧ v ∈ J ∧ c.one = u + v",
			By(idealI, idealJ, comaximal, ComaximalDecomposition.Read(c).At(I, J)))
		pieces := a.Conjuncts(
			decomposition,
			"u belongs to I",
			"v belongs to J",
			"one is u plus v")
		inCarrier := a.Have(
			"both ideals lie in the carrier",
			"I ⊆ c.carrier ∧ J ⊆ c.carrier",
			By(idealI, idealJ, ring_ideal.IdealSubset))
		productIdeal := a.Have(
			"the product is an ideal",
			"ring_ideal(c, ideal_mul(c, I, J))",
			By(inCarrier, ring_ideal.IdealMulIdeal.Read(c).At(I, J)))
		productInside := a.Have(
			"product generators are absorbed by each factor",
			"ideal_mul(c, I, J) ⊆ I ∩ J",
			By(idealI, idealJ, ring_ideal.IdealMulSubsetInter.Read(c).At(I, J)))
		intersectionInside := a.Have(
			"an intersection element is a sum of two product generators",
			"∀z:A. z ∈ I ∧ z ∈ J ⇒ z ∈ ideal_mul(c, I, J)",
			Derive(func(b *Argument) {
				z := b.FixAs[A]("z")
				both := b.Assume()
				carriers := b.Have(
					"the decomposition and the intersection element lie in the ring",
					"u ∈ c.carrier ∧ v ∈ c.carrier ∧ z ∈ c.carrier",
					BySets(both, inCarrier, decomposition))
				carrierParts := b.Conjuncts(
					carriers,
					"u belongs to the ring",
					"v belongs to the ring",
					"z belongs to the ring")
				um := b.MemberOf[on.C](u, carrierParts[0])
				vm := b.MemberOf[on.C](v, carrierParts[1])
				zm := b.MemberOf[on.C](z, carrierParts[2])
				expansion := b.Have(
					"multiply the decomposition of one by z",
					"z = u * z + z * v",
					ByArith(c, um, vm, zm, Scaled(z, pieces[2])))
				b.Show(
					"the product ideal holds both generators and their sum",
					By(
						Normalized,
						expansion,
						productIdeal,
						both,
						decomposition,
						ring_ideal.IdealMulHolds.At(ops, I, J, u, z),
						ring_ideal.IdealMulHolds.At(ops, I, J, z, v),
						ring_ideal.IdealAdd.At(
							ops, b.TermAs[Set[A]]("ideal_mul(c, I, J)"), b.TermAs[A]("u * z"), b.TermAs[A]("z * v"))))
			}))
		a.Show(
			"the two inclusions identify the ideals",
			BySets(intersectionInside, productInside))
	}),
})}
