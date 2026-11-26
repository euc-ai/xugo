package ideal_factorization

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_away"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/registry"
)

// MaximalPowerLocalization — extending a maximal-ideal power to an away
// ring and contracting to S gives the same power: denominator powers are
// units modulo the ideal power, so saturation adds no element of S.
var MaximalPowerLocalization = maximalPowerLocalizationThm{family.Add(registry.ProofEntry{
	Name: "MaximalPowerLocalization",
	Key:  "prop_41568b769d92e6f4",
	Reading: "The coordinate u need not be a unit in S, " +
		"only outside m; exponent zero gives the unit ideal.",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀S m:set(A). ∀u:A. ∀n:num.",
		Hypotheses: []string{"subring(field_ring(L), S)", "u ∈ S", "maximal_ideal(«R», m)", "u ∉ m"},
		Conclusion: "S ∩ ideal_span(«Localized», ideal_pow(«R», m, n)) = ideal_pow(«R», m, n)",
		Abbrev: Abbrev{
			{Name: "Localized", Text: "restrict_ring(field_ring(L), ring_away(field_ring(L), S, u))"},
		},
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		S, m *Expr[Set[A]],
		u *Expr[A],
		n *Expr[Nat],
		h Fact,
	) {
		parts := a.Conjuncts(
			h,
			"S is a subring",
			"u belongs to S",
			"m is maximal",
			"u lies outside m")
		subringS, uIn, maximal, outside := parts[0], parts[1], parts[2], parts[3]
		H, powerDef := a.LetAs[Set[A]]("H", "ideal_pow(«R», m, n)")
		_, awayDef := a.LetAs[Set[A]]("D", "ring_away(field_ring(L), S, u)")
		r := a.TermAs[RingOps[A]]("«R»")
		fieldRing := a.TermAs[RingOps[A]]("field_ring(L)")
		awayRing := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), D)")
		ringS := a.Have(
			"S is a commutative ring",
			"comm_ring_on(«R»)",
			By(subringS, comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(S)))
		idealM := a.Have(
			"m is a prime ideal",
			"ring_ideal(«R», m) ∧ prime_ideal(«R», m)",
			By(maximal, ring_ideal.MaximalIdealIdeal.At(r, m), ring_ideal.MaximalIsPrime.Read(ringS).At(m)))
		idealH := a.Have(
			"the maximal-ideal power is an ideal",
			"ring_ideal(«R», H)",
			Simp(Fwd(powerDef)),
			By(idealM, ring_ideal.IdealPowIdeal.Read(ringS).At(m, n)))
		carriers := a.Have(
			"the power lies in S and S lies in the field",
			"H ⊆ S ∧ S ⊆ L.carrier ∧ u ∈ L.carrier",
			BySets(
				idealH,
				subringS,
				uIn,
				ring_ideal.IdealSubset.At(r, H),
				comm_ring.SubringSubset.At(fieldRing, S)))
		saturation := a.Have(
			"the denominator saturation is an ideal containing the power",
			"ring_ideal(restrict_ring(field_ring(L), D), ring_away(field_ring(L), H, u)) ∧ "+
				"H ⊆ ring_away(field_ring(L), H, u)",
			Simp(Fwd(awayDef)),
			By(idealH, uIn, subringS, ring_away.RingAwayIdeal.Read(L).At(S, H, u)))
		extensionInside := a.Have(
			"leastness places the extended ideal inside denominator saturation",
			"ideal_span(restrict_ring(field_ring(L), D), H) ⊆ ring_away(field_ring(L), H, u)",
			By(
				saturation,
				ring_ideal.SpanLeast.At(awayRing, H, a.TermAs[Set[A]]("ring_away(field_ring(L), H, u)"))))
		contracted := a.Have(
			"saturation adds no members of S to a maximal-ideal power",
			"∀z:A. z ∈ S ∧ z ∈ ring_away(field_ring(L), H, u) ⇒ z ∈ H",
			Derive(func(b *Argument) {
				z := b.FixAs[A]("z")
				member := b.Assume()
				k, cleared := b.ObtainAs[Nat](
					"choose a denominator power clearing z into H",
					"∃k:num. monoid_pow(L.mul, L.one, u, k) * z ∈ H",
					BySets(member, ring_away.RingAwayDef.At(fieldRing, H, u)))
				powerU := b.TermAs[A]("monoid_pow(L.mul, L.one, u, k)")
				avoids := b.Have(
					"every denominator power belongs to S and stays outside m",
					"monoid_pow(L.mul, L.one, u, k) ∈ S ∧ monoid_pow(L.mul, L.one, u, k) ∉ m",
					By(
						outside,
						uIn,
						idealM,
						comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ringS)).AsFact().At(u, k),
						ring_ideal.PrimeIdealPow.Read(ringS).At(m, b.MemberOf[on.Any](u, uIn), k)))
				coeff, t, inverse := b.Obtain2As[A, A](
					"invert the denominator power modulo H",
					"∃c t:A. c ∈ S ∧ t ∈ H ∧ L.one = c * monoid_pow(L.mul, L.one, u, k) + t",
					Simp(Fwd(powerDef)),
					By(ringS, maximal, avoids, ring_ideal.MaximalPowerUnitModulo.At(r, m, powerU, n)))
				invParts := b.Conjuncts(
					inverse,
					"the coefficient belongs to S",
					"the remainder belongs to H",
					"the denominator has inverse modulo H")
				ambient := b.Have(
					"the inverse data and z belong to the ambient field",
					"c ∈ L.carrier ∧ t ∈ L.carrier ∧ z ∈ L.carrier",
					BySets(inverse, carriers, member))
				expansion := b.Have(
					"multiply the inverse identity by z",
					"z = c * (monoid_pow(L.mul, L.one, u, k) * z) + z * t",
					ByArith(L, ambient, carriers, Scaled(z, invParts[2])))
				b.Show(
					"both terms of the expansion belong to H",
					By(
						expansion,
						idealH,
						cleared,
						inverse,
						member,
						ring_ideal.IdealMul.At(r, H, coeff, b.TermAs[A]("monoid_pow(L.mul, L.one, u, k) * z")),
						ring_ideal.IdealMul.At(r, H, z, t),
						ring_ideal.IdealAdd.At(
							r, H, b.TermAs[A]("c * (monoid_pow(L.mul, L.one, u, k) * z)"), b.TermAs[A]("z * t"))))
			}))
		a.Show(
			"extension and contraction leave the maximal-ideal power unchanged",
			BySets(contracted, extensionInside, carriers, ring_ideal.SpanContains.At(awayRing, H)))
	}),
})}
