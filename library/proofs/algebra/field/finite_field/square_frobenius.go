// square_frobenius.go — the power map of a square root of the size of a
// finite subfield: a Frobenius power of the ambient field, and an involution
// of the subfield.

package finite_field

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_prime"
	"github.com/euc-ai/xugo/library/registry"
)

// SquareFieldFrobenius — the s-th power map of a finite subfield of s * s
// elements is a ring endomorphism of the ambient field and an involution of
// the subfield. The subfield is a finite field of prime characteristic p with
// a power of p elements, so its square root s is a power of p and the map is
// a Frobenius power of the ambient field; on the subfield the map stays
// inside, and applied twice it raises to the size of the subfield, which
// fixes every element.
var SquareFieldFrobenius = squareFieldFrobeniusThm{family.Add(registry.ProofEntry{
	Name: "SquareFieldFrobenius",
	Key:  "prop_40acb37d236b500c",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀s:num.",
		Hypotheses: []string{
			"subfield(M, k)",
			"finite(k)",
			"card(k) = s * s",
		},
		Conclusion: "ring_homomorphism(field_ring(M), " +
			"    field_ring(M), " +
			"    frobenius_power(field_ring(M), s)) ∧ " +
			"(∀c:A. " +
			"    c ∈ k ⇒ " +
			"    monoid_pow(M.mul, M.one, c, s) ∈ k ∧ " +
			"    monoid_pow(M.mul, M.one, monoid_pow(M.mul, M.one, c, s), s) = c)",
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		k *Expr[Set[A]],
		s *Expr[Nat],
		subfield, finite, size Fact,
	) {
		ambient := a.TermAs[RingOps[A]]("field_ring(M)")
		restricted := a.Have(
			"k with M's operations is a field",
			"field_on(restrict_field(M, k))",
			By(subfield, field.SubfieldFieldOn.Read(M).At(k)))
		multiplicative := comm_ring.MulMonoidOn.Read(field.RingOn.Read(restricted))
		p, restrictedPrime := a.ObtainAs[Nat](
			"a finite field has a prime characteristic",
			"∃p:num. ring_prime_characteristic(field_ring(restrict_field(M, k)), p)",
			By(finite, FiniteFieldCharacteristic.Read(restricted)))
		prime := a.Have(
			"restriction keeps M's addition, zero and one, so p is the characteristic of M too",
			"ring_prime_characteristic(field_ring(M), p)",
			By(
				restrictedPrime,
				PrimeCharacteristicDef.At(a.TermAs[RingOps[A]]("field_ring(restrict_field(M, k))"), p),
				PrimeCharacteristicDef.At(ambient, p)))
		e, sizePower := a.ObtainAs[Nat](
			"the finite field k has a power of p elements",
			"∃e:num. s * s = p ^ e",
			By(Normalized, finite, size, restrictedPrime, FiniteFieldSizePower.Read(restricted).AsFact().At(p)))
		n, rootPower := a.ObtainAs[Nat](
			"so its square root s is a power of p",
			"∃n:num. s = p ^ n",
			By(
				sizePower,
				prime,
				PrimeCharacteristicDef.At(ambient, p),
				nat_prime.PrimePowerSquareRoot.At(p, e, s)))
		a.Show(
			"the map is a Frobenius power of M, and an involution of k",
			SplitConj(
				Case(
					"a power of the characteristic is a ring endomorphism",
					By(Normalized, rootPower, prime, FrobeniusRingHomomorphism.Read(field.RingOn.Read(M)).At(p, n))),
				Case(
					"on k the map is an involution",
					Derive(func(b *Argument) {
						c := b.FixAs[A]("c")
						member := b.Assume()
						b.Show(
							"the field k is closed under powers, and the double "+
								"power raises c to the size of k, which fixes it",
							By(
								member,
								finite,
								size,
								comm_monoid.PowIn.Read(multiplicative).AsFact().At(c, s),
								comm_monoid.PowPowOn.Read(multiplicative).AsFact().At(c, s, s),
								FiniteFieldFixedByFrobenius.Read(restricted).AsFact().At(c)))
					}))))
	}),
})}
