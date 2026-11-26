// ring.go — ℤ[i] as a subring of ℂ, and an integral domain.

package gaussian_integer

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_construction"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// MemberIffIntegerParts — a complex number is a Gaussian integer exactly
// when its real and imaginary parts are integers: the parts of a + bi are
// the reals of the integers a and b, and a real that is an integer is the
// real of the integer it names.
var MemberIffIntegerParts = memberIffIntegerPartsThm{family.Add(registry.ProofEntry{
	Name: "MemberIffIntegerParts",
	Key:  "prop_f22c29146c49f21f",
	Build: family.Theorem(
		"∀z:complex. z ∈ gaussian_integers ⇔ integer(re(z)) ∧ integer(im(z))",
		func(a *Argument, z *Expr[Complex]) {
			a.Iff()
			a.Forward(
				"the parts of a + bi are the reals of the integers a and b",
				func(b *Argument, member Fact) {
					_, _, written := b.Unpack2(b.Unfolded(member, GaussianIntegersDef), "a", "b")
					b.Show(
						"each part is the real an integer stands for",
						written.Rw(),
						By(int_construction.RepresentativeIsInteger))
				})
			a.Backward(
				"integer parts are the reals of the integers they name",
				func(b *Argument, integral Fact) {
					named := b.Have(
						"z is the complex number at the integers its parts name",
						"∃a b:int. z = complex(real_of_int(a), real_of_int(b))",
						Witness(b.TermAs[Int]("int_of_real(re(z))")),
						Witness(b.TermAs[Int]("int_of_real(im(z))")),
						By(integral, int_construction.IntDef.Membership, complex_field.ComplexEq))
					b.Show(
						"so z lies in ℤ[i]",
						Unfold(GaussianIntegersDef),
						By(named))
				})
		}),
})}

// GaussianSubring — the Gaussian integers form a subring of ℂ: zero and
// one have integer parts, and the parts of a sum, a negation and a product
// are sums, negations and products of the parts of the operands, which the
// integers are closed under.
var GaussianSubring = gaussianSubringThm{family.Add(registry.ProofEntry{
	Name: "GaussianSubring",
	Key:  "prop_bb33ed17b11d34a9",
	Build: family.Theorem("subring(complex_ring, gaussian_integers)", func(a *Argument) {
		a.Do(Unfold(comm_ring.SubringDef), SplitConjAll(
			Case(
				"ℤ[i] lies in ℂ's carrier, the whole type",
				By(set_order.SubsetUniv)),
			Case(
				"zero is 0 + 0i",
				By(MemberIffIntegerParts, complex_field.PartsOfReal, int_construction.IntegerOfNum)),
			Case(
				"one is 1 + 0i",
				By(MemberIffIntegerParts, complex_field.PartsOfReal, int_construction.IntegerOfNum)),
			Case(
				"the parts of a sum are the sums of the parts",
				Simp(Fwd(MemberIffIntegerParts), Fwd(complex_field.ComplexAddDef)),
				By(int_construction.IntegerClosedUnderAdd)),
			Case(
				"the parts of a negation are the negated parts",
				Simp(Fwd(MemberIffIntegerParts), Fwd(complex_field.ComplexNegDef)),
				By(int_construction.IntegerClosedUnderNeg)),
			Case(
				"the real part of a product is a difference of products of parts, the imaginary part a sum",
				Simp(Fwd(MemberIffIntegerParts), Fwd(complex_field.ComplexMulDef), Fwd(real_ring.RealSubDef)),
				By(
					int_construction.IntegerClosedUnderMul,
					int_construction.IntegerClosedUnderAdd,
					int_construction.IntegerClosedUnderNeg)),
		))
	}),
})}

// IntegralDomain — the Gaussian integers, with ℂ's operations, are an
// integral domain: they form a subring of ℂ, which is an integral domain,
// and a subring of an integral domain is one.
var IntegralDomain = integralDomainThm{family.Add(registry.ProofEntry{
	Name: "IntegralDomain",
	Key:  "prop_62c3c6007a09c9b",
	Build: family.Theorem("integral_domain_on(gaussian_ring)", func(a *Argument) {
		a.Show(
			"the ring of ℂ restricted to ℤ[i], a subring of the domain ℂ",
			Unfold(GaussianRingDef),
			By(
				GaussianSubring,
				integral_domain.SubringOfDomainIsDomain.Read(complex_field.ComplexIntegralDomain).
					At(a.TermAs[Set[Complex]]("gaussian_integers"))))
	}),
})}
