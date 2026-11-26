// principal.go — a Euclidean domain's axioms, and that its ideals are principal.

package euclidean_domain

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/principal_ideal_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The structure's axioms
// ---------------------------------------------------------------------------

// IntegralDomain — a Euclidean domain is an integral domain: the
// projection at which the domain chapter's laws, and through it the
// ring chapter's, apply.
var IntegralDomain = integralDomainThm{family.Add(registry.ProofEntry{
	Name:  "IntegralDomain",
	Key:   "prop_8efbe3dbcf7793c5",
	Build: EuclideanDomain.Axiom("integral_domain_on(R)"),
})}

// Division — the division algorithm: a member a of the carrier divided
// by a nonzero member b leaves a quotient q and a remainder r in the
// carrier with a = q * b + r, the remainder zero or of smaller measure
// than b.
var Division = divisionThm{family.Add(registry.ProofEntry{
	Name: "Division",
	Key:  "prop_5f67596b743a1931",
	Build: EuclideanDomain.Axiom(Statement{
		Binders: "∀a b:A.",
		Hypotheses: []string{
			"a ∈ R.carrier",
			"b ∈ R.carrier",
			"b ≠ R.zero",
		},
		Conclusion: "∃q r:A. q ∈ R.carrier ∧ r ∈ R.carrier ∧ a = q * b + r ∧ (r = R.zero ∨ δ(r) < δ(b))",
	}),
})}

// ---------------------------------------------------------------------------
// The ideals are principal
// ---------------------------------------------------------------------------

// MinimalMeasureGenerates — a nonzero member d of an ideal I whose
// measure is least among the nonzero members of I generates I. I holds
// every multiple of d; and a member x of I divided by d leaves the
// remainder x - q * d, which I holds, so it is not a nonzero member of
// smaller measure than d: it is zero, and x is the multiple d * q.
var MinimalMeasureGenerates = minimalMeasureGeneratesThm{family.Add(registry.ProofEntry{
	Name: "MinimalMeasureGenerates",
	Key:  "prop_62b6f6d139f24ab4",
	Build: EuclideanDomain.Law(Statement{
		Binders: "∀I:set(A). ∀d:A.",
		Hypotheses: []string{
			"ring_ideal(R, I)",
			"d ∈ I",
			"d ≠ R.zero",
			"∀x:A. x ∈ I ∧ x ≠ R.zero ⇒ δ(d) ≤ δ(x)",
		},
		Conclusion: "I = image(R.mul(d), R.carrier)",
	},
		func(
			a *Argument,
			euclid EuclideanDomainFact[on.R],
			I *Expr[Set[A]],
			d *Expr[A],
			ideal, dInI, nonzero, least Fact,
		) {
			ring := integral_domain.Ring.Read(IntegralDomain.Read(euclid))
			dIn := a.MemberOf[on.R](d, a.Have(
				"d lies in the carrier, as I does",
				"d ∈ R.carrier",
				By(ideal, dInI, ring_ideal.IdealSubset, set_basic.SubsetDef)))
			absorbed := a.Have(
				"I holds every multiple of d, absorbing d * r = r * d",
				"∀r:A. r ∈ R.carrier ⇒ d * r ∈ I",
				By(
					ideal,
					dInI,
					dIn,
					ring_ideal.IdealMul,
					comm_monoid.CommOn.Read(comm_ring.MulMonoidOn.Read(ring))))
			divisible := a.Have(
				"every member of I is a multiple of d",
				"∀x:A. x ∈ I ⇒ ∃q:A. q ∈ R.carrier ∧ x = d * q",
				Derive(func(b *Argument) {
					x := b.FixAs[A]()
					xInI := b.Assume()
					xIn := b.MemberOf[on.R](x, b.Have(
						"x lies in the carrier, as I does",
						"x ∈ R.carrier",
						By(ideal, xInI, ring_ideal.IdealSubset, set_basic.SubsetDef)))
					q, r, division := b.Unpack2As[A, A](
						GroupPremises(nonzero, Division.Read(euclid).At(xIn, dIn)), "q", "r")
					parts := b.Conjuncts(
						division,
						"the quotient q lies in the carrier",
						"the remainder r lies in the carrier",
						"x = q * d + r",
						"r is zero or of smaller measure than d")
					qIn, rIn, quotient, smaller := parts[0], parts[1], parts[2], parts[3]
					difference := b.Have(
						"the remainder is x less the multiple d * q",
						"r = x + -(d * q)",
						ByArith(ring, xIn, dIn, qIn, rIn, quotient))
					remainderIn := b.Have(
						"so I holds the remainder, holding x and d * q",
						"r ∈ I",
						difference.Rw(),
						By(ideal, xInI, absorbed.At(q), qIn, ring_ideal.IdealSub.Read(ring)))
					vanishes := b.Have(
						"the remainder is zero: a nonzero one in I would have measure at least δ(d)",
						"r = R.zero",
						By(
							smaller,
							least.At(r),
							remainderIn,
							nat_order.NotLessEq.At(b.TermAs[Nat]("δ(d)"), b.TermAs[Nat]("δ(r)"))))
					b.Take(q)
					b.Show(
						"with the remainder zero, x is q * d, the multiple d * q",
						ByArith(ring, xIn, dIn, qIn, rIn, quotient, vanishes))
				}))
			a.Show(
				"I is the set of multiples of d",
				BySets(absorbed, divisible))
		}),
})}

// PrincipalIdealDomain — every Euclidean domain is a principal ideal
// domain. An ideal holding only zero is generated by zero; an ideal
// holding a nonzero member has, by well-ordering, a nonzero member of
// least measure, and that member generates it.
var PrincipalIdealDomain = principalIdealDomainThm{family.Add(registry.ProofEntry{
	Name: "PrincipalIdealDomain",
	Key:  "prop_6a0e5600cd1393e3",
	Build: EuclideanDomain.Law("principal_ideal_domain(R)",
		func(a *Argument, euclid EuclideanDomainFact[on.R]) {
			domain := IntegralDomain.Read(euclid)
			ring := integral_domain.Ring.Read(domain)
			principal := a.Have(
				"every ideal is generated by one member",
				"∀I:set(A). ring_ideal(R, I) ⇒ ∃d:A. d ∈ R.carrier ∧ I = image(R.mul(d), R.carrier)",
				Derive(func(b *Argument) {
					b.FixAs[Set[A]]()
					ideal := b.Assume()
					b.Cases(b.Term("∃x:A. x ∈ I ∧ x ≠ R.zero"))
					b.When(
						"a nonzero member of least measure generates I",
						func(c *Argument, nonzeroMember Fact) {
							measured := c.TermAs[Set[Nat]]("λn:num. ∃x:A. x ∈ I ∧ x ≠ R.zero ∧ δ(x) = n")
							d, least := c.ObtainAs[A](
								"by well-ordering, some nonzero member d of I has the least measure",
								"∃d:A. d ∈ I ∧ d ≠ R.zero ∧ ∀x:A. x ∈ I ∧ x ≠ R.zero ⇒ δ(d) ≤ δ(x)",
								By(nonzeroMember, nat_order.WellOrdering.At(measured), nat_order.NotLessThan))
							c.Take(d)
							c.Show(
								"d lies in the carrier, as I does, and generates I",
								By(ideal, least, ring_ideal.IdealSubset, set_basic.SubsetDef, MinimalMeasureGenerates.Read(euclid)))
						})
					b.Otherwise(
						"I holds zero alone, and zero generates it",
						func(c *Argument, onlyZero Fact) {
							c.Take(c.TermAs[A]("R.zero"))
							c.Show(
								"zero lies in the carrier, and its multiples are zero, as every member of I is",
								BySets(ring, onlyZero, ideal, ring_ideal.IdealZero, comm_ring.ZeroIn, comm_ring.MulLeftZeroOn))
						})
				}))
			a.Show(
				"an integral domain whose ideals are principal",
				By(principal_ideal_domain.PrincipalIdealDomainDef, domain, principal))
		}),
})}
