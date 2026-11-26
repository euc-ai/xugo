// integral_domain.go — the chapter: an integral domain on a set, the
// commutative ring whose one is not its zero and in which a product
// vanishes only when a factor does.

package integral_domain

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The structure and its axioms
// ---------------------------------------------------------------------------

// IntegralDomainOn — `integral_domain_on(R)`: a commutative ring on
// R.carrier whose one is not its zero, and in which a product of two
// members is zero only when one of them is. The first conjunct supplies
// the ring laws through Ring.
var IntegralDomainOn = integralDomainOnThm{family.DefineStructure(registry.DefEntry{
	Name:     "IntegralDomainOn",
	Key:      "prop_1b3998e331ecbb5b",
	Const:    "integral_domain_on",
	Subject:  "R",
	Type:     "ring_ops(A) → bool",
	Implicit: []string{},
	Equations: []string{
		"∀R:ring_ops(A). " +
			"    integral_domain_on(R) ⇔ " +
			"    comm_ring_on(R) ∧ " +
			"    R.one ≠ R.zero ∧ " +
			"    (∀x y:A. x ∈ R.carrier ∧ y ∈ R.carrier ∧ R.mul(x, y) = R.zero ⇒ x = R.zero ∨ y = R.zero)",
	},
	Symbols: map[string]string{},
})}

// Ring — an integral domain is a commutative ring on its set: the
// projection at which the ring chapter's carrier laws apply.
var Ring = ringThm{family.Add(registry.ProofEntry{
	Name:  "Ring",
	Key:   "prop_55ca7dca03851412",
	Build: IntegralDomainOn.Axiom("comm_ring_on(R)"),
})}

// OneNotZero — a domain has at least two elements.
var OneNotZero = oneNotZeroThm{family.Add(registry.ProofEntry{
	Name:  "OneNotZero",
	Key:   "prop_a0abdacbc6767b5a",
	Build: IntegralDomainOn.Axiom("R.one ≠ R.zero"),
})}

// NoZeroDivisors — a vanishing product of members has a vanishing factor.
var NoZeroDivisors = noZeroDivisorsThm{family.Add(registry.ProofEntry{
	Name: "NoZeroDivisors",
	Key:  "prop_ae2080b09411abc8",
	Build: IntegralDomainOn.Axiom(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ R.carrier",
			"y ∈ R.carrier",
			"x * y = R.zero",
		},
		Conclusion: "x = R.zero ∨ y = R.zero",
	}),
})}

// ---------------------------------------------------------------------------
// What the axiom gives
// ---------------------------------------------------------------------------

// MulCancelLeft — a nonzero member cancels from the left: the two
// products agree exactly when the factors do. Equal products put x times
// the difference y - z at zero, and the domain axiom, x being nonzero,
// puts the difference there.
var MulCancelLeft = mulCancelLeftThm{family.Add(registry.ProofEntry{
	Name: "MulCancelLeft",
	Key:  "prop_6de396a168e62add",
	Reading: "x ≠ R.zero carries the forward direction: at x = R.zero both products are R.zero " +
		"whatever y and z are. The memberships put y - z in R.carrier, where the domain axiom applies.",
	Build: IntegralDomainOn.Law(Statement{
		Binders: "∀x y z:A.",
		Hypotheses: []string{
			"x ∈ R.carrier",
			"y ∈ R.carrier",
			"z ∈ R.carrier",
			"x ≠ R.zero",
		},
		Conclusion: "x * y = x * z ⇔ y = z",
	},
		func(a *Argument, domain IntegralDomainFact[on.R], x, y, z *Member[A, on.R], nonzero Fact) {
			ring := Ring.Read(domain)
			a.Iff()
			a.Forward(
				"equal products make x times the difference y - z vanish, so the difference does",
				func(b *Argument, equal Fact) {
					product := b.Have(
						"x (y - z) = x y - x z, which the equal products make zero",
						"x * (y - z) = R.zero",
						ByArith(ring, x, y, z, equal))
					difference := comm_ring.SubIn.Read(ring).At(y, z)
					vanishes := b.Have(
						"x is not zero, so the factor y - z is",
						"y - z = R.zero",
						By(NoZeroDivisors.Read(domain).At(x, difference), product, nonzero))
					b.Show(
						"y = z, adding z back to the vanishing difference",
						CalcEq(
							Leg(
								b.TermAs[A]("R.zero + z"),
								"y is the difference y - z, which is zero, plus z",
								ByArith(ring, y, z, vanishes)),
							FinalLeg(
								"zero is the identity of the sum",
								ByArith(ring, z)),
						))
				})
			a.Backward(
				"equal factors give equal products",
				func(b *Argument, equal Fact) {
					b.Show(
						"multiply the equation y = z by x",
						By(Normalized, equal))
				})
		}),
})}

// MulCancelRight — a nonzero member cancels from the right: commute
// both products and apply left cancellation.
var MulCancelRight = mulCancelRightThm{family.Add(registry.ProofEntry{
	Name: "MulCancelRight",
	Key:  "prop_dc21b02e5b2e4ae8",
	Build: IntegralDomainOn.Law(Statement{
		Binders: "∀x y z:A.",
		Hypotheses: []string{
			"x ∈ R.carrier",
			"y ∈ R.carrier",
			"z ∈ R.carrier",
			"x ≠ R.zero",
		},
		Conclusion: "y * x = z * x ⇔ y = z",
	},
		func(a *Argument, domain IntegralDomainFact[on.R], x, y, z *Member[A, on.R], nonzero Fact) {
			multiplicative := comm_ring.MulMonoidOn.Read(Ring.Read(domain))
			a.Show(
				"commuting each product puts x on the left, where it cancels",
				Simp(Fwd(comm_monoid.CommOn.Read(multiplicative))),
				By(nonzero, MulCancelLeft.Read(domain).At(x, y, z)))
		}),
})}

// FieldIntegralDomain — a field on a set is an integral domain on it:
// the domain's three conditions are the field's ring, one ≠ zero, and
// the forward direction of field.MulEqZeroOn.
var FieldIntegralDomain = fieldIntegralDomainThm{family.Add(registry.ProofEntry{
	Name: "FieldIntegralDomain",
	Key:  "prop_b5f6e05d06354972",
	Reading: "The domain is the one on the field's own ring components and its set c: a " +
		"field on c is a domain on c as it stands, with no subring or embedding between them.",
	Build: field.FieldOn.Law("integral_domain_on(field_ring(F))",
		func(a *Argument, fieldOn field.FieldFact[on.F]) {
			a.Do(Unfold(IntegralDomainOn), SplitConjAll(
				Case(
					"the field's ring on c is the domain's ring",
					By(field.RingOn.Read(fieldOn))),
				Case(
					"one is not zero, in the field",
					By(field.OneNotZeroOn.Read(fieldOn))),
				Case(
					"a vanishing product of members has a vanishing factor, since a field has no zero divisors",
					By(field.MulEqZeroOn.Read(fieldOn))),
			))
		}),
})}

// SubringOfFieldDomain — a subring of a field is an integral domain under the field's
// operations: its one is the field's and a product of its members vanishes, in the
// field, only at a vanishing factor.
var SubringOfFieldDomain = subringOfFieldDomainThm{family.Add(registry.ProofEntry{
	Name: "SubringOfFieldDomain",
	Key:  "prop_bdf9372ea8682f72",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀S:set(A).",
		Hypotheses: []string{"subring(field_ring(L), S)"},
		Conclusion: "integral_domain_on(restrict_ring(field_ring(L), S))",
	}, func(a *Argument, L field.FieldFact[on.L], S *Expr[Set[A]], sub Fact) {
		ring := field.RingOn.Read(L)
		a.Show(
			"a ring inside L, where one is not zero and a product vanishes only at a factor",
			By(
				a.Have(
					"S is a ring under the operations of L",
					"comm_ring_on(restrict_ring(field_ring(L), S))",
					By(sub, comm_ring.SubringRingOn.Read(ring).At(S))),
				a.Have(
					"a product of members of S vanishes only at a vanishing factor",
					"∀x y:A. x ∈ S ∧ y ∈ S ∧ x * y = L.zero ⇒ x = L.zero ∨ y = L.zero",
					BySets(
						sub,
						comm_ring.SubringSubset.At(a.TermAs[RingOps[A]]("field_ring(L)"), S),
						field.MulEqZeroOn.Read(L))),
				field.OneNotZeroOn.Read(L),
				IntegralDomainOn))
	}),
})}

// SubringOfDomainIsDomain — a subring of an integral domain is an integral
// domain under the domain's operations: it is a ring on its own set, its
// one and zero are the domain's, and a product of its members vanishes, in
// the domain, only at a vanishing factor.
var SubringOfDomainIsDomain = subringOfDomainIsDomainThm{family.Add(registry.ProofEntry{
	Name: "SubringOfDomainIsDomain",
	Key:  "prop_db0151ad4baee93d",
	Build: family.Theorem(Statement{
		Binders:    "∀R:integral_domain_on(A). ∀S:set(A).",
		Hypotheses: []string{"subring(R, S)"},
		Conclusion: "integral_domain_on(restrict_ring(R, S))",
	}, func(a *Argument, R IntegralDomainFact[on.R], S *Expr[Set[A]], sub Fact) {
		products := a.Have(
			"a product of members of S vanishes only at a vanishing factor",
			"∀x y:A. x ∈ S ∧ y ∈ S ∧ x * y = R.zero ⇒ x = R.zero ∨ y = R.zero",
			BySets(sub, comm_ring.SubringSubset.At(a.TermAs[RingOps[A]]("R"), S), NoZeroDivisors.Read(R)))
		a.Show(
			"S is a ring on its own set, its one is not its zero, and a product vanishes only at a factor",
			By(
				sub,
				comm_ring.SubringRingOn.Read(Ring.Read(R)).At(S),
				products,
				OneNotZero.Read(R),
				IntegralDomainOn))
	}),
})}

// FiniteDomainIsField — every nonzero element of a finite integral domain has
// an inverse in its carrier: multiplication by that element is a carrier
// injection, hence a surjection, so one has a preimage.
var FiniteDomainIsField = finiteDomainIsFieldThm{family.Add(registry.ProofEntry{
	Name: "FiniteDomainIsField",
	Key:  "prop_18324025d69177f3",
	Build: family.Theorem(Statement{
		Binders:    "∀c:integral_domain_on(A). ∀a:A.",
		Hypotheses: []string{"finite(c.carrier)", "a ∈ c.carrier", "a ≠ c.zero"},
		Conclusion: "∃b:A. b ∈ c.carrier ∧ a * b = c.one",
	}, func(arg *Argument, c IntegralDomainFact[on.C], finite Fact, a *Expr[A], hypotheses Fact) {
		parts := arg.Conjuncts(
			hypotheses,
			"a lies in the carrier",
			"a is nonzero")
		am := arg.MemberOf[on.C](a, parts[0])
		nonzero := parts[1]
		ring := Ring.Read(c)
		carrier := arg.TermAs[Set[A]]("c.carrier")
		multiply := arg.TermAs[Fun[A, A]]("c.mul(a)")
		maps := arg.Have(
			"multiplication by a preserves the carrier",
			"image(c.mul(a), c.carrier) ⊆ c.carrier",
			By(comm_ring.MulIn.Read(ring), am, set_image.ImageSubsetIff.At(multiply, carrier, carrier)))
		injective := arg.Have(
			"nonzero multiplication is injective on the carrier",
			"injective_on(c.carrier, c.mul(a))",
			Unfold(functions.InjectiveOnDef),
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				y := b.FixAs[A]("y")
				data := b.Assume()
				factors := b.Conjuncts(
					data,
					"x lies in the carrier",
					"y lies in the carrier",
					"the products agree")
				xm := b.MemberOf[on.C](x, factors[0])
				ym := b.MemberOf[on.C](y, factors[1])
				b.Show(
					"cancel the nonzero carrier element a",
					By(nonzero, factors[2], MulCancelLeft.Read(c).At(am, xm, ym)))
			}))
		onto := arg.Have(
			"multiplication by a is surjective on the finite carrier",
			"∀y:A. y ∈ c.carrier ⇒ ∃x:A. x ∈ c.carrier ∧ a * x = y",
			By(finite, maps, injective, cardinality.SurjectiveIffInjective.At(carrier, multiply)))
		oneIn := arg.Have(
			"one lies in the carrier",
			"c.one ∈ c.carrier",
			By(comm_ring.OneIn.Read(ring)))
		one := arg.MemberOf[on.C](arg.TermAs[A]("c.one"), oneIn)
		b, preimage := arg.UnpackAs[A](GroupPremises(oneIn, onto.At(one)), "b")
		inverse := arg.Conjuncts(
			preimage,
			"b lies in the carrier",
			"a times b is one")
		bm := arg.MemberOf[on.C](b, inverse[0])
		arg.Take(bm)
		arg.Show(
			"the preimage of one is the required inverse",
			By(bm, inverse[1]))
	}),
})}
