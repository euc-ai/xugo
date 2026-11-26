// ring_ideal.go — the chapter: ideals of a commutative ring on a set,
// the prime and the maximal ones, the ideal a set generates, the product
// of two ideals, and the units.
//
// Five parts, marked by banners: the definitions and the conditions
// they are made of; every ideal, and the two ideals every ring has; the
// ideal a set generates; the product of two ideals; prime and maximal
// ideals. Every notion takes the ring record R, whose carrier is
// R.carrier: `ring_ideal(R, I)`.

package ring_ideal

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/relations/order"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The definitions
// ---------------------------------------------------------------------------

// RingIdealDef — `ring_ideal(R, I)`: I is a subset of R.carrier holding
// R.zero, closed under R.add, and absorbing multiplication by every
// element of R.carrier. Closure under negation is a law (IdealNeg).
var RingIdealDef = ringIdealDefThm{family.Define(registry.DefEntry{
	Name:     "RingIdealDef",
	Key:      "prop_4063a68d9c61d008",
	Const:    "ring_ideal",
	Type:     "ring_ops(A) → set(A) → bool",
	Implicit: []string{},
	Equations: []string{
		"∀R:ring_ops(A). ∀I:set(A). " +
			"    ring_ideal(R, I) ⇔ " +
			"    I ⊆ R.carrier ∧ " +
			"    R.zero ∈ I ∧ " +
			"    (∀x y:A. x ∈ I ∧ y ∈ I ⇒ R.add(x, y) ∈ I) ∧ " +
			"    (∀r x:A. r ∈ R.carrier ∧ x ∈ I ⇒ R.mul(r, x) ∈ I)",
	},
})}

// PrimeIdealDef — `prime_ideal(R, p)`: a proper
// ideal holding a factor of each product it holds.
var PrimeIdealDef = primeIdealDefThm{family.Define(registry.DefEntry{
	Name:     "PrimeIdealDef",
	Key:      "prop_5b30db29e48ae9cb",
	Const:    "prime_ideal",
	Type:     "ring_ops(A) → set(A) → bool",
	Implicit: []string{},
	Equations: []string{
		"∀R:ring_ops(A). ∀p:set(A). " +
			"    prime_ideal(R, p) ⇔ " +
			"    ring_ideal(R, p) ∧ " +
			"    R.one ∉ p ∧ " +
			"    (∀x y:A. x ∈ R.carrier ∧ y ∈ R.carrier ∧ R.mul(x, y) ∈ p ⇒ x ∈ p ∨ y ∈ p)",
	},
	Deps: []registry.EntryLike{RingIdealDef},
})}

// MaximalIdealDef — `maximal_ideal(R, m)`: a proper
// ideal with no proper ideal strictly above it.
var MaximalIdealDef = maximalIdealDefThm{family.Define(registry.DefEntry{
	Name:     "MaximalIdealDef",
	Key:      "prop_66885a87360ae7a",
	Const:    "maximal_ideal",
	Type:     "ring_ops(A) → set(A) → bool",
	Implicit: []string{},
	Equations: []string{
		"∀R:ring_ops(A). ∀m:set(A). " +
			"    maximal_ideal(R, m) ⇔ " +
			"    ring_ideal(R, m) ∧ R.one ∉ m ∧ (∀J:set(A). ring_ideal(R, J) ∧ m ⊆ J ⇒ J = m ∨ R.one ∈ J)",
	},
	Deps: []registry.EntryLike{RingIdealDef},
})}

// IdealCoverDef — `ideal_cover(R, J, H)`: H covers J: H lies strictly
// above J with no ideal strictly between.
var IdealCoverDef = idealCoverDefThm{family.Define(registry.DefEntry{
	Name:     "IdealCoverDef",
	Key:      "prop_96381c637dd96622",
	Const:    "ideal_cover",
	Type:     "ring_ops(A) → set(A) → set(A) → bool",
	Implicit: []string{},
	Equations: []string{
		"∀R:ring_ops(A). ∀J H:set(A). " +
			"    ideal_cover(R, J, H) ⇔ " +
			"    ring_ideal(R, J) ∧ " +
			"    ring_ideal(R, H) ∧ " +
			"    J ⊆ H ∧ " +
			"    J ≠ H ∧ " +
			"    (∀K:set(A). ring_ideal(R, K) ∧ J ⊆ K ∧ K ⊆ H ⇒ K = J ∨ K = H)",
	},
	Deps: []registry.EntryLike{RingIdealDef},
})}

// IdealSpanDef — `ideal_span(R, S)`: the ideal S
// generates, the intersection of every ideal of c holding S. Under a
// ring every subset of c lies in the ideal c, so the family is never
// empty there.
var IdealSpanDef = idealSpanDefThm{family.Define(registry.DefEntry{
	Name:     "IdealSpanDef",
	Key:      "prop_7436c6888e8e7abd",
	Const:    "ideal_span",
	Type:     "ring_ops(A) → set(A) → set(A)",
	Implicit: []string{},
	Equations: []string{
		"∀R:ring_ops(A). ∀S:set(A). ideal_span(R, S) = ⋂{J:set(A) | ring_ideal(R, J) ∧ S ⊆ J}",
	},
	Deps: []registry.EntryLike{RingIdealDef},
})}

// IdealMulDef — `ideal_mul(R, I, J)`: the product of the
// ideals I and J of the ring on c, the ideal the products x * y with x in
// I and y in J generate.
var IdealMulDef = idealMulDefThm{family.Define(registry.DefEntry{
	Name:     "IdealMulDef",
	Key:      "prop_e1b18bc0a129cad4",
	Const:    "ideal_mul",
	Type:     "ring_ops(A) → set(A) → set(A) → set(A)",
	Implicit: []string{},
	Equations: []string{
		"∀R:ring_ops(A). ∀I:set(A). ∀J:set(A). " +
			"    ideal_mul(R, I, J) = ideal_span(R, {R.mul(x, y):A | x:A, y:A | x ∈ I ∧ y ∈ J})",
	},
	Reading: "Under a ring with I and J ideals the product lies in I ∩ J and " +
		"its members are the finite sums of products, which the span, taking no " +
		"finite sum, leaves to a theorem; ideal_mul(R, I, I) is the square I² of the " +
		"conormal module I/I². When a product leaves R.carrier no ideal of R.carrier " +
		"holds the products, and the span, the meet of no ideals, is the whole type.",
	Deps: []registry.EntryLike{IdealSpanDef},
})}

// IdealPowDef — `ideal_pow(R, I, n)`: the n-th power of I under the
// product of ideals, whose unit is the whole carrier.
var IdealPowDef = idealPowDefThm{family.Define(registry.DefEntry{
	Name:     "IdealPowDef",
	Key:      "prop_d858aabe0916ef59",
	Const:    "ideal_pow",
	Type:     "ring_ops(A) → set(A) → num → set(A)",
	Implicit: []string{},
	Equations: []string{
		"∀R:ring_ops(A). ∀I:set(A). ∀n:num. " +
			"    ideal_pow(R, I, n) = monoid_pow(λJ:set(A). λK:set(A). ideal_mul(R, J, K), R.carrier, I, n)",
	},
	Reading: "This is the power in the monoid IdealsCommMonoid gives under a " +
		"commutative ring; the zeroth power is R.carrier for arbitrary ring operations.",
	Deps: []registry.EntryLike{IdealMulDef},
})}

// RingUnitDef — `ring_unit(R, x)`: x is a member of c with an
// inverse in c.
var RingUnitDef = ringUnitDefThm{family.Define(registry.DefEntry{
	Name:     "RingUnitDef",
	Key:      "prop_72ef331bc835607a",
	Const:    "ring_unit",
	Type:     "ring_ops(A) → A → bool",
	Implicit: []string{},
	Equations: []string{
		"∀R:ring_ops(A). ∀x:A. " +
			"    ring_unit(R, x) ⇔ x ∈ R.carrier ∧ (∃y:A. y ∈ R.carrier ∧ R.mul(x, y) = R.one)",
	},
})}

// The conditions, each a law a proof cites instead of unfolding a
// definition and picking a conjunct. They ask nothing of the ring — each
// is one conjunct of its definition read off — so they are stated with
// no ring assumption in scope, and take the record R explicitly.

// IdealSubset — an ideal lies in the carrier.
var IdealSubset = idealSubsetThm{family.Add(registry.ProofEntry{
	Name:  "IdealSubset",
	Key:   "prop_ecfa4e22ff57c5e0",
	Build: RingIdealDef.Entry().Conjunct("I ⊆ R.carrier"),
})}

// IdealZero — an ideal holds zero.
var IdealZero = idealZeroThm{family.Add(registry.ProofEntry{
	Name:  "IdealZero",
	Key:   "prop_b3150eb0875928cd",
	Build: RingIdealDef.Entry().Conjunct("R.zero ∈ I"),
})}

// IdealAdd — an ideal is closed under the addition.
var IdealAdd = idealAddThm{family.Add(registry.ProofEntry{
	Name: "IdealAdd",
	Key:  "prop_1045d03d947d64ce",
	Build: RingIdealDef.Entry().Conjunct(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ I",
			"y ∈ I",
		},
		Conclusion: "R.add(x, y) ∈ I",
	}),
})}

// IdealMul — an ideal absorbs the multiplication by the carrier.
var IdealMul = idealMulThm{family.Add(registry.ProofEntry{
	Name: "IdealMul",
	Key:  "prop_38703579166dd5f3",
	Build: RingIdealDef.Entry().Conjunct(Statement{
		Binders: "∀r x:A.",
		Hypotheses: []string{
			"r ∈ R.carrier",
			"x ∈ I",
		},
		Conclusion: "R.mul(r, x) ∈ I",
	}),
})}

// PrimeIdealIdeal — a prime ideal is an ideal.
var PrimeIdealIdeal = primeIdealIdealThm{family.Add(registry.ProofEntry{
	Name:  "PrimeIdealIdeal",
	Key:   "prop_ea33a0fa12bccbf",
	Build: PrimeIdealDef.Entry().Conjunct("ring_ideal(R, p)"),
})}

// PrimeIdealProper — a prime ideal does not hold one.
var PrimeIdealProper = primeIdealProperThm{family.Add(registry.ProofEntry{
	Name:  "PrimeIdealProper",
	Key:   "prop_87be12d6e61b5c70",
	Build: PrimeIdealDef.Entry().Conjunct("R.one ∉ p"),
})}

// PrimeIdealPrime — a prime ideal holds a factor of each product of
// members of c it holds.
var PrimeIdealPrime = primeIdealPrimeThm{family.Add(registry.ProofEntry{
	Name: "PrimeIdealPrime",
	Key:  "prop_f6679f24391a9772",
	Build: PrimeIdealDef.Entry().Conjunct(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ R.carrier",
			"y ∈ R.carrier",
			"R.mul(x, y) ∈ p",
		},
		Conclusion: "x ∈ p ∨ y ∈ p",
	}),
})}

// PrimeIdealPow — a prime ideal holding a power of a member f of c holds
// f: by induction on the exponent, the zeroth power being one, which a
// prime ideal does not hold, and the power at suc(n) the product of f and
// the power at n, a factor of which the prime holds.
var PrimeIdealPow = primeIdealPowThm{family.Add(registry.ProofEntry{
	Name: "PrimeIdealPow",
	Key:  "prop_f8e949d9cc494959",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀p:set(A). ∀f:A. ∀n:num.",
		Hypotheses: []string{
			"prime_ideal(R, p)",
			"f ∈ R.carrier",
			"monoid_pow(R.mul, R.one, f, n) ∈ p",
		},
		Conclusion: "f ∈ p",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], p *Expr[Set[A]], f *Expr[A]) {
			a.Induct("n")
			a.Base(
				"f ^ 0 is one, which no prime ideal holds",
				Simp(Fwd(comm_monoid.MonoidPowDef)),
				By(PrimeIdealProper))
			a.Step(
				"f ^ suc(n) is f * f ^ n, both factors in c: p holds f, or holds f ^ n and so f",
				func(b *Argument, ih Fact) {
					b.Show(
						"a prime ideal holds a factor of the product",
						Simp(Fwd(comm_monoid.MonoidPowDef)),
						By(PrimeIdealPrime, comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ring)), ih))
				})
		}),
})}

// PrimeIdealMulSubset — a prime ideal holding the product of two ideals
// holds one of them: were x in I and y in J both outside p, x * y, which
// the product ideal holds, would lie in p, and so would x or y.
var PrimeIdealMulSubset = primeIdealMulSubsetThm{family.Add(registry.ProofEntry{
	Name: "PrimeIdealMulSubset",
	Key:  "prop_a934d10f0c561bd",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀p I J:set(A).",
		Hypotheses: []string{
			"prime_ideal(R, p)",
			"ring_ideal(R, I)",
			"ring_ideal(R, J)",
			"ideal_mul(R, I, J) ⊆ p",
		},
		Conclusion: "I ⊆ p ∨ J ⊆ p",
	}, func(a *Argument, R *Expr[module_record.RingOps[A]], p, I, J *Expr[Set[A]], h Fact) {
		parts := a.Conjuncts(
			h,
			"p is prime",
			"I is an ideal",
			"J is an ideal",
			"p holds the product")
		prime, idealI, idealJ, contained := parts[0], parts[1], parts[2], parts[3]
		neither := a.SupposeNot()
		x, xOut := a.ObtainAs[A](
			"a member of I outside p",
			"∃x:A. x ∈ I ∧ x ∉ p",
			BySets(neither))
		y, yOut := a.ObtainAs[A](
			"a member of J outside p",
			"∃y:A. y ∈ J ∧ y ∉ p",
			BySets(neither))
		generated := a.Have(
			"x * y lies in the product ideal",
			"R.mul(x, y) ∈ ideal_mul(R, I, J)",
			By(xOut, yOut, IdealMulHolds.At(R, I, J, x, y)))
		inCarrier := a.Have(
			"x and y lie in the carrier",
			"x ∈ R.carrier ∧ y ∈ R.carrier",
			BySets(xOut, yOut, IdealSubset.At(R, I), IdealSubset.At(R, J), idealI, idealJ))
		inP := a.Have(
			"so p holds x * y",
			"R.mul(x, y) ∈ p",
			BySets(generated, contained))
		a.Show(
			"p holds x or y, and holds neither",
			By(prime, inCarrier, inP, xOut, yOut, PrimeIdealPrime.At(R, p, x, y)))
	}),
})}

// MaximalIdealIdeal — a maximal ideal is an ideal.
var MaximalIdealIdeal = maximalIdealIdealThm{family.Add(registry.ProofEntry{
	Name:  "MaximalIdealIdeal",
	Key:   "prop_670eece16e4dbb92",
	Build: MaximalIdealDef.Entry().Conjunct("ring_ideal(R, m)"),
})}

// MaximalIdealProper — a maximal ideal does not hold one.
var MaximalIdealProper = maximalIdealProperThm{family.Add(registry.ProofEntry{
	Name:  "MaximalIdealProper",
	Key:   "prop_43b64156fb544990",
	Build: MaximalIdealDef.Entry().Conjunct("R.one ∉ m"),
})}

// MaximalIdealNotWhole — a maximal ideal of a subring is not all of it: the
// subring holds one and the ideal does not.
var MaximalIdealNotWhole = maximalIdealNotWholeThm{family.Add(registry.ProofEntry{
	Name: "MaximalIdealNotWhole",
	Key:  "prop_90a1301f11229e0c",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀S m:set(A).",
		Hypotheses: []string{
			"subring(R, S)",
			"maximal_ideal(restrict_ring(R, S), m)",
		},
		Conclusion: "m ≠ S",
	},
		func(a *Argument, R *Expr[module_record.RingOps[A]], S, m *Expr[Set[A]], subring, maximal Fact) {
			restricted := a.TermAs[module_record.RingOps[A]]("restrict_ring(R, S)")
			proper := a.Have(
				"S holds one and m does not",
				"R.one ∉ m ∧ R.one ∈ S",
				By(maximal, subring, MaximalIdealProper.At(restricted, m), comm_ring.SubringOne.At(R, S)))
			a.Show(
				"so they differ",
				BySets(proper))
		}),
})}

// MaximalIdealMaximal — an ideal above a maximal ideal is it, or holds
// one.
var MaximalIdealMaximal = maximalIdealMaximalThm{family.Add(registry.ProofEntry{
	Name: "MaximalIdealMaximal",
	Key:  "prop_30377792bc0606c5",
	Build: MaximalIdealDef.Entry().Conjunct(Statement{
		Binders: "∀J:set(A).",
		Hypotheses: []string{
			"ring_ideal(R, J)",
			"m ⊆ J",
		},
		Conclusion: "J = m ∨ R.one ∈ J",
	}),
})}

// MaximalIdealCover — the carrier covers a maximal ideal: it holds one
// and m does not, and an ideal above m is m, or holds one and so is the
// carrier.
var MaximalIdealCover = maximalIdealCoverThm{family.Add(registry.ProofEntry{
	Name: "MaximalIdealCover",
	Key:  "prop_bff06f2132720944",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀m:set(A).",
		Hypotheses: []string{
			"maximal_ideal(R, m)",
		},
		Conclusion: "ideal_cover(R, m, R.carrier)",
	},
		func(
			a *Argument,
			R *Expr[module_record.RingOps[A]],
			ring comm_ring.CommRingFact[on.R],
			m *Expr[Set[A]],
			maximal Fact,
		) {
			ideal := a.Have(
				"m is an ideal",
				"ring_ideal(R, m)",
				By(maximal, MaximalIdealIdeal))
			strict := a.Have(
				"the carrier holds one and m does not",
				"m ≠ R.carrier",
				By(Normalized, maximal, MaximalIdealProper, comm_ring.OneIn.Read(ring)))
			interval := a.Have(
				"an ideal above m is m, or holds one and is the carrier",
				"∀K:set(A). ring_ideal(R, K) ∧ m ⊆ K ∧ K ⊆ R.carrier ⇒ K = m ∨ K = R.carrier",
				By(maximal, MaximalIdealDef.At(R, m), IdealOneIff.Read(ring)))
			a.Show(
				"the carrier is an ideal strictly above m with nothing between",
				By(ideal, CarrierIdeal.Read(ring), IdealSubset.Read(ideal), strict, interval, IdealCoverDef))
		}),
})}

// ---------------------------------------------------------------------------
// Every ideal, and the two ideals every ring has
// ---------------------------------------------------------------------------

// IdealNeg — an ideal is closed under the negation: -x is -one * x, and
// -one lies in c.
var IdealNeg = idealNegThm{family.Add(registry.ProofEntry{
	Name: "IdealNeg",
	Key:  "prop_d1c49baab4cc4bea",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀I:set(A). ∀x:A.",
		Hypotheses: []string{
			"ring_ideal(R, I)",
			"x ∈ I",
		},
		Conclusion: "-x ∈ I",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], I *Expr[Set[A]], x *Expr[A], hypotheses Fact) {
			parts := a.Conjuncts(
				hypotheses,
				"I is an ideal",
				"x lies in I")
			ideal, member := parts[0], parts[1]
			inC := a.Have(
				"x lies in I, which lies in c",
				"x ∈ R.carrier",
				BySets(IdealSubset, ideal, member))
			negOne := a.Have(
				"-x is -one * x",
				"-R.one * x = -x",
				By(comm_ring.NegOneMulOn, ring, inC))
			a.Show(
				"absorption keeps -one * x in I, -one lying in c",
				negOne.RwRev(),
				By(IdealMul, ideal, member, ring, comm_ring.NegIn, comm_ring.OneIn))
		}),
})}

// IdealSub — an ideal is closed under the difference: it holds the
// negation of the second member, and the sum.
var IdealSub = idealSubThm{family.Add(registry.ProofEntry{
	Name: "IdealSub",
	Key:  "prop_8962b9d634992a",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀I:set(A). ∀x y:A.",
		Hypotheses: []string{
			"ring_ideal(R, I)",
			"x ∈ I",
			"y ∈ I",
		},
		Conclusion: "x + -y ∈ I",
	},
		func(
			a *Argument,
			ring comm_ring.CommRingFact[on.R],
			I *Expr[Set[A]],
			x, y *Expr[A],
			ideal, xIn, yIn Fact,
		) {
			a.Show(
				"I holds −y, and the sum of x and −y",
				By(ideal, xIn, yIn, IdealNeg.Read(ring).At(I, y), IdealAdd))
		}),
})}

// CarrierIdeal — the carrier is an ideal of itself.
var CarrierIdeal = carrierIdealThm{family.Add(registry.ProofEntry{
	Name: "CarrierIdeal",
	Key:  "prop_9de5997fd10af4df",
	Build: comm_ring.CommRingOn.Law("ring_ideal(R, R.carrier)",
		func(a *Argument, ring comm_ring.CommRingFact[on.R]) {
			a.Do(Unfold(RingIdealDef), SplitConjAll(
				Case(
					"c lies in itself",
					BySets()),
				Case(
					"zero lies in c",
					By(comm_ring.ZeroIn, ring)),
				Case(
					"c is closed under the sum",
					By(comm_ring.AddIn, ring)),
				Case(
					"c absorbs its own products",
					By(comm_ring.MulIn, ring)),
			))
		}),
})}

// ZeroIdeal — zero alone is an ideal: a member of {zero} is zero, so
// the sum it is closed under is zero + zero, the additive identity at
// zero, and the product it absorbs is r * zero, which is zero.
var ZeroIdeal = zeroIdealThm{family.Add(registry.ProofEntry{
	Name: "ZeroIdeal",
	Key:  "prop_39a3b0f4e687481",
	Build: comm_ring.CommRingOn.Law("ring_ideal(R, {R.zero})",
		func(a *Argument, ring comm_ring.CommRingFact[on.R]) {
			a.Do(Unfold(RingIdealDef), SplitConjAll(
				Case(
					"{zero} lies in c, as zero does",
					BySets(ring, comm_ring.ZeroIn)),
				Case(
					"zero lies in {zero}",
					BySets()),
				Case(
					"two members of {zero} sum to zero + zero, which is zero",
					BySets(comm_monoid.LeftIdentityOn.Read(comm_ring.AddMonoidOn.Read(ring)), comm_ring.ZeroIn)),
				Case(
					"a member of c times zero is zero",
					BySets(ring, comm_ring.MulRightZeroOn)),
			))
		}),
})}

// IdealOneIff — an ideal holds one exactly when it is the whole carrier.
var IdealOneIff = idealOneIffThm{family.Add(registry.ProofEntry{
	Name: "IdealOneIff",
	Key:  "prop_5b4593511ef804f5",
	Reading: "In the zero ring every ideal holds R.one = R.zero " +
		"and is R.carrier = {R.zero}, consistent with both directions.",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀I:set(A).",
		Hypotheses: []string{
			"ring_ideal(R, I)",
		},
		Conclusion: "R.one ∈ I ⇔ I = R.carrier",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], I *Expr[Set[A]], ideal Fact) {
			a.Iff()
			a.Forward(
				"every r of c is r * one, which absorption keeps in I",
				func(b *Argument, oneIn Fact) {
					absorbs := b.Have(
						"every member of c lies in I",
						"∀r:A. r ∈ R.carrier ⇒ r ∈ I",
						Derive(func(d *Argument) {
							d.FixAs[A]("r")
							inC := d.Assume()
							absorbed := d.Have(
								"r * one lies in I",
								"r * R.one ∈ I",
								By(IdealMul, ideal, inC, oneIn))
							d.Show(
								"and r * one is r",
								By(Normalized, absorbed, comm_monoid.RightIdentityOn.Read(comm_ring.MulMonoidOn.Read(ring)), inC))
						}))
					b.Show(
						"I lies in c, so I and c have the same members",
						BySets(IdealSubset, ideal, absorbs))
				})
			a.Backward(
				"I is c, which holds one",
				func(b *Argument, equal Fact) {
					b.Show(
						"one lies in c",
						equal.Rw(),
						By(comm_ring.OneIn, ring))
				})
		}),
})}

// OneUnit — one is a unit: it lies in c and is its own inverse.
var OneUnit = oneUnitThm{family.Add(registry.ProofEntry{
	Name: "OneUnit",
	Key:  "prop_f64a41095a04ae9b",
	Build: comm_ring.CommRingOn.Law("ring_unit(R, R.one)",
		func(a *Argument, ring comm_ring.CommRingFact[on.R]) {
			oneIn := comm_ring.OneIn.Read(ring)
			inverse := a.Have(
				"one is its own inverse in c",
				"∃w:A. w ∈ R.carrier ∧ R.one * w = R.one",
				Witness(a.Term("R.one")),
				By(oneIn, comm_monoid.LeftIdentityOn.Read(comm_ring.MulMonoidOn.Read(ring))))
			a.Show(
				"so one is a unit",
				By(RingUnitDef, inverse, oneIn))
		}),
})}

// RingUnitPow — a power of a unit is a unit: when y inverts x, yⁿ
// inverts xⁿ.
var RingUnitPow = ringUnitPowThm{family.Add(registry.ProofEntry{
	Name: "RingUnitPow",
	Key:  "prop_2632f5e702390cf5",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀x:A. ∀n:num.",
		Hypotheses: []string{
			"ring_unit(R, x)",
		},
		Conclusion: "ring_unit(R, monoid_pow(R.mul, R.one, x, n))",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], x *Expr[A], n *Expr[Nat], unit Fact) {
			parts := a.Conjuncts(
				a.Unfolded(unit, RingUnitDef),
				"x lies in the ring",
				"and has an inverse y there")
			xIn := parts[0]
			y, inverse := a.UnpackAs[A](parts[1], "y")
			monoid := comm_ring.MulMonoidOn.Read(ring)
			a.Do(Simp(Fwd(RingUnitDef)), SplitConj(
				Case(
					"the power belongs to the ring",
					By(xIn, comm_monoid.PowIn.Read(monoid))),
				Case(
					"the corresponding power of the inverse is an inverse",
					Derive(func(b *Argument) {
						b.Take(b.TermAs[A]("monoid_pow(R.mul, R.one, y, n)"))
						b.Do(SplitConj(
							Case(
								"the inverse power belongs to the ring",
								By(inverse, comm_monoid.PowIn.Read(monoid))),
							Case(
								"xⁿ · yⁿ = (x · y)ⁿ, a power of one",
								By(xIn, inverse, comm_monoid.PowInverseOn.Read(monoid).AsFact().At(x, y, n))),
						))
					})),
			))
		}),
})}

// RingUnitMul — a product of units is a unit: when u inverts x and v
// inverts y, u · v inverts x · y.
var RingUnitMul = ringUnitMulThm{family.Add(registry.ProofEntry{
	Name: "RingUnitMul",
	Key:  "prop_c9dc638519e6b738",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"ring_unit(R, x)",
			"ring_unit(R, y)",
		},
		Conclusion: "ring_unit(R, x * y)",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], x, y *Expr[A], units Fact) {
			parts := a.Conjuncts(
				a.Unfolded(units, RingUnitDef),
				"x lies in the ring",
				"and has an inverse u there",
				"y lies in the ring",
				"and has an inverse v there")
			xIn, yIn := parts[0], parts[2]
			_, inverseX := a.UnpackAs[A](parts[1], "u")
			_, inverseY := a.UnpackAs[A](parts[3], "v")
			a.Do(Simp(Fwd(RingUnitDef)), SplitConj(
				Case(
					"the product belongs to the ring",
					By(xIn, yIn, comm_ring.MulIn.Read(ring))),
				Case(
					"the product of the inverses is an inverse",
					Derive(func(b *Argument) {
						b.Take(b.TermAs[A]("u * v"))
						b.Do(SplitConj(
							Case(
								"the inverse product belongs to the ring",
								By(inverseX, inverseY, comm_ring.MulIn.Read(ring))),
							Case(
								"reorder the factors into the two inverse equations",
								CalcEq(
									Leg(
										b.TermAs[A]("(x * u) * (y * v)"),
										"pair each unit with its inverse",
										ByArith(ring, xIn, yIn, inverseX, inverseY)),
									FinalLeg(
										"both pairs are one",
										By(
											Normalized,
											inverseX,
											inverseY,
											comm_ring.OneIn.Read(ring),
											comm_monoid.LeftIdentityOn.Read(comm_ring.MulMonoidOn.Read(ring)))),
								)),
						))
					})),
			))
		}),
})}

// UnitPlusSquareZeroIsUnit — in a commutative ring, a unit u with inverse
// w plus a member j of square zero is a unit, with inverse w − w² j: the
// product is one by a ring computation from u w = R.one and j j = R.zero.
var UnitPlusSquareZeroIsUnit = unitPlusSquareZeroIsUnitThm{family.Add(registry.ProofEntry{
	Name: "UnitPlusSquareZeroIsUnit",
	Key:  "prop_73df0d23817aa5b9",
	Reading: "Only j * j = R.zero is read, not an ideal of square zero. The inverse w − w² j " +
		"is w(1 + w j)⁻¹ = w(1 − w j + w² j² − …), the series cut off at j² = R.zero. It is how " +
		"two lifts of one member meet in the localization of a square-zero extension: they differ " +
		"by a member of square zero, so one is a unit wherever the other is. No nontriviality is " +
		"assumed: in the zero ring R.one = R.zero, and the statement holds trivially. " +
		"Commutativity is used too: j * w cancels w * j, and j * (w * w * j) is w * w * (j * j).",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀u w j:A.",
		Hypotheses: []string{
			"u ∈ R.carrier",
			"w ∈ R.carrier",
			"j ∈ R.carrier",
			"u * w = R.one",
			"j * j = R.zero",
		},
		Conclusion: "ring_unit(R, u + j) ∧ (u + j) * (w - w * w * j) = R.one",
	},
		func(
			a *Argument,
			ring comm_ring.CommRingFact[on.R],
			u, w, j *Member[A, on.R],
			inverse, square Fact,
		) {
			wj, wSquared := a.TermAs[A]("w * j"), a.TermAs[A]("w * w")
			product := a.Have(
				"(u + j)(w − w² j) − one is (u w − one)(one − w j) − w² · j j, and u w = one, j j = zero",
				"(u + j) * (w - w * w * j) = R.one",
				ByArith(ring, u, w, j, Scaled(wj, inverse), Scaled(wSquared, square)))
			inverts := a.Have(
				"w − w² j lies in the ring and inverts u + j",
				"∃y:A. y ∈ R.carrier ∧ (u + j) * y = R.one",
				Witness(a.TermAs[A]("w - w * w * j")),
				By(ring, w, j, product, comm_ring.SubIn, comm_ring.MulIn))
			a.Show(
				"so u + j, a member of the ring, is a unit",
				By(RingUnitDef, ring, u, j, comm_ring.AddIn, inverts, product))
		}),
})}

// UnitNotInProperIdeal — a proper ideal holds no unit: with u and its
// inverse, absorption would put one in it.
var UnitNotInProperIdeal = unitNotInProperIdealThm{family.Add(registry.ProofEntry{
	Name: "UnitNotInProperIdeal",
	Key:  "prop_7d5115cafb4bb4e9",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀I:set(A). ∀u:A.",
		Hypotheses: []string{
			"ring_ideal(R, I)",
			"R.one ∉ I",
			"ring_unit(R, u)",
		},
		Conclusion: "u ∉ I",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], I *Expr[Set[A]], u *Expr[A], hypotheses Fact) {
			parts := a.Conjuncts(
				hypotheses,
				"I is an ideal",
				"I does not hold one",
				"u is a unit")
			ideal, proper, unit := parts[0], parts[1], parts[2]
			unitParts := a.Conjuncts(
				a.Unfolded(unit, RingUnitDef),
				"u lies in c",
				"and has an inverse in c")
			inC, invertible := unitParts[0], unitParts[1]
			_, inverse := a.Unpack(invertible, "v")
			commute := a.Have(
				"u * v is v * u",
				"u * v = v * u",
				By(comm_monoid.CommOn.Read(comm_ring.MulMonoidOn.Read(ring)), inC, inverse))
			absorbs := a.Have(
				"were u in I, absorption would put v * u in I",
				"u ∈ I ⇒ v * u ∈ I",
				By(IdealMul, ideal, inverse))
			a.Show(
				"but v * u is u * v, which is one, and I does not hold one",
				By(Normalized, proper, absorbs, commute, inverse))
		}),
})}

// ChainUnionIdeal — the union of a non-empty chain of ideals is an ideal:
// each condition is met inside one member of the chain. Zero lies in any
// member; a member x of the union lies in a member of the chain, which
// holds its multiples; and of two members of the chain holding x and y,
// the larger holds both, and so their sum.
var ChainUnionIdeal = chainUnionIdealThm{family.Add(registry.ProofEntry{
	Name: "ChainUnionIdeal",
	Key:  "prop_6a3d499926038aeb",
	Reading: "Needs no ring. G ≠ ∅ is load-bearing: the " +
		"union of the empty chain is ∅, which does not hold zero.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀G:set(set(A)).",
		Hypotheses: []string{
			"G ≠ ∅",
			"∀J:set(A). J ∈ G ⇒ ring_ideal(R, J)",
			"∀J K:set(A). J ∈ G ∧ K ∈ G ⇒ J ⊆ K ∨ K ⊆ J",
		},
		Conclusion: "ring_ideal(R, ⋃G)",
	},
		func(a *Argument, R *Expr[module_record.RingOps[A]], G *Expr[Set[Set[A]]], hypotheses Fact) {
			parts := a.Conjuncts(
				hypotheses,
				"G is not empty",
				"every member of G is an ideal",
				"any two members of G are comparable")
			nonEmpty, ideals, chain := parts[0], parts[1], parts[2]
			g, gInG := a.ObtainAs[Set[A]](
				"G has a member g",
				"∃g:set(A). g ∈ G",
				By(nonEmpty, set_basic.MemberNotEmpty.At(G)))
			inC := a.Have(
				"each member of G, an ideal, lies in c",
				"∀J:set(A). J ∈ G ⇒ J ⊆ R.carrier",
				a.ForEach(func(J *Expr[Set[A]]) Action {
					return By(ideals.At(J), IdealSubset.At(R, J))
				}))
			a.Do(Simp(Fwd(RingIdealDef)), SplitConjAll(
				Case(
					"so their union lies in c",
					By(inC, set_order.UnionsSubset.At(G, a.TermAs[Set[A]]("R.carrier")))),
				Case(
					"zero lies in the ideal g",
					By(ideals.At(g), gInG, IdealZero.At(R, g), set_basic.InUnions.At(G, a.TermAs[A]("R.zero")))),
				Case(
					"of two members of G holding x and y, the larger holds both, and their sum",
					Derive(func(d *Argument) {
						x := d.FixAs[A]("x")
						y := d.FixAs[A]("y")
						given := d.Conjuncts(
							d.Assume(),
							"x lies in the union",
							"y lies in the union")
						J, xIn := d.ObtainAs[Set[A]](
							"x lies in a member J of G",
							"∃J:set(A). J ∈ G ∧ x ∈ J",
							By(given[0], set_basic.InUnions.At(G, x)))
						K, yIn := d.ObtainAs[Set[A]](
							"and y in a member K",
							"∃K:set(A). K ∈ G ∧ y ∈ K",
							By(given[1], set_basic.InUnions.At(G, y)))
						L, both := d.ObtainAs[Set[A]](
							"one of J and K contains the other, and so holds x and y",
							"∃L:set(A). L ∈ G ∧ x ∈ L ∧ y ∈ L",
							BySets(chain.At(J, K), xIn, yIn))
						d.Show(
							"that member is an ideal, holding R.add(x, y)",
							By(
								ideals.At(L),
								both,
								IdealAdd.At(R, L, x, y),
								set_basic.InUnions.At(G, d.TermAs[A]("R.add(x, y)"))))
					})),
				Case(
					"the member of G holding x holds its multiples",
					Derive(func(d *Argument) {
						r := d.FixAs[A]("r")
						x := d.FixAs[A]("x")
						given := d.Conjuncts(
							d.Assume(),
							"r lies in c",
							"x lies in the union")
						J, xIn := d.ObtainAs[Set[A]](
							"x lies in a member J of G",
							"∃J:set(A). J ∈ G ∧ x ∈ J",
							By(given[1], set_basic.InUnions.At(G, x)))
						d.Show(
							"J is an ideal, holding R.mul(r, x)",
							By(
								ideals.At(J),
								given[0],
								xIn,
								IdealMul.At(R, J, r, x),
								set_basic.InUnions.At(G, d.TermAs[A]("R.mul(r, x)"))))
					})),
			))
		}),
})}

// ---------------------------------------------------------------------------
// The ideal a set generates
// ---------------------------------------------------------------------------

// SpanIdeal — the span of a subset of c is an ideal: each condition of an
// ideal holds in every ideal holding S, so in their intersection, and c
// is one of them, which keeps the span inside c.
var SpanIdeal = spanIdealThm{family.Add(registry.ProofEntry{
	Name: "SpanIdeal",
	Key:  "prop_d294ab45b06b3045",
	Reading: "S ⊆ R.carrier is load-bearing: without it no ideal of R.carrier " +
		"holds S, the family is empty, and the span is ⋂∅ = 𝕌, which is not inside c.",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀S:set(A).",
		Hypotheses: []string{
			"S ⊆ R.carrier",
		},
		Conclusion: "ring_ideal(R, ideal_span(R, S))",
	},
		func(
			a *Argument,
			R *Expr[module_record.RingOps[A]],
			ring comm_ring.CommRingFact[on.R],
			S *Expr[Set[A]],
			inside Fact,
		) {
			member := a.Have(
				"a member of the span is a member of every ideal of c holding S",
				"∀x:A. x ∈ ideal_span(R, S) ⇔ ∀J:set(A). ring_ideal(R, J) ∧ S ⊆ J ⇒ x ∈ J",
				Unfold(IdealSpanDef),
				BySets())
			a.Do(Simp(Fwd(RingIdealDef)), SplitConjAll(
				Case(
					"the span lies in c, itself an ideal holding S",
					By(SpanLeast.At(R, S, a.TermAs[Set[A]]("R.carrier")), CarrierIdeal.Read(ring), inside)),
				Case(
					"zero lies in every ideal holding S",
					By(member, IdealZero)),
				Case(
					"each ideal holding S holds the sum of two of its members",
					By(member, IdealAdd)),
				Case(
					"each ideal holding S absorbs the product of one of its members by a member of c",
					By(member, IdealMul)),
			))
		}),
})}

// SpanContains — a set lies in its span: in every ideal holding it, and
// ⋂∅ is 𝕌.
var SpanContains = spanContainsThm{family.Add(registry.ProofEntry{
	Name:    "SpanContains",
	Key:     "prop_e7967a45d7b1038a",
	Reading: "Needs no ring and no hypothesis on S: when S is not inside c the span is ⋂∅ = 𝕌.",
	Build: family.Theorem("∀R:ring_ops(A). ∀S:set(A). S ⊆ ideal_span(R, S)",
		func(a *Argument, R *Expr[module_record.RingOps[A]], S *Expr[Set[A]]) {
			a.Show(
				"every member of the family the span intersects holds S",
				Unfold(IdealSpanDef),
				BySets())
		}),
})}

// SpanLeast — the span lies in every ideal holding the set.
var SpanLeast = spanLeastThm{family.Add(registry.ProofEntry{
	Name:    "SpanLeast",
	Key:     "prop_a60eb7486388bb1f",
	Reading: "Needs no ring: J is a member of the family the span intersects.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀S J:set(A).",
		Hypotheses: []string{
			"ring_ideal(R, J)",
			"S ⊆ J",
		},
		Conclusion: "ideal_span(R, S) ⊆ J",
	},
		func(a *Argument, R *Expr[module_record.RingOps[A]], S, J *Expr[Set[A]], hypotheses Fact) {
			member := a.Have(
				"J is a member of the family the span intersects",
				"J ∈ {K:set(A) | ring_ideal(R, K) ∧ S ⊆ K}",
				BySets(hypotheses))
			a.Show(
				"and an intersection lies in each of its members",
				Unfold(IdealSpanDef),
				BySets(member))
		}),
})}

// SpanOfIdeal — the span of an ideal is the ideal: it lies in I, an ideal
// holding I, and it holds I.
var SpanOfIdeal = spanOfIdealThm{family.Add(registry.ProofEntry{
	Name:    "SpanOfIdeal",
	Key:     "prop_d5c7c72b713a4b99",
	Reading: "Needs no ring: I is a member of the family the span intersects.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀I:set(A).",
		Hypotheses: []string{
			"ring_ideal(R, I)",
		},
		Conclusion: "ideal_span(R, I) = I",
	},
		func(a *Argument, R *Expr[module_record.RingOps[A]], I *Expr[Set[A]], ideal Fact) {
			span := a.TermAs[Set[A]]("ideal_span(R, I)")
			below := a.Have(
				"the span lies in I, an ideal holding I",
				"ideal_span(R, I) ⊆ I",
				By(SpanLeast.At(R, I, I), ideal, set_order.SubsetRefl.At(I)))
			a.Show(
				"and it holds I, so each lies in the other",
				By(set_order.SubsetAntisym.At(span, I), below, SpanContains.At(R, I)))
		}),
})}

// SpanMono — the span grows with the set: an ideal holding T holds S, so
// the span of S lies in each ideal the span of T is the intersection of.
var SpanMono = spanMonoThm{family.Add(registry.ProofEntry{
	Name:    "SpanMono",
	Key:     "prop_76730969154191e5",
	Reading: "Needs no ring and no hypothesis on T: when no ideal of c holds T, its span is ⋂∅ = 𝕌.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀S T:set(A).",
		Hypotheses: []string{
			"S ⊆ T",
		},
		Conclusion: "ideal_span(R, S) ⊆ ideal_span(R, T)",
	},
		func(a *Argument, R *Expr[module_record.RingOps[A]], S, T *Expr[Set[A]], below Fact) {
			a.Show(
				"every ideal holding T holds S",
				Unfold(IdealSpanDef),
				BySets(below))
		}),
})}

// SpanClosureOperator — ideal span is a closure operator on the subsets of
// a ring's carrier: each subset has a least ideal above it in the powerset
// order.
var SpanClosureOperator = spanClosureOperatorThm{family.Add(registry.ProofEntry{
	Name: "SpanClosureOperator",
	Key:  "prop_9886793a0cea8d19",
	Build: comm_ring.CommRingOn.Law("closure_operator_on({S:set(A) | S ⊆ R.carrier}, "+
		"    λS:set(A). λT:set(A). S ⊆ T, "+
		"    λS:set(A). ideal_span(R, S))",
		func(a *Argument, R *Expr[module_record.RingOps[A]], ring comm_ring.CommRingFact[on.R]) {
			powerset := a.Have(
				"the subsets of the ring's carrier form a complete lattice",
				"complete_lattice_on({S:set(A) | S ⊆ R.carrier}, "+
					"    λS:set(A). λT:set(A). S ⊆ T, "+
					"    λF:set(set(A)). ⋃F, "+
					"    λF:set(set(A)). R.carrier ∩ ⋂F)",
				By(order.PowersetCompleteLattice))
			idealsWithin := a.Have(
				"every ideal belongs to this powerset",
				"{I:set(A) | ring_ideal(R, I)} ⊆ {S:set(A) | S ⊆ R.carrier}",
				By(At(IdealSubset, R), set_basic.SubsetDef))
			least := a.Have(
				"the span is the least ideal containing each set in the carrier",
				Statement{
					Binders: "∀S:set(A).",
					Hypotheses: []string{
						"S ⊆ R.carrier",
					},
					Conclusion: "ring_ideal(R, ideal_span(R, S)) ∧ " +
						"S ⊆ ideal_span(R, S) ∧ " +
						"(∀I:set(A). ring_ideal(R, I) ∧ S ⊆ I ⇒ ideal_span(R, S) ⊆ I)",
				},
				By(SpanIdeal.Read(ring), At(SpanContains, R), At(SpanLeast, R)))
			ideals := a.TermAs[Set[Set[A]]]("{I:set(A) | ring_ideal(R, I)}")
			a.Show(
				"least ideals above sets give a closure operator on the powerset",
				By(
					order.CompleteLatticeOnPartialOrder.Read(powerset),
					least,
					idealsWithin,
					Where(order.ClosureFromLeast, "F", ideals)))
		}),
})}

// SpanInsertAbove — the span of S with one more element h of c is an
// ideal holding S and h, and so not S when h lies outside S: insert(h, S)
// lies in c, so its span is an ideal (SpanIdeal), and it holds
// insert(h, S) (SpanContains), which is h and S.
var SpanInsertAbove = spanInsertAboveThm{family.Add(registry.ProofEntry{
	Name: "SpanInsertAbove",
	Key:  "prop_45e04dee2800a337",
	Reading: "S ⊆ R.carrier and h ∈ R.carrier are what make the span an " +
		"ideal: if either fails it is ⋂∅ = 𝕌. S need not be an ideal; when " +
		"it is, the span is an ideal strictly above it exactly when h ∉ S.",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀S:set(A). ∀h:A.",
		Hypotheses: []string{
			"S ⊆ R.carrier",
			"h ∈ R.carrier",
		},
		Conclusion: "ring_ideal(R, ideal_span(R, insert(h, S))) ∧ " +
			"S ⊆ ideal_span(R, insert(h, S)) ∧ " +
			"h ∈ ideal_span(R, insert(h, S)) ∧ " +
			"(h ∉ S ⇒ ideal_span(R, insert(h, S)) ≠ S)",
	},
		func(
			a *Argument,
			R *Expr[module_record.RingOps[A]],
			ring comm_ring.CommRingFact[on.R],
			S *Expr[Set[A]],
			h *Expr[A],
			hypotheses Fact,
		) {
			parts := a.Conjuncts(
				hypotheses,
				"S lies in c",
				"h lies in c")
			inside, hIn := parts[0], parts[1]
			generators := a.TermAs[Set[A]]("insert(h, S)")
			span := a.TermAs[Set[A]]("ideal_span(R, insert(h, S))")
			generatorsInside := a.Have(
				"insert(h, S) lies in c",
				"insert(h, S) ⊆ R.carrier",
				By(hIn, inside, set_order.InsertSubset.At(S, a.TermAs[Set[A]]("R.carrier"), h)))
			holds := a.Have(
				"the span holds insert(h, S), so h and S",
				"h ∈ ideal_span(R, insert(h, S)) ∧ S ⊆ ideal_span(R, insert(h, S))",
				By(SpanContains.At(R, generators), set_order.InsertSubset.At(S, span, h)))
			distinct := a.Have(
				"holding h, the span is not S when S does not hold h",
				"h ∉ S ⇒ ideal_span(R, insert(h, S)) ≠ S",
				By(Normalized, holds))
			a.Show(
				"the span is an ideal holding S and h, and not S when h lies outside S",
				By(generatorsInside, SpanIdeal.Read(ring).At(generators), holds, distinct))
		}),
})}

// SpanInsert — the span of S with one more element h is every multiple
// of h added to a member of the span of S. Call that set B. The span of
// insert(h, S) is an ideal holding h and S (SpanInsertAbove), so the span
// of S, and it holds each b * h + t; and B is an ideal — the sum of two of its members and a
// multiple of one regroup into the same shape — holding h = one * h + zero
// and each s = zero * h + s of S, so it holds the span of insert(h, S).
var SpanInsert = spanInsertThm{family.Add(registry.ProofEntry{
	Name: "SpanInsert",
	Key:  "prop_896742ef662dc819",
	Reading: "S ⊆ R.carrier and h ∈ R.carrier are both " +
		"load-bearing: if either fails, the left side is ⋂∅ = 𝕌.",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀S:set(A). ∀h:A.",
		Hypotheses: []string{
			"S ⊆ R.carrier",
			"h ∈ R.carrier",
		},
		Conclusion: "ideal_span(R, insert(h, S)) = " +
			"{b * h + t | b:A, t:A | b ∈ R.carrier ∧ t ∈ ideal_span(R, S)}",
	},
		func(
			a *Argument,
			R *Expr[module_record.RingOps[A]],
			ring comm_ring.CommRingFact[on.R],
			S *Expr[Set[A]],
			h *Expr[A],
			hypotheses Fact,
		) {
			parts := a.Conjuncts(
				hypotheses,
				"S lies in c",
				"h lies in c")
			inside, hIn := parts[0], parts[1]
			addMonoid := comm_ring.AddMonoidOn.Read(ring)
			mulMonoid := comm_ring.MulMonoidOn.Read(ring)
			spanIdeal := a.Have(
				"the span of S is an ideal",
				"ring_ideal(R, ideal_span(R, S))",
				By(ring, inside, SpanIdeal))
			spanInC := a.Have(
				"so it lies in c",
				"ideal_span(R, S) ⊆ R.carrier",
				By(spanIdeal, IdealSubset))

			B, combinationSetDef := a.LetAs[Set[A]](
				"B", "{b * h + t | b:A, t:A | b ∈ R.carrier ∧ t ∈ ideal_span(R, S)}")
			member := a.Have(
				"a member of B is a multiple of h plus a member of the span of S",
				"∀z:A. z ∈ B ⇔ ∃b t:A. b ∈ R.carrier ∧ t ∈ ideal_span(R, S) ∧ z = b * h + t",
				BySets(combinationSetDef))
			intro := a.Have(
				"and every such sum lies in B",
				"∀b t:A. b ∈ R.carrier ∧ t ∈ ideal_span(R, S) ⇒ b * h + t ∈ B",
				BySets(combinationSetDef))

			// B lies in the span of insert(h, S).
			enlargedSpan := a.TermAs[Set[A]]("ideal_span(R, insert(h, S))")
			enlarged := a.Conjuncts(
				GroupPremises(parts[0], SpanInsertAbove.Read(ring).At(S, a.MemberOf[on.R](h, hIn))),
				"the span of insert(h, S) is an ideal",
				"holding S",
				"and h",
				"and not S when h lies outside S")
			enlargedSpanIdeal, generatorsInEnlargedSpan, hInEnlargedSpan :=
				enlarged[0], enlarged[1], enlarged[2]
			spanInEnlargedSpan := a.Have(
				"and so the span of S",
				"ideal_span(R, S) ⊆ ideal_span(R, insert(h, S))",
				By(SpanLeast.At(R, S, enlargedSpan), enlargedSpanIdeal, generatorsInEnlargedSpan))
			above := a.Have(
				"each member b * h + t of B lies in the span of "+
					"insert(h, S): absorption puts b * h there, and t is there",
				"B ⊆ ideal_span(R, insert(h, S))",
				Simp(Fwd(set_basic.SubsetDef)),
				Derive(func(d *Argument) {
					d.FixAs[A]("z")
					_, _, zForm := d.Obtain2(
						"z is b * h + t for some b in c and t in the span of S",
						"∃b t:A. b ∈ R.carrier ∧ t ∈ ideal_span(R, S) ∧ z = b * h + t",
						By(member, d.Assume()))
					zs := d.Conjuncts(
						zForm,
						"b lies in c",
						"t lies in the span of S",
						"z is b * h + t")
					tInEnlargedSpan := d.Have(
						"t lies in the span of insert(h, S)",
						"t ∈ ideal_span(R, insert(h, S))",
						BySets(spanInEnlargedSpan, zs[1]))
					d.Show(
						"b * h and t lie in that ideal, and so does their sum",
						zs[2].Rw(),
						By(enlargedSpanIdeal, hInEnlargedSpan, zs[0], tInEnlargedSpan, IdealAdd, IdealMul))
				}))

			// B is an ideal holding insert(h, S).
			bIdeal := a.Have(
				"B is an ideal",
				"ring_ideal(R, B)",
				Simp(Fwd(RingIdealDef)),
				SplitConjAll(
					Case(
						"B lies in the span of insert(h, S), which lies in c",
						BySets(above, enlargedSpanIdeal, IdealSubset)),
					Case(
						"zero is zero * h + zero",
						Derive(func(d *Argument) {
							inB := d.Have(
								"zero * h + zero lies in B, zero lying in c and in the span of S",
								"R.zero * h + R.zero ∈ B",
								By(intro, ring, spanIdeal, comm_ring.ZeroIn, IdealZero))
							sum := d.Have(
								"and zero * h + zero is zero",
								"R.zero * h + R.zero = R.zero",
								Simp(
									Fwd(comm_ring.MulLeftZeroOn),
									Fwd(comm_monoid.LeftIdentityOn.Read(addMonoid)),
									Fwd(comm_ring.ZeroIn)),
								Refl())
							d.Show(
								"so zero lies in B",
								By(sum, inB))
						})),
					Case(
						"(b * h + t) + (b' * h + t') is (b + b') * h + (t + t')",
						Derive(func(d *Argument) {
							d.FixAs[A]("x")
							d.FixAs[A]("y")
							inB := d.Conjuncts(
								d.Assume(),
								"x lies in B",
								"y lies in B")
							_, _, xForm := d.Obtain2(
								"x is b * h + t for some b in c and t in the span of S",
								"∃b t:A. b ∈ R.carrier ∧ t ∈ ideal_span(R, S) ∧ x = b * h + t",
								By(member, inB[0]))
							xs := d.Conjuncts(
								xForm,
								"b lies in c",
								"t lies in the span of S",
								"x is b * h + t")
							_, _, yForm := d.Obtain2(
								"and y is b' * h + t' likewise",
								"∃b' t':A. b' ∈ R.carrier ∧ t' ∈ ideal_span(R, S) ∧ y = b' * h + t'",
								By(member, inB[1]))
							ys := d.Conjuncts(
								yForm,
								"b' lies in c",
								"t' lies in the span of S",
								"y is b' * h + t'")
							tsInC := d.Have(
								"t and t' lie in c",
								"t ∈ R.carrier ∧ t' ∈ R.carrier",
								BySets(spanInC, xs[1], ys[1]))
							sum := d.Have(
								"x + y is (b + b') * h + (t + t')",
								"x + y = (b + b') * h + (t + t')",
								CalcEq(
									Leg(
										d.TermAs[A]("(b * h + t) + (b' * h + t')"),
										"write out x and y",
										By(Normalized, xs[2], ys[2])),
									FinalLeg(
										"regroup and gather the multiples of h",
										ByArith(ring, xs[0], ys[0], hIn, tsInC)),
								))
							d.Show(
								"b + b' lies in c and t + t' in the span of S",
								sum.Rw(),
								By(intro, ring, xs[0], ys[0], spanIdeal, xs[1], ys[1], comm_ring.AddIn, IdealAdd))
						})),
					Case(
						"r * (b * h + t) is (r * b) * h + r * t",
						Derive(func(d *Argument) {
							d.FixAs[A]("r")
							d.FixAs[A]("x")
							given := d.Conjuncts(
								d.Assume(),
								"r lies in c",
								"x lies in B")
							_, _, xForm := d.Obtain2(
								"x is b * h + t for some b in c and t in the span of S",
								"∃b t:A. b ∈ R.carrier ∧ t ∈ ideal_span(R, S) ∧ x = b * h + t",
								By(member, given[1]))
							xs := d.Conjuncts(
								xForm,
								"b lies in c",
								"t lies in the span of S",
								"x is b * h + t")
							tInC := d.Have(
								"t lies in c",
								"t ∈ R.carrier",
								BySets(spanInC, xs[1]))
							product := d.Have(
								"r * x is (r * b) * h + r * t",
								"r * x = (r * b) * h + r * t",
								CalcEq(
									Leg(
										d.TermAs[A]("r * (b * h + t)"),
										"write out x",
										By(Normalized, xs[2])),
									FinalLeg(
										"distribute r and regroup",
										ByArith(ring, given[0], xs[0], hIn, tInC)),
								))
							d.Show(
								"r * b lies in c and r * t in the span of S",
								product.Rw(),
								By(intro, ring, given[0], xs[0], spanIdeal, xs[1], comm_ring.MulIn, IdealMul))
						})),
				))
			oneInB := a.Have(
				"one * h + zero lies in B, one lying in c and zero in the span of S",
				"R.one * h + R.zero ∈ B",
				By(intro, ring, spanIdeal, comm_ring.OneIn, IdealZero))
			hSum := a.Have(
				"and one * h + zero is h",
				"R.one * h + R.zero = h",
				Simp(
					Fwd(comm_monoid.RightIdentityOn.Read(addMonoid)),
					Fwd(comm_monoid.LeftIdentityOn.Read(mulMonoid)),
					Fwd(comm_ring.MulIn),
					Fwd(comm_ring.OneIn)),
				Refl())
			hInB := a.Have(
				"so h lies in B",
				"h ∈ B",
				By(Normalized, hSum, oneInB))
			sInB := a.Have(
				"and so does each s of S, as zero * h + s",
				"S ⊆ B",
				Simp(Fwd(set_basic.SubsetDef)),
				Derive(func(d *Argument) {
					d.FixAs[A]("s")
					inS := d.Assume()
					d.Have(
						"s lies in c",
						"s ∈ R.carrier",
						BySets(inside, inS))
					inSpan := d.Have(
						"and in the span of S",
						"s ∈ ideal_span(R, S)",
						BySets(inS, SpanContains))
					inB := d.Have(
						"so zero * h + s lies in B",
						"R.zero * h + s ∈ B",
						By(intro, ring, inSpan, comm_ring.ZeroIn))
					sum := d.Have(
						"and zero * h + s is s",
						"R.zero * h + s = s",
						Simp(
							Fwd(comm_ring.MulLeftZeroOn),
							Fwd(comm_monoid.LeftIdentityOn.Read(addMonoid)),
							Fwd(comm_ring.ZeroIn)),
						Refl())
					d.Show(
						"so s lies in B",
						By(Normalized, sum, inB))
				}))
			insertInB := a.Have(
				"so B holds insert(h, S)",
				"insert(h, S) ⊆ B",
				By(hInB, sInB, set_order.InsertSubset))
			below := a.Have(
				"and, an ideal, the span of insert(h, S)",
				"ideal_span(R, insert(h, S)) ⊆ B",
				By(SpanLeast.At(R, a.TermAs[Set[A]]("insert(h, S)"), B), bIdeal, insertInB))
			a.Show(
				"each side lies in the other",
				By(set_order.SubsetAntisym.At(enlargedSpan, B), below, above))
		}),
})}

// SpanInsertIdeal — the span of an ideal I with one more element h is
// every multiple of h added to a member of I: SpanInsert says so with the
// span of I in place of I, and the span of I is I (SpanOfIdeal).
var SpanInsertIdeal = spanInsertIdealThm{family.Add(registry.ProofEntry{
	Name: "SpanInsertIdeal",
	Key:  "prop_d5ad84f307a6846f",
	Reading: "h ∈ R.carrier is load-bearing: otherwise the left side " +
		"is ⋂∅ = 𝕌. That I is an ideal is what makes its span I itself.",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀I:set(A). ∀h:A.",
		Hypotheses: []string{
			"ring_ideal(R, I)",
			"h ∈ R.carrier",
		},
		Conclusion: "ideal_span(R, insert(h, I)) = {b * h + t | b:A, t:A | b ∈ R.carrier ∧ t ∈ I}",
	},
		func(
			a *Argument,
			R *Expr[module_record.RingOps[A]],
			ring comm_ring.CommRingFact[on.R],
			I *Expr[Set[A]],
			h *Expr[A],
			hypotheses Fact,
		) {
			parts := a.Conjuncts(
				hypotheses,
				"I is an ideal",
				"h lies in c")
			ideal, hIn := parts[0], parts[1]
			a.Show(
				"the span of I with h is every multiple of h plus a member of the span of I, which is I",
				By(SpanInsert.At(R, I, h), ring, IdealSubset, hIn, SpanOfIdeal.At(R, I), ideal))
		}),
})}

// SpanPairWhole — two members of the ring with a combination equal to one
// span the whole ring: the span is an ideal holding both, so it holds the
// combination, which is one, and an ideal holding one is the ring.
var SpanPairWhole = spanPairWholeThm{family.Add(registry.ProofEntry{
	Name: "SpanPairWhole",
	Key:  "prop_2dcf719c69190c96",
	Reading: "One direction of the Bezout criterion for the unit ideal: a " +
		"combination of g₁ and g₂ equal to one puts one in their span. The " +
		"memberships of c₁ and c₂ are load-bearing: a combination with a cofactor " +
		"outside R.carrier says nothing about the ideal g₁ and g₂ span in the ring.",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀g₁ g₂ c₁ c₂:A.",
		Hypotheses: []string{
			"g₁ ∈ R.carrier",
			"g₂ ∈ R.carrier",
			"c₁ ∈ R.carrier",
			"c₂ ∈ R.carrier",
			"c₁ * g₁ + c₂ * g₂ = R.one",
		},
		Conclusion: "ideal_span(R, {g₁, g₂}) = R.carrier",
	},
		func(
			a *Argument,
			R *Expr[module_record.RingOps[A]],
			ring comm_ring.CommRingFact[on.R],
			g1, g2, c1, c2 *Member[A, on.R],
			combination Fact,
		) {
			pair := a.TermAs[Set[A]]("{g₁, g₂}")
			span := a.TermAs[Set[A]]("ideal_span(R, {g₁, g₂})")
			ideal := a.Have(
				"the span of g₁ and g₂ is an ideal, both lying in the ring",
				"ring_ideal(R, ideal_span(R, {g₁, g₂}))",
				BySets(SpanIdeal.Read(ring).At(pair), g1, g2))
			generators := a.Have(
				"it holds g₁ and g₂",
				"g₁ ∈ ideal_span(R, {g₁, g₂}) ∧ g₂ ∈ ideal_span(R, {g₁, g₂})",
				BySets(SpanContains.At(R, pair)))
			one := a.Have(
				"so it holds c₁ * g₁ + c₂ * g₂, which is one",
				"R.one ∈ ideal_span(R, {g₁, g₂})",
				combination.RwRev(),
				By(
					ideal,
					generators,
					c1,
					c2,
					IdealMul.At(R, span, c1, g1),
					IdealMul.At(R, span, c2, g2),
					IdealAdd.At(R, span, a.TermAs[A]("c₁ * g₁"), a.TermAs[A]("c₂ * g₂"))))
			a.Show(
				"and an ideal holding one is the whole ring",
				By(IdealOneIff.Read(ring), ideal, one))
		}),
})}

// SpanUnionIdeals — the ideal generated by two ideals consists of their element sums:
// the sums form an ideal containing both, and every containing ideal holds each sum.
var SpanUnionIdeals = spanUnionIdealsThm{family.Add(registry.ProofEntry{
	Name: "SpanUnionIdeals",
	Key:  "prop_d9f993d4fb6ee4ba",
	Build: family.Theorem(Statement{
		Binders: "∀c:comm_ring_on(A). ∀I J:set(A).",
		Hypotheses: []string{
			"ring_ideal(c, I)",
			"ring_ideal(c, J)",
		},
		Conclusion: "ideal_span(c, I ∪ J) = «Sum»",
		Abbrev: Abbrev{
			{Name: "Sum", Text: "{u + v | u:A, v:A | u ∈ I ∧ v ∈ J}"},
		},
	}, func(a *Argument, c comm_ring.CommRingFact[on.C], I, J *Expr[Set[A]], h Fact) {
		parts := a.Conjuncts(
			h,
			"I is an ideal",
			"J is an ideal")
		idealI, idealJ := parts[0], parts[1]
		ops := a.TermAs[RingOps[A]]("c")
		T, sumDef := a.LetAs[Set[A]]("T", "«Sum»")
		inCarrier := a.Have(
			"both ideals lie in the carrier",
			"I ⊆ c.carrier ∧ J ⊆ c.carrier",
			By(idealI, idealJ, IdealSubset))
		sumsIdeal := a.Have(
			"element sums form an ideal",
			"ring_ideal(c, T)",
			Simp(Fwd(RingIdealDef)),
			SplitConjAll(
				Case(
					"sums stay in the carrier",
					BySets(comm_ring.AddIn.Read(c), sumDef, inCarrier)),
				Case(
					"zero is the sum of the two ideal zeros",
					BySets(
						comm_ring.ZeroIn.Read(c),
						comm_monoid.LeftIdentityOn.Read(comm_ring.AddMonoidOn.Read(c)),
						sumDef,
						idealI,
						idealJ,
						IdealZero.At(ops, I),
						IdealZero.At(ops, J))),
				Case(
					"adding two sums adds their I and J components",
					Derive(func(b *Argument) {
						b.FixAs[A]("x")
						b.FixAs[A]("y")
						members := b.Assume()
						_, _, first := b.Obtain2As[A, A](
							"write the first sum in its two ideals",
							"∃u v:A. u ∈ I ∧ v ∈ J ∧ x = u + v",
							BySets(sumDef, members))
						_, _, second := b.Obtain2As[A, A](
							"write the second sum in its two ideals",
							"∃s t:A. s ∈ I ∧ t ∈ J ∧ y = s + t",
							BySets(sumDef, members))
						regroup := b.Have(
							"regroup the I components and the J components",
							"x + y = (u + s) + (v + t)",
							Derive(func(d *Argument) {
								carriers := d.Have(
									"the summands and their sums belong to the ring",
									"u ∈ c.carrier ∧ v ∈ c.carrier ∧ s ∈ c.carrier ∧ t ∈ c.carrier ∧ x ∈ c.carrier ∧ y ∈ c.carrier",
									BySets(comm_ring.AddIn.Read(c), inCarrier, second, first))
								d.Show(
									"associate and commute the summands",
									ByArith(c, second, first, carriers))
							}))
						b.Show(
							"each regrouped component remains in its ideal",
							BySets(regroup, sumDef, idealI, idealJ, second, first, IdealAdd))
					})),
				Case(
					"scaling a sum scales each component inside its ideal",
					Derive(func(b *Argument) {
						r := b.FixAs[A]("r")
						b.FixAs[A]("x")
						guard := b.Assume()
						u, v, sum := b.Obtain2As[A, A](
							"write the sum in its two ideals",
							"∃u v:A. u ∈ I ∧ v ∈ J ∧ x = u + v",
							BySets(sumDef, guard))
						b.Show(
							"distribution and ideal absorption preserve the sum",
							BySets(
								sumDef,
								idealI,
								idealJ,
								guard,
								inCarrier,
								sum,
								comm_ring.LeftDistribOn.Read(c).AsFact().At(r, u, v),
								IdealMul.At(ops, I, r, u),
								IdealMul.At(ops, J, r, v)))
					}))))
		contains := a.Have(
			"each ideal embeds by adding the other ideal's zero",
			"I ∪ J ⊆ T",
			BySets(
				comm_monoid.LeftIdentityOn.Read(comm_ring.AddMonoidOn.Read(c)),
				comm_monoid.RightIdentityOn.Read(comm_ring.AddMonoidOn.Read(c)),
				sumDef,
				idealI,
				idealJ,
				inCarrier,
				IdealZero.At(ops, I),
				IdealZero.At(ops, J)))
		spanIdeal := a.Have(
			"the span of the union is an ideal",
			"ring_ideal(c, ideal_span(c, I ∪ J))",
			BySets(inCarrier, SpanIdeal.Read(c).At(a.TermAs[Set[A]]("I ∪ J"))))
		a.Show(
			"leastness gives one inclusion and closure under addition gives the other",
			BySets(
				sumDef,
				sumsIdeal,
				spanIdeal,
				contains,
				SpanLeast.At(ops, a.TermAs[Set[A]]("I ∪ J"), T),
				SpanContains.At(ops, a.TermAs[Set[A]]("I ∪ J")),
				At(IdealAdd, ops, a.TermAs[Set[A]]("ideal_span(c, I ∪ J)"))))
	}),
})}

// PrincipalIdealMultiples — the ideal generated by one element p of c
// consists of its multiples: adjoining zero changes no ideal, {zero} is an
// ideal, and the span of {zero} with p is every multiple of p plus zero
// (SpanInsertIdeal), from which the zero summand drops out.
var PrincipalIdealMultiples = principalIdealMultiplesThm{family.Add(registry.ProofEntry{
	Name: "PrincipalIdealMultiples",
	Key:  "prop_d92c6ef123e628e2",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀p:A.",
		Hypotheses: []string{
			"p ∈ R.carrier",
		},
		Conclusion: "«principal» = {q:A | ∃r:A. r ∈ R.carrier ∧ q = r * p}",
		Abbrev: Abbrev{
			{Name: "principal", Text: "ideal_span(R, {p})"},
			{Name: "withZero", Text: "{p, R.zero}"},
		},
	},
		func(
			a *Argument,
			R *Expr[module_record.RingOps[A]],
			ring comm_ring.CommRingFact[on.R],
			p *Member[A, on.R],
		) {
			generator := a.TermAs[Set[A]]("{p}")
			principal := a.TermAs[Set[A]]("«principal»")
			withZero := a.TermAs[Set[A]]("«withZero»")
			ideal := a.Have(
				"the generated set is an ideal",
				"ring_ideal(R, «principal»)",
				BySets(p, SpanIdeal.Read(ring).At(generator)))
			zeroAddsNothing := a.Have(
				"adjoining zero changes no ideal",
				"ideal_span(R, «withZero») = «principal»",
				BySets(
					ideal,
					IdealZero.At(R, principal),
					SpanContains.At(R, generator),
					SpanLeast.At(R, withZero, principal),
					SpanMono.At(R, generator, withZero)))
			withP := a.Have(
				"{zero} is an ideal, so the span of {zero} with p is every multiple of p plus zero",
				"ideal_span(R, «withZero») = {b * p + t | b:A, t:A | b ∈ R.carrier ∧ t ∈ {R.zero}}",
				By(ZeroIdeal.Read(ring), SpanInsertIdeal.Read(ring).At(a.TermAs[Set[A]]("{R.zero}"), p)))
			a.Do(zeroAddsNothing.RwRev(), withP.Rw())
			// Equal sets have the same members: compare the two at an arbitrary element.
			a.Do(Simp(Fwd(set_basic.Extension)))
			a.FixAs[A]("x")
			a.Iff()
			a.Forward(
				"remove the zero summand",
				func(b *Argument, represented Fact) {
					coefficient, _, form := b.Unpack2As[A, A](represented, "b", "t")
					product := b.TermAs[A]("b * p")
					b.Show(
						"the remaining term is a multiple",
						BySets(
							p,
							form,
							comm_ring.MulIn.Read(ring).AsFact().At(coefficient, p),
							comm_monoid.RightIdentityOn.Read(comm_ring.AddMonoidOn.Read(ring)).AsFact().At(product)))
				})
			a.Backward(
				"a multiple has the required zero summand",
				func(b *Argument, multiple Fact) {
					r, productEq := b.UnpackAs[A](multiple, "r")
					product := b.TermAs[A]("r * p")
					b.Show(
						"x is r * p + zero",
						BySets(
							p,
							productEq,
							comm_ring.MulIn.Read(ring).AsFact().At(r, p),
							comm_monoid.RightIdentityOn.Read(comm_ring.AddMonoidOn.Read(ring)).AsFact().At(product)))
				})
		}),
})}

// SpanFinite — a member of the span of S lies in the span of a finite
// part of S. Let U be the union of the spans of the finite parts of S.
// U is an ideal: it lies in c, as each of those spans does; it holds
// zero, in the span of ∅; it absorbs, as each span does; and two of its
// members lie in the spans of finite parts T and T', so both in the
// span of the finite part T ∪ T' (SpanMono), which holds their sum. U
// holds S, a member s lying in the span of {s}; so it holds the span of
// S (SpanLeast), and x with it.
var SpanFinite = spanFiniteThm{family.Add(registry.ProofEntry{
	Name: "SpanFinite",
	Key:  "prop_f5e1060c825a0a89",
	Reading: "S ⊆ R.carrier keeps every finite part's span an ideal; without " +
		"it the claim holds trivially, a singleton outside R.carrier spanning 𝕌.",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀S:set(A). ∀x:A.",
		Hypotheses: []string{
			"S ⊆ R.carrier",
			"x ∈ ideal_span(R, S)",
		},
		Conclusion: "∃T:set(A). finite(T) ∧ T ⊆ S ∧ x ∈ ideal_span(R, T)",
	},
		func(
			a *Argument,
			R *Expr[module_record.RingOps[A]],
			ring comm_ring.CommRingFact[on.R],
			S *Expr[Set[A]],
			x *Expr[A],
			hypotheses Fact,
		) {
			parts := a.Conjuncts(
				hypotheses,
				"S lies in c",
				"x lies in the span of S")
			inside, xIn := parts[0], parts[1]

			// The union of the spans of the finite parts of S.
			U, unionDef := a.LetAs[Set[A]]("U", "{y:A | ∃T:set(A). finite(T) ∧ T ⊆ S ∧ y ∈ ideal_span(R, T)}")
			member := a.Have(
				"a member of U lies in the span of a finite part of S",
				"∀y:A. y ∈ U ⇒ ∃T:set(A). finite(T) ∧ T ⊆ S ∧ y ∈ ideal_span(R, T)",
				BySets(unionDef))
			intro := a.Have(
				"and a member of such a span lies in U",
				"∀T:set(A). ∀y:A. finite(T) ∧ T ⊆ S ∧ y ∈ ideal_span(R, T) ⇒ y ∈ U",
				BySets(unionDef))
			partIdeal := a.Have(
				"the span of a part of S is an ideal, the part lying in c",
				"∀T:set(A). T ⊆ S ⇒ ring_ideal(R, ideal_span(R, T))",
				a.ForEach(func(T *Expr[Set[A]]) Action {
					return By(
						inside,
						set_order.SubsetTrans.At(T, S, a.TermAs[Set[A]]("R.carrier")),
						SpanIdeal.Read(ring).At(T))
				}))

			uIdeal := a.Have(
				"U is an ideal",
				"ring_ideal(R, U)",
				Simp(Fwd(RingIdealDef)),
				SplitConjAll(
					Case(
						"a member of U lies in the span of a part of S, which lies in c",
						Simp(Fwd(set_basic.SubsetDef)),
						Derive(func(d *Argument) {
							y := d.FixAs[A]("y")
							T, yForm := d.ObtainAs[Set[A]](
								"y lies in the span of a finite part T of S",
								"∃T:set(A). finite(T) ∧ T ⊆ S ∧ y ∈ ideal_span(R, T)",
								By(member.At(y), d.Assume()))
							ys := d.Conjuncts(
								yForm,
								"T is finite",
								"T lies in S",
								"y lies in its span")
							spanInC := d.Have(
								"that span, an ideal, lies in c",
								"ideal_span(R, T) ⊆ R.carrier",
								By(partIdeal.At(T), ys[1], IdealSubset.At(R, d.TermAs[Set[A]]("ideal_span(R, T)"))))
							d.Show(
								"and so does y",
								BySets(spanInC, ys[2]))
						})),
					Case(
						"zero lies in the span of the finite part ∅",
						Derive(func(d *Argument) {
							empty := d.TermAs[Set[A]]("∅⟨A:A⟩")
							zeroIn := d.Have(
								"zero lies in the span of ∅, an ideal",
								"R.zero ∈ ideal_span(R, ∅)",
								By(
									partIdeal.At(empty),
									set_order.EmptySubset.At(S),
									IdealZero.At(R, d.TermAs[Set[A]]("ideal_span(R, ∅)"))))
							d.Show(
								"and ∅ is a finite part of S",
								By(
									intro.At(empty, d.TermAs[A]("R.zero")),
									finite_set.FiniteRules,
									set_order.EmptySubset.At(S),
									zeroIn))
						})),
					Case(
						"two members of U lie in the span of the union of their two finite parts, which holds their sum",
						Derive(func(d *Argument) {
							u := d.FixAs[A]("u")
							v := d.FixAs[A]("v")
							given := d.Conjuncts(
								d.Assume(),
								"u lies in U",
								"v lies in U")
							T, uForm := d.ObtainAs[Set[A]](
								"u lies in the span of a finite part T of S",
								"∃T:set(A). finite(T) ∧ T ⊆ S ∧ u ∈ ideal_span(R, T)",
								By(member.At(u), given[0]))
							us := d.Conjuncts(
								uForm,
								"T is finite",
								"T lies in S",
								"u lies in its span")
							T2, vForm := d.ObtainAs[Set[A]](
								"and v in the span of a finite part T' of S",
								"∃T':set(A). finite(T') ∧ T' ⊆ S ∧ v ∈ ideal_span(R, T')",
								By(member.At(v), given[1]))
							vs := d.Conjuncts(
								vForm,
								"T' is finite",
								"T' lies in S",
								"v lies in its span")
							both := d.TermAs[Set[A]]("T ∪ T'")
							bothFinite := d.Have(
								"T ∪ T' is finite",
								"finite(T ∪ T')",
								By(us[0], vs[0], finite_set.FiniteUnionImp.At(T, T2)))
							bothInS := d.Have(
								"and a part of S",
								"T ∪ T' ⊆ S",
								By(us[1], vs[1], set_order.UnionSubset.At(T, T2, S)))
							grows := d.Have(
								"its span holds the spans of T and T'",
								"ideal_span(R, T) ⊆ ideal_span(R, T ∪ T') ∧ ideal_span(R, T') ⊆ ideal_span(R, T ∪ T')",
								By(
									set_order.SubsetUnion.At(T, T2),
									set_order.SubsetUnion.At(T2, T),
									SpanMono.At(R, T, both),
									SpanMono.At(R, T2, both)))
							inBoth := d.Have(
								"and so u and v",
								"u ∈ ideal_span(R, T ∪ T') ∧ v ∈ ideal_span(R, T ∪ T')",
								BySets(grows, us[2], vs[2]))
							sumIn := d.Have(
								"so their sum lies in that span, an ideal",
								"u + v ∈ ideal_span(R, T ∪ T')",
								By(
									partIdeal.At(both),
									bothInS,
									inBoth,
									IdealAdd.At(R, d.TermAs[Set[A]]("ideal_span(R, T ∪ T')"), u, v)))
							d.Show(
								"and T ∪ T' is a finite part of S",
								By(intro.At(both, d.TermAs[A]("u + v")), bothFinite, bothInS, sumIn))
						})),
					Case(
						"the span holding a member of U holds its multiples",
						Derive(func(d *Argument) {
							r := d.FixAs[A]("r")
							y := d.FixAs[A]("y")
							given := d.Conjuncts(
								d.Assume(),
								"r lies in c",
								"y lies in U")
							T, yForm := d.ObtainAs[Set[A]](
								"y lies in the span of a finite part T of S",
								"∃T:set(A). finite(T) ∧ T ⊆ S ∧ y ∈ ideal_span(R, T)",
								By(member.At(y), given[1]))
							ys := d.Conjuncts(
								yForm,
								"T is finite",
								"T lies in S",
								"y lies in its span")
							product := d.Have(
								"that span, an ideal, holds r * y",
								"r * y ∈ ideal_span(R, T)",
								By(
									partIdeal.At(T),
									ys[1],
									given[0],
									ys[2],
									IdealMul.At(R, d.TermAs[Set[A]]("ideal_span(R, T)"), r, y)))
							d.Show(
								"so U does",
								By(intro.At(T, d.TermAs[A]("r * y")), ys[0], ys[1], product))
						})),
				))
			sInU := a.Have(
				"U holds S, a member s of S lying in the span of the finite part {s}",
				"S ⊆ U",
				Simp(Fwd(set_basic.SubsetDef)),
				Derive(func(d *Argument) {
					s := d.FixAs[A]("s")
					inS := d.Assume()
					single := d.TermAs[Set[A]]("{s}")
					inSpan := d.Have(
						"s lies in the span of {s}",
						"s ∈ ideal_span(R, {s})",
						BySets(SpanContains.At(R, single)))
					d.Show(
						"and {s} is a finite part of S",
						By(intro.At(single, s), finite_set.FiniteSing.At(s), set_order.SingSubset.At(S, s), inS, inSpan))
				}))
			spanInU := a.Have(
				"so U, an ideal, holds the span of S",
				"ideal_span(R, S) ⊆ U",
				By(SpanLeast.At(R, S, U), uIdeal, sInU))
			xInU := a.Have(
				"and x with it",
				"x ∈ U",
				BySets(spanInU, xIn))
			a.Show(
				"so x lies in the span of a finite part of S",
				By(member.At(x), xInU))
		}),
})}

// ---------------------------------------------------------------------------
// The product of two ideals
// ---------------------------------------------------------------------------

// IdealMulHolds — the product of I and J holds the product of a member of
// I and a member of J: x * y is one of the products the product ideal is
// the span of, and a span holds the set it spans.
var IdealMulHolds = idealMulHoldsThm{family.Add(registry.ProofEntry{
	Name: "IdealMulHolds",
	Key:  "prop_55f367a1ab96ad6",
	Reading: "Needs no ring and no hypothesis on I or J: when no " +
		"ideal of R.carrier holds the products, the product is ⋂∅ = 𝕌.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀I J:set(A). ∀x y:A.",
		Hypotheses: []string{
			"x ∈ I",
			"y ∈ J",
		},
		Conclusion: "R.mul(x, y) ∈ ideal_mul(R, I, J)",
	},
		func(
			a *Argument,
			R *Expr[module_record.RingOps[A]],
			I, J *Expr[Set[A]],
			x, y *Expr[A],
			members Fact,
		) {
			generators := a.TermAs[Set[A]]("{R.mul(u, w):A | u:A, w:A | u ∈ I ∧ w ∈ J}")
			generator := a.Have(
				"x * y is one of the products spanning the product ideal",
				"R.mul(x, y) ∈ {R.mul(u, w):A | u:A, w:A | u ∈ I ∧ w ∈ J}",
				BySets(members))
			a.Show(
				"and the span holds the set it spans",
				Simp(Fwd(IdealMulDef)),
				BySets(generator, SpanContains.At(R, generators)))
		}),
})}

// IdealMulLeast — the product of I and J lies in every ideal holding the
// products x * y of a member of I and a member of J: so does the span of
// those products (SpanLeast).
var IdealMulLeast = idealMulLeastThm{family.Add(registry.ProofEntry{
	Name:    "IdealMulLeast",
	Key:     "prop_4c814c5b957c2715",
	Reading: "Needs no ring: K is one of the ideals the span intersects.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀I J K:set(A).",
		Hypotheses: []string{
			"ring_ideal(R, K)",
			"∀x y:A. x ∈ I ∧ y ∈ J ⇒ R.mul(x, y) ∈ K",
		},
		Conclusion: "ideal_mul(R, I, J) ⊆ K",
	},
		func(a *Argument, R *Expr[module_record.RingOps[A]], I, J, K *Expr[Set[A]], hypotheses Fact) {
			parts := a.Conjuncts(
				hypotheses,
				"K is an ideal",
				"holding each product x * y")
			ideal, holding := parts[0], parts[1]
			products := a.Have(
				"the products of I with J lie in K",
				"{R.mul(x, y):A | x:A, y:A | x ∈ I ∧ y ∈ J} ⊆ K",
				BySets(holding))
			a.Show(
				"so does their span, the product ideal",
				Simp(Fwd(IdealMulDef)),
				By(ideal, products, SpanLeast))
		}),
})}

// IdealMulMono — the product grows with its factors: I ⊆ M and J ⊆ N put
// the products of I with J among those of M with N, and the span grows
// with the set (SpanMono).
var IdealMulMono = idealMulMonoThm{family.Add(registry.ProofEntry{
	Name:    "IdealMulMono",
	Key:     "prop_ebae82519f585c4a",
	Reading: "Needs no ring and no ideal: it compares two spans of sets of products.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀I J M N:set(A).",
		Hypotheses: []string{
			"I ⊆ M",
			"J ⊆ N",
		},
		Conclusion: "ideal_mul(R, I, J) ⊆ ideal_mul(R, M, N)",
	},
		func(a *Argument, R *Expr[module_record.RingOps[A]], I, J, M, N *Expr[Set[A]], inclusions Fact) {
			fewer := a.Have(
				"the products of I with J are among those of M with N",
				"{R.mul(x, y):A | x:A, y:A | x ∈ I ∧ y ∈ J} ⊆ {R.mul(x, y):A | x:A, y:A | x ∈ M ∧ y ∈ N}",
				BySets(inclusions))
			a.Show(
				"so their span lies in the span of the larger set",
				Simp(Fwd(IdealMulDef)),
				By(fewer, SpanMono))
		}),
})}

// IdealMulIdeal — the product of two subsets of c is an ideal: the
// products x * y lie in c, and the span of a subset of c is an ideal
// (SpanIdeal).
var IdealMulIdeal = idealMulIdealThm{family.Add(registry.ProofEntry{
	Name: "IdealMulIdeal",
	Key:  "prop_3d52861bad64619f",
	Reading: "I ⊆ R.carrier and J ⊆ R.carrier keep the products inside c: a product outside " +
		"c lies in no ideal of c, and the span is then ⋂∅ = 𝕌. Neither factor need be an ideal.",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀I J:set(A).",
		Hypotheses: []string{
			"I ⊆ R.carrier",
			"J ⊆ R.carrier",
		},
		Conclusion: "ring_ideal(R, ideal_mul(R, I, J))",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], I, J *Expr[Set[A]], inclusions Fact) {
			products := a.Have(
				"the products x * y of I with J lie in c",
				"{x * y | x:A, y:A | x ∈ I ∧ y ∈ J} ⊆ R.carrier",
				BySets(inclusions, comm_ring.MulIn.Read(ring)))
			a.Show(
				"so their span, the product ideal, is an ideal",
				Simp(Fwd(IdealMulDef)),
				By(products, SpanIdeal.Read(ring)))
		}),
})}

// IdealMulSubsetInter — the product of two ideals lies in each of them, so
// in their intersection: for x in I and y in J, J absorbs x * y, x lying
// in c, and I absorbs y * x, which is x * y; so I and J are ideals holding
// every product spanning IJ (IdealMulLeast).
var IdealMulSubsetInter = idealMulSubsetInterThm{family.Add(registry.ProofEntry{
	Name: "IdealMulSubsetInter",
	Key:  "prop_cdab18fe50efd3b0",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀I J:set(A).",
		Hypotheses: []string{
			"ring_ideal(R, I)",
			"ring_ideal(R, J)",
		},
		Conclusion: "ideal_mul(R, I, J) ⊆ I ∩ J",
	},
		func(
			a *Argument,
			R *Expr[module_record.RingOps[A]],
			ring comm_ring.CommRingFact[on.R],
			I, J *Expr[Set[A]],
			ideals Fact,
		) {
			parts := a.Conjuncts(
				ideals,
				"I is an ideal",
				"J is an ideal")
			idealI, idealJ := parts[0], parts[1]
			inC := a.Have(
				"I and J lie in c",
				"I ⊆ R.carrier ∧ J ⊆ R.carrier",
				By(idealI, idealJ, IdealSubset))
			inJ := a.Have(
				"J absorbs x * y, x lying in c",
				"∀x y:A. x ∈ I ∧ y ∈ J ⇒ x * y ∈ J",
				By(idealJ, inC, IdealMul, set_basic.SubsetDef))
			inI := a.Have(
				"I absorbs y * x, which is x * y",
				"∀x y:A. x ∈ I ∧ y ∈ J ⇒ x * y ∈ I",
				Derive(func(b *Argument) {
					b.FixAs[A]("x")
					b.FixAs[A]("y")
					members := b.Assume()
					memberships := b.Have(
						"x and y lie in c",
						"x ∈ R.carrier ∧ y ∈ R.carrier",
						BySets(members, inC))
					absorbed := b.Have(
						"I absorbs y * x, y lying in c",
						"y * x ∈ I",
						By(idealI, members, memberships, IdealMul))
					b.Show(
						"x * y is y * x, so I holds it",
						By(Normalized, memberships, comm_monoid.CommOn.Read(comm_ring.MulMonoidOn.Read(ring)), absorbed))
				}))
			belowI := a.Have(
				"so I holds the product ideal",
				"ideal_mul(R, I, J) ⊆ I",
				By(inI, idealI, IdealMulLeast.At(R, I, J, I)))
			belowJ := a.Have(
				"and so does J",
				"ideal_mul(R, I, J) ⊆ J",
				By(inJ, idealJ, IdealMulLeast.At(R, I, J, J)))
			a.Show(
				"so the intersection holds it",
				By(belowI, belowJ, set_order.SubsetInter))
		}),
})}

// IdealMulComm — the product of two subsets of c does not depend on their
// order: IJ and JI are the spans of the products x * y and y * x, which
// are one set, the multiplication commuting on c.
var IdealMulComm = idealMulCommThm{family.Add(registry.ProofEntry{
	Name: "IdealMulComm",
	Key:  "prop_7d1ebcdee80c1c83",
	Reading: "I ⊆ R.carrier and J ⊆ R.carrier are there only for " +
		"the commutativity of the multiplication, which holds on c.",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀I J:set(A).",
		Hypotheses: []string{
			"I ⊆ R.carrier",
			"J ⊆ R.carrier",
		},
		Conclusion: "ideal_mul(R, I, J) = ideal_mul(R, J, I)",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], I, J *Expr[Set[A]], inclusions Fact) {
			commute := a.Have(
				"a member of I and a member of J lie in c, where the multiplication commutes",
				"∀x y:A. x ∈ I ∧ y ∈ J ⇒ x * y = y * x",
				BySets(inclusions, comm_monoid.CommOn.Read(comm_ring.MulMonoidOn.Read(ring))))
			products := a.Have(
				"so the products of I with J are the products of J with I",
				"{x * y | x:A, y:A | x ∈ I ∧ y ∈ J} = {y * x | y:A, x:A | y ∈ J ∧ x ∈ I}",
				BySets(commute))
			a.Show(
				"IJ and JI are the spans of that one set",
				Simp(Fwd(IdealMulDef)),
				By(products))
		}),
})}

// ColonIdeal — the members w of c with w * z in an ideal I, for z in c,
// form an ideal, the colon ideal (I : z): zero * z is zero; (u + v) * z
// is u * z + v * z, a sum of members of I; and (r * u) * z is
// r * (u * z), which I absorbs.
var ColonIdeal = colonIdealThm{family.Add(registry.ProofEntry{
	Name:    "ColonIdeal",
	Key:     "prop_aacc04a0280d3238",
	Reading: "z ∈ R.carrier is what lets the ring laws regroup the products with z.",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀I:set(A). ∀z:A.",
		Hypotheses: []string{
			"ring_ideal(R, I)",
			"z ∈ R.carrier",
		},
		Conclusion: "ring_ideal(R, {w:A | w ∈ R.carrier ∧ w * z ∈ I})",
	},
		func(
			a *Argument,
			ring comm_ring.CommRingFact[on.R],
			I *Expr[Set[A]],
			ideal Fact,
			z *Member[A, on.R],
		) {
			a.Do(Simp(Fwd(RingIdealDef)), SplitConjAll(
				Case(
					"the colon ideal lies in c",
					BySets()),
				Case(
					"zero lies in it, zero * z being zero",
					Derive(func(d *Argument) {
						inI := d.Have(
							"zero * z is zero, which lies in I",
							"R.zero * z ∈ I",
							By(Normalized, z, comm_ring.MulLeftZeroOn.Read(ring), ideal, IdealZero))
						d.Show(
							"and zero lies in c",
							By(inI, comm_ring.ZeroIn.Read(ring)))
					})),
				Case(
					"(u + v) * z is u * z + v * z, a sum of members of I",
					Derive(func(d *Argument) {
						d.FixAs[A]("u")
						d.FixAs[A]("v")
						members := d.Have(
							"u and v lie in c, with u * z and v * z in I",
							"u ∈ R.carrier ∧ u * z ∈ I ∧ v ∈ R.carrier ∧ v * z ∈ I",
							By(d.Assume()))
						distribute := d.Have(
							"(u + v) * z is u * z + v * z",
							"(u + v) * z = u * z + v * z",
							By(z, members, comm_ring.RightDistribOn.Read(ring)))
						sum := d.Have(
							"so it lies in I",
							"(u + v) * z ∈ I",
							distribute.Rw(),
							By(ideal, members, IdealAdd))
						d.Show(
							"and u + v lies in c",
							By(sum, members, comm_ring.AddIn.Read(ring)))
					})),
				Case(
					"(r * u) * z is r * (u * z), which I absorbs",
					Derive(func(d *Argument) {
						d.FixAs[A]("r")
						d.FixAs[A]("u")
						members := d.Have(
							"r and u lie in c, with u * z in I",
							"r ∈ R.carrier ∧ u ∈ R.carrier ∧ u * z ∈ I",
							By(d.Assume()))
						regroup := d.Have(
							"(r * u) * z is r * (u * z)",
							"(r * u) * z = r * (u * z)",
							By(z, members, comm_monoid.AssocOn.Read(comm_ring.MulMonoidOn.Read(ring))))
						absorbed := d.Have(
							"so it lies in I",
							"(r * u) * z ∈ I",
							regroup.Rw(),
							By(ideal, members, IdealMul))
						d.Show(
							"and r * u lies in c",
							By(absorbed, members, comm_ring.MulIn.Read(ring)))
					})),
			))
		}),
})}

// IdealMulAssoc — the product of subsets of c associates. Both sides are
// ideals (IdealMulIdeal), and each lies in the other by IdealMulLeast with
// one factor fixed. For z in K the colon ideal (I(JK) : z) is an ideal
// (ColonIdeal) holding each x * y of IJ's spanning products, since
// (x * y) * z = x * (y * z) with y * z in JK; so it holds IJ, and w * z
// lies in I(JK) for every w in IJ. For x in I the colon ideal ((IJ)K : x)
// holds each y * z, since (y * z) * x = (x * y) * z with x * y in IJ; so
// it holds JK, and x * v = v * x lies in (IJ)K for every v in JK.
var IdealMulAssoc = idealMulAssocThm{family.Add(registry.ProofEntry{
	Name: "IdealMulAssoc",
	Key:  "prop_a3ae708f30214575",
	Reading: "I, J and K inside R.carrier keep every product of the argument in " +
		"c, where the ring laws regroup it and the spans are ideals. The product is " +
		"a span, so no finite sum is taken: one factor is fixed at a time.",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀I J K:set(A).",
		Hypotheses: []string{
			"I ⊆ R.carrier",
			"J ⊆ R.carrier",
			"K ⊆ R.carrier",
		},
		Conclusion: "ideal_mul(R, ideal_mul(R, I, J), K) = ideal_mul(R, I, ideal_mul(R, J, K))",
	},
		func(
			a *Argument,
			R *Expr[module_record.RingOps[A]],
			ring comm_ring.CommRingFact[on.R],
			I, J, K *Expr[Set[A]],
			inclusions Fact,
		) {
			parts := a.Conjuncts(
				inclusions,
				"I lies in c",
				"J lies in c",
				"K lies in c")
			iInC, jInC, kInC := parts[0], parts[1], parts[2]
			mulMonoid := comm_ring.MulMonoidOn.Read(ring)
			ij, jk := a.TermAs[Set[A]]("ideal_mul(R, I, J)"), a.TermAs[Set[A]]("ideal_mul(R, J, K)")
			left := a.TermAs[Set[A]]("ideal_mul(R, ideal_mul(R, I, J), K)")
			right := a.TermAs[Set[A]]("ideal_mul(R, I, ideal_mul(R, J, K))")
			factors := a.Have(
				"IJ and JK are ideals",
				"ring_ideal(R, ideal_mul(R, I, J)) ∧ ring_ideal(R, ideal_mul(R, J, K))",
				By(inclusions, IdealMulIdeal.Read(ring)))
			factorsInC := a.Have(
				"so they lie in c",
				"ideal_mul(R, I, J) ⊆ R.carrier ∧ ideal_mul(R, J, K) ⊆ R.carrier",
				By(factors, IdealSubset))
			bothSides := a.Have(
				"so (IJ)K and I(JK) are ideals",
				"ring_ideal(R, ideal_mul(R, ideal_mul(R, I, J), K)) ∧ "+
					"ring_ideal(R, ideal_mul(R, I, ideal_mul(R, J, K)))",
				By(inclusions, factorsInC, IdealMulIdeal.Read(ring)))
			sides := a.Conjuncts(
				bothSides,
				"(IJ)K is an ideal",
				"I(JK) is an ideal")
			leftIdeal, rightIdeal := sides[0], sides[1]

			// Fixing the right factor z: the colon ideal (I(JK) : z) holds IJ.
			leftProducts := a.Have(
				"w * z lies in I(JK) for w in IJ and z in K",
				"∀w z:A. w ∈ ideal_mul(R, I, J) ∧ z ∈ K ⇒ w * z ∈ ideal_mul(R, I, ideal_mul(R, J, K))",
				Derive(func(b *Argument) {
					b.FixAs[A]("w")
					z := b.FixAs[A]("z")
					given := b.Assume()
					zIn := b.Have(
						"z lies in c",
						"z ∈ R.carrier",
						BySets(kInC, given))
					colonSet := b.TermAs[Set[A]]("{u:A | u ∈ R.carrier ∧ u * z ∈ ideal_mul(R, I, ideal_mul(R, J, K))}")
					colon := b.Have(
						"the colon ideal (I(JK) : z) is an ideal",
						"ring_ideal(R, {u:A | u ∈ R.carrier ∧ u * z ∈ ideal_mul(R, I, ideal_mul(R, J, K))})",
						By(zIn, rightIdeal, ColonIdeal.Read(ring)))
					generators := b.Have(
						"it holds each x * y, as (x * y) * z is x * (y * z) with y * z in JK",
						Statement{
							Binders: "∀x y:A.",
							Hypotheses: []string{
								"x ∈ I",
								"y ∈ J",
							},
							Conclusion: "x * y ∈ {u:A | u ∈ R.carrier ∧ u * z ∈ ideal_mul(R, I, ideal_mul(R, J, K))}",
						},
						Derive(func(c *Argument) {
							x := c.FixAs[A]("x")
							y := c.FixAs[A]("y")
							members := c.Assume()
							memberships := c.Have(
								"x and y lie in c",
								"x ∈ R.carrier ∧ y ∈ R.carrier",
								BySets(members, iInC, jInC))
							inner := c.Have(
								"y * z lies in JK",
								"y * z ∈ ideal_mul(R, J, K)",
								By(members, given, IdealMulHolds.At(R, J, K, y, z)))
							triple := c.Have(
								"so x * (y * z) lies in I(JK)",
								"x * (y * z) ∈ ideal_mul(R, I, ideal_mul(R, J, K))",
								By(members, inner, IdealMulHolds.At(R, I, jk, x, c.TermAs[A]("y * z"))))
							regroup := c.Have(
								"(x * y) * z is x * (y * z)",
								"(x * y) * z = x * (y * z)",
								By(memberships, zIn, comm_monoid.AssocOn.Read(mulMonoid)))
							moved := c.Have(
								"so (x * y) * z lies in I(JK)",
								"(x * y) * z ∈ ideal_mul(R, I, ideal_mul(R, J, K))",
								By(Normalized, regroup, triple))
							c.Show(
								"and x * y lies in c",
								By(moved, memberships, comm_ring.MulIn.Read(ring)))
						}))
					within := b.Have(
						"so the colon ideal holds IJ",
						"ideal_mul(R, I, J) ⊆ {u:A | u ∈ R.carrier ∧ u * z ∈ ideal_mul(R, I, ideal_mul(R, J, K))}",
						By(colon, generators, IdealMulLeast.At(R, I, J, colonSet)))
					b.Show(
						"and w * z lies in I(JK)",
						BySets(within, given))
				}))

			// Fixing the left factor x: the colon ideal ((IJ)K : x) holds JK.
			rightProducts := a.Have(
				"x * v lies in (IJ)K for x in I and v in JK",
				"∀x v:A. x ∈ I ∧ v ∈ ideal_mul(R, J, K) ⇒ x * v ∈ ideal_mul(R, ideal_mul(R, I, J), K)",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					b.FixAs[A]("v")
					given := b.Assume()
					memberships := b.Have(
						"x and v lie in c",
						"x ∈ R.carrier ∧ v ∈ R.carrier",
						BySets(given, iInC, factorsInC))
					colonSet := b.TermAs[Set[A]]("{u:A | u ∈ R.carrier ∧ u * x ∈ ideal_mul(R, ideal_mul(R, I, J), K)}")
					colon := b.Have(
						"the colon ideal ((IJ)K : x) is an ideal",
						"ring_ideal(R, {u:A | u ∈ R.carrier ∧ u * x ∈ ideal_mul(R, ideal_mul(R, I, J), K)})",
						By(memberships, leftIdeal, ColonIdeal.Read(ring)))
					generators := b.Have(
						"it holds each y * z, as (y * z) * x is (x * y) * z with x * y in IJ",
						Statement{
							Binders: "∀y z:A.",
							Hypotheses: []string{
								"y ∈ J",
								"z ∈ K",
							},
							Conclusion: "y * z ∈ {u:A | u ∈ R.carrier ∧ u * x ∈ ideal_mul(R, ideal_mul(R, I, J), K)}",
						},
						Derive(func(c *Argument) {
							y := c.FixAs[A]("y")
							z := c.FixAs[A]("z")
							members := c.Assume()
							yzIn := c.Have(
								"y and z lie in c",
								"y ∈ R.carrier ∧ z ∈ R.carrier",
								BySets(members, jInC, kInC))
							inner := c.Have(
								"x * y lies in IJ",
								"x * y ∈ ideal_mul(R, I, J)",
								By(given, members, IdealMulHolds.At(R, I, J, x, y)))
							triple := c.Have(
								"so (x * y) * z lies in (IJ)K",
								"(x * y) * z ∈ ideal_mul(R, ideal_mul(R, I, J), K)",
								By(inner, members, IdealMulHolds.At(R, ij, K, c.TermAs[A]("x * y"), z)))
							regroup := c.Have(
								"(y * z) * x is (x * y) * z",
								"(y * z) * x = (x * y) * z",
								ByArith(ring, memberships, yzIn))
							moved := c.Have(
								"so (y * z) * x lies in (IJ)K",
								"(y * z) * x ∈ ideal_mul(R, ideal_mul(R, I, J), K)",
								By(Normalized, regroup, triple))
							c.Show(
								"and y * z lies in c",
								By(moved, yzIn, comm_ring.MulIn.Read(ring)))
						}))
					within := b.Have(
						"so the colon ideal holds JK",
						"ideal_mul(R, J, K) ⊆ {u:A | u ∈ R.carrier ∧ u * x ∈ ideal_mul(R, ideal_mul(R, I, J), K)}",
						By(colon, generators, IdealMulLeast.At(R, J, K, colonSet)))
					absorbed := b.Have(
						"so v * x lies in (IJ)K",
						"v * x ∈ ideal_mul(R, ideal_mul(R, I, J), K)",
						BySets(within, given))
					b.Show(
						"x * v is v * x, so it lies in (IJ)K",
						By(Normalized, memberships, comm_monoid.CommOn.Read(mulMonoid), absorbed))
				}))

			below := a.Have(
				"(IJ)K lies in I(JK)",
				"ideal_mul(R, ideal_mul(R, I, J), K) ⊆ ideal_mul(R, I, ideal_mul(R, J, K))",
				By(rightIdeal, leftProducts, IdealMulLeast.At(R, ij, K, right)))
			above := a.Have(
				"and I(JK) lies in (IJ)K",
				"ideal_mul(R, I, ideal_mul(R, J, K)) ⊆ ideal_mul(R, ideal_mul(R, I, J), K)",
				By(leftIdeal, rightProducts, IdealMulLeast.At(R, I, jk, left)))
			a.Show(
				"the two inclusions are the equation",
				By(below, above, set_order.SubsetAntisym.At(left, right)))
		}),
})}

// IdealMulOne — the carrier is the unit of the product: cI = I for an
// ideal I. The ideal I absorbs every r * x with r in c, so it holds cI
// (IdealMulLeast); and each x of I is one * x, one of the products
// spanning cI.
var IdealMulOne = idealMulOneThm{family.Add(registry.ProofEntry{
	Name: "IdealMulOne",
	Key:  "prop_3bd89c00e8a93a11",
	Reading: "That I is an ideal is load-bearing both ways: absorption puts " +
		"cI inside I, and I ⊆ R.carrier puts x = one * x among the products.",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀I:set(A).",
		Hypotheses: []string{
			"ring_ideal(R, I)",
		},
		Conclusion: "ideal_mul(R, R.carrier, I) = I",
	},
		func(
			a *Argument,
			R *Expr[module_record.RingOps[A]],
			ring comm_ring.CommRingFact[on.R],
			I *Expr[Set[A]],
			ideal Fact,
		) {
			carrier := a.TermAs[Set[A]]("R.carrier")
			product := a.TermAs[Set[A]]("ideal_mul(R, R.carrier, I)")
			below := a.Have(
				"I absorbs each r * x with r in c, so it holds cI",
				"ideal_mul(R, R.carrier, I) ⊆ I",
				By(ideal, IdealMul, IdealMulLeast.At(R, carrier, I, I)))
			above := a.Have(
				"each x of I is one * x, a product of c with I",
				"I ⊆ ideal_mul(R, R.carrier, I)",
				Simp(Fwd(set_basic.SubsetDef)),
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					inI := b.Assume()
					xIn := b.Have(
						"x lies in c",
						"x ∈ R.carrier",
						By(ideal, inI, IdealSubset, set_basic.SubsetDef))
					held := b.Have(
						"one * x lies in cI, one lying in c",
						"R.one * x ∈ ideal_mul(R, R.carrier, I)",
						By(inI, comm_ring.OneIn.Read(ring), IdealMulHolds.At(R, carrier, I, b.TermAs[A]("R.one"), x)))
					b.Show(
						"and one * x is x",
						By(Normalized, xIn, comm_monoid.LeftIdentityOn.Read(comm_ring.MulMonoidOn.Read(ring)), held))
				}))
			a.Show(
				"each lies in the other",
				By(below, above, set_order.SubsetAntisym.At(product, I)))
		}),
})}

// IdealsCommMonoid — the ideals of a commutative ring form a commutative
// monoid under the product, with the carrier as unit: the carrier is an
// ideal (CarrierIdeal), a product of ideals is an ideal (IdealMulIdeal),
// and on ideals, which lie in the carrier, the product commutes
// (IdealMulComm), associates (IdealMulAssoc) and has the carrier as unit
// (IdealMulOne).
var IdealsCommMonoid = idealsCommMonoidThm{family.Add(registry.ProofEntry{
	Name: "IdealsCommMonoid",
	Key:  "prop_38ccf46f59905755",
	Build: comm_ring.CommRingOn.Law("comm_monoid_on({I:set(A) | ring_ideal(R, I)}, "+
		"    λI:set(A). λJ:set(A). ideal_mul(R, I, J), "+
		"    R.carrier)",
		func(a *Argument, ring comm_ring.CommRingFact[on.R]) {
			a.Do(Unfold(comm_monoid.CommMonoidOn), SplitConjAll(
				Case(
					"the carrier is an ideal",
					By(CarrierIdeal.Read(ring))),
				Case(
					"a product of ideals is an ideal, ideals lying in the carrier",
					By(IdealSubset, IdealMulIdeal.Read(ring))),
				Case(
					"the product of ideals commutes",
					By(IdealSubset, IdealMulComm.Read(ring))),
				Case(
					"the product of ideals associates",
					By(IdealSubset, IdealMulAssoc.Read(ring))),
				Case(
					"the carrier is the unit of the product",
					By(IdealMulOne.Read(ring))),
			))
		}),
})}

// IdealPowZero — the zeroth power of an ideal is the whole carrier.
var IdealPowZero = idealPowZeroThm{family.Add(registry.ProofEntry{
	Name: "IdealPowZero",
	Key:  "prop_9a5f97b1460645a0",
	Build: family.Theorem("∀R:ring_ops(A). ∀I:set(A). ideal_pow(R, I, 0) = R.carrier",
		func(a *Argument, _ *Expr[module_record.RingOps[A]], _ *Expr[Set[A]]) {
			a.Show(
				"the zeroth power in the monoid is its unit",
				Simp(Fwd(IdealPowDef), Fwd(comm_monoid.MonoidPowDef)),
				Basic())
		}),
})}

// IdealPowSuc — the next power multiplies by the ideal on the left.
var IdealPowSuc = idealPowSucThm{family.Add(registry.ProofEntry{
	Name: "IdealPowSuc",
	Key:  "prop_3bee4663d9e352bd",
	Build: family.Theorem("∀R:ring_ops(A). ∀I:set(A). ∀n:num. "+
		"    ideal_pow(R, I, suc(n)) = ideal_mul(R, I, ideal_pow(R, I, n))",
		func(a *Argument, _ *Expr[module_record.RingOps[A]], _ *Expr[Set[A]], _ *Expr[Nat]) {
			a.Show(
				"the monoid's power unfolds one step",
				Simp(Fwd(IdealPowDef), Fwd(comm_monoid.MonoidPowDef)),
				Basic())
		}),
})}

// IdealPowIdeal — a power of an ideal is an ideal: ideals form a monoid
// under the product.
var IdealPowIdeal = idealPowIdealThm{family.Add(registry.ProofEntry{
	Name: "IdealPowIdeal",
	Key:  "prop_fee0ed6ec1cadc85",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀I:set(A). ∀n:num.",
		Hypotheses: []string{
			"ring_ideal(R, I)",
		},
		Conclusion: "ring_ideal(R, ideal_pow(R, I, n))",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], I *Expr[Set[A]], n *Expr[Nat], ideal Fact) {
			a.Show(
				"a power of a member of the monoid of ideals is a member",
				Simp(Fwd(IdealPowDef)),
				BySets(ideal, comm_monoid.PowIn.Read(IdealsCommMonoid.Read(ring)).AsFact().At(I, n)))
		}),
})}

// IdealPowAdd — a power at a sum of exponents is the product of the two
// powers.
var IdealPowAdd = idealPowAddThm{family.Add(registry.ProofEntry{
	Name: "IdealPowAdd",
	Key:  "prop_8f278803ba5c6b35",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀I:set(A). ∀m n:num.",
		Hypotheses: []string{
			"ring_ideal(R, I)",
		},
		Conclusion: "ideal_pow(R, I, m + n) = ideal_mul(R, ideal_pow(R, I, m), ideal_pow(R, I, n))",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], I *Expr[Set[A]], m, n *Expr[Nat], ideal Fact) {
			a.Show(
				"the monoid of ideals adds exponents",
				Simp(Fwd(IdealPowDef)),
				BySets(ideal, comm_monoid.PowAddOn.Read(IdealsCommMonoid.Read(ring)).AsFact().At(I, m, n)))
		}),
})}

// ---------------------------------------------------------------------------
// Prime and maximal ideals
// ---------------------------------------------------------------------------

// MaximalIsPrime — a maximal ideal is prime. If x * y lies in m and x
// does not, x is a unit modulo m (MaximalUnitModulo): v * x - one lies
// in m for some v in c. Then y = v * (x * y) + (-y) * (v * x - one), and
// absorption and the sum keep it in m.
var MaximalIsPrime = maximalIsPrimeThm{family.Add(registry.ProofEntry{
	Name:    "MaximalIsPrime",
	Key:     "prop_c3f2f944fa01e2d7",
	Reading: "Vacuous in the zero ring, which has no maximal ideal.",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀m:set(A).",
		Hypotheses: []string{
			"maximal_ideal(R, m)",
		},
		Conclusion: "prime_ideal(R, m)",
	},
		func(
			a *Argument,
			R *Expr[module_record.RingOps[A]],
			ring comm_ring.CommRingFact[on.R],
			m *Expr[Set[A]],
			maximal Fact,
		) {
			ideal := a.Have(
				"m is an ideal",
				"ring_ideal(R, m)",
				By(maximal, MaximalIdealIdeal))
			a.Do(Simp(Fwd(PrimeIdealDef)), SplitConjAll(
				Case(
					"m is an ideal",
					By(ideal)),
				Case(
					"m does not hold one",
					By(maximal, MaximalIdealProper)),
				Case(
					"of two members of c whose product lies in m, one lies in m",
					Derive(func(d *Argument) {
						x := d.FixAs[A]("x")
						d.FixAs[A]("y")
						given := d.Conjuncts(
							d.Assume(),
							"x lies in c",
							"y lies in c",
							"x * y lies in m")
						xIn, yIn, product := given[0], given[1], given[2]
						xOutside := d.Unless(
							d.Term("x ∈ m"),
							"x lying in m settles it",
							Given(func(e *Argument, xInM Fact) {
								e.Show(
									"x is the factor in m",
									By(xInM))
							}))

						// x is a unit modulo m: v * x - one lies in m for some v in c.
						_, inverse := d.UnpackAs[A](
							GroupPremises(maximal, xOutside, MaximalUnitModulo.Read(ring).At(m, d.MemberOf[on.R](x, xIn))), "v")
						inverses := d.Conjuncts(
							inverse,
							"v lies in c",
							"v * x - one lies in m")
						vIn, remainder := inverses[0], inverses[1]

						// y = v * (x * y) + (-y) * (v * x - one), which lies in m.
						yForm := d.Have(
							"y is v * (x * y) + (-y) * (v * x - one)",
							"y = v * (x * y) + (-y) * (v * x - R.one)",
							ByArith(ring, vIn, xIn, yIn))
						sumInM := d.Have(
							"v * (x * y) lies in m by absorption, (-y) * (v * x - one) too, -y lying in c, and so their sum",
							"v * (x * y) + (-y) * (v * x - R.one) ∈ m",
							By(ideal, vIn, product, yIn, remainder, ring, comm_ring.NegIn, IdealAdd, IdealMul))
						d.Show(
							"so y is the factor in m",
							By(Normalized, yForm, sumInM))
					})),
			))
		}),
})}

// MaximalComplement — a maximal ideal and one more member of c outside
// it generate the whole ring: their span is an ideal above m that is not
// m (SpanInsertAbove), so maximality puts one in it, and an ideal holding
// one is c (IdealOneIff).
var MaximalComplement = maximalComplementThm{family.Add(registry.ProofEntry{
	Name: "MaximalComplement",
	Key:  "prop_aea42358d3f6e32c",
	Reading: "a ∉ m is load-bearing: at a ∈ m the span is m itself. a ∈ " +
		"R.carrier keeps insert(a, m) inside R.carrier, so the span is an ideal " +
		"and not ⋂∅ = 𝕌. Vacuous in the zero ring, which has no maximal ideal.",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀m:set(A). ∀a:A.",
		Hypotheses: []string{
			"maximal_ideal(R, m)",
			"a ∈ R.carrier",
			"a ∉ m",
		},
		Conclusion: "ideal_span(R, insert(a, m)) = R.carrier",
	},
		func(
			arg *Argument,
			R *Expr[module_record.RingOps[A]],
			ring comm_ring.CommRingFact[on.R],
			m *Expr[Set[A]],
			a *Expr[A],
			given Fact,
		) {
			parts := arg.Conjuncts(
				given,
				"m is maximal",
				"a lies in the carrier",
				"a lies outside m")
			maximal, aIn, outside := parts[0], parts[1], parts[2]
			mInCarrier := arg.Have(
				"m is an ideal, so it lies in the carrier",
				"m ⊆ R.carrier",
				By(maximal, MaximalIdealIdeal.At(R, m), IdealSubset.At(R, m)))
			span := arg.TermAs[Set[A]]("ideal_span(R, insert(a, m))")
			adjoined := arg.Conjuncts(
				GroupPremises(mInCarrier, SpanInsertAbove.Read(ring).At(m, arg.MemberOf[on.R](a, aIn))),
				"the span of m with a is an ideal",
				"holding m",
				"and a",
				"and not m when a lies outside m")
			spanIdeal, above, distinctOutside := adjoined[0], adjoined[1], adjoined[3]
			either := arg.Have(
				"maximality makes the span m or an ideal holding one",
				"ideal_span(R, insert(a, m)) = m ∨ R.one ∈ ideal_span(R, insert(a, m))",
				By(maximal, spanIdeal, above, MaximalIdealMaximal.At(R, m, span)))
			oneIn := arg.Have(
				"a lies outside m, so the span differs from m, and the strict extension holds one",
				"R.one ∈ ideal_span(R, insert(a, m))",
				By(either, distinctOutside, outside))
			arg.Show(
				"an ideal holding one is the whole carrier",
				By(spanIdeal, oneIn, IdealOneIff.Read(ring).At(span)))
		}),
})}

// MaximalUnitModulo — a member of c outside a maximal ideal m is a unit
// modulo m: some v in c has v * a - one in m. The span of m with a is c
// (MaximalComplement), so it holds one, which is then b * a + t with t
// in m (SpanInsertIdeal), and b * a - one is -t, in m.
var MaximalUnitModulo = maximalUnitModuloThm{family.Add(registry.ProofEntry{
	Name: "MaximalUnitModulo",
	Key:  "prop_c3752a6ad67e10f6",
	Reading: "The element form of the inverse of a + m in the field R.carrier/m " +
		"(quotient_ring's QuotientInverseExists), with no coset chosen. a ∉ m is " +
		"load-bearing: at a ∈ m, v * a lies in m and v * a - R.one in m would put R.one in m.",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀m:set(A). ∀a:A.",
		Hypotheses: []string{
			"maximal_ideal(R, m)",
			"a ∈ R.carrier",
			"a ∉ m",
		},
		Conclusion: "∃v:A. v ∈ R.carrier ∧ v * a - R.one ∈ m",
	},
		func(
			arg *Argument,
			R *Expr[module_record.RingOps[A]],
			ring comm_ring.CommRingFact[on.R],
			m *Expr[Set[A]],
			a *Expr[A],
			given Fact,
		) {
			parts := arg.Conjuncts(
				given,
				"m is maximal",
				"a lies in the carrier",
				"a lies outside m")
			maximal, aIn, outside := parts[0], parts[1], parts[2]
			aMember := arg.MemberOf[on.R](a, aIn)
			ideal := arg.Have(
				"m is an ideal",
				"ring_ideal(R, m)",
				By(maximal, MaximalIdealIdeal.At(R, m)))
			wholeSpan := arg.Have(
				"adjoining a to m generates the whole carrier",
				"ideal_span(R, insert(a, m)) = R.carrier",
				By(maximal, outside, MaximalComplement.Read(ring).At(m, aMember)))
			oneInSpan := arg.Have(
				"the span therefore holds one",
				"R.one ∈ ideal_span(R, insert(a, m))",
				BySets(wholeSpan, comm_ring.OneIn.Read(ring)))
			spanForm := arg.Have(
				"the span consists of multiples of a plus members of m",
				"ideal_span(R, insert(a, m)) = {b * a + t | b:A, t:A | b ∈ R.carrier ∧ t ∈ m}",
				By(ideal, aIn, SpanInsertIdeal.Read(ring).At(m, aMember)))
			b, t, oneForm := arg.Obtain2As[A, A](
				"write one as b times a plus a remainder in m",
				"∃b t:A. b ∈ R.carrier ∧ t ∈ m ∧ R.one = b * a + t",
				BySets(spanForm, oneInSpan))
			terms := arg.Conjuncts(
				oneForm,
				"b lies in the carrier",
				"t lies in m",
				"one is b times a plus t")
			bIn, tInM, oneSum := terms[0], terms[1], terms[2]
			tInC := arg.Have(
				"the remainder lies in m, which lies in the carrier",
				"t ∈ R.carrier",
				BySets(ideal, IdealSubset.At(R, m), tInM))
			negInM := arg.Have(
				"the negative remainder lies in m",
				"-t ∈ m",
				By(ideal, tInM, IdealNeg.Read(ring).At(m, t)))
			difference := arg.Have(
				"subtracting one leaves the negative remainder",
				"b * a - R.one = -t",
				ByArith(ring, bIn, aIn, tInC, oneSum))
			arg.Take(b)
			arg.Show(
				"b is an inverse of a modulo m",
				By(bIn, negInM, difference))
		}),
})}

// MaximalPowerUnitModulo — an element outside a maximal ideal is a unit
// modulo every power: a proper ideal containing the power and the element
// would lie in a maximal ideal containing the original maximal ideal.
var MaximalPowerUnitModulo = maximalPowerUnitModuloThm{family.Add(registry.ProofEntry{
	Name: "MaximalPowerUnitModulo",
	Key:  "prop_9cc718ba9bd4f653",
	Build: family.Theorem(Statement{
		Binders:    "∀R:comm_ring_on(A). ∀m:set(A). ∀u:A. ∀n:num.",
		Hypotheses: []string{"maximal_ideal(R, m)", "u ∈ R.carrier", "u ∉ m"},
		Conclusion: "∃a t:A. a ∈ R.carrier ∧ t ∈ ideal_pow(R, m, n) ∧ R.one = a * u + t",
	}, func(
		a *Argument,
		R comm_ring.CommRingFact[on.R],
		m *Expr[Set[A]],
		u *Expr[A],
		n *Expr[Nat],
		h Fact,
	) {
		parts := a.Conjuncts(
			h,
			"m is maximal",
			"u belongs to the ring",
			"u lies outside m")
		maximal, uIn, outside := parts[0], parts[1], parts[2]
		um := a.MemberOf[on.R](u, uIn)
		r := a.TermAs[RingOps[A]]("R")
		idealM := a.Have(
			"m is an ideal",
			"ring_ideal(R, m)",
			By(maximal, MaximalIdealIdeal.At(r, m)))
		power := a.TermAs[Set[A]]("ideal_pow(R, m, n)")
		powerIdeal := a.Have(
			"the maximal-ideal power is an ideal",
			"ring_ideal(R, ideal_pow(R, m, n))",
			By(idealM, IdealPowIdeal.Read(R).At(m, n)))
		J, spanDef := a.LetAs[Set[A]]("J", "ideal_span(R, insert(u, ideal_pow(R, m, n)))")
		spanFacts := a.Have(
			"adjoining u gives an ideal containing u and the power",
			"ring_ideal(R, J) ∧ ideal_pow(R, m, n) ⊆ J ∧ u ∈ J",
			Simp(Fwd(spanDef)),
			By(powerIdeal, uIn, IdealSubset.At(r, power), SpanInsertAbove.Read(R).At(power, um)))
		oneIn := a.Have(
			"adjoining u to the power generates one",
			"R.one ∈ J",
			Derive(func(b *Argument) {
				notOne := b.SupposeNot()
				P, above := b.ObtainAs[Set[A]](
					"place the supposedly proper ideal in a maximal ideal",
					"∃P:set(A). maximal_ideal(R, P) ∧ J ⊆ P",
					By(notOne, spanFacts, ExistsMaximalAbove.Read(R).At(J)))
				prime := b.Have(
					"the containing maximal ideal is a proper prime ideal",
					"prime_ideal(R, P) ∧ ring_ideal(R, P) ∧ R.one ∉ P",
					By(above, MaximalIsPrime.Read(R).At(P), MaximalIdealIdeal.At(r, P), MaximalIdealProper.At(r, P)))
				powerForcesBase := b.Have(
					"a prime containing a power of m contains m",
					"∀j:num. ideal_pow(R, m, j) ⊆ P ⇒ m ⊆ P",
					Derive(func(c *Argument) {
						c.Induct("j")
						c.Base(
							"a proper prime cannot contain the zeroth power",
							Simp(Fwd(IdealPowZero)),
							BySets(prime, comm_ring.OneIn.Read(R)))
						c.Step(
							"a prime containing the product contains m or the preceding power",
							func(d *Argument, ih Fact) {
								d.Do(Simp(Fwd(IdealPowSuc)))
								productIn := d.Assume()
								j := d.TermAs[Nat]("j")
								previous := d.TermAs[Set[A]]("ideal_pow(R, m, j)")
								previousIdeal := d.Have(
									"the preceding power is an ideal",
									"ring_ideal(R, ideal_pow(R, m, j))",
									By(idealM, IdealPowIdeal.Read(R).At(m, j)))
								d.Show(
									"the induction hypothesis handles the preceding-power alternative",
									By(idealM, previousIdeal, productIn, ih, prime, PrimeIdealMulSubset.At(r, P, m, previous)))
							})
					}))
				mInP := b.Have(
					"P contains m",
					"m ⊆ P",
					BySets(powerForcesBase.At(n), spanFacts, above))
				b.Show(
					"maximality identifies P with m, contradicting the presence of u",
					BySets(outside, maximal, prime, above, spanFacts, mInP, MaximalIdealMaximal.At(r, m, P)))
			}))
		a.Show(
			"the span expression for one gives an inverse modulo the power",
			BySets(oneIn, spanDef, powerIdeal, uIn, SpanInsertIdeal.Read(R).At(power, um)))
	}),
})}

// ExistsMaximalAvoiding — an ideal missing a set S lies in an ideal that is
// maximal among the ideals missing S, by Zorn's lemma on the family F of
// the ideals holding I and missing S. F holds I. The union of a non-empty
// chain of members of F is an ideal (ChainUnionIdeal); it holds I, as any
// member of the chain does; and it misses S, since a member of S in the
// union would lie in a member of the chain. A member m of F that no other
// member contains is the ideal sought: an ideal above m that misses S
// holds I through m, so it is a member of F, and it is m.
var ExistsMaximalAvoiding = existsMaximalAvoidingThm{family.Add(registry.ProofEntry{
	Name: "ExistsMaximalAvoiding",
	Key:  "prop_2070740e699bbdcf",
	Reading: "Needs no ring. I ∩ S = ∅ is load-bearing: it is what puts I in the family " +
		"Zorn's lemma is applied to. Under a ring, with S = ∅ the ideal found is c itself.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀I S:set(A).",
		Hypotheses: []string{
			"ring_ideal(R, I)",
			"I ∩ S = ∅",
		},
		Conclusion: "∃m:set(A). " +
			"    ring_ideal(R, m) ∧ " +
			"    I ⊆ m ∧ " +
			"    m ∩ S = ∅ ∧ " +
			"    (∀J:set(A). ring_ideal(R, J) ∧ m ⊆ J ∧ J ∩ S = ∅ ⇒ J = m)",
	},
		func(a *Argument, R *Expr[module_record.RingOps[A]], I, S *Expr[Set[A]], hypotheses Fact) {
			parts := a.Conjuncts(
				hypotheses,
				"I is an ideal",
				"I misses S")
			ideal, missesS := parts[0], parts[1]

			// The ideals holding I and missing S.
			F, familyDef := a.LetAs[Set[Set[A]]]("F", "{J:set(A) | ring_ideal(R, J) ∧ I ⊆ J ∧ J ∩ S = ∅}")
			inF := a.Have(
				"the members of F are the ideals holding I and missing S",
				"∀J:set(A). J ∈ F ⇔ ring_ideal(R, J) ∧ I ⊆ J ∧ J ∩ S = ∅",
				BySets(familyDef))
			iInF := a.Have(
				"I is a member of F",
				"I ∈ F",
				By(ideal, missesS, set_order.SubsetRefl.At(I), inF.At(I)))
			nonEmpty := a.Have(
				"so F is not empty",
				"F ≠ ∅",
				By(Normalized, iInF, set_basic.MemberNotEmpty.At(F)))

			closedUnderChainUnions := a.Have(
				"F contains the union of each of its non-empty chains",
				"∀G:set(set(A)). G ⊆ F ∧ G ≠ ∅ ∧ (∀s t:set(A). s ∈ G ∧ t ∈ G ⇒ s ⊆ t ∨ t ⊆ s) ⇒ ⋃G ∈ F",
				Derive(func(b *Argument) {
					G := b.FixAs[Set[Set[A]]]("G")
					union := b.TermAs[Set[A]]("⋃G")
					about := b.Conjuncts(
						b.Assume(),
						"G is a part of F",
						"G is not empty",
						"any two members of G are comparable")
					partOfF, gNonEmpty, gIsChain := about[0], about[1], about[2]
					inFamily := b.Unfolded(partOfF, set_basic.SubsetDef)
					members := b.Have(
						"each member of G is an ideal holding I and missing S",
						"∀J:set(A). J ∈ G ⇒ ring_ideal(R, J) ∧ I ⊆ J ∧ J ∩ S = ∅",
						b.ForEach(func(J *Expr[Set[A]]) Action {
							return By(inFamily.At(J), inF.At(J))
						}))
					unionIdeal := b.Have(
						"the union of G is an ideal, G being a non-empty chain of ideals",
						"ring_ideal(R, ⋃G)",
						By(members, gNonEmpty, gIsChain, ChainUnionIdeal.At(R, G)))
					g, gInG := b.ObtainAs[Set[A]](
						"G has a member g",
						"∃g:set(A). g ∈ G",
						By(gNonEmpty, set_basic.MemberNotEmpty.At(G)))
					holdsI := b.Have(
						"I lies in g, and g in the union",
						"I ⊆ ⋃G",
						By(
							gInG,
							members.At(g),
							set_order.MemberSubsetUnions.At(G, g),
							set_order.SubsetTrans.At(I, g, union)))
					unionMisses := b.Have(
						"a member of S in the union would lie in a member of G, which misses S",
						"⋃G ∩ S = ∅",
						BySets(members))
					b.Show(
						"so the union is an ideal holding I and missing S: a member of F",
						By(unionIdeal, holdsI, unionMisses, inF.At(union)))
				}))

			m, atM := a.ObtainAs[Set[A]](
				"so F has a member m that no other member contains: Zorn's lemma",
				"∃m:set(A). m ∈ F ∧ (∀s:set(A). s ∈ F ∧ m ⊆ s ⇒ s = m)",
				By(nonEmpty, closedUnderChainUnions, order.ZornFamily.At(F)))
			aboutM := a.Conjuncts(
				atM,
				"m is a member of F",
				"every member of F that contains m is m")
			mInF, maximalInFamily := aboutM[0], aboutM[1]
			mAvoids := a.Have(
				"m is an ideal holding I and missing S",
				"ring_ideal(R, m) ∧ I ⊆ m ∧ m ∩ S = ∅",
				By(mInF, inF.At(m)))
			maximal := a.Have(
				"an ideal above m that misses S is m",
				"∀J:set(A). ring_ideal(R, J) ∧ m ⊆ J ∧ J ∩ S = ∅ ⇒ J = m",
				Derive(func(b *Argument) {
					J := b.FixAs[Set[A]]("J")
					aboutJ := b.Assume()
					b.Show(
						"J holds I through m, so it is a member of F, and so it is m",
						By(aboutJ, mAvoids, set_order.SubsetTrans.At(I, m, J), inF.At(J), maximalInFamily.At(J)))
				}))
			a.Take(m)
			a.Show(
				"m is an ideal holding I, missing S, and maximal among the ideals missing S",
				By(mAvoids, maximal))
		}),
})}

// ExistsMaximalAbove — every proper ideal lies in a maximal ideal. A
// proper ideal I misses {one}, so it lies in an ideal m that is maximal
// among the ideals missing {one} (ExistsMaximalAvoiding). That m is a
// maximal ideal: it does not hold one, and an ideal above m that does not
// hold one misses {one}, so it is m.
var ExistsMaximalAbove = existsMaximalAboveThm{family.Add(registry.ProofEntry{
	Name: "ExistsMaximalAbove",
	Key:  "prop_32723a417c2cbea1",
	Reading: "The ring hypothesis is idle — ExistsMaximalAvoiding and the definition of a " +
		"maximal ideal need none; the statement is made over a ring, where maximal ideals are wanted.",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀I:set(A).",
		Hypotheses: []string{
			"ring_ideal(R, I)",
			"R.one ∉ I",
		},
		Conclusion: "∃m:set(A). maximal_ideal(R, m) ∧ I ⊆ m",
	},
		func(
			a *Argument,
			R *Expr[module_record.RingOps[A]],
			_ comm_ring.CommRingFact[on.R],
			I *Expr[Set[A]],
			hypotheses Fact,
		) {
			parts := a.Conjuncts(
				hypotheses,
				"I is an ideal",
				"I does not hold one")
			ideal, proper := parts[0], parts[1]
			missesOne := a.Have(
				"so I misses {one}",
				"I ∩ {R.one} = ∅",
				BySets(proper))
			m, atM := a.ObtainAs[Set[A]](
				"so I lies in an ideal m maximal among the ideals missing {one}",
				"∃m:set(A). "+
					"    ring_ideal(R, m) ∧ "+
					"    I ⊆ m ∧ "+
					"    m ∩ {R.one} = ∅ ∧ "+
					"    (∀J:set(A). ring_ideal(R, J) ∧ m ⊆ J ∧ J ∩ {R.one} = ∅ ⇒ J = m)",
				By(ExistsMaximalAvoiding.At(R, I, a.TermAs[Set[A]]("{R.one}")), ideal, missesOne))
			mParts := a.Conjuncts(
				atM,
				"m is an ideal",
				"m holds I",
				"m misses {one}",
				"an ideal above m missing {one} is m")
			mIdeal, holdsI, mMisses, maximalAvoidingOne := mParts[0], mParts[1], mParts[2], mParts[3]
			mProper := a.Have(
				"so m does not hold one",
				"R.one ∉ m",
				BySets(mMisses))
			maximal := a.Have(
				"an ideal above m is m or holds one",
				"∀J:set(A). ring_ideal(R, J) ∧ m ⊆ J ⇒ J = m ∨ R.one ∈ J",
				Derive(func(b *Argument) {
					J := b.FixAs[Set[A]]("J")
					aboutJ := b.Assume()
					notOne := b.Unless(
						b.Term("R.one ∈ J"),
						"J holding one settles it",
						Given(func(e *Argument, oneIn Fact) {
							e.Show(
								"J holds one",
								By(oneIn))
						}))
					jMisses := b.Have(
						"not holding one, J misses {one}",
						"J ∩ {R.one} = ∅",
						BySets(notOne))
					b.Show(
						"so J, an ideal above m missing {one}, is m",
						By(maximalAvoidingOne.At(J), aboutJ, jMisses))
				}))
			a.Take(m)
			a.Show(
				"m is a maximal ideal holding I",
				By(mIdeal, mProper, maximal, holdsI, MaximalIdealDef.At(R, m)))
		}),
})}

// PrimeAvoidingPowers — an ideal holding no power of f lies in a prime
// ideal missing f. I misses the powers of f, so it lies in an ideal p that
// is maximal among the ideals missing them (ExistsMaximalAvoiding). An
// element z of c outside p makes the span of p with z an ideal strictly
// above p (SpanInsertAbove), which therefore meets the powers of f; a
// power in it is b * z + t with t in p (SpanInsertIdeal). If x * y lies
// in p and neither x nor y does, write f ^ m = b * x + s and
// f ^ n = b' * y + s': then f ^ m * y = b * (x * y) + y * s lies in p,
// and so does f ^ m * f ^ n = b' * (f ^ m * y) + f ^ m * s', which is
// f ^ (m + n).
// Nor does p hold one = f ^ 0, or f = f ^ 1.
var PrimeAvoidingPowers = primeAvoidingPowersThm{family.Add(registry.ProofEntry{
	Name: "PrimeAvoidingPowers",
	Key:  "prop_dfea4c75820e4993",
	Reading: "The n = 0 instance of the hypothesis, R.one ∉ I, already makes " +
		"I proper; in the zero ring the hypothesis fails, f^0 = R.one = R.zero ∈ I.",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀I:set(A). ∀f:A.",
		Hypotheses: []string{
			"ring_ideal(R, I)",
			"f ∈ R.carrier",
			"∀n:num. monoid_pow(R.mul, R.one, f, n) ∉ I",
		},
		Conclusion: "∃p:set(A). prime_ideal(R, p) ∧ I ⊆ p ∧ f ∉ p",
	},
		func(
			a *Argument,
			R *Expr[module_record.RingOps[A]],
			ring comm_ring.CommRingFact[on.R],
			I *Expr[Set[A]],
			f *Expr[A],
			hypotheses Fact,
		) {
			parts := a.Conjuncts(
				hypotheses,
				"I is an ideal",
				"f lies in c",
				"I holds no power of f")
			ideal, fIn, noPower := parts[0], parts[1], parts[2]
			mulMonoid := comm_ring.MulMonoidOn.Read(ring)

			// The ideal above I maximal among those missing the powers of f.
			missesPowers := a.Have(
				"so I misses the powers of f",
				"I ∩ monoid_powers(R.mul, R.one, f) = ∅",
				Unfold(comm_monoid.MonoidPowersDef),
				BySets(noPower))
			p, atP := a.ObtainAs[Set[A]](
				"so I lies in an ideal p maximal among the ideals missing the powers of f",
				"∃p:set(A). "+
					"    ring_ideal(R, p) ∧ "+
					"    I ⊆ p ∧ "+
					"    p ∩ monoid_powers(R.mul, R.one, f) = ∅ ∧ "+
					"    (∀J:set(A). ring_ideal(R, J) ∧ p ⊆ J ∧ J ∩ monoid_powers(R.mul, R.one, f) = ∅ ⇒ J = p)",
				By(
					ExistsMaximalAvoiding.At(R, I, a.TermAs[Set[A]]("monoid_powers(R.mul, R.one, f)")),
					ideal,
					missesPowers))
			pParts := a.Conjuncts(
				atP,
				"p is an ideal",
				"p holds I",
				"p misses the powers of f",
				"an ideal above p missing the powers of f is p")
			pIdeal, holdsI, pMisses, maximalAvoidingPowers := pParts[0], pParts[1], pParts[2], pParts[3]
			noPowerInP := a.Have(
				"so p holds no power of f",
				"∀n:num. monoid_pow(R.mul, R.one, f, n) ∉ p",
				BySets(a.Unfolded(pMisses, comm_monoid.MonoidPowersDef)))
			pInC := a.Have(
				"p lies in c",
				"p ⊆ R.carrier",
				By(pIdeal, IdealSubset))

			// An element outside p brings a power of f into p's span with it.
			powerAbove := a.Have(
				"for z in c outside p, the span of p with z holds a power of f",
				Statement{
					Binders: "∀z:A.",
					Hypotheses: []string{
						"z ∈ R.carrier",
						"z ∉ p",
					},
					Conclusion: "∃n:num. monoid_pow(R.mul, R.one, f, n) ∈ ideal_span(R, insert(z, p))",
				},
				Derive(func(d *Argument) {
					z := d.FixAs[A]("z")
					aboutZ := d.Conjuncts(
						d.Assume(),
						"z lies in c",
						"z does not lie in p")
					zIn, zOut := aboutZ[0], aboutZ[1]
					span := d.TermAs[Set[A]]("ideal_span(R, insert(z, p))")
					adjoined := d.Conjuncts(
						GroupPremises(pInC, SpanInsertAbove.Read(ring).At(p, d.MemberOf[on.R](z, zIn))),
						"the span J of p with z is an ideal",
						"holding p",
						"and z",
						"and not p when z lies outside p")
					spanIdeal, above, distinctOutside := adjoined[0], adjoined[1], adjoined[3]
					meets := d.Have(
						"z lies outside p, so J, an ideal strictly above p, meets the powers of f",
						"¬(ideal_span(R, insert(z, p)) ∩ monoid_powers(R.mul, R.one, f) = ∅)",
						By(maximalAvoidingPowers.At(span), spanIdeal, above, distinctOutside, zOut))
					d.Show(
						"that is, J holds a power of f",
						BySets(d.Unfolded(meets, comm_monoid.MonoidPowersDef)))
				}))
			multiples := a.Have(
				"and a member of that span is a multiple of z plus a member of p",
				Statement{
					Binders: "∀z u:A.",
					Hypotheses: []string{
						"z ∈ R.carrier",
						"u ∈ ideal_span(R, insert(z, p))",
					},
					Conclusion: "∃b t:A. b ∈ R.carrier ∧ t ∈ p ∧ u = b * z + t",
				},
				Derive(func(d *Argument) {
					z := d.FixAs[A]("z")
					d.FixAs[A]("u")
					given := d.Conjuncts(
						d.Assume(),
						"z lies in c",
						"u lies in the span of p with z")
					d.Show(
						"that span is every multiple of z plus a member of p",
						BySets(SpanInsertIdeal.At(R, p, z), ring, pIdeal, given[0], given[1]))
				}))

			// p is proper and misses f.
			zeroPower := a.Have(
				"f ^ 0 is one",
				"monoid_pow(R.mul, R.one, f, 0) = R.one",
				Simp(Fwd(comm_monoid.MonoidPowDef)),
				Refl())
			proper := a.Have(
				"so p does not hold one",
				"R.one ∉ p",
				By(Normalized, noPowerInP.At(a.TermAs[Nat]("0")), zeroPower))
			fOut := a.Have(
				"f ^ 1 is f, so p does not hold f",
				"f ∉ p",
				By(Normalized, noPowerInP.At(a.TermAs[Nat]("1")), comm_monoid.PowOneOn.Read(mulMonoid), fIn))

			// p holds a factor of each product it holds.
			prime := a.Have(
				"of two members of c whose product lies in p, one lies in p",
				"∀x y:A. x ∈ R.carrier ∧ y ∈ R.carrier ∧ x * y ∈ p ⇒ x ∈ p ∨ y ∈ p",
				Derive(func(d *Argument) {
					x := d.FixAs[A]("x")
					y := d.FixAs[A]("y")
					given := d.Conjuncts(
						d.Assume(),
						"x lies in c",
						"y lies in c",
						"x * y lies in p")
					xIn, yIn, product := given[0], given[1], given[2]
					xOut := d.Unless(
						d.Term("x ∈ p"),
						"x lying in p settles it",
						Given(func(e *Argument, xInP Fact) {
							e.Show(
								"x is the factor in p",
								By(xInP))
						}))
					yOut := d.Unless(
						d.Term("y ∈ p"),
						"y lying in p settles it",
						Given(func(e *Argument, yInP Fact) {
							e.Show(
								"y is the factor in p",
								By(yInP))
						}))

					// f ^ m = b * x + s and f ^ n = b' * y + s', with s and s' in p.
					_, xPower := d.ObtainAs[Nat](
						"the span of p with x holds a power f ^ m",
						"∃m:num. monoid_pow(R.mul, R.one, f, m) ∈ ideal_span(R, insert(x, p))",
						By(powerAbove.At(x), xIn, xOut))
					_, _, xForm := d.Obtain2(
						"f ^ m is b * x + s for some b in c and s in p",
						"∃b s:A. b ∈ R.carrier ∧ s ∈ p ∧ monoid_pow(R.mul, R.one, f, m) = b * x + s",
						By(multiples.At(x, d.TermAs[A]("monoid_pow(R.mul, R.one, f, m)")), xIn, xPower))
					xs := d.Conjuncts(
						xForm,
						"b lies in c",
						"s lies in p",
						"f ^ m is b * x + s")
					_, yPower := d.ObtainAs[Nat](
						"and the span of p with y a power f ^ n",
						"∃n:num. monoid_pow(R.mul, R.one, f, n) ∈ ideal_span(R, insert(y, p))",
						By(powerAbove.At(y), yIn, yOut))
					_, _, yForm := d.Obtain2(
						"f ^ n is b' * y + s' for some b' in c and s' in p",
						"∃b' s':A. b' ∈ R.carrier ∧ s' ∈ p ∧ monoid_pow(R.mul, R.one, f, n) = b' * y + s'",
						By(multiples.At(y, d.TermAs[A]("monoid_pow(R.mul, R.one, f, n)")), yIn, yPower))
					ys := d.Conjuncts(
						yForm,
						"b' lies in c",
						"s' lies in p",
						"f ^ n is b' * y + s'")
					sInC := d.Have(
						"s and s' lie in c",
						"s ∈ R.carrier ∧ s' ∈ R.carrier",
						BySets(pInC, xs[1], ys[1]))
					powerIn := d.Have(
						"f ^ m lies in c",
						"monoid_pow(R.mul, R.one, f, m) ∈ R.carrier",
						By(comm_monoid.PowIn.Read(mulMonoid), fIn))

					// f ^ m * y lies in p, and so does f ^ m * f ^ n.
					powerTimesYExpansion := d.Have(
						"f ^ m * y is b * (x * y) + y * s",
						"monoid_pow(R.mul, R.one, f, m) * y = b * (x * y) + y * s",
						CalcEq(
							Leg(
								d.TermAs[A]("(b * x + s) * y"),
								"f ^ m is b * x + s",
								By(Normalized, xs[2])),
							FinalLeg(
								"distribute y and regroup",
								ByArith(ring, xs[0], xIn, sInC, yIn)),
						))
					powerTimesYInP := d.Have(
						"which lies in p, as x * y and s do",
						"monoid_pow(R.mul, R.one, f, m) * y ∈ p",
						powerTimesYExpansion.Rw(),
						By(pIdeal, xs[0], product, yIn, xs[1], IdealAdd, IdealMul))
					powerProductExpansion := d.Have(
						"f ^ m * f ^ n is b' * (f ^ m * y) + f ^ m * s'",
						"monoid_pow(R.mul, R.one, f, m) * monoid_pow(R.mul, R.one, f, n) = "+
							"b' * (monoid_pow(R.mul, R.one, f, m) * y) + monoid_pow(R.mul, R.one, f, m) * s'",
						CalcEq(
							Leg(
								d.TermAs[A]("monoid_pow(R.mul, R.one, f, m) * (b' * y + s')"),
								"f ^ n is b' * y + s'",
								By(Normalized, ys[2])),
							FinalLeg(
								"distribute f ^ m and regroup",
								ByArith(ring, powerIn, ys[0], yIn, sInC)),
						))
					powerProductInP := d.Have(
						"which lies in p, as f ^ m * y and s' do",
						"monoid_pow(R.mul, R.one, f, m) * monoid_pow(R.mul, R.one, f, n) ∈ p",
						powerProductExpansion.Rw(),
						By(pIdeal, ys[0], powerTimesYInP, powerIn, ys[1], IdealAdd, IdealMul))
					d.Show(
						"and it is f ^ (m + n), a power of f in p, which p does not hold",
						By(
							noPowerInP.At(d.TermAs[Nat]("m + n")),
							comm_monoid.PowAddOn.Read(mulMonoid),
							fIn,
							powerProductInP))
				}))

			a.Take(p)
			a.Show(
				"p is a prime ideal holding I and not f",
				By(pIdeal, proper, prime, holdsI, fOut, PrimeIdealDef.At(R, p)))
		}),
})}

// IdealContraction — an ideal J of T meets a subring S of R lying in T in an
// ideal of S: S holds zero and is closed under its operations, and J is
// closed under addition and under multiplication by T, which holds S.
var IdealContraction = idealContractionThm{family.Add(registry.ProofEntry{
	Name: "IdealContraction",
	Key:  "prop_68fb14405b00e2ea",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀S T J:set(A).",
		Hypotheses: []string{
			"subring(R, S)",
			"S ⊆ T",
			"ring_ideal(restrict_ring(R, T), J)",
		},
		Conclusion: "ring_ideal(restrict_ring(R, S), S ∩ J)",
	},
		func(
			a *Argument,
			R *Expr[module_record.RingOps[A]],
			S, T, J *Expr[Set[A]],
			subringS, inside, ideal Fact,
		) {
			big := a.TermAs[module_record.RingOps[A]]("restrict_ring(R, T)")
			a.Show(
				"S and J are each closed under the operations of the ideal",
				Simp(Fwd(RingIdealDef)),
				BySets(
					ideal,
					subringS,
					inside,
					comm_ring.SubringZero.At(R, S),
					IdealZero.At(big, J),
					At(comm_ring.SubringAdd, R, S),
					At(comm_ring.SubringMul, R, S),
					At(IdealAdd, big, J),
					At(IdealMul, big, J)))
		}),
})}
