// ring_localization.go — the chapter: the ring of fractions r / u of a
// ring on c with denominators in a multiplicative set s.
//
// A fraction is the class of a pair (r, u), r ∈ c and u ∈ s, under
// (r, u) ~ (r', u') ⇔ some t of s has t * (r * u') = t * (r' * u), an
// equivalence on c × s (FractionEquivalenceOn). The ring of fractions is
// the quotient of c × s by it, relations/equivalence's quotient_on: a set
// of sets of pairs, of the type set(set(prod(A, A))), which no type of
// fractions could be — its carrier depends on c and s, which are
// variables. The operations on classes choose nothing: the sum of two
// classes is the union of the classes of the sums of their
// representatives, and that this union is one class is a theorem
// (FractionAddClass). Two parts, marked by banners: the definitions; the
// ring.

package ring_localization

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The definitions
// ---------------------------------------------------------------------------

// MultiplicativeSetDef — `multiplicative_set(mul, one, c, s)`: a subset
// of c holding one and closed under the multiplication.
var MultiplicativeSetDef = multiplicativeSetDefThm{family.Define(registry.DefEntry{
	Name:     "MultiplicativeSetDef",
	Key:      "prop_a54fe2b05ceb6d81",
	Const:    "multiplicative_set",
	Type:     "(A → A → A) → A → set(A) → set(A) → bool",
	Implicit: []string{"mul", "one"},
	Equations: []string{
		"∀mul:(A → A → A). ∀one:A. ∀c s:set(A). " +
			"    multiplicative_set(mul, one, c, s) ⇔ " +
			"    s ⊆ c ∧ one ∈ s ∧ (∀u v:A. u ∈ s ∧ v ∈ s ⇒ mul(u, v) ∈ s)",
	},
})}

// PowersMultiplicative — the powers of a member x of a commutative ring form
// a multiplicative set: every xⁿ lies in the ring, one is x⁰, and xᵐ · xⁿ is
// the power xᵐ⁺ⁿ.
var PowersMultiplicative = powersMultiplicativeThm{family.Add(registry.ProofEntry{
	Name: "PowersMultiplicative",
	Key:  "prop_9533d78ce64e7bf7",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀x:A.",
		Hypotheses: []string{
			"x ∈ R.carrier",
		},
		Conclusion: "multiplicative_set(R.carrier, monoid_powers(R.mul, R.one, x))",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], x *Member[A, on.R]) {
			monoid := comm_ring.MulMonoidOn.Read(ring)
			a.Show(
				"the powers of x lie in the ring, hold one and are closed under the product",
				Unfold(MultiplicativeSetDef),
				Unfold(comm_monoid.MonoidPowersDef),
				SplitConjAll(
					Case(
						"every power xⁿ lies in the ring",
						BySets(x, comm_monoid.PowIn.Read(monoid))),
					Case(
						"one is x⁰",
						BySets(comm_monoid.MonoidPowDef)),
					Case(
						"xᵐ · xⁿ is the power xᵐ⁺ⁿ",
						BySets(x, comm_monoid.PowAddOn.Read(monoid))),
				))
		}),
})}

// fractionRelationDef — `fraction_relation(mul, c, s, p, q)`: q is a
// pair of c × s equivalent to p — some t of s has t * (r * u') =
// t * (r' * u) for p = (r, u) and q = (r', u'). Asking q to lie in c × s
// keeps c × s closed under the relation, so the quotient of c × s is
// made of the classes themselves (equivalence.InQuotientOnClosed).
var fractionRelationDef = fractionRelationDefThm{family.Define(registry.DefEntry{
	Name:     "fractionRelationDef",
	Key:      "prop_43d6a188ef3be2c6",
	Const:    "fraction_relation",
	Type:     "(A → A → A) → set(A) → set(A) → prod(A, A) → prod(A, A) → bool",
	Implicit: []string{"mul"},
	Equations: []string{
		"∀mul:(A → A → A). ∀c s:set(A). ∀p q:prod(A, A). " +
			"    fraction_relation(mul, c, s, p, q) ⇔ " +
			"    fst(q) ∈ c ∧ " +
			"    snd(q) ∈ s ∧ " +
			"    (∃t:A. t ∈ s ∧ mul(t, mul(fst(p), snd(q))) = mul(t, mul(fst(q), snd(p))))",
	},
})}

// FractionClassDef — `fraction_class(mul, c, s, r, u)`: the class of the
// pair (r, u) under the fraction relation, the pairs of c × s equivalent
// to it.
var FractionClassDef = fractionClassDefThm{family.Define(registry.DefEntry{
	Name:     "FractionClassDef",
	Key:      "prop_4b006bd65e770ba3",
	Const:    "fraction_class",
	Type:     "(A → A → A) → set(A) → set(A) → A → A → set(prod(A, A))",
	Implicit: []string{"mul"},
	Equations: []string{
		"∀mul:(A → A → A). ∀c s:set(A). ∀r u:A. " +
			"    fraction_class(mul, c, s, r, u) = equivalence_class(fraction_relation(mul, c, s), (r, u))",
	},
	Deps: []registry.EntryLike{fractionRelationDef},
})}

// RingLocalizationDef — `ring_localization(mul, c, s)`: the quotient of
// c × s by the fraction relation, the classes of the pairs of c × s.
var RingLocalizationDef = ringLocalizationDefThm{family.Define(registry.DefEntry{
	Name:     "RingLocalizationDef",
	Key:      "prop_13c21be3f197f405",
	Const:    "ring_localization",
	Type:     "(A → A → A) → set(A) → set(A) → set(set(prod(A, A)))",
	Implicit: []string{"mul"},
	Equations: []string{
		"∀mul:(A → A → A). ∀c s:set(A). " +
			"    ring_localization(mul, c, s) = quotient_on(set_cross(c, s), fraction_relation(mul, c, s))",
	},
	Deps: []registry.EntryLike{fractionRelationDef},
})}

// RingLocalizationMember — the ring of fractions read at a set of pairs:
// X is a fraction exactly when it is the class of some r of c over some
// u of s. The relation reaches only pairs of c × s, so c × s is closed
// under it and a member of its quotient is the class of a pair p of
// c × s (equivalence.InQuotientOnClosed), which is the pair of its
// components; and the class of (r, u), r ∈ c and u ∈ s, is the class of
// a pair of c × s. It asks nothing of the operation, so the text spells
// it.
var RingLocalizationMember = ringLocalizationMemberThm{family.Add(registry.ProofEntry{
	Name: "RingLocalizationMember",
	Key:  "prop_888aa3b075de2346",
	Build: family.Theorem("∀mul:(A → A → A). ∀c s:set(A). ∀X:set(prod(A, A)). "+
		"    X ∈ ring_localization(mul, c, s) ⇔ "+
		"    ∃r u:A. r ∈ c ∧ u ∈ s ∧ X = fraction_class(mul, c, s, r, u)",
		func(a *Argument, mul *Arrow2[A, A, A], c, s *Expr[Set[A]], X *Expr[Set[Prod[A, A]]]) {
			closed := a.Have(
				"c × s is closed under the relation, which asks "+
					"the components of the pair it reaches in c and in s",
				"∀p q:prod(A, A). p ∈ set_cross(c, s) ∧ fraction_relation(mul, c, s, p, q) ⇒ q ∈ set_cross(c, s)",
				By(fractionRelationDef, set_product.InCrossProjections))
			member := a.Have(
				"so a member of its quotient is the class of a pair of c × s",
				"X ∈ ring_localization(mul, c, s) ⇔ "+
					"∃p:prod(A, A). X = equivalence_class(fraction_relation(mul, c, s), p) ∧ p ∈ set_cross(c, s)",
				Unfold(RingLocalizationDef),
				By(closed, equivalence.InQuotientOnClosed))
			a.Do(member.Rw(), Simp(Fwd(FractionClassDef)))
			a.Iff()
			a.Forward(
				"X is the class of a pair p of c × s",
				func(b *Argument, image Fact) {
					p, classOf := b.UnpackAs[Prod[A, A]](image, "p")
					b.Take(b.TermAs[A]("fst(p)"))
					b.Take(b.TermAs[A]("snd(p)"))
					b.Show(
						"p is the pair of its components, the first in c and the second in s",
						By(Normalized, classOf, pairs.PairEta.At(p), set_product.InCrossProjections.At(c, s, p)))
				})
			a.Backward(
				"X is the class of (r, u) with r ∈ c and u ∈ s",
				func(b *Argument, fraction Fact) {
					r, u, classOf := b.Unpack2As[A, A](fraction, "r", "u")
					b.Take(b.TermAs[Prod[A, A]]("(r, u)"))
					b.Show(
						"which is a pair of c × s",
						By(classOf, set_product.InCross.At(c, s, r, u)))
				})
		}),
})}

// FractionAddDef — `fraction_add(add, mul, c, s, X, Y)`: the classes of
// r * u' + r' * u over u * u', for (r, u) in X and (r', u') in Y, united.
var FractionAddDef = fractionAddDefThm{family.Define(registry.DefEntry{
	Name:  "FractionAddDef",
	Key:   "prop_376db23b5bd45795",
	Const: "fraction_add",
	Type: "(A → A → A) → " +
		"(A → A → A) → " +
		"set(A) → " +
		"set(A) → " +
		"set(prod(A, A)) → " +
		"set(prod(A, A)) → " +
		"set(prod(A, A))",
	Implicit: []string{"add", "mul"},
	Equations: []string{
		"∀add mul:(A → A → A). ∀c s:set(A). ∀X Y:set(prod(A, A)). " +
			"    fraction_add(add, mul, c, s, X, Y) = " +
			"    ⋃{fraction_class(mul, c, s, add(mul(r, u'), mul(r', u)), mul(u, u')) | " +
			"        r:A, " +
			"        u:A, " +
			"        r':A, " +
			"        u':A | " +
			"        (r, u) ∈ X ∧ (r', u') ∈ Y}",
	},
	Deps: []registry.EntryLike{FractionClassDef},
})}

// FractionMulDef — `fraction_mul(mul, c, s, X, Y)`: the classes of
// r * r' over u * u', united.
var FractionMulDef = fractionMulDefThm{family.Define(registry.DefEntry{
	Name:     "FractionMulDef",
	Key:      "prop_af28a8328cabbe6b",
	Const:    "fraction_mul",
	Type:     "(A → A → A) → set(A) → set(A) → set(prod(A, A)) → set(prod(A, A)) → set(prod(A, A))",
	Implicit: []string{"mul"},
	Equations: []string{
		"∀mul:(A → A → A). ∀c s:set(A). ∀X Y:set(prod(A, A)). " +
			"    fraction_mul(mul, c, s, X, Y) = " +
			"    ⋃{fraction_class(mul, c, s, mul(r, r'), mul(u, u')) | " +
			"        r:A, " +
			"        u:A, " +
			"        r':A, " +
			"        u':A | " +
			"        (r, u) ∈ X ∧ (r', u') ∈ Y}",
	},
	Deps: []registry.EntryLike{FractionClassDef},
})}

// FractionNegDef — `fraction_neg(neg, mul, c, s, X)`: the classes of
// -r over u, united.
var FractionNegDef = fractionNegDefThm{family.Define(registry.DefEntry{
	Name:     "FractionNegDef",
	Key:      "prop_2f0a4ffd6f3db151",
	Const:    "fraction_neg",
	Type:     "(A → A) → (A → A → A) → set(A) → set(A) → set(prod(A, A)) → set(prod(A, A))",
	Implicit: []string{"neg", "mul"},
	Equations: []string{
		"∀neg:(A → A). ∀mul:(A → A → A). ∀c s:set(A). ∀X:set(prod(A, A)). " +
			"    fraction_neg(neg, mul, c, s, X) = " +
			"    ⋃{fraction_class(mul, c, s, neg(r), u) | r:A, u:A | (r, u) ∈ X}",
	},
	Deps: []registry.EntryLike{FractionClassDef},
})}

// FractionSubDef — `fraction_sub(add, neg, mul, c, s, X, Y)`: X plus the
// negation of Y.
var FractionSubDef = fractionSubDefThm{family.Define(registry.DefEntry{
	Name:  "FractionSubDef",
	Key:   "prop_968c4259fec1e065",
	Const: "fraction_sub",
	Type: "(A → A → A) → " +
		"(A → A) → " +
		"(A → A → A) → " +
		"set(A) → " +
		"set(A) → " +
		"set(prod(A, A)) → " +
		"set(prod(A, A)) → " +
		"set(prod(A, A))",
	Implicit: []string{"add", "neg", "mul"},
	Equations: []string{
		"∀add:(A → A → A). ∀neg:(A → A). ∀mul:(A → A → A). ∀c s:set(A). ∀X Y:set(prod(A, A)). " +
			"    fraction_sub(add, neg, mul, c, s, X, Y) = " +
			"    fraction_add(add, mul, c, s, X, fraction_neg(neg, mul, c, s, Y))",
	},
	Deps: []registry.EntryLike{FractionAddDef, FractionNegDef},
})}

// FractionZeroDef — `fraction_zero(zero, mul, one, c, s)`: the class of
// zero over one.
var FractionZeroDef = fractionZeroDefThm{family.Define(registry.DefEntry{
	Name:     "FractionZeroDef",
	Key:      "prop_158272c4e2f17930",
	Const:    "fraction_zero",
	Type:     "A → (A → A → A) → A → set(A) → set(A) → set(prod(A, A))",
	Implicit: []string{"zero", "mul", "one"},
	Equations: []string{
		"∀zero:A. ∀mul:(A → A → A). ∀one:A. ∀c s:set(A). " +
			"    fraction_zero(zero, mul, one, c, s) = fraction_class(mul, c, s, zero, one)",
	},
	Deps: []registry.EntryLike{FractionClassDef},
})}

// FractionOneDef — `fraction_one(mul, one, c, s)`: the class of one over
// one.
var FractionOneDef = fractionOneDefThm{family.Define(registry.DefEntry{
	Name:     "FractionOneDef",
	Key:      "prop_fe7ffa7f6dfc0c50",
	Const:    "fraction_one",
	Type:     "(A → A → A) → A → set(A) → set(A) → set(prod(A, A))",
	Implicit: []string{"mul", "one"},
	Equations: []string{
		"∀mul:(A → A → A). ∀one:A. ∀c s:set(A). " +
			"    fraction_one(mul, one, c, s) = fraction_class(mul, c, s, one, one)",
	},
	Deps: []registry.EntryLike{FractionClassDef},
})}

// ToFractionDef — `to_fraction(mul, one, c, s, r)`: r over one, the map
// from the ring into its fractions.
var ToFractionDef = toFractionDefThm{family.Define(registry.DefEntry{
	Name:     "ToFractionDef",
	Key:      "prop_d4ee44b23db82089",
	Const:    "to_fraction",
	Type:     "(A → A → A) → A → set(A) → set(A) → A → set(prod(A, A))",
	Implicit: []string{"mul", "one"},
	Equations: []string{
		"∀mul:(A → A → A). ∀one:A. ∀c s:set(A). ∀r:A. " +
			"    to_fraction(mul, one, c, s, r) = fraction_class(mul, c, s, r, one)",
	},
	Deps: []registry.EntryLike{FractionClassDef},
})}

// LocalizedRingDef — `localized_ring(R, s)`: the ring of fractions of R
// at the multiplicative set s as a ring record, its six operations on
// the classes ring_localization(R.mul, R.carrier, s).
var LocalizedRingDef = localizedRingDefThm{family.Define(registry.DefEntry{
	Name:  "LocalizedRingDef",
	Key:   "prop_4af816665c3ec783",
	Const: "localized_ring",
	Type:  "ring_ops(A) → set(A) → ring_ops(set(prod(A, A)))",
	Equations: []string{
		"∀R:ring_ops(A). ∀s:set(A). " +
			"    localized_ring(R, s) = " +
			"    mk_ring(fraction_add(R.add, R.mul, R.carrier, s), " +
			"        fraction_zero(R.zero, R.mul, R.one, R.carrier, s), " +
			"        fraction_neg(R.neg, R.mul, R.carrier, s), " +
			"        fraction_mul(R.mul, R.carrier, s), " +
			"        fraction_one(R.mul, R.one, R.carrier, s), " +
			"        fraction_sub(R.add, R.neg, R.mul, R.carrier, s), " +
			"        ring_localization(R.mul, R.carrier, s))",
	},
	Deps: []registry.EntryLike{
		RingLocalizationDef,
		FractionAddDef,
		FractionZeroDef,
		FractionNegDef,
		FractionMulDef,
		FractionOneDef,
		FractionSubDef,
	},
})}

// FractionClassMember — the definition of a class read at a pair: (x, y)
// lies in the class of (r, u) exactly when x lies in c, y in s, and some
// t of s relates the two pairs. Lying in the class of (r, u) is being
// related to it (equivalence.InClass), and the fraction relation read at
// the pairs (r, u) and (x, y) is the condition. It asks nothing of the
// operation, so the text spells it.
var FractionClassMember = fractionClassMemberThm{family.Add(registry.ProofEntry{
	Name: "FractionClassMember",
	Key:  "prop_5e61a3ed40e9725b",
	Build: family.Theorem("∀mul:(A → A → A). ∀c s:set(A). "+
		"    ∀r u x y:A.(x, y) ∈ fraction_class(mul, c, s, r, u) ⇔ "+
		"    x ∈ c ∧ y ∈ s ∧ (∃t:A. t ∈ s ∧ mul(t, mul(r, y)) = mul(t, mul(x, u)))",
		func(a *Argument, mul *Arrow2[A, A, A], c, s *Expr[Set[A]], r, u, x, y *Expr[A]) {
			a.Show(
				"(x, y) lies in the class of (r, u) when the fraction relation holds "+
					"of the two pairs, which read at their components is the condition",
				Unfold(FractionClassDef),
				Simp(Fwd(equivalence.InClass)),
				Unfold(fractionRelationDef),
				Simp(Fwd(pairs.Fst), Fwd(pairs.Snd)),
				Basic())
		}),
})}

// ---------------------------------------------------------------------------
// The ring
// ---------------------------------------------------------------------------

// FractionEquivalenceOn — the fraction relation is an equivalence on
// c × s. One relates each pair to itself; the t that relates p to q
// relates q to p, its equation read backwards; and if t relates p to q
// and t' relates q to w, the witness t * (t' * snd(q)) relates p to w:
// the first equation is read under the factor t' * snd(w), the second
// under t * snd(p), and between them the five factors regroup. Each
// regrouping is a ring identity on c, the arithmetic closer's with the
// eight factors' memberships named.
var FractionEquivalenceOn = fractionEquivalenceOnThm{family.Add(registry.ProofEntry{
	Name: "FractionEquivalenceOn",
	Key:  "prop_219f581361405b29",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀s:set(A).",
		Hypotheses: []string{
			"multiplicative_set(R.carrier, s)",
		},
		Conclusion: "equivalence_on(set_cross(R.carrier, s), fraction_relation(R.carrier, s))",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], s *Expr[Set[A]], multiplicative Fact) {
			conditions := a.Conjuncts(
				a.Unfolded(multiplicative, MultiplicativeSetDef),
				"s lies in c",
				"one lies in s",
				"s is closed under the product")
			subset, oneIn, closed := conditions[0], conditions[1], conditions[2]
			a.Do(Unfold(equivalence.EquivalenceOn), SplitConjAll(
				Case(
					"reflexive: one relates each pair of c × s to itself",
					By(oneIn, fractionRelationDef, set_product.InCrossProjections)),
				Case(
					"symmetric: the t that relates p to q relates q to p, its equation read backwards",
					By(fractionRelationDef, set_product.InCrossProjections)),
				Case(
					"transitive: two steps of the relation are one",
					Derive(func(b *Argument) {
						b.FixAs[Prod[A, A]]("p")
						b.FixAs[Prod[A, A]]("q")
						b.FixAs[Prod[A, A]]("w")
						inCross := b.Assume()
						steps := b.Conjuncts(
							b.Assume(),
							"p is related to q",
							"and q to w")
						components := b.Have(
							"the first components lie in c and the second in s",
							"fst(p) ∈ R.carrier ∧ "+
								"snd(p) ∈ s ∧ "+
								"fst(q) ∈ R.carrier ∧ "+
								"snd(q) ∈ s ∧ "+
								"fst(w) ∈ R.carrier ∧ "+
								"snd(w) ∈ s",
							By(inCross, set_product.InCrossProjections))
						first := b.Conjuncts(
							b.Unfolded(steps[0], fractionRelationDef),
							"fst(q) lies in c",
							"snd(q) lies in s",
							"some t of s relates p to q")
						second := b.Conjuncts(
							b.Unfolded(steps[1], fractionRelationDef),
							"fst(w) lies in c",
							"snd(w) lies in s",
							"some t' of s relates q to w")
						_, tFacts := b.UnpackAs[A](first[2], "t")
						_, t2Facts := b.UnpackAs[A](second[2], "t'")
						tParts := b.Conjuncts(
							tFacts,
							"t lies in s",
							"and relates p to q")
						t2Parts := b.Conjuncts(
							t2Facts,
							"t' lies in s",
							"and relates q to w")
						members := b.Have(
							"the eight factors lie in c, s lying in c",
							"t ∈ R.carrier ∧ "+
								"t' ∈ R.carrier ∧ "+
								"snd(p) ∈ R.carrier ∧ "+
								"snd(q) ∈ R.carrier ∧ "+
								"snd(w) ∈ R.carrier ∧ "+
								"fst(p) ∈ R.carrier ∧ "+
								"fst(q) ∈ R.carrier ∧ "+
								"fst(w) ∈ R.carrier",
							BySets(subset, tParts[0], t2Parts[0], components))
						witness := b.TermAs[A]("t * (t' * snd(q))")
						related := b.Have(
							"the witness t * (t' * snd(q)) relates p to w",
							"t * (t' * snd(q)) * (fst(p) * snd(w)) = t * (t' * snd(q)) * (fst(w) * snd(p))",
							CalcEq(
								Leg(
									b.TermAs[A]("t * (fst(p) * snd(q)) * (t' * snd(w))"),
									"regroup the five factors so that t meets fst(p) * snd(q)",
									ByArith(ring, members)),
								Leg(
									b.TermAs[A]("t * (fst(q) * snd(p)) * (t' * snd(w))"),
									"t relates p to q",
									By(tParts[1])),
								Leg(
									b.TermAs[A]("t * snd(p) * (t' * (fst(q) * snd(w)))"),
									"regroup so that t' meets fst(q) * snd(w)",
									ByArith(ring, members)),
								Leg(
									b.TermAs[A]("t * snd(p) * (t' * (fst(w) * snd(q)))"),
									"t' relates q to w",
									By(t2Parts[1])),
								FinalLeg(
									"and regroup back around the witness",
									ByArith(ring, members)),
							))
						witnessed := b.Have(
							"so t * (t' * snd(q)), a product of members of s, relates p to w",
							"∃t:A. t ∈ s ∧ t * (fst(p) * snd(w)) = t * (fst(w) * snd(p))",
							Derive(func(d *Argument) {
								d.Take(witness)
								d.Show(
									"it lies in s, and the chain relates the two pairs",
									By(closed, tParts[0], t2Parts[0], components, related))
							}))
						b.Show(
							"so p is related to w",
							By(fractionRelationDef, components, witnessed))
					})),
			))
		}),
})}

// FractionClassEq — two classes are equal exactly when their pairs are
// equivalent: the class law of an equivalence on a set closed under it
// (equivalence.ClassEqIffClosed) read at the fraction relation on c × s
// (FractionEquivalenceOn), which reaches only pairs of c × s. A fraction
// class is the class of its pair (FractionClassDef), and the relation
// read at the two pairs is the condition.
var FractionClassEq = fractionClassEqThm{family.Add(registry.ProofEntry{
	Name: "FractionClassEq",
	Key:  "prop_3eae78f43a4691f3",
	Reading: "s ⊆ R.carrier, from multiplicative_set, puts the witness t and the denominators " +
		"in R.carrier, where the ring laws apply; with R.zero ∈ s every two pairs are related.",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀s:set(A). ∀r u r' u':A.",
		Hypotheses: []string{
			"multiplicative_set(R.carrier, s)",
			"r ∈ R.carrier",
			"u ∈ s",
			"r' ∈ R.carrier",
			"u' ∈ s",
		},
		Conclusion: "fraction_class(R.carrier, s, r, u) = fraction_class(R.carrier, s, r', u') ⇔ " +
			"∃t:A. t ∈ s ∧ t * (r * u') = t * (r' * u)",
	},
		func(
			a *Argument,
			ring comm_ring.CommRingFact[on.R],
			s *Expr[Set[A]],
			r, u, r2, u2 *Expr[A],
			hypotheses Fact,
		) {
			parts := a.Conjuncts(
				hypotheses,
				"s is a multiplicative set",
				"r lies in c",
				"u lies in s",
				"r' lies in c",
				"u' lies in s")
			multiplicative, rIn, uIn, r2In, u2In := parts[0], parts[1], parts[2], parts[3], parts[4]
			read := a.Have(
				"the fraction relation at (r, u) and (r', u') is the condition, r' lying in c and u' in s",
				"fraction_relation(R.carrier, s, (r, u), (r', u')) ⇔ ∃t:A. t ∈ s ∧ t * (r * u') = t * (r' * u)",
				Unfold(fractionRelationDef),
				Simp(Fwd(pairs.Fst), Fwd(pairs.Snd)),
				By(r2In, u2In))
			equiv := a.Have(
				"the fraction relation is an equivalence on c × s",
				"equivalence_on(set_cross(R.carrier, s), fraction_relation(R.carrier, s))",
				By(FractionEquivalenceOn, ring, multiplicative))
			pairsIn := a.Have(
				"(r, u) and (r', u') are pairs of c × s",
				"(r, u) ∈ set_cross(R.carrier, s) ∧ (r', u') ∈ set_cross(R.carrier, s)",
				By(set_product.InCross, rIn, uIn, r2In, u2In))
			closed := a.Have(
				"c × s is closed under the relation, which asks "+
					"the components of the pair it reaches in c and in s",
				Statement{
					Binders: "∀p q:prod(A, A).",
					Hypotheses: []string{
						"p ∈ set_cross(R.carrier, s)",
						"fraction_relation(R.carrier, s, p, q)",
					},
					Conclusion: "q ∈ set_cross(R.carrier, s)",
				},
				By(fractionRelationDef, set_product.InCrossProjections))
			sameClass := a.Have(
				"so the classes of (r, u) and (r', u') are equal exactly when the pairs are related",
				"equivalence_class(fraction_relation(R.carrier, s), (r, u)) = "+
					"equivalence_class(fraction_relation(R.carrier, s), (r', u')) ⇔ "+
					"fraction_relation(R.carrier, s, (r, u), (r', u'))",
				By(closed, pairsIn, equivalence.ClassEqIffClosed.Read(equiv)))
			a.Show(
				"a fraction class is the class of its pair, so the two are equal exactly when the condition holds",
				Simp(Fwd(FractionClassDef)),
				By(sameClass, read))
		}),
})}

// FractionClassCross — two pairs whose cross products agree have one
// class: the criterion of FractionClassEq with the witness one, which lies
// in s and relates the pairs because their cross products are equal.
var FractionClassCross = fractionClassCrossThm{family.Add(registry.ProofEntry{
	Name: "FractionClassCross",
	Key:  "prop_b33ce8d2a2ef7b25",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀s:set(A). ∀r u r' u':A.",
		Hypotheses: []string{
			"multiplicative_set(R.carrier, s)",
			"r ∈ R.carrier",
			"u ∈ s",
			"r' ∈ R.carrier",
			"u' ∈ s",
			"r * u' = r' * u",
		},
		Conclusion: "fraction_class(R.carrier, s, r, u) = fraction_class(R.carrier, s, r', u')",
	},
		func(
			a *Argument,
			ring comm_ring.CommRingFact[on.R],
			s *Expr[Set[A]],
			r, u, r2, u2 *Expr[A],
			hypotheses Fact,
		) {
			parts := a.Conjuncts(
				hypotheses,
				"s is a multiplicative set",
				"r lies in c",
				"u lies in s",
				"r' lies in c",
				"u' lies in s",
				"the cross products agree")
			multiplicative, rIn, uIn, r2In, u2In, cross :=
				parts[0], parts[1], parts[2], parts[3], parts[4], parts[5]
			oneIn := a.Conjuncts(
				a.Unfolded(multiplicative, MultiplicativeSetDef),
				"s lies in c",
				"one lies in s",
				"s is closed under the product")[1]
			a.Show(
				"one lies in s, and relates the two pairs as their cross products agree",
				By(
					FractionClassEq.Read(ring).AsFact().At(s, r, u, r2, u2),
					multiplicative,
					rIn,
					uIn,
					r2In,
					u2In,
					cross,
					oneIn))
		}),
})}

// FractionAddClass — the sum of two classes is the class of the sum of
// any representatives. A pair (x, y) of the class of (r, u) is related to
// it by some t of s, and a pair (x', y') of the class of (r', u') by some
// t' of s; the product t * t' lies in s and relates the two sums, the
// first relation read under the factor t' * y' * u' and the second under
// t * y * u. Every class in the union defining the sum is therefore the
// class of the sum at (r, u) and (r', u'), and the union holds it, each
// pair lying in its own class.
var FractionAddClass = fractionAddClassThm{family.Add(registry.ProofEntry{
	Name: "FractionAddClass",
	Key:  "prop_86c846580d42396",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀s:set(A). ∀r u r' u':A.",
		Hypotheses: []string{
			"multiplicative_set(R.carrier, s)",
			"r ∈ R.carrier",
			"u ∈ s",
			"r' ∈ R.carrier",
			"u' ∈ s",
		},
		Conclusion: "fraction_add(R.carrier, " +
			"    s, " +
			"    fraction_class(R.carrier, s, r, u), " +
			"    fraction_class(R.carrier, s, r', u')) = " +
			"fraction_class(R.carrier, s, r * u' + r' * u, u * u')",
	},
		func(
			a *Argument,
			ring comm_ring.CommRingFact[on.R],
			s *Expr[Set[A]],
			r, u, r2, u2 *Expr[A],
			hypotheses Fact,
		) {
			parts := a.Conjuncts(
				hypotheses,
				"s is a multiplicative set",
				"r lies in c",
				"u lies in s",
				"r' lies in c",
				"u' lies in s")
			multiplicative, rIn, uIn, r2In, u2In := parts[0], parts[1], parts[2], parts[3], parts[4]
			conditions := a.Conjuncts(
				a.Unfolded(multiplicative, MultiplicativeSetDef),
				"s lies in c",
				"one lies in s",
				"s is closed under the product")
			subset, oneIn, closed := conditions[0], conditions[1], conditions[2]
			added := a.Have(
				"each pair (x, y) of the first class and (x', y') of the "+
					"second add into the class of (r * u' + r' * u, u * u')",
				Statement{
					Binders: "∀x y x' y':A.",
					Hypotheses: []string{
						"(x, y) ∈ fraction_class(R.carrier, s, r, u)",
						"(x', y') ∈ fraction_class(R.carrier, s, r', u')",
					},
					Conclusion: "fraction_class(R.carrier, s, x * y' + x' * y, y * y') = " +
						"fraction_class(R.carrier, s, r * u' + r' * u, u * u')",
				},
				Derive(func(b *Argument) {
					b.FixAs[A]("x")
					b.FixAs[A]("y")
					b.FixAs[A]("x'")
					b.FixAs[A]("y'")
					inClasses := b.Conjuncts(
						b.Assume(),
						"(x, y) lies in the class of (r, u)",
						"and (x', y') in the class of (r', u')")
					first := b.Conjuncts(
						b.Have(
							"so x lies in c, y in s, and some t of s relates (r, u) to (x, y)",
							"x ∈ R.carrier ∧ y ∈ s ∧ (∃t:A. t ∈ s ∧ t * (r * y) = t * (x * u))",
							By(FractionClassMember, inClasses[0])),
						"x lies in c",
						"y lies in s",
						"some t of s relates (r, u) to (x, y)")
					second := b.Conjuncts(
						b.Have(
							"and x' lies in c, y' in s, and some t' of s relates (r', u') to (x', y')",
							"x' ∈ R.carrier ∧ y' ∈ s ∧ (∃t:A. t ∈ s ∧ t * (r' * y') = t * (x' * u'))",
							By(FractionClassMember, inClasses[1])),
						"x' lies in c",
						"y' lies in s",
						"some t' of s relates (r', u') to (x', y')")
					xIn, yIn, x2In, y2In := first[0], first[1], second[0], second[1]
					_, tFacts := b.UnpackAs[A](first[2], "t")
					_, t2Facts := b.UnpackAs[A](second[2], "t'")
					tParts := b.Conjuncts(
						tFacts,
						"t lies in s",
						"and relates (r, u) to (x, y)")
					t2Parts := b.Conjuncts(
						t2Facts,
						"t' lies in s",
						"and relates (r', u') to (x', y')")
					members := b.Have(
						"the ten factors lie in c, s lying in c",
						"t ∈ R.carrier ∧ "+
							"t' ∈ R.carrier ∧ "+
							"u ∈ R.carrier ∧ "+
							"u' ∈ R.carrier ∧ "+
							"y ∈ R.carrier ∧ "+
							"y' ∈ R.carrier ∧ "+
							"r ∈ R.carrier ∧ "+
							"r' ∈ R.carrier ∧ "+
							"x ∈ R.carrier ∧ "+
							"x' ∈ R.carrier",
						BySets(subset, tParts[0], t2Parts[0], uIn, u2In, yIn, y2In, rIn, r2In, xIn, x2In))
					related := b.Have(
						"t * t' relates the two sums: the first relation scaled by t' * y' * u', the second by t * y * u",
						"t * t' * ((x * y' + x' * y) * (u * u')) = t * t' * ((r * u' + r' * u) * (y * y'))",
						ByArith(
							ring,
							Scaled(b.TermAs[A]("t' * y' * u'"), tParts[1]),
							Scaled(b.TermAs[A]("t * y * u"), t2Parts[1]),
							members))
					witnessed := b.Have(
						"so t * t', a product of members of s, relates the two sums",
						"∃t:A. t ∈ s ∧ t * ((x * y' + x' * y) * (u * u')) = t * ((r * u' + r' * u) * (y * y'))",
						Derive(func(d *Argument) {
							d.Take(d.TermAs[A]("t * t'"))
							d.Show(
								"t * t' lies in s, which is closed under the product, and relates the sums",
								By(closed, tParts[0], t2Parts[0], related))
						}))
					b.Show(
						"so the two classes are equal",
						By(
							FractionClassEq.Read(ring).AsFact().At(s, b.TermAs[A]("x * y' + x' * y"), b.TermAs[A]("y * y'"),
								b.TermAs[A]("r * u' + r' * u"), b.TermAs[A]("u * u'")),
							multiplicative,
							comm_ring.AddIn.Read(ring),
							comm_ring.MulIn.Read(ring),
							closed,
							members,
							yIn,
							y2In,
							uIn,
							u2In,
							witnessed))
				}))
			own := a.Have(
				"(r, u) lies in its own class: one relates it to itself",
				"(r, u) ∈ fraction_class(R.carrier, s, r, u)",
				By(FractionClassMember, rIn, uIn, oneIn))
			own2 := a.Have(
				"and (r', u') in its own",
				"(r', u') ∈ fraction_class(R.carrier, s, r', u')",
				By(FractionClassMember, r2In, u2In, oneIn))
			a.Show(
				"so every class in the union is the class of (r * u' + r' * u, u * u'), which the union holds",
				Unfold(FractionAddDef),
				BySets(added, own, own2))
		}),
})}

// FractionMulClass — the product of two classes is the class of the
// product of any representatives. A pair (x, y) of the class of (r, u) is
// related to it by some t of s, and a pair (x', y') of the class of
// (r', u') by some t' of s; the product t * t' lies in s and relates the
// two products, the first relation read under the factor t' * (x' * u')
// and the second under t * (r * y). Every class in the union defining the
// product is therefore the class of the product at (r, u) and (r', u'),
// and the union holds it, each pair lying in its own class.
var FractionMulClass = fractionMulClassThm{family.Add(registry.ProofEntry{
	Name: "FractionMulClass",
	Key:  "prop_86c0b2d5cdb00de4",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀s:set(A). ∀r u r' u':A.",
		Hypotheses: []string{
			"multiplicative_set(R.carrier, s)",
			"r ∈ R.carrier",
			"u ∈ s",
			"r' ∈ R.carrier",
			"u' ∈ s",
		},
		Conclusion: "fraction_mul(R.carrier, " +
			"    s, " +
			"    fraction_class(R.carrier, s, r, u), " +
			"    fraction_class(R.carrier, s, r', u')) = " +
			"fraction_class(R.carrier, s, r * r', u * u')",
	},
		func(
			a *Argument,
			ring comm_ring.CommRingFact[on.R],
			s *Expr[Set[A]],
			r, u, r2, u2 *Expr[A],
			hypotheses Fact,
		) {
			parts := a.Conjuncts(
				hypotheses,
				"s is a multiplicative set",
				"r lies in c",
				"u lies in s",
				"r' lies in c",
				"u' lies in s")
			multiplicative, rIn, uIn, r2In, u2In := parts[0], parts[1], parts[2], parts[3], parts[4]
			conditions := a.Conjuncts(
				a.Unfolded(multiplicative, MultiplicativeSetDef),
				"s lies in c",
				"one lies in s",
				"s is closed under the product")
			subset, oneIn, closed := conditions[0], conditions[1], conditions[2]
			multiplied := a.Have(
				"each pair (x, y) of the first class and (x', y') of "+
					"the second multiply into the class of (r * r', u * u')",
				Statement{
					Binders: "∀x y x' y':A.",
					Hypotheses: []string{
						"(x, y) ∈ fraction_class(R.carrier, s, r, u)",
						"(x', y') ∈ fraction_class(R.carrier, s, r', u')",
					},
					Conclusion: "fraction_class(R.carrier, s, x * x', y * y') = " +
						"fraction_class(R.carrier, s, r * r', u * u')",
				},
				Derive(func(b *Argument) {
					b.FixAs[A]("x")
					b.FixAs[A]("y")
					b.FixAs[A]("x'")
					b.FixAs[A]("y'")
					inClasses := b.Conjuncts(
						b.Assume(),
						"(x, y) lies in the class of (r, u)",
						"and (x', y') in the class of (r', u')")
					first := b.Conjuncts(
						b.Have(
							"so x lies in c, y in s, and some t of s relates (r, u) to (x, y)",
							"x ∈ R.carrier ∧ y ∈ s ∧ (∃t:A. t ∈ s ∧ t * (r * y) = t * (x * u))",
							By(FractionClassMember, inClasses[0])),
						"x lies in c",
						"y lies in s",
						"some t of s relates (r, u) to (x, y)")
					second := b.Conjuncts(
						b.Have(
							"and x' lies in c, y' in s, and some t' of s relates (r', u') to (x', y')",
							"x' ∈ R.carrier ∧ y' ∈ s ∧ (∃t:A. t ∈ s ∧ t * (r' * y') = t * (x' * u'))",
							By(FractionClassMember, inClasses[1])),
						"x' lies in c",
						"y' lies in s",
						"some t' of s relates (r', u') to (x', y')")
					xIn, yIn, x2In, y2In := first[0], first[1], second[0], second[1]
					_, tFacts := b.UnpackAs[A](first[2], "t")
					_, t2Facts := b.UnpackAs[A](second[2], "t'")
					tParts := b.Conjuncts(
						tFacts,
						"t lies in s",
						"and relates (r, u) to (x, y)")
					t2Parts := b.Conjuncts(
						t2Facts,
						"t' lies in s",
						"and relates (r', u') to (x', y')")
					members := b.Have(
						"the ten factors lie in c, s lying in c",
						"t ∈ R.carrier ∧ "+
							"t' ∈ R.carrier ∧ "+
							"u ∈ R.carrier ∧ "+
							"u' ∈ R.carrier ∧ "+
							"y ∈ R.carrier ∧ "+
							"y' ∈ R.carrier ∧ "+
							"r ∈ R.carrier ∧ "+
							"r' ∈ R.carrier ∧ "+
							"x ∈ R.carrier ∧ "+
							"x' ∈ R.carrier",
						BySets(subset, tParts[0], t2Parts[0], uIn, u2In, yIn, y2In, rIn, r2In, xIn, x2In))
					related := b.Have(
						"t * t' relates the two products: the first relation "+
							"scaled by t' * (x' * u'), the second by t * (r * y)",
						"t * t' * (x * x' * (u * u')) = t * t' * (r * r' * (y * y'))",
						ByArith(
							ring,
							Scaled(b.TermAs[A]("t' * (x' * u')"), tParts[1]),
							Scaled(b.TermAs[A]("t * (r * y)"), t2Parts[1]),
							members))
					witnessed := b.Have(
						"so t * t', a product of members of s, relates the two products",
						"∃t:A. t ∈ s ∧ t * (x * x' * (u * u')) = t * (r * r' * (y * y'))",
						Derive(func(d *Argument) {
							d.Take(d.TermAs[A]("t * t'"))
							d.Show(
								"t * t' lies in s, which is closed under the product, and relates the products",
								By(closed, tParts[0], t2Parts[0], related))
						}))
					b.Show(
						"so the two classes are equal",
						By(
							FractionClassEq.Read(ring).AsFact().At(s, b.TermAs[A]("x * x'"), b.TermAs[A]("y * y'"),
								b.TermAs[A]("r * r'"), b.TermAs[A]("u * u'")),
							multiplicative,
							comm_ring.MulIn.Read(ring),
							closed,
							members,
							yIn,
							y2In,
							uIn,
							u2In,
							witnessed))
				}))
			own := a.Have(
				"(r, u) lies in its own class: one relates it to itself",
				"(r, u) ∈ fraction_class(R.carrier, s, r, u)",
				By(FractionClassMember, rIn, uIn, oneIn))
			own2 := a.Have(
				"and (r', u') in its own",
				"(r', u') ∈ fraction_class(R.carrier, s, r', u')",
				By(FractionClassMember, r2In, u2In, oneIn))
			a.Show(
				"so every class in the union is the class of (r * r', u * u'), which the union holds",
				Unfold(FractionMulDef),
				BySets(multiplied, own, own2))
		}),
})}

// FractionNegClass — the negation of a class is the class of the
// negation of any representative. A pair (x, y) of the class of (r, u) is
// related to it by some t of s, t * (r * y) = t * (x * u); the negation
// passes out of both products, so the same t relates (-x, y) to (-r, u).
// Every class in the union defining the negation is therefore the class
// of (-r, u), and the union holds it, (r, u) lying in its own class.
var FractionNegClass = fractionNegClassThm{family.Add(registry.ProofEntry{
	Name: "FractionNegClass",
	Key:  "prop_c3f3b56b65155972",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀s:set(A). ∀r u:A.",
		Hypotheses: []string{
			"multiplicative_set(R.carrier, s)",
			"r ∈ R.carrier",
			"u ∈ s",
		},
		Conclusion: "fraction_neg(R.carrier, s, fraction_class(R.carrier, s, r, u)) = " +
			"fraction_class(R.carrier, s, -r, u)",
	},
		func(
			a *Argument,
			ring comm_ring.CommRingFact[on.R],
			s *Expr[Set[A]],
			r, u *Expr[A],
			hypotheses Fact,
		) {
			parts := a.Conjuncts(
				hypotheses,
				"s is a multiplicative set",
				"r lies in c",
				"u lies in s")
			multiplicative, rIn, uIn := parts[0], parts[1], parts[2]
			conditions := a.Conjuncts(
				a.Unfolded(multiplicative, MultiplicativeSetDef),
				"s lies in c",
				"one lies in s",
				"s is closed under the product")
			subset, oneIn := conditions[0], conditions[1]
			passOut := Simp(
				Fwd(comm_ring.MulLeftNegOn.Read(ring)),
				Fwd(comm_ring.MulRightNegOn.Read(ring)),
				Fwd(comm_ring.MulIn.Read(ring)))
			negated := a.Have(
				"each pair (x, y) of the class negates into the class of (-r, u)",
				Statement{
					Binders: "∀x y:A.",
					Hypotheses: []string{
						"(x, y) ∈ fraction_class(R.carrier, s, r, u)",
					},
					Conclusion: "fraction_class(R.carrier, s, -x, y) = fraction_class(R.carrier, s, -r, u)",
				},
				Derive(func(b *Argument) {
					b.FixAs[A]("x")
					y := b.FixAs[A]("y")
					inClass := b.Assume()
					pair := b.Conjuncts(
						b.Have(
							"so x lies in c, y in s, and some t of s relates (r, u) to (x, y)",
							"x ∈ R.carrier ∧ y ∈ s ∧ (∃t:A. t ∈ s ∧ t * (r * y) = t * (x * u))",
							By(FractionClassMember, inClass)),
						"x lies in c",
						"y lies in s",
						"some t of s relates (r, u) to (x, y)")
					xIn, yIn := pair[0], pair[1]
					t, tFacts := b.UnpackAs[A](pair[2], "t")
					tParts := b.Conjuncts(
						tFacts,
						"t lies in s",
						"and relates (r, u) to (x, y)")
					b.Have(
						"t, u and y lie in c, s lying in c, where the negation rules apply",
						"t ∈ R.carrier ∧ u ∈ R.carrier ∧ y ∈ R.carrier",
						BySets(subset, tParts[0], uIn, yIn))
					negRelated := b.Have(
						"t relates (-x, y) to (-r, u): its relation, negated",
						"t * (-x * u) = t * (-r * y)",
						CalcEq(
							Leg(
								b.TermAs[A]("-(t * (x * u))"),
								"the negation passes out of both products",
								passOut,
								Refl()),
							Leg(
								b.TermAs[A]("-(t * (r * y))"),
								"t relates (r, u) to (x, y)",
								By(Normalized, tParts[1])),
							FinalLeg(
								"and back into them",
								passOut,
								Refl()),
						))
					witnessed := b.Have(
						"so some t of s relates (-x, y) to (-r, u)",
						"∃t:A. t ∈ s ∧ t * (-x * u) = t * (-r * y)",
						Derive(func(d *Argument) {
							d.Take(t)
							d.Show(
								"t lies in s and relates the negated pairs",
								By(tParts[0], negRelated))
						}))
					b.Show(
						"so the two classes are equal",
						By(
							FractionClassEq.Read(ring).AsFact().At(s, b.TermAs[A]("-x"), y, b.TermAs[A]("-r"), u),
							multiplicative,
							comm_ring.NegIn.Read(ring),
							xIn,
							yIn,
							rIn,
							uIn,
							witnessed))
				}))
			own := a.Have(
				"(r, u) lies in its own class: one relates it to itself",
				"(r, u) ∈ fraction_class(R.carrier, s, r, u)",
				By(FractionClassMember, rIn, uIn, oneIn))
			a.Show(
				"so every class in the union is the class of (-r, u), which the union holds",
				Unfold(FractionNegDef),
				BySets(negated, own))
		}),
})}

// FractionZeroIff — a class is the zero fraction exactly when some
// denominator annihilates its numerator. The zero fraction is the class
// of (zero, one), and FractionClassEq relates (r, u) to that pair by a t
// of s with t * (r * one) = t * (zero * u); one is the identity and zero
// absorbs, so the condition reads t * r = zero.
var FractionZeroIff = fractionZeroIffThm{family.Add(registry.ProofEntry{
	Name: "FractionZeroIff",
	Key:  "prop_57bb3be2415a292f",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀s:set(A). ∀r u:A.",
		Hypotheses: []string{
			"multiplicative_set(R.carrier, s)",
			"r ∈ R.carrier",
			"u ∈ s",
		},
		Conclusion: "fraction_class(R.carrier, s, r, u) = fraction_zero(R.carrier, s) ⇔ " +
			"∃t:A. t ∈ s ∧ t * r = R.zero",
	},
		func(
			a *Argument,
			ring comm_ring.CommRingFact[on.R],
			s *Expr[Set[A]],
			r, u *Expr[A],
			hypotheses Fact,
		) {
			parts := a.Conjuncts(
				hypotheses,
				"s is a multiplicative set",
				"r lies in c",
				"u lies in s")
			multiplicative, rIn, uIn := parts[0], parts[1], parts[2]
			conditions := a.Conjuncts(
				a.Unfolded(multiplicative, MultiplicativeSetDef),
				"s lies in c",
				"one lies in s",
				"s is closed under the product")
			subset, oneIn := conditions[0], conditions[1]
			related := a.Have(
				"the class of (r, u) is the class of (zero, one) exactly when some t of s relates the two pairs",
				"fraction_class(R.carrier, s, r, u) = fraction_class(R.carrier, s, R.zero, R.one) ⇔ "+
					"∃t:A. t ∈ s ∧ t * (r * R.one) = t * (R.zero * u)",
				By(
					FractionClassEq.Read(ring).AsFact().At(s, r, u, a.TermAs[A]("R.zero"), a.TermAs[A]("R.one")),
					multiplicative,
					rIn,
					uIn,
					comm_ring.ZeroIn.Read(ring),
					oneIn))
			rightIdentity := comm_monoid.RightIdentityOn.Read(comm_ring.MulMonoidOn.Read(ring)).AsFact()
			leftZero := comm_ring.MulLeftZeroOn.Read(ring).AsFact()
			rightZero := comm_ring.MulRightZeroOn.Read(ring).AsFact()
			reads := a.Have(
				"at each t of s the relation reads t * r = R.zero",
				"∀t:A. t ∈ s ⇒ t * (r * R.one) = t * r ∧ t * (R.zero * u) = R.zero",
				Derive(func(b *Argument) {
					t := b.FixAs[A]("t")
					tIn := b.Assume()
					members := b.Have(
						"t and u lie in c, s lying in c",
						"t ∈ R.carrier ∧ u ∈ R.carrier",
						BySets(subset, tIn, uIn))
					b.Show(
						"r * one is r, zero * u is zero, and t * zero is zero",
						By(Normalized, members, rIn, rightIdentity.At(r), leftZero.At(u), rightZero.At(t)))
				}))
			a.Show(
				"the zero fraction is the class of (zero, one)",
				Unfold(FractionZeroDef),
				By(related, reads))
		}),
})}

// LocalizationRing — the fractions form a ring on the set of classes.
// Every fraction is r / u for some r of c and u of s, and every such
// class is a fraction (RingLocalizationMember); so each condition of a
// ring is checked at representatives. The class laws turn a sum, a
// product or a negation of classes into one class — of r * u' + r' * u
// over u * u', of r * r' over u * u', of -r over u — again a fraction,
// its denominator a member of s. An identity of the ring of fractions
// then asks its two sides to be one class: where they are the class of
// one pair spelled two ways — associativity, commutativity, the
// identities — the numerators agree in the ring and so do the
// denominators; where they are not — the inverse and distributivity —
// the cross products agree (FractionClassCross).
var LocalizationRing = localizationRingThm{family.Add(registry.ProofEntry{
	Name: "LocalizationRing",
	Key:  "prop_d93ecb2bd618e3b7",
	Reading: "If R.zero ∈ s every fraction class is R.carrier × s: the ring of " +
		"fractions is the one-point zero ring, fraction_zero = fraction_one, and " +
		"the statement holds. s ⊆ R.carrier, which multiplicative_set supplies, is " +
		"what puts witnesses and denominators where the ring laws apply.",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀s:set(A).",
		Hypotheses: []string{
			"multiplicative_set(R.carrier, s)",
		},
		Conclusion: "comm_ring_on(mk_ring(fraction_add(R.carrier, s), " +
			"        fraction_zero(R.carrier, s), " +
			"        fraction_neg(R.carrier, s), " +
			"        fraction_mul(R.carrier, s), " +
			"        fraction_one(R.carrier, s), " +
			"        fraction_sub(R.carrier, s), " +
			"        ring_localization(R.carrier, s)))",
		Abbrev: Abbrev{
			{Name: "fractionRingRecord", Text: "mk_ring(fraction_add(R.carrier, s), " +
				"    fraction_zero(R.carrier, s), " +
				"    fraction_neg(R.carrier, s), " +
				"    fraction_mul(R.carrier, s), " +
				"    fraction_one(R.carrier, s), " +
				"    fraction_sub(R.carrier, s), " +
				"    ring_localization(R.carrier, s))"},
		},
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], s *Expr[Set[A]], multiplicative Fact) {
			conditions := a.Conjuncts(
				a.Unfolded(multiplicative, MultiplicativeSetDef),
				"s lies in c",
				"one lies in s",
				"s is closed under the product")
			subset, oneIn, closed := conditions[0], conditions[1], conditions[2]
			inclusion := a.Unfolded(subset, set_basic.SubsetDef)
			classIn := a.Have(
				"the class of each pair of c × s is a fraction",
				Statement{
					Binders: "∀r u:A.",
					Hypotheses: []string{
						"r ∈ R.carrier",
						"u ∈ s",
					},
					Conclusion: "fraction_class(R.carrier, s, r, u) ∈ ring_localization(R.carrier, s)",
				},
				Derive(func(b *Argument) {
					r, u := b.FixAs[A]("r"), b.FixAs[A]("u")
					pair := b.Assume()
					b.Show(
						"a fraction is the class of a member of c over a member "+
							"of s, and the class of (r, u) is that of r over u",
						Simp(Fwd(RingLocalizationMember)),
						Witness(r),
						Witness(u),
						By(pair))
				}))

			fractions := a.Have(
				"every fraction is the class of a member of c over a member of s",
				Statement{
					Binders: "∀X:set(prod(A, A)).",
					Hypotheses: []string{
						"X ∈ ring_localization(R.carrier, s)",
					},
					Conclusion: "∃r u:A. r ∈ R.carrier ∧ u ∈ s ∧ X = fraction_class(R.carrier, s, r, u)",
				},
				By(RingLocalizationMember))
			// A fraction written as a class: the numerator's membership in
			// c, the denominator's in s, and the equation of the fraction
			// with the class.
			type _FractionAsClass struct{ numeratorIn, denominatorIn, isClass Fact }
			// represent writes the fraction X, inFractions stating it is one,
			// as the class of its numerator r over its denominator u.
			represent := func(
				b *Argument,
				X *Expr[Set[Prod[A, A]]],
				inFractions Fact,
				r, u string,
			) _FractionAsClass {
				_, _, represented := b.Unpack2As[A, A](GroupPremises(inFractions, fractions.At(X)), r, u)
				parts := b.Conjuncts(
					represented,
					"the numerator lies in c",
					"the denominator lies in s",
					"the fraction is their class")
				return _FractionAsClass{numeratorIn: parts[0], denominatorIn: parts[1], isClass: parts[2]}
			}
			// sameClass closes an equation of two classes whose numerators
			// agree in the ring and whose denominators do too.
			sameClass := func(members ...any) Action {
				ringAt := append([]any{ring}, members...)
				return Expect(Congr(),
					Case(
						"the numerators agree in the ring",
						ByArith(ringAt...)),
					Case(
						"and so do the denominators",
						ByArith(ringAt...)))
			}
			addClass := FractionAddClass.Read(ring)
			mulClass := FractionMulClass.Read(ring)
			negClass := FractionNegClass.Read(ring)
			classCross := FractionClassCross.Read(ring)
			addIn, mulIn := comm_ring.AddIn.Read(ring), comm_ring.MulIn.Read(ring)

			// The group of fractions under the sum.
			zeroFraction := a.Have(
				"zero / one is a fraction",
				"fraction_zero(R.carrier, s) ∈ ring_localization(R.carrier, s)",
				Unfold(FractionZeroDef),
				By(classIn, comm_ring.ZeroIn.Read(ring), oneIn))
			sumIn := a.Have(
				"a sum of fractions is a fraction",
				Statement{
					Binders: "∀X Y:set(prod(A, A)).",
					Hypotheses: []string{
						"X ∈ ring_localization(R.carrier, s)",
						"Y ∈ ring_localization(R.carrier, s)",
					},
					Conclusion: "fraction_add(R.carrier, s, X, Y) ∈ ring_localization(R.carrier, s)",
				},
				Derive(func(b *Argument) {
					X := b.FixAs[Set[Prod[A, A]]]("X")
					Y := b.FixAs[Set[Prod[A, A]]]("Y")
					given := b.Conjuncts(
						b.Assume(),
						"X is a fraction",
						"Y is a fraction")
					x := represent(b, X, given[0], "r₁", "u₁")
					y := represent(b, Y, given[1], "r₂", "u₂")
					inC := b.Have(
						"the denominators lie in c, s lying in c",
						"u₁ ∈ R.carrier ∧ u₂ ∈ R.carrier",
						By(inclusion, x.denominatorIn, y.denominatorIn))
					b.Show(
						"the sum is the class of r₁ * u₂ + r₂ * u₁ over u₁ * u₂, a member of c over a member of s",
						x.isClass.Rw(),
						y.isClass.Rw(),
						Simp(Fwd(addClass)),
						By(
							classIn,
							addIn,
							mulIn,
							closed,
							x.numeratorIn,
							x.denominatorIn,
							y.numeratorIn,
							y.denominatorIn,
							inC))
				}))
			negationIn := a.Have(
				"the negation of a fraction is a fraction",
				Statement{
					Binders: "∀X:set(prod(A, A)).",
					Hypotheses: []string{
						"X ∈ ring_localization(R.carrier, s)",
					},
					Conclusion: "fraction_neg(R.carrier, s, X) ∈ ring_localization(R.carrier, s)",
				},
				Derive(func(b *Argument) {
					X := b.FixAs[Set[Prod[A, A]]]("X")
					isFraction := b.Assume()
					x := represent(b, X, isFraction, "r", "u")
					b.Show(
						"the negation is the class of -r over u",
						x.isClass.Rw(),
						Simp(Fwd(negClass)),
						By(classIn, comm_ring.NegIn.Read(ring), x.numeratorIn, x.denominatorIn))
				}))
			sumAssociates := a.Have(
				"the sum associates",
				Statement{
					Binders: "∀X Y Z:set(prod(A, A)).",
					Hypotheses: []string{
						"X ∈ ring_localization(R.carrier, s)",
						"Y ∈ ring_localization(R.carrier, s)",
						"Z ∈ ring_localization(R.carrier, s)",
					},
					Conclusion: "fraction_add(R.carrier, s, X, fraction_add(R.carrier, s, Y, Z)) = " +
						"fraction_add(R.carrier, s, fraction_add(R.carrier, s, X, Y), Z)",
				},
				Derive(func(b *Argument) {
					X := b.FixAs[Set[Prod[A, A]]]("X")
					Y := b.FixAs[Set[Prod[A, A]]]("Y")
					Z := b.FixAs[Set[Prod[A, A]]]("Z")
					given := b.Conjuncts(
						b.Assume(),
						"X is a fraction",
						"Y is a fraction",
						"Z is a fraction")
					x := represent(b, X, given[0], "r₁", "u₁")
					y := represent(b, Y, given[1], "r₂", "u₂")
					z := represent(b, Z, given[2], "r₃", "u₃")
					inC := b.Have(
						"the denominators lie in c, s lying in c",
						"u₁ ∈ R.carrier ∧ u₂ ∈ R.carrier ∧ u₃ ∈ R.carrier",
						By(inclusion, x.denominatorIn, y.denominatorIn, z.denominatorIn))
					b.Have(
						"the inner sums have their denominators in s, so the class laws apply to the inner classes",
						"u₁ * u₂ ∈ s ∧ u₂ * u₃ ∈ s",
						By(closed, x.denominatorIn, y.denominatorIn, z.denominatorIn))
					b.Show(
						"both groupings are the class of r₁ * u₂ * u₃ + r₂ * u₁ "+
							"* u₃ + r₃ * u₁ * u₂ over u₁ * u₂ * u₃, grouped two ways",
						x.isClass.Rw(),
						y.isClass.Rw(),
						z.isClass.Rw(),
						Simp(Fwd(addClass), Fwd(addIn), Fwd(mulIn)),
						sameClass(x.numeratorIn, y.numeratorIn, z.numeratorIn, inC))
				}))
			zeroAdds := a.Have(
				"zero / one is a left identity: zero / one plus r / u is (zero * u + r * one) / (one * u)",
				Statement{
					Binders: "∀X:set(prod(A, A)).",
					Hypotheses: []string{
						"X ∈ ring_localization(R.carrier, s)",
					},
					Conclusion: "fraction_add(R.carrier, s, fraction_zero(R.carrier, s), X) = X",
				},
				Derive(func(b *Argument) {
					X := b.FixAs[Set[Prod[A, A]]]("X")
					isFraction := b.Assume()
					x := represent(b, X, isFraction, "r", "u")
					inC := b.Have(
						"the denominator lies in c, s lying in c",
						"u ∈ R.carrier",
						By(inclusion, x.denominatorIn))
					b.Show(
						"and zero * u + r * one is r, one * u is u",
						x.isClass.Rw(),
						Unfold(FractionZeroDef),
						Simp(Fwd(addClass), Fwd(comm_ring.ZeroIn.Read(ring))),
						sameClass(x.numeratorIn, inC))
				}))
			negationAdds := a.Have(
				"-r / u is a left inverse of r / u: their sum is (-r * u + r * u) / (u * u)",
				Statement{
					Binders: "∀X:set(prod(A, A)).",
					Hypotheses: []string{
						"X ∈ ring_localization(R.carrier, s)",
					},
					Conclusion: "fraction_add(R.carrier, s, fraction_neg(R.carrier, s, X), X) = " +
						"fraction_zero(R.carrier, s)",
				},
				Derive(func(b *Argument) {
					X := b.FixAs[Set[Prod[A, A]]]("X")
					isFraction := b.Assume()
					x := represent(b, X, isFraction, "r", "u")
					inC := b.Have(
						"the denominator lies in c, s lying in c",
						"u ∈ R.carrier",
						By(inclusion, x.denominatorIn))
					cross := b.Have(
						"(-r * u + r * u) / (u * u) and zero / one have equal cross products",
						"(-r * u + r * u) * R.one = R.zero * (u * u)",
						ByArith(ring, x.numeratorIn, inC))
					b.Show(
						"so it is zero / one",
						x.isClass.Rw(),
						Unfold(FractionZeroDef),
						Simp(Fwd(negClass), Fwd(addClass), Fwd(comm_ring.NegIn.Read(ring))),
						By(
							classCross,
							multiplicative,
							cross,
							addIn,
							mulIn,
							comm_ring.NegIn.Read(ring),
							comm_ring.ZeroIn.Read(ring),
							closed,
							oneIn,
							x.numeratorIn,
							x.denominatorIn,
							inC))
				}))
			sumCommutes := a.Have(
				"the sum commutes",
				Statement{
					Binders: "∀X Y:set(prod(A, A)).",
					Hypotheses: []string{
						"X ∈ ring_localization(R.carrier, s)",
						"Y ∈ ring_localization(R.carrier, s)",
					},
					Conclusion: "fraction_add(R.carrier, s, X, Y) = fraction_add(R.carrier, s, Y, X)",
				},
				Derive(func(b *Argument) {
					X := b.FixAs[Set[Prod[A, A]]]("X")
					Y := b.FixAs[Set[Prod[A, A]]]("Y")
					given := b.Conjuncts(
						b.Assume(),
						"X is a fraction",
						"Y is a fraction")
					x := represent(b, X, given[0], "r₁", "u₁")
					y := represent(b, Y, given[1], "r₂", "u₂")
					inC := b.Have(
						"the denominators lie in c, s lying in c",
						"u₁ ∈ R.carrier ∧ u₂ ∈ R.carrier",
						By(inclusion, x.denominatorIn, y.denominatorIn))
					b.Show(
						"both sums are the class of r₁ * u₂ + r₂ * u₁ over u₁ * u₂, spelled two ways",
						x.isClass.Rw(),
						y.isClass.Rw(),
						Simp(Fwd(addClass)),
						sameClass(x.numeratorIn, y.numeratorIn, inC))
				}))
			additiveGroup := a.Have(
				"under the sum the fractions form a group",
				"group_on(mk_group(fraction_add(R.carrier, s), "+
					"        fraction_zero(R.carrier, s), "+
					"        fraction_neg(R.carrier, s), "+
					"        ring_localization(R.carrier, s)))",
				By(group.GroupOn, zeroFraction, sumIn, negationIn, sumAssociates, zeroAdds, negationAdds))
			abelian := a.Have(
				"an abelian one",
				"abelian_group_on(mk_group(fraction_add(R.carrier, s), "+
					"        fraction_zero(R.carrier, s), "+
					"        fraction_neg(R.carrier, s), "+
					"        ring_localization(R.carrier, s)))",
				By(abelian_group.AbelianGroupOn, additiveGroup, sumCommutes))

			// The monoid of fractions under the product.
			oneFraction := a.Have(
				"one / one is a fraction",
				"fraction_one(R.carrier, s) ∈ ring_localization(R.carrier, s)",
				Unfold(FractionOneDef),
				By(classIn, comm_ring.OneIn.Read(ring), oneIn))
			productIn := a.Have(
				"a product of fractions is a fraction",
				Statement{
					Binders: "∀X Y:set(prod(A, A)).",
					Hypotheses: []string{
						"X ∈ ring_localization(R.carrier, s)",
						"Y ∈ ring_localization(R.carrier, s)",
					},
					Conclusion: "fraction_mul(R.carrier, s, X, Y) ∈ ring_localization(R.carrier, s)",
				},
				Derive(func(b *Argument) {
					X := b.FixAs[Set[Prod[A, A]]]("X")
					Y := b.FixAs[Set[Prod[A, A]]]("Y")
					given := b.Conjuncts(
						b.Assume(),
						"X is a fraction",
						"Y is a fraction")
					x := represent(b, X, given[0], "r₁", "u₁")
					y := represent(b, Y, given[1], "r₂", "u₂")
					b.Show(
						"the product is the class of r₁ * r₂ over u₁ * u₂",
						x.isClass.Rw(),
						y.isClass.Rw(),
						Simp(Fwd(mulClass)),
						By(classIn, mulIn, closed, x.numeratorIn, x.denominatorIn, y.numeratorIn, y.denominatorIn))
				}))
			productCommutes := a.Have(
				"the product commutes",
				Statement{
					Binders: "∀X Y:set(prod(A, A)).",
					Hypotheses: []string{
						"X ∈ ring_localization(R.carrier, s)",
						"Y ∈ ring_localization(R.carrier, s)",
					},
					Conclusion: "fraction_mul(R.carrier, s, X, Y) = fraction_mul(R.carrier, s, Y, X)",
				},
				Derive(func(b *Argument) {
					X := b.FixAs[Set[Prod[A, A]]]("X")
					Y := b.FixAs[Set[Prod[A, A]]]("Y")
					given := b.Conjuncts(
						b.Assume(),
						"X is a fraction",
						"Y is a fraction")
					x := represent(b, X, given[0], "r₁", "u₁")
					y := represent(b, Y, given[1], "r₂", "u₂")
					inC := b.Have(
						"the denominators lie in c, s lying in c",
						"u₁ ∈ R.carrier ∧ u₂ ∈ R.carrier",
						By(inclusion, x.denominatorIn, y.denominatorIn))
					b.Show(
						"both products are the class of r₁ * r₂ over u₁ * u₂, spelled two ways",
						x.isClass.Rw(),
						y.isClass.Rw(),
						Simp(Fwd(mulClass)),
						sameClass(x.numeratorIn, y.numeratorIn, inC))
				}))
			productAssociates := a.Have(
				"the product associates",
				Statement{
					Binders: "∀X Y Z:set(prod(A, A)).",
					Hypotheses: []string{
						"X ∈ ring_localization(R.carrier, s)",
						"Y ∈ ring_localization(R.carrier, s)",
						"Z ∈ ring_localization(R.carrier, s)",
					},
					Conclusion: "fraction_mul(R.carrier, s, X, fraction_mul(R.carrier, s, Y, Z)) = " +
						"fraction_mul(R.carrier, s, fraction_mul(R.carrier, s, X, Y), Z)",
				},
				Derive(func(b *Argument) {
					X := b.FixAs[Set[Prod[A, A]]]("X")
					Y := b.FixAs[Set[Prod[A, A]]]("Y")
					Z := b.FixAs[Set[Prod[A, A]]]("Z")
					given := b.Conjuncts(
						b.Assume(),
						"X is a fraction",
						"Y is a fraction",
						"Z is a fraction")
					x := represent(b, X, given[0], "r₁", "u₁")
					y := represent(b, Y, given[1], "r₂", "u₂")
					z := represent(b, Z, given[2], "r₃", "u₃")
					inC := b.Have(
						"the denominators lie in c, s lying in c",
						"u₁ ∈ R.carrier ∧ u₂ ∈ R.carrier ∧ u₃ ∈ R.carrier",
						By(inclusion, x.denominatorIn, y.denominatorIn, z.denominatorIn))
					b.Have(
						"the inner products have their denominators in s, so the class laws apply to the inner classes",
						"u₁ * u₂ ∈ s ∧ u₂ * u₃ ∈ s",
						By(closed, x.denominatorIn, y.denominatorIn, z.denominatorIn))
					b.Show(
						"both groupings are the class of r₁ * r₂ * r₃ over u₁ * u₂ * u₃, grouped two ways",
						x.isClass.Rw(),
						y.isClass.Rw(),
						z.isClass.Rw(),
						Simp(Fwd(mulClass), Fwd(mulIn)),
						sameClass(x.numeratorIn, y.numeratorIn, z.numeratorIn, inC))
				}))
			oneMultiplies := a.Have(
				"one / one is a left identity: one / one times r / u is (one * r) / (one * u)",
				Statement{
					Binders: "∀X:set(prod(A, A)).",
					Hypotheses: []string{
						"X ∈ ring_localization(R.carrier, s)",
					},
					Conclusion: "fraction_mul(R.carrier, s, fraction_one(R.carrier, s), X) = X",
				},
				Derive(func(b *Argument) {
					X := b.FixAs[Set[Prod[A, A]]]("X")
					isFraction := b.Assume()
					x := represent(b, X, isFraction, "r", "u")
					inC := b.Have(
						"the denominator lies in c, s lying in c",
						"u ∈ R.carrier",
						By(inclusion, x.denominatorIn))
					b.Show(
						"and one * r is r, one * u is u",
						x.isClass.Rw(),
						Unfold(FractionOneDef),
						Simp(Fwd(mulClass), Fwd(comm_ring.OneIn.Read(ring))),
						sameClass(x.numeratorIn, inC))
				}))
			multiplicativeMonoid := a.Have(
				"under the product the fractions form a commutative monoid",
				"comm_monoid_on(ring_localization(R.carrier, s), "+
					"    fraction_mul(R.carrier, s), "+
					"    fraction_one(R.carrier, s))",
				By(
					comm_monoid.CommMonoidOn,
					oneFraction,
					productIn,
					productCommutes,
					productAssociates,
					oneMultiplies))

			// The two operations together.
			distributes := a.Have(
				"the product distributes over the sum",
				Statement{
					Binders: "∀X Y Z:set(prod(A, A)).",
					Hypotheses: []string{
						"X ∈ ring_localization(R.carrier, s)",
						"Y ∈ ring_localization(R.carrier, s)",
						"Z ∈ ring_localization(R.carrier, s)",
					},
					Conclusion: "fraction_mul(R.carrier, s, X, fraction_add(R.carrier, s, Y, Z)) = " +
						"fraction_add(R.carrier, s, fraction_mul(R.carrier, s, X, Y), fraction_mul(R.carrier, s, X, Z))",
				},
				Derive(func(b *Argument) {
					X := b.FixAs[Set[Prod[A, A]]]("X")
					Y := b.FixAs[Set[Prod[A, A]]]("Y")
					Z := b.FixAs[Set[Prod[A, A]]]("Z")
					given := b.Conjuncts(
						b.Assume(),
						"X is a fraction",
						"Y is a fraction",
						"Z is a fraction")
					x := represent(b, X, given[0], "r₁", "u₁")
					y := represent(b, Y, given[1], "r₂", "u₂")
					z := represent(b, Z, given[2], "r₃", "u₃")
					inC := b.Have(
						"the denominators lie in c, s lying in c",
						"u₁ ∈ R.carrier ∧ u₂ ∈ R.carrier ∧ u₃ ∈ R.carrier",
						By(inclusion, x.denominatorIn, y.denominatorIn, z.denominatorIn))
					cross := b.Have(
						"the cross products of the two sides agree: each is r₁ * u₁ * (r₂ * u₃ + r₃ * u₂) * (u₁ * u₂ * u₃)",
						"r₁ * (r₂ * u₃ + r₃ * u₂) * (u₁ * u₂ * (u₁ * u₃)) = "+
							"(r₁ * r₂ * (u₁ * u₃) + r₁ * r₃ * (u₁ * u₂)) * (u₁ * (u₂ * u₃))",
						ByArith(ring, x.numeratorIn, y.numeratorIn, z.numeratorIn, inC))
					b.Have(
						"the inner sum and products have their denominators "+
							"in s, so the class laws apply to the inner classes",
						"u₂ * u₃ ∈ s ∧ u₁ * u₂ ∈ s ∧ u₁ * u₃ ∈ s",
						By(closed, x.denominatorIn, y.denominatorIn, z.denominatorIn))
					b.Show(
						"so the two sides are one class",
						x.isClass.Rw(),
						y.isClass.Rw(),
						z.isClass.Rw(),
						Simp(Fwd(addClass), Fwd(mulClass), Fwd(addIn), Fwd(mulIn)),
						By(
							classCross,
							multiplicative,
							cross,
							addIn,
							mulIn,
							closed,
							x.numeratorIn,
							x.denominatorIn,
							y.numeratorIn,
							y.denominatorIn,
							z.numeratorIn,
							z.denominatorIn,
							inC))
				}))
			difference := a.Have(
				"the difference of two fractions is the sum with the negation, by the difference's definition",
				Statement{
					Binders: "∀X Y:set(prod(A, A)).",
					Hypotheses: []string{
						"X ∈ ring_localization(R.carrier, s)",
						"Y ∈ ring_localization(R.carrier, s)",
					},
					Conclusion: "fraction_sub(R.carrier, s, X, Y) = " +
						"fraction_add(R.carrier, s, X, fraction_neg(R.carrier, s, Y))",
				},
				Unfold(FractionSubDef))
			fractionRing := a.TermAs[RingOps[Set[Prod[A, A]]]]("«fractionRingRecord»")
			additive := a.Have(
				"the additive group of the fraction ring record is the abelian group already proved",
				"abelian_group_on(additive_group(«fractionRingRecord»))",
				Simp(
					Fwd(module_record.AdditiveGroupDef),
					Fwd(module_record.RingAddDef),
					Fwd(module_record.RingZeroDef),
					Fwd(module_record.RingNegDef),
					Fwd(module_record.RingCarrierDef)),
				By(abelian))
			a.Show(
				"with distributivity and the difference, a commutative ring",
				By(comm_ring.CommRingOn.At(fractionRing), additive, multiplicativeMonoid, distributes, difference))
		}),
})}

// ToFractionHomomorphism — r ↦ r / one is a homomorphism from the ring
// into its fractions: the class laws at the denominator one, read through
// the identity, carry the sum and the product over.
var ToFractionHomomorphism = toFractionHomomorphismThm{family.Add(registry.ProofEntry{
	Name: "ToFractionHomomorphism",
	Key:  "prop_b80dee9eabefc187",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀s:set(A).",
		Hypotheses: []string{
			"multiplicative_set(R.carrier, s)",
		},
		Conclusion: "ring_homomorphism(R, «fractionRingRecord», to_fraction(R.carrier, s))",
		Abbrev: Abbrev{
			{Name: "fractionRingRecord", Text: "mk_ring(fraction_add(R.carrier, s), " +
				"    fraction_zero(R.carrier, s), " +
				"    fraction_neg(R.carrier, s), " +
				"    fraction_mul(R.carrier, s), " +
				"    fraction_one(R.carrier, s), " +
				"    fraction_sub(R.carrier, s), " +
				"    ring_localization(R.carrier, s))"},
		},
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], s *Expr[Set[A]], multiplicative Fact) {
			oneIn := a.Have(
				"one is a denominator in s",
				"R.one ∈ s",
				Unfold(MultiplicativeSetDef))
			one := a.TermAs[A]("R.one")
			rightIdentity := comm_monoid.RightIdentityOn.Read(comm_ring.MulMonoidOn.Read(ring))
			a.Show(
				"r ↦ r / one has a ring as target and preserves the carrier, sum, product, and one",
				Unfold(ring_homomorphism.RingHomomorphism),
				SplitConjAll(
					Case(
						"the source is the given commutative ring",
						By(ring)),
					Case(
						"the fractions form a commutative ring",
						By(multiplicative, LocalizationRing.Read(ring).At(s))),
					Case(
						"each source element maps to its class with denominator one",
						Derive(func(b *Argument) {
							x := b.FixAs[A]("x")
							inR := b.Assume()
							b.Do(Unfold(ToFractionDef), Simp(Fwd(RingLocalizationMember)))
							b.Take(x)
							b.Take(one)
							b.Show(
								"the numerator lies in the ring and one lies in s",
								By(inR, oneIn))
						})),
					Case(
						"the sum of x over one and y over one is their sum over one",
						Derive(func(b *Argument) {
							b.FixAs[A]("x")
							b.FixAs[A]("y")
							b.Assume()
							b.Show(
								"the class formula for addition reduces by the unit laws",
								Unfold(ToFractionDef),
								Simp(Fwd(FractionAddClass.Read(ring)), Fwd(rightIdentity), Fwd(comm_ring.OneIn.Read(ring))),
								Basic())
						})),
					Case(
						"the product of x over one and y over one is their product over one",
						Derive(func(b *Argument) {
							b.FixAs[A]("x")
							b.FixAs[A]("y")
							b.Assume()
							b.Show(
								"the class formula for multiplication reduces by the unit law",
								Unfold(ToFractionDef),
								Simp(Fwd(FractionMulClass.Read(ring)), Fwd(rightIdentity), Fwd(comm_ring.OneIn.Read(ring))),
								Basic())
						})),
					Case(
						"one maps to the unit fraction",
						Simp(Fwd(ToFractionDef), Fwd(FractionOneDef)),
						Basic())))
		}),
})}

// DenominatorUnit — a denominator becomes a unit among the fractions. The
// product of u / one and one / u is the class of (u * one, one * u), whose
// cross products with (one, one) are both u: so the product is one / one.
var DenominatorUnit = denominatorUnitThm{family.Add(registry.ProofEntry{
	Name: "DenominatorUnit",
	Key:  "prop_4594af7de32e7008",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀s:set(A). ∀u:A.",
		Hypotheses: []string{
			"multiplicative_set(R.carrier, s)",
			"u ∈ s",
		},
		Conclusion: "fraction_mul(R.carrier, " +
			"    s, " +
			"    to_fraction(R.carrier, s, u), " +
			"    fraction_class(R.carrier, s, R.one, u)) = " +
			"fraction_one(R.carrier, s)",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], s *Expr[Set[A]], u *Expr[A], hypotheses Fact) {
			parts := a.Conjuncts(
				hypotheses,
				"s is a multiplicative set",
				"u lies in s")
			multiplicative, uIn := parts[0], parts[1]
			conditions := a.Conjuncts(
				a.Unfolded(multiplicative, MultiplicativeSetDef),
				"s lies in c",
				"one lies in s",
				"s is closed under the product")
			subset, oneIn, closed := conditions[0], conditions[1], conditions[2]
			uInC := a.Have(
				"u lies in c, s lying in c",
				"u ∈ R.carrier",
				BySets(subset, uIn))
			one := a.TermAs[A]("R.one")
			cross := a.Have(
				"the cross products of (u * one, one * u) and (one, one) are both u",
				"u * R.one * R.one = R.one * (R.one * u)",
				ByArith(ring, uInC))
			a.Show(
				"so the product is the unit fraction",
				CalcEq(
					Leg(
						a.TermAs[Set[Prod[A, A]]](
							"fraction_mul(R.carrier, "+
								"    s, "+
								"    fraction_class(R.carrier, s, u, R.one), "+
								"    fraction_class(R.carrier, s, R.one, u))"),
						"u / one is the class of (u, one)",
						Unfold(ToFractionDef)),
					Leg(
						a.TermAs[Set[Prod[A, A]]]("fraction_class(R.carrier, s, u * R.one, R.one * u)"),
						"a product of classes is the class of the products of the representatives",
						By(
							FractionMulClass.Read(ring).AsFact().At(s, u, one, one, u),
							multiplicative,
							uInC,
							oneIn,
							comm_ring.OneIn.Read(ring),
							uIn)),
					FinalLeg(
						"so the product is one / one",
						Unfold(FractionOneDef),
						By(
							FractionClassCross.Read(ring).AsFact().At(
								s, a.TermAs[A]("u * R.one"), a.TermAs[A]("R.one * u"), one, one),
							multiplicative,
							comm_ring.MulIn.Read(ring),
							comm_ring.OneIn.Read(ring),
							closed,
							uInC,
							uIn,
							oneIn,
							cross)),
				))
		}),
})}

// DenominatorClearsFraction — a denominator clears its fraction: b / one
// times a / b is a / one. The two fractions multiply to (b * a) / b, whose
// cross products with a / one agree.
var DenominatorClearsFraction = denominatorClearsFractionThm{family.Add(registry.ProofEntry{
	Name: "DenominatorClearsFraction",
	Key:  "prop_fa40f66b9730846c",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀s:set(A). ∀a b:A.",
		Hypotheses: []string{
			"multiplicative_set(R.carrier, s)",
			"a ∈ R.carrier",
			"b ∈ s",
		},
		Conclusion: "fraction_mul(R.carrier, " +
			"    s, " +
			"    fraction_class(R.carrier, s, b, R.one), " +
			"    fraction_class(R.carrier, s, a, b)) = " +
			"fraction_class(R.carrier, s, a, R.one)",
	},
		func(
			arg *Argument,
			ring comm_ring.CommRingFact[on.R],
			s *Expr[Set[A]],
			a, b *Expr[A],
			hypotheses Fact,
		) {
			parts := arg.Conjuncts(
				hypotheses,
				"s is a multiplicative set",
				"a lies in c",
				"b lies in s")
			multiplicative, aIn, bIn := parts[0], parts[1], parts[2]
			conditions := arg.Conjuncts(
				arg.Unfolded(multiplicative, MultiplicativeSetDef),
				"s lies in c",
				"one lies in s",
				"s is closed under the product")
			bInC := arg.Have(
				"b lies in c, s lying in c",
				"b ∈ R.carrier",
				BySets(conditions[0], bIn))
			cross := arg.Have(
				"the two fractions have equal cross products",
				"b * a * R.one = a * b",
				ByArith(ring, aIn, bInC))
			arg.Show(
				"the denominator clears the fraction",
				CalcEq(
					Leg(
						arg.TermAs[Set[Prod[A, A]]]("fraction_class(R.carrier, s, b * a, b)"),
						"multiply numerators and denominators, one times b being b",
						Simp(
							Fwd(FractionMulClass.Read(ring)),
							Fwd(comm_monoid.LeftIdentityOn.Read(comm_ring.MulMonoidOn.Read(ring)))),
						Refl()),
					FinalLeg(
						"the cross products agree",
						By(
							comm_ring.MulIn.Read(ring),
							cross,
							multiplicative,
							aIn,
							bIn,
							bInC,
							conditions[1],
							At(FractionClassCross.Read(ring), s, arg.TermAs[A]("b * a"), b, a, arg.TermAs[A]("R.one"))))))
		}),
})}
