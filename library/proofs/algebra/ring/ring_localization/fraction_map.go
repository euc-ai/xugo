// fraction_map.go — localization maps induced by homomorphisms of rings.

package ring_localization

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/registry"
)

// FractionMapDef — the target classes of the images of all representatives,
// united; FractionMapClass reads this union as one class on the carrier.
var FractionMapDef = fractionMapDefThm{family.Define(registry.DefEntry{
	Name:    "FractionMapDef",
	Key:     "prop_d3bee87fe75870c5",
	Const:   "fraction_map",
	Type:    "(B → B → B) → set(B) → (A → B) → set(A) → set(B) → set(prod(A, A)) → set(prod(B, B))",
	Bundles: []string{},
	Equations: []string{
		"∀mul':(B → B → B). ∀c':set(B). ∀φ:(A → B). ∀s:set(A). ∀s':set(B). ∀X:set(prod(A, A)). " +
			"    fraction_map(mul', c', φ, s, s', X) = " +
			"    ⋃{fraction_class(mul', c', s', φ(a), φ(u)) | a:A, u:A | (a, u) ∈ X}",
	},
	Deps: []registry.EntryLike{FractionClassDef},
})}

// FractionMapClass — the union defining the map is one class. A pair
// (x, y) of the class of (a, u) is related to it by some t of s,
// t * (a * y) = t * (x * u); φ keeps the products of members of c, so
// φ(t) relates (φ(x), φ(y)) to (φ(a), φ(u)), and φ(t) lies in s'. Every
// class in the union is therefore the class of (φ(a), φ(u)), and the
// union holds it, (a, u) lying in its own class — whether or not either
// ring of fractions is the zero ring.
var FractionMapClass = fractionMapClassThm{family.Add(registry.ProofEntry{
	Name: "FractionMapClass",
	Key:  "prop_bd3615637e4fd57d",
	Build: family.Theorem(Statement{
		Binders: "∀φ:ring_homomorphism(A, B). ∀s:set(A). ∀s':set(B). ∀a u:A.",
		Hypotheses: []string{
			"multiplicative_set(R.carrier, s)",
			"multiplicative_set(S.carrier, s')",
			"∀v:A. v ∈ s ⇒ φ(v) ∈ s'",
			"a ∈ R.carrier",
			"u ∈ s",
		},
		Conclusion: "fraction_map(S.mul, S.carrier, φ, s, s', fraction_class(R.carrier, s, a, u)) = " +
			"fraction_class(S.carrier, s', φ(a), φ(u))",
	},
		func(
			arg *Argument,
			φ ring_homomorphism.RingHomomorphismFact[on.R, on.S],
			s *Expr[Set[A]],
			s2 *Expr[Set[B]],
			a, u *Expr[A],
			hypotheses Fact,
		) {
			parts := arg.Conjuncts(
				hypotheses,
				"s is a multiplicative set",
				"s' is a multiplicative set of the target",
				"φ carries s into s'",
				"a lies in c",
				"u lies in s")
			multiplicative, targetMultiplicative, preserves, aIn, uIn :=
				parts[0], parts[1], parts[2], parts[3], parts[4]
			conditions := arg.Conjuncts(
				arg.Unfolded(multiplicative, MultiplicativeSetDef),
				"s lies in c",
				"one lies in s",
				"s is closed under the product")
			subset, oneIn := conditions[0], conditions[1]
			keepsProducts := Simp(
				Fwd(ring_homomorphism.MapMul.Read(φ)),
				Fwd(comm_ring.MulIn.Read(ring_homomorphism.Source.Read(φ))))
			mapped := arg.Have(
				"each pair (x, y) of the class maps to the class of (φ(a), φ(u))",
				Statement{
					Binders: "∀x y:A.",
					Hypotheses: []string{
						"(x, y) ∈ fraction_class(R.carrier, s, a, u)",
					},
					Conclusion: "fraction_class(S.carrier, s', φ(x), φ(y)) = fraction_class(S.carrier, s', φ(a), φ(u))",
				},
				Derive(func(b *Argument) {
					b.FixAs[A]("x")
					b.FixAs[A]("y")
					inClass := b.Assume()
					pair := b.Conjuncts(
						b.Have(
							"so x lies in c, y in s, and some t of s relates (a, u) to (x, y)",
							"x ∈ R.carrier ∧ y ∈ s ∧ (∃t:A. t ∈ s ∧ t * (a * y) = t * (x * u))",
							By(FractionClassMember, inClass)),
						"x lies in c",
						"y lies in s",
						"some t of s relates (a, u) to (x, y)")
					xIn, yIn := pair[0], pair[1]
					_, tFacts := b.UnpackAs[A](pair[2], "t")
					tParts := b.Conjuncts(
						tFacts,
						"t lies in s",
						"and relates (a, u) to (x, y)")
					b.Have(
						"t, y and u lie in c, s lying in c, where φ keeps products",
						"t ∈ R.carrier ∧ y ∈ R.carrier ∧ u ∈ R.carrier",
						BySets(subset, tParts[0], yIn, uIn))
					related := b.Have(
						"φ(t) relates (φ(x), φ(y)) to (φ(a), φ(u)): t's relation, carried by φ",
						"φ(t) * (φ(x) * φ(u)) = φ(t) * (φ(a) * φ(y))",
						CalcEq(
							Leg(
								b.TermAs[B]("φ(t * (x * u))"),
								"φ keeps the products of members of c",
								keepsProducts,
								Refl()),
							Leg(
								b.TermAs[B]("φ(t * (a * y))"),
								"t relates (a, u) to (x, y)",
								By(Normalized, tParts[1])),
							FinalLeg(
								"and φ keeps these products too",
								keepsProducts,
								Refl()),
						))
					witnessed := b.Have(
						"so some t of s' relates (φ(x), φ(y)) to (φ(a), φ(u))",
						"∃t:B. t ∈ s' ∧ t * (φ(x) * φ(u)) = t * (φ(a) * φ(y))",
						Derive(func(d *Argument) {
							d.Take(d.TermAs[B]("φ(t)"))
							d.Show(
								"φ carries the denominator t into s', and φ(t) relates the images",
								By(preserves, tParts[0], related))
						}))
					b.Show(
						"so the images of (x, y) and of (a, u) have one class in the target",
						By(
							FractionClassEq.Read(ring_homomorphism.Target.Read(φ)).AsFact().At(s2,
								b.TermAs[B]("φ(x)"), b.TermAs[B]("φ(y)"), b.TermAs[B]("φ(a)"), b.TermAs[B]("φ(u)")),
							targetMultiplicative,
							ring_homomorphism.MapIn.Read(φ),
							preserves,
							xIn,
							yIn,
							aIn,
							uIn,
							witnessed))
				}))
			own := arg.Have(
				"(a, u) lies in its own class: one relates it to itself",
				"(a, u) ∈ fraction_class(R.carrier, s, a, u)",
				By(FractionClassMember, aIn, uIn, oneIn))
			arg.Show(
				"so every class in the union is the class of (φ(a), φ(u)), which the union holds",
				Unfold(FractionMapDef),
				BySets(mapped, own))
		}),
})}

// FractionMapHomomorphism — localization maps preserve the ring operations.
var FractionMapHomomorphism = fractionMapHomomorphismThm{family.Add(registry.ProofEntry{
	Name: "FractionMapHomomorphism",
	Key:  "prop_99910a038bd5635f",
	Deps: []registry.EntryLike{FractionMapClass, LocalizationRing, FractionAddClass, FractionMulClass,
		ring_homomorphism.MapAdd, ring_homomorphism.MapMul, ring_homomorphism.MapOne},
	Build: family.Card(Statement{
		Binders: "∀φ:ring_homomorphism(A, B). ∀s:set(A). ∀s':set(B).",
		Hypotheses: []string{
			"multiplicative_set(R.carrier, s)",
			"multiplicative_set(S.carrier, s')",
			"∀u:A. u ∈ s ⇒ φ(u) ∈ s'",
		},
		Conclusion: "ring_homomorphism(localized_ring(R, s), " +
			"    localized_ring(S, s'), " +
			"    fraction_map(S.mul, S.carrier, φ, s, s'))",
	},
		"Use LocalizationRing on both carriers. Represent each source fraction, "+
			"read its image through FractionMapClass, and use the addition, "+
			"multiplication and one class laws with the corresponding laws of φ."),
})}

// FractionMapToFraction — the canonical maps commute with localization.
var FractionMapToFraction = fractionMapToFractionThm{family.Add(registry.ProofEntry{
	Name: "FractionMapToFraction",
	Key:  "prop_727cec78c751883c",
	Deps: []registry.EntryLike{FractionMapClass, ToFractionDef, ring_homomorphism.MapOne},
	Build: family.Card(Statement{
		Binders: "∀φ:ring_homomorphism(A, B). ∀s:set(A). ∀s':set(B). ∀a:A.",
		Hypotheses: []string{
			"multiplicative_set(R.carrier, s)",
			"multiplicative_set(S.carrier, s')",
			"∀u:A. u ∈ s ⇒ φ(u) ∈ s'",
			"a ∈ R.carrier",
		},
		Conclusion: "fraction_map(S.mul, S.carrier, φ, s, s', to_fraction(R.carrier, s, a)) = " +
			"to_fraction(S.carrier, s', φ(a))",
	},
		"Apply FractionMapClass to a/one; φ sends one to the target one."),
})}

// FractionMapCompose — localization respects composition on source
// fractions. Write X as the class r/u (RingLocalizationMember). The
// composite χ ∘ φ is a ring homomorphism from R to Q (RingHomCompose),
// and it carries the denominators s into those of Q by way of s'.
// FractionMapClass then evaluates each map at a class: along the
// composite r/u goes to χ(φ(r))/χ(φ(u)); along φ it goes to
// φ(r)/φ(u), whose numerator lies in S and denominator in s'; and χ
// sends that class to χ(φ(r))/χ(φ(u)) as well.
var FractionMapCompose = fractionMapComposeThm{family.Add(registry.ProofEntry{
	Name: "FractionMapCompose",
	Key:  "prop_859d95a89d2458af",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). " +
			"∀S:comm_ring_on(B). " +
			"∀Q:comm_ring_on(C). " +
			"∀φ:(A → B). " +
			"∀χ:(B → C). " +
			"∀s:set(A). " +
			"∀s':set(B). " +
			"∀s'':set(C). " +
			"∀X:set(prod(A, A)).",
		Hypotheses: []string{
			"ring_homomorphism(R, S, φ)",
			"ring_homomorphism(S, Q, χ)",
			"multiplicative_set(R.carrier, s)",
			"multiplicative_set(S.carrier, s')",
			"multiplicative_set(Q.carrier, s'')",
			"∀u:A. u ∈ s ⇒ φ(u) ∈ s'",
			"∀v:B. v ∈ s' ⇒ χ(v) ∈ s''",
			"X ∈ ring_localization(R.carrier, s)",
		},
		Conclusion: "fraction_map(Q.mul, Q.carrier, λa:A. χ(φ(a)), s, s'', X) = " +
			"fraction_map(Q.mul, Q.carrier, χ, s', s'', fraction_map(S.mul, S.carrier, φ, s, s', X))",
	},
		func(
			arg *Argument,
			R comm_ring.CommRingFact[on.R],
			S comm_ring.CommRingFact[on.S],
			Q Fact,
			φ *Arrow[A, B],
			χ *Arrow[B, C],
			s *Expr[Set[A]],
			sPrime *Expr[Set[B]],
			sDoublePrime *Expr[Set[C]],
			X *Expr[Set[Prod[A, A]]],
			hypotheses Fact,
		) {
			parts := arg.Conjuncts(
				hypotheses,
				"φ is a ring homomorphism from R to S",
				"χ is a ring homomorphism from S to Q",
				"s is a multiplicative set of R",
				"s' is a multiplicative set of S",
				"s'' is a multiplicative set of Q",
				"φ carries s into s'",
				"χ carries s' into s''",
				"X is a fraction of R with denominator in s")
			homφ, homχ := parts[0], parts[1]
			multiplicativeR, multiplicativeS, multiplicativeQ := parts[2], parts[3], parts[4]
			φDenominators, χDenominators, xIn := parts[5], parts[6], parts[7]
			composite := arg.Have(
				"χ ∘ φ is a ring homomorphism from R to Q",
				"ring_homomorphism(R, Q, λa:A. χ(φ(a)))",
				By(ring_homomorphism.RingHomCompose, homφ, homχ))
			_, _, representative := arg.Obtain2As[A, A](
				"write X as the class of some r of R over some u of s",
				"∃r u:A. r ∈ R.carrier ∧ u ∈ s ∧ X = fraction_class(R.carrier, s, r, u)",
				By(xIn, RingLocalizationMember))
			pair := arg.Conjuncts(
				representative,
				"r lies in R",
				"u lies in s",
				"X is the class of (r, u)")
			rIn, uIn, isClass := pair[0], pair[1], pair[2]
			arg.Show(
				"both sides are the class of χ(φ(r)) over χ(φ(u))",
				isClass.Rw(),
				CalcEq(
					Leg(
						arg.TermAs[Set[Prod[C, C]]]("fraction_class(Q.carrier, s'', χ(φ(r)), χ(φ(u)))"),
						"the composite sends r/u to χ(φ(r))/χ(φ(u)), carrying s into s'' through s'",
						By(
							FractionMapClass.Read(composite),
							multiplicativeR,
							multiplicativeQ,
							φDenominators,
							χDenominators,
							rIn,
							uIn)),
					Leg(
						arg.TermAs[Set[Prod[C, C]]](
							"fraction_map(Q.mul, Q.carrier, χ, s', s'', fraction_class(S.carrier, s', φ(r), φ(u)))"),
						"χ sends φ(r)/φ(u) to the same class, φ(r) lying in S and φ(u) in s'",
						By(
							FractionMapClass.Read(homχ),
							multiplicativeS,
							multiplicativeQ,
							χDenominators,
							ring_homomorphism.MapIn.Read(homφ),
							rIn,
							φDenominators,
							uIn)),
					FinalLeg(
						"φ sends r/u to φ(r)/φ(u)",
						Simp(Fwd(FractionMapClass.Read(homφ))),
						Refl()),
				))
		}),
})}

// FractionMapIdentity — the identity fixes each fraction in its carrier. A
// fraction X is the class of some r over some u, r in c and u in s
// (RingLocalizationMember); the identity is a homomorphism from the ring
// to itself carrying s into s, so FractionMapClass sends the class of
// (r, u) to the class of (r, u), which is X.
var FractionMapIdentity = fractionMapIdentityThm{family.Add(registry.ProofEntry{
	Name: "FractionMapIdentity",
	Key:  "prop_dfeb4139dc50c921",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀s:set(A). ∀X:set(prod(A, A)).",
		Hypotheses: []string{
			"multiplicative_set(R.carrier, s)",
			"X ∈ ring_localization(R.carrier, s)",
		},
		Conclusion: "fraction_map(R.mul, R.carrier, λa:A. a, s, s, X) = X",
	},
		func(
			a *Argument,
			ring comm_ring.CommRingFact[on.R],
			s *Expr[Set[A]],
			X *Expr[Set[Prod[A, A]]],
			hypotheses Fact,
		) {
			parts := a.Conjuncts(
				hypotheses,
				"s is a multiplicative set",
				"X is a fraction of c at s")
			multiplicative, fraction := parts[0], parts[1]
			r, u, represented := a.Obtain2As[A, A](
				"so X is the class of some r of c over some u of s",
				"∃r u:A. r ∈ R.carrier ∧ u ∈ s ∧ X = fraction_class(R.carrier, s, r, u)",
				By(fraction, RingLocalizationMember))
			representative := a.Conjuncts(
				represented,
				"r lies in c",
				"u lies in s",
				"X is the class of (r, u)")
			rIn, uIn, isClass := representative[0], representative[1], representative[2]
			identity := ring_homomorphism.RingHomIdentity.Read(ring)
			a.Show(
				"the identity carries s into s, so it sends the class of (r, u) to the class of (r, u)",
				isClass.Rw(),
				By(FractionMapClass.Read(identity).At(s, s, a.MemberOf[on.R](r, rIn), u), multiplicative, uIn))
		}),
})}
