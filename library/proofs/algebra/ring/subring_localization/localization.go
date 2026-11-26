// localization.go — the localization of a subring S of a field at a prime m:
// the fractions with numerator in S and denominator in S off m are a subring
// holding S and the inverse of every denominator, and m generates a proper
// ideal of it. Extending fractional ideals along subrings S ⊆ T, and to the
// localization, is multiplicative, keeps invertible ideals invertible with the
// extended inverse and takes signed powers to signed powers. At the ideal of a
// rational point, invertible in a chart S, the localization is a valuation
// ring: every nonzero function generates exactly one integer power of its
// maximal ideal, and the exponent is a valuation.

package subring_localization

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ideal_colength"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/quotient_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/signed_ideal_power"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// LocalRingSubring — the localization of a subring S at a prime m, the
// fractions of the field with numerator in S and denominator in S off m, is a
// subring holding S and the inverse of every denominator: a common denominator
// is a product of two, off m since m is prime.
var LocalRingSubring = localRingSubringThm{family.Add(registry.ProofEntry{
	Name: "LocalRingSubring",
	Key:  "prop_3f5abed725a1921d",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S m:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"prime_ideal(restrict_ring(field_ring(L), S), m)",
		},
		Conclusion: "subring(field_ring(L), subring_localization(field_ring(L), S, m)) ∧ " +
			"S ⊆ subring_localization(field_ring(L), S, m) ∧ " +
			"(∀u:A. " +
			"    u ∈ S ∧ u ∉ m ⇒ L.inv(u) ∈ subring_localization(field_ring(L), S, m) ∧ u * L.inv(u) = L.one)",
	},
		func(a *Argument, L field.FieldFact[on.L], S, m *Expr[Set[A]], h Fact) {
			given := a.Conjuncts(
				h,
				"S is a subring of L",
				"m is a prime of S")
			subring, prime := given[0], given[1]
			ringOn := field.RingOn.Read(L)
			ringOps := a.TermAs[RingOps[A]]("field_ring(L)")
			_, localDef := a.LetAs[Set[A]]("O", "subring_localization(field_ring(L), S, m)")
			membership := a.Have(
				"O is the fractions of L with numerator in S and denominator in S off m",
				"∀f:A. f ∈ O ⇔ f ∈ L.carrier ∧ (∃a b:A. a ∈ S ∧ b ∈ S ∧ b ∉ m ∧ f * b = a)",
				localDef.Rw(),
				BySets(SubringLocalizationDef.At(ringOps, S, m)))
			fraction := a.Have(
				"so a member of L that a denominator brings into S lies in O",
				"∀f p q:A. f ∈ L.carrier ∧ p ∈ S ∧ q ∈ S ∧ q ∉ m ∧ f * q = p ⇒ f ∈ O",
				Derive(func(b *Argument) {
					f, p, q := b.FixAs[A]("f"), b.FixAs[A]("p"), b.FixAs[A]("q")
					parts := b.Conjuncts(
						b.Assume(),
						"f lies in L",
						"p lies in S",
						"q lies in S",
						"q lies off m",
						"f · q = p")
					isFraction := b.Have(
						"f is the fraction p / q",
						"∃a b:A. a ∈ S ∧ b ∈ S ∧ b ∉ m ∧ f * b = a",
						Derive(func(c *Argument) {
							c.Take(p)
							c.Take(q)
							c.Show(
								"p and q are the numerator and the denominator",
								By(parts[1], parts[2], parts[3], parts[4]))
						}))
					b.Show(
						"so f lies in O",
						By(parts[0], isFraction, membership.At(f)))
				}))
			chartOps := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), S)")
			chart := a.Conjuncts(
				a.Have(
					"S lies in L and holds one, and m holds zero, misses "+
						"one, and its complement in S is closed under products",
					"S ⊆ L.carrier ∧ "+
						"L.one ∈ S ∧ "+
						"L.one ∉ m ∧ "+
						"L.zero ∈ m ∧ "+
						"(∀x y:A. x ∈ S ∧ y ∈ S ∧ x ∉ m ∧ y ∉ m ⇒ x * y ∉ m)",
					By(
						subring,
						prime,
						comm_ring.SubringDef.At(a.TermAs[RingOps[A]]("field_ring(L)"), S),
						ring_ideal.PrimeIdealDef.At(chartOps, m),
						ring_ideal.RingIdealDef.At(chartOps, m))),
				"S lies in L",
				"one lies in S",
				"one lies off m",
				"zero lies in m",
				"the denominators are closed under products")
			inL, oneIn, oneOff, zeroIn, products := chart[0], chart[1], chart[2], chart[3], chart[4]
			sumsAndProducts := a.Have(
				"O is closed under the sum and the product, over the product of the two denominators",
				"∀x y:A. x ∈ O ∧ y ∈ O ⇒ x + y ∈ O ∧ x * y ∈ O",
				Derive(func(b *Argument) {
					x, y := b.FixAs[A]("x"), b.FixAs[A]("y")
					members := b.Conjuncts(
						b.Assume(),
						"x lies in O",
						"so does y")
					xIn := b.Have(
						"x lies in L",
						"x ∈ L.carrier",
						By(membership.At(x), members[0]))
					yIn := b.Have(
						"y lies in L",
						"y ∈ L.carrier",
						By(membership.At(y), members[1]))
					p, q, xFraction := b.Obtain2As[A, A](
						"x is a fraction p / q",
						"∃p q:A. p ∈ S ∧ q ∈ S ∧ q ∉ m ∧ x * q = p",
						By(membership.At(x), members[0]))
					r, s, yFraction := b.Obtain2As[A, A](
						"y is a fraction r / s",
						"∃r s:A. r ∈ S ∧ s ∈ S ∧ s ∉ m ∧ y * s = r",
						By(membership.At(y), members[1]))
					first := b.Conjuncts(
						xFraction,
						"p lies in S",
						"q lies in S",
						"q lies off m",
						"x · q = p")
					second := b.Conjuncts(
						yFraction,
						"r lies in S",
						"s lies in S",
						"s lies off m",
						"y · s = r")
					memberships := b.Have(
						"the four lie in L",
						"p ∈ L.carrier ∧ q ∈ L.carrier ∧ r ∈ L.carrier ∧ s ∈ L.carrier",
						BySets(inL, first[0], first[1], second[0], second[1]))
					denominatorIn := b.Have(
						"the common denominator lies in S",
						"q * s ∈ S",
						By(subring, first[1], second[1], comm_ring.SubringMul.At(ringOps, S, q, s)))
					denominatorOff := b.Have(
						"and off m",
						"q * s ∉ m",
						By(first[1], first[2], second[1], second[2], products.At(q, s)))
					sumNumerator := b.Have(
						"the numerator of the sum lies in S",
						"p * s + r * q ∈ S",
						By(
							subring,
							first[0],
							first[1],
							second[0],
							second[1],
							comm_ring.SubringMul.At(ringOps, S, p, s),
							comm_ring.SubringMul.At(ringOps, S, r, q),
							comm_ring.SubringAdd.At(ringOps, S, b.TermAs[A]("p * s"), b.TermAs[A]("r * q"))))
					sumEquation := b.Have(
						"the sum over the common denominator",
						"(x + y) * (q * s) = p * s + r * q",
						ByArith(L, xIn, yIn, memberships, Scaled(s, first[3]), Scaled(q, second[3])))
					productNumerator := b.Have(
						"the numerator of the product lies in S",
						"p * r ∈ S",
						By(subring, first[0], second[0], comm_ring.SubringMul.At(ringOps, S, p, r)))
					productEquation := b.Have(
						"the product over the common denominator",
						"(x * y) * (q * s) = p * r",
						ByArith(L, xIn, yIn, memberships, Scaled(b.TermAs[A]("y * s"), first[3]), Scaled(p, second[3])))
					b.Show(
						"both are fractions",
						By(
							sumNumerator,
							denominatorIn,
							denominatorOff,
							sumEquation,
							productNumerator,
							productEquation,
							comm_ring.AddIn.Read(ringOn).AsFact().At(x, y),
							comm_ring.MulIn.Read(ringOn).AsFact().At(x, y),
							fraction.At(b.TermAs[A]("x + y"), b.TermAs[A]("p * s + r * q"), b.TermAs[A]("q * s")),
							fraction.At(b.TermAs[A]("x * y"), b.TermAs[A]("p * r"), b.TermAs[A]("q * s")),
							xIn,
							yIn))
				}))
			negations := a.Have(
				"O is closed under the negation, over the same denominator",
				"∀x:A. x ∈ O ⇒ -x ∈ O",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					member := b.Assume()
					xIn := b.Have(
						"x lies in L",
						"x ∈ L.carrier",
						By(membership.At(x), member))
					p, q, xFraction := b.Obtain2As[A, A](
						"x is a fraction p / q",
						"∃p q:A. p ∈ S ∧ q ∈ S ∧ q ∉ m ∧ x * q = p",
						By(membership.At(x), member))
					parts := b.Conjuncts(
						xFraction,
						"p lies in S",
						"q lies in S",
						"q lies off m",
						"x · q = p")
					memberships := b.Have(
						"p and q lie in L",
						"p ∈ L.carrier ∧ q ∈ L.carrier",
						BySets(inL, parts[0], parts[1]))
					negated := b.Have(
						"-x · q = -p",
						"-x * q = -p",
						ByArith(L, xIn, memberships, parts[3]))
					b.Show(
						"so -x is a fraction",
						By(
							parts[0],
							parts[1],
							parts[2],
							negated,
							xIn,
							subring,
							comm_ring.SubringNeg.At(ringOps, S, p),
							comm_ring.NegIn.Read(ringOn).AsFact().At(x),
							fraction.At(b.TermAs[A]("-x"), b.TermAs[A]("-p"), q)))
				}))
			fromS := a.Have(
				"S lies in O, over the denominator one",
				"S ⊆ O",
				Unfold(set_basic.SubsetDef),
				Derive(func(b *Argument) {
					s := b.FixAs[A]("s")
					sIn := b.Assume()
					sInL := b.Have(
						"s lies in L",
						"s ∈ L.carrier",
						BySets(inL, sIn))
					unit := b.Have(
						"s · 1 = s",
						"s * L.one = s",
						ByArith(L, sInL))
					b.Show(
						"s is s / 1",
						By(sIn, sInL, oneIn, oneOff, unit, fraction.At(s, s, b.TermAs[A]("L.one"))))
				}))
			inLocal := a.Have(
				"O lies in L",
				"O ⊆ L.carrier",
				Unfold(set_basic.SubsetDef),
				a.ForEach(func(f *Expr[A]) Action { return By(membership.At(f)) }))
			isSubring := a.Have(
				"so O is a subring of L, holding zero and one and closed under its operations",
				"subring(field_ring(L), O)",
				Simp(Fwd(comm_ring.SubringDef)),
				By(
					inLocal,
					a.Unfolded(fromS, set_basic.SubsetDef),
					subring,
					comm_ring.SubringDef.At(ringOps, S),
					sumsAndProducts,
					negations))
			denominators := a.Have(
				"a denominator is invertible in O",
				"∀u:A. u ∈ S ∧ u ∉ m ⇒ L.inv(u) ∈ O ∧ u * L.inv(u) = L.one",
				Derive(func(b *Argument) {
					u := b.FixAs[A]("u")
					parts := b.Conjuncts(
						b.Assume(),
						"u lies in S",
						"u lies off m")
					uIn := b.Have(
						"u lies in L",
						"u ∈ L.carrier",
						BySets(inL, parts[0]))
					nonzero := b.Have(
						"u is nonzero, since zero lies in m",
						"u ≠ L.zero",
						By(Normalized, parts[1], zeroIn))
					um := b.MemberOf[on.L](u, uIn)
					leftInverse := b.Have(
						"its inverse is the fraction 1 / u",
						"L.inv(u) * u = L.one",
						By(nonzero, field.MulLeftInverseOn.Read(L).At(um)))
					rightInverse := b.Have(
						"and on the right",
						"u * L.inv(u) = L.one",
						By(nonzero, field.MulRightInverseOn.Read(L).At(um)))
					b.Show(
						"so the inverse lies in O",
						By(
							parts[0],
							parts[1],
							oneIn,
							leftInverse,
							rightInverse,
							field.InvIn.Read(L).At(um),
							fraction.At(b.TermAs[A]("L.inv(u)"), b.TermAs[A]("L.one"), u)))
				}))
			a.Show(
				"O is a subring holding S, and the denominators are invertible in it",
				By(isSubring, fromS, denominators))
		}),
})}

// LocalExtensionCleared — the extension of a fractional ideal M of S to the
// localization O of S at a prime p is the set of members of L that a
// denominator off p brings into M. Those members form an O-submodule of L
// holding M, a common denominator being the product of two, so they hold the
// O-span of M; and each of them, y with b · y in M, is inv(b) · (b · y), a
// multiple from O of a member of M.
var LocalExtensionCleared = localExtensionClearedThm{family.Add(registry.ProofEntry{
	Name: "LocalExtensionCleared",
	Key:  "prop_dafa0d55aefe0e6f",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S p M:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"prime_ideal(«wfScalars», p)",
			"«wfFractional»(M)",
		},
		Conclusion: "«extended»(M) = {y:A | y ∈ L.carrier ∧ (∃b:A. b ∈ S ∧ b ∉ p ∧ b * y ∈ M)}",
		Abbrev: Abbrev{
			{Name: "extended", Text: "module_span( " +
				"    restrict_ring(field_ring(L), subring_localization(field_ring(L), S, p)), «wfField»)"},
		},
	},
		func(a *Argument, L field.FieldFact[on.L], S, p, M *Expr[Set[A]], h Fact) {
			given := a.Conjuncts(
				h,
				"S is a subring of L",
				"p is a prime of S",
				"M is a fractional ideal of S")
			subring, prime, fractional := given[0], given[1], given[2]
			O, oDef := a.LetAs[Set[A]]("O", "subring_localization(field_ring(L), S, p)")
			fieldRing := a.TermAs[RingOps[A]]("field_ring(L)")
			chartRing := a.TermAs[RingOps[A]]("«wfScalars»")
			localRing := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), O)")
			vectors := a.TermAs[module_record.ModuleOps[A, A]]("«wfField»")
			ringL := field.RingOn.Read(L)
			local := a.Conjuncts(
				a.Have(
					"O is a subring of L holding S, in which each denominator is a unit",
					"subring(field_ring(L), O) ∧ S ⊆ O ∧ (∀u:A. u ∈ S ∧ u ∉ p ⇒ L.inv(u) ∈ O ∧ u * L.inv(u) = L.one)",
					oDef.Rw(),
					By(subring, prime, LocalRingSubring.Read(L).At(S, p))),
				"O is a subring of L",
				"it holds S",
				"it inverts the denominators")
			subringO, units := local[0], local[2]
			sInL := a.Have(
				"S lies in L",
				"S ⊆ L.carrier",
				By(subring, comm_ring.SubringSubset.At(fieldRing, S)))
			oInL := a.Have(
				"O lies in L",
				"O ⊆ L.carrier",
				By(subringO, comm_ring.SubringSubset.At(fieldRing, O)))
			mInL := a.Have(
				"M lies in L",
				"M ⊆ L.carrier",
				By(submodule.SubmoduleSubset.Read(fractional)))
			chart := a.Conjuncts(
				a.Have(
					"one lies in S off p, and the denominators are closed under products",
					"L.one ∈ S ∧ L.one ∉ p ∧ (∀x y:A. x ∈ S ∧ y ∈ S ∧ x ∉ p ∧ y ∉ p ⇒ x * y ∉ p)",
					By(
						subring,
						prime,
						comm_ring.SubringDef.At(fieldRing, S),
						ring_ideal.PrimeIdealDef.At(chartRing, p))),
				"one lies in S",
				"one lies off p",
				"the denominators are closed under products")
			oneIn, oneOff, products := chart[0], chart[1], chart[2]
			oneTerm := a.TermAs[A]("L.one")
			J, clearedDef := a.LetAs[Set[A]]("J", "{y:A | y ∈ L.carrier ∧ (∃b:A. b ∈ S ∧ b ∉ p ∧ b * y ∈ M)}")
			clearedMembership := a.Have(
				"J is the members of L a denominator off p brings into M",
				"∀y:A. y ∈ J ⇔ y ∈ L.carrier ∧ (∃b:A. b ∈ S ∧ b ∉ p ∧ b * y ∈ M)",
				clearedDef.Rw(),
				BySets())
			clears := a.Have(
				"a member of L a denominator off p brings into M lies in J",
				"∀y b:A. y ∈ L.carrier ∧ b ∈ S ∧ b ∉ p ∧ b * y ∈ M ⇒ y ∈ J",
				Derive(func(b *Argument) {
					y, d := b.FixAs[A]("y"), b.FixAs[A]("b")
					parts := b.Conjuncts(
						b.Assume(),
						"y lies in L",
						"b lies in S",
						"b lies off p",
						"b · y lies in M")
					isCleared := b.Have(
						"b is the denominator",
						"∃c:A. c ∈ S ∧ c ∉ p ∧ c * y ∈ M",
						Derive(func(c *Argument) {
							c.Take(d)
							c.Show(
								"b brings y into M",
								By(parts[1], parts[2], parts[3]))
						}))
					b.Show(
						"so y lies in J",
						By(parts[0], isCleared, clearedMembership.At(y)))
				}))
			jInL := a.Have(
				"J lies in L",
				"J ⊆ L.carrier",
				Unfold(set_basic.SubsetDef),
				a.ForEach(func(y *Expr[A]) Action { return By(clearedMembership.At(y)) }))
			moduleO := a.Have(
				"L is a module over O",
				"module_on(restrict_ring(field_ring(L), O), «wfField»)",
				By(subringO, fractional_ideal.FieldModuleOn.Read(L).At(O)))
			zeroUnit := a.Have(
				"1 · 0 = 0",
				"L.one * L.zero = L.zero",
				ByArith(L))
			zeroInJ := a.Have(
				"zero lies in J, over the denominator one",
				"L.zero ∈ J",
				By(
					Normalized,
					oneIn,
					oneOff,
					zeroUnit,
					fractional,
					submodule.SubmoduleZero.At(chartRing, vectors, M),
					comm_ring.ZeroIn.Read(ringL),
					clears.At(a.TermAs[A]("L.zero"), oneTerm)))
			sums := a.Have(
				"J is closed under sums, over the product of the two denominators",
				"∀u v:A. u ∈ J ∧ v ∈ J ⇒ u + v ∈ J",
				Derive(func(b *Argument) {
					u, v := b.FixAs[A]("u"), b.FixAs[A]("v")
					members := b.Conjuncts(
						b.Assume(),
						"u lies in J",
						"so does v")
					c, uCleared := b.ObtainAs[A](
						"a denominator c brings u into M",
						"∃c:A. c ∈ S ∧ c ∉ p ∧ c * u ∈ M",
						By(clearedMembership.At(u), members[0]))
					d, vCleared := b.ObtainAs[A](
						"a denominator d brings v into M",
						"∃d:A. d ∈ S ∧ d ∉ p ∧ d * v ∈ M",
						By(clearedMembership.At(v), members[1]))
					first := b.Conjuncts(
						uCleared,
						"c lies in S",
						"c lies off p",
						"c · u lies in M")
					second := b.Conjuncts(
						vCleared,
						"d lies in S",
						"d lies off p",
						"d · v lies in M")
					memberships := b.Have(
						"the four lie in L",
						"u ∈ L.carrier ∧ v ∈ L.carrier ∧ c ∈ L.carrier ∧ d ∈ L.carrier",
						BySets(jInL, sInL, members[0], members[1], first[0], second[0]))
					regroup := b.Have(
						"c · d · (u + v) = d · (c · u) + c · (d · v)",
						"(c * d) * (u + v) = d * (c * u) + c * (d * v)",
						ByArith(L, memberships))
					cu, dv := b.TermAs[A]("c * u"), b.TermAs[A]("d * v")
					inM := b.Have(
						"which lies in M",
						"(c * d) * (u + v) ∈ M",
						By(
							regroup,
							first[0],
							first[2],
							second[0],
							second[2],
							fractional,
							submodule.SubmoduleSmul.At(chartRing, vectors, M, d, cu),
							submodule.SubmoduleSmul.At(chartRing, vectors, M, c, dv),
							submodule.SubmoduleAdd.At(
								chartRing, vectors, M, b.TermAs[A]("d * (c * u)"), b.TermAs[A]("c * (d * v)"))))
					b.Show(
						"so the sum is brought into M by c · d",
						By(
							memberships,
							first[0],
							first[1],
							second[0],
							second[1],
							inM,
							products.At(c, d),
							comm_ring.SubringMul.At(fieldRing, S, c, d),
							subring,
							comm_ring.AddIn.Read(ringL),
							clears.At(b.TermAs[A]("u + v"), b.TermAs[A]("c * d"))))
				}))
			multiples := a.Have(
				"J is closed under multiples from O, over the product of the two denominators",
				"∀r u:A. r ∈ O ∧ u ∈ J ⇒ r * u ∈ J",
				Derive(func(b *Argument) {
					b.FixAs[A]("r")
					u := b.FixAs[A]("u")
					members := b.Conjuncts(
						b.Assume(),
						"r lies in O",
						"u lies in J")
					s, q, rFraction := b.Obtain2As[A, A](
						"r is a fraction s / q",
						"∃s q:A. s ∈ S ∧ q ∈ S ∧ q ∉ p ∧ r * q = s",
						BySets(members[0], oDef, SubringLocalizationDef.At(fieldRing, S, p)))
					c, uCleared := b.ObtainAs[A](
						"a denominator c brings u into M",
						"∃c:A. c ∈ S ∧ c ∉ p ∧ c * u ∈ M",
						By(clearedMembership.At(u), members[1]))
					first := b.Conjuncts(
						rFraction,
						"s lies in S",
						"q lies in S",
						"q lies off p",
						"r · q = s")
					second := b.Conjuncts(
						uCleared,
						"c lies in S",
						"c lies off p",
						"c · u lies in M")
					memberships := b.Have(
						"the five lie in L",
						"r ∈ L.carrier ∧ u ∈ L.carrier ∧ s ∈ L.carrier ∧ q ∈ L.carrier ∧ c ∈ L.carrier",
						BySets(sInL, oInL, jInL, members[0], members[1], first[0], first[1], second[0]))
					regroup := b.Have(
						"q · c · (r · u) = s · (c · u)",
						"(q * c) * (r * u) = s * (c * u)",
						ByArith(L, memberships, Scaled(b.TermAs[A]("c * u"), first[3])))
					inM := b.Have(
						"which lies in M",
						"(q * c) * (r * u) ∈ M",
						By(
							regroup,
							first[0],
							second[2],
							fractional,
							submodule.SubmoduleSmul.At(chartRing, vectors, M, s, b.TermAs[A]("c * u"))))
					b.Show(
						"so the multiple is brought into M by q · c",
						By(
							memberships,
							first[1],
							first[2],
							second[0],
							second[1],
							inM,
							products.At(q, c),
							comm_ring.SubringMul.At(fieldRing, S, q, c),
							subring,
							comm_ring.MulIn.Read(ringL),
							clears.At(b.TermAs[A]("r * u"), b.TermAs[A]("q * c"))))
				}))
			jSubmodule := a.Have(
				"J is an O-submodule of L",
				"submodule(restrict_ring(field_ring(L), O), «wfField», J)",
				By(moduleO, jInL, zeroInJ, sums, multiples, submodule.SubmoduleCriterion.At(localRing, vectors, J)))
			mInJ := a.Have(
				"M lies in J, over the denominator one",
				"M ⊆ J",
				Unfold(set_basic.SubsetDef),
				Derive(func(b *Argument) {
					y := b.FixAs[A]("y")
					yIn := b.Assume()
					yInL := b.Have(
						"y lies in L",
						"y ∈ L.carrier",
						BySets(mInL, yIn))
					unit := b.Have(
						"1 · y = y",
						"L.one * y = y",
						ByArith(L, b.MemberOf[on.L](y, yInL)))
					b.Show(
						"so y lies in J",
						By(Normalized, yInL, oneIn, oneOff, unit, yIn, clears.At(y, oneTerm)))
				}))
			spanInJ := a.Have(
				"so the extension of M, the least O-submodule holding it, lies in J",
				"«extended»(M) ⊆ J",
				By(Normalized, oDef, jSubmodule, mInJ, submodule.SpanLeast.At(localRing, vectors, M, J)))
			spanSubmodule := a.Have(
				"the extension of M is an O-submodule of L",
				"submodule(restrict_ring(field_ring(L), O), «wfField», «extended»(M))",
				By(Normalized, oDef, moduleO, mInL, submodule.SpanSubmodule.At(localRing, vectors, M)))
			mInSpan := a.Have(
				"holding M",
				"M ⊆ «extended»(M)",
				By(Normalized, oDef, submodule.SubsetSpan.At(localRing, vectors, M)))
			extension := a.TermAs[Set[A]]("«extended»(M)")
			jInSpan := a.Have(
				"each member y of J, b · y lying in M, is inv(b) · (b · y), a multiple from O of a member of M",
				"J ⊆ «extended»(M)",
				Unfold(set_basic.SubsetDef),
				Derive(func(b *Argument) {
					y := b.FixAs[A]("y")
					yIn := b.Assume()
					yInL := b.Have(
						"y lies in L",
						"y ∈ L.carrier",
						By(clearedMembership.At(y), yIn))
					d, cleared := b.ObtainAs[A](
						"a denominator b brings y into M",
						"∃b:A. b ∈ S ∧ b ∉ p ∧ b * y ∈ M",
						By(clearedMembership.At(y), yIn))
					parts := b.Conjuncts(
						cleared,
						"b lies in S",
						"b lies off p",
						"b · y lies in M")
					unit := b.Conjuncts(
						GroupPremises(parts[0], parts[1], units.At(d)),
						"inv(b) lies in O",
						"b · inv(b) = 1")
					members := b.Have(
						"y, b and inv(b) lie in L",
						"y ∈ L.carrier ∧ b ∈ L.carrier ∧ L.inv(b) ∈ L.carrier",
						BySets(yInL, sInL, oInL, parts[0], unit[0]))
					cancel := b.Have(
						"y is inv(b) · (b · y)",
						"L.inv(b) * (b * y) = y",
						ByArith(L, members, Scaled(y, unit[1])))
					b.Show(
						"a multiple from O of a member of M lies in its extension",
						By(
							cancel,
							unit[0],
							parts[2],
							spanSubmodule,
							mInSpan,
							submodule.SubmoduleSmul.At(
								localRing, vectors, extension, b.TermAs[A]("L.inv(b)"), b.TermAs[A]("b * y"))))
				}))
			a.Show(
				"so the extension of M is J",
				BySets(oDef, spanInJ, jInSpan))
		}),
})}

// LocalIdealProper — the ideal a prime m of S generates in the localization of
// S at m is proper: it is the extension of m, the members of L that a
// denominator off m brings into m (LocalExtensionCleared), and one is not
// among them, since a denominator d brings it to d itself, which lies off m.
var LocalIdealProper = localIdealProperThm{family.Add(registry.ProofEntry{
	Name: "LocalIdealProper",
	Key:  "prop_c12932e33ad0141a",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S m:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"prime_ideal(restrict_ring(field_ring(L), S), m)",
		},
		Conclusion: "L.one ∉ " +
			"ideal_span(restrict_ring(field_ring(L), subring_localization(field_ring(L), S, m)), m)",
	},
		func(a *Argument, L field.FieldFact[on.L], S, m *Expr[Set[A]], h Fact) {
			given := a.Conjuncts(
				h,
				"S is a subring of L",
				"m is a prime of S")
			subring, prime := given[0], given[1]
			chartRing := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), S)")
			O := a.TermAs[Set[A]]("subring_localization(field_ring(L), S, m)")
			local := a.Conjuncts(
				GroupPremises(subring, prime, LocalRingSubring.Read(L).At(S, m)),
				"the localization O is a subring of L",
				"it holds S",
				"it inverts the denominators")
			ideal := a.Conjuncts(
				a.Have(
					"m is an ideal of S, so a fractional ideal inside S",
					"submodule(restrict_ring(field_ring(L), S), regular_module(field_ring(L)), m) ∧ m ⊆ S",
					By(
						subring,
						prime,
						ring_ideal.PrimeIdealIdeal.At(chartRing, m),
						fractional_ideal.IntegralIdealFractional.Read(L).At(S, m))),
				"m is a fractional ideal of S",
				"inside S")
			extension := a.Have(
				"the ideal m generates in O is its extension, the members of L a denominator off m brings into m",
				"ideal_span(restrict_ring(field_ring(L), subring_localization(field_ring(L), S, m)), m) = "+
					"{y:A | y ∈ L.carrier ∧ (∃b:A. b ∈ S ∧ b ∉ m ∧ b * y ∈ m)}",
				By(
					local[0],
					local[1],
					ideal[1],
					set_order.SubsetTrans.At(m, S, O),
					fractional_ideal.SpanInSubringIsIdealSpan.Read(L).At(O, m),
					subring,
					prime,
					ideal[0],
					LocalExtensionCleared.Read(L).At(S, m, m)))
			inSpan := a.SupposeNot()
			_, cleared := a.ObtainAs[A](
				"so a denominator d off m brings one into m",
				"∃d:A. d ∈ S ∧ d ∉ m ∧ d * L.one ∈ m",
				BySets(inSpan, extension))
			parts := a.Conjuncts(
				cleared,
				"d lies in S",
				"d lies off m",
				"d · 1 lies in m")
			dInL := a.Have(
				"d lies in L",
				"d ∈ L.carrier",
				BySets(parts[0], subring, comm_ring.SubringSubset.At(a.TermAs[RingOps[A]]("field_ring(L)"), S)))
			unit := a.Have(
				"d · 1 = d",
				"d * L.one = d",
				ByArith(L, dInL))
			a.Show(
				"so d lies in m after all",
				By(Normalized, parts[1], parts[2], unit))
		}),
})}

// ExtensionOfProduct — extending along S ⊆ T, the span over T, takes a
// product over S to the product over T of the extensions: over T the
// products x · y span what their span over S spans, and a product over T
// reads each factor through its span (fractional_ideal.FractionalMulSpan,
// fractional_ideal.FractionalMulSpanRight). S need not be a subring.
var ExtensionOfProduct = extensionOfProductThm{family.Add(registry.ProofEntry{
	Name: "ExtensionOfProduct",
	Key:  "prop_1424f5a61c62a02d",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S T X Y:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), T)",
			"S ⊆ T",
			"X ⊆ L.carrier",
			"Y ⊆ L.carrier",
		},
		Conclusion: "«extended»(fractional_mul(field_ring(L), S, X, Y)) = " +
			"fractional_mul(field_ring(L), T, «extended»(X), «extended»(Y))",
		Abbrev: Abbrev{
			{Name: "extended", Text: "module_span(restrict_ring(field_ring(L), T), " +
				"    regular_module(field_ring(L)))"},
		},
	},
		func(a *Argument, L field.FieldFact[on.L], S, T, X, Y *Expr[Set[A]], given Fact) {
			parts := a.Conjuncts(
				given,
				"T is a subring of L",
				"S lies in T",
				"X lies in L",
				"and so does Y")
			subringT, inside, xInL, yInL := parts[0], parts[1], parts[2], parts[3]
			fieldModule := a.Have(
				"L is a module over T",
				"module_on(restrict_ring(field_ring(L), T), regular_module(field_ring(L)))",
				By(subringT, fractional_ideal.FieldModuleOn.Read(L).At(T)))
			spanY := a.TermAs[Set[A]]("«extended»(Y)")
			spanYSubmodule := a.Have(
				"the T-span of Y is a submodule of L",
				"submodule(restrict_ring(field_ring(L), T), regular_module(field_ring(L)), «extended»(Y))",
				By(yInL, submodule.SpanSubmodule.Read(fieldModule).At(Y)))
			products := a.TermAs[Set[A]]("{m * n | m:A, n:A | m ∈ X ∧ n ∈ Y}")
			productsInL := a.Have(
				"the products generating the product lie in L",
				"{m * n | m:A, n:A | m ∈ X ∧ n ∈ Y} ⊆ L.carrier",
				BySets(xInL, yInL, comm_ring.MulIn.Read(field.RingOn.Read(L))))
			scalarsS := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), S)")
			absorbed := a.Have(
				"the T-span absorbs the S-span of those products",
				"«extended»(fractional_mul(field_ring(L), S, X, Y)) = fractional_mul(field_ring(L), T, X, Y)",
				Unfold(fractional_ideal.FractionalMulDef),
				By(inside, productsInL, submodule.SpanOfSubringSpan.Read(fieldModule).At(scalarsS, products)))
			spansProduct := a.Have(
				"the product over T of the T-spans is the product of their generators",
				"fractional_mul(field_ring(L), T, «extended»(X), «extended»(Y)) = "+
					"fractional_mul(field_ring(L), T, X, Y)",
				CalcEq(
					Leg(
						a.TermAs[Set[A]]("fractional_mul(field_ring(L), T, X, «extended»(Y))"),
						"the product reads its first factor through its span",
						By(
							subringT,
							xInL,
							submodule.SubmoduleSubset.Read(spanYSubmodule),
							fractional_ideal.FractionalMulSpan.Read(L).At(T, X, spanY))),
					FinalLeg(
						"and its second factor too",
						By(subringT, xInL, yInL, fractional_ideal.FractionalMulSpanRight.Read(L).At(T, X, Y)))))
			a.Show(
				"both sides are the product over T of X and Y",
				By(absorbed, spansProduct))
		}),
})}

// ExtensionOfInvertible — extending along subrings S ⊆ T keeps an invertible
// fractional ideal X of S invertible, with the extension of its inverse as
// the inverse. Over S the products of X and (S : X) span S, so over T they
// span T, S holding one; a product over T reads each factor through its span,
// so the two extensions multiply to T, and a fractional ideal multiplying
// with the extension of X to T is its inverse (fractional_ideal.FractionalInverseUnique).
var ExtensionOfInvertible = extensionOfInvertibleThm{family.Add(registry.ProofEntry{
	Name: "ExtensionOfInvertible",
	Key:  "prop_a3db91ef3f2f6146",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S T X:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"subring(field_ring(L), T)",
			"S ⊆ T",
			"invertible_fractional(field_ring(L), S, X)",
		},
		Conclusion: "invertible_fractional(field_ring(L), T, «extended»(X)) ∧ " +
			"fractional_inverse(field_ring(L), T, «extended»(X)) = " +
			"«extended»(fractional_inverse(field_ring(L), S, X))",
		Abbrev: Abbrev{
			{Name: "extended", Text: "module_span(restrict_ring(field_ring(L), T), " +
				"    regular_module(field_ring(L)))"},
			{Name: "products", Text: "{m * n | " +
				"    m:A, " +
				"    n:A | " +
				"    m ∈ X ∧ n ∈ fractional_inverse(field_ring(L), S, X)}"},
		},
	},
		func(a *Argument, L field.FieldFact[on.L], S, T, X *Expr[Set[A]], given Fact) {
			parts := a.Conjuncts(
				given,
				"S is a subring of L",
				"T is a subring of L",
				"S lies in T",
				"X is invertible over S")
			subringS, subringT, inside, invertible := parts[0], parts[1], parts[2], parts[3]
			first := a.Conjuncts(
				a.Unfolded(invertible, fractional_ideal.InvertibleFractionalDef),
				"so X is an S-submodule of L",
				"whose product with (S : X) is S")
			xSubmodule, xProduct := first[0], first[1]
			inverse := a.TermAs[Set[A]]("fractional_inverse(field_ring(L), S, X)")
			xInL := a.Have(
				"X lies in L, a submodule of it",
				"X ⊆ L.carrier",
				By(submodule.SubmoduleSubset.Read(xSubmodule)))
			inverseInL := fractional_ideal.FractionalInverseSubset.Read(L).At(S, X)
			fieldModule := a.Have(
				"L is a module over T",
				"module_on(restrict_ring(field_ring(L), T), regular_module(field_ring(L)))",
				By(subringT, fractional_ideal.FieldModuleOn.Read(L).At(T)))
			extension, inverseExtension :=
				a.TermAs[Set[A]]("«extended»(X)"),
				a.TermAs[Set[A]]("«extended»(fractional_inverse(field_ring(L), S, X))")
			inverseSubmodule := a.Have(
				"the T-span of (S : X) is a T-submodule of L",
				"submodule(restrict_ring(field_ring(L), T), "+
					"    regular_module(field_ring(L)), "+
					"    «extended»(fractional_inverse(field_ring(L), S, X)))",
				By(inverseInL, submodule.SpanSubmodule.Read(fieldModule).At(inverse)))
			products := a.TermAs[Set[A]]("«products»")
			productsInL := a.Have(
				"a member of X times a member of (S : X) lies in L, which is closed under the product",
				"«products» ⊆ L.carrier",
				BySets(xInL, inverseInL, comm_ring.MulIn.Read(field.RingOn.Read(L))))
			scalarsS := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), S)")
			spanned := a.Unfolded(xProduct, fractional_ideal.FractionalMulDef)
			overT := a.Have(
				"over T, X · (S : X) is T",
				"fractional_mul(field_ring(L), T, X, fractional_inverse(field_ring(L), S, X)) = T",
				Unfold(fractional_ideal.FractionalMulDef),
				CalcEq(
					Leg(
						a.TermAs[Set[A]](
							"«extended»( "+
								"    module_span(restrict_ring(field_ring(L), S), regular_module(field_ring(L)), «products»))"),
						"over T the products span what their S-span spans",
						By(inside, productsInL, submodule.SpanOfSubringSpan.Read(fieldModule).At(scalarsS, products))),
					Leg(
						a.TermAs[Set[A]]("«extended»(S)"),
						"X being invertible over S, their S-span is S",
						By(spanned)),
					FinalLeg(
						"and S, inside T and holding one, spans T",
						By(
							subringT,
							inside,
							comm_ring.SubringOne.Read(subringS),
							fractional_ideal.SpanHoldingOne.Read(L).At(T, S)))))
			extensionsProduct := a.Have(
				"so the two extensions multiply to T, each factor read through its span",
				"fractional_mul(field_ring(L), "+
					"    T, "+
					"    «extended»(X), "+
					"    «extended»(fractional_inverse(field_ring(L), S, X))) = "+
					"T",
				CalcEq(
					Leg(
						a.TermAs[Set[A]](
							"fractional_mul(field_ring(L), T, X, «extended»(fractional_inverse(field_ring(L), S, X)))"),
						"the product reads its first factor through its span",
						By(
							subringT,
							xInL,
							submodule.SubmoduleSubset.Read(inverseSubmodule),
							fractional_ideal.FractionalMulSpan.Read(L).At(T, X, inverseExtension))),
					Leg(
						a.TermAs[Set[A]]("fractional_mul(field_ring(L), T, X, fractional_inverse(field_ring(L), S, X))"),
						"and its second factor too",
						By(subringT, xInL, inverseInL, fractional_ideal.FractionalMulSpanRight.Read(L).At(T, X, inverse))),
					FinalLeg(
						"which is T",
						By(overT))))
			a.Show(
				"a fractional ideal whose product with the extension of "+
					"X is T is its inverse, and the extension is invertible",
				By(
					subringT,
					xInL,
					submodule.SpanSubmodule.Read(fieldModule).At(X),
					inverseSubmodule,
					extensionsProduct,
					fractional_ideal.FractionalInverseUnique.Read(L).At(T, extension, inverseExtension)))
		}),
})}

// ExtensionOfSignedPowers — extending fractional ideals along subrings
// S ⊆ T takes each signed power of an invertible ideal I of S to the same
// power of the extension of I: the natural powers extend by induction,
// products extending to products, and a negative power is a power of the
// inverse, which extends to the inverse of the extension.
var ExtensionOfSignedPowers = extensionOfSignedPowersThm{family.Add(registry.ProofEntry{
	Name: "ExtensionOfSignedPowers",
	Key:  "prop_4f9f594c1ce904e0",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S T I:set(A). ∀j:int.",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"subring(field_ring(L), T)",
			"S ⊆ T",
			"invertible_fractional(field_ring(L), S, I)",
		},
		Conclusion: "«extended»(signed_ideal_power(field_ring(L), S, I, j)) = " +
			"signed_ideal_power(field_ring(L), T, «extended»(I), j)",
		Abbrev: Abbrev{
			{Name: "extended", Text: "module_span(restrict_ring(field_ring(L), T), " +
				"    regular_module(field_ring(L)))"},
		},
	},
		func(a *Argument, L field.FieldFact[on.L], S, T, I *Expr[Set[A]], j *Expr[Int], h Fact) {
			given := a.Conjuncts(
				h,
				"S is a subring of L",
				"so is T",
				"S lies in T",
				"I is invertible over S")
			subringS, subringT, inside, invertible := given[0], given[1], given[2], given[3]
			ringOps := a.TermAs[RingOps[A]]("field_ring(L)")
			whole := a.Have(
				"S extends to T, for it lies in T and holds one",
				"«extended»(S) = T",
				By(
					subringT,
					inside,
					comm_ring.SubringOne.Read(subringS),
					fractional_ideal.SpanHoldingOne.Read(L).At(T, S)))
			powers := a.Have(
				"the natural powers of a subset of L extend to the powers of its extension, and stay in L",
				Statement{
					Binders: "∀X:set(A). ∀n:num.",
					Hypotheses: []string{
						"X ⊆ L.carrier",
					},
					Conclusion: "«extended»( " +
						"    monoid_pow(λU:set(A). λV:set(A). fractional_mul(field_ring(L), S, U, V), S, X, n)) = " +
						"monoid_pow(λU:set(A). λV:set(A). fractional_mul(field_ring(L), T, U, V), T, «extended»(X), n) ∧ " +
						"monoid_pow(λU:set(A). λV:set(A). fractional_mul(field_ring(L), S, U, V), S, X, n) ⊆ L.carrier",
				},
				Derive(func(b *Argument) {
					X := b.FixAs[Set[A]]("X")
					b.Induct("n")
					b.Base(
						"the zeroth powers are S and T",
						By(Normalized, whole, subringS, comm_monoid.MonoidPowDef, comm_ring.SubringSubset.At(ringOps, S)))
					b.Step(
						"one more factor X on each side",
						func(c *Argument, ih Fact) {
							inL := c.Assume()
							previous := c.Conjuncts(
								c.Have(
									"the induction hypothesis holds at X",
									"«extended»(monoid_pow(λU:set(A). λV:set(A). fractional_mul(field_ring(L), S, U, V), S, X, n)) = "+
										"monoid_pow(λU:set(A). λV:set(A). fractional_mul(field_ring(L), T, U, V), T, «extended»(X), n) ∧ "+
										"monoid_pow(λU:set(A). λV:set(A). fractional_mul(field_ring(L), S, U, V), S, X, n) ⊆ L.carrier",
									By(inL, ih)),
								"the n-th power extends to the n-th power of the extension",
								"and lies in L")
							last := c.TermAs[Set[A]](
								"monoid_pow(λU:set(A). λV:set(A). fractional_mul(field_ring(L), S, U, V), S, X, n)")
							extended := c.Have(
								"the extension of X times the n-th power is the extension of X times its n-th power",
								"«extended»( "+
									"    monoid_pow(λU:set(A). λV:set(A). fractional_mul(field_ring(L), S, U, V), S, X, suc(n))) = "+
									"monoid_pow(λU:set(A). λV:set(A). fractional_mul(field_ring(L), T, U, V), "+
									"    T, "+
									"    «extended»(X), "+
									"    suc(n))",
								Simp(Fwd(comm_monoid.MonoidPowDef)),
								By(inL, previous[0], previous[1], subringT, inside, ExtensionOfProduct.Read(L).At(S, T, X, last)))
							productInL := c.Have(
								"the product lies in L",
								"monoid_pow(λU:set(A). λV:set(A). fractional_mul(field_ring(L), S, U, V), S, X, suc(n)) ⊆ "+
									"L.carrier",
								By(
									subringS,
									inL,
									previous[1],
									comm_monoid.MonoidPowDef,
									fractional_ideal.FractionalMulSubmodule.Read(L).At(S, X, last),
									submodule.SubmoduleSubset.At(
										c.TermAs[RingOps[A]]("restrict_ring(field_ring(L), S)"),
										c.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))"),
										c.TermAs[Set[A]](
											"fractional_mul(field_ring(L), "+
												"    S, "+
												"    X, "+
												"    monoid_pow(λU:set(A). λV:set(A). fractional_mul(field_ring(L), S, U, V), S, X, n))"))))
							c.Show(
								"both parts at the next power",
								By(extended, productInL))
						})
				}))
			ideal := a.Conjuncts(
				a.Unfolded(invertible, fractional_ideal.InvertibleFractionalDef),
				"I is a fractional ideal",
				"it multiplies with its inverse to S")
			subsets := a.Have(
				"I and its inverse lie in L, and the inverse extends to the inverse of the extension",
				"I ⊆ L.carrier ∧ "+
					"fractional_inverse(field_ring(L), S, I) ⊆ L.carrier ∧ "+
					"«extended»(fractional_inverse(field_ring(L), S, I)) = "+
					"fractional_inverse(field_ring(L), T, «extended»(I))",
				By(
					subringS,
					subringT,
					inside,
					invertible,
					ExtensionOfInvertible.Read(L).At(S, T, I),
					submodule.SubmoduleSubset.At(
						a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), S)"),
						a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))"),
						I),
					ideal[0],
					fractional_ideal.FractionalInverseSubset.Read(L).At(S, I)))
			parts := a.Conjuncts(
				subsets,
				"I lies in L",
				"its inverse lies in L",
				"the inverse extends to the inverse of the extension")
			a.Do(Simp(Fwd(signed_ideal_power.SignedIdealPowerDef)))
			a.Cases(a.TermAs[Bool]("0 ≤ j"))
			a.When(
				"a natural power extends to the natural power",
				func(b *Argument, natural Fact) {
					b.Show(
						"the powers of I at num_of_int(j)",
						By(natural, parts[0], powers.At(I, b.TermAs[Nat]("num_of_int(j)"))))
				})
			a.Otherwise(
				"a negative power extends as a power of the inverse",
				func(b *Argument, negative Fact) {
					b.Show(
						"the powers of the inverse at num_of_int(−j)",
						By(
							negative,
							parts[1],
							parts[2],
							powers.At(
								b.TermAs[Set[A]]("fractional_inverse(field_ring(L), S, I)"), b.TermAs[Nat]("num_of_int(-j)"))))
				})
		}),
})}

// LocalExtensionLaws — extending fractional ideals from S to its localization at
// a prime m: S extends to the local ring, the extension is multiplicative on
// invertible ideals and keeps inverses, m extends to a proper ideal, and an ideal
// holding a function off m extends to the local ring, the function being a unit.
var LocalExtensionLaws = localExtensionLawsThm{family.Add(registry.ProofEntry{
	Name: "LocalExtensionLaws",
	Key:  "prop_367cbe81afe0613b",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S m:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"prime_ideal(restrict_ring(field_ring(L), S), m)",
		},
		Conclusion: "subring(field_ring(L), subring_localization(field_ring(L), S, m)) ∧ " +
			"«extended»(S) = subring_localization(field_ring(L), S, m) ∧ " +
			"(∀X Y:set(A). " +
			"    invertible_fractional(field_ring(L), S, X) ∧ invertible_fractional(field_ring(L), S, Y) ⇒ " +
			"    «extended»(fractional_mul(field_ring(L), S, X, Y)) = " +
			"    fractional_mul(field_ring(L), " +
			"        subring_localization(field_ring(L), S, m), " +
			"        «extended»(X), " +
			"        «extended»(Y))) ∧ " +
			"(∀X:set(A). " +
			"    invertible_fractional(field_ring(L), S, X) ⇒ " +
			"    invertible_fractional(field_ring(L), " +
			"        subring_localization(field_ring(L), S, m), " +
			"        «extended»(X)) ∧ " +
			"    fractional_inverse(field_ring(L), " +
			"        subring_localization(field_ring(L), S, m), " +
			"        «extended»(X)) = " +
			"    «extended»(fractional_inverse(field_ring(L), S, X))) ∧ " +
			"«extended»(m) = «maximal» ∧ " +
			"«maximal» ⊆ subring_localization(field_ring(L), S, m) ∧ " +
			"L.one ∉ «maximal» ∧ " +
			"(∀X:set(A). ∀u:A. " +
			"    X ⊆ S ∧ u ∈ X ∧ u ∉ m ⇒ «extended»(X) = subring_localization(field_ring(L), S, m))",
		Abbrev: Abbrev{
			{Name: "extended", Text: "module_span( " +
				"    restrict_ring(field_ring(L), subring_localization(field_ring(L), S, m)), " +
				"    regular_module(field_ring(L)))"},
			{Name: "maximal", Text: "ideal_span( " +
				"    restrict_ring(field_ring(L), subring_localization(field_ring(L), S, m)), m)"},
		},
	},
		func(a *Argument, L field.FieldFact[on.L], S, m *Expr[Set[A]], h Fact) {
			given := a.Conjuncts(
				h,
				"S is a subring of L",
				"m is a prime of S")
			subring, prime := given[0], given[1]
			ops := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), S)")
			O := a.TermAs[Set[A]]("subring_localization(field_ring(L), S, m)")
			local := a.Conjuncts(
				GroupPremises(given[0], given[1], LocalRingSubring.Read(L).At(S, m)),
				"the local ring is a subring",
				"it holds S",
				"it inverts the denominators")
			subringO, inside, units := local[0], local[1], local[2]
			inS := a.Have(
				"m lies in S",
				"m ⊆ S",
				By(prime, ring_ideal.PrimeIdealIdeal.At(ops, m), ring_ideal.RingIdealDef.At(ops, m)))
			inO := a.Have(
				"so m lies in the local ring",
				"m ⊆ subring_localization(field_ring(L), S, m)",
				By(inS, inside, set_order.SubsetTrans.At(m, S, O)))
			whole := a.Have(
				"S extends to the local ring, for it lies there and holds one",
				"«extended»(S) = subring_localization(field_ring(L), S, m)",
				By(
					subringO,
					inside,
					comm_ring.SubringOne.Read(subring),
					fractional_ideal.SpanHoldingOne.Read(L).At(O, S)))
			inL := a.Have(
				"an invertible ideal lies in L",
				"∀X:set(A). invertible_fractional(field_ring(L), S, X) ⇒ X ⊆ L.carrier",
				Derive(func(b *Argument) {
					b.FixAs[Set[A]]("X")
					clauses := b.Conjuncts(
						b.Unfolded(b.Assume(), fractional_ideal.InvertibleFractionalDef),
						"X is a fractional ideal",
						"it multiplies with its inverse to S")
					b.Show(
						"a submodule of L lies in L",
						By(submodule.SubmoduleSubset.Read(clauses[0])))
				}))
			multiplicative := a.Have(
				"the extension is multiplicative on invertible ideals",
				Statement{
					Binders: "∀X Y:set(A).",
					Hypotheses: []string{
						"invertible_fractional(field_ring(L), S, X)",
						"invertible_fractional(field_ring(L), S, Y)",
					},
					Conclusion: "«extended»(fractional_mul(field_ring(L), S, X, Y)) = " +
						"fractional_mul(field_ring(L), " +
						"    subring_localization(field_ring(L), S, m), " +
						"    «extended»(X), " +
						"    «extended»(Y))",
				},
				Derive(func(b *Argument) {
					X, Y := b.FixAs[Set[A]]("X"), b.FixAs[Set[A]]("Y")
					parts := b.Conjuncts(
						b.Assume(),
						"X is invertible",
						"Y is invertible")
					b.Show(
						"both lie in L, and extension along S ⊆ O is multiplicative",
						By(
							parts[0],
							parts[1],
							inL.At(X),
							inL.At(Y),
							subringO,
							inside,
							ExtensionOfProduct.Read(L).At(S, O, X, Y)))
				}))
			invertibles := a.Have(
				"the extension of an invertible ideal is invertible, with the extension of the inverse",
				Statement{
					Binders:    "∀X:set(A).",
					Hypotheses: []string{"invertible_fractional(field_ring(L), S, X)"},
					Conclusion: "invertible_fractional(field_ring(L), " +
						"    subring_localization(field_ring(L), S, m), " +
						"    «extended»(X)) ∧ " +
						"fractional_inverse(field_ring(L), subring_localization(field_ring(L), S, m), «extended»(X)) = " +
						"«extended»(fractional_inverse(field_ring(L), S, X))",
				},
				Derive(func(b *Argument) {
					X := b.FixAs[Set[A]]("X")
					invertible := b.Assume()
					b.Show(
						"extension along S ⊆ O keeps invertible ideals and their inverses",
						By(invertible, subring, subringO, inside, ExtensionOfInvertible.Read(L).At(S, O, X)))
				}))
			extendedM := a.Have(
				"m extends to the ideal it generates",
				"«extended»(m) = «maximal»",
				By(subringO, inO, fractional_ideal.SpanInSubringIsIdealSpan.Read(L).At(O, m)))
			insideLocal := a.Have(
				"which lies in the local ring",
				"«maximal» ⊆ subring_localization(field_ring(L), S, m)",
				extendedM.RwRev(),
				By(a.Simplified(
					GroupPremises(inS, submodule.SpanMono.At(
						a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), subring_localization(field_ring(L), S, m))"),
						a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))"),
						m,
						S)),
					Fwd(whole))))
			proper := a.Have(
				"and misses one",
				"L.one ∉ «maximal»",
				By(subring, prime, LocalIdealProper.Read(L).At(S, m)))
			unitIdeals := a.Have(
				"an ideal holding a function off m extends to the local ring",
				Statement{
					Binders:    "∀X:set(A). ∀u:A.",
					Hypotheses: []string{"X ⊆ S", "u ∈ X", "u ∉ m"},
					Conclusion: "«extended»(X) = subring_localization(field_ring(L), S, m)",
				},
				Derive(func(b *Argument) {
					X, u := b.FixAs[Set[A]]("X"), b.FixAs[A]("u")
					parts := b.Conjuncts(
						b.Assume(),
						"X lies in S",
						"X holds u",
						"u lies off m")
					uIn := b.Have(
						"u is a denominator",
						"u ∈ S",
						BySets(parts[0], parts[1]))
					xIn := b.Have(
						"X lies in the local ring",
						"X ⊆ subring_localization(field_ring(L), S, m)",
						By(parts[0], inside, set_order.SubsetTrans.At(X, S, O)))
					b.Show(
						"u is a unit of the local ring",
						By(
							subringO,
							xIn,
							parts[1],
							uIn,
							parts[2],
							units.At(u),
							fractional_ideal.SpanHoldingUnit.Read(L).At(O, X, u, b.TermAs[A]("L.inv(u)"))))
				}))
			a.Show(
				"O is a subring extending S; extension keeps products and "+
					"inverses, gives the maximal ideal, and takes a unit ideal to O",
				By(subringO, whole, multiplicative, invertibles, extendedM, insideLocal, proper, unitIdeals))
		}),
})}

// LocalHoldsSignedPowers — the localization of S at a prime m holds every
// signed power of an invertible ideal C of S that does not lie inside m. C
// holds a member off m, so it extends to the whole localization
// (LocalExtensionLaws); each signed power of C extends to the same power of
// that extension (ExtensionOfSignedPowers), which is the localization itself,
// the unit of its fractional ideals (signed_ideal_power.SignedPowerOfRing); and
// a set lies in the span it extends to.
var LocalHoldsSignedPowers = localHoldsSignedPowersThm{family.Add(registry.ProofEntry{
	Name: "LocalHoldsSignedPowers",
	Key:  "prop_e4f89700281ccc53",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S m C:set(A). ∀j:int.",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"prime_ideal(restrict_ring(field_ring(L), S), m)",
			"invertible_fractional(field_ring(L), S, C)",
			"C ⊆ S",
			"¬(C ⊆ m)",
		},
		Conclusion: "signed_ideal_power(field_ring(L), S, C, j) ⊆ " +
			"subring_localization(field_ring(L), S, m)",
	},
		func(a *Argument, L field.FieldFact[on.L], S, m, C *Expr[Set[A]], j *Expr[Int], h Fact) {
			given := a.Conjuncts(
				h,
				"S is a subring of L",
				"m is a prime ideal of S",
				"C is invertible",
				"C lies in S",
				"C is not inside m")
			subring, prime, invertible, inS, outside := given[0], given[1], given[2], given[3], given[4]
			localization := a.TermAs[Set[A]]("subring_localization(field_ring(L), S, m)")
			_, off := a.ObtainAs[A](
				"C holds some u off m",
				"∃u:A. u ∈ C ∧ u ∉ m",
				By(Normalized, outside, set_basic.SubsetDef.At(C, m)))
			member := a.Conjuncts(
				off,
				"u lies in C",
				"u lies off m")
			local := a.Conjuncts(
				a.Have(
					"the localization is a subring holding S, and C extends to all of it",
					"subring(field_ring(L), subring_localization(field_ring(L), S, m)) ∧ "+
						"S ⊆ subring_localization(field_ring(L), S, m) ∧ "+
						"module_span(restrict_ring(field_ring(L), subring_localization(field_ring(L), S, m)), "+
						"    regular_module(field_ring(L)), "+
						"    C) = "+
						"subring_localization(field_ring(L), S, m)",
					By(
						member[0],
						member[1],
						subring,
						prime,
						inS,
						LocalExtensionLaws.Read(L).At(S, m),
						LocalRingSubring.Read(L).At(S, m))),
				"the localization is a subring",
				"it holds S",
				"C extends to all of it")
			a.Show(
				"the power of C lies in its extension, the same power of the localization",
				By(
					local[2],
					signed_ideal_power.SignedPowerOfRing.Read(L).At(localization, j),
					subring,
					local[0],
					local[1],
					invertible,
					ExtensionOfSignedPowers.Read(L).At(S, localization, C, j),
					submodule.SubsetSpan.At(
						a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), subring_localization(field_ring(L), S, m))"),
						a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))"),
						a.TermAs[Set[A]]("signed_ideal_power(field_ring(L), S, C, j)"))))
		}),
})}

// OrderAtChartPoint — the order at the ideal p of a k-rational point of a
// chart S, p invertible, L the field of fractions of S and each nonzero
// principal ideal of S of finite colength: in the localization O of S at p,
// with maximal ideal 𝔪 = pO, every nonzero f of L generates exactly one integer
// power of 𝔪, the powers decrease strictly, and any exponent so chosen is a
// valuation.
//
// O is local: a member of O off 𝔪 has numerator off p, so its inverse lies in
// O. A nonzero a in S lies in 𝔪ⁿ only when it lies in pⁿ
// (LocalPowerContraction), so only for n up to the colength of aS
// (ideal_colength.RationalPowerColength); for the largest such n, aO·𝔪⁻ⁿ is
// an ideal of O not inside 𝔪, hence O, and aO = 𝔪ⁿ. A nonzero f is a/b with
// a, b in S, and fO·bO = aO gives fO = 𝔪^(m − j). The powers of the proper
// invertible 𝔪 are distinct and decrease strictly
// (signed_ideal_power.SignedPowerInjective, signed_ideal_power.SignedPowerAntitone),
// and an exponent of the principal ideals is a valuation
// (signed_ideal_power.SignedPowerValuation).
var OrderAtChartPoint = orderAtChartPointThm{family.Add(registry.ProofEntry{
	Name: "OrderAtChartPoint",
	Key:  "prop_2acb3f276f74b492",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k S p:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"subfield(L, k)",
			"k ⊆ S",
			"fraction_field_carrier(field_ring(L), S)",
			"rational_ideal(field_ring(L), k, S, p)",
			"invertible_fractional(field_ring(L), S, p)",
			"∀a:A. a ∈ S ∧ a ≠ L.zero ⇒ «finiteQuotient»(S, image(L.mul(a), S))",
		},
		Conclusion: "(∀f:A. " +
			"    f ∈ L.carrier ∧ f ≠ L.zero ⇒ " +
			"    ∃!n:int. image(L.mul(f), subring_localization(field_ring(L), S, p)) = «power»(n)) ∧ " +
			"(∀i j:int. «power»(i) ⊆ «power»(j) ⇔ j ≤ i) ∧ " +
			"(∀v:(A → int). " +
			"    (∀f:A. " +
			"        f ∈ L.carrier ∧ f ≠ L.zero ⇒ " +
			"        image(L.mul(f), subring_localization(field_ring(L), S, p)) = «power»(v(f))) ⇒ " +
			"    valuation_order(field_ring(L), v))",
		Abbrev: Abbrev{
			{Name: "maximal", Text: "ideal_span( " +
				"    restrict_ring(field_ring(L), subring_localization(field_ring(L), S, p)), p)"},
			{Name: "power", Text: "λn:int. " +
				"    signed_ideal_power(field_ring(L), subring_localization(field_ring(L), S, p), «maximal», n)"},
			{Name: "product", Text: "λX:set(A). λY:set(A). " +
				"    fractional_mul(field_ring(L), subring_localization(field_ring(L), S, p), X, Y)"},
			{Name: "fractional", Text: "submodule( " +
				"    restrict_ring(field_ring(L), subring_localization(field_ring(L), S, p)), " +
				"    regular_module(field_ring(L)))"},
			{Name: "chartPower", Text: "λn:num. " +
				"    monoid_pow(λX:set(A). λY:set(A). fractional_mul(field_ring(L), S, X, Y), S, p, n)"},
			{Name: "localPower", Text: "λn:num. " +
				"    monoid_pow(λX:set(A). λY:set(A). " +
				"            fractional_mul(field_ring(L), subring_localization(field_ring(L), S, p), X, Y), " +
				"        subring_localization(field_ring(L), S, p), " +
				"        «maximal», " +
				"        n)"},
		},
	},
		func(a *Argument, L field.FieldFact[on.L], k, S, p *Expr[Set[A]], h Fact) {
			given := a.Conjuncts(
				h,
				"S is a subring of L",
				"k is a subfield",
				"k lies in S",
				"L is the field of fractions of S",
				"p is the ideal of a k-rational point",
				"p is invertible",
				"each nonzero principal ideal of S has finite colength")
			subring, subfield, kInS, fractions, rational, invertible, finite :=
				given[0], given[1], given[2], given[3], given[4], given[5], given[6]
			fieldRing := a.TermAs[RingOps[A]]("field_ring(L)")
			localRing := a.TermAs[RingOps[A]](
				"restrict_ring(field_ring(L), subring_localization(field_ring(L), S, p))")
			vectors := a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))")
			inv := a.TermAs[Fun[A, A]]("L.inv")
			O := a.TermAs[Set[A]]("subring_localization(field_ring(L), S, p)")
			M := a.TermAs[Set[A]]("«maximal»")
			ringL := field.RingOn.Read(L)
			ringS := a.Have(
				"S is a commutative ring",
				"comm_ring_on(restrict_ring(field_ring(L), S))",
				By(subring, comm_ring.SubringRingOn.Read(ringL).At(S)))
			ringSubfield := a.Have(
				"k is a subfield of the ring of L",
				"ring_subfield(field_ring(L), L.inv, k)",
				By(
					subfield,
					field.SubfieldRingSubfield.Read(L).At(k, S),
					field.RingSubfieldRestrict.At(fieldRing, S, inv, k)))
			maximal := a.Have(
				"p is maximal, its residues lying in the field k",
				"maximal_ideal(restrict_ring(field_ring(L), S), p)",
				By(
					ringL,
					ringSubfield,
					subring,
					kInS,
					rational,
					quotient_ring.FieldResiduesMaximal.At(fieldRing, k, inv, S, p)))
			prime := a.Have(
				"hence prime",
				"prime_ideal(restrict_ring(field_ring(L), S), p)",
				By(maximal, ring_ideal.MaximalIsPrime.Read(ringS).At(p)))
			laws := a.Conjuncts(
				GroupPremises(subring, prime, LocalExtensionLaws.Read(L).At(S, p)),
				"O is a subring",
				"S extends to O",
				"extension is multiplicative on invertible ideals",
				"it keeps invertible ideals invertible",
				"p extends to 𝔪",
				"𝔪 lies in O",
				"𝔪 misses one",
				"an ideal holding a unit extends to O")
			subringO, invertibles, extendedP, mInO, proper := laws[0], laws[3], laws[4], laws[5], laws[6]
			sInO := a.Have(
				"O holds S",
				"S ⊆ subring_localization(field_ring(L), S, p)",
				By(subring, prime, LocalRingSubring.Read(L).At(S, p)))
			inverts := a.Have(
				"O inverts the denominators",
				"∀u:A. u ∈ S ∧ u ∉ p ⇒ L.inv(u) ∈ subring_localization(field_ring(L), S, p) ∧ u * L.inv(u) = L.one",
				By(subring, prime, LocalRingSubring.Read(L).At(S, p)))
			mInvertible := a.Have(
				"𝔪 is invertible over O",
				"invertible_fractional(field_ring(L), subring_localization(field_ring(L), S, p), «maximal»)",
				By(invertible, extendedP, invertibles.At(p)))
			powerLaws := a.Conjuncts(
				GroupPremises(subringO, mInvertible, signed_ideal_power.SignedIdealPowerLaws.Read(L).At(O, M)),
				"the power at 0 is O",
				"the power at 1 is 𝔪",
				"at a natural exponent the power is the natural power",
				"every power is a fractional ideal of O",
				"the exponents add")
			atZero, atOne, natural, powersFractional, additive :=
				powerLaws[0], powerLaws[1], powerLaws[2], powerLaws[3], powerLaws[4]
			mFractional := a.Have(
				"𝔪 is a fractional ideal of O",
				"«fractional»(«maximal»)",
				By(mInvertible, fractional_ideal.InvertibleFractionalDef.At(fieldRing, O, M)))
			oFractional := a.Have(
				"O is a fractional ideal of itself",
				"«fractional»(subring_localization(field_ring(L), S, p))",
				By(subringO, fractional_ideal.SubringSubmodule.Read(L).At(O)))
			sInL := a.Have(
				"S lies in L",
				"S ⊆ L.carrier",
				By(subring, comm_ring.SubringSubset.At(fieldRing, S)))
			oInL := a.Have(
				"O lies in L",
				"subring_localization(field_ring(L), S, p) ⊆ L.carrier",
				By(subringO, comm_ring.SubringSubset.At(fieldRing, O)))
			oneInO := a.Have(
				"one lies in O",
				"L.one ∈ subring_localization(field_ring(L), S, p)",
				By(subringO, comm_ring.SubringOne.At(fieldRing, O)))
			powersInL := a.Have(
				"every power of 𝔪 lies in L",
				"∀n:int. «power»(n) ⊆ L.carrier",
				Derive(func(b *Argument) {
					n := b.FixAs[Int]("n")
					b.Show(
						"a fractional ideal of O lies in L",
						By(
							powersFractional.At(n),
							submodule.SubmoduleSubset.At(localRing, vectors, b.TermAs[Set[A]]("«power»(n)"))))
				}))
			pInM := a.Have(
				"p lies in 𝔪",
				"p ⊆ «maximal»",
				By(extendedP, submodule.SubsetSpan.At(localRing, vectors, p)))
			wholeIdeal := a.Have(
				"a fractional ideal of O inside O but not inside 𝔪 is "+
					"O: it holds a member of O off 𝔪, whose inverse lies in O",
				Statement{
					Binders: "∀I:set(A).",
					Hypotheses: []string{
						"«fractional»(I)",
						"I ⊆ subring_localization(field_ring(L), S, p)",
						"¬(I ⊆ «maximal»)",
					},
					Conclusion: "I = subring_localization(field_ring(L), S, p)",
				},
				Derive(func(b *Argument) {
					I := b.FixAs[Set[A]]("I")
					parts := b.Conjuncts(
						b.Assume(),
						"I is a fractional ideal of O",
						"I lies in O",
						"I is not inside 𝔪")
					x, outside := b.ObtainAs[A](
						"I holds some x off 𝔪",
						"∃x:A. x ∈ I ∧ x ∉ «maximal»",
						By(parts[2], set_basic.SubsetDef.At(I, M)))
					xParts := b.Conjuncts(
						outside,
						"x lies in I",
						"x lies off 𝔪")
					xInO := b.Have(
						"x lies in O",
						"x ∈ subring_localization(field_ring(L), S, p)",
						BySets(parts[1], xParts[0]))
					num, den, fraction := b.Obtain2As[A, A](
						"x is a fraction c / d",
						"∃c d:A. c ∈ S ∧ d ∈ S ∧ d ∉ p ∧ x * d = c",
						BySets(xInO, SubringLocalizationDef.At(fieldRing, S, p)))
					fParts := b.Conjuncts(
						fraction,
						"c lies in S",
						"d lies in S",
						"d lies off p",
						"x · d = c")
					memberships := b.Have(
						"x, c and d lie in L",
						"x ∈ L.carrier ∧ c ∈ L.carrier ∧ d ∈ L.carrier",
						BySets(sInL, oInL, xInO, fParts[0], fParts[1]))
					inL := b.Conjuncts(
						memberships,
						"x lies in L",
						"c lies in L",
						"d lies in L")
					xm := b.MemberOf[on.L](x, inL[0])
					cm := b.MemberOf[on.L](num, inL[1])
					dm := b.MemberOf[on.L](den, inL[2])
					dInverse := b.Conjuncts(
						GroupPremises(fParts[1], fParts[2], inverts.At(den)),
						"the inverse of d lies in O",
						"d · d⁻¹ = 1")
					numeratorOff := b.Have(
						"c lies off p: else x = d⁻¹ · c would lie in 𝔪",
						"c ∉ p",
						Derive(func(c *Argument) {
							inP := c.SupposeNot()
							quotient := c.Have(
								"x = d⁻¹ · c",
								"x = L.inv(d) * c",
								ByArith(
									L,
									xm,
									cm,
									dm,
									field.InvIn.Read(L).At(dm),
									Scaled(c.TermAs[A]("L.inv(d)"), fParts[3]),
									Scaled(x, dInverse[1])))
							inM := c.Have(
								"c lies in 𝔪, which holds p",
								"c ∈ «maximal»",
								By(inP, pInM, set_basic.SubsetDef.At(p, M)))
							c.Show(
								"d⁻¹ · c is an O-multiple of a member of 𝔪",
								By(
									quotient,
									xParts[1],
									dInverse[0],
									inM,
									mFractional,
									submodule.SubmoduleSmul.At(localRing, vectors, M, c.TermAs[A]("L.inv(d)"), num)))
						}))
					zeroInM := b.Have(
						"zero lies in 𝔪",
						"L.zero ∈ «maximal»",
						By(mFractional, submodule.SubmoduleZero.At(localRing, vectors, M)))
					nonzero := b.Have(
						"x is not zero, zero lying in 𝔪",
						"x ≠ L.zero",
						By(zeroInM, xParts[1]))
					leftInverse := b.Have(
						"x⁻¹ · x = 1",
						"L.inv(x) * x = L.one",
						By(nonzero, field.MulLeftInverseOn.Read(L).At(xm)))
					inverseInO := b.Have(
						"the inverse of x is d / c, which lies in O",
						"L.inv(x) ∈ subring_localization(field_ring(L), S, p)",
						Derive(func(c *Argument) {
							xInverse := field.InvIn.Read(L).At(xm)
							swapped := c.Have(
								"x⁻¹ · c = d",
								"L.inv(x) * c = d",
								ByArith(
									L,
									xm,
									cm,
									dm,
									xInverse,
									Scaled(c.TermAs[A]("L.inv(x)"), fParts[3]),
									Scaled(den, leftInverse)))
							c.Show(
								"with numerator d and denominator c",
								BySets(
									xInverse,
									fParts[1],
									fParts[0],
									numeratorOff,
									swapped,
									SubringLocalizationDef.At(fieldRing, S, p)))
						}))
					oneInI := b.Have(
						"so one = x⁻¹ · x lies in I",
						"L.one ∈ I",
						By(
							Normalized,
							leftInverse,
							inverseInO,
							xParts[0],
							parts[0],
							submodule.SubmoduleSmul.At(localRing, vectors, I, b.TermAs[A]("L.inv(x)"), x)))
					oInI := b.Have(
						"and every member of O, a multiple of one, lies in I",
						"subring_localization(field_ring(L), S, p) ⊆ I",
						Unfold(set_basic.SubsetDef),
						Derive(func(c *Argument) {
							o := c.FixAs[A]("o")
							oIn := c.Assume()
							om := c.MemberOf[on.L](o, c.Have(
								"o lies in L",
								"o ∈ L.carrier",
								BySets(oInL, oIn)))
							unit := c.Have(
								"o · 1 = o",
								"o * L.one = o",
								ByArith(L, om))
							c.Show(
								"o · 1 lies in I",
								By(
									Normalized,
									unit,
									oIn,
									oneInI,
									parts[0],
									submodule.SubmoduleSmul.At(localRing, vectors, I, o, c.TermAs[A]("L.one"))))
						}))
					b.Show(
						"so I is O",
						By(parts[1], oInI, set_order.SubsetAntisym.At(I, O)))
				}))
			cancels := a.Have(
				"the powers at z and −z multiply to O",
				"∀z:int. «product»(«power»(z), «power»(-z)) = subring_localization(field_ring(L), S, p)",
				Derive(func(b *Argument) {
					z := b.FixAs[Int]("z")
					opposite := b.Have(
						"z and −z add to 0",
						"z + -z = int_of_num(0)",
						ByArith())
					b.Show(
						"the exponents add to 0",
						By(opposite, atZero, additive.At(z, b.TermAs[Int]("-z"))))
				}))
			chartPowers := a.Have(
				"𝔪ⁿ meets S in pⁿ",
				"∀n:num. S ∩ «localPower»(n) = «chartPower»(n)",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					b.Show(
						"by the contraction of the powers",
						By(subring, maximal, invertible, LocalPowerContraction.Read(L).At(S, p, n)))
				}))
			colengthBound := a.Conjuncts(
				GroupPremises(
					subring,
					subfield,
					kInS,
					rational,
					invertible,
					ideal_colength.RationalPowerColength.Read(L).At(k, S, p)),
				"the n-th power of p has colength n",
				"a member of pⁿ generates an ideal of colength at least n")[1]
			elementPower := a.Have(
				"a nonzero member a of S generates a natural power of 𝔪",
				Statement{
					Binders:    "∀a:A.",
					Hypotheses: []string{"a ∈ S", "a ≠ L.zero"},
					Conclusion: "∃n:num. " +
						"    image(L.mul(a), subring_localization(field_ring(L), S, p)) = «power»(int_of_num(n))",
				},
				Derive(func(b *Argument) {
					x := b.FixAs[A]("a")
					parts := b.Conjuncts(
						b.Assume(),
						"a lies in S",
						"a is not zero")
					aInO := b.Have(
						"a lies in O",
						"a ∈ subring_localization(field_ring(L), S, p)",
						BySets(sInO, parts[0]))
					am := b.MemberOf[on.L](x, b.Have(
						"a lies in L",
						"a ∈ L.carrier",
						BySets(sInL, parts[0])))
					finiteA := b.Have(
						"S/aS is finite-dimensional",
						"«finiteQuotient»(S, image(L.mul(a), S))",
						By(parts[0], parts[1], finite.At(x)))
					bounded := b.Have(
						"a lies in 𝔪ⁿ only for n up to the colength of aS, lying then in pⁿ",
						"∀n:num. a ∈ «power»(int_of_num(n)) ⇒ n ≤ «colength»(S, image(L.mul(a), S))",
						Derive(func(c *Argument) {
							n := c.FixAs[Nat]("n")
							inPower := c.Assume()
							inChart := c.Have(
								"so a lies in pⁿ",
								"a ∈ «chartPower»(n)",
								BySets(parts[0], inPower, natural.At(n), chartPowers.At(n)))
							c.Show(
								"which bounds n by the colength of aS",
								By(inChart, finiteA, colengthBound.At(x, n)))
						}))
					aInZero := b.Have(
						"a lies in 𝔪⁰, which is O",
						"a ∈ «power»(int_of_num(0))",
						atZero.Rw(),
						By(aInO))
					descend := b.Have(
						"below a power of 𝔪 missing a there is a largest one holding a",
						Statement{
							Binders:    "∀N:num.",
							Hypotheses: []string{"a ∉ «power»(int_of_num(N))"},
							Conclusion: "∃n:num. a ∈ «power»(int_of_num(n)) ∧ a ∉ «power»(int_of_num(n + 1))",
						},
						Derive(func(c *Argument) {
							c.Induct("N")
							c.Base(
								"𝔪⁰ is O, which holds a",
								func(d *Argument) {
									missing := d.Assume()
									d.Show(
										"a would miss O",
										By(missing, aInZero))
								})
							c.Step(
								"either a lies in 𝔪ᴺ, the largest, or a lower power is",
								func(d *Argument, ih Fact) {
									missing := d.Assume()
									N := d.TermAs[Nat]("N")
									d.Cases(d.TermAs[Bool]("a ∈ «power»(int_of_num(N))"))
									d.When(
										"a lies in 𝔪ᴺ but not in the next power",
										func(e *Argument, holds Fact) {
											successor := e.Have(
												"suc(N) is N + 1",
												"suc(N) = N + 1",
												ByArith())
											e.Take(N)
											e.Show(
												"N is the largest",
												By(holds, missing, successor))
										})
									d.Otherwise(
										"a misses 𝔪ᴺ too, and a lower power is the largest",
										func(e *Argument, missesLower Fact) {
											e.Show(
												"by induction",
												By(missesLower, ih))
										})
								})
						}))
					beyond := b.Have(
						"the colength plus one exceeds the colength",
						"¬(«colength»(S, image(L.mul(a), S)) + 1 ≤ «colength»(S, image(L.mul(a), S)))",
						ByArith())
					n, largest := b.ObtainAs[Nat](
						"take the largest n with a in 𝔪ⁿ",
						"∃n:num. a ∈ «power»(int_of_num(n)) ∧ a ∉ «power»(int_of_num(n + 1))",
						By(
							beyond,
							bounded.At(b.TermAs[Nat]("«colength»(S, image(L.mul(a), S)) + 1")),
							descend.At(b.TermAs[Nat]("«colength»(S, image(L.mul(a), S)) + 1"))))
					ends := b.Conjuncts(
						largest,
						"a lies in 𝔪ⁿ",
						"but not in 𝔪ⁿ⁺¹")
					N, minusN := b.TermAs[Int]("n"), b.TermAs[Int]("-&n")
					powerN, powerMinus :=
						b.TermAs[Set[A]]("«power»(int_of_num(n))"), b.TermAs[Set[A]]("«power»(-int_of_num(n))")
					principal := b.TermAs[Set[A]]("image(L.mul(a), subring_localization(field_ring(L), S, p))")
					aOFractional := b.Have(
						"aO is a fractional ideal of O",
						"«fractional»(image(L.mul(a), subring_localization(field_ring(L), S, p)))",
						By(subringO, oFractional, fractional_ideal.ScaleSubmodule.Read(L).At(O, O, am)))
					aOInL := b.Have(
						"aO lies in L",
						"image(L.mul(a), subring_localization(field_ring(L), S, p)) ⊆ L.carrier",
						By(aOFractional, submodule.SubmoduleSubset.At(localRing, vectors, principal)))
					unit := b.Have(
						"a · 1 = a",
						"a * L.one = a",
						ByArith(L, am))
					aInAO := b.Have(
						"a lies in aO, O holding one",
						"a ∈ image(L.mul(a), subring_localization(field_ring(L), S, p))",
						By(unit, oneInO, set_image.FunInImage.At(b.TermAs[Fun[A, A]]("L.mul(a)"), O, b.TermAs[A]("L.one"))))
					multiples := b.Have(
						"each multiple a · o with o in O lies in 𝔪ⁿ, an O-module holding a",
						"∀o:A. o ∈ subring_localization(field_ring(L), S, p) ⇒ a * o ∈ «power»(int_of_num(n))",
						Derive(func(c *Argument) {
							o := c.FixAs[A]("o")
							oIn := c.Assume()
							om := c.MemberOf[on.L](o, c.Have(
								"o lies in L",
								"o ∈ L.carrier",
								BySets(oInL, oIn)))
							commuted := c.Have(
								"a · o = o · a",
								"a * o = o * a",
								ByArith(L, am, om))
							c.Show(
								"o · a lies in 𝔪ⁿ",
								By(
									commuted,
									oIn,
									ends[0],
									powersFractional.At(N),
									submodule.SubmoduleSmul.At(localRing, vectors, powerN, o, x)))
						}))
					aOInPower := b.Have(
						"so aO lies in 𝔪ⁿ",
						"image(L.mul(a), subring_localization(field_ring(L), S, p)) ⊆ «power»(int_of_num(n))",
						By(multiples, set_image.ImageSubsetIff.At(b.TermAs[Fun[A, A]]("L.mul(a)"), O, powerN)))
					I, iDef := b.LetAs[Set[A]](
						"I",
						"«product»(image(L.mul(a), subring_localization(field_ring(L), S, p)), «power»(-int_of_num(n)))")
					inside := b.Have(
						"I lies in 𝔪ⁿ · 𝔪⁻ⁿ = O",
						"I ⊆ subring_localization(field_ring(L), S, p)",
						By(
							iDef,
							aOInPower,
							set_order.SubsetRefl,
							cancels.At(N),
							fractional_ideal.FractionalMulMono.Read(L).At(O, principal, powerN, powerMinus, powerMinus)))
					back := b.Have(
						"I · 𝔪ⁿ is aO",
						"«product»(I, «power»(int_of_num(n))) = image(L.mul(a), subring_localization(field_ring(L), S, p))",
						By(
							iDef,
							subringO,
							aOInL,
							oInL,
							aOFractional,
							powersInL.At(minusN),
							powersInL.At(N),
							cancels.At(N),
							fractional_ideal.FractionalMulAssoc.Read(L).At(O, principal, powerMinus, powerN),
							fractional_ideal.FractionalMulComm.Read(L).At(O, powerMinus, powerN),
							fractional_ideal.FractionalMulComm.Read(L).At(O, principal, O),
							fractional_ideal.FractionalMulOne.Read(L).At(O, principal)))
					nextPower := b.Have(
						"𝔪 · 𝔪ⁿ is 𝔪ⁿ⁺¹",
						"«product»(«maximal», «power»(int_of_num(n))) = «power»(int_of_num(n + 1))",
						By(
							atOne,
							b.Have(
								"1 + n is n + 1",
								"1 + &n = int_of_num(n + 1)",
								ByArith()),
							additive.At(b.TermAs[Int]("1"), N)))
					notInsideM := b.Have(
						"I is not inside 𝔪, else aO = I · 𝔪ⁿ would lie in 𝔪ⁿ⁺¹",
						"¬(I ⊆ «maximal»)",
						Derive(func(c *Argument) {
							insideM := c.SupposeNot()
							smaller := c.Have(
								"aO = I · 𝔪ⁿ lies in 𝔪 · 𝔪ⁿ",
								"image(L.mul(a), subring_localization(field_ring(L), S, p)) ⊆ "+
									"«product»(«maximal», «power»(int_of_num(n)))",
								By(
									back,
									insideM,
									set_order.SubsetRefl,
									fractional_ideal.FractionalMulMono.Read(L).At(O, I, M, powerN, powerN)))
							c.Show(
								"so a would lie in 𝔪ⁿ⁺¹",
								By(
									aInAO,
									smaller,
									nextPower,
									ends[1],
									set_basic.SubsetDef.At(
										principal, c.TermAs[Set[A]]("«product»(«maximal», «power»(int_of_num(n)))"))))
						}))
					iFractional := b.Have(
						"I is a fractional ideal of O",
						"«fractional»(I)",
						By(
							Normalized,
							iDef,
							subringO,
							aOInL,
							powersInL.At(minusN),
							fractional_ideal.FractionalMulSubmodule.Read(L).At(O, principal, powerMinus)))
					whole := b.Have(
						"so I is O",
						"I = subring_localization(field_ring(L), S, p)",
						By(iFractional, inside, notInsideM, wholeIdeal.At(I)))
					b.Take(n)
					b.Show(
						"and aO = O · 𝔪ⁿ = 𝔪ⁿ",
						By(
							back,
							whole,
							subringO,
							powersFractional.At(N),
							fractional_ideal.FractionalMulOne.Read(L).At(O, powerN)))
				}))
			represented := a.Unfolded(fractions, field.FractionFieldCarrierDef)
			everyPower := a.Have(
				"a nonzero f = a / b generates the power of 𝔪 at the difference of the exponents of a and b",
				Statement{
					Binders: "∀f:A.",
					Hypotheses: []string{
						"f ∈ L.carrier",
						"f ≠ L.zero",
					},
					Conclusion: "∃n:int. image(L.mul(f), subring_localization(field_ring(L), S, p)) = «power»(n)",
				},
				Derive(func(b *Argument) {
					f := b.FixAs[A]("f")
					parts := b.Conjuncts(
						b.Assume(),
						"f lies in L",
						"f is not zero")
					fm := b.MemberOf[on.L](f, parts[0])
					num, den, fraction := b.Obtain2As[A, A](
						"f is a fraction a / b of S",
						"∃a b:A. a ∈ S ∧ b ∈ S ∧ b ≠ L.zero ∧ f * b = a",
						By(parts[0], represented))
					fp := b.Conjuncts(
						fraction,
						"a lies in S",
						"b lies in S",
						"b is not zero",
						"f · b = a")
					bm := b.MemberOf[on.L](den, b.Have(
						"b lies in L",
						"b ∈ L.carrier",
						BySets(sInL, fp[1])))
					aNonzero := b.Have(
						"a is not zero, f and b not being zero",
						"a ≠ L.zero",
						By(Normalized, fp[3], parts[1], fp[2], field.MulEqZeroOn.Read(L).At(fm, bm)))
					_, aPower := b.ObtainAs[Nat](
						"aO is a natural power 𝔪ᵐ",
						"∃m:num. image(L.mul(a), subring_localization(field_ring(L), S, p)) = «power»(int_of_num(m))",
						By(fp[0], aNonzero, elementPower.At(num)))
					_, bPower := b.ObtainAs[Nat](
						"bO is a natural power 𝔪ʲ",
						"∃j:num. image(L.mul(b), subring_localization(field_ring(L), S, p)) = «power»(int_of_num(j))",
						By(fp[1], fp[2], elementPower.At(den)))
					principalProduct := b.Have(
						"fO · bO = (f · b)O = aO",
						"«product»(image(L.mul(f), subring_localization(field_ring(L), S, p)), "+
							"    image(L.mul(b), subring_localization(field_ring(L), S, p))) = "+
							"image(L.mul(a), subring_localization(field_ring(L), S, p))",
						By(fp[3], subringO, fm, bm, fractional_ideal.PrincipalProduct.Read(L).At(O, fm, bm)))
					fO := b.TermAs[Set[A]]("image(L.mul(f), subring_localization(field_ring(L), S, p))")
					J, minusJ := b.TermAs[Int]("j"), b.TermAs[Int]("-&j")
					powerJ, powerMinusJ :=
						b.TermAs[Set[A]]("«power»(int_of_num(j))"), b.TermAs[Set[A]]("«power»(-int_of_num(j))")
					fOFractional := b.Have(
						"fO is a fractional ideal of O",
						"«fractional»(image(L.mul(f), subring_localization(field_ring(L), S, p)))",
						By(subringO, oFractional, fractional_ideal.ScaleSubmodule.Read(L).At(O, O, fm)))
					fOInL := b.Have(
						"fO lies in L",
						"image(L.mul(f), subring_localization(field_ring(L), S, p)) ⊆ L.carrier",
						By(fOFractional, submodule.SubmoduleSubset.At(localRing, vectors, fO)))
					b.Take(b.TermAs[Int]("&m + -&j"))
					b.Show(
						"fO is fO · 𝔪ʲ · 𝔪⁻ʲ = aO · 𝔪⁻ʲ = 𝔪ᵐ · 𝔪⁻ʲ",
						CalcEq(
							Leg(
								b.TermAs[Set[A]](
									"«product»(image(L.mul(f), subring_localization(field_ring(L), S, p)), "+
										"    subring_localization(field_ring(L), S, p))"),
								"O is the unit",
								By(
									subringO,
									fOFractional,
									fOInL,
									oInL,
									fractional_ideal.FractionalMulComm.Read(L).At(O, fO, O),
									fractional_ideal.FractionalMulOne.Read(L).At(O, fO))),
							Leg(
								b.TermAs[Set[A]](
									"«product»(image(L.mul(f), subring_localization(field_ring(L), S, p)), "+
										"    «product»(«power»(int_of_num(j)), «power»(-int_of_num(j))))"),
								"the powers at j and −j cancel",
								By(cancels.At(J))),
							Leg(
								b.TermAs[Set[A]](
									"«product»(«product»(image(L.mul(f), subring_localization(field_ring(L), S, p)), "+
										"        «power»(int_of_num(j))), "+
										"    «power»(-int_of_num(j)))"),
								"the product associates",
								By(
									subringO,
									fOInL,
									powersInL.At(J),
									powersInL.At(minusJ),
									fractional_ideal.FractionalMulAssoc.Read(L).At(O, fO, powerJ, powerMinusJ))),
							Leg(
								b.TermAs[Set[A]]("«product»(«power»(int_of_num(m)), «power»(-int_of_num(j)))"),
								"fO · bO is aO, the powers at j and m",
								By(principalProduct, bPower, aPower)),
							FinalLeg(
								"the exponents add",
								By(additive.At(b.TermAs[Int]("m"), minusJ)))))
				}))
			distinct := a.Have(
				"the powers of 𝔪, a proper invertible ideal of O, are distinct",
				"∀m n:int. «power»(m) = «power»(n) ⇒ m = n",
				Derive(func(b *Argument) {
					m, n := b.FixAs[Int]("m"), b.FixAs[Int]("n")
					equal := b.Assume()
					b.Show(
						"by injectivity of the signed powers",
						By(
							equal,
							subringO,
							mInvertible,
							mInO,
							proper,
							signed_ideal_power.SignedPowerInjective.Read(L).At(O, M, m, n)))
				}))
			unique := a.Have(
				"so each nonzero f generates exactly one power of 𝔪",
				Statement{
					Binders: "∀f:A.",
					Hypotheses: []string{
						"f ∈ L.carrier",
						"f ≠ L.zero",
					},
					Conclusion: "∃!n:int. image(L.mul(f), subring_localization(field_ring(L), S, p)) = «power»(n)",
				},
				By(everyPower, distinct))
			decreasing := a.Have(
				"the powers of 𝔪 decrease strictly",
				"∀i j:int. «power»(i) ⊆ «power»(j) ⇔ j ≤ i",
				Derive(func(b *Argument) {
					i, j := b.FixAs[Int]("i"), b.FixAs[Int]("j")
					b.Show(
						"by antitony of the signed powers",
						By(
							subringO,
							mInvertible,
							mInO,
							proper,
							signed_ideal_power.SignedPowerAntitone.Read(L).At(O, M, i, j)))
				}))
			valuation := a.Have(
				"an exponent of the principal ideals is a valuation",
				Statement{
					Binders: "∀v:(A → int).",
					Hypotheses: []string{
						"∀f:A. " +
							"    f ∈ L.carrier ∧ f ≠ L.zero ⇒ " +
							"    image(L.mul(f), subring_localization(field_ring(L), S, p)) = «power»(v(f))",
					},
					Conclusion: "valuation_order(field_ring(L), v)",
				},
				Derive(func(b *Argument) {
					v := b.FixAs[Fun[A, Int]]("v")
					exponents := b.Assume()
					b.Show(
						"signed powers carry a valuation",
						By(
							exponents,
							subringO,
							mInvertible,
							mInO,
							proper,
							signed_ideal_power.SignedPowerValuation.Read(L).At(O, M, v)))
				}))
			a.Show(
				"exactly one exponent, decreasing powers, and the valuation",
				By(unique, decreasing, valuation))
		}),
})}

// LocalPowerContraction — the powers of the maximal ideal 𝔪 of the
// localization O of S at a maximal invertible ideal p meet S in the powers of
// p. 𝔪ⁿ is the extension of pⁿ to O, extension multiplying invertible ideals
// (LocalExtensionLaws), and pⁿ is an invertible ideal inside S
// (fractional_ideal.InvertibleIdealPowers); so its members y are those a denominator b off p
// brings into pⁿ (LocalExtensionCleared). For y in S, b is a unit modulo pⁿ
// (UnitModuloMaximalPowers), b·c + z = 1 with c in S and z in pⁿ, and
// y = c·(b·y) + y·z lies in pⁿ.
var LocalPowerContraction = localPowerContractionThm{family.Add(registry.ProofEntry{
	Name: "LocalPowerContraction",
	Key:  "prop_8ab76ddd1d40cc8",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S p:set(A). ∀n:num.",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"maximal_ideal(restrict_ring(field_ring(L), S), p)",
			"invertible_fractional(field_ring(L), S, p)",
		},
		Conclusion: "S ∩ «localPower»(n) = «power»(n)",
		Abbrev: Abbrev{
			{Name: "maximal", Text: "ideal_span( " +
				"    restrict_ring(field_ring(L), subring_localization(field_ring(L), S, p)), p)"},
			{Name: "extended", Text: "module_span( " +
				"    restrict_ring(field_ring(L), subring_localization(field_ring(L), S, p)), " +
				"    regular_module(field_ring(L)))"},
			{Name: "power", Text: "λn:num. " +
				"    monoid_pow(λX:set(A). λY:set(A). fractional_mul(field_ring(L), S, X, Y), S, p, n)"},
			{Name: "localPower", Text: "λn:num. " +
				"    monoid_pow(λX:set(A). λY:set(A). " +
				"            fractional_mul(field_ring(L), subring_localization(field_ring(L), S, p), X, Y), " +
				"        subring_localization(field_ring(L), S, p), " +
				"        «maximal», " +
				"        n)"},
		},
	},
		func(a *Argument, L field.FieldFact[on.L], S, p *Expr[Set[A]], n *Expr[Nat], h Fact) {
			given := a.Conjuncts(
				h,
				"S is a subring of L",
				"p is maximal",
				"p is invertible")
			subring, maximal, invertible := given[0], given[1], given[2]
			fieldRing := a.TermAs[RingOps[A]]("field_ring(L)")
			chartRing := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), S)")
			localRing := a.TermAs[RingOps[A]](
				"restrict_ring(field_ring(L), subring_localization(field_ring(L), S, p))")
			vectors := a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))")
			ringS := a.Have(
				"S is a commutative ring",
				"comm_ring_on(restrict_ring(field_ring(L), S))",
				By(subring, comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(S)))
			prime := a.Have(
				"p is prime",
				"prime_ideal(restrict_ring(field_ring(L), S), p)",
				By(maximal, ring_ideal.MaximalIsPrime.Read(ringS).At(p)))
			laws := a.Conjuncts(
				GroupPremises(subring, prime, LocalExtensionLaws.Read(L).At(S, p)),
				"O is a subring",
				"S extends to O",
				"extension is multiplicative on invertible ideals",
				"it keeps invertible ideals invertible",
				"p extends to 𝔪",
				"𝔪 lies in O",
				"𝔪 misses one",
				"an ideal holding a unit extends to O")
			whole, multiplicative, extendedP := laws[1], laws[2], laws[4]
			pInS := a.Have(
				"p lies in S",
				"p ⊆ S",
				By(prime, ring_ideal.PrimeIdealIdeal.At(chartRing, p), ring_ideal.RingIdealDef.At(chartRing, p)))
			sInL := a.Have(
				"S lies in L",
				"S ⊆ L.carrier",
				By(subring, comm_ring.SubringSubset.At(fieldRing, S)))
			extendedPowers := a.Have(
				"𝔪ᵐ is the extension of pᵐ for every m, extension multiplying invertible ideals",
				"∀m:num. «localPower»(m) = «extended»(«power»(m))",
				Derive(func(b *Argument) {
					b.Induct("m")
					b.Base(
						"the zeroth powers are S and O, the extension of S",
						Simp(Fwd(comm_monoid.MonoidPowDef.Inst[Set[A]]())),
						By(whole))
					b.Step(
						"the next powers are p and 𝔪 times the last",
						func(c *Argument, ih Fact) {
							last := c.TermAs[Set[A]]("«power»(m)")
							lastInvertible := c.Conjuncts(
								GroupPremises(
									subring,
									invertible,
									pInS,
									fractional_ideal.InvertibleIdealPowers.Read(L).At(S, p, c.TermAs[Nat]("m"))),
								"pᵐ is invertible",
								"and lies inside S")[0]
							c.Do(Simp(Fwd(comm_monoid.MonoidPowDef.Inst[Set[A]]())))
							c.Show(
								"the extension of p · pᵐ is 𝔪 · 𝔪ᵐ",
								By(invertible, lastInvertible, ih, extendedP, multiplicative.At(p, last)))
						})
				}))
			current := a.Conjuncts(
				GroupPremises(
					subring, invertible, pInS, fractional_ideal.InvertibleIdealPowers.Read(L).At(S, p, n)),
				"pⁿ is invertible",
				"it lies in S")
			power := a.TermAs[Set[A]]("«power»(n)")
			powerFractional := a.Have(
				"pⁿ is a fractional ideal of S",
				"submodule(restrict_ring(field_ring(L), S), regular_module(field_ring(L)), «power»(n))",
				By(current[0], fractional_ideal.InvertibleFractionalDef.At(fieldRing, S, power)))
			cleared := a.Have(
				"so 𝔪ⁿ is the members of L a denominator off p brings into pⁿ",
				"«localPower»(n) = {y:A | y ∈ L.carrier ∧ (∃b:A. b ∈ S ∧ b ∉ p ∧ b * y ∈ «power»(n))}",
				By(
					extendedPowers.At(n),
					subring,
					prime,
					powerFractional,
					LocalExtensionCleared.Read(L).At(S, p, power)))
			contained := a.Have(
				"a member of S in 𝔪ⁿ lies in pⁿ",
				"S ∩ «localPower»(n) ⊆ «power»(n)",
				Unfold(set_basic.SubsetDef),
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					xIn := b.Conjuncts(
						b.Simplified(b.Assume(), Fwd(set_basic.InInter)),
						"x lies in S",
						"x lies in 𝔪ⁿ")
					d, brought := b.ObtainAs[A](
						"a denominator b brings x into pⁿ",
						"∃b:A. b ∈ S ∧ b ∉ p ∧ b * x ∈ «power»(n)",
						BySets(xIn[1], cleared))
					denominator := b.Conjuncts(
						brought,
						"b lies in S",
						"b lies off p",
						"b · x lies in pⁿ")
					c, y, unit := b.Obtain2As[A, A](
						"b is a unit modulo pⁿ: b · c + y = 1 with c in S and y in pⁿ",
						"∃c y:A. c ∈ S ∧ y ∈ «power»(n) ∧ b * c + y = L.one",
						By(
							subring,
							maximal,
							denominator[0],
							denominator[1],
							UnitModuloMaximalPowers.Read(L).At(S, p, d, n)))
					unitParts := b.Conjuncts(
						unit,
						"c lies in S",
						"y lies in pⁿ",
						"b · c + y = 1")
					memberships := b.Have(
						"x, b, c and y lie in L",
						"x ∈ L.carrier ∧ b ∈ L.carrier ∧ c ∈ L.carrier ∧ y ∈ L.carrier",
						BySets(sInL, current[1], xIn[0], denominator[0], unitParts[0], unitParts[1]))
					expand := b.Have(
						"x = c · (b · x) + x · y",
						"x = c * (b * x) + x * y",
						ByArith(L, memberships, Scaled(x, unitParts[2])))
					bx := b.TermAs[A]("b * x")
					b.Show(
						"both terms lie in pⁿ",
						By(
							expand,
							unitParts[0],
							unitParts[1],
							denominator[2],
							xIn[0],
							powerFractional,
							submodule.SubmoduleSmul.At(chartRing, vectors, power, c, bx),
							submodule.SubmoduleSmul.At(chartRing, vectors, power, x, y),
							submodule.SubmoduleAdd.At(
								chartRing, vectors, power, b.TermAs[A]("c * (b * x)"), b.TermAs[A]("x * y"))))
				}))
			containing := a.Have(
				"pⁿ lies in S and in its extension 𝔪ⁿ",
				"«power»(n) ⊆ S ∩ «localPower»(n)",
				BySets(current[1], extendedPowers.At(n), submodule.SubsetSpan.At(localRing, vectors, power)))
			a.Show(
				"so S meets 𝔪ⁿ in pⁿ",
				By(
					contained,
					containing,
					set_order.SubsetAntisym.At(a.TermAs[Set[A]]("S ∩ «localPower»(n)"), power)))
		}),
})}
