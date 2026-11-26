// embedding.go — how the reals sit in ⟦0, ∞⟧: every extended value is ∞
// or the image of a nonnegative real, the image is never ∞, it is
// one-to-one on the nonnegative reals and flat on the negative ones, and
// the finite value reads a nonnegative real back.
//
// These are the only members that open the representation; every later
// law is argued from them.

package extended_nonneg_real

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/datatypes/option"
	"github.com/euc-ai/xugo/library/registry"
)

// ExtendedCases — every extended nonnegative real is ∞ or the image of a
// nonnegative real: its representative is absent, or present with a
// nonnegative value.
var ExtendedCases = extendedCasesThm{family.Add(registry.ProofEntry{
	Name: "ExtendedCases",
	Key:  "prop_25bb21b7ccfed9e7",
	Build: family.Theorem("∀x:extended_nonneg_real. "+
		"    x = extended_infinity ∨ (∃r:real. &0 ≤ r ∧ x = extended_of_real(r))",
		func(a *Argument, x *Expr[ExtendedNonnegReal]) {
			a.Cases(a.Term("option_of_extended(x) = none"))
			a.When(
				"an absent representative is ∞",
				func(b *Argument, absent Fact) {
					b.Show(
						"x is ∞",
						By(absent, ExtendedNonnegRealRetraction.At(x), ExtendedInfinityDef))
				})
			a.Otherwise(
				"a present representative carries a nonnegative value",
				func(b *Argument, present Fact) {
					rep := b.TermAs[option.Option[Real]]("option_of_extended(x)")
					s, value := b.ObtainAs[Real](
						"the representative is some(s)",
						"∃s:real. option_of_extended(x) = some(s)",
						By(present, option.Cases.At(rep)))
					nonneg := b.Have(
						"a representative's value is nonnegative",
						"&0 ≤ s",
						By(value, ExtendedNonnegRealRetraction.At(x), ExtendedNonnegRealMembership.At(rep)))
					clamp := b.Have(
						"clamping at zero leaves s alone",
						"max(s, &0) = s",
						ByArith(nonneg))
					b.Show(
						"x is the image of s",
						By(value, clamp, nonneg, ExtendedNonnegRealRetraction.At(x), ExtendedOfRealDef.At(s)))
				})
		}),
})}

// OfRealRepresentative — the representative of the image of r is the
// present value max(r, 0): the clamped value is nonnegative, so the
// optional value carrying it lies in the type.
var OfRealRepresentative = ofRealRepresentativeThm{family.Add(registry.ProofEntry{
	Name: "OfRealRepresentative",
	Key:  "prop_45de20ce1c3b68f1",
	Build: family.Theorem("∀r:real. option_of_extended(extended_of_real(r)) = some(max(r, &0))",
		func(a *Argument, r *Expr[Real]) {
			clamped := a.Have(
				"the clamped value is nonnegative",
				"&0 ≤ max(r, &0)",
				ByArith())
			a.Show(
				"some(max(r, 0)) lies in the type, so it is its own representative",
				By(
					clamped,
					ExtendedNonnegRealMembership.At(a.TermAs[option.Option[Real]]("some(max(r, &0))")),
					ExtendedOfRealDef.At(r),
					option.SomeInjective))
		}),
})}

// OfRealNotInfinity — no real embeds as ∞: the representative of an
// image is present, that of ∞ absent.
var OfRealNotInfinity = ofRealNotInfinityThm{family.Add(registry.ProofEntry{
	Name: "OfRealNotInfinity",
	Key:  "prop_d32aa5d61f6e80d2",
	Build: family.Theorem("∀r:real. extended_of_real(r) ≠ extended_infinity",
		func(a *Argument, r *Expr[Real]) {
			a.Show(
				"the image of r is represented by a some, ∞ by none",
				By(
					OfRealRepresentative.At(r),
					ExtendedNonnegRealMembership.At(a.TermAs[option.Option[Real]]("none")),
					ExtendedInfinityDef,
					option.NoneNotSome))
		}),
})}

// ZeroNotInfinity — 0 is not ∞: 0 is the image of a real.
var ZeroNotInfinity = zeroNotInfinityThm{family.Add(registry.ProofEntry{
	Name: "ZeroNotInfinity",
	Key:  "prop_3e7408371c60f94a",
	Build: family.Theorem("&0 ≠ extended_infinity",
		func(a *Argument) {
			a.Show(
				"no real embeds as ∞, 0 among them",
				Cite(OfRealNotInfinity))
		}),
})}

// OfRealInjective — on the nonnegative reals the embedding is
// one-to-one: there clamping does nothing, and some is one-to-one.
var OfRealInjective = ofRealInjectiveThm{family.Add(registry.ProofEntry{
	Name: "OfRealInjective",
	Key:  "prop_279794fb65f02a4c",
	Build: family.Theorem(Statement{
		Binders: "∀r s:real.",
		Hypotheses: []string{
			"&0 ≤ r",
			"&0 ≤ s",
		},
		Conclusion: "extended_of_real(r) = extended_of_real(s) ⇔ r = s",
	}, func(a *Argument, r, s *Expr[Real], nonneg Fact) {
		clamps := a.Have(
			"clamping at zero leaves r and s alone",
			"max(r, &0) = r ∧ max(s, &0) = s",
			ByArith(nonneg))
		a.Show(
			"the representatives some(r) and some(s) agree exactly when r = s",
			By(clamps, OfRealRepresentative.At(r), OfRealRepresentative.At(s), option.SomeInjective.At(r, s)))
	}),
})}

// OfRealNeg — every nonpositive real embeds as 0, the clamp sending it to
// zero.
var OfRealNeg = ofRealNegThm{family.Add(registry.ProofEntry{
	Name: "OfRealNeg",
	Key:  "prop_7ffff8f6fb944454",
	Build: family.Theorem(Statement{
		Binders:    "∀r:real.",
		Hypotheses: []string{"r ≤ &0"},
		Conclusion: "extended_of_real(r) = &0",
	},
		func(a *Argument, r *Expr[Real], nonpos Fact) {
			clamps := a.Have(
				"r and 0 clamp to the same value",
				"max(r, &0) = max(&0, &0)",
				ByArith(nonpos))
			a.Show(
				"the two images carry one clamped value",
				By(Normalized, clamps, ExtendedOfRealDef))
		}),
})}

// OfRealPositivePart — the embedding reads a real at its positive part: a
// nonnegative r is its own positive part, and a negative r and its positive
// part 0 both embed as 0.
var OfRealPositivePart = ofRealPositivePartThm{family.Add(registry.ProofEntry{
	Name: "OfRealPositivePart",
	Key:  "prop_ee39d000cb164aa8",
	Build: family.Theorem("∀r:real. extended_of_real(max(r, &0)) = extended_of_real(r)",
		func(a *Argument, r *Expr[Real]) {
			a.Cases(a.Term("&0 ≤ r"))
			a.When(
				"a nonnegative r is its own positive part",
				func(b *Argument, nonneg Fact) {
					b.Show(
						"max(r, 0) = r",
						ByArith(nonneg))
				})
			a.Otherwise(
				"a negative r and its positive part 0 both embed as 0",
				func(b *Argument, negative Fact) {
					b.Show(
						"each lies at or below 0",
						ByArith(negative, OfRealNeg))
				})
		}),
})}

// ToRealOfReal — the finite value of the image of a nonnegative real is
// the real itself: the image is not ∞, and r is the only nonnegative real
// with that image.
var ToRealOfReal = toRealOfRealThm{family.Add(registry.ProofEntry{
	Name: "ToRealOfReal",
	Key:  "prop_806874184ed00a64",
	Build: family.Theorem(Statement{
		Binders:    "∀r:real.",
		Hypotheses: []string{"&0 ≤ r"},
		Conclusion: "extended_to_real(extended_of_real(r)) = r",
	},
		func(a *Argument, r *Expr[Real], nonneg Fact) {
			a.Show(
				"the nonnegative real chosen with the image of r is r",
				By(
					nonneg,
					ExtendedToRealDef.At(a.TermAs[ExtendedNonnegReal]("extended_of_real(r)")),
					OfRealNotInfinity.At(r),
					OfRealInjective))
		}),
})}

// ToRealOfRealMax — the finite value of the image of any real is its
// positive part: r embeds as its positive part max(r, 0), a nonnegative real
// read back as itself.
var ToRealOfRealMax = toRealOfRealMaxThm{family.Add(registry.ProofEntry{
	Name: "ToRealOfRealMax",
	Key:  "prop_d48d6f80fbe06d62",
	Build: family.Theorem("∀r:real. extended_to_real(extended_of_real(r)) = max(r, &0)",
		func(a *Argument, r *Expr[Real]) {
			a.Show(
				"the image of r is that of its positive part",
				ByArith(OfRealPositivePart.At(r), ToRealOfReal.At(a.TermAs[Real]("max(r, &0)"))))
		}),
})}

// ToRealInfinity — the finite value of ∞ is 0.
var ToRealInfinity = toRealInfinityThm{family.Add(registry.ProofEntry{
	Name: "ToRealInfinity",
	Key:  "prop_f28aa4e5388c0087",
	Build: family.Theorem("extended_to_real(extended_infinity) = &0",
		func(a *Argument) {
			a.Show(
				"at ∞ the definition takes its first branch",
				By(ExtendedToRealDef))
		}),
})}

// OfRealToReal — a finite value is the image of its finite value: it is
// the image of some nonnegative real, which the finite value chooses.
var OfRealToReal = ofRealToRealThm{family.Add(registry.ProofEntry{
	Name: "OfRealToReal",
	Key:  "prop_1204bd97691cf297",
	Build: family.Theorem(Statement{
		Binders:    "∀x:extended_nonneg_real.",
		Hypotheses: []string{"x ≠ extended_infinity"},
		Conclusion: "extended_of_real(extended_to_real(x)) = x",
	},
		func(a *Argument, x *Expr[ExtendedNonnegReal], finite Fact) {
			a.Show(
				"x is the image of a nonnegative real, and the finite value chooses one",
				By(finite, ExtendedToRealDef.At(x), ExtendedCases.At(x)))
		}),
})}

// ToRealNonneg — every finite value is nonnegative: 0 at ∞, and a chosen
// nonnegative real elsewhere.
var ToRealNonneg = toRealNonnegThm{family.Add(registry.ProofEntry{
	Name: "ToRealNonneg",
	Key:  "prop_ae378ee1bff952a8",
	Build: family.Theorem("∀x:extended_nonneg_real. &0 ≤ extended_to_real(x)",
		func(a *Argument, x *Expr[ExtendedNonnegReal]) {
			a.Cases(a.Term("x = extended_infinity"))
			a.When(
				"at ∞ the finite value is 0",
				func(b *Argument, atInfinity Fact) {
					b.Do(atInfinity.Rw())
					b.Show(
						"0 is nonnegative",
						ByArith(ToRealInfinity))
				})
			a.Otherwise(
				"a finite x is the image of a nonnegative real, which its value chooses",
				func(b *Argument, finite Fact) {
					b.Show(
						"the chosen real is nonnegative",
						By(finite, ExtendedToRealDef.At(x), ExtendedCases.At(x)))
				})
		}),
})}

// ToRealZero — the finite value of 0 is 0.
var ToRealZero = toRealZeroThm{family.Add(registry.ProofEntry{
	Name: "ToRealZero",
	Key:  "prop_7fce36085e44d2bb",
	Build: family.Theorem("extended_to_real(&0) = &0",
		func(a *Argument) {
			a.Show(
				"0 is a nonnegative real, read back by its image",
				By(ToRealOfReal.At(a.TermAs[Real]("&0"))))
		}),
})}

// ExtendedEq — two extended values are equal exactly when they are ∞
// together and have the same finite value: a finite value is the image
// of its finite value.
var ExtendedEq = extendedEqThm{family.Add(registry.ProofEntry{
	Name: "ExtendedEq",
	Key:  "prop_ff32101f78ed95cc",
	Build: family.Theorem("∀x y:extended_nonneg_real. "+
		"    x = y ⇔ "+
		"    (x = extended_infinity ⇔ y = extended_infinity) ∧ extended_to_real(x) = extended_to_real(y)",
		func(a *Argument, x, y *Expr[ExtendedNonnegReal]) {
			a.Show(
				"two finite values are the images of their finite values",
				By(OfRealToReal.At(x), OfRealToReal.At(y)))
		}),
})}
