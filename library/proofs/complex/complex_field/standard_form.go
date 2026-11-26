// standard_form.go — the reals inside ℂ, and i: every complex number is
// x + i·y.

package complex_field

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/real/real_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// ISquared — i² = −1: the imaginary unit is a square root of −1, which
// is what the product's definition was built to make true.
var ISquared = iSquaredThm{family.Add(registry.ProofEntry{
	Name: "ISquared",
	Key:  "prop_92ac9df5041ad3b",
	Build: family.Theorem("complex_i * complex_i = -complex_of_real(&1)",
		Chain(Simp(
			Parts,
			Fwd(ComplexIDef),
			Fwd(ComplexMulDef),
			Fwd(ComplexNegDef),
			Fwd(ComplexOfRealDef)), ByArith())),
})}

// INonzero — i is not zero: its imaginary part is 1, and zero's is 0.
var INonzero = iNonzeroThm{family.Add(registry.ProofEntry{
	Name: "INonzero",
	Key:  "prop_7e9d1f6cf54f790",
	Build: family.Theorem("complex_i ≠ &0",
		Chain(Simp(Parts, Fwd(ComplexIDef), Fwd(ComplexOfRealDef)), ByArith())),
})}

// InvI — the inverse of i is −i: i has parts 0 and 1, the sum of their
// squares is 1, so the inverse has parts 0/1 and −1/1.
var InvI = invIThm{family.Add(registry.ProofEntry{
	Name: "InvI",
	Key:  "prop_6cb647a58f8ade4a",
	Build: family.Theorem("complex_inv(complex_i) = -complex_i",
		Chain(Simp(Parts, Fwd(ComplexInvDef), Fwd(ComplexIDef), Fwd(ComplexNegDef)), ByArith())),
})}

// StandardForm — the pair with parts x and y is x + i·y, the reals
// seen in ℂ.
var StandardForm = standardFormThm{family.Add(registry.ProofEntry{
	Name: "StandardForm",
	Key:  "prop_2e48e57231b3606b",
	Build: family.Theorem("∀x y:real. "+
		"    complex(x, y) = complex_of_real(x) + complex_i * complex_of_real(y)",
		Chain(Simp(
			Parts,
			Fwd(ComplexAddDef),
			Fwd(ComplexMulDef),
			Fwd(ComplexIDef),
			Fwd(ComplexOfRealDef)), ByArith())),
})}

// OfRealInjective — distinct reals stay distinct in ℂ.
var OfRealInjective = ofRealInjectiveThm{family.Add(registry.ProofEntry{
	Name: "OfRealInjective",
	Key:  "prop_508b23c2f4fcabf2",
	Build: family.Theorem("∀x y:real. complex_of_real(x) = complex_of_real(y) ⇔ x = y",
		Chain(Simp(Parts, Fwd(ComplexOfRealDef)), Basic())),
})}

// OfRealAdd — the sum of two reals, seen in ℂ, is the sum there.
var OfRealAdd = ofRealAddThm{family.Add(registry.ProofEntry{
	Name: "OfRealAdd",
	Key:  "prop_c830e7da89f67f3c",
	Build: family.Theorem("∀x y:real. complex_of_real(x + y) = complex_of_real(x) + complex_of_real(y)",
		Chain(Simp(Parts, Fwd(ComplexAddDef), Fwd(ComplexOfRealDef)), ByArith())),
})}

// OfRealNeg — and so is the negation.
var OfRealNeg = ofRealNegThm{family.Add(registry.ProofEntry{
	Name: "OfRealNeg",
	Key:  "prop_177cd86e29b8c7c6",
	Build: family.Theorem("∀x:real. complex_of_real(-x) = -complex_of_real(x)",
		Chain(Simp(Parts, Fwd(ComplexNegDef), Fwd(ComplexOfRealDef)), ByArith())),
})}

// OfRealSub — and the difference: a difference in ℂ is a sum with the
// negation, and at zero imaginary parts each part of it is the real
// difference.
var OfRealSub = ofRealSubThm{family.Add(registry.ProofEntry{
	Name: "OfRealSub",
	Key:  "prop_32b1f9df0ec5282c",
	Build: family.Theorem("∀x y:real. complex_of_real(x - y) = complex_of_real(x) - complex_of_real(y)",
		Chain(Simp(
			Parts,
			Fwd(ComplexOfRealDef),
			Fwd(ComplexSubDef),
			Fwd(ComplexAddDef),
			Fwd(ComplexNegDef)), ByArith())),
})}

// OfRealMul — and the product: at a zero imaginary part, the cross
// terms of the complex product vanish.
var OfRealMul = ofRealMulThm{family.Add(registry.ProofEntry{
	Name: "OfRealMul",
	Key:  "prop_3efff61aed391aba",
	Build: family.Theorem("∀x y:real. complex_of_real(x * y) = complex_of_real(x) * complex_of_real(y)",
		Chain(Simp(Parts, Fwd(ComplexMulDef), Fwd(ComplexOfRealDef)), ByArith())),
})}

// OfRealInv — the inverse of a real, seen in ℂ, is the inverse there.
// The embedding sends zero to zero, one to one and products to products,
// and a map between fields that does carries inverses to inverses
// (field.MapInv).
var OfRealInv = ofRealInvThm{family.Add(registry.ProofEntry{
	Name: "OfRealInv",
	Key:  "prop_6483436194d50ff8",
	Build: family.Theorem("∀x:real. complex_of_real(real_inv(x)) = complex_inv(complex_of_real(x))",
		func(a *Argument, x *Expr[Real]) {
			reals := a.TermAs[field.FieldOps[Real]]("restrict_field(real_field_ops, 𝕌)")
			complexes := a.TermAs[field.FieldOps[Complex]]("restrict_field(complex_field_ops, 𝕌)")
			realsWhole := a.Have(
				"ℝ is a field on the whole of ℝ",
				"field_on(restrict_field(real_field_ops, 𝕌))",
				By(real_field.Field, field.FieldOnUniverse))
			complexesWhole := a.Have(
				"ℂ is a field on the whole of ℂ",
				"field_on(restrict_field(complex_field_ops, 𝕌))",
				By(Field, field.FieldOnUniverse))
			a.Show(
				"the embedding respects zero, one and products, so it carries inverses to inverses",
				By(
					field.MapInv.At(reals, complexes, a.TermAs[Fun[Real, Complex]]("complex_of_real"), x),
					realsWhole,
					complexesWhole,
					OfRealMul,
					set_basic.InUniv))
		}),
})}

// OfRealDiv — the embedding carries quotients to quotients: a quotient
// is a product with an inverse, and the embedding carries both.
var OfRealDiv = ofRealDivThm{family.Add(registry.ProofEntry{
	Name: "OfRealDiv",
	Key:  "prop_2094f57446691947",
	Build: family.Theorem("∀x y:real. complex_of_real(x / y) = complex_of_real(x) / complex_of_real(y)",
		func(a *Argument, x, y *Expr[Real]) {
			a.Show(
				"each quotient is a product with an inverse, and the embedding carries both",
				Simp(Fwd(real_field.RealDivDef), Fwd(ComplexDivDef), Rev(OfRealInv), Rev(OfRealMul)),
				Refl())
		}),
})}

// OfRealPow — the embedding carries powers to powers. ℝ's power is its
// product's monoid power (real_pow.MonoidPow), and the embedding keeps 1
// and carries products to products, which is all comm_monoid.MapPow
// asks. ℂ's power is spelled with its components here: a chapter cannot
// bind the monoid instance it registers itself.
var OfRealPow = ofRealPowThm{family.Add(registry.ProofEntry{
	Name: "OfRealPow",
	Key:  "prop_a448fea3f02b7040",
	Build: family.Theorem("∀x:real. ∀n:num. "+
		"    complex_of_real(real_pow(x, n)) = "+
		"    monoid_pow(complex_mul, complex_of_real(&1), complex_of_real(x), n)",
		func(a *Argument, x *Expr[Real], n *Expr[Nat]) {
			a.Show(
				"ℝ's power is its product's monoid power, and the embedding keeps 1 and products",
				Simp(Fwd(real_pow.MonoidPow)),
				By(Where(comm_monoid.MapPow, "h", a.Term("complex_of_real")), OfRealMul))
		}),
})}

// OfRealSum — the embedding carries finite sums to sums. A real sum is
// the fold at real addition, and a map that keeps zero and carries a sum
// of two to the sum of the images carries every finite fold
// (monoidal.Homomorphic); the embedding keeps zero, both zeros being 0,
// and carries sums (OfRealAdd).
var OfRealSum = ofRealSumThm{family.Add(registry.ProofEntry{
	Name: "OfRealSum",
	Key:  "prop_c8c8405df2d99c0",
	Build: family.Theorem(Statement{
		Binders:    "∀s:set(A). ∀f:(A → real).",
		Hypotheses: []string{"finite(s)"},
		Conclusion: "complex_of_real(Σ_{i∈s} f(i)) = Σ_{i∈s} complex_of_real(f(i))",
	}, func(a *Argument, s *Expr[Set[A]], f *Arrow[A, Real], finite Fact) {
		a.Show(
			"the embedding keeps zero and carries sums of two to sums, so it carries the fold",
			Unfold(real_sum.RealSumDef),
			By(
				finite,
				monoidal.Homomorphic.At(
					a.TermAs[Op[Real]]("real_add"),
					a.TermAs[Op[Complex]]("complex_add"),
					a.TermAs[Fun[Real, Complex]]("complex_of_real"),
					s,
					f),
				real_ring.MonoidalAdd,
				comm_ring.MonoidalAdd.Read(CommRing),
				real_ring.NeutralAdd,
				comm_ring.NeutralAdd.Read(CommRing),
				OfRealAdd))
	}),
})}

// OfRealCond — the embedding commutes with a conditional: the image of
// COND(c, x, y) is the conditional of the images, by cases on c.
var OfRealCond = ofRealCondThm{family.Add(registry.ProofEntry{
	Name: "OfRealCond",
	Key:  "prop_5493ea5a2476dfd6",
	Reading: "The condition c is any proposition, decided by cases, so no property of the " +
		"embedding enters. At y = 0 it reads a real indicator, COND(c, x, &0), in ℂ as the complex one.",
	Build: family.Theorem("∀c:bool. ∀x y:real. "+
		"    complex_of_real(COND(c, x, y)) = COND(c, complex_of_real(x), complex_of_real(y))",
		func(a *Argument, c *Expr[Bool], _, _ *Expr[Real]) {
			a.Cases(c)
			a.When(
				"c holds",
				func(b *Argument, truth Fact) {
					b.Show(
						"both sides lift x",
						By(truth))
				})
			a.Otherwise(
				"c fails",
				func(b *Argument, falsehood Fact) {
					b.Show(
						"both sides lift y",
						By(falsehood))
				})
		}),
})}

// AddPowOne — n copies of one summed is the real numeral n seen in ℂ:
// the additive power of one is the embedding of ℕ. By induction on n; the
// step is one more copy of one, carried across the embedding. This is the
// bridge the arithmetic closer's structure ring reads ℂ's literals by.
var AddPowOne = addPowOneThm{family.Add(registry.ProofEntry{
	Name: "AddPowOne",
	Key:  "prop_8176237f8256f38",
	Build: family.Theorem("∀n:num. "+
		"    monoid_pow(complex_add, complex_of_real(&0), complex_of_real(&1), n) = complex_of_real(&n)",
		func(a *Argument, n Term) {
			a.Induct(n)
			a.Base(
				"no copies of one is zero",
				Simp(Fwd(comm_monoid.MonoidPowDef.Inst[Complex]())),
				Refl())
			a.Step(
				"one more copy of one, carried across the embedding",
				func(d *Argument, ih Fact) {
					d.Do(Simp(Fwd(comm_monoid.MonoidPowDef.Inst[Complex]())), ih.Rw(), Simp(Fwd(real_ring.OfNumSuc)),
						Simp(Parts, Fwd(ComplexAddDef), Fwd(ComplexOfRealDef)), ByArith())
				})
		}),
})}
