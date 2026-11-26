// euclidean.go — the norm of ℤ[i] and its division algorithm.

package gaussian_integer

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/euclidean_domain"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_construction"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_embed"
	"github.com/euc-ai/xugo/library/proofs/real/rational"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/registry"
)

// NormReal — the norm of a Gaussian integer, read in ℝ, is the square sum
// of its parts: that sum is an integer and not negative, so reading it as
// an integer and then as a natural number loses nothing.
var NormReal = normRealThm{family.Add(registry.ProofEntry{
	Name: "NormReal",
	Key:  "prop_232d29d1ad3ef740",
	Build: family.Theorem(Statement{
		Binders:    "∀z:complex.",
		Hypotheses: []string{"z ∈ gaussian_integers"},
		Conclusion: "&(gaussian_norm(z)) = «SquareSum»(z)",
		Abbrev:     Abbrev{{Name: "SquareSum", Text: "λz:complex. re(z) * re(z) + im(z) * im(z)"}},
	}, func(a *Argument, z *Expr[Complex], member Fact) {
		integral := a.Have(
			"the square sum of integer parts is an integer",
			"integer(«SquareSum»(z))",
			By(
				member,
				MemberIffIntegerParts.At(z),
				int_construction.IntegerClosedUnderMul,
				int_construction.IntegerClosedUnderAdd))
		named := a.TermAs[Int]("int_of_real(«SquareSum»(z))")
		represented := a.Have(
			"so it is the real of the integer it names",
			"real_of_int(int_of_real(«SquareSum»(z))) = «SquareSum»(z)",
			By(integral, int_construction.IntDef.Membership))
		nonnegative := a.Have(
			"that integer is not negative, its real being a sum of squares",
			"&0 ≤ int_of_real(«SquareSum»(z))",
			ByArith(
				represented,
				int_construction.IntLeDef.At(a.TermAs[Int]("&0"), named),
				int_construction.OfNumBridge.At(a.TermAs[Nat]("0"))))
		a.Show(
			"so the norm, that integer read as a natural number, is the square sum",
			Unfold(GaussianNormDef),
			By(
				represented,
				nonnegative,
				int_embed.NumOfIntSection.At(named),
				int_construction.OfNumBridge.At(a.TermAs[Nat]("num_of_int(int_of_real(«SquareSum»(z)))"))))
	}),
})}

// NormMul — the norm is multiplicative on the Gaussian integers: read in
// ℝ, the norm of z * w is the square sum of its parts, which is the product
// of the square sums of the parts of z and of w.
var NormMul = normMulThm{family.Add(registry.ProofEntry{
	Name: "NormMul",
	Key:  "prop_b4dd80fe5e7bdd05",
	Build: family.Theorem(Statement{
		Binders: "∀z w:complex.",
		Hypotheses: []string{
			"z ∈ gaussian_integers",
			"w ∈ gaussian_integers",
		},
		Conclusion: "gaussian_norm(z * w) = gaussian_norm(z) * gaussian_norm(w)",
	}, func(a *Argument, z, w *Expr[Complex], zIn, wIn Fact) {
		product := a.TermAs[Complex]("z * w")
		productIn := a.Have(
			"ℤ[i] holds the product",
			"z * w ∈ gaussian_integers",
			By(
				zIn,
				wIn,
				GaussianSubring,
				comm_ring.SubringMul.At(
					a.TermAs[module_record.RingOps[Complex]]("complex_ring"),
					a.TermAs[Set[Complex]]("gaussian_integers"),
					z,
					w)))
		inReals := a.Have(
			"read in ℝ, the norm of z * w is the product of the norms",
			"real_of_num(gaussian_norm(z * w)) = real_of_num(gaussian_norm(z)) * real_of_num(gaussian_norm(w))",
			CalcEq(
				Leg(
					a.TermAs[Real]("re(z * w) * re(z * w) + im(z * w) * im(z * w)"),
					"the norm of z * w is the square sum of its parts",
					By(productIn, NormReal.At(product))),
				Leg(
					a.TermAs[Real]("(re(z) * re(z) + im(z) * im(z)) * (re(w) * re(w) + im(w) * im(w))"),
					"which is the product of the square sums of the factors",
					Cite(complex_field.SquareSumMul, z, w)),
				FinalLeg(
					"which are the norms of z and w",
					By(zIn, wIn, NormReal.At(z), NormReal.At(w)))))
		a.Show(
			"the embedding of ℕ in ℝ is one-to-one and keeps products",
			By(inReals, real_construction.OfNumEq, real_construction.OfNumMul))
	}),
})}

// NormZero — a Gaussian integer has norm zero exactly when it is zero: the
// norm is zero exactly when the square sum of the parts is, which is when
// both parts are.
var NormZero = normZeroThm{family.Add(registry.ProofEntry{
	Name: "NormZero",
	Key:  "prop_57b37cdc2d17bc27",
	Build: family.Theorem(Statement{
		Binders:    "∀z:complex.",
		Hypotheses: []string{"z ∈ gaussian_integers"},
		Conclusion: "gaussian_norm(z) = 0 ⇔ z = &0",
	}, func(a *Argument, z *Expr[Complex], member Fact) {
		a.Show(
			"the norm vanishes with the square sum of the parts, and that with both parts",
			By(
				member,
				NormReal.At(z),
				real_construction.OfNumEq.At(a.TermAs[Nat]("gaussian_norm(z)"), a.TermAs[Nat]("0")),
				real_order_ring.SumSquaresEqZero.At(a.TermAs[Real]("re(z)"), a.TermAs[Real]("im(z)")),
				complex_field.ComplexEq.At(z, a.TermAs[Complex]("&0")),
				complex_field.PartsOfReal))
	}),
})}

// GaussianDivision — division with remainder in ℤ[i]: a Gaussian integer
// divided by a nonzero one leaves a quotient and a remainder in ℤ[i], the
// remainder of smaller norm than the divisor. Divide in ℂ, w = a / b, and
// round both parts of w to nearest integers m and k; with q = m + ki the
// remainder r = a − q * b is (w − q) * b, whose square sum is that of
// w − q, at most a half, times that of b.
var GaussianDivision = gaussianDivisionThm{family.Add(registry.ProofEntry{
	Name: "GaussianDivision",
	Key:  "prop_745a54f72e447921",
	Build: family.Theorem(Statement{
		Binders: "∀a b:complex.",
		Hypotheses: []string{
			"a ∈ gaussian_integers",
			"b ∈ gaussian_integers",
			"b ≠ &0",
		},
		Conclusion: "∃q r:complex. " +
			"    q ∈ gaussian_integers ∧ " +
			"    r ∈ gaussian_integers ∧ " +
			"    a = q * b + r ∧ " +
			"    gaussian_norm(r) < gaussian_norm(b)",
	}, func(arg *Argument, a, b *Expr[Complex], aIn, bIn, nonzero Fact) {
		_, wDef := arg.LetAs[Complex]("w", "a / b")
		quotient := arg.Have(
			"b is nonzero, so w times b is a",
			"w * b = a",
			By(Normalized, wDef, nonzero, field.DivRightMul.Read(complex_field.Field).At(a, b)))
		_, mNear := arg.UnpackAs[Real](rational.NearestInteger.At(arg.TermAs[Real]("re(w)")), "m")
		_, kNear := arg.UnpackAs[Real](rational.NearestInteger.At(arg.TermAs[Real]("im(w)")), "k")
		q, qDef := arg.LetAs[Complex]("q", "complex(m, k)")
		qIn := arg.Have(
			"the quotient q = m + ki has integer parts",
			"q ∈ gaussian_integers",
			qDef.Rw(),
			By(mNear, kNear, MemberIffIntegerParts))
		r, rDef := arg.LetAs[Complex]("r", "a - q * b")
		complexRing := arg.TermAs[module_record.RingOps[Complex]]("complex_ring")
		gaussianIntegers := arg.TermAs[Set[Complex]]("gaussian_integers")
		product := arg.TermAs[Complex]("q * b")
		rIn := arg.Have(
			"ℤ[i] holds the remainder, a plus the negated product of q and b",
			"r ∈ gaussian_integers",
			By(
				Normalized,
				rDef,
				aIn,
				bIn,
				qIn,
				GaussianSubring,
				complex_field.ComplexSubDef.At(a, product),
				comm_ring.SubringAdd.At(complexRing, gaussianIntegers, a, arg.TermAs[Complex]("-(q * b)")),
				comm_ring.SubringNeg.At(complexRing, gaussianIntegers, product),
				comm_ring.SubringMul.At(complexRing, gaussianIntegers, q, b)))
		decomposition := arg.Have(
			"a is q times b plus the remainder",
			"a = q * b + r",
			ByArith(rDef))
		_, uDef := arg.LetAs[Complex]("u", "w - q")
		remainder := arg.Have(
			"the remainder is u times b",
			"r = u * b",
			ByArith(rDef, Scaled(b, uDef), quotient))
		quarter := arg.Have(
			"a real within a half of zero squares to at most a quarter",
			"∀t:real. |t| ≤ &1 / &2 ⇒ t * t ≤ &1 / &4",
			Derive(func(c *Argument) {
				t := c.FixAs[Real]("t")
				within := c.Assume()
				c.Show(
					"t lies between minus a half and a half",
					ByArith(within, real_sgn_abs.AbsBounds.At(t, c.TermAs[Real]("&1 / &2"))))
			}))
		near := arg.Have(
			"the parts of u are the rounding errors, so its square sum is at most a half",
			"re(u) * re(u) + im(u) * im(u) ≤ &1 / &2",
			uDef.Rw(),
			qDef.Rw(),
			Simp(
				Fwd(complex_field.ComplexSubDef),
				Fwd(complex_field.ComplexAddDef),
				Fwd(complex_field.ComplexNegDef)),
			ByArith(
				mNear,
				kNear,
				quarter.At(arg.TermAs[Real]("re(w) - m")),
				quarter.At(arg.TermAs[Real]("im(w) - k"))))
		squares := arg.Have(
			"the square sum of the parts of r is that of u times that of b",
			"re(r) * re(r) + im(r) * im(r) = (re(u) * re(u) + im(u) * im(u)) * (re(b) * re(b) + im(b) * im(b))",
			remainder.Rw(),
			Cite(complex_field.SquareSumMul))
		half := arg.Have(
			"so it is at most half the square sum of the parts of b",
			"re(r) * re(r) + im(r) * im(r) ≤ (re(b) * re(b) + im(b) * im(b)) / &2",
			ByArith(squares, near, complex_abs.SumSquaresNonneg.At(b)))
		positive := arg.Have(
			"b is nonzero, so its norm is positive",
			"0 < gaussian_norm(b)",
			ByArith(nonzero, bIn, NormZero.At(b)))
		smaller := arg.Have(
			"read in ℝ, the norm of r is below the norm of b",
			"real_of_num(gaussian_norm(r)) < real_of_num(gaussian_norm(b))",
			ByArith(positive, half, rIn, bIn, NormReal.At(r), NormReal.At(b)))
		arg.Take(q)
		arg.Take(r)
		arg.Show(
			"q and r are Gaussian integers, a = q * b + r, and r has the smaller norm",
			By(qIn, rIn, decomposition, smaller, real_order_ring.OfNumLessThan))
	}),
})}

// Euclidean — ℤ[i] is a Euclidean domain, its norm the measure.
var Euclidean = euclideanThm{family.Add(registry.ProofEntry{
	Name: "Euclidean",
	Key:  "prop_30562d8a60afa9a4",
	Build: family.Instance(euclidean_domain.EuclideanDomain,
		"euclidean_domain(gaussian_ring, gaussian_norm)",
		Case(
			"ℤ[i] is an integral domain",
			Cite(IntegralDomain)),
		Case(
			"dividing by a nonzero Gaussian integer leaves a remainder of smaller norm",
			By(GaussianDivision))),
})}

// PrincipalIdealDomain — every ideal of ℤ[i] is principal: a Euclidean
// domain is a principal ideal domain.
var PrincipalIdealDomain = principalIdealDomainThm{family.Add(registry.ProofEntry{
	Name: "PrincipalIdealDomain",
	Key:  "prop_9717f63295894b4e",
	Build: family.Theorem("principal_ideal_domain(gaussian_ring)", func(a *Argument) {
		a.Show(
			"ℤ[i] is a Euclidean domain, and a Euclidean domain is a principal ideal domain",
			Cite(euclidean_domain.PrincipalIdealDomain.Read(Euclidean)))
	}),
})}
