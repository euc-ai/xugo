// sequences.go — a sequence of complex numbers converges exactly when its
// real and imaginary parts do, each part of a difference being at most its
// modulus and the modulus at most the sum of the parts' sizes. The limit
// laws for constants, negatives, sums, products and conjugates,
// Bolzano–Weierstrass and Cauchy's criterion from Cauchy to convergent are
// then the line's theorems read on the two parts; the limits of the modulus
// and of the inverse, and the limit 0 of a sequence whose moduli a real
// sequence tending to 0 bounds, are direct ε–N arguments; and the
// uniqueness of a limit, and a convergent sequence being Cauchy, are the
// metric chapter's theorems read at the plane.

package complex_topology

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/topology/complete_metric"
	"github.com/euc-ai/xugo/library/registry"
)

// ConvergesIffParts — a sequence of complex numbers tends to l exactly
// when its real parts tend to re(l) and its imaginary parts to im(l).
// Forward, each part of a(n) − l is the difference of the parts
// (complex_field.PartsSub) and at most its modulus, so the index past which a is within
// ε of l serves both parts. Backward, past an index that puts both parts
// within ε/2 of the parts of l (real_sequences.LimitCommonIndex), the
// modulus of a(n) − l is at most the sum of the sizes of its parts
// (complex_abs.AbsLeParts), below ε.
var ConvergesIffParts = convergesIffPartsThm{family.Add(registry.ProofEntry{
	Name: "ConvergesIffParts",
	Key:  "prop_989e28254b5d3125",
	Build: family.Theorem(
		"∀a:(num → complex). ∀l:complex. a ⟶ l ⇔ (λn:num. re(a(n))) ⟶ re(l) ∧ (λn:num. im(a(n))) ⟶ im(l)",
		func(arg *Argument, a *Arrow[Nat, Complex], l *Expr[Complex]) {
			arg.Iff()
			arg.Forward(
				"each part of a(n) − l is at most its modulus, so the index that serves a serves both parts",
				func(b *Argument, converges Fact) {
					near := b.Unfolded(converges, ComplexConvergesToDef)
					tails := b.Have(
						"past the index at which a is within ε of l, both parts are within ε of the parts of l",
						"∀ε:real. &0 < ε ⇒ ∃N:num. ∀n:num. N ≤ n ⇒ |re(a(n)) - re(l)| < ε ∧ |im(a(n)) - im(l)| < ε",
						Derive(func(c *Argument) {
							eps := c.FixAs[Real]("ε")
							pos := c.Assume()
							N, tail := c.ObtainAs[Nat](
								"from some index N on, a is within ε of l",
								"∃N:num. ∀n:num. N ≤ n ⇒ |a(n) - l| < ε",
								By(near.At(eps), pos))
							c.Take(N)
							n := c.FixAs[Nat]("n")
							past := c.Assume()
							c.Show(
								"each part of a(n) − l is at most its modulus, which is below ε",
								ByArith(tail.At(n), past, complex_abs.PartsNonexpanding.At(a.Apply(n), l)))
						}))
					b.Show(
						"so each part converges to the part of l",
						By(tails, real_sequences.RealConvergesToDef))
				})
			arg.Backward(
				"past one index both parts are within ε/2 of the parts of "+
					"l, and the modulus is at most the sum of the parts' sizes",
				func(b *Argument, parts Fact) {
					b.Do(Simp(Fwd(ComplexConvergesToDef)))
					b.FixAs[Real]("ε")
					pos := b.Assume()
					half := b.TermAs[Real]("ε / &2")
					halfPos := b.Have(
						"ε/2 is positive",
						"&0 < ε / &2",
						ByArith(pos))
					N, tail := b.ObtainAs[Nat](
						"from some index N on, both parts are within ε/2 of the parts of l",
						"∃N:num. ∀n:num. N ≤ n ⇒ |re(a(n)) - re(l)| < ε / &2 ∧ |im(a(n)) - im(l)| < ε / &2",
						By(
							parts,
							halfPos,
							real_sequences.LimitCommonIndex.At(
								b.TermAs[Fun[Nat, Real]]("λn:num. re(a(n))"),
								b.TermAs[Fun[Nat, Real]]("λn:num. im(a(n))"),
								b.TermAs[Real]("re(l)"),
								b.TermAs[Real]("im(l)"),
								half)))
					b.Take(N)
					n := b.FixAs[Nat]("n")
					past := b.Assume()
					b.Show(
						"|a(n) − l| is at most the sum of the sizes of its parts, each below ε/2",
						ByArith(
							tail.At(n),
							past,
							complex_abs.AbsLeParts.At(b.TermAs[Complex]("a(n) - l")),
							complex_field.PartsSub.At(a.Apply(n), l)))
				})
		}),
})}

// LimitConst — a constant sequence tends to its value: each of its parts
// is a constant sequence of reals.
var LimitConst = limitConstThm{family.Add(registry.ProofEntry{
	Name: "LimitConst",
	Key:  "prop_66c29ae68d4db6f2",
	Build: family.Theorem("∀c:complex. (λn:num. c) ⟶ c",
		func(a *Argument, c *Expr[Complex]) {
			a.Show(
				"each part is a constant sequence of reals, which tends to its value",
				Simp(Fwd(ConvergesIffParts)),
				By(
					real_sequences.LimitConst.At(a.TermAs[Real]("re(c)")),
					real_sequences.LimitConst.At(a.TermAs[Real]("im(c)"))))
		}),
})}

// LimitNeg — the negatives of a convergent sequence tend to the negative
// of its limit: the parts of −a(n) are the negatives of the parts of a(n).
var LimitNeg = limitNegThm{family.Add(registry.ProofEntry{
	Name: "LimitNeg",
	Key:  "prop_87fffa0a2c17fe98",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → complex). ∀l:complex.",
		Hypotheses: []string{
			"a ⟶ l",
		},
		Conclusion: "(λn:num. -a(n)) ⟶ -l",
	}, func(arg *Argument, a *Arrow[Nat, Complex], l *Expr[Complex], limit Fact) {
		arg.Show(
			"the parts of −a(n) are the negated parts of a(n), which tend to the negated parts of l",
			Simp(
				Fwd(ConvergesIffParts),
				Fwd(complex_field.ComplexNegDef),
				Fwd(complex_field.ComplexReDef),
				Fwd(complex_field.ComplexImDef)),
			By(
				limit,
				ConvergesIffParts.At(a, l),
				real_sequences.LimitNeg.At(
					arg.TermAs[Fun[Nat, Real]]("λn:num. re(a(n))"), arg.TermAs[Real]("re(l)")),
				real_sequences.LimitNeg.At(
					arg.TermAs[Fun[Nat, Real]]("λn:num. im(a(n))"), arg.TermAs[Real]("im(l)"))))
	}),
})}

// LimitAdd — the termwise sum of two convergent sequences tends to the sum
// of their limits: the parts of a sum are the sums of the parts.
var LimitAdd = limitAddThm{family.Add(registry.ProofEntry{
	Name: "LimitAdd",
	Key:  "prop_392cb9bc9bdfe7cf",
	Build: family.Theorem(Statement{
		Binders: "∀a b:(num → complex). ∀l m:complex.",
		Hypotheses: []string{
			"a ⟶ l",
			"b ⟶ m",
		},
		Conclusion: "(λn:num. a(n) + b(n)) ⟶ l + m",
	}, func(arg *Argument, a, b *Arrow[Nat, Complex], l, m *Expr[Complex], aLimit, bLimit Fact) {
		arg.Show(
			"each part of a(n) + b(n) is the sum of the parts, which tends to the sum of the limits' parts",
			Simp(
				Fwd(ConvergesIffParts),
				Fwd(complex_field.ComplexAddDef),
				Fwd(complex_field.ComplexReDef),
				Fwd(complex_field.ComplexImDef)),
			By(
				aLimit,
				bLimit,
				ConvergesIffParts.At(a, l),
				ConvergesIffParts.At(b, m),
				real_sequences.LimitAdd.At(
					arg.TermAs[Fun[Nat, Real]]("λn:num. re(a(n))"),
					arg.TermAs[Fun[Nat, Real]]("λn:num. re(b(n))"),
					arg.TermAs[Real]("re(l)"),
					arg.TermAs[Real]("re(m)")),
				real_sequences.LimitAdd.At(
					arg.TermAs[Fun[Nat, Real]]("λn:num. im(a(n))"),
					arg.TermAs[Fun[Nat, Real]]("λn:num. im(b(n))"),
					arg.TermAs[Real]("im(l)"),
					arg.TermAs[Real]("im(m)"))))
	}),
})}

// LimitSub — the termwise difference of two convergent sequences tends to
// the difference of their limits: a difference is a sum with the negation,
// so a(n) − b(n) is a(n) + −b(n), which tends to l + −m.
var LimitSub = limitSubThm{family.Add(registry.ProofEntry{
	Name: "LimitSub",
	Key:  "prop_ddb5878a3f865461",
	Build: family.Theorem(Statement{
		Binders: "∀a b:(num → complex). ∀l m:complex.",
		Hypotheses: []string{
			"a ⟶ l",
			"b ⟶ m",
		},
		Conclusion: "(λn:num. a(n) - b(n)) ⟶ l - m",
	}, func(arg *Argument, a, b *Arrow[Nat, Complex], l, m *Expr[Complex], aLimit, bLimit Fact) {
		arg.Show(
			"a(n) − b(n) is a(n) + −b(n), the sum of a and the negatives of b, which tend to −m",
			Simp(Fwd(complex_field.ComplexSubDef)),
			By(
				aLimit,
				bLimit,
				LimitNeg.At(b, m),
				LimitAdd.At(a, arg.TermAs[Fun[Nat, Complex]]("λn:num. -b(n)"), l, arg.TermAs[Complex]("-m"))))
	}),
})}

// LimitMul — the termwise product of two convergent sequences tends to the
// product of their limits. The real part of a(n)·b(n) is
// re(a(n))·re(b(n)) − im(a(n))·im(b(n)) and the imaginary part
// re(a(n))·im(b(n)) + im(a(n))·re(b(n)); each of the four products of parts
// converges by the line's law for products, and their difference and sum
// by its laws for differences and sums.
var LimitMul = limitMulThm{family.Add(registry.ProofEntry{
	Name: "LimitMul",
	Key:  "prop_46cb5a27b3023548",
	Build: family.Theorem(Statement{
		Binders: "∀a b:(num → complex). ∀l m:complex.",
		Hypotheses: []string{
			"a ⟶ l",
			"b ⟶ m",
		},
		Conclusion: "(λn:num. a(n) * b(n)) ⟶ l * m",
	}, func(arg *Argument, a, b *Arrow[Nat, Complex], l, m *Expr[Complex], aLimit, bLimit Fact) {
		reA, imA :=
			arg.TermAs[Fun[Nat, Real]]("λn:num. re(a(n))"), arg.TermAs[Fun[Nat, Real]]("λn:num. im(a(n))")
		reB, imB :=
			arg.TermAs[Fun[Nat, Real]]("λn:num. re(b(n))"), arg.TermAs[Fun[Nat, Real]]("λn:num. im(b(n))")
		reL, imL := arg.TermAs[Real]("re(l)"), arg.TermAs[Real]("im(l)")
		reM, imM := arg.TermAs[Real]("re(m)"), arg.TermAs[Real]("im(m)")
		aParts := arg.Have(
			"the parts of a tend to the parts of l",
			"(λn:num. re(a(n))) ⟶ re(l) ∧ (λn:num. im(a(n))) ⟶ im(l)",
			By(aLimit, ConvergesIffParts.At(a, l)))
		bParts := arg.Have(
			"the parts of b tend to the parts of m",
			"(λn:num. re(b(n))) ⟶ re(m) ∧ (λn:num. im(b(n))) ⟶ im(m)",
			By(bLimit, ConvergesIffParts.At(b, m)))
		reRe := arg.Have(
			"re(a(n))·re(b(n)) tends to re(l)·re(m), by the line's law for products",
			"(λn:num. re(a(n)) * re(b(n))) ⟶ re(l) * re(m)",
			By(aParts, bParts, real_sequences.LimitMul.At(reA, reB, reL, reM)))
		imIm := arg.Have(
			"so does im(a(n))·im(b(n)), to im(l)·im(m)",
			"(λn:num. im(a(n)) * im(b(n))) ⟶ im(l) * im(m)",
			By(aParts, bParts, real_sequences.LimitMul.At(imA, imB, imL, imM)))
		reIm := arg.Have(
			"and re(a(n))·im(b(n)), to re(l)·im(m)",
			"(λn:num. re(a(n)) * im(b(n))) ⟶ re(l) * im(m)",
			By(aParts, bParts, real_sequences.LimitMul.At(reA, imB, reL, imM)))
		imRe := arg.Have(
			"and im(a(n))·re(b(n)), to im(l)·re(m)",
			"(λn:num. im(a(n)) * re(b(n))) ⟶ im(l) * re(m)",
			By(aParts, bParts, real_sequences.LimitMul.At(imA, reB, imL, reM)))
		arg.Show(
			"the real part of a(n)·b(n) is the difference of the first "+
				"two products, the imaginary part the sum of the last two",
			Simp(
				Fwd(ConvergesIffParts),
				Fwd(complex_field.ComplexMulDef),
				Fwd(complex_field.ComplexReDef),
				Fwd(complex_field.ComplexImDef)),
			By(
				reRe,
				imIm,
				reIm,
				imRe,
				real_sequences.LimitSub.At(
					arg.TermAs[Fun[Nat, Real]]("λn:num. re(a(n)) * re(b(n))"),
					arg.TermAs[Fun[Nat, Real]]("λn:num. im(a(n)) * im(b(n))"),
					arg.TermAs[Real]("re(l) * re(m)"),
					arg.TermAs[Real]("im(l) * im(m)")),
				real_sequences.LimitAdd.At(
					arg.TermAs[Fun[Nat, Real]]("λn:num. re(a(n)) * im(b(n))"),
					arg.TermAs[Fun[Nat, Real]]("λn:num. im(a(n)) * re(b(n))"),
					arg.TermAs[Real]("re(l) * im(m)"),
					arg.TermAs[Real]("im(l) * re(m)"))))
	}),
})}

// LimitConj — the conjugates of a convergent sequence tend to the
// conjugate of its limit: conjugation keeps the real part and negates the
// imaginary part.
var LimitConj = limitConjThm{family.Add(registry.ProofEntry{
	Name: "LimitConj",
	Key:  "prop_4394761ed704b112",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → complex). ∀l:complex.",
		Hypotheses: []string{
			"a ⟶ l",
		},
		Conclusion: "(λn:num. conj(a(n))) ⟶ conj(l)",
	}, func(arg *Argument, a *Arrow[Nat, Complex], l *Expr[Complex], limit Fact) {
		arg.Show(
			"the real parts are unchanged, and the negated imaginary parts tend to −im(l)",
			Simp(
				Fwd(ConvergesIffParts),
				Fwd(complex_field.ComplexConjDef),
				Fwd(complex_field.ComplexReDef),
				Fwd(complex_field.ComplexImDef)),
			By(
				limit,
				ConvergesIffParts.At(a, l),
				real_sequences.LimitNeg.At(
					arg.TermAs[Fun[Nat, Real]]("λn:num. im(a(n))"), arg.TermAs[Real]("im(l)"))))
	}),
})}

// LimitUnique — a sequence of complex numbers has at most one limit: a
// limit in the plane is a limit in the metric space the plane is under its
// distance (ConvergesIffMetric), and there a sequence converges to at most
// one point.
var LimitUnique = limitUniqueThm{family.Add(registry.ProofEntry{
	Name: "LimitUnique",
	Key:  "prop_acce0245372c0e95",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → complex). ∀l m:complex.",
		Hypotheses: []string{
			"a ⟶ l",
			"a ⟶ m",
		},
		Conclusion: "l = m",
	}, func(arg *Argument, a *Arrow[Nat, Complex], l, m *Expr[Complex], toL, toM Fact) {
		arg.Show(
			"a converges to l and to m in the metric space of the plane, where a sequence has one limit",
			By(
				toL,
				toM,
				ConvergesIffMetric.At(a, l),
				ConvergesIffMetric.At(a, m),
				complete_metric.LimitUnique.Read(ComplexMetric).At(a, l, m)))
	}),
})}

// LimitOfReal — a sequence of reals, seen in ℂ, tends to a real l exactly
// when it tends to l on the line: its real parts are the sequence itself
// and its imaginary parts are zeros, which tend to zero.
var LimitOfReal = limitOfRealThm{family.Add(registry.ProofEntry{
	Name: "LimitOfReal",
	Key:  "prop_7968e1341924ec40",
	Build: family.Theorem("∀x:(num → real). ∀l:real. (λn:num. &(x(n))) ⟶ &l ⇔ x ⟶ l",
		func(a *Argument, x *Arrow[Nat, Real], l *Expr[Real]) {
			a.Show(
				"the real parts are x and l, and the imaginary parts are zeros tending to zero",
				Simp(
					Fwd(ConvergesIffParts),
					Fwd(complex_field.ComplexOfRealDef),
					Fwd(complex_field.ComplexReDef),
					Fwd(complex_field.ComplexImDef)),
				By(real_sequences.LimitConst.At(a.TermAs[Real]("&0"))))
		}),
})}

// LimitAbs — the moduli of a convergent sequence tend to the modulus of
// its limit: two moduli differ by at most the modulus of the difference
// (complex_abs.AbsTriangleReverse), so the index past which a is within ε
// of l serves the moduli.
var LimitAbs = limitAbsThm{family.Add(registry.ProofEntry{
	Name: "LimitAbs",
	Key:  "prop_edee714772fd418a",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → complex). ∀l:complex.",
		Hypotheses: []string{
			"a ⟶ l",
		},
		Conclusion: "(λn:num. |a(n)|) ⟶ |l|",
	}, func(arg *Argument, a *Arrow[Nat, Complex], l *Expr[Complex], limit Fact) {
		near := arg.Unfolded(limit, ComplexConvergesToDef)
		arg.Do(Unfold(real_sequences.RealConvergesToDef))
		eps := arg.FixAs[Real]("ε")
		pos := arg.Assume()
		N, tail := arg.ObtainAs[Nat](
			"from some index N on, a is within ε of l",
			"∃N:num. ∀n:num. N ≤ n ⇒ |a(n) - l| < ε",
			By(near.At(eps), pos))
		arg.Take(N)
		n := arg.FixAs[Nat]("n")
		past := arg.Assume()
		arg.Show(
			"||a(n)| − |l|| is at most |a(n) − l|, which is below ε",
			ByArith(tail.At(n), past, complex_abs.AbsTriangleReverse.At(a.Apply(n), l)))
	}),
})}

// LimitSqueezeZero — a sequence of complex numbers whose moduli are at
// most the terms of a real sequence tending to 0 tends to 0 itself: the
// index past which b is within ε of 0 serves a, the distance of a(n) from
// 0 being its modulus, at most b(n).
var LimitSqueezeZero = limitSqueezeZeroThm{family.Add(registry.ProofEntry{
	Name: "LimitSqueezeZero",
	Key:  "prop_824d8601b302912e",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → complex). ∀b:(num → real).",
		Hypotheses: []string{
			"∀n:num. |a(n)| ≤ b(n)",
			"b ⟶ &0",
		},
		Conclusion: "a ⟶ complex_of_real(&0)",
	}, func(arg *Argument, a *Arrow[Nat, Complex], b *Arrow[Nat, Real], bounded, vanishing Fact) {
		near := arg.Unfolded(vanishing, real_sequences.RealConvergesToDef)
		arg.Do(Unfold(ComplexConvergesToDef))
		eps := arg.FixAs[Real]("ε")
		pos := arg.Assume()
		N, tail := arg.ObtainAs[Nat](
			"from some index N on, b is within ε of 0",
			"∃N:num. ∀n:num. N ≤ n ⇒ |b(n) - &0| < ε",
			By(near.At(eps), pos))
		arg.Take(N)
		n := arg.FixAs[Nat]("n")
		past := arg.Assume()
		removeZero := arg.Have(
			"the distance of a(n) from 0 is a(n) itself",
			"a(n) - complex_of_real(&0) = a(n)",
			ByArith())
		arg.Show(
			"so its modulus is |a(n)|, at most b(n), which is below ε",
			ByArith(tail.At(n), past, bounded.At(n), removeZero))
	}),
})}

// InvEstimate — near a nonzero l the inverse is near the inverse of l: a
// number u larger than |l|/2 in modulus and within ε·|l|·|l|/2 of l has its
// inverse within ε of the inverse of l. Neither u nor l is zero, and the
// difference of the inverses, multiplied by u·l, is −(u − l), so
// |1/u − 1/l| = |u − l| / (|u|·|l|), which the two bounds make less than ε.
var InvEstimate = invEstimateThm{family.Add(registry.ProofEntry{
	Name: "InvEstimate",
	Key:  "prop_f90d046b0d0cd58e",
	Build: family.Theorem(Statement{
		Binders: "∀u l:complex. ∀ε:real.",
		Hypotheses: []string{
			"&0 < ε",
			"l ≠ &0",
			"|l| / &2 < |u|",
			"|u - l| < ε * |l| * |l| / &2",
		},
		Conclusion: "|complex_inv(u) - complex_inv(l)| < ε",
	}, func(s *Argument, u, l *Expr[Complex], ε *Expr[Real], pos, nonzero, large, close Fact) {
		difference := s.TermAs[Complex]("complex_inv(u) - complex_inv(l)")
		lPos := s.Have(
			"l is not zero, so |l| is positive",
			"&0 < |l|",
			By(nonzero, complex_abs.AbsPosIffNonzero.At(l)))
		uPos := s.Have(
			"|u| exceeds |l|/2, so it is positive too",
			"&0 < |u|",
			ByArith(lPos, large))
		uNonzero := s.Have(
			"so u is not zero",
			"u ≠ &0",
			By(uPos, complex_abs.AbsPosIffNonzero.At(u)))
		inverse := field.MulRightInverse.Read(complex_field.Field)
		identity := s.Have(
			"neither u nor l is zero, so the difference of the inverses, multiplied by u·l, is −(u − l)",
			"(complex_inv(u) - complex_inv(l)) * (u * l) = -(u - l)",
			ByArith(uNonzero, nonzero, Scaled(l, inverse.At(u)), Scaled(u, inverse.At(l))))
		distance := s.Have(
			"taking moduli: |1/u − 1/l|·(|u|·|l|) = |u − l|",
			"|complex_inv(u) - complex_inv(l)| * (|u| * |l|) = |u - l|",
			By(
				identity,
				complex_abs.AbsMul.At(difference, s.TermAs[Complex]("u * l")),
				complex_abs.AbsMul.At(u, l),
				complex_abs.AbsNeg.At(s.TermAs[Complex]("u - l"))))
		scaled := s.Have(
			"|u − l| < ε·|l|·|l|/2 < ε·(|u|·|l|), since |l| < 2|u|",
			"|u - l| < ε * (|u| * |l|)",
			ByArith(
				real_order_ring.LessThanMulLeft.At(
					s.TermAs[Real]("ε * |l|"), s.TermAs[Real]("|l|"), s.TermAs[Real]("&2 * |u|")),
				lPos,
				pos,
				large,
				close))
		s.Show(
			"so |1/u − 1/l|·(|u|·|l|) < ε·(|u|·|l|), and the positive factor |u|·|l| cancels",
			ByArith(
				real_order_ring.LessThanCancelMulRight.At(
					s.TermAs[Real]("|complex_inv(u) - complex_inv(l)|"), ε, s.TermAs[Real]("|u| * |l|")),
				distance,
				scaled,
				lPos,
				uPos))
	}),
})}

// LimitInv — the inverses of a sequence with a nonzero limit tend to the
// inverse of the limit. Past one index the terms are within |l|/2 of l, so
// their moduli exceed |l|/2; past another they are within the tolerance
// ε·|l|·|l|/2 of l. Past both, the estimate on the inverse (InvEstimate)
// puts 1/a(n) within ε of 1/l.
var LimitInv = limitInvThm{family.Add(registry.ProofEntry{
	Name: "LimitInv",
	Key:  "prop_6b633ba0a59be7d9",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → complex). ∀l:complex.",
		Hypotheses: []string{
			"a ⟶ l",
			"l ≠ &0",
		},
		Conclusion: "(λn:num. complex_inv(a(n))) ⟶ complex_inv(l)",
	}, func(arg *Argument, a *Arrow[Nat, Complex], l *Expr[Complex], limit, nonzero Fact) {
		lPos := arg.Have(
			"l is not zero, so |l| is positive",
			"&0 < |l|",
			By(nonzero, complex_abs.AbsPosIffNonzero.At(l)))
		near := arg.Unfolded(limit, ComplexConvergesToDef)
		halfPos := arg.Have(
			"half of |l| is positive",
			"&0 < |l| / &2",
			ByArith(lPos))
		_, away := arg.ObtainAs[Nat](
			"past some index N₁ the terms are within |l|/2 of l",
			"∃N:num. ∀n:num. N ≤ n ⇒ |a(n) - l| < |l| / &2",
			By(near.At(arg.TermAs[Real]("|l| / &2")), halfPos),
			Named("N₁"))
		arg.Do(Unfold(ComplexConvergesToDef))
		eps := arg.FixAs[Real]("ε")
		pos := arg.Assume()
		tolPos := arg.Have(
			"the tolerance ε·|l|·|l|/2 is positive",
			"&0 < ε * |l| * |l| / &2",
			ByArith(pos, lPos))
		_, within := arg.ObtainAs[Nat](
			"past some index N₂ the terms are within that tolerance of l",
			"∃N:num. ∀n:num. N ≤ n ⇒ |a(n) - l| < ε * |l| * |l| / &2",
			By(near.At(arg.TermAs[Real]("ε * |l| * |l| / &2")), tolPos),
			Named("N₂"))
		arg.Take(arg.TermAs[Nat]("N₁ + N₂"))
		n := arg.FixAs[Nat]("n")
		past := arg.Assume()
		pastBoth := arg.Have(
			"n lies past both indices",
			"N₁ ≤ n ∧ N₂ ≤ n",
			ByArith(past))
		term := a.Apply(n)
		large := arg.Have(
			"|a(n)| exceeds |l|/2: |l| ≤ |a(n)| + |a(n) − l|, the second below |l|/2",
			"|l| / &2 < |a(n)|",
			ByArith(away.At(n), pastBoth, complex_abs.AbsTriangleReverse.At(term, l)))
		arg.Show(
			"the estimate on the inverse at a(n) puts its inverse within ε of the inverse of l",
			By(InvEstimate.At(term, l, eps), pos, nonzero, large, within.At(n), pastBoth))
	}),
})}

// CauchyIffConvergent — Cauchy's criterion in the plane: a sequence of
// complex numbers converges exactly when its terms end up within any
// positive distance of each other. Forward, each part of a(m) − a(n) is at
// most its modulus, so both parts are Cauchy sequences of reals; they
// converge on the line, to x and y, and the sequence converges to the
// number with parts x and y (ConvergesIffParts). Backward, a convergent
// sequence converges in the metric space (ConvergesIffMetric), so it is
// Cauchy for the distance, which is the modulus of the difference.
var CauchyIffConvergent = cauchyIffConvergentThm{family.Add(registry.ProofEntry{
	Name: "CauchyIffConvergent",
	Key:  "prop_a57958c9495498fc",
	Build: family.Theorem(
		"∀a:(num → complex). "+
			"    (∀ε:real. &0 < ε ⇒ ∃N:num. ∀m n:num. N ≤ m ∧ N ≤ n ⇒ |a(m) - a(n)| < ε) ⇔ ∃l:complex. a ⟶ l",
		func(arg *Argument, a *Arrow[Nat, Complex]) {
			arg.Iff()
			arg.Forward(
				"both parts are Cauchy, so they converge, and the "+
					"number with their limits as its parts is the limit",
				func(b *Argument, cauchy Fact) {
					reA, imA :=
						b.TermAs[Fun[Nat, Real]]("λn:num. re(a(n))"), b.TermAs[Fun[Nat, Real]]("λn:num. im(a(n))")
					together := b.Have(
						"past the index at which the terms are within ε of each other, so are their parts",
						Statement{
							Binders: "∀ε:real.",
							Hypotheses: []string{
								"&0 < ε",
							},
							Conclusion: "∃N:num. ∀m n:num. " +
								"    N ≤ m ∧ N ≤ n ⇒ |re(a(m)) - re(a(n))| < ε ∧ |im(a(m)) - im(a(n))| < ε",
						},
						Derive(func(c *Argument) {
							eps := c.FixAs[Real]("ε")
							pos := c.Assume()
							N, tail := c.ObtainAs[Nat](
								"from some index N on, any two terms are within ε of each other",
								"∃N:num. ∀m n:num. N ≤ m ∧ N ≤ n ⇒ |a(m) - a(n)| < ε",
								By(cauchy.At(eps), pos))
							c.Take(N)
							m := c.FixAs[Nat]("m")
							n := c.FixAs[Nat]("n")
							past := c.Assume()
							c.Show(
								"each part of a(m) − a(n) is at most its modulus, which is below ε",
								ByArith(tail.At(m, n), past, complex_abs.PartsNonexpanding.At(a.Apply(m), a.Apply(n))))
						}))
					partsCauchy := b.Have(
						"so both parts are Cauchy sequences of reals",
						"real_cauchy(λn:num. re(a(n))) ∧ real_cauchy(λn:num. im(a(n)))",
						By(together, real_sequences.RealCauchyDef))
					_, reLimit := b.ObtainAs[Real](
						"the real parts converge, by Cauchy's criterion on the line, to some x",
						"∃x:real. (λn:num. re(a(n))) ⟶ x",
						By(partsCauchy, real_sequences.CauchyIffConvergent.At(reA)),
						Named("x"))
					_, imLimit := b.ObtainAs[Real](
						"and the imaginary parts to some y",
						"∃y:real. (λn:num. im(a(n))) ⟶ y",
						By(partsCauchy, real_sequences.CauchyIffConvergent.At(imA)),
						Named("y"))
					b.Take(b.TermAs[Complex]("complex(x, y)"))
					b.Show(
						"complex(x, y) has parts x and y, the limits of the parts",
						Simp(Fwd(ConvergesIffParts), Fwd(complex_field.ComplexReDef), Fwd(complex_field.ComplexImDef)),
						By(reLimit, imLimit))
				})
			arg.Backward(
				"a convergent sequence is Cauchy for the distance, which is the modulus of the difference",
				func(b *Argument, convergent Fact) {
					l, limit := b.UnpackAs[Complex](convergent, "l")
					cauchy := b.Have(
						"a converges to l in the metric space, so it is Cauchy for the distance",
						"metric_cauchy(𝕌, complex_dist, a)",
						By(limit, ConvergesIffMetric.At(a, l), complete_metric.ConvergentImpCauchy.Read(ComplexMetric)))
					b.Show(
						"the distance of two terms is the modulus of their difference",
						Simp(Rev(ComplexDistDef)),
						By(b.Unfolded(cauchy, complete_metric.MetricCauchyDef)))
				})
		}),
})}

// BolzanoWeierstrass — a bounded sequence of complex numbers has a
// convergent subsequence. Each part of a term is at most its modulus, so
// the real parts are bounded and Bolzano–Weierstrass on the line thins
// them along σ to a limit x; the imaginary parts along σ are bounded too
// and thin along τ to a limit y. Along σ ∘ τ the real parts still tend to
// x, a subsequence of a convergent sequence
// (real_sequences.LimitSubsequence), so both parts converge and the
// sequence tends to the number with parts x and y (ConvergesIffParts).
// σ ∘ τ rises strictly because σ, rising one step at a time, rises
// between any two indices (nat_order.LessThanStrictlyIncreasing).
var BolzanoWeierstrass = bolzanoWeierstrassThm{family.Add(registry.ProofEntry{
	Name: "BolzanoWeierstrass",
	Key:  "prop_cf18ff5f8d8f40af",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → complex). ∀B:real.",
		Hypotheses: []string{
			"∀n:num. |a(n)| ≤ B",
		},
		Conclusion: "∃σ:(num → num). ∃l:complex. (∀j:num. σ(j) < σ(j + 1)) ∧ a ∘ σ ⟶ l",
	}, func(arg *Argument, a *Arrow[Nat, Complex], B *Expr[Real], bounded Fact) {
		reBounded := arg.Have(
			"the real parts are bounded by B, a part being at most the modulus",
			"∀n:num. |re(a(n))| ≤ B",
			arg.ForEach(func(n *Expr[Nat]) Action {
				return ByArith(bounded.At(n), complex_abs.ReLessEqAbs.At(a.Apply(n)))
			}))
		_, x, thinned := arg.Obtain2As[Fun[Nat, Nat], Real](
			"by Bolzano–Weierstrass on the line, the real parts have a subsequence tending to some x",
			"∃σ:(num → num). ∃x:real. (∀j:num. σ(j) < σ(j + 1)) ∧ (λn:num. re(a(n))) ∘ σ ⟶ x",
			By(
				reBounded,
				real_sequences.BolzanoWeierstrass.At(arg.TermAs[Fun[Nat, Real]]("λn:num. re(a(n))"), B)),
			Named("σ", "x"))
		first := arg.Conjuncts(
			thinned,
			"σ rises strictly",
			"and the real parts along σ tend to x")
		σRises, reConverges := first[0], first[1]
		imBounded := arg.Have(
			"the imaginary parts along σ are bounded by B as well",
			"∀j:num. |im(a(σ(j)))| ≤ B",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("j")
				b.Show(
					"an imaginary part is at most the modulus",
					ByArith(
						bounded.At(b.TermAs[Nat]("σ(j)")),
						complex_abs.ImLessEqAbs.At(b.TermAs[Complex]("a(σ(j))"))))
			}))
		τ, _, thinnedAgain := arg.Obtain2As[Fun[Nat, Nat], Real](
			"and thin along some τ to a limit y",
			"∃τ:(num → num). ∃y:real. (∀j:num. τ(j) < τ(j + 1)) ∧ (λj:num. im(a(σ(j)))) ∘ τ ⟶ y",
			By(
				imBounded,
				real_sequences.BolzanoWeierstrass.At(arg.TermAs[Fun[Nat, Real]]("λj:num. im(a(σ(j)))"), B)),
			Named("τ", "y"))
		second := arg.Conjuncts(
			thinnedAgain,
			"τ rises strictly",
			"and the imaginary parts along σ ∘ τ tend to y")
		τRises, imConverges := second[0], second[1]
		composite := arg.Have(
			"σ ∘ τ rises strictly, σ rising between any two indices",
			"∀j:num. σ(τ(j)) < σ(τ(j + 1))",
			By(σRises, τRises, nat_order.LessThanStrictlyIncreasing))
		reAlong := arg.Have(
			"along σ ∘ τ the real parts still tend to x, a subsequence of a convergent sequence",
			"(λj:num. re(a(σ(τ(j))))) ⟶ x",
			By(
				reConverges,
				τRises,
				real_sequences.LimitSubsequence.At(
					arg.TermAs[Fun[Nat, Real]]("(λn:num. re(a(n))) ∘ σ"),
					τ,
					x),
				functions.ComposeApply))
		imAlong := arg.Simplified(imConverges, Fwd(functions.ComposeApply))
		arg.Take(arg.TermAs[Fun[Nat, Nat]]("σ ∘ τ"))
		arg.Take(arg.TermAs[Complex]("complex(x, y)"))
		arg.Show(
			"σ ∘ τ rises strictly, and along it both parts of a converge, to the parts of complex(x, y)",
			Simp(
				Fwd(ConvergesIffParts),
				Fwd(functions.ComposeApply),
				Fwd(complex_field.ComplexReDef),
				Fwd(complex_field.ComplexImDef)),
			By(composite, reAlong, imAlong))
	}),
})}
