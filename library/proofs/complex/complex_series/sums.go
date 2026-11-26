// sums.go — the laws of complex series: uniqueness, sums, multiples,
// pairing, real series, and absolute convergence, each the series
// chapter's law read on the two parts; and the partial sums, which tend
// to the sum.

package complex_series

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_topology"
	"github.com/euc-ai/xugo/library/proofs/real/real_series"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/registry"
)

// SumsUnique — a series has only one sum: each of its parts has one,
// and a complex number is its parts.
var SumsUnique = sumsUniqueThm{family.Add(registry.ProofEntry{
	Name: "SumsUnique",
	Key:  "prop_a9b79b6fb5ccf38f",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → complex). ∀s t:complex.",
		Hypotheses: []string{
			"complex_sums(a, s)",
			"complex_sums(a, t)",
		},
		Conclusion: "s = t",
	},
		func(arg *Argument, a *Arrow[Nat, Complex], s, t *Expr[Complex], sums Fact) {
			both := arg.Conjuncts(
				sums,
				"a sums to s",
				"and to t")
			toS := arg.Conjuncts(
				arg.Have(
					"the parts of a sum to those of s",
					"real_sums(λn:num. re(a(n)), re(s)) ∧ real_sums(λn:num. im(a(n)), im(s))",
					By(both[0], ComplexSumsDef)),
				"the real parts sum to re(s)",
				"the imaginary parts to im(s)")
			toT := arg.Conjuncts(
				arg.Have(
					"and to those of t",
					"real_sums(λn:num. re(a(n)), re(t)) ∧ real_sums(λn:num. im(a(n)), im(t))",
					By(both[1], ComplexSumsDef)),
				"the real parts sum to re(t)",
				"the imaginary parts to im(t)")
			reEq := arg.Have(
				"the real parts have one sum",
				"re(s) = re(t)",
				By(toS[0], toT[0], real_series.SumsUnique))
			imEq := arg.Have(
				"and so do the imaginary parts",
				"im(s) = im(t)",
				By(toS[1], toT[1], real_series.SumsUnique))
			arg.Show(
				"a complex number is its parts",
				Simp(complex_field.Parts),
				By(reEq, imEq))
		}),
})}

// SumsAdd — two series added term by term sum to the sum of their sums:
// the parts of a sum are the sums of the parts.
var SumsAdd = sumsAddThm{family.Add(registry.ProofEntry{
	Name: "SumsAdd",
	Key:  "prop_e428c946c252ed56",
	Build: family.Theorem(Statement{
		Binders: "∀a b:(num → complex). ∀s t:complex.",
		Hypotheses: []string{
			"complex_sums(a, s)",
			"complex_sums(b, t)",
		},
		Conclusion: "complex_sums(λn:num. a(n) + b(n), s + t)",
	},
		func(arg *Argument, a, b *Arrow[Nat, Complex], s, t *Expr[Complex], sums Fact) {
			both := arg.Conjuncts(
				sums,
				"a sums to s",
				"b sums to t")
			toS := arg.Conjuncts(
				arg.Have(
					"the parts of a sum to those of s",
					"real_sums(λn:num. re(a(n)), re(s)) ∧ real_sums(λn:num. im(a(n)), im(s))",
					By(both[0], ComplexSumsDef)),
				"the real parts of a sum to re(s)",
				"the imaginary parts to im(s)")
			toT := arg.Conjuncts(
				arg.Have(
					"the parts of b sum to those of t",
					"real_sums(λn:num. re(b(n)), re(t)) ∧ real_sums(λn:num. im(b(n)), im(t))",
					By(both[1], ComplexSumsDef)),
				"the real parts of b sum to re(t)",
				"the imaginary parts to im(t)")
			reSum := arg.Have(
				"the real parts add",
				"real_sums(λn:num. re(a(n)) + re(b(n)), re(s) + re(t))",
				By(toS[0], toT[0], real_series.SumsAdd))
			imSum := arg.Have(
				"and so do the imaginary parts",
				"real_sums(λn:num. im(a(n)) + im(b(n)), im(s) + im(t))",
				By(toS[1], toT[1], real_series.SumsAdd))
			arg.Show(
				"which are the parts of the sum, term by term and of the sums",
				Simp(Fwd(ComplexSumsDef), Fwd(complex_field.PartsAdd)),
				By(reSum, imSum))
		}),
})}

// SumsSub — two series subtracted term by term sum to the difference of
// their sums: the parts subtract.
var SumsSub = sumsSubThm{family.Add(registry.ProofEntry{
	Name: "SumsSub",
	Key:  "prop_30ea13ce956e5804",
	Build: family.Theorem(Statement{
		Binders: "∀a b:(num → complex). ∀s t:complex.",
		Hypotheses: []string{
			"complex_sums(a, s)",
			"complex_sums(b, t)",
		},
		Conclusion: "complex_sums(λn:num. a(n) - b(n), s - t)",
	},
		func(arg *Argument, a, b *Arrow[Nat, Complex], s, t *Expr[Complex], sums Fact) {
			both := arg.Conjuncts(
				sums,
				"a sums to s",
				"b sums to t")
			toS := arg.Conjuncts(
				arg.Have(
					"the parts of a sum to those of s",
					"real_sums(λn:num. re(a(n)), re(s)) ∧ real_sums(λn:num. im(a(n)), im(s))",
					By(both[0], ComplexSumsDef)),
				"the real parts of a sum to re(s)",
				"the imaginary parts to im(s)")
			toT := arg.Conjuncts(
				arg.Have(
					"the parts of b sum to those of t",
					"real_sums(λn:num. re(b(n)), re(t)) ∧ real_sums(λn:num. im(b(n)), im(t))",
					By(both[1], ComplexSumsDef)),
				"the real parts of b sum to re(t)",
				"the imaginary parts to im(t)")
			reDiff := arg.Have(
				"the real parts subtract",
				"real_sums(λn:num. re(a(n)) - re(b(n)), re(s) - re(t))",
				By(toS[0], toT[0], real_series.SumsSub))
			imDiff := arg.Have(
				"and so do the imaginary parts",
				"real_sums(λn:num. im(a(n)) - im(b(n)), im(s) - im(t))",
				By(toS[1], toT[1], real_series.SumsSub))
			arg.Show(
				"which are the parts of the difference, term by term and of the sums",
				Simp(Fwd(ComplexSumsDef), Fwd(complex_field.PartsSub)),
				By(reDiff, imDiff))
		}),
})}

// SumsScale — a series multiplied term by term by c sums to c times
// its sum. The real part of c·a(n) is re(c)·re(a(n)) − im(c)·im(a(n)),
// and the imaginary part re(c)·im(a(n)) + im(c)·re(a(n)): each part is a
// combination of the two real series with constant coefficients.
var SumsScale = sumsScaleThm{family.Add(registry.ProofEntry{
	Name: "SumsScale",
	Key:  "prop_7f3478415aecbc35",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → complex). ∀s c:complex.",
		Hypotheses: []string{
			"complex_sums(a, s)",
		},
		Conclusion: "complex_sums(λn:num. c * a(n), c * s)",
	},
		func(arg *Argument, a *Arrow[Nat, Complex], s, c *Expr[Complex], sums Fact) {
			toS := arg.Have(
				"the parts of a sum to those of s",
				"real_sums(λn:num. re(a(n)), re(s)) ∧ real_sums(λn:num. im(a(n)), im(s))",
				By(sums, ComplexSumsDef))
			parts := arg.Conjuncts(
				toS,
				"the real parts sum to re(s)",
				"the imaginary parts to im(s)")
			reRe := arg.Have(
				"re(c) times the real parts",
				"real_sums(λn:num. re(c) * re(a(n)), re(c) * re(s))",
				By(parts[0], real_series.SumsScale))
			imIm := arg.Have(
				"im(c) times the imaginary parts",
				"real_sums(λn:num. im(c) * im(a(n)), im(c) * im(s))",
				By(parts[1], real_series.SumsScale))
			reIm := arg.Have(
				"re(c) times the imaginary parts",
				"real_sums(λn:num. re(c) * im(a(n)), re(c) * im(s))",
				By(parts[1], real_series.SumsScale))
			imRe := arg.Have(
				"im(c) times the real parts",
				"real_sums(λn:num. im(c) * re(a(n)), im(c) * re(s))",
				By(parts[0], real_series.SumsScale))
			reProduct := arg.Have(
				"so the real parts of the products, re(c)·re(a(n)) "+
					"− im(c)·im(a(n)), sum to re(c)·re(s) − im(c)·im(s)",
				"real_sums(λn:num. re(c) * re(a(n)) - im(c) * im(a(n)), re(c) * re(s) - im(c) * im(s))",
				By(reRe, imIm, real_series.SumsSub))
			imProduct := arg.Have(
				"and the imaginary parts, re(c)·im(a(n)) + im(c)·re(a(n)), to re(c)·im(s) + im(c)·re(s)",
				"real_sums(λn:num. re(c) * im(a(n)) + im(c) * re(a(n)), re(c) * im(s) + im(c) * re(s))",
				By(reIm, imRe, real_series.SumsAdd))
			arg.Show(
				"which are the parts of c·a(n) and of c·s",
				Simp(Fwd(ComplexSumsDef), Fwd(complex_field.PartsMul)),
				By(reProduct, imProduct))
		}),
})}

// SumsPair — a series taken two terms at a time sums to the same sum:
// each part does.
var SumsPair = sumsPairThm{family.Add(registry.ProofEntry{
	Name: "SumsPair",
	Key:  "prop_1d65d30478cc9e71",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → complex). ∀s:complex.",
		Hypotheses: []string{
			"complex_sums(a, s)",
		},
		Conclusion: "complex_sums(λn:num. a(2 * n) + a(2 * n + 1), s)",
	},
		func(arg *Argument, a *Arrow[Nat, Complex], s *Expr[Complex], sums Fact) {
			toS := arg.Conjuncts(
				arg.Have(
					"the parts of a sum to those of s",
					"real_sums(λn:num. re(a(n)), re(s)) ∧ real_sums(λn:num. im(a(n)), im(s))",
					By(sums, ComplexSumsDef)),
				"the real parts sum to re(s)",
				"the imaginary parts to im(s)")
			rePair := arg.Have(
				"the real parts, taken two at a time, sum to re(s)",
				"real_sums(λn:num. re(a(2 * n)) + re(a(2 * n + 1)), re(s))",
				By(toS[0], real_series.SumsPair))
			imPair := arg.Have(
				"and so do the imaginary parts, to im(s)",
				"real_sums(λn:num. im(a(2 * n)) + im(a(2 * n + 1)), im(s))",
				By(toS[1], real_series.SumsPair))
			arg.Show(
				"which are the parts of the paired series",
				Simp(Fwd(ComplexSumsDef), Fwd(complex_field.PartsAdd)),
				By(rePair, imPair))
		}),
})}

// SumsOfReal — on real terms a complex series is the real one: its real
// parts are the terms and its imaginary parts are zero, which sum to 0.
var SumsOfReal = sumsOfRealThm{family.Add(registry.ProofEntry{
	Name: "SumsOfReal",
	Key:  "prop_3a0cce1b8d6cf6e1",
	Build: family.Theorem(
		"∀a:(num → real). ∀s:real. "+
			"    complex_sums(λn:num. complex_of_real(a(n)), complex_of_real(s)) ⇔ real_sums(a, s)",
		Chain(Simp(Fwd(ComplexSumsDef), Fwd(complex_field.PartsOfReal)), By(real_series.SumsZero))),
})}

// AbsoluteConvergence — a series whose sizes have a sum has a sum. The
// size of a term bounds the size of each of its parts, so each part
// converges by comparison with the sizes; the number with those two
// sums as its parts is the series' sum.
var AbsoluteConvergence = absoluteConvergenceThm{family.Add(registry.ProofEntry{
	Name: "AbsoluteConvergence",
	Key:  "prop_c8f91d82921be991",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → complex). ∀t:real.",
		Hypotheses: []string{
			"real_sums(λn:num. |a(n)|, t)",
		},
		Conclusion: "∃s:complex. complex_sums(a, s)",
	},
		func(arg *Argument, a *Arrow[Nat, Complex], t *Expr[Real], sizes Fact) {
			zero := arg.TermAs[Nat]("0")
			terms := arg.TermAs[Fun[Nat, Real]]("λn:num. |a(n)|")
			reBound := arg.Have(
				"the real part of each term is at most the term's size",
				"∀n:num. 0 ≤ n ⇒ |re(a(n))| ≤ |a(n)|",
				arg.ForEach(func(n *Expr[Nat]) Action { return By(complex_abs.ReLessEqAbs.At(a.Apply(n))) }))
			imBound := arg.Have(
				"and so is the imaginary part",
				"∀n:num. 0 ≤ n ⇒ |im(a(n))| ≤ |a(n)|",
				arg.ForEach(func(n *Expr[Nat]) Action { return By(complex_abs.ImLessEqAbs.At(a.Apply(n))) }))
			_, reSums := arg.ObtainAs[Real](
				"so the real parts have a sum u, by comparison with the sizes",
				"∃u:real. real_sums(λn:num. re(a(n)), u)",
				By(
					reBound,
					sizes,
					real_series.Comparison.At(arg.TermAs[Fun[Nat, Real]]("λn:num. re(a(n))"), terms, t, zero)))
			_, imSums := arg.ObtainAs[Real](
				"and the imaginary parts a sum v",
				"∃v:real. real_sums(λn:num. im(a(n)), v)",
				By(
					imBound,
					sizes,
					real_series.Comparison.At(arg.TermAs[Fun[Nat, Real]]("λn:num. im(a(n))"), terms, t, zero)))
			sum := arg.Have(
				"the number with parts u and v is a sum of the series",
				"complex_sums(a, complex(u, v))",
				Simp(Fwd(ComplexSumsDef)),
				By(reSums, imSums))
			arg.Show(
				"so the series has a sum",
				By(Normalized, sum))
		}),
})}

// SumsShift — dropping the first term of a series drops it from the sum,
// and conversely: each part does so.
var SumsShift = sumsShiftThm{family.Add(registry.ProofEntry{
	Name: "SumsShift",
	Key:  "prop_6448d6b5cf7b3fb",
	Build: family.Theorem("∀a:(num → complex). ∀s:complex. "+
		"    complex_sums(a, s) ⇔ complex_sums(λn:num. a(n + 1), s - a(0))",
		func(arg *Argument, a *Arrow[Nat, Complex], s *Expr[Complex]) {
			arg.Show(
				"the real parts and the imaginary parts each drop their first term from their sums",
				Simp(Fwd(ComplexSumsDef), Fwd(complex_field.PartsSub)),
				By(
					real_series.SumsShift.At(arg.TermAs[Fun[Nat, Real]]("λn:num. re(a(n))"), arg.TermAs[Real]("re(s)")),
					real_series.SumsShift.At(
						arg.TermAs[Fun[Nat, Real]]("λn:num. im(a(n))"), arg.TermAs[Real]("im(s)"))))
		}),
})}

// ComparisonBound — a series whose terms are at most b(n) in size has a
// sum at most the sum t of the b(n) in size. Multiplied term by term by
// the conjugate of its sum s, the series sums to conj(s)·s, whose real
// part is |s|²; each real part re(conj(s)·a(n)) is at most
// |conj(s)·a(n)| = |s|·|a(n)| ≤ |s|·b(n), so the real comparison bound
// gives |s|² ≤ |s|·t. Where |s| is positive it divides out; where s is 0,
// t is at least 0, the b(n) being nonnegative.
var ComparisonBound = comparisonBoundThm{family.Add(registry.ProofEntry{
	Name: "ComparisonBound",
	Key:  "prop_118a55ef215b5087",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → complex). ∀b:(num → real). ∀s:complex. ∀t:real.",
		Hypotheses: []string{
			"∀n:num. |a(n)| ≤ b(n)",
			"complex_sums(a, s)",
			"real_sums(b, t)",
		},
		Conclusion: "|s| ≤ t",
	},
		func(
			arg *Argument,
			a *Arrow[Nat, Complex],
			b *Arrow[Nat, Real],
			s *Expr[Complex],
			t *Expr[Real],
			bounded, sums, bounds Fact,
		) {
			rotated := arg.Have(
				"multiplied term by term by conj(s), the series sums to conj(s)·s",
				"complex_sums(λn:num. conj(s) * a(n), conj(s) * s)",
				By(sums, SumsScale))
			realParts := arg.Have(
				"so its real parts sum to re(conj(s)·s)",
				"real_sums(λn:num. re(conj(s) * a(n)), re(conj(s) * s))",
				By(rotated, ComplexSumsDef))
			square := arg.Have(
				"which is |s|²",
				"re(conj(s) * s) = |s| * |s|",
				Simp(Fwd(complex_field.ComplexConjDef), Fwd(complex_field.ComplexMulDef)),
				ByArith(complex_abs.AbsSquare.At(s)))
			termwise := arg.Have(
				"each real part re(conj(s)·a(n)) is at most |conj(s)·a(n)| = |s|·|a(n)| ≤ |s|·b(n)",
				"∀n:num. |re(conj(s) * a(n))| ≤ |s| * b(n)",
				Derive(func(d *Argument) {
					n := d.FixAs[Nat]()
					d.Show(
						"a part is at most the modulus, and the modulus is multiplicative",
						ByArith(
							bounded.At(n),
							complex_abs.ReLessEqAbs.At(d.TermAs[Complex]("conj(s) * a(n)")),
							complex_abs.AbsMul.At(d.TermAs[Complex]("conj(s)"), a.Apply(n)),
							complex_abs.AbsConj.At(s),
							complex_abs.AbsNonneg.At(s)))
				}))
			ownSizes := arg.Have(
				"each b(n), at least |a(n)| ≥ 0, is its own size",
				"∀n:num. |b(n)| ≤ b(n)",
				arg.ForEach(func(n *Expr[Nat]) Action {
					return ByArith(bounded.At(n), complex_abs.AbsNonneg.At(a.Apply(n)))
				}))
			nonneg := arg.Have(
				"so their sum t is nonnegative",
				"&0 ≤ t",
				ByArith(ownSizes, bounds, real_series.ComparisonBound.At(b, b, t, t)))
			realBound := arg.Have(
				"the real comparison bound, against |s| times the series of the b(n)",
				"|re(conj(s) * s)| ≤ |s| * t",
				By(
					termwise,
					bounds,
					realParts,
					real_series.SumsScale.At(b, t, arg.TermAs[Real]("|s|")),
					real_series.ComparisonBound.At(
						arg.TermAs[Fun[Nat, Real]]("λn:num. re(conj(s) * a(n))"),
						arg.TermAs[Fun[Nat, Real]]("λn:num. |s| * b(n)"),
						arg.TermAs[Real]("re(conj(s) * s)"),
						arg.TermAs[Real]("|s| * t"))))
			squareBound := arg.Have(
				"so |s|² ≤ |s|·t",
				"|s| * |s| ≤ |s| * t",
				ByArith(square, realBound))
			arg.Cases(arg.Term("&0 < |s|"))
			arg.When(
				"where |s| is positive it divides out",
				func(d *Argument, positive Fact) {
					d.Show(
						"|s| ≤ t",
						ByArith(positive, squareBound))
				})
			arg.Otherwise(
				"where |s| is 0, t ≥ 0 is the bound",
				func(d *Argument, zero Fact) {
					d.Show(
						"|s| ≤ t",
						ByArith(zero, nonneg, complex_abs.AbsNonneg.At(s)))
				})
		}),
})}

// Comparison — a complex series whose terms are at most b(n) in size, the
// b(n) summing to t, has a sum, at most t in size. The sizes are their own
// absolute values, so they have a sum by the real comparison test; a series
// whose sizes have a sum has a sum, and the comparison bound prices it.
var Comparison = comparisonThm{family.Add(registry.ProofEntry{
	Name: "Comparison",
	Key:  "prop_201b68fe658c0328",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → complex). ∀b:(num → real). ∀t:real.",
		Hypotheses: []string{
			"∀n:num. |a(n)| ≤ b(n)",
			"real_sums(b, t)",
		},
		Conclusion: "∃s:complex. complex_sums(a, s) ∧ |s| ≤ t",
	},
		func(
			arg *Argument,
			a *Arrow[Nat, Complex],
			b *Arrow[Nat, Real],
			t *Expr[Real],
			bounded, bounds Fact,
		) {
			sizes := arg.TermAs[Fun[Nat, Real]]("λn:num. |a(n)|")
			dominated := arg.Have(
				"each size is its own absolute value, so b dominates the sizes from the first index on",
				"∀n:num. 0 ≤ n ⇒ ||a(n)|| ≤ b(n)",
				arg.ForEach(func(n *Expr[Nat]) Action {
					return ByArith(bounded.At(n), complex_abs.AbsNonneg.At(a.Apply(n)))
				}))
			u, sizesSum := arg.ObtainAs[Real](
				"so the sizes have a sum u, by comparison with b",
				"∃u:real. real_sums(λn:num. |a(n)|, u)",
				By(dominated, bounds, real_series.Comparison.At(sizes, b, t, arg.TermAs[Nat]("0"))))
			s, sum := arg.ObtainAs[Complex](
				"and the series a sum s, its sizes having one",
				"∃s:complex. complex_sums(a, s)",
				By(sizesSum, AbsoluteConvergence.At(a, u)),
				Named("s"))
			arg.Take(s)
			arg.Show(
				"whose size the comparison bound puts at most t",
				By(sum, bounded, bounds, ComparisonBound.At(a, b, s, t)))
		}),
})}

// SumsIffPartialSums — a complex series sums to s exactly when its partial
// sums tend to s. A series sums to s when its real parts sum to re(s) and
// its imaginary parts to im(s), each a statement about real partial sums.
// The parts of a partial sum are the partial sums of the parts (SumParts),
// and the partial sums of the series converge as their parts do
// (complex_topology.ConvergesIffParts).
var SumsIffPartialSums = sumsIffPartialSumsThm{family.Add(registry.ProofEntry{
	Name: "SumsIffPartialSums",
	Key:  "prop_f6b883006cbb220d",
	Build: family.Theorem(
		"∀a:(num → complex). ∀s:complex. complex_sums(a, s) ⇔ (λn:num. Σ_{k∈0 .. n} a(k)) ⟶ s",
		func(arg *Argument, a *Arrow[Nat, Complex], s *Expr[Complex]) {
			parts := arg.Have(
				"the parts of a partial sum are the partial sums of the parts",
				"∀n:num. "+
					"    re(Σ_{k∈0 .. n} a(k)) = Σ_{k∈0 .. n} re(a(k)) ∧ im(Σ_{k∈0 .. n} a(k)) = Σ_{k∈0 .. n} im(a(k))",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					b.Show(
						"the segment 0 .. n is finite, and the parts of a finite sum are the sums of the parts",
						By(num_segment.Finite.At(b.TermAs[Nat]("0"), n), SumParts.At(b.TermAs[Set[Nat]]("0 .. n"), a)))
				}))
			arg.Show(
				"the series sums to s when its parts sum to the parts "+
					"of s, and the partial sums converge as their parts do",
				Unfold(ComplexSumsDef),
				Unfold(real_series.RealSumsDef),
				Simp(Fwd(complex_topology.ConvergesIffParts)),
				Simp(Fwd(parts)),
				Basic())
		}),
})}
