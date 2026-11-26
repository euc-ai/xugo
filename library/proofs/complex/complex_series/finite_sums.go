// finite_sums.go — a finite sum of complex numbers read in the Σ spelling
// (its parts, its modulus, summation by parts), a series with its first
// terms dropped, and the regrouping of an absolutely convergent double
// series along a map with finite fibres.

package complex_series

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_series"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/registry"
)

// SumParts — the real part of a finite complex sum is the sum of the real
// parts, and the imaginary part likewise.
var SumParts = sumPartsThm{family.Add(registry.ProofEntry{
	Name: "SumParts",
	Key:  "prop_755a1cf02c937718",
	Build: family.Theorem(Statement{
		Binders:    "∀s:set(A). ∀f:(A → complex).",
		Hypotheses: []string{"finite(s)"},
		Conclusion: "re(Σ_{i∈s} f(i)) = Σ_{i∈s} re(f(i)) ∧ im(Σ_{i∈s} f(i)) = Σ_{i∈s} im(f(i))",
	},
		func(a *Argument, s *Expr[Set[A]], f *Arrow[A, Complex], finite Fact) {
			zeros := a.Have(
				"the real and imaginary projections send complex zero to real zero",
				"re(neutral_elem(complex_add)) = neutral_elem(real_add) ∧ "+
					"im(neutral_elem(complex_add)) = neutral_elem(real_add)",
				Simp(
					Fwd(comm_ring.NeutralAdd.Read(complex_field.CommRing)),
					Fwd(real_ring.NeutralAdd),
					Fwd(complex_field.ComplexOfRealDef),
					Fwd(complex_field.ComplexReDef),
					Fwd(complex_field.ComplexImDef)),
				Basic())
			fold := monoidal.Homomorphic.Read(comm_ring.MonoidalAdd.Read(complex_field.CommRing))
			realAdd := a.TermAs[Op[Real]]("real_add")
			a.Show(
				"each projection preserves addition and so carries the complex fold to a real sum",
				By(
					zeros,
					complex_field.PartsAdd,
					real_ring.MonoidalAdd,
					finite,
					real_sum.RealSumDef,
					fold.At(realAdd, a.TermAs[Fun[Complex, Real]]("complex_re"), s, f),
					fold.At(realAdd, a.TermAs[Fun[Complex, Real]]("complex_im"), s, f)))
		}),
	Reading: "Finiteness is needed: over an infinite support both folds are 0 by convention, " +
		"but the supports of f and of its parts differ, so the equation can fail there.",
})}

// AbsSumLessEq — the modulus of a finite complex sum is at most the sum of
// the moduli.
var AbsSumLessEq = absSumLessEqThm{family.Add(registry.ProofEntry{
	Name: "AbsSumLessEq",
	Key:  "prop_88984ad778399cdf",
	Build: family.Theorem(Statement{
		Binders:    "∀s:set(A). ∀f:(A → complex).",
		Hypotheses: []string{"finite(s)"},
		Conclusion: "|Σ_{i∈s} f(i)| ≤ Σ_{i∈s} |f(i)|",
	}, func(a *Argument, s *Expr[Set[A]], f *Arrow[A, Complex], finite Fact) {
		addition := comm_ring.AddMonoid.Read(complex_field.CommRing)
		a.Show(
			"the module sum at complex addition is the finite sum",
			By(finite, complex_abs.AbsSumTriangle.At(s, f), module.ModuleSumIteratedOp.Read(addition).At(s, f)))
	}),
})}

// SummationByParts — Abel's summation by parts for complex sequences on a
// segment m .. n: summing f against the forward differences of g gives the
// boundary term f(n + 1)·g(n + 1) − f(m)·g(m) less the sum of g, read one
// step ahead, against the forward differences of f.
//
// By induction on n, m fixed. On a one-term interval {k} the identity is
// the discrete product rule at k: the step of f·g from k to k + 1 is f(k)
// times the step of g plus g(k + 1) times the step of f. The sums start on
// such an interval: at n = 0, where m can only be 0, and at suc n when m is
// suc n. Otherwise each sum gains its term at suc n, the hypothesis
// evaluates the sums up to n, and the product rule at suc n moves the
// boundary term from f(n + 1)·g(n + 1) to f(suc n + 1)·g(suc n + 1).
var SummationByParts = summationByPartsThm{family.Add(registry.ProofEntry{
	Name: "SummationByParts",
	Key:  "prop_7f624bad34f67bdd",
	Build: family.Theorem(Statement{
		Binders:    "∀m n:num. ∀f g:(num → complex).",
		Hypotheses: []string{"m ≤ n"},
		Conclusion: "Σ_{k∈m .. n} f(k) * (g(k + 1) - g(k)) = " +
			"(f(n + 1) * g(n + 1) - f(m) * g(m)) - Σ_{k∈m .. n} g(k + 1) * (f(k + 1) - f(k))",
	},
		func(a *Argument, m *Expr[Nat]) {
			addition := comm_ring.MonoidalAdd.Read(complex_field.CommRing)
			a.Induct("n")
			a.Base(
				"n = 0: m can only be 0, each sum is its one term at 0, "+
					"and the identity between those terms is ring arithmetic",
				ByArith(monoidal.IntervalClauses.Read(addition), nat_order.LessEq))
			a.Step(
				"n → suc n: each sum gains its term at suc n, unless the interval is that one point",
				func(b *Argument, ih Fact) {
					f := b.FixAs[Fun[Nat, Complex]]()
					g := b.FixAs[Fun[Nat, Complex]]()
					reaches := b.Assume()
					n := b.TermAs[Nat]("n")
					top := b.TermAs[Nat]("suc(n)")
					fDeltaG := b.TermAs[Fun[Nat, Complex]]("λk:num. f(k) * (g(k + 1) - g(k))")
					gDeltaF := b.TermAs[Fun[Nat, Complex]]("λk:num. g(k + 1) * (f(k + 1) - f(k))")

					rule := b.Have(
						"the product rule at suc n: the step of f·g is f times "+
							"the step of g, plus g one step ahead times the step of f",
						"f(suc(n) + 1) * g(suc(n) + 1) - f(suc(n)) * g(suc(n)) = "+
							"f(suc(n)) * (g(suc(n) + 1) - g(suc(n))) + g(suc(n) + 1) * (f(suc(n) + 1) - f(suc(n)))",
						ByArith())

					below := b.Assuming(
						b.Term("m ≤ n"),
						"m = suc n: each sum is its one term at suc n, and the identity is the product rule there",
						Given(func(c *Argument, pastN Fact) {
							c.Show(
								"both one-term sums read off, the product rule closes the identity",
								ByArith(
									pastN,
									reaches,
									rule,
									monoidal.IntervalPoint.Read(addition).At(top, fDeltaG),
									monoidal.IntervalPoint.Read(addition).At(top, gDeltaF)))
						}))

					b.Show(
						"m ≤ n: the hypothesis evaluates the sums up to n, and the "+
							"product rule at suc n carries the boundary term one step up",
						ByArith(
							ih.At(f, g),
							below,
							reaches,
							rule,
							monoidal.IntervalClauses.Read(addition).At(fDeltaG),
							monoidal.IntervalClauses.Read(addition).At(gDeltaF),
							nat_arith.Add1.At(n)))
				})
		}),
	Reading: "With f the constant 1 this is the telescope: " +
		"the sum of g(k + 1) − g(k) over m .. n is g(n + 1) − g(m).",
})}

// SumsOffset — a series sums to s exactly when the series without its
// first m + 1 terms sums to s less those terms. By induction on m: dropping
// the first term alone is SumsShift, the sum over 0 .. 0 being a(0); and
// SumsShift drops the first term a(m + 1) of the series left after m + 1
// terms, which the partial sum up to m + 1 adds to the one up to m.
var SumsOffset = sumsOffsetThm{family.Add(registry.ProofEntry{
	Name: "SumsOffset",
	Key:  "prop_6d334f8e7d25c8db",
	Build: family.Theorem("∀a:(num → complex). ∀s:complex. ∀m:num. "+
		"    complex_sums(a, s) ⇔ complex_sums(λn:num. a(n + m + 1), s - Σ_{k∈0 .. m} a(k))",
		func(arg *Argument, a *Arrow[Nat, Complex], s *Expr[Complex]) {
			addition := comm_ring.MonoidalAdd.Read(complex_field.CommRing)
			arg.Induct("m")
			arg.Base(
				"dropping a(0), the sum over 0 .. 0, is SumsShift",
				By(SumsShift.At(a, s), nat_arith.AddZero, monoidal.IntervalPoint.Read(addition)))
			arg.Step(
				"dropping a(m + 1) as well moves it from the series into the partial sum",
				func(b *Argument, ih Fact) {
					m := b.TermAs[Nat]("m")
					partial := b.Have(
						"the partial sum up to m + 1 is the partial sum up to m plus a(m + 1)",
						"Σ_{k∈0 .. suc(m)} a(k) = Σ_{k∈0 .. m} a(k) + a(suc(m))",
						By(nat_order.ZeroLessEq.At(b.TermAs[Nat]("suc(m)")), monoidal.IntervalClauses.Read(addition).At(a)))
					reindexed := b.Have(
						"the series left after m + 1 terms, less its first term, is the series left after m + 2",
						"(λn:num. a(n + 1 + m + 1)) = (λn:num. a(n + suc(m) + 1))",
						Funext(),
						Derive(func(c *Argument) {
							c.FixAs[Nat]("n")
							index := c.Have(
								"n + 1 + m + 1 is n + (m + 1) + 1",
								"n + 1 + m + 1 = n + suc(m) + 1",
								ByArith())
							c.Show(
								"so the two terms are one",
								By(index))
						}))
					remainder := b.Have(
						"s less the partial sum up to m, less the next term "+
							"a(0 + m + 1), is s less the partial sum up to m + 1",
						"s - Σ_{k∈0 .. m} a(k) - a(0 + m + 1) = s - Σ_{k∈0 .. suc(m)} a(k)",
						ByArith(partial, nat_arith.Add1.At(m)))
					b.Show(
						"so the induction hypothesis and SumsShift on the series left after m + 1 terms give the step",
						By(
							ih,
							remainder,
							reindexed,
							SumsShift.At(
								b.TermAs[Fun[Nat, Complex]]("λn:num. a(n + m + 1)"), b.TermAs[Complex]("s - Σ_{k∈0 .. m} a(k)"))))
				})
		}),
})}

// DoubleSeriesRegroup — an absolutely convergent double series of complex
// numbers has the same sum taken row by row and taken along the fibres of
// a map with finite fibres.
var DoubleSeriesRegroup = doubleSeriesRegroupThm{family.Add(registry.ProofEntry{
	Name: "DoubleSeriesRegroup",
	Key:  "prop_6a2b58b7ce28f31e",
	Build: family.Theorem(Statement{
		Binders: "∀u:(num → num → complex). ∀φ:(num → num → num). ∀R:(num → real). ∀T:real.",
		Hypotheses: []string{
			"∀m:num. real_sums(λn:num. |u(m, n)|, R(m))",
			"real_sums(R, T)",
			"∀k:num. finite({p:prod(num, num) | φ(fst(p), snd(p)) = k})",
		},
		Conclusion: "∃r:(num → complex). ∃S:complex. " +
			"    (∀m:num. complex_sums(λn:num. u(m, n), r(m))) ∧ " +
			"    complex_sums(r, S) ∧ " +
			"    complex_sums(λk:num. Σ_{p∈{p:prod(num, num) | φ(fst(p), snd(p)) = k}} u(fst(p), snd(p)), S)",
		Abbrev: Abbrev{
			{Name: "fibre", Text: "λk:num. {p:prod(num, num) | φ(fst(p), snd(p)) = k}"},
			{Name: "entry", Text: "λp:prod(num, num). u(fst(p), snd(p))"},
		},
	},
		func(
			a *Argument,
			u *Arrow2[Nat, Nat, Complex],
			φ *Arrow2[Nat, Nat, Nat],
			R *Arrow[Nat, Real],
			T *Expr[Real],
			hypotheses Fact,
		) {
			parts := a.Conjuncts(
				hypotheses,
				"each row of moduli sums to the corresponding R(m)",
				"the row totals sum to T",
				"each fibre is finite")
			absoluteRows, absoluteTotal, finiteFibres := parts[0], parts[1], parts[2]
			zero := a.TermAs[Nat]("0")
			regroup := a.Have(
				"every real-valued projection bounded by the modulus can be summed in either grouping",
				Statement{
					Binders:    "∀f:(complex → real).",
					Hypotheses: []string{"∀z:complex. |f(z)| ≤ |z|"},
					Conclusion: "∃V:(num → real). ∃A:real. " +
						"    (∀m:num. real_sums(λn:num. f(u(m, n)), V(m))) ∧ " +
						"    real_sums(V, A) ∧ " +
						"    real_sums(λk:num. Σ_{p∈«fibre»(k)} f(«entry»(p)), A)",
				},
				Derive(func(b *Argument) {
					b.FixAs[Fun[Complex, Real]]()
					bounded := b.Assume()
					termBounds := b.Have(
						"the projection is bounded term by term",
						"∀m n:num. |f(u(m, n))| ≤ |u(m, n)|",
						Derive(func(c *Argument) {
							m := c.FixAs[Nat]()
							n := c.FixAs[Nat]()
							c.Show(
								"use the bound at the chosen entry",
								By(bounded.At(u.Apply(m, n))))
						}))
					rowExists := b.Have(
						"each row of projected moduli has a sum by comparison",
						"∀m:num. ∃B:real. real_sums(λn:num. |f(u(m, n))|, B)",
						Derive(func(c *Argument) {
							m := c.FixAs[Nat]()
							c.Show(
								"compare with the row of complex moduli",
								By(
									termBounds.At(m),
									absoluteRows.At(m),
									real_sgn_abs.AbsIdempotent,
									real_series.Comparison.At(
										c.TermAs[Fun[Nat, Real]]("λn:num. |f(u(m, n))|"),
										c.TermAs[Fun[Nat, Real]]("λn:num. |u(m, n)|"),
										R.Apply(m),
										zero)))
						}))
					Q, rowSums := b.ObtainAs[Fun[Nat, Real]](
						"choose the projected absolute row sums as a function",
						"∃Q:(num → real). ∀m:num. real_sums(λn:num. |f(u(m, n))|, Q(m))",
						By(rowExists),
						Named("Q"))
					rowBounds := b.Have(
						"the projected row sums are bounded in absolute value by R",
						"∀m:num. |Q(m)| ≤ R(m)",
						Derive(func(c *Argument) {
							m := c.FixAs[Nat]()
							c.Show(
								"the termwise bound passes to the row sums",
								By(
									termBounds.At(m),
									absoluteRows.At(m),
									rowSums.At(m),
									real_sgn_abs.AbsIdempotent,
									real_series.ComparisonBound.At(
										c.TermAs[Fun[Nat, Real]]("λn:num. |f(u(m, n))|"),
										c.TermAs[Fun[Nat, Real]]("λn:num. |u(m, n)|"),
										c.TermAs[Real]("Q(m)"),
										R.Apply(m))))
						}))
					B, total := b.ObtainAs[Real](
						"compare the projected absolute row sums with R to obtain a total",
						"∃B:real. real_sums(Q, B)",
						By(rowBounds, absoluteTotal, real_series.Comparison.At(Q, R, T, zero)))
					b.Show(
						"regroup the absolutely summable real double series",
						By(
							rowSums,
							total,
							finiteFibres,
							extended_nonneg_real.AbsolutelySummableRegroup.At(
								b.TermAs[Fun2[Nat, Nat, Real]]("λm:num. λn:num. f(u(m, n))"), φ, Q, B)))
				}))
			_, _, reSums := a.Obtain2As[Fun[Nat, Real], Real](
				"sum and regroup the real parts",
				"∃Vre:(num → real). ∃Are:real. "+
					"    (∀m:num. real_sums(λn:num. re(u(m, n)), Vre(m))) ∧ "+
					"    real_sums(Vre, Are) ∧ "+
					"    real_sums(λk:num. Σ_{p∈«fibre»(k)} re(«entry»(p)), Are)",
				By(regroup.At(a.TermAs[Fun[Complex, Real]]("complex_re")), complex_abs.ReLessEqAbs),
				Named("Vre", "Are"))
			_, _, imSums := a.Obtain2As[Fun[Nat, Real], Real](
				"sum and regroup the imaginary parts",
				"∃Vim:(num → real). ∃Aim:real. "+
					"    (∀m:num. real_sums(λn:num. im(u(m, n)), Vim(m))) ∧ "+
					"    real_sums(Vim, Aim) ∧ "+
					"    real_sums(λk:num. Σ_{p∈«fibre»(k)} im(«entry»(p)), Aim)",
				By(regroup.At(a.TermAs[Fun[Complex, Real]]("complex_im")), complex_abs.ImLessEqAbs),
				Named("Vim", "Aim"))
			fibreParts := a.Have(
				"the real and imaginary parts pass through each finite fibre sum",
				"∀k:num. "+
					"    re(Σ_{p∈«fibre»(k)} «entry»(p)) = Σ_{p∈«fibre»(k)} re(«entry»(p)) ∧ "+
					"    im(Σ_{p∈«fibre»(k)} «entry»(p)) = Σ_{p∈«fibre»(k)} im(«entry»(p))",
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]()
					b.Show(
						"apply the finite-sum formula on the fibre",
						By(
							finiteFibres.At(k),
							SumParts.At(
								b.TermAs[Set[Prod[Nat, Nat]]]("«fibre»(k)"),
								b.TermAs[Fun[Prod[Nat, Nat], Complex]]("«entry»"))))
				}))
			a.Take(a.TermAs[Fun[Nat, Complex]]("λm:num. complex(Vre(m), Vim(m))"))
			a.Take(a.TermAs[Complex]("complex(Are, Aim)"))
			a.Show(
				"pair the two components for the row sums and the common total",
				Simp(Fwd(ComplexSumsDef), Fwd(complex_field.ComplexReDef), Fwd(complex_field.ComplexImDef)),
				By(fibreParts, imSums, reSums))
		}),
	Reading: "The first two hypotheses say that the sum of all the moduli is finite, " +
		"taken row by row. The fibres must be finite for the regrouped term to be a " +
		"finite sum: over an infinite fibre the fold is 0 by convention and the statement " +
		"would fail. Every pair lies in exactly one fibre, so nothing is counted twice or " +
		"lost. The Dirichlet product reads it at φ(m, n) = (m + 1)(n + 1) − 1.",
})}
