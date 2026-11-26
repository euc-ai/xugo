// convergence.go — where a Dirichlet series converges: to the right of a
// point of absolute convergence, absolutely for Re s > 1 when its
// coefficients are bounded or at most log n, and for Re s > 0 when its
// coefficients have bounded partial sums, by partial summation.

package dirichlet_series

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_cpow"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_series"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_topology"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_rpow"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/real/real_series"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/registry"
)

// DirichletSeriesValue — a Dirichlet series that sums to v has v as its
// value by uniqueness of the sum.
var DirichletSeriesValue = dirichletSeriesValueThm{family.Add(registry.ProofEntry{
	Name: "DirichletSeriesValue",
	Key:  "prop_7dd3d8f945c76b31",
	Build: family.Theorem(Statement{
		Binders:    "∀a:(num → complex). ∀s v:complex.",
		Hypotheses: []string{"dirichlet_sums(a, s, v)"},
		Conclusion: "dirichlet_series(a, s) = v",
	}, func(arg *Argument, a *Arrow[Nat, Complex], s, v *Expr[Complex], toV Fact) {
		chosen := arg.Have(
			"the series value is a sum because v witnesses convergence",
			"dirichlet_sums(a, s, dirichlet_series(a, s))",
			Unfold(DirichletSeriesDef),
			By(HilbertDenoted, toV))
		toVTerms := arg.Unfolded(toV, DirichletSumsDef)
		toChosenTerms := arg.Unfolded(chosen, DirichletSumsDef)
		terms := arg.TermAs[Fun[Nat, Complex]]("λn:num. a(n + 1) * complex_cpow(&(n + 1), -s)")
		value := arg.TermAs[Complex]("dirichlet_series(a, s)")
		arg.Show(
			"the term sequence has only one sum",
			By(toVTerms, toChosenTerms, complex_series.SumsUnique.At(terms, value, v)))
	}),
})}

// DirichletSumsAdd — Dirichlet series add coefficient by coefficient: the
// Dirichlet weight distributes over the two coefficients.
var DirichletSumsAdd = dirichletSumsAddThm{family.Add(registry.ProofEntry{
	Name: "DirichletSumsAdd",
	Key:  "prop_a10baf91f3f8217b",
	Build: family.Theorem(Statement{
		Binders: "∀a b:(num → complex). ∀s v w:complex.",
		Hypotheses: []string{
			"dirichlet_sums(a, s, v)",
			"dirichlet_sums(b, s, w)",
		},
		Conclusion: "dirichlet_sums(λn:num. a(n) + b(n), s, v + w)",
	}, func(arg *Argument, a, b *Arrow[Nat, Complex], s, v, w *Expr[Complex], toV, toW Fact) {
		aSums := arg.Unfolded(toV, DirichletSumsDef)
		bSums := arg.Unfolded(toW, DirichletSumsDef)
		aTerms := arg.TermAs[Fun[Nat, Complex]]("λn:num. a(n + 1) * complex_cpow(&(n + 1), -s)")
		bTerms := arg.TermAs[Fun[Nat, Complex]]("λn:num. b(n + 1) * complex_cpow(&(n + 1), -s)")
		arg.Show(
			"the Dirichlet weight distributes over the two coefficients",
			Simp(Fwd(DirichletSumsDef), Fwd(comm_ring.RightDistrib.Read(complex_field.CommRing))),
			By(aSums, bSums, complex_series.SumsAdd.At(aTerms, bTerms, v, w)))
	}),
})}

// DirichletSumsScale — a complex multiple of a Dirichlet series is the
// series of the multiplied coefficients: the scalar factors out of each
// weighted coefficient.
var DirichletSumsScale = dirichletSumsScaleThm{family.Add(registry.ProofEntry{
	Name: "DirichletSumsScale",
	Key:  "prop_f2441ff24362c753",
	Build: family.Theorem(Statement{
		Binders:    "∀a:(num → complex). ∀s v c:complex.",
		Hypotheses: []string{"dirichlet_sums(a, s, v)"},
		Conclusion: "dirichlet_sums(λn:num. c * a(n), s, c * v)",
	}, func(arg *Argument, a *Arrow[Nat, Complex], s, v, c *Expr[Complex], toV Fact) {
		aSums := arg.Unfolded(toV, DirichletSumsDef)
		aTerms := arg.TermAs[Fun[Nat, Complex]]("λn:num. a(n + 1) * complex_cpow(&(n + 1), -s)")
		arg.Show(
			"the scalar factors out of the weighted coefficient",
			Simp(Fwd(DirichletSumsDef), Rev(comm_monoid.Assoc.Read(complex_field.MulMonoid))),
			By(aSums, complex_series.SumsScale.At(aTerms, v, c)))
	}),
})}

// DirichletSumsZero — the Dirichlet series with zero coefficients sums to
// zero at every s: each of its terms is zero, and the series of zeros sums
// to zero.
var DirichletSumsZero = dirichletSumsZeroThm{family.Add(registry.ProofEntry{
	Name: "DirichletSumsZero",
	Key:  "prop_ae63a762f5c1b80c",
	Reading: "No hypothesis is put on s: every term of the series is zero, " +
		"whatever the power n^(−s), so the zero series converges on the whole plane.",
	Build: family.Theorem("∀s:complex. "+
		"    dirichlet_sums(λn:num. complex_of_real(&0), s, complex_of_real(&0))",
		func(a *Argument, s *Expr[Complex]) {
			a.Do(Simp(Fwd(DirichletSumsDef)))
			zero := a.Have(
				"every weighted term vanishes",
				"(λn:num. complex_of_real(&0) * complex_cpow(complex_of_real(&(n + 1)), -s)) = "+
					"(λn:num. complex_of_real(&0))",
				Funext(),
				Derive(func(b *Argument) {
					b.FixAs[Nat]("n")
					b.Show(
						"multiply by zero",
						ByArith())
				}))
			a.Show(
				"embed the zero real series",
				By(
					zero,
					complex_series.SumsOfReal.At(a.TermAs[Fun[Nat, Real]]("λn:num. &0"), a.TermAs[Real]("&0")),
					real_series.SumsZero))
		}),
})}

// DirichletSumsFiniteSum — a finite sum of Dirichlet series that converge
// at s converges at s, coefficient by coefficient, to the sum of their
// values: by induction on the finite index set, the empty sum being the
// zero series (DirichletSumsZero) and each insertion one more addition
// (DirichletSumsAdd).
var DirichletSumsFiniteSum = dirichletSumsFiniteSumThm{family.Add(registry.ProofEntry{
	Name: "DirichletSumsFiniteSum",
	Key:  "prop_263f8db10e231b8",
	Reading: "Every series is read at the same s, and the index set must " +
		"be finite: over the empty set the statement is that of the zero " +
		"series. The index type is arbitrary, as for the characters modulo q.",
	Build: family.Theorem(Statement{
		Binders:    "∀F:(A → num → complex). ∀V:(A → complex). ∀s:complex. ∀S:set(A).",
		Hypotheses: []string{"finite(S)", "∀x:A. x ∈ S ⇒ dirichlet_sums(F(x), s, V(x))"},
		Conclusion: "dirichlet_sums(λn:num. Σ_{x∈S} F(x, n), s, Σ_{x∈S} V(x))",
	}, func(
		a *Argument,
		F *Arrow2[A, Nat, Complex],
		V *Arrow[A, Complex],
		s *Expr[Complex],
		S *Expr[Set[A]],
		all Fact,
	) {
		addition := comm_ring.MonoidalAdd.Read(complex_field.CommRing)
		properties := a.TermAs[Fun[Set[A], Bool]](
			"λS:set(A). dirichlet_sums(λn:num. Σ_{x∈S} F(x, n), s, Σ_{x∈S} V(x))")
		summable := a.TermAs[Fun[A, Bool]]("λx:A. dirichlet_sums(F(x), s, V(x))")
		a.Show(
			"insert the terms of the finite set one at a time",
			ByInduction(At(finite_set.FiniteInductFreshOn.Inst[A](), properties, summable), all,
				Case(
					"the empty sum has zero coefficients and value",
					Simp(Fwd(monoidal.Clauses.Read(addition)), Fwd(comm_ring.NeutralAdd.Read(complex_field.CommRing))),
					By(At(DirichletSumsZero, s))),
				Case(
					"adding one term adds its coefficients and its value",
					Derive(func(b *Argument) {
						x := b.FixAs[A]("x")
						t := b.FixAs[Set[A]]("t")
						step := b.Assume()
						combined := b.Have(
							"add the two convergent series",
							"dirichlet_sums(λn:num. F(x,n) + Σ_{y∈t} F(y,n), s, V(x) + Σ_{y∈t} V(y))",
							By(
								step,
								DirichletSumsAdd.At(
									b.TermAs[Fun[Nat, Complex]]("F(x)"),
									b.TermAs[Fun[Nat, Complex]]("λn:num. Σ_{y∈t} F(y,n)"),
									s,
									b.TermAs[Complex]("V(x)"),
									b.TermAs[Complex]("Σ_{y∈t} V(y)"))))
						coefficients := b.Have(
							"the inserted summand gives the new coefficient function",
							"(λn:num. Σ_{y∈insert(x,t)} F(y,n)) = (λn:num. F(x,n) + Σ_{y∈t} F(y,n))",
							Funext(),
							Derive(func(c *Argument) {
								c.FixAs[Nat]("n")
								c.Show(
									"insert x into the coefficient sum",
									By(step, monoidal.OneTurn.Read(addition).At(t, x, c.TermAs[Fun[A, Complex]]("λy:A. F(y,n)"))))
							}))
						value := b.Have(
							"insert x into the sum of values",
							"Σ_{y∈insert(x,t)} V(y) = V(x) + Σ_{y∈t} V(y)",
							By(step, monoidal.OneTurn.Read(addition).At(t, x, V)))
						b.Show(
							"substitute the two insert equations",
							By(coefficients, value, combined))
					}))))
	}),
})}

// DirichletSeriesOfReal — a Dirichlet series with real coefficients f,
// read in ℂ at a real point σ, has the value v when the real series
// Σ f(n + 1)·(n + 1)^(−σ) sums to v: at a real exponent each complex power
// is the real one, so the complex series is the real one embedded.
var DirichletSeriesOfReal = dirichletSeriesOfRealThm{family.Add(registry.ProofEntry{
	Name: "DirichletSeriesOfReal",
	Key:  "prop_34bd4e5767fc1cf5",
	Reading: "The hypothesis is that the real series sums to v, not that it " +
		"converges absolutely, and f(0) is never read. This is how a Dirichlet " +
		"series with real coefficients, summed in ℝ, is read as a value in ℂ.",
	Build: family.Theorem(Statement{
		Binders:    "∀f:(num → real). ∀σ v:real.",
		Hypotheses: []string{"real_sums(λn:num. f(n + 1) * real_rpow(&(n + 1), -σ), v)"},
		Conclusion: "dirichlet_series(λn:num. complex_of_real(f(n)), complex_of_real(σ)) = " +
			"complex_of_real(v)",
	}, func(a *Argument, f *Arrow[Nat, Real], σ, v *Expr[Real], sums Fact) {
		terms := a.Have(
			"the complex terms at a real parameter are the embedded real terms",
			"(λn:num. complex_of_real(f(n + 1)) * complex_cpow(&(n + 1), -complex_of_real(σ))) = "+
				"(λn:num. complex_of_real(f(n + 1) * real_rpow(&(n + 1), -σ)))",
			Funext(),
			Derive(func(b *Argument) {
				b.FixAs[Nat]("n")
				base := b.TermAs[Real]("&(n + 1)")
				exponent := b.TermAs[Real]("-σ")
				positive := b.Have(
					"the shifted index is positive",
					"&0 < &(n + 1)",
					ByArith())
				b.Show(
					"embed the negation, power, and product",
					By(
						positive,
						complex_field.OfRealNeg.At(σ),
						complex_cpow.CpowRealExponent.At(base, exponent),
						complex_field.OfRealMul.At(b.TermAs[Real]("f(n + 1)"), b.TermAs[Real]("real_rpow(&(n + 1), -σ)"))))
			}))
		coefficients := a.TermAs[Fun[Nat, Complex]]("λn:num. complex_of_real(f(n))")
		s := a.TermAs[Complex]("complex_of_real(σ)")
		value := a.TermAs[Complex]("complex_of_real(v)")
		complexSum := a.Have(
			"the real sum embeds as a Dirichlet sum",
			"dirichlet_sums(λn:num. complex_of_real(f(n)), complex_of_real(σ), complex_of_real(v))",
			By(
				sums,
				terms,
				DirichletSumsDef.At(coefficients, s, value),
				complex_series.SumsOfReal.At(
					a.TermAs[Fun[Nat, Real]]("λn:num. f(n + 1) * real_rpow(&(n + 1), -σ)"), v)))
		a.Show(
			"the sum determines the series value",
			By(complexSum, DirichletSeriesValue.At(coefficients, s, value)))
	}),
})}

// AbsolutelySummableRight — a Dirichlet series whose moduli converge at a
// real σ has summable moduli at every s with Re s ≥ σ, their sum at most
// the sum at σ: at s each term is at most its majorant at σ in modulus.
var AbsolutelySummableRight = absolutelySummableRightThm{family.Add(registry.ProofEntry{
	Name: "AbsolutelySummableRight",
	Key:  "prop_8d7a779acc3deae9",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → complex). ∀σ t:real. ∀s:complex.",
		Hypotheses: []string{
			"real_sums(λn:num. |a(n + 1)| * real_rpow(&(n + 1), -σ), t)",
			"σ ≤ re(s)",
		},
		Conclusion: "∃u:real. real_sums(λn:num. |a(n + 1) * complex_cpow(&(n + 1), -s)|, u) ∧ u ≤ t",
	}, func(
		arg *Argument,
		a *Arrow[Nat, Complex],
		σ, t *Expr[Real],
		s *Expr[Complex],
		atSigma, toRight Fact,
	) {
		_, termsDef := arg.LetAs[Fun[Nat, Complex]]("f", "λn:num. a(n + 1) * complex_cpow(&(n + 1), -s)")
		g, majorantDef := arg.LetAs[Fun[Nat, Real]]("g", "λn:num. |a(n + 1)| * real_rpow(&(n + 1), -σ)")
		dominated := arg.Have(
			"the convergent majorant dominates the moduli term by term",
			"∀n:num. |f(n)| ≤ g(n)",
			Derive(func(d *Argument) {
				d.FixAs[Nat]("n")
				d.Do(Simp(Fwd(termsDef), Fwd(majorantDef)))
				x, baseDef := d.LetAs[Real]("x", "&(n + 1)")
				atLeastOne := d.Have(
					"the base is at least one",
					"&1 ≤ x",
					ByArith(baseDef))
				powerBound := d.Have(
					"at a base of at least one the power x^(−s) is at most x^(−σ) in modulus, σ being at most Re s",
					"|complex_cpow(&x, -s)| ≤ real_rpow(x, -σ)",
					By(atLeastOne, toRight, complex_cpow.AbsCpowNegLessEq.At(x, σ, s)))
				coefficient := d.TermAs[Complex]("a(n + 1)")
				d.Show(
					"the modulus of the term is |a(n + 1)| times that of the power, which the power bound bounds",
					ByArith(
						powerBound,
						complex_abs.AbsMul.At(coefficient, d.TermAs[Complex]("complex_cpow(&x, -s)")),
						complex_abs.AbsNonneg.At(coefficient)))
			}))
		comparison := arg.Have(
			"from index zero the real comparison bound applies to the moduli",
			"∀n:num. 0 ≤ n ⇒ real_abs(|f(n)|) ≤ g(n)",
			arg.ForEach(func(n *Expr[Nat]) Action { return ByArith(dominated.At(n)) }))
		moduli := arg.TermAs[Fun[Nat, Real]]("λn:num. |f(n)|")
		u, moduliSum := arg.UnpackAs[Real](
			GroupPremises(comparison, atSigma, real_series.Comparison.At(moduli, g, t, arg.TermAs[Nat]("0"))),
			"u")
		arg.Show(
			"the moduli sum to u, which the termwise bound puts at most t",
			Witness(u),
			SplitConj(
				Case(
					"the moduli of the terms sum to u",
					By(moduliSum)),
				Case(
					"u is at most the sum t of the majorant",
					By(dominated, moduliSum, atSigma, real_series.SumsLessEq.At(moduli, g, u, t)))))
	}),
})}

// AbsolutelyConvergentRight — a Dirichlet series whose moduli converge at
// a real σ converges at every s with Re s ≥ σ, to a sum no larger than the
// sum of the moduli.
var AbsolutelyConvergentRight = absolutelyConvergentRightThm{family.Add(registry.ProofEntry{
	Name: "AbsolutelyConvergentRight",
	Key:  "prop_fc9f33e4ced2e545",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → complex). ∀σ t:real. ∀s:complex.",
		Hypotheses: []string{
			"real_sums(λn:num. |a(n + 1)| * real_rpow(&(n + 1), -σ), t)",
			"σ ≤ re(s)",
		},
		Conclusion: "∃v:complex. dirichlet_sums(a, s, v) ∧ |v| ≤ t",
	}, func(
		arg *Argument,
		a *Arrow[Nat, Complex],
		σ, t *Expr[Real],
		s *Expr[Complex],
		atSigma, toRight Fact,
	) {
		u, summable := arg.UnpackAs[Real](
			GroupPremises(atSigma, toRight, AbsolutelySummableRight.At(a, σ, t, s)),
			"u")
		moduli := arg.Conjuncts(
			summable,
			"the moduli of the terms at s sum to u",
			"u is at most t")
		f := arg.TermAs[Fun[Nat, Complex]]("λn:num. a(n + 1) * complex_cpow(&(n + 1), -s)")
		v, seriesSum := arg.UnpackAs[Complex](
			GroupPremises(moduli[0], complex_series.AbsoluteConvergence.At(f, u)),
			"v")
		arg.Show(
			"the sum of the absolutely convergent series is bounded by the sum of its moduli",
			Witness(v),
			SplitConj(
				Case(
					"v is a Dirichlet sum",
					Simp(Fwd(DirichletSumsDef)),
					By(seriesSum)),
				Case(
					"the moduli bound the modulus of v by u, and u is at most t",
					ByArith(
						moduli[1],
						seriesSum,
						moduli[0],
						complex_series.ComparisonBound.At(
							f, arg.TermAs[Fun[Nat, Real]]("λn:num. |a(n + 1) * complex_cpow(&(n + 1), -s)|"), v, u)))))
	}),
	Reading: "The hypothesis is absolute convergence at the real point σ, with " +
		"its sum t named; it gives the whole closed half-plane to the right of σ.",
})}

// BoundedCoefficientsConverge — a Dirichlet series with bounded
// coefficients converges for Re s > 1, and its sum is within
// B/(Re s − 1) of its first coefficient.
var BoundedCoefficientsConverge = boundedCoefficientsConvergeThm{family.Add(registry.ProofEntry{
	Name: "BoundedCoefficientsConverge",
	Key:  "prop_c706ed005aabf232",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → complex). ∀B:real. ∀s:complex.",
		Hypotheses: []string{
			"∀n:num. |a(n)| ≤ B",
			"&1 < re(s)",
		},
		Conclusion: "∃v:complex. dirichlet_sums(a, s, v) ∧ |v - a(1)| ≤ B / (re(s) - &1)",
	}, func(
		arg *Argument,
		a *Arrow[Nat, Complex],
		B *Expr[Real],
		s *Expr[Complex],
		coefficients, aboveOne Fact,
	) {
		p, powersDef := arg.LetAs[Fun[Nat, Real]]("p", "λn:num. real_rpow(&(n + 1), -re(s))")
		f, termsDef := arg.LetAs[Fun[Nat, Complex]]("f", "λn:num. a(n + 1) * complex_cpow(&(n + 1), -s)")
		exponent := arg.TermAs[Real]("-re(s)")
		complexExponent := arg.TermAs[Complex]("-s")
		one := arg.TermAs[Nat]("1")
		T, powerSum := arg.ObtainAs[Real](
			"the real power series has a sum bounded by one plus the reciprocal exponent gap",
			"∃T:real. real_sums(p, T) ∧ T ≤ &1 + &1 / (re(s) - &1)",
			Simp(Fwd(powersDef)),
			By(aboveOne, real_rpow.RpowSeriesConverges.At(arg.TermAs[Real]("re(s)"))))
		powers := arg.Conjuncts(
			powerSum,
			"the powers sum to T",
			"the upper bound on T")
		firstPower := arg.Have(
			"the first power is one",
			"p(0) = &1",
			Simp(Fwd(powersDef)),
			By(real_rpow.RpowOneBase.At(exponent)))
		powersTail := arg.Have(
			"the shifted power series sums to T less its first term",
			"real_sums(λn:num. p(n + 1), T - p(0))",
			By(powers[0], real_series.SumsShift.At(p, T)))
		nonnegative := arg.Have(
			"the bound on the first coefficient makes B nonnegative",
			"&0 ≤ B",
			ByArith(coefficients.At(one)))
		majorantBound := arg.Have(
			"scaling the power tail by B gives the reciprocal-gap bound",
			"B * (T - p(0)) ≤ B / (re(s) - &1)",
			ByArith(firstPower, powers[1], nonnegative))
		g, majorantDef := arg.LetAs[Fun[Nat, Real]]("g", "λn:num. B * p(n + 1)")
		h, tailDef := arg.LetAs[Fun[Nat, Complex]]("h", "λn:num. f(n + 1)")
		majorantTotal := arg.TermAs[Real]("B * (T - p(0))")
		majorantSum := arg.Have(
			"the majorant sums to B times the power tail sum",
			"real_sums(g, B * (T - p(0)))",
			Simp(Fwd(majorantDef)),
			By(
				powersTail,
				real_series.SumsScale.At(
					arg.TermAs[Fun[Nat, Real]]("λn:num. p(n + 1)"), arg.TermAs[Real]("T - p(0)"), B)))
		dominated := arg.Have(
			"the majorant dominates the moduli of the complex tail term by term",
			"∀n:num. |h(n)| ≤ g(n)",
			Derive(func(d *Argument) {
				d.FixAs[Nat]("n")
				d.Do(Simp(Fwd(termsDef), Fwd(tailDef), Fwd(majorantDef), Fwd(powersDef)))
				x, baseDef := d.LetAs[Real]("x", "&(n + 1 + 1)")
				positive := d.Have(
					"the base is positive",
					"&0 < x",
					ByArith(baseDef))
				powerSize := d.Have(
					"the modulus of the complex power is the corresponding real power",
					"|complex_cpow(&x, -s)| = real_rpow(x, -re(s))",
					By(Normalized, positive, complex_cpow.AbsCpow.At(x, complexExponent), complex_field.PartsNeg.At(s)))
				d.Show(
					"multiply the coefficient bound by the nonnegative power",
					ByArith(
						coefficients.At(d.TermAs[Nat]("n + 1 + 1")),
						powerSize,
						real_rpow.RpowNonneg.At(x, exponent)))
			}))
		_, tailSum := arg.UnpackAs[Complex](
			GroupPremises(dominated, majorantSum, complex_series.Comparison.At(h, g, majorantTotal)), "w")
		firstTerm := arg.Have(
			"the complex weight is one on the first coefficient",
			"f(0) = a(1)",
			Simp(Fwd(termsDef)),
			ByArith(complex_cpow.CpowOneBase.At(complexExponent)))
		remainder := arg.Have(
			"adding back the first term leaves w as the remainder",
			"a(1) + w - f(0) = w",
			ByArith(firstTerm))
		shifted := arg.Have(
			"the shifted complex series sums to the proposed sum less its first term",
			"complex_sums(λn:num. f(n + 1), a(1) + w - f(0))",
			Simp(Rev(tailDef), Fwd(remainder)),
			By(tailSum))
		value := arg.TermAs[Complex]("a(1) + w")
		errorTerm := arg.Simplified(remainder, Fwd(firstTerm))
		arg.Show(
			"adding back the first coefficient gives a Dirichlet sum with the tail bound",
			Witness(value),
			SplitConj(
				Case(
					"restore the first term of the original series",
					Simp(Fwd(DirichletSumsDef), Rev(termsDef)),
					By(shifted, complex_series.SumsShift.At(f, value))),
				Case(
					"the error is the modulus of the tail sum",
					Simp(Fwd(errorTerm)),
					ByArith(tailSum, majorantBound))))
	}),
	Reading: "The bound on v − a(1) is what lets s tend to +∞: the sum tends to its first coefficient.",
})}

// BoundedAbsolutelySummable — a Dirichlet series with bounded coefficients
// converges absolutely at every real σ > 1: its terms are at most
// B·n^(−σ), and that series converges.
var BoundedAbsolutelySummable = boundedAbsolutelySummableThm{family.Add(registry.ProofEntry{
	Name: "BoundedAbsolutelySummable",
	Key:  "prop_31c68d936a4ce0d6",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → complex). ∀B σ:real.",
		Hypotheses: []string{
			"∀n:num. |a(n)| ≤ B",
			"&1 < σ",
		},
		Conclusion: "∃t:real. real_sums(λn:num. |a(n + 1)| * real_rpow(&(n + 1), -σ), t)",
	}, func(arg *Argument, a *Arrow[Nat, Complex], B, σ *Expr[Real], bounded, aboveOne Fact) {
		T, powerSum := arg.UnpackAs[Real](GroupPremises(aboveOne, real_rpow.RpowSeriesConverges.At(σ)), "T")
		scaled := arg.Have(
			"B times the powers sums to B·T",
			"real_sums(λn:num. B * real_rpow(&(n + 1), -σ), B * T)",
			By(
				powerSum,
				real_series.SumsScale.At(arg.TermAs[Fun[Nat, Real]]("λn:num. real_rpow(&(n + 1), -σ)"), T, B)))
		dominated := arg.Have(
			"from index zero each term is at most B·(n + 1)^(−σ), the power being nonnegative",
			"∀n:num. 0 ≤ n ⇒ ||a(n + 1)| * real_rpow(&(n + 1), -σ)| ≤ B * real_rpow(&(n + 1), -σ)",
			Derive(func(d *Argument) {
				d.FixAs[Nat]("n")
				d.Assume()
				d.Show(
					"multiply the coefficient bound by the nonnegative power",
					ByArith(
						bounded.At(d.TermAs[Nat]("n + 1")),
						real_rpow.RpowNonneg.At(d.TermAs[Real]("&(n + 1)"), d.TermAs[Real]("-σ"))))
			}))
		arg.Show(
			"so the moduli have a sum, by comparison with B times the powers",
			By(
				dominated,
				scaled,
				real_series.Comparison.At(
					arg.TermAs[Fun[Nat, Real]]("λn:num. |a(n + 1)| * real_rpow(&(n + 1), -σ)"),
					arg.TermAs[Fun[Nat, Real]]("λn:num. B * real_rpow(&(n + 1), -σ)"),
					arg.TermAs[Real]("B * T"),
					arg.TermAs[Nat]("0"))))
	}),
})}

// LogBoundedAbsolutelySummable — a Dirichlet series whose coefficients are
// at most log n in modulus converges absolutely at every real σ > 1: its
// terms are at most log n · n^(−σ), and that series converges.
var LogBoundedAbsolutelySummable = logBoundedAbsolutelySummableThm{family.Add(registry.ProofEntry{
	Name: "LogBoundedAbsolutelySummable",
	Key:  "prop_530176d66066e629",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → complex). ∀σ:real.",
		Hypotheses: []string{
			"∀n:num. |a(n + 1)| ≤ log(&(n + 1))",
			"&1 < σ",
		},
		Conclusion: "∃t:real. real_sums(λn:num. |a(n + 1)| * real_rpow(&(n + 1), -σ), t)",
	}, func(arg *Argument, a *Arrow[Nat, Complex], σ *Expr[Real], bounded, aboveOne Fact) {
		L, logSum := arg.UnpackAs[Real](
			GroupPremises(aboveOne, real_rpow.LogRpowSeriesConverges.At(σ)), "L")
		dominated := arg.Have(
			"from index zero each term is at most log(n + 1)·(n + 1)^(−σ), the power being nonnegative",
			"∀n:num. 0 ≤ n ⇒ ||a(n + 1)| * real_rpow(&(n + 1), -σ)| ≤ log(&(n + 1)) * real_rpow(&(n + 1), -σ)",
			Derive(func(d *Argument) {
				n := d.FixAs[Nat]("n")
				d.Assume()
				d.Show(
					"multiply the coefficient bound by the nonnegative power",
					ByArith(bounded.At(n), real_rpow.RpowNonneg.At(d.TermAs[Real]("&(n + 1)"), d.TermAs[Real]("-σ"))))
			}))
		arg.Show(
			"so the moduli have a sum, by comparison with the logarithm-weighted powers",
			By(
				dominated,
				logSum,
				real_series.Comparison.At(
					arg.TermAs[Fun[Nat, Real]]("λn:num. |a(n + 1)| * real_rpow(&(n + 1), -σ)"),
					arg.TermAs[Fun[Nat, Real]]("λn:num. log(&(n + 1)) * real_rpow(&(n + 1), -σ)"),
					L,
					arg.TermAs[Nat]("0"))))
	}),
})}

// LogBoundedCoefficientsConverge — a Dirichlet series whose coefficients are
// at most log n in modulus converges for Re s > 1, and its sum is its value:
// its moduli are summable at Re s (LogBoundedAbsolutelySummable), so it
// converges absolutely there.
var LogBoundedCoefficientsConverge = logBoundedCoefficientsConvergeThm{family.Add(registry.ProofEntry{
	Name: "LogBoundedCoefficientsConverge",
	Key:  "prop_cbdad71ee8d558dc",
	Reading: "The bound is put on f(n + 1) for every n, so f(0), which no Dirichlet " +
		"series reads, is free. The conclusion names the sum as dirichlet_series(f, s), " +
		"the form in which a proof goes on to compute with the value.",
	Build: family.Theorem(Statement{
		Binders:    "∀f:(num → complex). ∀s:complex.",
		Hypotheses: []string{"∀n:num. |f(n + 1)| ≤ log(&(n + 1))", "&1 < re(s)"},
		Conclusion: "dirichlet_sums(f, s, dirichlet_series(f, s))",
	}, func(a *Argument, f *Arrow[Nat, Complex], s *Expr[Complex], bounds Fact) {
		σ := a.TermAs[Real]("re(s)")
		t, absolute := a.ObtainAs[Real](
			"coefficients at most log n in modulus make the moduli summable",
			"∃t:real. real_sums(λn:num. |f(n + 1)| * real_rpow(&(n + 1), -re(s)), t)",
			By(bounds, LogBoundedAbsolutelySummable.At(f, σ)))
		v, summed := a.ObtainAs[Complex](
			"the Dirichlet series has a sum",
			"∃v:complex. dirichlet_sums(f, s, v)",
			By(absolute, AbsolutelyConvergentRight.At(f, σ, t, s), real_order_ring.LessEqRefl))
		a.Show(
			"the chosen value is the sum",
			By(Normalized, summed, DirichletSeriesValue.At(f, s, v)))
	}),
})}

// DirichletSeriesDifferenceBound — at a real σ > 1, two Dirichlet series
// with real coefficients F and G, F at most the logarithm in modulus, differ
// in value by at most t when the weighted differences |F(n) − G(n)|·n^(−σ)
// are dominated by a series U summing to t: the logarithm makes the terms of
// F summable, U makes the differences summable with a sum of modulus at most
// t, and the terms of G are those of F less the differences, so the two
// values differ by the sum of the differences.
var DirichletSeriesDifferenceBound = dirichletSeriesDifferenceBoundThm{family.Add(registry.ProofEntry{
	Name: "DirichletSeriesDifferenceBound",
	Key:  "prop_116c39572f617289",
	Reading: "F(0) and G(0) are never read: every hypothesis is put on n + 1. The logarithmic " +
		"bound and σ > 1 are what make the series of F converge; that of G then converges because " +
		"U dominates the differences, so neither series is assumed to converge, and U is any " +
		"summable majorant of the weighted differences, not the differences themselves.",
	Build: family.Theorem(Statement{
		Binders: "∀F G U:(num → real). ∀σ t:real.",
		Hypotheses: []string{
			"&1 < σ",
			"∀n:num. |F(n + 1)| ≤ log(&(n + 1))",
			"∀n:num. |F(n + 1) - G(n + 1)| * real_rpow(&(n + 1), -σ) ≤ U(n)",
			"real_sums(U, t)",
		},
		Conclusion: "|dirichlet_series(λn:num. complex_of_real(F(n)), complex_of_real(σ)) - " +
			"dirichlet_series(λn:num. complex_of_real(G(n)), complex_of_real(σ))| ≤ " +
			"t",
	}, func(
		a *Argument,
		F, G, U *Arrow[Nat, Real],
		σ, t *Expr[Real],
		right, logBound, dominated, uSums Fact,
	) {
		_, weight := a.LetAs[Fun[Nat, Real]]("W", "λn:num. real_rpow(&n, -σ)")
		A, allTerms := a.LetAs[Fun[Nat, Real]]("A", "λn:num. F(n + 1) * W(n + 1)")
		_, keptTerms := a.LetAs[Fun[Nat, Real]]("B", "λn:num. G(n + 1) * W(n + 1)")
		P, logTerms := a.LetAs[Fun[Nat, Real]]("P", "λn:num. log(&(n + 1)) * W(n + 1)")
		C, removedTerms := a.LetAs[Fun[Nat, Real]]("C", "λn:num. (F(n + 1) - G(n + 1)) * W(n + 1)")
		p, pSums := a.ObtainAs[Real](
			"the logarithmic majorant converges",
			"∃p:real. real_sums(P, p)",
			By(right, logTerms, weight, real_rpow.LogRpowSeriesConverges.At(σ)),
			Named("p"))
		weights := a.Have(
			"the weights are positive",
			"∀n:num. &0 < W(n + 1)",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("n")
				b.Show(
					"a positive base has a positive power",
					ByArith(weight, real_rpow.RpowPositive.At(b.TermAs[Real]("&(n + 1)"), b.TermAs[Real]("-σ"))))
			}))
		allMajorized := a.Have(
			"the logarithmic majorant dominates the terms of F",
			"∀n:num. |A(n)| ≤ P(n)",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				b.Show(
					"the positive weight preserves the bound",
					ByArith(allTerms, logTerms, logBound.At(n), weights.At(n)))
			}))
		removedMajorized := a.Have(
			"U dominates the weighted differences",
			"∀n:num. |C(n)| ≤ U(n)",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				b.Show(
					"the positive weight comes out of the modulus",
					ByArith(removedTerms, weight, dominated.At(n), weights.At(n)))
			}))
		subtract := a.Have(
			"subtracting the differences leaves the terms of G",
			"B = (λn:num. A(n) - C(n))",
			Funext(),
			Derive(func(b *Argument) {
				b.FixAs[Nat]("n")
				b.Show(
					"the weight distributes over the difference",
					ByArith(allTerms, keptTerms, removedTerms))
			}))
		zero := a.TermAs[Nat]("0")
		v, aSums := a.ObtainAs[Real](
			"comparison gives a sum for the series of F",
			"∃v:real. real_sums(A, v)",
			By(allMajorized, pSums, real_series.Comparison.At(A, P, p, zero), nat_order.ZeroLessEq),
			Named("v"))
		w, cSums := a.ObtainAs[Real](
			"comparison gives a sum for the differences",
			"∃w:real. real_sums(C, w)",
			By(removedMajorized, uSums, real_series.Comparison.At(C, U, t, zero), nat_order.ZeroLessEq),
			Named("w"))
		bSums := a.Have(
			"the terms of G sum to the difference",
			"real_sums(B, v - w)",
			By(Normalized, aSums, cSums, subtract, real_series.SumsSub.At(A, C, v, w)))
		wBound := a.Have(
			"the sum of the differences is bounded by the sum of the majorant",
			"|w| ≤ t",
			By(removedMajorized, cSums, uSums, real_series.ComparisonBound.At(C, U, w, t)))
		allValue := a.Have(
			"the series of F has the embedded real value",
			"dirichlet_series(λn:num. complex_of_real(F(n)), complex_of_real(σ)) = complex_of_real(v)",
			By(aSums, allTerms, weight, DirichletSeriesOfReal.At(F, σ, v)))
		net := a.TermAs[Real]("v - w")
		keptValue := a.Have(
			"the series of G has the embedded difference",
			"dirichlet_series(λn:num. complex_of_real(G(n)), complex_of_real(σ)) = complex_of_real(v - w)",
			By(bSums, keptTerms, weight, DirichletSeriesOfReal.At(G, σ, net)))
		a.Show(
			"the modulus of the difference is |w|",
			ByArith(allValue, keptValue, wBound, complex_abs.AbsOfRealSub.At(v, net)))
	}),
})}

// DirichletPartialSummation — a partial sum of a Dirichlet series through
// the partial sums of its coefficients.
var DirichletPartialSummation = dirichletPartialSummationThm{family.Add(registry.ProofEntry{
	Name: "DirichletPartialSummation",
	Key:  "prop_9a9c146a89d1009f",
	Build: family.Theorem(
		"∀a:(num → complex). ∀s:complex. ∀N:num. "+
			"    Σ_{n∈1 .. N} a(n) * complex_cpow(&n, -s) = "+
			"    (Σ_{k∈1 .. N} a(k)) * complex_cpow(&(N + 1), -s) + "+
			"    Σ_{n∈1 .. N} (Σ_{k∈1 .. n} a(k)) * (complex_cpow(&n, -s) - complex_cpow(&(n + 1), -s))",
		func(arg *Argument, a *Arrow[Nat, Complex], s *Expr[Complex]) {
			addition := comm_ring.MonoidalAdd.Read(complex_field.CommRing)
			appendTerm := monoidal.IntervalClauses.Read(addition)
			arg.Induct("N")
			arg.Base(
				"at zero all three sums are empty",
				func(b *Argument) {
					empty := b.Have(
						"the interval from one to zero is empty",
						"1 .. 0 = ∅",
						By(num_segment.Empty.At(b.TermAs[Nat]("1"), b.TermAs[Nat]("0"))))
					b.Show(
						"the sums are zero, so both sides vanish",
						Simp(Fwd(empty)),
						ByArith(monoidal.Clauses.Read(addition), comm_ring.NeutralAdd.Read(complex_field.CommRing)))
				})
			arg.Step(
				"append the next summands and advance the boundary term",
				func(b *Argument, ih Fact) {
					f, weightedDef := b.LetAs[Fun[Nat, Complex]]("f", "λn:num. a(n) * complex_cpow(&n, -s)")
					g, differencesDef := b.LetAs[Fun[Nat, Complex]](
						"g", "λn:num. (Σ_{k∈1 .. n} a(k)) * (complex_cpow(&n, -s) - complex_cpow(&(n + 1), -s))")
					reaches := b.Have(
						"the new upper bound is at least one",
						"1 ≤ suc(N)",
						ByArith())
					weightedAppend := b.Have(
						"the weighted sum gains its last term",
						"Σ_{n∈1 .. suc(N)} f(n) = (Σ_{n∈1 .. N} f(n)) + f(suc(N))",
						ByArith(reaches, appendTerm.At(f)))
					differencesAppend := b.Have(
						"the difference sum gains its last term",
						"Σ_{n∈1 .. suc(N)} g(n) = (Σ_{n∈1 .. N} g(n)) + g(suc(N))",
						ByArith(reaches, appendTerm.At(g)))
					coefficientsAppend := b.Have(
						"the new boundary uses the partial sum including the next coefficient",
						"Σ_{n∈1 .. suc(N)} a(n) = (Σ_{n∈1 .. N} a(n)) + a(suc(N))",
						ByArith(reaches, appendTerm.At(a)))
					weightedLast := b.Have(
						"the added coefficient is weighted at the successor",
						"f(suc(N)) = a(suc(N)) * complex_cpow(&suc(N), -s)",
						Simp(Fwd(weightedDef)),
						Refl())
					differencesLast := b.Have(
						"the added difference uses the new coefficient sum",
						"g(suc(N)) = "+
							"(Σ_{k∈1 .. suc(N)} a(k)) * (complex_cpow(&suc(N), -s) - complex_cpow(&(suc(N) + 1), -s))",
						Simp(Fwd(differencesDef)),
						Refl())
					b.Show(
						"the new difference and boundary add the next weighted coefficient to the old identity",
						Simp(
							Fwd(weightedAppend),
							Fwd(differencesAppend),
							Fwd(weightedLast),
							Fwd(differencesLast),
							Fwd(coefficientsAppend),
							Fwd(nat_arith.Add1)),
						ByArith(ih))
				})
		}),
	Reading: "The boundary term carries (N + 1)^(−s), not N^(−s): with that " +
		"choice the identity needs no hypothesis on N and no truncated subtraction.",
})}

// abelSeriesTransfer carries an Abel-transformed sum back to the Dirichlet series.
func abelSeriesTransfer(ctx *Script) *GoalStackNode {
	return ctx.Lemma(Statement{
		Binders: "∀a:(num → complex). ∀B:real. ∀s v:complex.",
		Hypotheses: []string{
			"∀M:num. |Σ_{k∈1 .. M} a(k)| ≤ B",
			"&0 < re(s)",
			"complex_sums(λn:num. " +
				"        (Σ_{k∈1 .. n + 1} a(k)) * (complex_cpow(&(n + 1), -s) - complex_cpow(&(n + 2), -s)), " +
				"    v)",
		},
		Conclusion: "dirichlet_sums(a, s, v)",
	}, func(
		arg *Argument,
		a *Arrow[Nat, Complex],
		B *Expr[Real],
		s, v *Expr[Complex],
		bounded, positive, transformed Fact,
	) {
		zeroR := arg.TermAs[Real]("&0")
		zeroC := arg.TermAs[Complex]("complex_of_real(&0)")
		zeroN, oneN := arg.TermAs[Nat]("0"), arg.TermAs[Nat]("1")
		σ := arg.TermAs[Real]("re(s)")
		negS := arg.TermAs[Complex]("-s")
		E, boundary := arg.LetAs[Fun[Nat, Complex]]("E",
			"λn:num. (Σ_{k∈1 .. n + 1} a(k)) * complex_cpow(&(n + 2), -s)")
		R, power := arg.LetAs[Fun[Nat, Real]]("R", "λn:num. real_rpow(&(n + 2), -re(s))")
		singleShift := arg.TermAs[Fun[Nat, Real]]("λn:num. real_rpow(&(n + 1), -re(s))")
		vanishingPower := arg.Have(
			"positive real part gives a vanishing real power",
			"(λn:num. real_rpow(&(n + 1), -re(s))) ⟶ &0",
			By(positive, real_rpow.RpowNegTendsToZero.At(σ)))
		shifted := arg.Have(
			"shifting the power sequence by one keeps its zero limit",
			"(λn:num. real_rpow(&(n + 1 + 1), -re(s))) ⟶ &0",
			By(vanishingPower, real_sequences.LimitShift.At(singleShift, zeroR)))
		shiftEq := arg.Have(
			"R is the shifted sequence",
			"R = (λn:num. real_rpow(&(n + 1 + 1), -re(s)))",
			Funext(),
			Derive(func(b *Argument) {
				b.FixAs[Nat]("n")
				index := b.Have(
					"add two successors",
					"n + 1 + 1 = n + 2",
					ByArith())
				b.Show(
					"expand R at this index",
					By(Normalized, power, index))
			}))
		rLimit := arg.Have(
			"R tends to zero",
			"R ⟶ &0",
			By(shiftEq, shifted))
		scaled := arg.TermAs[Fun[Nat, Real]]("λn:num. B * R(n)")
		scaledLimit := arg.Have(
			"the coefficient bound times R also tends to zero",
			"(λn:num. B * R(n)) ⟶ &0",
			By(Normalized, rLimit, real_sequences.LimitScale.At(R, zeroR, B), real_ring.MulRightZero.At(B)))
		estimate := arg.Have(
			"the boundary term is bounded in modulus by B times R",
			"∀n:num. |E(n)| ≤ B * R(n)",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("n")
				k := b.TermAs[Nat]("n + 1")
				x := b.TermAs[Real]("&(n + 2)")
				cpow := b.TermAs[Complex]("complex_cpow(&(n + 2), -s)")
				partial := b.TermAs[Complex]("Σ_{k∈1 .. n + 1} a(k)")
				positiveBase := b.Have(
					"the power has positive base",
					"&0 < &(n + 2)",
					ByArith())
				modulus := b.Have(
					"the modulus of the complex power is the real power",
					"|complex_cpow(&(n + 2), -s)| = R(n)",
					By(positiveBase, power, complex_cpow.AbsCpow.At(x, negS), complex_field.PartsNeg.At(s)))
				nonnegative := b.Have(
					"the real power is nonnegative",
					"&0 ≤ R(n)",
					By(modulus, complex_abs.AbsNonneg.At(cpow)))
				product := b.Have(
					"moduli multiply in the boundary term",
					"|E(n)| = |Σ_{k∈1 .. n + 1} a(k)| * R(n)",
					By(Normalized, boundary, modulus, complex_abs.AbsMul.At(partial, cpow)))
				b.Show(
					"multiply the bound on the partial sum by the nonnegative power",
					ByArith(bounded.At(k), nonnegative, product))
			}))
		boundaryLimit := arg.Have(
			"the boundary term tends to zero, being at most B times R in modulus, which does",
			"E ⟶ complex_of_real(&0)",
			By(estimate, scaledLimit, complex_topology.LimitSqueezeZero.At(E, scaled)))

		Q, transformedTerm := arg.LetAs[Fun[Nat, Complex]]("Q",
			"λn:num. (Σ_{k∈1 .. n + 1} a(k)) * (complex_cpow(&(n + 1), -s) - complex_cpow(&(n + 2), -s))")
		qSums := arg.Have(
			"Q sums to v by hypothesis",
			"complex_sums(Q, v)",
			By(transformed, transformedTerm))
		H, hPartial := arg.LetAs[Fun[Nat, Complex]]("H", "λn:num. Σ_{k∈0 .. n} Q(k)")
		T, unshifted := arg.LetAs[Fun[Nat, Complex]]("T",
			"λn:num. (Σ_{k∈1 .. n} a(k)) * (complex_cpow(&n, -s) - complex_cpow(&(n + 1), -s))")
		G, original := arg.LetAs[Fun[Nat, Complex]]("G", "λn:num. a(n) * complex_cpow(&n, -s)")
		_, dTerm := arg.LetAs[Fun[Nat, Complex]]("D", "λn:num. G(n + 1)")
		hLimit := arg.Have(
			"the transformed partial sums tend to v",
			"H ⟶ v",
			By(Normalized, qSums, hPartial, complex_series.SumsIffPartialSums.At(Q, v)))
		qShift := arg.Have(
			"the transformed term is the shift of T",
			"Q = (λn:num. T(n + 1))",
			Funext(),
			Derive(func(b *Argument) {
				b.FixAs[Nat]("n")
				index := b.Have(
					"add two successors",
					"n + 1 + 1 = n + 2",
					ByArith())
				b.Show(
					"the two definitions give the same value at this index",
					Simp(Fwd(transformedTerm), Fwd(unshifted), Fwd(index)),
					Basic())
			}))
		_, fPartial := arg.LetAs[Fun[Nat, Complex]]("F", "λn:num. Σ_{k∈0 .. n} D(k)")
		addition := comm_ring.MonoidalAdd.Read(complex_field.CommRing)
		partialSummation := arg.Have(
			"the original partial sums add the vanishing boundary to H",
			"F = (λn:num. E(n) + H(n))",
			Funext(),
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				hShift := b.Have(
					"reindex H from one",
					"H(n) = Σ_{k∈1 .. n + 1} T(k)",
					By(
						hPartial,
						qShift,
						monoidal.Shift.Read(addition).At(zeroN, n, oneN, T),
						nat_arith.AddLeftZeroClause))
				fShift := b.Have(
					"reindex F from one",
					"F(n) = Σ_{k∈1 .. n + 1} G(k)",
					By(
						fPartial,
						dTerm,
						monoidal.Shift.Read(addition).At(zeroN, n, oneN, G),
						nat_arith.AddLeftZeroClause))
				index := b.Have(
					"one past n + 1 is n + 2",
					"n + 1 + 1 = n + 2",
					ByArith())
				abel := b.Have(
					"apply partial summation to the original terms",
					"Σ_{k∈1 .. n + 1} G(k) = E(n) + Σ_{k∈1 .. n + 1} T(k)",
					Simp(Fwd(original), Fwd(unshifted), Fwd(boundary)),
					By(index, DirichletPartialSummation.At(a, s, b.TermAs[Nat]("n + 1"))))
				b.Show(
					"combine the reindexings with the partial summation identity",
					By(hShift, fShift, abel))
			}))
		sumLimit := arg.Have(
			"the sum of the boundary term and H tends to zero plus v",
			"(λn:num. E(n) + H(n)) ⟶ complex_of_real(&0) + v",
			By(boundaryLimit, hLimit, complex_topology.LimitAdd.At(E, H, zeroC, v)))
		zeroAdd := arg.Have(
			"zero does not change the limit",
			"complex_of_real(&0) + v = v",
			ByArith())
		fLimit := arg.Have(
			"the original partial sums tend to v",
			"F ⟶ v",
			By(Normalized, zeroAdd, partialSummation, sumLimit))
		dSums := arg.Have(
			"the original shifted terms sum to v",
			"complex_sums(D, v)",
			Simp(Fwd(complex_series.SumsIffPartialSums), Rev(fPartial)),
			By(fLimit))
		arg.Show(
			"these terms define the Dirichlet series",
			Simp(Fwd(DirichletSumsDef)),
			By(dSums, dTerm, original))
	})
}

// BoundedSumsConverge — a Dirichlet series whose coefficients have bounded
// partial sums converges for Re s > 0, and its sum is within
// 2B|s|/(Re s · N^(Re s)) of its N-th partial sum.
var BoundedSumsConverge = boundedSumsConvergeThm{family.Add(registry.ProofEntry{
	Name: "BoundedSumsConverge",
	Key:  "prop_2f88799f7c02807a",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → complex). ∀B:real. ∀s:complex. ∀N:num.",
		Hypotheses: []string{
			"∀M:num. |Σ_{k∈1 .. M} a(k)| ≤ B",
			"&0 < re(s)",
			"0 < N",
		},
		Conclusion: "∃v:complex. " +
			"    dirichlet_sums(a, s, v) ∧ " +
			"    |v - Σ_{n∈1 .. N} a(n) * complex_cpow(&n, -s)| ≤ " +
			"    &2 * B * |s| / (re(s) * real_rpow(&N, re(s)))",
	},
		func(
			arg *Argument, a *Arrow[Nat, Complex], B *Expr[Real], s *Expr[Complex], N *Expr[Nat],
			bounded, positive, positiveN Fact,
		) {
			zero := arg.TermAs[Nat]("0")
			one := arg.TermAs[Nat]("1")
			σ := arg.TermAs[Real]("re(s)")
			σPlusOne := arg.TermAs[Real]("re(s) + &1")
			Q, abelTerm := arg.LetAs[Fun[Nat, Complex]]("Q",
				"λn:num. (Σ_{k∈1 .. n + 1} a(k)) * (complex_cpow(&(n + 1), -s) - complex_cpow(&(n + 2), -s))")
			U, power := arg.LetAs[Fun[Nat, Real]]("U", "λn:num. real_rpow(&(n + 1), -(re(s) + &1))")
			c, coefficient := arg.LetAs[Real]("c", "B * |s|")
			nonnegativeB := arg.Have(
				"a bound above a modulus is nonnegative",
				"&0 ≤ B",
				ByArith(bounded.At(zero), complex_abs.AbsNonneg.At(arg.TermAs[Complex]("Σ_{k∈1 .. 0} a(k)"))))
			nonnegativeC := arg.Have(
				"the majorant coefficient is nonnegative",
				"&0 ≤ c",
				ByArith(nonnegativeB, coefficient, complex_abs.AbsNonneg.At(s)))
			exponent := arg.Have(
				"negation of the shifted exponent distributes",
				"-re(s) - &1 = -(re(s) + &1)",
				ByArith())
			majorized := arg.Have(
				"the Abel terms have a power-series majorant",
				"∀n:num. |Q(n)| ≤ c * U(n)",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("n")
					k := b.TermAs[Nat]("n + 1")
					x := b.TermAs[Real]("&(n + 1)")
					y := b.TermAs[Real]("&(n + 2)")
					partial := b.TermAs[Complex]("Σ_{k∈1 .. n + 1} a(k)")
					difference := b.TermAs[Complex]("complex_cpow(&(n + 1), -s) - complex_cpow(&(n + 2), -s)")
					positiveBase := b.Have(
						"n + 1 is positive",
						"&0 < &(n + 1)",
						ByArith())
					order := b.Have(
						"the power comparison uses increasing bases",
						"&(n + 1) ≤ &(n + 2)",
						ByArith())
					step := b.Have(
						"the bases are one apart",
						"&(n + 2) - &(n + 1) = &1",
						ByArith())
					realPart := b.Have(
						"the real part meets the lower bound for power differences",
						"-&1 ≤ re(s)",
						ByArith(positive))
					rawDifference := b.Have(
						"bound the difference between the two consecutive weights",
						"|complex_cpow(&(n + 1), -s) - complex_cpow(&(n + 2), -s)| ≤ "+
							"|s| * (&(n + 2) - &(n + 1)) * real_rpow(&(n + 1), -re(s) - &1)",
						By(positiveBase, order, realPart, complex_cpow.CpowDifferenceBound.At(x, y, s)))
					samePower := b.Have(
						"the upper bound uses U at n",
						"U(n) = real_rpow(&(n + 1), -re(s) - &1)",
						By(power, exponent))
					differenceBound := b.Have(
						"the step of length one gives |s| times U",
						"|complex_cpow(&(n + 1), -s) - complex_cpow(&(n + 2), -s)| ≤ |s| * U(n)",
						ByArith(rawDifference, step, samePower))
					modulus := b.Have(
						"the modulus of the Abel term multiplies the two moduli",
						"|Q(n)| = |Σ_{k∈1 .. n + 1} a(k)| * |complex_cpow(&(n + 1), -s) - complex_cpow(&(n + 2), -s)|",
						By(abelTerm, complex_abs.AbsMul.At(partial, difference)))
					product := b.Have(
						"the partial sum factor is at most B in modulus",
						"|Q(n)| ≤ B * |complex_cpow(&(n + 1), -s) - complex_cpow(&(n + 2), -s)|",
						ByArith(modulus, bounded.At(k), complex_abs.AbsNonneg.At(difference)))
					b.Show(
						"multiply the bound on the weight difference by B",
						ByArith(product, differenceBound, nonnegativeB, coefficient))
				}))

			M, majorant := arg.LetAs[Fun[Nat, Real]]("M", "λn:num. c * U(n)")
			exponentLarge := arg.Have(
				"the majorant exponent exceeds one",
				"&1 < re(s) + &1",
				ByArith(positive))
			t, pSeries := arg.ObtainAs[Real](
				"the p-series has a sum t",
				"∃t:real. real_sums(U, t) ∧ t ≤ &1 + &1 / (re(s) + &1 - &1)",
				By(exponentLarge, power, real_rpow.RpowSeriesConverges.At(σPlusOne)))
			pSum := arg.Conjuncts(
				pSeries,
				"the sequence U sums to t",
				"the p-series bound")[0]
			majorantSum := arg.Have(
				"the scaled p-series sums to c times t",
				"real_sums(M, c * t)",
				By(Normalized, pSum, majorant, real_series.SumsScale.At(U, t, c)))
			v, abelSum := arg.ObtainAs[Complex](
				"the Abel-transformed series has a sum, by comparison with the scaled p-series",
				"∃v:complex. complex_sums(Q, v)",
				By(
					Normalized,
					majorized,
					majorant,
					majorantSum,
					complex_series.Comparison.At(Q, M, arg.TermAs[Real]("c * t"))))
			dirichletSum := arg.Have(
				"partial summation transfers the sum to the Dirichlet series",
				"dirichlet_sums(a, s, v)",
				By(bounded, positive, abelSum, abelTerm, At(abelSeriesTransfer(arg.Ctx()), a, B, s, v)))

			m, preceding := arg.LetAs[Nat]("m", "N - 1")
			Y, abelTail := arg.LetAs[Fun[Nat, Complex]]("Y", "λn:num. Q(n + m + 1)")
			W, powerTail := arg.LetAs[Fun[Nat, Real]]("W", "λn:num. U(n + m + 1)")
			H, abelPartial := arg.LetAs[Complex]("H", "Σ_{k∈0 .. m} Q(k)")
			τ, remaining := arg.LetAs[Real]("τ", "t - Σ_{k∈0 .. m} U(k)")
			endpoint := arg.Have(
				"the shifted partial sum ends at N",
				"m + 1 = N",
				ByArith(positiveN, preceding))
			abelTailSum := arg.Have(
				"the Abel tail sums to the difference from H",
				"complex_sums(Y, v - H)",
				By(abelSum, abelTail, abelPartial, complex_series.SumsOffset.At(Q, v, m)))
			powerTailSum := arg.Have(
				"the p-series tail sums to the difference from its partial sum",
				"real_sums(W, τ)",
				By(pSum, powerTail, remaining, real_series.SumsOffset.At(U, t, m)))
			scaledTail := arg.TermAs[Fun[Nat, Real]]("λn:num. c * W(n)")
			scaledTailSum := arg.Have(
				"the scaled tail sums to c times τ",
				"real_sums(λn:num. c * W(n), c * τ)",
				By(powerTailSum, real_series.SumsScale.At(W, τ, c)))
			tailMajorized := arg.Have(
				"the shifted terms keep the termwise bounds",
				"∀n:num. |Y(n)| ≤ c * W(n)",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("n")
					k := b.TermAs[Nat]("n + m + 1")
					b.Show(
						"compare at the corresponding original index",
						By(Normalized, majorized.At(k), abelTail, powerTail, majorant))
				}))
			abelRemainder := arg.Have(
				"comparison bounds the Abel remainder by the scaled tail",
				"|v - H| ≤ c * τ",
				By(
					abelTailSum,
					scaledTailSum,
					tailMajorized,
					complex_series.ComparisonBound.At(
						Y, scaledTail, arg.TermAs[Complex]("v - H"), arg.TermAs[Real]("c * τ"))))

			P, unshiftedPower := arg.LetAs[Fun[Nat, Real]]("P", "λk:num. real_rpow(&k, -re(s) - &1)")
			F, tailPartial := arg.LetAs[Fun[Nat, Real]]("F", "λn:num. Σ_{k∈0 .. n} W(k)")
			powerShift := arg.Have(
				"the p-series tail starts at original index N + 1",
				"W = (λn:num. P(n + (N + 1)))",
				Funext(),
				Derive(func(b *Argument) {
					b.FixAs[Nat]("n")
					index := b.Have(
						"the shift drops the first N positive indices",
						"n + m + 1 + 1 = n + (N + 1)",
						ByArith(endpoint))
					b.Show(
						"the same power occurs at the corresponding index",
						Simp(Fwd(powerTail), Fwd(power), Fwd(unshiftedPower)),
						By(index, exponent))
				}))
			tailLimit := arg.Have(
				"the finite partial sums of the power tail tend to τ",
				"F ⟶ τ",
				By(Normalized, powerTailSum, tailPartial, real_series.RealSumsDef.At(W, τ)))
			finiteTail := arg.Have(
				"each partial sum of the p-series tail keeps the same bound",
				"∀n:num. F(n) ≤ real_rpow(&N, -re(s)) / re(s)",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					first := b.TermAs[Nat]("N + 1")
					last := b.TermAs[Nat]("n + (N + 1)")
					reindexed := b.Have(
						"read the shifted sum on the segment from N + 1",
						"F(n) = Σ_{k∈N + 1 .. n + (N + 1)} P(k)",
						By(tailPartial, powerShift, real_sum.Shift.At(zero, n, first, P), nat_arith.AddLeftZeroClause))
					bound := b.Have(
						"apply the negative-power tail bound to this segment",
						"Σ_{k∈N + 1 .. n + (N + 1)} P(k) ≤ real_rpow(&N, -re(s)) / re(s)",
						By(positive, positiveN, unshiftedPower, real_rpow.RpowTailSumBound.At(σ, N, last)))
					b.Show(
						"the same bound holds for F(n)",
						By(reindexed, bound))
				}))
			powerLimitBound := arg.Have(
				"the power tail bound passes to the limit",
				"τ ≤ real_rpow(&N, -re(s)) / re(s)",
				By(
					tailLimit,
					finiteTail,
					real_sequences.LimitLessEqBound.At(F, τ, arg.TermAs[Real]("real_rpow(&N, -re(s)) / re(s)"))))
			abelBound := arg.Have(
				"the Abel remainder has the scaled power tail bound",
				"|v - H| ≤ c * (real_rpow(&N, -re(s)) / re(s))",
				ByArith(abelRemainder, powerLimitBound, nonnegativeC))

			S, originalPartial := arg.LetAs[Complex]("S", "Σ_{n∈1 .. N} a(n) * complex_cpow(&n, -s)")
			E, boundary := arg.LetAs[Complex]("E", "(Σ_{k∈1 .. N} a(k)) * complex_cpow(&(N + 1), -s)")
			T, unshiftedTerm := arg.LetAs[Fun[Nat, Complex]]("T",
				"λn:num. (Σ_{k∈1 .. n} a(k)) * (complex_cpow(&n, -s) - complex_cpow(&(n + 1), -s))")
			termShift := arg.Have(
				"Q shifts the Abel summand by one",
				"Q = (λn:num. T(n + 1))",
				Funext(),
				Derive(func(b *Argument) {
					b.FixAs[Nat]("n")
					index := b.Have(
						"add the two successors",
						"n + 1 + 1 = n + 2",
						ByArith())
					b.Show(
						"both summands agree at n",
						Simp(Fwd(abelTerm), Fwd(unshiftedTerm), Fwd(index)),
						Basic())
				}))
			addition := comm_ring.MonoidalAdd.Read(complex_field.CommRing)
			abelIndex := arg.Have(
				"the Abel terms sum over the original interval 1 through N",
				"H = Σ_{k∈1 .. N} T(k)",
				By(
					abelPartial,
					termShift,
					endpoint,
					monoidal.Shift.Read(addition).At(zero, m, one, T),
					nat_arith.AddLeftZeroClause))
			partial := arg.Have(
				"partial summation gives the boundary plus the Abel partial sum",
				"S = E + Σ_{k∈1 .. N} T(k)",
				Simp(Fwd(originalPartial), Fwd(boundary), Fwd(unshiftedTerm)),
				By(DirichletPartialSummation.At(a, s, N)))
			abelIdentity := arg.Have(
				"the original partial sum is E plus H",
				"S = E + H",
				By(Normalized, partial, abelIndex))

			base := arg.TermAs[Real]("&N")
			next := arg.TermAs[Real]("&(N + 1)")
			negσ := arg.TermAs[Real]("-re(s)")
			cpow := arg.TermAs[Complex]("complex_cpow(&(N + 1), -s)")
			ρ := arg.TermAs[Real]("real_rpow(&N, re(s))")
			η := arg.TermAs[Real]("real_rpow(&N, -re(s))")
			basePositive := arg.Have(
				"N gives a positive real base",
				"&0 < &N",
				ByArith(positiveN))
			nextPositive := arg.Have(
				"N + 1 gives a positive real base",
				"&0 < &(N + 1)",
				ByArith())
			basesIncreasing := arg.Have(
				"N + 1 exceeds N after casting to real",
				"&N < &(N + 1)",
				ByArith())
			exponentNegative := arg.Have(
				"the boundary exponent is negative",
				"-re(s) < &0",
				ByArith(positive))
			positivePower := arg.Have(
				"the positive power at N is positive",
				"&0 < real_rpow(&N, re(s))",
				By(basePositive, real_rpow.RpowPositive.At(base, σ)))
			nextPowerNonnegative := arg.Have(
				"the real power at N + 1 is nonnegative",
				"&0 ≤ real_rpow(&(N + 1), -re(s))",
				By(nextPositive, real_rpow.RpowNonneg.At(next, negσ)))
			powerDecreasing := arg.Have(
				"the negative power at N + 1 is smaller than at N",
				"real_rpow(&(N + 1), -re(s)) < real_rpow(&N, -re(s))",
				By(
					basePositive,
					basesIncreasing,
					exponentNegative,
					real_rpow.RpowLessBaseNegative.At(base, next, negσ)))
			boundaryWeight := arg.Have(
				"the boundary weight has modulus equal to the real power",
				"|complex_cpow(&(N + 1), -s)| = real_rpow(&(N + 1), -re(s))",
				By(
					nextPositive,
					complex_cpow.AbsCpow.At(next, arg.TermAs[Complex]("-s")),
					complex_field.PartsNeg.At(s)))
			boundaryModulus := arg.Have(
				"moduli multiply in the boundary term",
				"|E| = |Σ_{k∈1 .. N} a(k)| * real_rpow(&(N + 1), -re(s))",
				By(
					Normalized,
					boundary,
					boundaryWeight,
					complex_abs.AbsMul.At(arg.TermAs[Complex]("Σ_{k∈1 .. N} a(k)"), cpow)))
			earlyBoundary := arg.Have(
				"bound the partial sum factor by B",
				"|E| ≤ B * real_rpow(&(N + 1), -re(s))",
				ByArith(bounded.At(N), boundaryModulus, nextPowerNonnegative))
			boundaryBound := arg.Have(
				"the same upper bound using the larger power at N",
				"|E| ≤ B * real_rpow(&N, -re(s))",
				ByArith(earlyBoundary, powerDecreasing, nonnegativeB))

			L, boundScale := arg.LetAs[Real]("L", "real_rpow(&N, -re(s)) / re(s)")
			boundaryDifference := arg.Have(
				"H minus the original partial sum is the negative boundary",
				"H - S = -E",
				ByArith(abelIdentity))
			boundarySize := arg.Have(
				"negating the boundary does not change its modulus",
				"|H - S| = |E|",
				By(Normalized, boundaryDifference, complex_abs.AbsNeg.At(E)))
			remainderTriangle := arg.Have(
				"the total error is bounded by the Abel error and boundary modulus",
				"|v - S| ≤ |v - H| + |E|",
				By(Normalized, boundarySize, complex_abs.AbsSubTriangle.At(v, H, S)))
			nonnegativePower := arg.Have(
				"the negative power at N is nonnegative",
				"&0 ≤ real_rpow(&N, -re(s))",
				ByArith(nextPowerNonnegative, powerDecreasing))
			clearsScale := arg.Have(
				"multiplying L by the positive exponent recovers the negative power",
				"L * re(s) = real_rpow(&N, -re(s))",
				By(positive, boundScale, real_order_field.EqDivMulLeft.At(L, η, σ)))
			nonnegativeScale := arg.Have(
				"L is nonnegative",
				"&0 ≤ L",
				ByArith(
					positive,
					nonnegativePower,
					boundScale,
					real_order_field.LessEqDivMulLeft.At(arg.TermAs[Real]("&0"), η, σ)))
			boundCoefficient := arg.Have(
				"the real part is at most the modulus",
				"B * re(s) ≤ c",
				ByArith(nonnegativeB, coefficient, complex_abs.ReLessEqAbs.At(s)))
			scaledCoefficient := arg.Have(
				"multiply the coefficient inequality by L",
				"B * re(s) * L ≤ c * L",
				By(
					boundCoefficient,
					nonnegativeScale,
					real_order_ring.LessEqMulRight.At(arg.TermAs[Real]("B * re(s)"), c, L)))
			boundaryScale := arg.Have(
				"the boundary bound also is at most c times L",
				"B * real_rpow(&N, -re(s)) ≤ c * L",
				ByArith(Scaled(B, clearsScale), scaledCoefficient))
			doubled := arg.Have(
				"the boundary and Abel estimates each contribute c times L",
				"|v - S| ≤ &2 * c * L",
				ByArith(remainderTriangle, abelBound, boundScale, boundaryBound, boundaryScale))

			reciprocal := arg.Have(
				"the negative power is the reciprocal of the positive power",
				"real_rpow(&N, -re(s)) = real_inv(real_rpow(&N, re(s)))",
				By(basePositive, real_rpow.RpowNeg.At(base, σ)))
			inverseProduct := arg.Have(
				"the positive power times its inverse is one",
				"real_inv(real_rpow(&N, re(s))) * real_rpow(&N, re(s)) = &1",
				ByArith(positivePower, field.MulLeftInverse.Read(real_field.Field).At(ρ)))
			powerProduct := arg.Have(
				"the negative and positive powers multiply to one",
				"real_rpow(&N, -re(s)) * real_rpow(&N, re(s)) = &1",
				ByArith(Scaled(ρ, reciprocal), inverseProduct))
			clearsDenominator := arg.Have(
				"L is reciprocal to the denominator in the error bound",
				"L * (re(s) * real_rpow(&N, re(s))) = &1",
				ByArith(Scaled(ρ, clearsScale), powerProduct))
			positiveDenominator := arg.Have(
				"the exponent and the power are positive",
				"&0 < re(s) * real_rpow(&N, re(s))",
				ByArith(positive, positivePower))
			numerator := arg.Have(
				"multiplying the doubled bound by that denominator gives the claimed numerator",
				"(&2 * c * L) * (re(s) * real_rpow(&N, re(s))) = &2 * B * |s|",
				ByArith(
					Scaled(arg.TermAs[Real]("&2 * c"), clearsDenominator),
					Scaled(arg.TermAs[Real]("&2"), coefficient)))
			errorBound := arg.Have(
				"divide by the positive denominator",
				"&2 * c * L = &2 * B * |s| / (re(s) * real_rpow(&N, re(s)))",
				By(
					positiveDenominator,
					numerator,
					real_order_field.EqDivMulLeft.At(
						arg.TermAs[Real]("&2 * c * L"), arg.TermAs[Real]("&2 * B * |s|"),
						arg.TermAs[Real]("re(s) * real_rpow(&N, re(s))"))))
			arg.Take(v)
			arg.Show(
				"the Dirichlet sum has the stated error",
				By(dirichletSum, doubled, errorBound))
		}),
	Reading: "The convergence is conditional on 0 < Re s ≤ 1: the order " +
		"of summation is that of n. The bound grows with |s|, so it is " +
		"uniform on compact subsets of the half-plane, not on the half-plane.",
})}

// DirichletSeriesAtInfinity — along the reals, a Dirichlet series with
// bounded coefficients tends to its first coefficient.
var DirichletSeriesAtInfinity = dirichletSeriesAtInfinityThm{family.Add(registry.ProofEntry{
	Name: "DirichletSeriesAtInfinity",
	Key:  "prop_b2ee37da973dbe78",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → complex). ∀B ε:real.",
		Hypotheses: []string{
			"∀n:num. |a(n)| ≤ B",
			"&0 < ε",
		},
		Conclusion: "∃c:real. ∀σ:real. c ≤ σ ⇒ |dirichlet_series(a, &σ) - a(1)| < ε",
	}, func(arg *Argument, a *Arrow[Nat, Complex], B, ε *Expr[Real], coefficients, positive Fact) {
		nonnegative := arg.Have(
			"the bound on the first coefficient makes B nonnegative",
			"&0 ≤ B",
			ByArith(coefficients.At(arg.TermAs[Nat]("1"))))
		cutoff := arg.TermAs[Real]("&2 + B / ε")
		arg.Do(Witness(cutoff))
		σ := arg.FixAs[Real]("σ")
		beyond := arg.Assume()
		aboveOne := arg.Have(
			"the real argument is above one",
			"&1 < σ",
			ByArith(nonnegative, beyond, positive))
		gap := arg.Have(
			"the cutoff leaves a strict gap",
			"B / ε < σ - &1",
			ByArith(beyond))
		crossed := arg.Have(
			"multiply the gap inequality by the positive tolerance",
			"B < ε * (σ - &1)",
			ByArith(positive, gap, real_order_field.LessThanDivMulRight.At(B, arg.TermAs[Real]("σ - &1"), ε)))
		small := arg.Have(
			"the error bound is below the tolerance",
			"B / (σ - &1) < ε",
			ByArith(aboveOne, crossed))
		realPart := arg.Have(
			"the real part at the embedded point is σ",
			"re(&σ) = σ",
			By(complex_field.PartsOfReal.At(σ)))
		rightOfOne := arg.Have(
			"the embedded point lies to the right of one",
			"&1 < re(&σ)",
			By(Normalized, realPart, aboveOne))
		s := arg.TermAs[Complex]("&σ")
		v, sum := arg.UnpackAs[Complex](
			GroupPremises(coefficients, rightOfOne, BoundedCoefficientsConverge.At(a, B, s)),
			"v")
		parts := arg.Conjuncts(
			sum,
			"the series sums to v",
			"the error bound for v")
		value := arg.Have(
			"the Dirichlet series takes the value v",
			"dirichlet_series(a, &σ) = v",
			By(parts[0], DirichletSeriesValue.At(a, s, v)))
		bound := arg.Simplified(parts[1], Fwd(realPart))
		arg.Show(
			"the series value is within the tolerance of the first coefficient",
			value.Rw(),
			ByArith(bound, small))
	}),
})}
