// substitution.go — the substitution T ↦ Tᵈ: where it puts each
// coefficient and that it puts zero off the multiples of d, what it does to
// the binomial 1 − c·T, that it keeps the coefficients in the carrier, that
// it is multiplicative, that it takes a polynomial to a polynomial with the
// same value at one, and that it takes a counting sequence to d times its
// substitution.

package formal_series

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// SeriesSubstituteAtMultiple — substituting Tᵈ, d positive, puts the
// coefficient of Tʲ at the index d·j. That index is a multiple of d,
// and cancelling the nonzero d identifies the quotient the definition
// chooses with j.
var SeriesSubstituteAtMultiple = seriesSubstituteAtMultipleThm{family.Add(registry.ProofEntry{
	Name: "SeriesSubstituteAtMultiple",
	Key:  "prop_7a24466940d153c9",
	Build: family.Theorem(Statement{
		Binders:    "∀R:ring_ops(A). ∀p:(num → A). ∀d j:num.",
		Hypotheses: []string{"0 < d"},
		Conclusion: "series_substitute(R, p, d, d * j) = p(j)",
	}, func(arg *Argument, R *Expr[RingOps[A]], p *Arrow[Nat, A], d, j *Expr[Nat], positive Fact) {
		arg.Do(Unfold(SeriesSubstituteDef))
		nonzero := arg.Have(
			"the dilation is nonzero",
			"d ≠ 0",
			ByArith(positive))
		arg.Show(
			"cancellation identifies the chosen quotient",
			Simp(Fwd(nat_arith.MulEqLCancel)),
			By(Normalized, nonzero))
	}),
})}

// SeriesSubstituteOffMultiples — after substituting Tᵈ, an index that is
// not a multiple of d has coefficient zero: the definition's second branch.
var SeriesSubstituteOffMultiples = seriesSubstituteOffMultiplesThm{family.Add(registry.ProofEntry{
	Name: "SeriesSubstituteOffMultiples",
	Key:  "prop_f8f434d707e19b06",
	Build: family.Theorem(Statement{
		Binders:    "∀R:ring_ops(A). ∀p:(num → A). ∀d n:num.",
		Hypotheses: []string{"¬∃j:num. d * j = n"},
		Conclusion: "series_substitute(R, p, d, n) = R.zero",
	}, func(arg *Argument, R *Expr[RingOps[A]], p *Arrow[Nat, A], d, n *Expr[Nat], offMultiples Fact) {
		arg.Do(Unfold(SeriesSubstituteDef))
		arg.Show(
			"an index outside the dilation image has zero coefficient",
			By(Normalized, offMultiples))
	}),
})}

// SeriesSubstituteBinomial — substituting Tᵈ, d positive, into the binomial
// 1 - c T gives 1 - c Tᵈ. Substitution puts the coefficient of Tʲ at the
// index d·j, and d·j is 0 exactly at j = 0 and d exactly at j = 1; off the
// multiples of d the substituted coefficient is zero, and so is that of
// 1 - c Tᵈ, the index being neither 0 nor d.
var SeriesSubstituteBinomial = seriesSubstituteBinomialThm{family.Add(registry.ProofEntry{
	Name: "SeriesSubstituteBinomial",
	Key:  "prop_a32ab2276c0a478d",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀c:A. ∀d:num.",
		Hypotheses: []string{
			"c ∈ R.carrier",
			"0 < d",
		},
		Conclusion: "series_substitute(R, basis_vector(0) - c • basis_vector(1), d) = " +
			"basis_vector(0) - c • basis_vector(d)",
	},
		func(
			arg *Argument,
			ring comm_ring.CommRingFact[on.R],
			c *Member[A, on.R],
			d *Expr[Nat],
			positive Fact,
		) {
			R := arg.TermAs[RingOps[A]]("R")
			binomial := arg.TermAs[Fun[Nat, A]]("basis_vector(0) - c • basis_vector(1)")
			arg.Do(Funext())
			k := arg.FixAs[Nat]("k")
			endpoints := arg.Have(
				"d·j is 0 exactly at j = 0 and d exactly at j = 1",
				"∀j:num. (d * j = 0 ⇔ j = 0) ∧ (d * j = d ⇔ j = 1)",
				ByArith(positive, At(nat_arith.MulEqLCancel, d)))
			arg.Cases(arg.TermAs[Bool]("∃j:num. d * j = k"))
			arg.When(
				"at a multiple d·j the coefficient is that of the binomial at j",
				func(arg *Argument, multiple Fact) {
					j, index := arg.UnpackAs[Nat](multiple, "j")
					lookup := arg.Have(
						"substitution puts the coefficient of 1 - c T at j at the index d·j",
						"series_substitute(R, basis_vector(0) - c • basis_vector(1), d, d * j) = "+
							"(basis_vector(0) - c • basis_vector(1))(j)",
						By(positive, SeriesSubstituteAtMultiple.At(R, binomial, d, j)))
					arg.Show(
						"and the two coefficients of the binomial move from 0 and 1 to 0 and d",
						Simp(Rev(index), Fwd(lookup)),
						Simp(
							Fwd(vec_space.VecSubDef),
							Fwd(vec_space.VecScalarMulDef),
							Fwd(vec_space.BasisVectorDef),
							Fwd(endpoints)),
						Basic())
				})
			arg.Otherwise(
				"off the multiples of d both coefficients vanish",
				func(arg *Argument, absent Fact) {
					distinct := arg.Have(
						"the index is neither d·0 nor d·1",
						"d * 0 ≠ k ∧ d * 1 ≠ k",
						By(Normalized, absent))
					outside := arg.Have(
						"so it is neither 0 nor d",
						"k ≠ 0 ∧ k ≠ d",
						ByArith(distinct))
					vanishing := arg.Have(
						"the substituted coefficient is zero there",
						"series_substitute(R, basis_vector(0) - c • basis_vector(1), d, k) = R.zero",
						By(absent, SeriesSubstituteOffMultiples.At(R, binomial, d, k)))
					arg.Show(
						"and that of 1 - c Tᵈ is zero less c times zero",
						Simp(
							Fwd(vanishing),
							Fwd(vec_space.VecSubDef),
							Fwd(vec_space.VecScalarMulDef),
							Fwd(vec_space.BasisVectorDef)),
						ByArith(ring, c, outside))
				})
		}),
})}

// SeriesSubstituteLinearFactor — substituting Tᵈ, d positive, into the
// linear factor 1 − T gives 1 − Tᵈ: 1 − T is the binomial 1 − c·T at c = 1,
// which substitution takes to 1 − 1·Tᵈ (SeriesSubstituteBinomial).
var SeriesSubstituteLinearFactor = seriesSubstituteLinearFactorThm{family.Add(registry.ProofEntry{
	Name: "SeriesSubstituteLinearFactor",
	Key:  "prop_7933a26adf5d855b",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders:    "∀d:num.",
		Hypotheses: []string{"0 < d"},
		Conclusion: "series_substitute(R, «1−T», d) = «1−Tᵈ»(d)",
	},
		func(arg *Argument, ring comm_ring.CommRingFact[on.R], d *Expr[Nat], positive Fact) {
			first := arg.TermAs[Nat]("1")
			one := arg.MemberOf[on.R](arg.TermAs[A]("R.one"), comm_ring.OneIn.Read(ring))
			powers := arg.Have(
				"the coefficients of T and of Tᵈ lie in the ring",
				"∀i:num. basis_vector(1, i) ∈ R.carrier ∧ basis_vector(d, i) ∈ R.carrier",
				By(
					polynomial.BasisVectorOver.Read(ring).At(first),
					polynomial.BasisVectorOver.Read(ring).At(d),
					polynomial.PolynomialOverDef))
			arg.Show(
				"so T and Tᵈ are one times themselves, and substitution takes 1 − 1·T to 1 − 1·Tᵈ",
				By(
					positive,
					powers,
					vec_space.SmulOneOn.Read(ring).At(arg.TermAs[Fun[Nat, A]]("basis_vector(1)")),
					vec_space.SmulOneOn.Read(ring).At(arg.TermAs[Fun[Nat, A]]("basis_vector(d)")),
					SeriesSubstituteBinomial.Read(ring).At(one, d)))
		}),
})}

// SeriesSubstituteIn — substituting Tᵈ into a sequence with every term in
// the ring's carrier keeps every term there: each new coefficient is an old
// coefficient or zero.
var SeriesSubstituteIn = seriesSubstituteInThm{family.Add(registry.ProofEntry{
	Name: "SeriesSubstituteIn",
	Key:  "prop_d0fa1890008f9760",
	Build: family.Theorem(Statement{
		Binders:    "∀R:comm_ring_on(A). ∀p:(num → A). ∀d n:num.",
		Hypotheses: []string{"∀i:num. p(i) ∈ R.carrier"},
		Conclusion: "series_substitute(R, p, d, n) ∈ R.carrier",
	}, func(
		arg *Argument,
		ring comm_ring.CommRingFact[on.R],
		p *Arrow[Nat, A],
		d, n *Expr[Nat],
		coefficients Fact,
	) {
		arg.Do(Unfold(SeriesSubstituteDef))
		arg.Show(
			"each substituted coefficient is an old coefficient or zero",
			By(Normalized, comm_ring.ZeroIn.Read(ring), coefficients))
	}),
})}

// SeriesSubstituteMul — substituting Tᵈ, d positive, is multiplicative on
// sequences with every term in the ring's carrier. At a multiple d·k the
// convolution of the substituted sequences sums over the indices up to
// d·k; only the multiples contribute, and reindexing them by dilation
// gives the convolution of p and q at k. Off the multiples, two indices
// summing to n cannot both be multiples, so every summand has a zero factor.
var SeriesSubstituteMul = seriesSubstituteMulThm{family.Add(registry.ProofEntry{
	Name: "SeriesSubstituteMul",
	Key:  "prop_309b42a8459e337d",
	Build: family.Sections(Statement{
		Binders:    "∀R:comm_ring_on(A). ∀p q:(num → A). ∀d:num.",
		Hypotheses: []string{"0 < d", "∀i:num. p(i) ∈ R.carrier ∧ q(i) ∈ R.carrier"},
		Conclusion: "series_substitute(R, polynomial_mul(p, q), d) = " +
			"polynomial_mul(series_substitute(R, p, d), series_substitute(R, q, d))",
	},
		func(ctx *Script, headline string) *GoalStackNode {
			convolutionAtMultiple := ctx.Lemma(Statement{
				Binders:    "∀R:comm_ring_on(A). ∀p q:(num → A). ∀d k:num.",
				Hypotheses: []string{"0 < d", "∀i:num. p(i) ∈ R.carrier ∧ q(i) ∈ R.carrier"},
				Conclusion: "polynomial_mul(series_substitute(R, p, d), series_substitute(R, q, d), d * k) = " +
					"polynomial_mul(p, q, k)",
			}, func(
				arg *Argument,
				ring comm_ring.CommRingFact[on.R],
				p, q *Arrow[Nat, A],
				d, k *Expr[Nat],
				given Fact,
			) {
				R := arg.TermAs[RingOps[A]]("R")
				substituteIn := SeriesSubstituteIn.Read(ring).AsFact()
				parts := arg.Conjuncts(
					given,
					"the dilation is positive",
					"both coefficient sequences lie in the ring")
				positive, coefficients := parts[0], parts[1]
				bounds := arg.Have(
					"positive dilation preserves the summation bound",
					"∀j:num. j ≤ k ⇔ d * j ≤ d * k",
					ByArith(positive, At(nat_order.LessEqMulCancel, d)))
				dilated, dilatedDef := arg.LetAs[Set[Nat]]("dilated", "image(λj:num. d * j, {j:num | j ≤ k})")
				image := arg.Have(
					"the contributing indices are exactly the dilated segment",
					"dilated = {i:num | i ≤ d * k ∧ (∃j:num. d * j = i)}",
					dilatedDef.Rw(),
					BySets(bounds))
				injective := arg.Have(
					"dilation is injective",
					"injective_on({j:num | j ≤ k}, λj:num. d * j)",
					ByArith(positive, functions.InjectiveOnDef, At(nat_arith.MulEqLCancel, d)))
				F, Fdef := arg.LetAs[Fun[Nat, A]](
					"F", "λi:num. R.mul(series_substitute(R, p, d, i), series_substitute(R, q, d, d * k - i))")
				inside := arg.Have(
					"the summands lie in the ring",
					"∀i:num. F(i) ∈ R.carrier",
					Fdef.Rw(),
					By(comm_ring.MulIn.Read(ring), coefficients, substituteIn.At(p, d), substituteIn.At(q, d)))
				vanishes := arg.Have(
					"only multiples of d contribute",
					"∀i:num. ¬(∃j:num. d * j = i) ⇒ F(i) = R.zero",
					Fdef.Rw(),
					By(
						comm_ring.MulLeftZeroOn.Read(ring),
						coefficients,
						At(SeriesSubstituteOffMultiples, R, p, d),
						substituteIn.At(q, d)))
				subset := arg.Have(
					"the dilated segment lies in the segment up to d·k",
					"dilated ⊆ {i:num | i ≤ d * k}",
					BySets(image))
				outside := arg.Have(
					"off the dilated segment every summand vanishes",
					"∀i:num. i ∈ {j:num | j ≤ d * k} ∧ i ∉ dilated ⇒ F(i) = R.zero",
					BySets(vanishes, image))
				regular := module.RegularModuleOn.Read(ring)
				restrict := arg.Have(
					"restrict the sum to its contributing indices",
					"module_sum(R.add, R.zero, {i:num | i ≤ d * k}, F) = module_sum(R.add, R.zero, dilated, F)",
					By(
						subset,
						outside,
						inside,
						num_segment.FiniteBelow.At(arg.TermAs[Nat]("d * k")),
						module.ModuleSumSupport.Read(regular).At(arg.TermAs[Set[Nat]]("{i:num | i ≤ d * k}"), dilated, F)))
				reindex := arg.Have(
					"reindex the finite sum by dilation",
					"module_sum(R.add, R.zero, dilated, F) = "+
						"module_sum(R.add, R.zero, {j:num | j ≤ k}, λj:num. F(d * j))",
					dilatedDef.Rw(),
					By(
						inside,
						injective,
						num_segment.FiniteBelow.At(k),
						module.ModuleSumImage.Read(regular).At(
							arg.TermAs[Set[Nat]]("{j:num | j ≤ k}"), arg.TermAs[Fun[Nat, Nat]]("λj:num. d * j"), F)))
				terms := arg.Have(
					"the reindexed summands are the original convolution summands",
					"∀j:num. F(d * j) = R.mul(p(j), q(k - j))",
					Simp(Fwd(Fdef), Rev(nat_monus.LeftSubDistrib)),
					Basic(),
					By(positive, At(SeriesSubstituteAtMultiple, R, p, d), At(SeriesSubstituteAtMultiple, R, q, d)))
				arg.Show(
					"the two convolution coefficients have the same finite sum",
					Simp(Fwd(polynomial.PolynomialMulDef)),
					Simp(Rev(Fdef), Fwd(restrict), Fwd(reindex), Fwd(terms)),
					Basic())
			})
			convolutionOffMultiples := ctx.Lemma(Statement{
				Binders:    "∀R:comm_ring_on(A). ∀p q:(num → A). ∀d n:num.",
				Hypotheses: []string{"∀i:num. p(i) ∈ R.carrier ∧ q(i) ∈ R.carrier", "¬∃j:num. d * j = n"},
				Conclusion: "polynomial_mul(series_substitute(R, p, d), series_substitute(R, q, d), n) = R.zero",
			}, func(
				arg *Argument,
				ring comm_ring.CommRingFact[on.R],
				p, q *Arrow[Nat, A],
				d, n *Expr[Nat],
				given Fact,
			) {
				R := arg.TermAs[RingOps[A]]("R")
				substituteIn := SeriesSubstituteIn.Read(ring).AsFact()
				parts := arg.Conjuncts(
					given,
					"the original coefficients lie in the ring",
					"the target index is not a multiple")
				coefficients, notMultiple := parts[0], parts[1]
				addIndices := arg.Have(
					"two contributing multiples would make their sum a multiple",
					"∀i j k:num. i ≤ n ∧ d * j = i ∧ d * k = n - i ⇒ d * (j + k) = n",
					ByArith())
				missing := arg.Have(
					"at least one factor vanishes in each summand",
					"∀i:num. i ≤ n ⇒ ¬(∃j:num. d * j = i) ∨ ¬∃j:num. d * j = n - i",
					Derive(func(arg *Argument) {
						i := arg.FixAs[Nat]("i")
						bound := arg.Assume()
						both := arg.SupposeNot()
						j, k, witnesses := arg.Obtain2As[Nat, Nat](
							"if neither factor vanishes, both indices are multiples",
							"∃j k:num. d * j = i ∧ d * k = n - i",
							By(Normalized, both),
							Named("j", "k"))
						multiple := arg.Have(
							"the two witness indices make n a multiple",
							"d * (j + k) = n",
							By(bound, witnesses, addIndices.At(i, j, k)))
						arg.Show(
							"n cannot be a multiple",
							By(Normalized, notMultiple, multiple))
					}))
				inside := arg.Have(
					"the substituted coefficients lie in the ring",
					"∀i:num. series_substitute(R, p, d, i) ∈ R.carrier ∧ series_substitute(R, q, d, i) ∈ R.carrier",
					By(coefficients, substituteIn.At(p, d), substituteIn.At(q, d)))
				zero := arg.Have(
					"all summands are zero",
					"∀i:num. i ≤ n ⇒ R.mul(series_substitute(R, p, d, i), series_substitute(R, q, d, n - i)) = R.zero",
					By(
						comm_ring.MulLeftZeroOn.Read(ring),
						comm_ring.MulRightZeroOn.Read(ring),
						missing,
						inside,
						At(SeriesSubstituteOffMultiples, R, p, d),
						At(SeriesSubstituteOffMultiples, R, q, d)))
				arg.Show(
					"the finite convolution sum is zero",
					Simp(Fwd(polynomial.PolynomialMulDef)),
					BySets(
						zero,
						num_segment.FiniteBelow.At(n),
						module.ModuleSumZero.Read(module.RegularModuleOn.Read(ring)).At(
							arg.TermAs[Set[Nat]]("{i:num | i ≤ n}"),
							arg.TermAs[Fun[Nat, A]](
								"λi:num. R.mul(series_substitute(R, p, d, i), series_substitute(R, q, d, n - i))"))))
			})
			return ctx.Theorem(headline, func(
				arg *Argument,
				ring comm_ring.CommRingFact[on.R],
				p, q *Arrow[Nat, A],
				d *Expr[Nat],
				given Fact,
			) {
				R := arg.TermAs[RingOps[A]]("R")
				product := arg.TermAs[Fun[Nat, A]]("polynomial_mul(p, q)")
				arg.Do(Funext())
				n := arg.FixAs[Nat]("n")
				arg.Cases(arg.TermAs[Bool]("∃j:num. d * j = n"))
				arg.When(
					"an index in the dilation image reduces to the original coefficient",
					func(arg *Argument, multiple Fact) {
						j, index := arg.UnpackAs[Nat](multiple, "j")
						arg.Show(
							"lookup and reindexing give the same coefficient",
							By(
								ring,
								index,
								given,
								SeriesSubstituteAtMultiple.At(R, product, d, j),
								At(convolutionAtMultiple, R, p, q, d, j)))
					})
				arg.Otherwise(
					"outside the dilation image both coefficients vanish",
					func(arg *Argument, absent Fact) {
						arg.Show(
							"both sides have zero coefficient",
							By(
								ring,
								absent,
								given,
								SeriesSubstituteOffMultiples.At(R, product, d, n),
								At(convolutionOffMultiples, R, p, q, d, n)))
					})
			})
		}),
})}

// SeriesSubstitutePolynomial — substituting Tᵈ, d positive, into a
// polynomial over the ring gives a polynomial with the same value at one.
// Dilation carries the old support onto the new one, which is finite as
// the image of a finite set; and the value at one sums the coefficients
// over the support (EvalOneSupport), a sum dilation reindexes.
var SeriesSubstitutePolynomial = seriesSubstitutePolynomialThm{family.Add(registry.ProofEntry{
	Name: "SeriesSubstitutePolynomial",
	Key:  "prop_2c78eb9d1f4dac4b",
	Build: family.Sections(Statement{
		Binders:    "∀R:comm_ring_on(A). ∀p:(num → A). ∀d:num.",
		Hypotheses: []string{"0 < d", "polynomial_over(R.carrier, p)"},
		Conclusion: "polynomial_over(R.carrier, series_substitute(R, p, d)) ∧ " +
			"polynomial_eval(series_substitute(R, p, d), R.one) = polynomial_eval(p, R.one)",
	},
		func(ctx *Script, headline string) *GoalStackNode {
			substituteSupport := ctx.Lemma(Statement{
				Binders:    "∀R:ring_ops(A). ∀p:(num → A). ∀d:num.",
				Hypotheses: []string{"0 < d"},
				Conclusion: "fun_support(R.zero, λn:num. series_substitute(R, p, d, n)) = " +
					"image(λi:num. d * i, fun_support(R.zero, p))",
			}, func(arg *Argument, R *Expr[RingOps[A]], p *Arrow[Nat, A], d *Expr[Nat], positive Fact) {
				arg.Show(
					"dilation maps the old support exactly onto the new support",
					BySets(
						positive,
						At(SeriesSubstituteAtMultiple, R, p, d),
						At(SeriesSubstituteOffMultiples, R, p, d)))
			})
			return ctx.Theorem(headline, func(
				arg *Argument,
				ring comm_ring.CommRingFact[on.R],
				p *Arrow[Nat, A],
				d *Expr[Nat],
				given Fact,
			) {
				R := arg.TermAs[RingOps[A]]("R")
				zero, carrier := arg.TermAs[A]("R.zero"), arg.TermAs[Set[A]]("R.carrier")
				substituted := arg.TermAs[Fun[Nat, A]]("series_substitute(R, p, d)")
				support, dilation :=
					arg.TermAs[Set[Nat]]("fun_support(R.zero, p)"), arg.TermAs[Fun[Nat, Nat]]("λi:num. d * i")
				supportFinite := arg.Have(
					"p is a polynomial, so its support is finite",
					"finite(fun_support(R.zero, p))",
					By(given, polynomial.PolynomialFiniteSupport.At(zero, carrier, p)))
				coefficients := arg.Have(
					"every coefficient of p lies in the ring, and so does every substituted coefficient",
					"∀i:num. p(i) ∈ R.carrier ∧ series_substitute(R, p, d, i) ∈ R.carrier",
					By(
						given,
						polynomial.PolynomialFiniteSupport.At(zero, carrier, p),
						SeriesSubstituteIn.Read(ring).AsFact().At(p, d)))
				imageFinite := arg.Have(
					"the dilated support is finite",
					"finite(fun_support(R.zero, λi:num. series_substitute(R, p, d, i)))",
					By(
						supportFinite,
						given,
						At(substituteSupport, R, p, d),
						finite_set.FiniteImage.At(dilation, support)))
				injective := arg.Have(
					"dilation is injective on the support",
					"injective_on(fun_support(R.zero, p), λi:num. d * i)",
					ByArith(given, functions.InjectiveOnDef, At(nat_arith.MulEqLCancel, d)))
				arg.Show(
					"the substituted series is a polynomial, and substitution preserves evaluation at one",
					SplitConjAll(
						Case(
							"finite support and coefficient membership make the substituted series a polynomial",
							By(imageFinite, coefficients, polynomial.PolynomialFiniteSupport.At(zero, carrier, substituted))),
						Case(
							"both values at one are coefficient sums, and dilation reindexes the one into the other",
							CalcEq(
								Leg(
									arg.TermAs[A](
										"module_sum(R.add, "+
											"    R.zero, "+
											"    fun_support(R.zero, λi:num. series_substitute(R, p, d, i)), "+
											"    series_substitute(R, p, d))"),
									"the value at one sums the substituted coefficients over their support",
									By(coefficients, polynomial_evaluation.EvalOneSupport.Read(ring).At(substituted))),
								Leg(
									arg.TermAs[A](
										"module_sum(R.add, "+
											"    R.zero, "+
											"    image(λi:num. d * i, fun_support(R.zero, p)), "+
											"    series_substitute(R, p, d))"),
									"that support is the dilated support of p",
									By(given, At(substituteSupport, R, p, d))),
								Leg(
									arg.TermAs[A](
										"module_sum(R.add, R.zero, fun_support(R.zero, p), λi:num. series_substitute(R, p, d, d * i))"),
									"reindex the sum along the injective dilation",
									By(
										injective,
										supportFinite,
										coefficients,
										module.ModuleSumImage.Read(module.RegularModuleOn.Read(ring)).At(support, dilation, substituted))),
								Leg(
									arg.TermAs[A]("module_sum(R.add, R.zero, fun_support(R.zero, p), p)"),
									"the coefficient at d * i is the coefficient of p at i",
									By(given, At(SeriesSubstituteAtMultiple, R, p, d), module.ModuleSumCongruence)),
								FinalLeg(
									"which is the value of p at one",
									By(coefficients, polynomial_evaluation.EvalOneSupport.Read(ring).At(p))),
							))))
			})
		}),
})}

// RecurrenceSubstitute — substituting Tᵈ, d positive, takes a counting
// sequence m to d times the substituted m, by the Euler equation: d times the
// substituted m, convolved with the substituted a, is d times the substitution
// of m·a (SeriesSubstituteMul), that is d times the substituted Euler
// derivative of a. At an index d·j that and the Euler derivative of the
// substituted a are both d·j times a(j), and off the multiples of d both
// vanish.
var RecurrenceSubstitute = recurrenceSubstituteThm{family.Add(registry.ProofEntry{
	Name: "RecurrenceSubstitute",
	Key:  "prop_1121c0c84209d8cc",
	Build: family.Theorem(Statement{
		Binders:    "∀R:comm_ring_on(A). ∀a m:(num → A). ∀d:num.",
		Hypotheses: []string{"0 < d", "series_recurrence(R, a, m)"},
		Conclusion: "series_recurrence(R, " +
			"    series_substitute(R, a, d), " +
			"    λn:num. «numeral»(d) * series_substitute(R, m, d, n))",
	}, func(
		arg *Argument,
		ring comm_ring.CommRingFact[on.R],
		a, m *Arrow[Nat, A],
		d *Expr[Nat],
		positive, recurrence Fact,
	) {
		R := arg.TermAs[RingOps[A]]("R")
		data := arg.Simplified(recurrence, Fwd(RecurrenceEuler))
		coefficients := arg.Have(
			"both sequences take values in the ring",
			"∀n:num. a(n) ∈ R.carrier ∧ m(n) ∈ R.carrier",
			By(data))
		numerals := arg.Have(
			"every numeral lies in the ring",
			"∀k:num. «numeral»(k) ∈ R.carrier",
			By(comm_ring.OneIn.Read(ring), comm_monoid.PowIn.Read(comm_ring.AddMonoidOn.Read(ring))))
		origin := arg.Have(
			"substitution keeps the coefficient at 0, which is the multiple d·0",
			"∀p:(num → A). series_substitute(R, p, d, 0) = p(0)",
			arg.ForEach(func(p *Expr[Fun[Nat, A]]) Action {
				return By(
					Normalized,
					positive,
					nat_arith.MulZero.At(d),
					SeriesSubstituteAtMultiple.At(R, p, d, arg.TermAs[Nat]("0")))
			}))
		substitutedIn := arg.Have(
			"the substituted sequences stay in the ring",
			"∀n:num. series_substitute(R, a, d, n) ∈ R.carrier ∧ series_substitute(R, m, d, n) ∈ R.carrier",
			By(data, SeriesSubstituteIn.Read(ring)))
		arg.Show(
			"read as an Euler equation, the clauses of the substituted series come from those of a",
			Simp(Fwd(RecurrenceEuler)),
			SplitConjAll(Case(
				"the constant coefficient stays one",
				By(Normalized, data, origin.At(a))),
				Case(
					"the counting sequence stays zero at zero",
					By(data, origin.At(m), numerals.At(d), comm_ring.MulRightZeroOn.Read(ring))),
				Case(
					"the substituted coefficients lie in the ring",
					By(substitutedIn)),
				Case(
					"and so do their multiples by d",
					By(numerals, substitutedIn, comm_ring.MulIn.Read(ring))),
				Case(
					"the substituted Euler equation is d times the substitution of the Euler equation of a",
					Derive(func(arg *Argument) {
						scaledCounts := arg.Have(
							"the new counting sequence is the scalar d times the substituted m",
							"(λn:num. «numeral»(d) * series_substitute(R, m, d, n)) = "+
								"«numeral»(d) • series_substitute(R, m, d)",
							Funext(),
							Simp(Fwd(vec_space.VecScalarMulDef)),
							Basic())
						series, counts :=
							arg.TermAs[Fun[Nat, A]]("series_substitute(R, a, d)"),
							arg.TermAs[Fun[Nat, A]]("series_substitute(R, m, d)")
						scalar := arg.TermAs[A]("«numeral»(d)")
						scalarOut := arg.Have(
							"the scalar d passes out of the convolution",
							"polynomial_mul(λn:num. «numeral»(d) * series_substitute(R, m, d, n), "+
								"    series_substitute(R, a, d)) = "+
								"«numeral»(d) • polynomial_mul(series_substitute(R, m, d), series_substitute(R, a, d))",
							By(
								numerals.At(d),
								substitutedIn,
								scaledCounts,
								comm_ring.MulIn.Read(ring),
								polynomial.PolynomialMulComm.Read(ring).At(
									arg.TermAs[Fun[Nat, A]]("λn:num. «numeral»(d) * series_substitute(R, m, d, n)"), series),
								polynomial.PolynomialMulScalar.Read(ring).AsFact().At(scalar, series, counts),
								polynomial.PolynomialMulComm.Read(ring).At(series, counts)))
						weights := arg.Have(
							"coefficient by coefficient, n times the substituted "+
								"a is d times the substituted Euler derivative of a",
							"∀n:num. "+
								"    «numeral»(n) * series_substitute(R, a, d, n) = "+
								"    «numeral»(d) * series_substitute(R, «euler»(a), d, n)",
							Derive(func(arg *Argument) {
								n := arg.FixAs[Nat]("n")
								euler := arg.TermAs[Fun[Nat, A]]("«euler»(a)")
								arg.Cases(arg.TermAs[Bool]("∃j:num. d * j = n"))
								arg.When(
									"at a multiple d·j both sides are d·j times a(j)",
									func(arg *Argument, multiple Fact) {
										j, index := arg.UnpackAs[Nat](multiple, "j")
										arg.Show(
											"the numeral d·j is the product of the numerals d and j",
											index.RwRev(),
											Simp(Fwd(SeriesSubstituteAtMultiple), Fwd(comm_ring.AddPowMulOn.Read(ring))),
											ByArith(ring, coefficients.At(j)))
									})
								arg.Otherwise(
									"off the multiples of d both sides vanish",
									func(arg *Argument, absent Fact) {
										arg.Show(
											"a numeral times zero is zero",
											By(
												absent,
												numerals.At(n),
												numerals.At(d),
												SeriesSubstituteOffMultiples.At(R, a, d, n),
												SeriesSubstituteOffMultiples.At(R, euler, d, n),
												comm_ring.MulRightZeroOn.Read(ring)))
									})
							}))
						multiplicative := arg.Have(
							"substitution is multiplicative, so the substituted "+
								"convolution is the substituted Euler derivative of a",
							"polynomial_mul(series_substitute(R, m, d), series_substitute(R, a, d)) = "+
								"series_substitute(R, «euler»(a), d)",
							By(ring, positive, data, SeriesSubstituteMul.Read(ring).AsFact().At(m, a, d)))
						arg.Do(scalarOut.Rw(), multiplicative.Rw(), Funext())
						arg.FixAs[Nat]("n")
						arg.Show(
							"which is d times the substitution at n",
							Simp(Fwd(vec_space.VecScalarMulDef)),
							By(weights))
					})),
			))
	}),
})}

// EvalSeriesSubstitute — substituting T ^ d for the variable of a polynomial c
// and evaluating at x is evaluating c at x ^ d. Both are the sum over the
// support of c, reindexed by d: the support of the substitution is the support
// of c dilated by d, and at a multiple d * i the term is c(i) times the i-th
// power of x ^ d.
var EvalSeriesSubstitute = evalSeriesSubstituteThm{family.Add(registry.ProofEntry{
	Name: "EvalSeriesSubstitute",
	Key:  "prop_8709bab547478440",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). ∀c:(num → A). ∀d:num. ∀x:A.",
		Hypotheses: []string{
			"0 < d",
			"polynomial_over(R.carrier, c)",
			"x ∈ R.carrier",
		},
		Conclusion: "polynomial_eval(series_substitute(R, c, d), x) = " +
			"polynomial_eval(c, monoid_pow(R.mul, R.one, x, d))",
	}, func(
		a *Argument,
		ring comm_ring.CommRingFact[on.R],
		c *Arrow[Nat, A],
		d *Expr[Nat],
		x *Expr[A],
		positive, over, xInR Fact,
	) {
		R := a.TermAs[RingOps[A]]("R")
		zero, carrier := a.TermAs[A]("R.zero"), a.TermAs[Set[A]]("R.carrier")
		support, dilation :=
			a.TermAs[Set[Nat]]("fun_support(R.zero, c)"), a.TermAs[Fun[Nat, Nat]]("λi:num. d * i")
		regular := module.RegularModuleOn.Read(ring)
		coefficients := a.Have(
			"the coefficients of c and of its substitution lie in R",
			"∀i:num. c(i) ∈ R.carrier ∧ series_substitute(R, c, d, i) ∈ R.carrier",
			By(over, polynomial.PolynomialOverDef, SeriesSubstituteIn.Read(ring)))
		terms := a.Have(
			"so do the terms of its value at x",
			"∀n:num. series_substitute(R, c, d, n) * monoid_pow(R.mul, R.one, x, n) ∈ R.carrier",
			By(
				coefficients,
				xInR,
				comm_ring.MulIn.Read(ring),
				comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ring))))
		dilated := a.Have(
			"the support of the substitution is the support of c dilated by d",
			"fun_support(R.zero, λn:num. series_substitute(R, c, d, n)) = "+
				"image(λi:num. d * i, fun_support(R.zero, c))",
			BySets(
				positive,
				At(SeriesSubstituteAtMultiple, R, c, d),
				At(SeriesSubstituteOffMultiples, R, c, d)))
		injective := a.Have(
			"dilation by d is injective",
			"injective_on(fun_support(R.zero, c), λi:num. d * i)",
			ByArith(positive, functions.InjectiveOnDef, At(nat_arith.MulEqLCancel, d)))
		reindexed := a.Have(
			"at a multiple d * i the term is c(i) times the i-th power of x ^ d",
			"∀i:num. "+
				"    series_substitute(R, c, d, d * i) * monoid_pow(R.mul, R.one, x, d * i) = "+
				"    c(i) * monoid_pow(R.mul, R.one, monoid_pow(R.mul, R.one, x, d), i)",
			a.ForEach(func(i *Expr[Nat]) Action {
				return By(
					positive,
					xInR,
					SeriesSubstituteAtMultiple.At(R, c, d, i),
					comm_monoid.PowPowOn.Read(comm_ring.MulMonoidOn.Read(ring)).AsFact().At(x, d, i))
			}))
		a.Show(
			"sum over the support of the substitution, reindex along "+
				"the dilation, and read the terms as those of c at x ^ d",
			CalcEq(
				Leg(
					a.TermAs[A](
						"module_sum(R.add, "+
							"    R.zero, "+
							"    image(λi:num. d * i, fun_support(R.zero, c)), "+
							"    λn:num. series_substitute(R, c, d, n) * monoid_pow(R.mul, R.one, x, n))"),
					"the value sums the terms over the support, the dilated support of c",
					By(dilated, polynomial_evaluation.PolynomialEvalDef)),
				Leg(
					a.TermAs[A](
						"module_sum(R.add, "+
							"    R.zero, "+
							"    fun_support(R.zero, c), "+
							"    λi:num. series_substitute(R, c, d, d * i) * monoid_pow(R.mul, R.one, x, d * i))"),
					"reindex along the injective dilation, the support of c being finite",
					By(
						over,
						injective,
						terms,
						polynomial.PolynomialFiniteSupport.At(zero, carrier, c),
						module.ModuleSumImage.Read(regular).At(
							support,
							dilation,
							a.TermAs[Fun[Nat, A]]("λn:num. series_substitute(R, c, d, n) * monoid_pow(R.mul, R.one, x, n)")))),
				Leg(
					a.TermAs[A](
						"module_sum(R.add, "+
							"    R.zero, "+
							"    fun_support(R.zero, c), "+
							"    λi:num. c(i) * monoid_pow(R.mul, R.one, monoid_pow(R.mul, R.one, x, d), i))"),
					"term by term",
					By(
						reindexed,
						module.ModuleSumCongruence.At(
							a.TermAs[Op[A]]("R.add"),
							zero,
							support,
							a.TermAs[Fun[Nat, A]](
								"λi:num. series_substitute(R, c, d, d * i) * monoid_pow(R.mul, R.one, x, d * i)"),
							a.TermAs[Fun[Nat, A]](
								"λi:num. c(i) * monoid_pow(R.mul, R.one, monoid_pow(R.mul, R.one, x, d), i)")))),
				FinalLeg(
					"which is the value of c at x ^ d",
					By(polynomial_evaluation.PolynomialEvalDef))))
	}),
})}
