// divisor_sum.go — φ(n) as the size of the set it counts, Gauss's
// identity (the totients of the divisors of n add up to n), the
// divisors of a product of two coprime numbers, and the sum of a
// multiplicative function over them.

package totient

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_gcd"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/registry"
)

// TotientHasSize — φ(n) is the size of the set it counts: the residues below
// n coprime to n lie among the finitely many residues below n, so they are
// finite, and φ(n) is their number by definition.
var TotientHasSize = totientHasSizeThm{family.Add(registry.ProofEntry{
	Name: "TotientHasSize",
	Key:  "prop_15824bfb73c2bb97",
	Build: family.Theorem(
		"∀n:num. has_size({a:num | a < n ∧ nat_coprime(a, n)}, totient(n))",
		func(a *Argument, n *Expr[Nat]) {
			coprimes := a.TermAs[Set[Nat]]("{a:num | a < n ∧ nat_coprime(a, n)}")
			a.Show(
				"a part of the finitely many residues below n, counted by φ(n)",
				By(
					TotientDef.At(n),
					cardinality.HasSizeDef.At(coprimes, a.TermAs[Nat]("totient(n)")),
					finite_set.FiniteSubset.At(coprimes, a.TermAs[Set[Nat]]("{a:num | a < n}")),
					num_segment.FiniteBelowStrict.At(n),
					set_basic.SubsetDef))
		}),
})}

// GcdClassCount — for a divisor d of n > 0, the residues a below n with
// gcd(a, n)·d = n, those whose gcd with n is the complementary divisor e = n/d,
// are φ(d) in number. They are exactly e·b for the b below d coprime to d,
// since gcd(e·b, e·d) = e·gcd(b, d) is e just when gcd(b, d) = 1; so the class
// is the image of the residues φ(d) counts under b ↦ e·b, which is one-to-one.
var GcdClassCount = gcdClassCountThm{family.Add(registry.ProofEntry{
	Name: "GcdClassCount",
	Key:  "prop_36e392fcf58b15e6",
	Build: family.Theorem(Statement{
		Binders: "∀n d:num.",
		Hypotheses: []string{
			"0 < n",
			"d ∣ n",
		},
		Conclusion: "has_size(«class», totient(d))",
		Abbrev: Abbrev{
			{Name: "class", Text: "{a:num | a < n ∧ nat_gcd(a, n) * d = n}"},
			{Name: "reduced", Text: "{b:num | b < d ∧ nat_coprime(b, d)}"},
		},
	}, func(a *Argument, n, d *Expr[Nat], positive, divides Fact) {
		e, cofactor := a.ObtainAs[Nat](
			"n is d taken e times",
			"∃e:num. n = d * e",
			By(divides, nat_divides.DividesFactor.At(d, n)))
		nonzero := a.Have(
			"neither d nor e is 0, their product n being positive",
			"d ≠ 0 ∧ e ≠ 0",
			ByArith(positive, cofactor, nat_arith.MulEqZero.At(d, e)))

		members := a.Have(
			"a residue lies in the class exactly when it is e·b for some b below d coprime to d",
			"∀a:num. a < n ∧ nat_gcd(a, n) * d = n ⇔ (∃b:num. a = e * b ∧ b < d ∧ nat_coprime(b, d))",
			Derive(func(res *Argument) {
				a := res.FixAs[Nat]("a")
				res.Iff()
				res.Forward(
					"a residue of the class is e times a residue below d coprime to d",
					func(fwd *Argument, inClass Fact) {
						g := fwd.TermAs[Nat]("nat_gcd(a, n)")
						gcdIsE := fwd.Have(
							"gcd(a, n)·d = n = d·e, and cancelling d ≠ 0 leaves gcd(a, n) = e",
							"nat_gcd(a, n) = e",
							By(
								Normalized,
								cofactor,
								nonzero,
								inClass,
								nat_arith.MulEqLCancel.At(d, g, e),
								nat_arith.MulSym.At(g, d)))
						c, multiple := fwd.ObtainAs[Nat](
							"e, the gcd, divides a: a = e·c",
							"∃c:num. a = e * c",
							By(Normalized, gcdIsE, nat_gcd.Gcd.At(a, n), nat_divides.DividesFactor.At(e, a)))
						below := fwd.Have(
							"e·c = a < n = e·d puts c below d",
							"c < d",
							By(
								Normalized,
								multiple,
								cofactor,
								inClass,
								nat_order.LessThanMulCancel.At(e, c, d),
								nat_arith.MulSym.At(d, e)))
						gcdOne := fwd.Have(
							"e·gcd(c, d) = gcd(e·c, e·d) = gcd(a, n) = e, and cancelling e ≠ 0 leaves gcd(c, d) = 1",
							"nat_gcd(c, d) = 1",
							By(
								Normalized,
								multiple,
								cofactor,
								gcdIsE,
								nonzero,
								nat_gcd.GcdMulLeft.At(e, c, d),
								nat_arith.MulEqLCancel.At(e, fwd.TermAs[Nat]("nat_gcd(c, d)"), fwd.TermAs[Nat]("1")),
								nat_arith.MulOne.At(e),
								nat_arith.MulSym.At(d, e)))
						fwd.Take(c)
						fwd.Show(
							"so a is e·c, with c below d and coprime to d",
							By(multiple, below, gcdOne, nat_gcd.CoprimeDef.At(c, d)))
					})
				res.Backward(
					"e times a residue below d coprime to d lies in the class",
					func(bwd *Argument, isMultiple Fact) {
						m, spelled := bwd.UnpackAs[Nat](isMultiple, "m")
						below := bwd.Have(
							"a = e·m < e·d = n",
							"a < n",
							By(
								Normalized,
								cofactor,
								nonzero,
								spelled,
								nat_order.LessThanMulCancel.At(e, m, d),
								nat_arith.MulSym.At(d, e)))
						gcdIsE := bwd.Have(
							"gcd(a, n) = gcd(e·m, e·d) = e·gcd(m, d) = e, m being coprime to d",
							"nat_gcd(a, n) = e",
							By(
								Normalized,
								cofactor,
								spelled,
								nat_gcd.GcdMulLeft.At(e, m, d),
								nat_gcd.CoprimeDef.At(m, d),
								nat_arith.MulSym.At(d, e),
								nat_arith.MulOne.At(e)))
						bwd.Show(
							"so gcd(a, n)·d = e·d = n, and a lies in the class",
							By(Normalized, below, gcdIsE, cofactor, nat_arith.MulSym.At(d, e)))
					})
			}))

		reduced := a.TermAs[Set[Nat]]("«reduced»")
		scale := a.TermAs[Fun[Nat, Nat]]("λb:num. e * b")
		class := a.Have(
			"so the class is the image of the residues below d coprime to d under b ↦ e·b",
			"«class» = image(λb:num. e * b, «reduced»)",
			BySets(members))
		oneToOne := a.Have(
			"multiplying by e ≠ 0 is one-to-one",
			"injective_on(«reduced», λb:num. e * b)",
			By(nonzero, functions.InjectiveOnDef, nat_arith.MulEqLCancel))
		a.Show(
			"so the class is a one-to-one image of the φ(d) residues below d coprime to d",
			By(
				class,
				oneToOne,
				TotientHasSize.At(d),
				cardinality.HasSizeImageInj.At(scale, reduced, a.TermAs[Nat]("totient(d)"))))
	}),
})}

// DivisorSum — Gauss's identity: the totients of the divisors of n add up to
// n. Every residue a lies in the class of exactly one divisor d of n, the one
// with gcd(a, n)·d = n, the cofactor of gcd(a, n) in n; the class of d has
// φ(d) members (GcdClassCount); so the n residues below n, counted class by
// class, number Σ_{d ∣ n} φ(d).
var DivisorSum = divisorSumThm{family.Add(registry.ProofEntry{
	Name: "DivisorSum",
	Key:  "prop_a9393d5b85fc1891",
	Build: family.Theorem(Statement{
		Binders: "∀n:num.",
		Hypotheses: []string{
			"0 < n",
		},
		Conclusion: "Σ_{d∈{d:num | d ∣ n}} totient(d) = n",
	}, func(a *Argument, n *Expr[Nat], positive Fact) {
		oneClass := a.Have(
			"every a lies in the class of exactly one divisor: "+
				"gcd(a, n)·d = n pins d as the cofactor of gcd(a, n) in n",
			"∀a:num. ∃!d:num. d ∣ n ∧ nat_gcd(a, n) * d = n",
			Derive(func(res *Argument) {
				a := res.FixAs[Nat]("a")
				g := res.TermAs[Nat]("nat_gcd(a, n)")
				c, cofactor := res.ObtainAs[Nat](
					"gcd(a, n) divides n, which is gcd(a, n) taken c times",
					"∃c:num. n = nat_gcd(a, n) * c",
					By(nat_gcd.Gcd.At(a, n), nat_divides.DividesFactor.At(g, n)))
				nonzero := res.Have(
					"gcd(a, n) is not 0, n being positive",
					"nat_gcd(a, n) ≠ 0",
					ByArith(positive, cofactor, nat_arith.MulEqZero.At(g, c)))
				res.Take(c)
				res.Do(SplitConj(
					Case(
						"c is such a divisor, dividing gcd(a, n)·c = n",
						By(Normalized, cofactor, nat_divides.DividesOwnMultiple.At(c, g))),
					Case(
						"gcd(a, n)·y = n = gcd(a, n)·c cancels to y = c",
						res.ForEach(func(y *Expr[Nat]) Action {
							return By(Normalized, nonzero, cofactor, nat_arith.MulEqLCancel.At(g, y, c))
						}))))
			}))

		residues := a.TermAs[Set[Nat]]("{a:num | a < n}")
		a.Show(
			"Σ φ(d) counts the residues below n class by class, and there are n of them",
			CalcEq(
				Leg(
					a.TermAs[Nat]("card({a:num | a < n})"),
					"each residue in exactly one class, and the class of d of size φ(d)",
					By(
						num_segment.FiniteBelowStrict.At(n),
						oneClass,
						positive,
						GcdClassCount,
						nat_sum.CardByFibres.At(
							residues,
							a.TermAs[Set[Nat]]("{d:num | d ∣ n}"),
							a.TermAs[Fun2[Nat, Nat, Bool]]("λa:num. λd:num. nat_gcd(a, n) * d = n"),
							a.TermAs[Fun[Nat, Nat]]("totient")))),
				FinalLeg(
					"there are n residues below n",
					By(num_segment.HasSizeBelowStrict.At(n), cardinality.CardOfSized.At(residues, n)))))
	}),
})}

// DivisorsOfCoprimeProduct — for coprime m and n, the divisors of m·n are
// the products d·e of a divisor d of m and a divisor e of n, each divisor
// arising from exactly one pair. Coprime cancellation recovers each
// coordinate from an equality of products.
var DivisorsOfCoprimeProduct = divisorsOfCoprimeProductThm{family.Add(registry.ProofEntry{
	Name: "DivisorsOfCoprimeProduct",
	Key:  "prop_6e82e0795d418feb",
	Build: family.Sections(Statement{
		Binders:    "∀m n:num.",
		Hypotheses: []string{"nat_coprime(m, n)"},
		Conclusion: "{d:num | d ∣ m * n} = " +
			"image(λp:prod(num, num). fst(p) * snd(p), {p:prod(num, num) | fst(p) ∣ m ∧ snd(p) ∣ n}) ∧ " +
			"injective_on({p:prod(num, num) | fst(p) ∣ m ∧ snd(p) ∣ n}, λp:prod(num, num). fst(p) * snd(p))",
	},
		func(ctx *Script, headline string) *GoalStackNode {
			divisorCoprime := ctx.Lemma(Statement{
				Binders: "∀m n d e:num.",
				Hypotheses: []string{
					"nat_coprime(m, n)",
					"d ∣ m",
					"e ∣ n",
				},
				Conclusion: "nat_coprime(d, e)",
			}, func(a *Argument, m, n, d, e *Expr[Nat], coprime, dividesM, dividesN Fact) {
				onlyOne := a.Have(
					"a common divisor of d and e also divides m and n, so it is 1",
					"∀c:num. c ∣ d ∧ c ∣ e ⇒ c = 1",
					Derive(func(a *Argument) {
						c := a.FixAs[Nat]("c")
						common := a.Assume()
						a.Show(
							"coprimality of m and n forces the common divisor to be 1",
							By(
								common,
								coprime,
								dividesM,
								dividesN,
								nat_divides.DividesTrans.At(c, d, m),
								nat_divides.DividesTrans.At(c, e, n),
								nat_gcd.Coprime.At(m, n)))
					}))
				a.Show(
					"therefore d and e are coprime",
					By(onlyOne, nat_gcd.Coprime.At(d, e)))
			})

			return ctx.Theorem(headline, func(a *Argument, m, n *Expr[Nat], coprime Fact) {
				a.Do(SplitConj(
					Case(
						"the product divisors are exactly the products of divisor pairs",
						Derive(func(a *Argument) {
							factors := a.Have(
								"a product divisor splits into one divisor of each factor",
								"∀c:num. c ∣ m * n ⇔ ∃d e:num. c = d * e ∧ d ∣ m ∧ e ∣ n",
								Derive(func(a *Argument) {
									c := a.FixAs[Nat]("c")
									a.Iff()
									a.Forward(
										"split a divisor of m·n into its two divisor factors",
										func(a *Argument, divides Fact) {
											a.Show(
												"the two factors exist",
												By(divides, nat_gcd.DivisorProductFactors.At(c, m, n)))
										})
									a.Backward(
										"a product of divisors divides m·n",
										func(a *Argument, split Fact) {
											d, e, factor := a.Unpack2As[Nat, Nat](split)
											first := a.Have(
												"multiply d ∣ m by e",
												"d * e ∣ m * e",
												By(
													factor,
													nat_divides.MulDividesMulLeft.At(e, d, m),
													nat_arith.MulSym.At(d, e),
													nat_arith.MulSym.At(m, e)))
											a.Show(
												"multiply e ∣ n by m and compose the divisibilities",
												By(
													Normalized,
													first,
													factor,
													nat_divides.MulDividesMulLeft.At(m, e, n),
													nat_divides.DividesTrans.At(
														a.TermAs[Nat]("d * e"),
														a.TermAs[Nat]("m * e"),
														a.TermAs[Nat]("m * n"))))
										})
								}))
							a.Show(
								"pairing the two divisor factors gives precisely the image",
								Simp(Fwd(set_basic.Extension)),
								BySets(
									factors,
									pairs.Fst.Inst(TypeBinder.BindA[Nat](), TypeBinder.BindB[Nat]()),
									pairs.Snd.Inst(TypeBinder.BindA[Nat](), TypeBinder.BindB[Nat]())))
						})),
					Case(
						"coprimality makes the divisor pair unique",
						Derive(func(a *Argument) {
							unique := a.Have(
								"each divisor coordinate is determined by the product",
								"∀d e f g:num. d ∣ m ∧ e ∣ n ∧ f ∣ m ∧ g ∣ n ∧ d * e = f * g ⇒ d = f ∧ e = g",
								Derive(func(a *Argument) {
									d := a.FixAs[Nat]("d")
									e := a.FixAs[Nat]("e")
									f := a.FixAs[Nat]("f")
									g := a.FixAs[Nat]("g")
									factorPairs := a.Assume()
									crossCoprime := a.Have(
										"factors belonging to different coprime parents are coprime",
										"nat_coprime(d, g) ∧ nat_coprime(f, e)",
										By(coprime, factorPairs, At(divisorCoprime, m, n, d, g), At(divisorCoprime, m, n, f, e)))
									dDividesF := a.Have(
										"d divides f·g and is coprime to g, so d divides f",
										"d ∣ f",
										By(
											crossCoprime,
											factorPairs,
											nat_divides.DividesOwnMultiple.At(d, e),
											nat_gcd.CoprimeCancel.At(d, f, g)))
									fDividesD := a.Have(
										"f divides d·e and is coprime to e, so f divides d",
										"f ∣ d",
										By(
											crossCoprime,
											factorPairs,
											nat_divides.DividesOwnMultiple.At(f, g),
											nat_gcd.CoprimeCancel.At(f, d, e)))
									eDividesG := a.Have(
										"e divides g·f and is coprime to f, so e divides g",
										"e ∣ g",
										By(
											crossCoprime,
											factorPairs,
											nat_gcd.CoprimeSym.At(f, e),
											nat_divides.DividesOwnMultiple.At(e, d),
											nat_arith.MulSym.At(f, g),
											nat_gcd.CoprimeCancel.At(e, g, f)))
									gDividesE := a.Have(
										"g divides e·d and is coprime to d, so g divides e",
										"g ∣ e",
										By(
											crossCoprime,
											factorPairs,
											nat_gcd.CoprimeSym.At(d, g),
											nat_divides.DividesOwnMultiple.At(g, f),
											nat_arith.MulSym.At(d, e),
											nat_gcd.CoprimeCancel.At(g, e, d)))
									a.Show(
										"mutual divisibility identifies both coordinates",
										By(
											dDividesF,
											fDividesD,
											eDividesG,
											gDividesE,
											nat_divides.DividesAntisym.At(d, f),
											nat_divides.DividesAntisym.At(e, g)))
								}))
							a.Show(
								"equal coordinates reconstruct equal pairs",
								Unfold(functions.InjectiveOnDef),
								BySets(unique, pairs.PairEta.Inst(TypeBinder.BindA[Nat](), TypeBinder.BindB[Nat]())))
						}))))
			})
		}),
	Reading: "Coprimality is what makes the pair unique: 2·1 = 1·2 are two pairs for " +
		"m = n = 2. With m = 1 and n = 0 the statement holds too: every number divides 0.",
})}

// DivisorSumMultiplicative — the sum of a multiplicative function over the
// divisors of a product of two coprime numbers is the product of its sums
// over the divisors of each. The divisors of m·n are the products of a
// divisor of m and a divisor of n, each from exactly one pair, so the sum
// runs over the pairs; the two coordinates of a pair are coprime, so f
// splits there, and the sum over the pairs factors (real_sum.ProductOfSums).
var DivisorSumMultiplicative = divisorSumMultiplicativeThm{family.Add(registry.ProofEntry{
	Name: "DivisorSumMultiplicative",
	Key:  "prop_42136917775b59ed",
	Reading: "m and n are positive so that the divisor " +
		"sets of m and n are finite and their sums multiply out.",
	Build: family.Theorem(Statement{
		Binders: "∀f:(num → real). ∀m n:num.",
		Hypotheses: []string{
			"∀a b:num. nat_coprime(a, b) ⇒ f(a * b) = f(a) * f(b)",
			"nat_coprime(m, n)",
			"0 < m",
			"0 < n",
		},
		Conclusion: "Σ_{d∈{d:num | d ∣ m * n}} f(d) = " +
			"(Σ_{d∈{d:num | d ∣ m}} f(d)) * Σ_{d∈{d:num | d ∣ n}} f(d)",
		Abbrev: Abbrev{
			{Name: "divisorPairs", Text: "set_cross({d:num | d ∣ m}, {d:num | d ∣ n})"},
		},
	},
		func(a *Argument, f *Arrow[Nat, Real], m, n *Expr[Nat], multiplicative, coprime, mPos, nPos Fact) {
			divisorsM := a.TermAs[Set[Nat]]("{d:num | d ∣ m}")
			divisorsN := a.TermAs[Set[Nat]]("{d:num | d ∣ n}")
			coprimeDivisors := a.Have(
				"a divisor of m and a divisor of n are coprime: a common divisor of the two divides m and n",
				"∀d e:num. d ∣ m ∧ e ∣ n ⇒ nat_coprime(d, e)",
				By(coprime, nat_gcd.Coprime, nat_divides.DividesTrans))
			pairsAreCross := a.Have(
				"the pairs whose coordinates divide m and n are the cross product of the two divisor sets",
				"{p:prod(num, num) | fst(p) ∣ m ∧ snd(p) ∣ n} = «divisorPairs»",
				BySets(set_product.InCrossProjections))
			splits := a.Have(
				"f splits at every divisor pair, its two coordinates being coprime",
				"∀p:prod(num, num). p ∈ «divisorPairs» ⇒ f(fst(p) * snd(p)) = f(fst(p)) * f(snd(p))",
				Derive(func(b *Argument) {
					p := b.FixAs[Prod[Nat, Nat]]("p")
					inPairs := b.Assume()
					first := b.TermAs[Nat]("fst(p)")
					second := b.TermAs[Nat]("snd(p)")
					b.Show(
						"the coordinates divide m and n, hence are coprime",
						By(
							inPairs,
							multiplicative.At(first, second),
							coprimeDivisors.At(first, second),
							set_product.InCrossProjections.At(divisorsM, divisorsN, p)))
				}))
			product := a.TermAs[Fun[Prod[Nat, Nat], Nat]]("λp:prod(num, num). fst(p) * snd(p)")
			dividingPairs := a.TermAs[Set[Prod[Nat, Nat]]]("{p:prod(num, num) | fst(p) ∣ m ∧ snd(p) ∣ n}")
			a.Show(
				"reindex by the divisor pairs, split f at each pair, and factor the sum",
				CalcEq(
					Leg(
						a.TermAs[Real]("Σ_{p∈«divisorPairs»} f(fst(p) * snd(p))"),
						"the divisors of m·n are the products of the divisor pairs, each from one pair",
						By(
							pairsAreCross,
							coprime,
							DivisorsOfCoprimeProduct.At(m, n),
							real_sum.Image.At(dividingPairs, product, f),
							functions.ComposeApply.At(f, product))),
					Leg(
						a.TermAs[Real]("Σ_{p∈«divisorPairs»} f(fst(p)) * f(snd(p))"),
						"f splits term by term",
						By(splits, real_sum.Congruence)),
					FinalLeg(
						"the divisors of m and of n are finitely many, and the sum over their pairs factors",
						By(
							mPos,
							nPos,
							nat_divides.DivisorsFinite.At(m),
							nat_divides.DivisorsFinite.At(n),
							real_sum.ProductOfSums.At(divisorsM, divisorsN, f, f))),
				))
		}),
})}
