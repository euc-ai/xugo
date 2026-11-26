// frobenius.go — the binomial theorem in a commutative ring on a set,
// and the Frobenius power of prime characteristic p: the p-th power
// preserves addition and fixes the image of every integer, its iterates
// are ring endomorphisms, and on a finite field it is one-to-one and onto.

package finite_field

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/characteristic_zero"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_embed"
	"github.com/euc-ai/xugo/library/proofs/nat_num/binomial"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_prime"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// carrierFoldAsModuleSum reads an additive fold as a finite sum in the ring carrier.
func carrierFoldAsModuleSum(ctx *Script) *GoalStackNode {
	return ctx.Lemma(Statement{
		Binders: "∀R:comm_ring_on(A). ∀s:set(num). ∀F:(num → A).",
		Hypotheses: []string{
			"finite(s)",
			"∀i:num. F(i) ∈ R.carrier",
		},
		Conclusion: "set_fold(λi:num. λz:A. F(i) + z, s, R.zero) = module_sum(R.add, R.zero, s, F)",
		Abbrev: Abbrev{
			{Name: "plainStep", Text: "λx:num. λz:A. F(x) + z"},
			{Name: "guardedStep", Text: "λx:num. λz:A. COND(x ∈ s, F(x) + z, z)"},
		},
	}, func(
		arg *Argument,
		R comm_ring.CommRingFact[on.R],
		s *Expr[Set[Nat]],
		F *Arrow[Nat, A],
		finite, values Fact,
	) {
		arg.Do(Unfold(module.ModuleSumDef))
		agree := arg.Have(
			"The steps agree on the index set",
			"∀x:num. x ∈ s ⇒ «plainStep»(x) = «guardedStep»(x)",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("x")
				inS := b.Assume()
				b.Show(
					"The membership guard selects the additive step",
					By(inS))
			}))
		plainClosed := arg.Have(
			"The additive step preserves the carrier",
			"∀x:num. ∀z:A. z ∈ R.carrier ⇒ «plainStep»(x, z) ∈ R.carrier",
			By(comm_ring.AddIn.Read(R), values))
		plainCommutes := arg.Have(
			"The additive steps commute on the carrier",
			Statement{
				Binders:    "∀x y:num. ∀z:A.",
				Hypotheses: []string{"x ≠ y", "z ∈ R.carrier"},
				Conclusion: "«plainStep»(x, «plainStep»(y, z)) = «plainStep»(y, «plainStep»(x, z))",
			},
			By(comm_monoid.LeftCommOn.Read(comm_ring.AddMonoidOn.Read(R)), values))
		guardedClosed := arg.Have(
			"The guarded step preserves the carrier",
			"∀x:num. ∀z:A. z ∈ R.carrier ⇒ «guardedStep»(x, z) ∈ R.carrier",
			By(comm_ring.AddIn.Read(R), values))
		guardedCommutes := arg.Have(
			"The guarded steps commute on the carrier",
			Statement{
				Binders:    "∀x y:num. ∀z:A.",
				Hypotheses: []string{"x ≠ y", "z ∈ R.carrier"},
				Conclusion: "«guardedStep»(x, «guardedStep»(y, z)) = «guardedStep»(y, «guardedStep»(x, z))",
			},
			Derive(func(b *Argument) {
				x := b.FixAs[Nat]("x")
				y := b.FixAs[Nat]("y")
				z := b.FixAs[A]("z")
				guard := b.Assume()
				inX := b.Assuming(
					b.Term("x ∈ s"),
					"When the first index lies off the index set the first step is the identity",
					Given(func(c *Argument, offX Fact) {
						c.Show(
							"The identity step commutes with the second step",
							By(offX))
					}))
				inY := b.Assuming(
					b.Term("y ∈ s"),
					"When the second index lies off the index set the second step is the identity",
					Given(func(c *Argument, offY Fact) {
						c.Show(
							"The identity step commutes with the first step",
							By(offY))
					}))
				b.Show(
					"At two indices the additive steps commute within the carrier",
					By(inX, inY, guard, plainCommutes.At(x, y, z)))
			}))
		arg.Show(
			"The two folds agree from the ring's zero",
			By(
				comm_ring.ZeroIn.Read(R),
				finite,
				guardedClosed,
				plainClosed,
				guardedCommutes,
				plainCommutes,
				agree,
				Where(cardinality.FoldOfAgreeingStepsWithin, "K", arg.TermAs[Set[A]]("R.carrier"))))
	})
}

// carrierPowerProducts proves that a natural multiple of one times a
// power of a and a power of b lies in the ring carrier when a and b do:
// every binomial summand, at every index. BinomialTheoremRing and
// FrobeniusAdditive cite it for the summands of their binomial sums.
func carrierPowerProducts(ctx *Script) *GoalStackNode {
	return ctx.Lemma(Statement{
		Binders: "∀R:comm_ring_on(A). ∀a b:A. ∀i j k:num.",
		Hypotheses: []string{
			"a ∈ R.carrier",
			"b ∈ R.carrier",
		},
		Conclusion: "monoid_pow(R.add, R.zero, R.one, i) * " +
			"monoid_pow(R.mul, R.one, a, j) * " +
			"monoid_pow(R.mul, R.one, b, k) ∈ " +
			"R.carrier",
	}, func(arg *Argument, R comm_ring.CommRingFact[on.R], a, b *Member[A, on.R]) {
		additive := comm_ring.AddMonoidOn.Read(R)
		multiplicative := comm_ring.MulMonoidOn.Read(R)
		arg.Show(
			"Multiples of one and powers of carrier elements lie in the carrier, and so do their products",
			By(
				comm_ring.OneIn.Read(R),
				comm_ring.MulIn.Read(R),
				comm_monoid.PowIn.Read(additive),
				comm_monoid.PowIn.Read(multiplicative),
				a,
				b))
	})
}

// BinomialTheoremRing — the binomial expansion in a commutative ring on a set:
// Pascal's rule splits the next row into the preceding row multiplied by a and b.
var BinomialTheoremRing = binomialTheoremRingThm{family.Add(registry.ProofEntry{
	Name: "BinomialTheoremRing",
	Key:  "prop_81d89fd2b01af5fd",
	Reading: "Every summand lies in the ring carrier for every natural index, including indices " +
		"outside the displayed interval. The fold therefore needs no off-carrier ring laws; n=0 gives one.",
	Build: family.Sections(Statement{
		Binders: "∀R:comm_ring_on(A). ∀a b:A. ∀n:num.",
		Hypotheses: []string{
			"a ∈ R.carrier",
			"b ∈ R.carrier",
		},
		Conclusion: "monoid_pow(R.mul, R.one, a + b, n) = " +
			"set_fold(λj:num. λs:A. " +
			"        monoid_pow(R.add, R.zero, R.one, binomial(n, j)) * " +
			"        monoid_pow(R.mul, R.one, a, j) * " +
			"        monoid_pow(R.mul, R.one, b, n - j) + " +
			"        s, " +
			"    0 .. n, " +
			"    R.zero)",
		Abbrev: Abbrev{
			{Name: "coefficient", Text: "λk:num. monoid_pow(R.add, R.zero, R.one, k)"},
			{Name: "leftPower", Text: "λk:num. monoid_pow(R.mul, R.one, a, k)"},
			{Name: "rightPower", Text: "λk:num. monoid_pow(R.mul, R.one, b, k)"},
			{Name: "binomialRow", Text: "λm:num. λj:num. " +
				"    «coefficient»(binomial(m, j)) * «leftPower»(j) * «rightPower»(m - j)"},
			{Name: "rowSum", Text: "module_sum(R.add, R.zero, 0 .. n, «binomialRow»(n))"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		summandsIn := carrierPowerProducts(ctx)
		foldAsSum := carrierFoldAsModuleSum(ctx)
		expansion := ctx.Lemma(Statement{
			Binders:    "∀R:comm_ring_on(A). ∀a b:A. ∀n:num.",
			Hypotheses: []string{"a ∈ R.carrier", "b ∈ R.carrier"},
			Conclusion: "monoid_pow(R.mul, R.one, a + b, n) = «rowSum»",
		}, func(arg *Argument, R comm_ring.CommRingFact[on.R], a, b *Member[A, on.R]) {
			additiveMonoid := comm_ring.AddMonoidOn.Read(R)
			regular := module.RegularModuleOn.Read(R)
			arg.Induct("n")
			arg.Base(
				"The initial row consists of one",
				func(c *Argument) {
					c.Do(Simp(Fwd(num_segment.Sing), Fwd(comm_monoid.MonoidPowDef)))
					corner := c.Have(
						"The initial summand is one",
						"«binomialRow»(0, 0) = R.one",
						Simp(Fwd(binomial.Clauses), Fwd(nat_monus.Sub), Fwd(comm_monoid.MonoidPowDef)),
						ByArith(R))
					singleton := c.TermAs[Set[Nat]]("{0}")
					initialTerms := c.TermAs[Fun[Nat, A]]("«binomialRow»(0)")
					c.Show(
						"The singleton sum is its only term",
						By(
							comm_ring.OneIn.Read(R),
							corner,
							module.ModuleSumSingle.Read(regular).At(singleton, c.Ctx().Nat(0), initialTerms),
							finite_set.FiniteRules,
							set_basic.InSing))
				})
			arg.Step(
				"Pascal's two shares sum to the next power",
				func(c *Argument, ih Fact) {
					productsIn := c.Have(
						"Every possible summand lies in the carrier",
						"∀i j k:num. «coefficient»(i) * «leftPower»(j) * «rightPower»(k) ∈ R.carrier",
						By(R, a, b, summandsIn))
					coefficientAdd := c.Have(
						"Natural multiples of one preserve addition",
						"∀i j:num. «coefficient»(i + j) = «coefficient»(i) + «coefficient»(j)",
						By(comm_ring.OneIn.Read(R), comm_monoid.PowAddOn.Read(additiveMonoid)))
					above, aboveDef := c.LetAs[Fun[Nat, A]](
						"above", "λk:num. «coefficient»(binomial(n, k)) * «leftPower»(k) * «rightPower»(suc(n) - k)")
					aboveLeft, aboveLeftDef := c.LetAs[Fun[Nat, A]](
						"aboveLeft",
						"λk:num. "+
							"    COND(k = 0, "+
							"        R.zero, "+
							"        «coefficient»(binomial(n, k - 1)) * «leftPower»(k) * «rightPower»(suc(n) - k))")
					sharesIn := c.Have(
						"Both shares lie in the carrier at every index",
						"∀k:num. above(k) ∈ R.carrier ∧ aboveLeft(k) ∈ R.carrier",
						Simp(Fwd(aboveDef), Fwd(aboveLeftDef)),
						By(comm_ring.ZeroIn.Read(R), productsIn))
					pascal := c.Have(
						"Each next-row term is the sum of its two shares",
						"∀k:num. «binomialRow»(suc(n), k) = above(k) + aboveLeft(k)",
						Derive(func(d *Argument) {
							d.FixAs[Nat]("k")
							d.Cases(d.TermAs[Bool]("k = 0"))
							d.When(
								"Column zero has no share from above-left",
								func(e *Argument, isZero Fact) {
									e.Show(
										"Column zero receives only the share from above",
										Simp(
											Fwd(aboveDef),
											Fwd(aboveLeftDef),
											Fwd(isZero),
											Fwd(binomial.Clauses),
											Fwd(comm_monoid.MonoidPowDef),
											Fwd(nat_monus.Sub)),
										ByArith(R, a, b))
								})
							d.Otherwise(
								"Positive columns satisfy Pascal's rule",
								func(e *Argument, nonzero Fact) {
									coefficient := e.Have(
										"Pascal adds the two preceding coefficients",
										"binomial(suc(n), k) = binomial(n, k - 1) + binomial(n, k)",
										By(Normalized, nonzero, binomial.BinomialDef))
									e.Show(
										"The coefficient sum distributes over the powers",
										Simp(Fwd(aboveDef), Fwd(aboveLeftDef), Fwd(coefficient), Fwd(coefficientAdd)),
										ByArith(R, a, b, nonzero))
								})
						}))
					n := c.TermAs[Nat]("n")
					next := c.TermAs[Nat]("suc(n)")
					row := c.TermAs[Set[Nat]]("0 .. n")
					nextRow := c.TermAs[Set[Nat]]("0 .. suc(n)")
					terms := c.TermAs[Fun[Nat, A]]("«binomialRow»(n)")
					ringAdd := c.TermAs[Op[A]]("R.add")
					ringZero := c.TermAs[A]("R.zero")
					sumIn := c.Have(
						"The preceding row sum lies in the carrier",
						"«rowSum» ∈ R.carrier",
						By(productsIn, num_segment.Finite, module.ModuleSumInMonoid.Read(additiveMonoid).At(row, terms)))
					bShare := c.Have(
						"The shares from above sum to b times the preceding row",
						"module_sum(R.add, R.zero, 0 .. suc(n), above) = b * «rowSum»",
						Derive(func(d *Argument) {
							topCoefficient := d.Have(
								"The preceding row ends before the new endpoint",
								"binomial(n, suc(n)) = 0",
								ByArith(binomial.EqZero.At(n, next)))
							top := d.Have(
								"The extra share from above is zero",
								"above(suc(n)) = R.zero",
								Simp(Fwd(aboveDef), Fwd(topCoefficient), Fwd(comm_monoid.MonoidPowDef)),
								ByArith(R, a, b))
							pointwise := d.Have(
								"Multiplication by b gives the shares from above",
								"∀k:num. k ≤ n ⇒ above(k) = b * «binomialRow»(n, k)",
								Derive(func(e *Argument) {
									e.FixAs[Nat]("k")
									bound := e.Assume()
									exponent := e.Have(
										"The exponent of b gains one",
										"suc(n) - k = suc(n - k)",
										ByArith(bound))
									e.Show(
										"The powers supply exactly one more factor b",
										Simp(Fwd(aboveDef), Fwd(exponent), Fwd(comm_monoid.MonoidPowDef)),
										ByArith(R, a, b))
								}))
							interval := d.Have(
								"The next interval appends its new endpoint",
								"0 .. suc(n) = insert(suc(n), 0 .. n)",
								By(num_segment.Rec, nat_order.ZeroLessEq))
							fresh := d.Have(
								"The new endpoint is absent from the preceding interval",
								"suc(n) ∉ 0 .. n",
								ByArith())
							appendTerm := d.Have(
								"The next sum appends its endpoint term",
								"module_sum(R.add, R.zero, 0 .. suc(n), above) = "+
									"above(suc(n)) + module_sum(R.add, R.zero, 0 .. n, above)",
								Simp(Fwd(interval)),
								By(fresh, sharesIn, num_segment.Finite, module.ModuleSumInsert.Read(regular).At(row, next, above)))
							scaledByB := d.TermAs[Fun[Nat, A]]("λk:num. b * «binomialRow»(n, k)")
							termwise := d.Have(
								"The preceding interval reads the same summands",
								"module_sum(R.add, R.zero, 0 .. n, above) = "+
									"module_sum(R.add, R.zero, 0 .. n, λk:num. b * «binomialRow»(n, k))",
								By(pointwise, module.ModuleSumCongruence.At(ringAdd, ringZero, row, above, scaledByB)))
							scaled := d.Have(
								"Multiplication by b passes through the sum",
								"b * «rowSum» = module_sum(R.add, R.zero, 0 .. n, λk:num. b * «binomialRow»(n, k))",
								By(a, b, productsIn, num_segment.Finite, module.ModuleSumSmul.Read(regular).At(row, b, terms)))
							d.Show(
								"The zero endpoint adds nothing to b times the row",
								Simp(Fwd(appendTerm), Fwd(top), Fwd(termwise), Rev(scaled)),
								ByArith(R, sumIn, a, b))
						}))
					aShare := c.Have(
						"The shares from above-left sum to a times the preceding row",
						"module_sum(R.add, R.zero, 0 .. suc(n), aboveLeft) = a * «rowSum»",
						Derive(func(d *Argument) {
							pointwise := d.Have(
								"Shifting a share back gives multiplication by a",
								"∀k:num. aboveLeft(k + 1) = a * «binomialRow»(n, k)",
								Derive(func(e *Argument) {
									e.FixAs[Nat]("k")
									indices := e.Have(
										"The shift preserves the complementary exponent",
										"k + 1 ≠ 0 ∧ k + 1 - 1 = k ∧ suc(n) - (k + 1) = n - k ∧ k + 1 = suc(k)",
										ByArith())
									e.Show(
										"The powers supply exactly one more factor a",
										Simp(Fwd(aboveLeftDef), Fwd(indices), Fwd(comm_monoid.MonoidPowDef)),
										ByArith(R, a, b))
								}))
							interval := d.Have(
								"The next interval begins with column zero",
								"0 .. suc(n) = insert(0, 1 .. suc(n))",
								Derive(func(e *Argument) {
									bounds := e.Have(
										"The initial endpoint is in range",
										"0 ≤ suc(n) ∧ 0 + 1 = 1",
										ByArith())
									e.Show(
										"The left interval clause selects zero",
										By(Normalized, bounds, num_segment.RecLeft.At(e.Ctx().Nat(0), next)))
								}))
							fresh := d.Have(
								"Zero is absent from the positive columns",
								"0 ∉ 1 .. suc(n)",
								ByArith())
							zero := d.Have(
								"Column zero has no share from above-left",
								"aboveLeft(0) = R.zero",
								By(aboveLeftDef))
							positive := d.TermAs[Set[Nat]]("1 .. suc(n)")
							prependTerm := d.Have(
								"The sum splits off column zero",
								"module_sum(R.add, R.zero, 0 .. suc(n), aboveLeft) = "+
									"aboveLeft(0) + module_sum(R.add, R.zero, 1 .. suc(n), aboveLeft)",
								Simp(Fwd(interval)),
								By(
									fresh,
									sharesIn,
									num_segment.Finite,
									module.ModuleSumInsert.Read(regular).At(positive, d.Ctx().Nat(0), aboveLeft)))
							image := d.Have(
								"The positive columns are the shifted preceding interval",
								"1 .. suc(n) = image(λj:num. j + 1, 0 .. n)",
								Derive(func(e *Argument) {
									endpoints := e.Have(
										"Shifting both endpoints gives the positive interval",
										"0 + 1 = 1 ∧ n + 1 = suc(n)",
										ByArith())
									e.Show(
										"Translation gives the required image",
										By(endpoints, num_segment.OffsetImage.At(e.Ctx().Nat(0), n, e.Ctx().Nat(1))))
								}))
							injective := d.Have(
								"The shift is injective",
								"injective_on(0 .. n, λj:num. j + 1)",
								Unfold(functions.InjectiveOnDef),
								ByArith())
							successor := d.TermAs[Fun[Nat, Nat]]("λj:num. j + 1")
							shift := d.Have(
								"Reindex the positive-column sum by the shift",
								"module_sum(R.add, R.zero, 1 .. suc(n), aboveLeft) = "+
									"module_sum(R.add, R.zero, 0 .. n, λj:num. aboveLeft(j + 1))",
								Simp(Fwd(image)),
								By(
									injective,
									sharesIn,
									num_segment.Finite,
									module.ModuleSumImage.Read(regular).At(row, successor, aboveLeft)))
							shifted := d.TermAs[Fun[Nat, A]]("λj:num. aboveLeft(j + 1)")
							scaledByA := d.TermAs[Fun[Nat, A]]("λj:num. a * «binomialRow»(n, j)")
							termwise := d.Have(
								"The shifted shares are a times the preceding summands",
								"module_sum(R.add, R.zero, 0 .. n, λj:num. aboveLeft(j + 1)) = "+
									"module_sum(R.add, R.zero, 0 .. n, λj:num. a * «binomialRow»(n, j))",
								By(pointwise, module.ModuleSumCongruence.At(ringAdd, ringZero, row, shifted, scaledByA)))
							scaled := d.Have(
								"Multiplication by a passes through the sum",
								"a * «rowSum» = module_sum(R.add, R.zero, 0 .. n, λj:num. a * «binomialRow»(n, j))",
								By(a, b, productsIn, num_segment.Finite, module.ModuleSumSmul.Read(regular).At(row, a, terms)))
							d.Show(
								"The zero initial share adds nothing to a times the row",
								Simp(Fwd(prependTerm), Fwd(zero), Fwd(shift), Fwd(termwise), Rev(scaled)),
								ByArith(R, sumIn, a, b))
						}))
					nextTerms := c.TermAs[Fun[Nat, A]]("«binomialRow»(suc(n))")
					shares := c.TermAs[Fun[Nat, A]]("λk:num. above(k) + aboveLeft(k)")
					split := c.Have(
						"Pascal's identity holds under the sum",
						"module_sum(R.add, R.zero, 0 .. suc(n), «binomialRow»(suc(n))) = "+
							"module_sum(R.add, R.zero, 0 .. suc(n), λk:num. above(k) + aboveLeft(k))",
						By(pascal, module.ModuleSumCongruence.At(ringAdd, ringZero, nextRow, nextTerms, shares)))
					additive := c.Have(
						"Finite summation distributes over the two shares",
						"module_sum(R.add, R.zero, 0 .. suc(n), λk:num. above(k) + aboveLeft(k)) = "+
							"module_sum(R.add, R.zero, 0 .. suc(n), above) + module_sum(R.add, R.zero, 0 .. suc(n), aboveLeft)",
						By(sharesIn, num_segment.Finite, module.ModuleSumAdd.Read(regular).At(nextRow, above, aboveLeft)))
					c.Show(
						"Multiply the preceding row by a+b",
						Simp(Fwd(comm_monoid.MonoidPowDef), Fwd(ih), Fwd(split), Fwd(additive), Fwd(bShare), Fwd(aShare)),
						ByArith(R, sumIn, a, b))
				})
		})
		return ctx.Theorem(headline, func(
			arg *Argument,
			R comm_ring.CommRingFact[on.R],
			a, b *Member[A, on.R],
			n *Expr[Nat],
		) {
			values := arg.Have(
				"Every displayed summand lies in the carrier at every index",
				"∀j:num. «binomialRow»(n, j) ∈ R.carrier",
				By(R, a, b, summandsIn))
			finite := arg.Have(
				"The index interval is finite",
				"finite(0 .. n)",
				By(num_segment.Finite))
			ring := arg.TermAs[RingOps[A]]("R")
			indices := arg.TermAs[Set[Nat]]("0 .. n")
			terms := arg.TermAs[Fun[Nat, A]]("«binomialRow»(n)")
			bridge := arg.Have(
				"The displayed fold is the finite ring sum",
				"set_fold(λj:num. λs:A. «binomialRow»(n, j) + s, 0 .. n, R.zero) = «rowSum»",
				By(R, finite, values, At(foldAsSum, ring, indices, terms)))
			arg.Show(
				"Read the binomial sum as the displayed fold",
				bridge.Rw(),
				By(R, a, b, At(expansion, ring, a, b, n)))
		})
	}),
})}

// FrobeniusAdditive — the p-th power preserves addition in prime characteristic:
// every interior binomial coefficient vanishes, leaving the two endpoint powers.
var FrobeniusAdditive = frobeniusAdditiveThm{family.Add(registry.ProofEntry{
	Name: "FrobeniusAdditive",
	Key:  "prop_675ed7d79890f990",
	Build: family.Sections(Statement{
		Binders: "∀R:comm_ring_on(A). ∀p:num. ∀a b:A.",
		Hypotheses: []string{
			"ring_prime_characteristic(R, p)",
			"a ∈ R.carrier",
			"b ∈ R.carrier",
		},
		Conclusion: "monoid_pow(R.mul, R.one, a + b, p) = " +
			"monoid_pow(R.mul, R.one, a, p) + monoid_pow(R.mul, R.one, b, p)",
		Abbrev: Abbrev{
			{Name: "coefficient", Text: "λk:num. monoid_pow(R.add, R.zero, R.one, k)"},
			{Name: "leftPower", Text: "λk:num. monoid_pow(R.mul, R.one, a, k)"},
			{Name: "rightPower", Text: "λk:num. monoid_pow(R.mul, R.one, b, k)"},
			{Name: "row", Text: "λj:num. «coefficient»(binomial(p, j)) * «leftPower»(j) * «rightPower»(p - j)"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		summandsIn := carrierPowerProducts(ctx)
		characteristicMultiples := ctx.Lemma(Statement{
			Binders:    "∀R:comm_ring_on(A). ∀p n:num.",
			Hypotheses: []string{"ring_prime_characteristic(R, p)", "p ∣ n"},
			Conclusion: "«coefficient»(n) = R.zero",
		}, func(
			arg *Argument,
			R comm_ring.CommRingFact[on.R],
			p, n *Expr[Nat],
			characteristic, divides Fact,
		) {
			annihilator := arg.Unfolded(characteristic, PrimeCharacteristicDef)
			_, multiple := arg.ObtainAs[Nat](
				"Write the coefficient index as a multiple of the characteristic",
				"∃m:num. n = p * m",
				By(divides, nat_divides.DividesFactor))
			arg.Show(
				"Natural coefficient multiplication carries the annihilator through the multiple",
				Simp(Fwd(multiple), Fwd(comm_ring.AddPowMulOn.Read(R)), Fwd(annihilator)),
				ByArith(R))
		})
		endpointSum := ctx.Lemma(Statement{
			Binders:    "∀R:comm_ring_on(A). ∀p:num. ∀a b:A.",
			Hypotheses: []string{"ring_prime_characteristic(R, p)", "a ∈ R.carrier", "b ∈ R.carrier"},
			Conclusion: "module_sum(R.add, R.zero, 0 .. p, «row») = «leftPower»(p) + «rightPower»(p)",
		}, func(
			arg *Argument,
			R comm_ring.CommRingFact[on.R],
			p *Expr[Nat],
			characteristic Fact,
			a, b *Member[A, on.R],
		) {
			ring := arg.TermAs[RingOps[A]]("R")
			regular := module.RegularModuleOn.Read(R)
			prime := arg.Unfolded(characteristic, PrimeCharacteristicDef)
			bound := arg.Have(
				"A prime characteristic separates the two endpoints",
				"2 ≤ p",
				By(prime, nat_prime.PrimeAtLeastTwo))
			values := arg.Have(
				"All binomial summands lie in the carrier",
				"∀j:num. «row»(j) ∈ R.carrier",
				By(R, a, b, summandsIn))
			initial := arg.Have(
				"Column zero contributes the power of b",
				"«row»(0) = «rightPower»(p)",
				Simp(Fwd(binomial.Clauses), Fwd(comm_monoid.MonoidPowDef), Fwd(nat_monus.Sub)),
				ByArith(R, a, b))
			last := arg.Have(
				"Column p contributes the power of a",
				"«row»(p) = «leftPower»(p)",
				Derive(func(c *Argument) {
					complement := c.Have(
						"The final complementary exponent is zero",
						"p - p = 0",
						ByArith())
					c.Show(
						"The diagonal coefficient and the zero-th power are one",
						Simp(Fwd(binomial.Diagonal), Fwd(complement), Fwd(comm_monoid.MonoidPowDef)),
						ByArith(R, a, b))
				}))
			interior := arg.Have(
				"Every interior summand vanishes",
				"∀j:num. 0 < j ∧ j < p ⇒ «row»(j) = R.zero",
				Derive(func(c *Argument) {
					j := c.FixAs[Nat]("j")
					inside := c.Assume()
					divides := c.Have(
						"The characteristic divides each interior binomial coefficient",
						"p ∣ binomial(p, j)",
						By(prime, inside, nat_prime.PrimeDividesBinomial.At(p, j)))
					coefficientIndex := c.TermAs[Nat]("binomial(p, j)")
					coefficient := c.Have(
						"The interior coefficient is zero in the ring",
						"«coefficient»(binomial(p, j)) = R.zero",
						By(R, characteristic, divides, At(characteristicMultiples, ring, p, coefficientIndex)))
					c.Show(
						"A zero coefficient kills the summand",
						Simp(Fwd(coefficient)),
						ByArith(R, a, b))
				}))
			endpointsIn := arg.Have(
				"Both endpoints belong to the summation interval",
				"0 ∈ 0 .. p ∧ p ∈ 0 .. p",
				ByArith())
			endpointsSubset := arg.Have(
				"The endpoint pair is contained in the interval",
				"{0, p} ⊆ 0 .. p",
				BySets(endpointsIn))
			zeroOffEndpoints := arg.Have(
				"The interval has no other supported summands",
				"∀j:num. j ∈ 0 .. p ∧ j ∉ {0, p} ⇒ «row»(j) = R.zero",
				Derive(func(c *Argument) {
					j := c.FixAs[Nat]("j")
					located := c.Assume()
					away := c.Have(
						"Away from both endpoints an interval index is bounded by p",
						"j ≠ 0 ∧ j ≠ p ∧ j ≤ p",
						BySets(located))
					inside := c.Have(
						"Such an index is strictly between zero and p",
						"0 < j ∧ j < p",
						ByArith(away))
					c.Show(
						"The interior-vanishing statement applies",
						By(inside, interior.At(j)))
				}))
			indices := arg.TermAs[Set[Nat]]("0 .. p")
			pair := arg.TermAs[Set[Nat]]("{0, p}")
			singleton := arg.TermAs[Set[Nat]]("{p}")
			row := arg.TermAs[Fun[Nat, A]]("«row»")
			support := arg.Have(
				"Restrict the sum to its two supported indices",
				"module_sum(R.add, R.zero, 0 .. p, «row») = module_sum(R.add, R.zero, {0, p}, «row»)",
				By(
					values,
					endpointsSubset,
					zeroOffEndpoints,
					num_segment.Finite,
					module.ModuleSumSupport.Read(regular).At(indices, pair, row)))
			fresh := arg.Have(
				"The two endpoints are distinct",
				"0 ∉ {p}",
				ByArith(bound, set_basic.InSing))
			finite := arg.Have(
				"The final endpoint forms a finite singleton",
				"finite({p})",
				By(finite_set.FiniteRules))
			split := arg.Have(
				"Split the endpoint pair into its two contributions",
				"module_sum(R.add, R.zero, {0, p}, «row») = «row»(0) + module_sum(R.add, R.zero, {p}, «row»)",
				By(
					values,
					fresh,
					finite,
					module.ModuleSumInsert.Read(regular).At(singleton, arg.Ctx().Nat(0), row)))
			point := arg.Have(
				"The singleton sum is the final summand",
				"module_sum(R.add, R.zero, {p}, «row») = «row»(p)",
				By(values, finite, set_basic.InSing, module.ModuleSumSingle.Read(regular).At(singleton, p, row)))
			arg.Show(
				"Only the two endpoint powers remain",
				Simp(Fwd(support), Fwd(split), Fwd(point), Fwd(initial), Fwd(last)),
				ByArith(R, a, b))
		})
		foldAsSum := carrierFoldAsModuleSum(ctx)
		return ctx.Theorem(headline,
			func(
				arg *Argument,
				R comm_ring.CommRingFact[on.R],
				p *Expr[Nat],
				characteristic Fact,
				a, b *Member[A, on.R],
			) {
				values := arg.Have(
					"The fold reads carrier-valued summands at every index",
					"∀j:num. «row»(j) ∈ R.carrier",
					By(R, a, b, summandsIn))
				finite := arg.Have(
					"The interval is finite",
					"finite(0 .. p)",
					By(num_segment.Finite))
				ring := arg.TermAs[RingOps[A]]("R")
				indices := arg.TermAs[Set[Nat]]("0 .. p")
				row := arg.TermAs[Fun[Nat, A]]("«row»")
				arg.Show(
					"Expand the p-th power and retain its endpoint terms",
					CalcEq(
						Leg(
							arg.TermAs[A]("set_fold(λx:num. λz:A. «row»(x) + z, 0 .. p, R.zero)"),
							"Apply the binomial theorem in the carrier ring",
							By(R, a, b, BinomialTheoremRing.Read(R).At(a, b, p))),
						Leg(
							arg.TermAs[A]("module_sum(R.add, R.zero, 0 .. p, «row»)"),
							"Read this binomial fold as a finite sum",
							By(R, finite, values, At(foldAsSum, ring, indices, row))),
						FinalLeg(
							"The interior coefficients vanish in prime characteristic",
							By(R, characteristic, a, b, At(endpointSum, ring, p, a, b)))))
			})
	}),
})}

// FrobeniusRingHomomorphism — the p^n power map is a ring endomorphism:
// iterate p-power additivity and use the commutative monoid power laws.
var FrobeniusRingHomomorphism = frobeniusRingHomomorphismThm{family.Add(registry.ProofEntry{
	Name: "FrobeniusRingHomomorphism",
	Key:  "prop_8dcb6218a312444c",
	Reading: "Equality and the ring map laws are on the carrier. At n=0 the " +
		"map is the identity there; no surjectivity is asserted for positive n.",
	Build: family.Sections(Statement{
		Binders: "∀R:comm_ring_on(A). ∀p n:num.",
		Hypotheses: []string{
			"ring_prime_characteristic(R, p)",
		},
		Conclusion: "ring_homomorphism(R, R, frobenius_power(R, p ^ n))",
		Abbrev: Abbrev{
			{Name: "power", Text: "λx:A. monoid_pow(R.mul, R.one, x, p ^ n)"},
			{Name: "map", Text: "frobenius_power(R, p ^ n)"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		additivePowers := ctx.Lemma(Statement{
			Binders: "∀R:comm_ring_on(A). ∀p:num. ∀a b:A. ∀n:num.",
			Hypotheses: []string{
				"ring_prime_characteristic(R, p)",
				"a ∈ R.carrier",
				"b ∈ R.carrier",
			},
			Conclusion: "«power»(a + b) = «power»(a) + «power»(b)",
		}, func(
			arg *Argument,
			R comm_ring.CommRingFact[on.R],
			p *Expr[Nat],
			characteristic Fact,
			a, b *Member[A, on.R],
		) {
			multiplicative := comm_ring.MulMonoidOn.Read(R)
			arg.Induct("n")
			arg.Base(
				"At exponent p^0 the map is the identity on the carrier",
				func(c *Argument) {
					c.Show(
						"The first power leaves each carrier element unchanged",
						Simp(
							Fwd(nat_arith.NatPow),
							Fwd(comm_monoid.PowOneOn.Read(multiplicative)),
							Fwd(comm_ring.AddIn.Read(R))),
						Basic())
				})
			arg.Step(
				"One more p-th power preserves the preceding additive law",
				func(c *Argument, ih Fact) {
					exponent := c.Have(
						"The next exponent applies the p-th power once more",
						"p ^ suc(n) = p ^ n * p",
						ByArith(nat_arith.NatPow))
					powerA := comm_monoid.PowIn.Read(multiplicative).At(a, c.TermAs[Nat]("p ^ n"))
					powerB := comm_monoid.PowIn.Read(multiplicative).At(b, c.TermAs[Nat]("p ^ n"))
					powersIn := c.Have(
						"The preceding powers lie in the ring carrier",
						"«power»(a) ∈ R.carrier ∧ «power»(b) ∈ R.carrier",
						By(comm_monoid.PowIn.Read(multiplicative), a, b))
					c.Show(
						"Apply p-power additivity to the preceding carrier powers",
						Simp(
							Fwd(exponent),
							Rev(comm_monoid.PowPowOn.Read(multiplicative)),
							Fwd(comm_ring.AddIn.Read(R)),
							Fwd(ih)),
						By(R, powersIn, characteristic, FrobeniusAdditive.Read(R).At(p, powerA, powerB)))
				})
		})
		return ctx.Theorem(headline,
			func(arg *Argument, R comm_ring.CommRingFact[on.R], p, n *Expr[Nat], characteristic Fact) {
				multiplicative := comm_ring.MulMonoidOn.Read(R)
				carries := arg.Have(
					"The iterated power map preserves the carrier",
					"∀x:A. x ∈ R.carrier ⇒ «map»(x) ∈ R.carrier",
					Simp(Fwd(FrobeniusPowerDef)),
					By(comm_monoid.PowIn.Read(multiplicative)))
				additive := arg.Have(
					"The iterated power map preserves addition on the carrier",
					"∀x y:A. x ∈ R.carrier ∧ y ∈ R.carrier ⇒ «map»(x + y) = «map»(x) + «map»(y)",
					Simp(Fwd(FrobeniusPowerDef)),
					By(R, characteristic, additivePowers))
				products := arg.Have(
					"The iterated power map preserves multiplication on the carrier",
					"∀x y:A. x ∈ R.carrier ∧ y ∈ R.carrier ⇒ «map»(x * y) = «map»(x) * «map»(y)",
					Simp(Fwd(FrobeniusPowerDef)),
					By(comm_monoid.MulPowOn.Read(multiplicative)))
				one := arg.Have(
					"The iterated power map preserves one",
					"«map»(R.one) = R.one",
					Simp(Fwd(FrobeniusPowerDef)),
					By(comm_monoid.IdentityPowOn.Read(multiplicative)))
				ring := arg.TermAs[RingOps[A]]("R")
				arg.Show(
					"These are exactly the carrier ring-homomorphism laws",
					By(
						R,
						additive,
						products,
						carries,
						one,
						ring_homomorphism.RingHomomorphism.At(ring, ring, arg.TermAs[Fun[A, A]]("«map»"))))
			})
	}),
})}

// FrobeniusFixesIntegers — in characteristic q the q-th power map fixes the
// image of every integer. The map x ↦ x^q is a ring homomorphism, so it fixes
// the numeral n·1; an integer is n or −n, its image n·1 or −(n·1), and the
// homomorphism keeps negatives.
var FrobeniusFixesIntegers = frobeniusFixesIntegersThm{family.Add(registry.ProofEntry{
	Name: "FrobeniusFixesIntegers",
	Key:  "prop_ea9c0e9a91ab499d",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀q:num. ∀z:int.",
		Hypotheses: []string{
			"ring_prime_characteristic(R, q)",
		},
		Conclusion: "monoid_pow(R.mul, R.one, integer_map(R, z), q) = integer_map(R, z)",
	},
		func(
			arg *Argument,
			ring comm_ring.CommRingFact[on.R],
			q *Expr[Nat],
			z *Expr[Int],
			characteristic Fact,
		) {
			frobenius := arg.Have(
				"in characteristic q the q-th power map is a ring homomorphism",
				"ring_homomorphism(R, R, frobenius_power(R, q ^ 1))",
				By(FrobeniusRingHomomorphism.Read(ring), characteristic))
			n, signs := arg.ObtainAs[Nat](
				"z is a natural number n or its negative",
				"∃n:num. z = n ∨ z = -n",
				By(int_embed.Image.At(z)))
			one := arg.MemberOf[on.R](arg.TermAs[A]("R.one"), comm_ring.OneIn.Read(ring))
			numeral := comm_monoid.PowIn.Read(comm_ring.AddMonoidOn.Read(ring)).At(one, n)
			fixed := arg.Have(
				"so it fixes the numeral n·1",
				"monoid_pow(R.mul, R.one, monoid_pow(R.add, R.zero, R.one, n), q) = "+
					"monoid_pow(R.add, R.zero, R.one, n)",
				By(ring_homomorphism.RingMapNumeral.Read(frobenius), FrobeniusPowerDef, nat_arith.PowOne))
			arg.Show(
				"the image of z is n·1 or its negative",
				signs.SplitDisj(
					LeftHolds(
						"z = n: its image is the numeral n·1",
						Given(func(b *Argument, natural Fact) {
							b.Show(
								"which the q-th power fixes",
								By(natural, fixed, characteristic_zero.IntegerMapOfNum.Read(ring).At(n)))
						})),
					RightHolds(
						"z = −n: its image is −(n·1)",
						Given(func(b *Argument, negative Fact) {
							b.Show(
								"the homomorphism keeps the negative of the numeral it fixes",
								By(
									negative,
									fixed,
									numeral,
									characteristic_zero.IntegerMapNegOfNum.Read(ring).At(n),
									ring_homomorphism.MapNeg.Read(frobenius).AsFact().At(numeral),
									FrobeniusPowerDef,
									nat_arith.PowOne))
						}))))
		}),
})}

// FiniteFieldPerfect — every power of the characteristic is bijective on a
// finite field: it is a field endomorphism, hence injective, and a finite
// self-injection is onto.
var FiniteFieldPerfect = finiteFieldPerfectThm{family.Add(registry.ProofEntry{
	Name: "FiniteFieldPerfect",
	Key:  "prop_8a090b69fd3b9fb",
	Build: family.Theorem(Statement{
		Binders: "∀k:field_on(A). ∀p n:num.",
		Hypotheses: []string{
			"finite(k.carrier)",
			"ring_prime_characteristic(field_ring(k), p)",
		},
		Conclusion: "injective_on(k.carrier, frobenius_power(field_ring(k), p ^ n)) ∧ " +
			"image(frobenius_power(field_ring(k), p ^ n), k.carrier) = k.carrier",
	}, func(a *Argument, k Fact, p, n *Expr[Nat], finite, characteristic Fact) {
		ring := field.RingOn.Read(k)
		ringValue := a.TermAs[RingOps[A]]("field_ring(k)")
		fieldValue := a.TermAs[FieldOps[A]]("k")
		power := a.TermAs[Fun[A, A]]("frobenius_power(field_ring(k), p ^ n)")
		hom := a.Have(
			"The p^n-th power is a field endomorphism",
			"ring_homomorphism(field_ring(k), field_ring(k), frobenius_power(field_ring(k), p ^ n))",
			By(ring, characteristic, FrobeniusRingHomomorphism.At(ringValue, p, n)))
		injective := a.Have(
			"A field endomorphism is injective on its carrier",
			"injective_on(k.carrier, frobenius_power(field_ring(k), p ^ n))",
			By(k, hom, ring_homomorphism.FieldHomomorphismInjective.At(fieldValue, fieldValue, power)))
		a.Show(
			"An injection of the finite carrier into itself is onto",
			BySets(
				ring_homomorphism.MapIn.Read(hom),
				injective,
				finite,
				cardinality.SurjectiveIffInjective.At(a.TermAs[Set[A]]("k.carrier"), power)))
	}),
})}

// PolynomialRingCharacteristic — the polynomials over a ring of prime
// characteristic p have characteristic p: the constants carry the numerals
// of the ring to those of the polynomials, and they keep zero.
var PolynomialRingCharacteristic = polynomialRingCharacteristicThm{family.Add(registry.ProofEntry{
	Name: "PolynomialRingCharacteristic",
	Key:  "prop_28b650414009ca0e",
	Build: family.Theorem(Statement{
		Binders: "∀R:comm_ring_on(A). ∀p:num.",
		Hypotheses: []string{
			"ring_prime_characteristic(R, p)",
		},
		Conclusion: "ring_prime_characteristic(polynomial_ring(R), p)",
	},
		func(a *Argument, ring comm_ring.CommRingFact[on.R], p *Expr[Nat], characteristic Fact) {
			constants := polynomial.ConstantPolynomialHomomorphism.Read(ring)
			additive := comm_ring.AddMonoidOn.Read(ring)
			one := a.TermAs[A]("R.one")
			oneMember := a.MemberOf[on.R](one, comm_ring.OneIn.Read(ring))
			prime := a.Unfolded(characteristic, PrimeCharacteristicDef)
			numerals := a.Have(
				"the constants carry each numeral of R to that numeral of the polynomials",
				"∀n:num. "+
					"    monoid_pow(R.add, R.zero, R.one, n) • basis_vector(0) = "+
					"    monoid_pow(vec_add, vec_zero, basis_vector(0), n)",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					b.Induct(n)
					b.Base(
						"the zeroth numerals are the zeros, which the constants keep",
						Simp(Fwd(comm_monoid.MonoidPowDef)),
						By(ring_homomorphism.MapZero.Read(constants)))
					b.Step(
						"one more summand is one in both rings, and the constants keep sums",
						func(c *Argument, ih Fact) {
							c.Show(
								"the constants keep one and sums",
								Simp(Fwd(comm_monoid.MonoidPowDef)),
								By(
									ih,
									oneMember,
									ring_homomorphism.MapOne.Read(constants),
									comm_monoid.PowIn.Read(additive).AsFact().At(oneMember, n),
									ring_homomorphism.MapAdd.Read(constants).AsFact().At(
										one, c.TermAs[A]("monoid_pow(R.add, R.zero, R.one, n)"))))
						})
				}))
			vanishes := a.Have(
				"the numeral p of the polynomials is the constant of the numeral p of R, which is zero",
				"monoid_pow(vec_add, vec_zero, basis_vector(0), p) = vec_zero",
				By(numerals.At(p), prime, ring_homomorphism.MapZero.Read(constants)))
			a.Show(
				"p is prime and the numeral p of the polynomials is zero",
				By(
					prime,
					vanishes,
					PrimeCharacteristicDef.At(a.TermAs[module_record.RingOps[Fun[Nat, A]]]("polynomial_ring(R)"), p)))
		}),
})}

// PowersInsideSubfield — a subfield holds the p-th powers of its points, a power
// of a point being a product of points.
var PowersInsideSubfield = powersInsideSubfieldThm{family.Add(registry.ProofEntry{
	Name: "PowersInsideSubfield",
	Key:  "prop_3c9df36cc5197e95",
	Build: family.Theorem(Statement{
		Binders:    "∀M:field_on(A). ∀p:num. ∀S:set(A).",
		Hypotheses: []string{"subfield(M, S)"},
		Conclusion: "image(frobenius_power(field_ring(M), p), S) ⊆ S",
	}, func(a *Argument, M field.FieldFact[on.M], p *Expr[Nat], S *Expr[Set[A]], subfieldS Fact) {
		restricted := a.Have(
			"S is a field under the operations of M",
			"field_on(restrict_field(M, S))",
			By(subfieldS, field.SubfieldFieldOn.Read(M).At(S)))
		a.Show(
			"a power of a point of S is a product of points of S",
			BySets(
				comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(field.RingOn.Read(restricted))),
				FrobeniusPowerDef))
	}),
})}
