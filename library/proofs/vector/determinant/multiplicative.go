package determinant

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/vector/matrix"
	"github.com/euc-ai/xugo/library/registry"
)

// MatrixProductOver — multiplying two matrices over a commutative ring
// preserves their carrier and square support, by closure of finite sums.
var MatrixProductOver = matrixProductOverThm{family.Add(registry.ProofEntry{
	Name: "MatrixProductOver",
	Key:  "prop_455c316e2f7c7a10",
	Build: family.Sections(Statement{
		Binders:    "∀c:comm_ring_on(A). ∀n:num. ∀P Q:(num → num → A).",
		Hypotheses: []string{"matrix_over(c, n, P)", "matrix_over(c, n, Q)"},
		Conclusion: "matrix_over(c, n, matrix_product(c, n, P, Q))",
	}, func(ctx *Script, headline string) *GoalStackNode {
		products := ctx.Lemma(Statement{
			Binders: "∀c:comm_ring_on(A). ∀n:num. ∀P Q:(num → num → A).",
			Hypotheses: []string{
				"matrix_over(c, n, P)",
				"matrix_over(c, n, Q)",
			},
			Conclusion: "∀i j:num. " +
				"    matrix_product(c, n, P, Q, i, j) ∈ c.carrier ∧ " +
				"    (n ≤ i ∨ n ≤ j ⇒ matrix_product(c, n, P, Q, i, j) = c.zero)",
		},
			func(
				a *Argument,
				c comm_ring.CommRingFact[on.C],
				n *Expr[Nat],
				P, Q *Mat[A, DimN, DimN],
				members Fact,
				i, j *Expr[Nat],
			) {
				terms := a.Have(
					"each summand lies in the carrier and vanishes outside the product square",
					"∀k:num. P(i, k) * Q(k, j) ∈ c.carrier ∧ (n ≤ i ∨ n ≤ j ⇒ P(i, k) * Q(k, j) = c.zero)",
					Derive(func(b *Argument) {
						b.FixAs[Nat]("k")
						p, q := b.TermAs[A]("P(i, k)"), b.TermAs[A]("Q(k, j)")
						b.Show(
							"a zero row or column annihilates the corresponding product",
							By(
								members,
								MatrixOverEntries.Read(c).At(n, P),
								MatrixOverEntries.Read(c).At(n, Q),
								comm_ring.MulIn.Read(c).AsFact().At(p, q),
								comm_ring.MulLeftZeroOn.Read(c).AsFact().At(q),
								comm_ring.MulRightZeroOn.Read(c).AsFact().At(p)))
					}))
				regular := module.RegularModuleOn.Read(c)
				indices := a.TermAs[Set[Nat]]("{k:num | k < n}")
				summand := a.TermAs[Fun[Nat, A]]("λk:num. P(i, k) * Q(k, j)")
				a.Show(
					"the finite sum preserves membership and zero absorption",
					Simp(Fwd(matrix.MatrixProductDef)),
					By(
						terms,
						num_segment.FiniteBelowStrict.At(n),
						module.ModuleSumIn.Read(regular).AsFact().At(indices, summand),
						module.ModuleSumZero.Read(regular).AsFact().At(indices, summand)))
			})
		return ctx.Theorem(headline, func(
			a *Argument,
			c comm_ring.CommRingFact[on.C],
			n *Expr[Nat],
			P, Q *Mat[A, DimN, DimN],
			members Fact,
		) {
			product := a.MatAs[A, DimN, DimN]("matrix_product(c, n, P, Q)")
			a.Show(
				"the product entry conditions make it a matrix over the ring",
				By(members, Read(products, c).At(n, P, Q), MatrixOverEntries.Read(c).At(n, product)))
		})
	}),
})}

// MatrixProductRightIdentity — the identity matrix leaves each matrix
// unchanged: each column below n selects one summand, and every entry outside
// the square stays zero.
var MatrixProductRightIdentity = matrixProductRightIdentityThm{family.Add(registry.ProofEntry{
	Name: "MatrixProductRightIdentity",
	Key:  "prop_2dda7b53bbfa2d0b",
	Build: family.Theorem(Statement{
		Binders:    "∀c:comm_ring_on(A). ∀n:num. ∀P:(num → num → A).",
		Hypotheses: []string{"matrix_over(c, n, P)"},
		Conclusion: "matrix_product(c, n, P, matrix_identity(c, n)) = P",
	}, func(
		a *Argument,
		c comm_ring.CommRingFact[on.C],
		n *Expr[Nat],
		P *Mat[A, DimN, DimN],
		member Fact,
	) {
		a.Do(Funext())
		a.FixAs[Nat]("i")
		j := a.FixAs[Nat]("j")
		entries := MatrixOverEntries.Read(c).At(n, P)
		terms := a.Have(
			"the identity column keeps the matching index and kills every other one",
			"∀k:num. k < n ⇒ P(i, k) * matrix_identity(c, n, k, j) = COND(k = j, P(i, j), c.zero)",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("k")
				below := b.Assume()
				p := b.TermAs[A]("P(i, k)")
				b.Show(
					"the identity entry is one at the matching index and zero elsewhere",
					Simp(Fwd(MatrixIdentityDef)),
					By(
						below,
						member,
						entries,
						comm_ring.MulRightZeroOn.Read(c).AsFact().At(p),
						comm_monoid.RightIdentityOn.Read(comm_ring.MulMonoidOn.Read(c)).AsFact().At(p)))
			}))
		values := a.Have(
			"each summand lies in the ring carrier",
			"∀k:num. k ∈ {r:num | r < n} ⇒ P(i, k) * matrix_identity(c, n, k, j) ∈ c.carrier",
			BySets(terms, member, entries, comm_ring.ZeroIn.Read(c)))
		regular := module.RegularModuleOn.Read(c)
		finiteIndices := num_segment.FiniteBelowStrict.At(n)
		indices := a.TermAs[Set[Nat]]("{k:num | k < n}")
		summand := a.TermAs[Fun[Nat, A]]("λk:num. P(i, k) * matrix_identity(c, n, k, j)")
		a.Do(Simp(Fwd(matrix.MatrixProductDef)))
		a.Cases(a.Term("j < n"))
		a.When(
			"a column below n has its unique diagonal index",
			func(b *Argument, below Fact) {
				b.Show(
					"the finite sum is its one surviving diagonal term",
					BySets(
						terms,
						values,
						below,
						finiteIndices,
						module.ModuleSumSingle.Read(regular).AsFact().At(indices, j, summand)))
			})
		a.Otherwise(
			"a column from n on has only zero summands",
			func(b *Argument, outside Fact) {
				b.Show(
					"the finite sum and the matrix entry are both zero",
					BySets(
						outside,
						terms,
						member,
						entries,
						nat_order.NotLessThan.At(j, n),
						finiteIndices,
						module.ModuleSumZero.Read(regular).AsFact().At(indices, summand)))
			})
	}),
})}

// matrixProductReplaceColumn — multiplying by P turns the replacement of
// column j by u into the replacement of that column by P·u.
func matrixProductReplaceColumn(ctx *Script) *GoalStackNode {
	return ctx.Lemma(Statement{
		Binders: "∀c:comm_ring_on(A). ∀n:num. ∀P Q:(num → num → A). ∀j:num. ∀u:(num → A).",
		Hypotheses: []string{
			"matrix_over(c, n, P)",
			"matrix_over(c, n, Q)",
			"u ∈ free_module_record(c, {i:num | i < n}).carrier",
		},
		Conclusion: "matrix_product(c, n, P, matrix_replace_column(c, n, Q, j, u)) = " +
			"matrix_replace_column(c, n, matrix_product(c, n, P, Q), j, «column map»(u))",
	}, func(
		a *Argument,
		c comm_ring.CommRingFact[on.C],
		n *Expr[Nat],
		P, Q *Mat[A, DimN, DimN],
		j *Expr[Nat],
		u *Vec[A, DimN],
		given Fact,
	) {
		a.Do(Funext())
		r, s := a.FixAs[Nat]("r"), a.FixAs[Nat]("s")
		ring := a.TermAs[RingOps[A]]("c")
		a.Cases(a.Term("r < n ∧ s < n"))
		a.When(
			"inside the square, the selected column uses the column map",
			func(b *Argument, inside Fact) {
				b.Do(Simp(Fwd(matrix.MatrixProductDef), Fwd(ColumnReplaceDef)))
				indices := b.TermAs[Set[Nat]]("{k:num | k < n}")
				f := b.TermAs[Fun[Nat, A]](
					"λk:num. P(r, k) * COND(k < n ∧ s < n, COND(s = j, u(k), Q(k, s)), c.zero)")
				b.Cases(b.Term("s = j"))
				b.When(
					"the replacement column is multiplied by P",
					func(d *Argument, selected Fact) {
						d.Show(
							"the row sum is the corresponding entry of the column image",
							BySets(
								selected,
								inside,
								module.ModuleSumCongruence.At(
									d.TermAs[Op[A]]("c.add"),
									d.TermAs[A]("c.zero"),
									indices,
									f,
									d.TermAs[Fun[Nat, A]]("λk:num. P(r, k) * u(k)"))))
					})
				b.Otherwise(
					"every other column agrees with the original product",
					func(d *Argument, other Fact) {
						d.Show(
							"the row sum keeps the original column",
							BySets(
								other,
								inside,
								module.ModuleSumCongruence.At(
									d.TermAs[Op[A]]("c.add"),
									d.TermAs[A]("c.zero"),
									indices,
									f,
									d.TermAs[Fun[Nat, A]]("λk:num. P(r, k) * Q(k, s)"))))
					})
			})
		a.Otherwise(
			"outside the square, both sides are zero",
			func(b *Argument, outside Fact) {
				product := b.MatAs[A, DimN, DimN]("matrix_product(c, n, P, Q)")
				column := b.VecAs[A, DimN]("«column map»(u)")
				entry := b.Have(
					"the replaced output entry is zero outside the square",
					"matrix_replace_column(c, n, matrix_product(c, n, P, Q), j, «column map»(u), r, s) = "+
						"COND(r < n ∧ s < n, COND(s = j, «column map»(u, r), matrix_product(c, n, P, Q, r, s)), c.zero)",
					By(ColumnReplaceDef.At(ring, n, product, j, column, r, s)))
				b.Do(entry.Rw())
				q := b.MatAs[A, DimN, DimN]("matrix_replace_column(c, n, Q, j, u)")
				productIn := b.Have(
					"the product with the replaced matrix is a matrix over the ring",
					"matrix_over(c, n, matrix_product(c, n, P, matrix_replace_column(c, n, Q, j, u)))",
					By(given, ReplaceColumnMatrixOver.At(ring, n, Q, j, u), MatrixProductOver.Read(c).At(n, P, q)))
				b.Show(
					"the product entry vanishes outside the square",
					By(
						outside,
						productIn,
						MatrixOverEntries.Read(c).At(
							n, b.MatAs[A, DimN, DimN]("matrix_product(c, n, P, matrix_replace_column(c, n, Q, j, u))")),
						nat_order.NotLessThan.At(r, n),
						nat_order.NotLessThan.At(s, n)))
			})
	})
}

// determinantCompositeMultilinear — det(P·Q) is multilinear in the columns
// of Q.
func determinantCompositeMultilinear(ctx *Script, transport *GoalStackNode) *GoalStackNode {
	return ctx.Lemma(Statement{
		Binders:    "∀c:comm_ring_on(A). ∀n:num. ∀P:(num → num → A).",
		Hypotheses: []string{"matrix_over(c, n, P)"},
		Conclusion: "column_multilinear(c, " +
			"    n, " +
			"    λQ:(num → num → A). determinant(c, n, matrix_product(c, n, P, Q)))",
	}, func(
		a *Argument,
		c comm_ring.CommRingFact[on.C],
		n *Expr[Nat],
		P *Mat[A, DimN, DimN],
		member Fact,
	) {
		ring := a.TermAs[RingOps[A]]("c")
		free := a.Have(
			"the vectors over c on the points below n form a module over c",
			"module_on(c, free_module_record(c, {i:num | i < n}))",
			By(c, free_module.FreeModuleOn.At(ring, a.TermAs[Set[Nat]]("{i:num | i < n}"))))
		// the column map of P is linear on that module
		linear := a.Simplified(GroupPremises(member, MatrixColumnMapLinear.Read(c).At(n, P)))
		multilinear := a.Conjuncts(
			a.Unfolded(DeterminantColumnMultilinear.Read(c).At(n), ColumnMultilinearDef),
			"determinants take carrier values",
			"the determinant preserves column sums",
			"and column multiples")
		additive, homogeneous := multilinear[1], multilinear[2]
		a.Do(Unfold(ColumnMultilinearDef))
		a.Show(
			"the composite takes carrier values and is additive and homogeneous in each column",
			SplitConjAll(
				Case(
					"a matrix product has its determinant in the carrier",
					Derive(func(b *Argument) {
						Q := b.MatFixAs[A, DimN, DimN]("Q")
						given := b.Assume()
						b.Show(
							"matrix product closure supplies the determinant's carrier premise",
							By(
								c,
								member,
								given,
								MatrixProductOver.Read(c).At(n, P, Q),
								DeterminantInCarrier.Read(c).At(n, b.MatAs[A, DimN, DimN]("matrix_product(c, n, P, Q)"))))
					})),
				Case(
					"replacing a column by a sum commutes with the column map, which is additive",
					Derive(func(b *Argument) {
						Q := b.MatFixAs[A, DimN, DimN]("Q")
						j := b.FixAs[Nat]("j")
						u, v := b.VecFixAs[A, DimN]("u"), b.VecFixAs[A, DimN]("v")
						given := b.Assume()
						images := b.Have(
							"the column images and the sum of the two vectors lie in the free module",
							"«column map»(u) ∈ free_module_record(c, {i:num | i < n}).carrier ∧ "+
								"«column map»(v) ∈ free_module_record(c, {i:num | i < n}).carrier ∧ "+
								"fun_add(u, v) ∈ free_module_record(c, {i:num | i < n}).carrier",
							By(
								given,
								module_homomorphism.HomIn.Read(linear).AsFact().At(u),
								module_homomorphism.HomIn.Read(linear).AsFact().At(v),
								group.MulIn.Read(module.AddGroupOn.Read(free))))
						columnAdditive := b.Have(
							"the column map preserves the sum",
							"«column map»(fun_add(u, v)) = fun_add(«column map»(u), «column map»(v))",
							By(given, module_homomorphism.HomAdd.Read(linear).AsFact().At(u, v)))
						b.Show(
							"multiplying by P turns each column replacement into one "+
								"by the column's image, where the determinant is additive",
							Simp(Fwd(Read(transport, c)), Fwd(columnAdditive)),
							By(
								c,
								additive.At(
									b.MatAs[A, DimN, DimN]("matrix_product(c, n, P, Q)"),
									j,
									b.VecAs[A, DimN]("«column map»(u)"),
									b.VecAs[A, DimN]("«column map»(v)")),
								images,
								given,
								member,
								MatrixProductOver.Read(c).At(n, P, Q)))
					})),
				Case(
					"replacing a column by a multiple commutes with the column map, which is homogeneous",
					Derive(func(b *Argument) {
						Q := b.MatFixAs[A, DimN, DimN]("Q")
						j := b.FixAs[Nat]("j")
						u := b.VecFixAs[A, DimN]("u")
						scalar := b.FixAs[A]("a")
						given := b.Assume()
						parts := b.Conjuncts(
							given,
							"Q is a matrix over c",
							"column j is below n",
							"u lies in the coordinate module",
							"a lies in the ring")
						um, am := b.MemberOf[on.Any](&u.Expr, parts[2]), b.MemberOf[on.Any](scalar, parts[3])
						images := b.Have(
							"the column image and the multiple of the vector lie in the free module",
							"«column map»(u) ∈ free_module_record(c, {i:num | i < n}).carrier ∧ "+
								"fun_smul(a, u) ∈ free_module_record(c, {i:num | i < n}).carrier",
							By(given, module_homomorphism.HomIn.Read(linear).AsFact().At(u), module.SmulIn.Read(free)))
						columnHomogeneous := b.Have(
							"the column map preserves the multiple",
							"«column map»(fun_smul(a, u)) = fun_smul(a, «column map»(u))",
							By(module_homomorphism.HomSmul.Read(linear).At(am, um)))
						b.Show(
							"multiplying by P turns each column replacement into one "+
								"by the column's image, where the determinant is homogeneous",
							Simp(Fwd(Read(transport, c)), Fwd(columnHomogeneous)),
							By(
								c,
								homogeneous.At(
									b.MatAs[A, DimN, DimN]("matrix_product(c, n, P, Q)"),
									j,
									b.VecAs[A, DimN]("«column map»(u)"),
									scalar),
								images,
								given,
								member,
								MatrixProductOver.Read(c).At(n, P, Q)))
					})),
			))
	})
}

// matrixProductEqualColumns — two equal columns of Q stay equal in P·Q.
func matrixProductEqualColumns(ctx *Script) *GoalStackNode {
	return ctx.Lemma(Statement{
		Binders: "∀R:ring_ops(A). ∀n:num. ∀P Q:(num → num → A). ∀i j:num.",
		Hypotheses: []string{
			"transpose(Q, i) = transpose(Q, j)",
		},
		Conclusion: "transpose(matrix_product(R, n, P, Q), i) = transpose(matrix_product(R, n, P, Q), j)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			n *Expr[Nat],
			P, Q *Mat[A, DimN, DimN],
			i, j *Expr[Nat],
			equal Fact,
		) {
			a.Do(equal.Simp(Fwd(matrix.TransposeDef)), Funext())
			a.FixAs[Nat]("r")
			a.Show(
				"equal column entries give equal finite row sums",
				Simp(Fwd(matrix.TransposeDef), Fwd(matrix.MatrixProductDef)),
				By(
					equal,
					module.ModuleSumCongruence.At(
						a.TermAs[Op[A]]("R.add"),
						a.TermAs[A]("R.zero"),
						a.TermAs[Set[Nat]]("{k:num | k < n}"),
						a.TermAs[Fun[Nat, A]]("λk:num. R.mul(P(r, k), Q(k, i))"),
						a.TermAs[Fun[Nat, A]]("λk:num. R.mul(P(r, k), Q(k, j))"))))
		})
}

// DeterminantMultiplicative — left multiplication gives an alternating column form;
// its value at the identity gives the determinant product formula.
var DeterminantMultiplicative = determinantMultiplicativeThm{family.Add(registry.ProofEntry{
	Name: "DeterminantMultiplicative",
	Key:  "prop_d6b8a36e99655a4b",
	Build: family.Sections(Statement{
		Binders: "∀c:comm_ring_on(A). ∀n:num. ∀P Q:(num → num → A).",
		Hypotheses: []string{
			"matrix_over(c, n, P)",
			"matrix_over(c, n, Q)",
		},
		Conclusion: "determinant(c, n, matrix_product(c, n, P, Q)) = " +
			"determinant(c, n, P) * determinant(c, n, Q)",
	}, determinantMultiplicative),
})}

// determinantMultiplicative — Q ↦ det(P·Q) is an alternating form, so
// universality evaluates it as det(P·I) times det(Q).
func determinantMultiplicative(ctx *Script, headline string) *GoalStackNode {
	transport := matrixProductReplaceColumn(ctx)
	multilinear := determinantCompositeMultilinear(ctx, transport)
	equalColumns := matrixProductEqualColumns(ctx)
	alternating := ctx.Lemma(Statement{
		Binders: "∀c:comm_ring_on(A). ∀n:num. ∀P:(num → num → A).",
		Hypotheses: []string{
			"matrix_over(c, n, P)",
		},
		Conclusion: "alternating_form(c, " +
			"    n, " +
			"    λQ:(num → num → A). determinant(c, n, matrix_product(c, n, P, Q)))",
	},
		func(
			a *Argument,
			c comm_ring.CommRingFact[on.C],
			n *Expr[Nat],
			P *Mat[A, DimN, DimN],
			member Fact,
		) {
			ring := a.TermAs[RingOps[A]]("c")
			a.Do(Unfold(AlternatingFormDef))
			a.Show(
				"the composite is multilinear and vanishes on a repeated column",
				SplitConj(
					Case(
						"left multiplication preserves column multilinearity",
						By(member, Read(multilinear, c).At(n, P))),
					Case(
						"a repeated column remains repeated after left multiplication",
						Derive(func(b *Argument) {
							Q := b.MatFixAs[A, DimN, DimN]("Q")
							i, j := b.FixAs[Nat]("i"), b.FixAs[Nat]("j")
							given := b.Assume()
							determinantAlternates := b.Have(
								"the determinant is alternating",
								"alternating_form(c, n, determinant(c, n))",
								By(DeterminantAlternating.Read(c).At(n)))
							parts := b.Conjuncts(
								b.Unfolded(determinantAlternates, AlternatingFormDef),
								"the determinant is column multilinear",
								"a repeated column makes its determinant zero")
							b.Show(
								"the product has a repeated column and hence determinant zero",
								By(
									c,
									given,
									member,
									parts[1].At(b.MatAs[A, DimN, DimN]("matrix_product(c, n, P, Q)"), i, j),
									MatrixProductOver.Read(c).At(n, P, Q),
									At(equalColumns, ring, n, P, Q, i, j)))
						}))))
		})
	return ctx.Theorem(headline, func(
		a *Argument,
		c comm_ring.CommRingFact[on.C],
		n *Expr[Nat],
		P, Q *Mat[A, DimN, DimN],
		members Fact,
	) {
		a.Show(
			"universality evaluates the alternating composite at the identity",
			CalcEq(
				Leg(
					a.TermAs[A](
						"determinant(c, n, matrix_product(c, n, P, matrix_identity(c, n))) * determinant(c, n, Q)"),
					"evaluate the alternating composite on Q",
					By(
						members,
						Read(alternating, c).At(n, P),
						AlternatingFormUniversal.Read(c).At(
							n,
							a.TermAs[Fun[Fun2[Nat, Nat, A], A]](
								"λQ:(num → num → A). determinant(c, n, matrix_product(c, n, P, Q))"),
							Q))),
				FinalLeg(
					"the identity matrix leaves P unchanged",
					By(Normalized, c, members, MatrixProductRightIdentity.Read(c).At(n, P)))))
	})
}

// DeterminantChangeBasis — a change of basis preserves the determinant:
// multiplicativity reduces the change to a scalar product equal to one.
var DeterminantChangeBasis = determinantChangeBasisThm{family.Add(registry.ProofEntry{
	Name: "DeterminantChangeBasis",
	Key:  "prop_228e72b52bcd192",
	Build: family.Theorem(Statement{
		Binders: "∀c:comm_ring_on(A). ∀n:num. ∀P Q U:(num → num → A).",
		Hypotheses: []string{
			"matrix_over(c, n, P)",
			"matrix_over(c, n, Q)",
			"matrix_over(c, n, U)",
			"matrix_product(c, n, Q, U) = matrix_identity(c, n)",
		},
		Conclusion: "determinant(c, n, matrix_product(c, n, Q, matrix_product(c, n, P, U))) = " +
			"determinant(c, n, P)",
	}, determinantChangeBasis),
})}

func determinantChangeBasis(
	a *Argument,
	c comm_ring.CommRingFact[on.C],
	n *Expr[Nat],
	P, Q, U *Mat[A, DimN, DimN],
	given Fact,
) {
	product := a.MatAs[A, DimN, DimN]("matrix_product(c, n, P, U)")
	productIn := a.Have(
		"P times U is a matrix over the carrier ring",
		"matrix_over(c, n, matrix_product(c, n, P, U))",
		By(given, MatrixProductOver.Read(c).At(n, P, U)))
	unitProduct := a.Have(
		"the determinants of Q and U multiply to one",
		"determinant(c, n, Q) * determinant(c, n, U) = c.one",
		By(c, given, DeterminantMultiplicative.Read(c).At(n, Q, U), DeterminantIdentity.Read(c).At(n)))
	scalars := a.Have(
		"the three determinants lie in the ring carrier",
		"determinant(c, n, P) ∈ c.carrier ∧ "+
			"determinant(c, n, Q) ∈ c.carrier ∧ "+
			"determinant(c, n, U) ∈ c.carrier",
		By(
			given,
			DeterminantInCarrier.Read(c).At(n, P),
			DeterminantInCarrier.Read(c).At(n, Q),
			DeterminantInCarrier.Read(c).At(n, U)))
	a.Show(
		"multiplicativity and the unit determinant product preserve the determinant",
		CalcEq(
			Leg(
				a.TermAs[A]("determinant(c, n, Q) * (determinant(c, n, P) * determinant(c, n, U))"),
				"expand the two matrix products",
				By(
					given,
					productIn,
					DeterminantMultiplicative.Read(c).At(n, Q, product),
					DeterminantMultiplicative.Read(c).At(n, P, U))),
			Leg(
				a.TermAs[A]("determinant(c, n, P) * (determinant(c, n, Q) * determinant(c, n, U))"),
				"regroup the three carrier scalars",
				ByArith(c, scalars)),
			FinalLeg(
				"the determinant product of Q and U is the ring one",
				unitProduct.Rw(),
				ByArith(c, scalars))))
}
