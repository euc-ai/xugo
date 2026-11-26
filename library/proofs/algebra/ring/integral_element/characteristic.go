// characteristic.go — the determinant trick: det(z·I − P) for a matrix P over
// a subring S is the value at z of a monic polynomial over S, so an eigenvalue
// z of P with a nonzero eigenvector in the field is integral over S, and so is
// every element of a subring of the field finitely spanned over S.

package integral_element

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/vector/determinant"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// CharacteristicPolynomial — for a square matrix P over a subring S of a
// field and z in the field, det(z·I − P) is the value at z of a monic
// polynomial over S of degree n. Shift the columns one at a time: with the
// first k columns of a matrix Q over S shifted to z·e_s − Q_s, the
// determinant is the value at z of a polynomial over S of degree at most k
// whose k-th coefficient is the determinant with those columns e_s. The claim
// is made for every matrix Q because the step changes the matrix: column k
// splits by multilinearity into z times column e_k and minus column Q_k, the
// first term being Q with column k replaced by e_k, the second Q itself, both
// shifted k columns deep. With g₁ and g₂ their polynomials, the polynomial
// for k + 1 is X·g₁ − g₂, its leading coefficient g₁(k). At k = n the leading
// coefficient is det I = 1.
var CharacteristicPolynomial = characteristicPolynomialThm{family.Add(registry.ProofEntry{
	Name: "CharacteristicPolynomial",
	Key:  "prop_d6f02e55183bc8b0",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S:set(A). ∀n:num. ∀P:(num → num → A). ∀z:A.",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"matrix_over(restrict_ring(field_ring(L), S), n, P)",
			"z ∈ L.carrier",
		},
		Conclusion: "∃g:(num → A). " +
			"    polynomial_over(S, g) ∧ " +
			"    polynomial_monic(g) ∧ " +
			"    polynomial_degree(g) = n ∧ " +
			"    polynomial_eval(g, z) = " +
			"    determinant(field_ring(L), " +
			"        n, " +
			"        λr:num. λs:num. z * matrix_identity(field_ring(L), n, r, s) - P(r, s))",
		Abbrev: Abbrev{
			{Name: "shifted", Text: "λk:num. λQ:(num → num → A). λr:num. λs:num. " +
				"    COND(s < k, z * matrix_identity(field_ring(L), n, r, s) - Q(r, s), Q(r, s))"},
			{Name: "leading", Text: "λk:num. λQ:(num → num → A). λr:num. λs:num. " +
				"    COND(s < k, matrix_identity(field_ring(L), n, r, s), Q(r, s))"},
			{Name: "R", Text: "restrict_ring(field_ring(L), S)"},
		},
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		S *Expr[Set[A]],
		n *Expr[Nat],
		P *Arrow2[Nat, Nat, A],
		z *Expr[A],
		subS, overS, zIn Fact,
	) {
		ring := field.RingOn.Read(L)
		c := a.TermAs[RingOps[A]]("field_ring(L)")
		cS := a.TermAs[RingOps[A]]("«R»")
		below := a.TermAs[Set[Nat]]("{i:num | i < n}")
		ringS := a.Have(
			"S is a ring under L's operations",
			"comm_ring_on(«R»)",
			By(subS, comm_ring.SubringRingOn.Read(ring).At(S)))
		inside := a.Have(
			"S lies in L",
			"S ⊆ L.carrier",
			By(comm_ring.SubringSubset.Read(subS)))
		polynomials := polynomial.PolynomialRingOn.Read(ringS)
		zeroShift := a.Have(
			"shifting zero by z leaves zero",
			"z * L.zero - L.zero = L.zero",
			ByArith(L, zIn))
		multilinear := a.Conjuncts(
			a.Unfolded(
				determinant.DeterminantColumnMultilinear.Read(ring).At(n), determinant.ColumnMultilinearDef),
			"determinants of matrices over L lie in L",
			"the determinant is additive in each column",
			"and homogeneous in each column")
		free := a.Have(
			"the vectors over L on the points below n form a module over L",
			"module_on(field_ring(L), free_module_record(field_ring(L), {i:num | i < n}))",
			By(ring, free_module.FreeModuleOn.At(c, below)))

		columns := a.Have(
			"with k columns shifted, the determinant is a polynomial over "+
				"S of degree at most k at z, led by the identity's columns",
			Statement{
				Binders:    "∀k:num. ∀Q:(num → num → A).",
				Hypotheses: []string{"k ≤ n", "matrix_over(«R», n, Q)"},
				Conclusion: "∃g:(num → A). " +
					"    polynomial_over(S, g) ∧ " +
					"    vec⟨suc(k)⟩(g) ∧ " +
					"    g(k) = determinant(field_ring(L), n, «leading»(k, Q)) ∧ " +
					"    polynomial_eval(g, z) = determinant(field_ring(L), n, «shifted»(k, Q))",
			},
			Derive(func(b *Argument) {
				b.Induct("k")
				b.Base(
					"with no column shifted both matrices are Q, and det Q is a constant over S",
					func(d *Argument) {
						Q := d.FixAs[Fun2[Nat, Nat, A]]("Q")
						overQ := d.Conjuncts(
							d.Assume(),
							"no column lies past n",
							"Q is a matrix over S")[1]
						d.Do(Simp(Fwd(nat_order.LessThanZeroClause)))
						sameDeterminant := d.Have(
							"the determinant over S is the determinant over L",
							"determinant(field_ring(L), n, Q) = determinant(«R», n, Q)",
							Unfold(determinant.DeterminantDef))
						valueInS := d.Have(
							"det Q lies in S",
							"determinant(field_ring(L), n, Q) ∈ S",
							By(Normalized, sameDeterminant, overQ, determinant.DeterminantInCarrier.Read(ringS).At(n, Q)))
						valueInL := d.Have(
							"so in L",
							"determinant(field_ring(L), n, Q) ∈ L.carrier",
							By(valueInS, inside, set_basic.SubsetDef))
						constant := d.TermAs[Fun[Nat, A]]("determinant(field_ring(L), n, Q) • basis_vector(0)")
						over := d.Have(
							"the constant polynomial det Q is over S",
							"polynomial_over(S, determinant(field_ring(L), n, Q) • basis_vector(0))",
							By(
								ringS,
								valueInS,
								module.SmulIn.Read(polynomial.PolynomialModuleOn.Read(ringS)),
								polynomial.BasisVectorOver.Read(ringS).At(d.TermAs[Nat]("0"))))
						short := d.Have(
							"it vanishes from degree one on",
							"vec⟨suc(0)⟩(determinant(field_ring(L), n, Q) • basis_vector(0))",
							Simp(Fwd(vec_space.VecDef)),
							Derive(func(e *Argument) {
								e.FixAs[Nat]("i")
								past := e.Assume()
								e.Show(
									"past the constant term the basis vector vanishes",
									ByArith(L, past, valueInL, vec_space.VecScalarMulDef, vec_space.BasisVectorDef))
							}))
						coefficient := d.Have(
							"its constant coefficient is det Q",
							"vec_scalar_mul(determinant(field_ring(L), n, Q), basis_vector(0), 0) = "+
								"determinant(field_ring(L), n, Q)",
							ByArith(L, valueInL, vec_space.VecScalarMulDef, vec_space.BasisVectorDef))
						value := d.Have(
							"and its value at z is det Q",
							"polynomial_eval(determinant(field_ring(L), n, Q) • basis_vector(0), z) = "+
								"determinant(field_ring(L), n, Q)",
							By(
								valueInL,
								zIn,
								polynomial_evaluation.EvalConstant.Read(ring).AsFact().At(
									d.TermAs[A]("determinant(field_ring(L), n, Q)"), z)))
						d.Take(constant)
						d.Show(
							"the constant polynomial det Q",
							By(over, short, coefficient, value))
					})
				b.Step(
					"shifting column k splits the determinant into z times "+
						"one with column e_k and minus one with column Q_k",
					func(d *Argument, shallower Fact) {
						k := d.TermAs[Nat]("k")
						Q := d.FixAs[Fun2[Nat, Nat, A]]("Q")
						given := d.Conjuncts(
							d.Assume(),
							"column k lies inside the block",
							"Q is a matrix over S")
						room, overQ := given[0], given[1]
						kBelow := d.Have(
							"k < n",
							"k < n",
							ByArith(room))
						unit := d.TermAs[Fun[Nat, A]]("delta_at(k)")
						next := d.TermAs[Fun2[Nat, Nat, A]]("matrix_replace_column(«R», n, Q, k, delta_at(k))")
						padding := determinant.MatrixOverEntries.Read(ringS).At(n, Q)
						recursion := d.Have(
							"the determinant is z times the one for Q with column k replaced "+
								"by e_k, minus the one for Q, both shifted k columns deep",
							"determinant(field_ring(L), n, «shifted»(suc(k), Q)) = "+
								"z * "+
								"determinant(field_ring(L), n, «shifted»(k, matrix_replace_column(«R», n, Q, k, delta_at(k)))) - "+
								"determinant(field_ring(L), n, «shifted»(k, Q))",
							Derive(func(e *Argument) {
								X := e.TermAs[Fun2[Nat, Nat, A]]("«shifted»(suc(k), Q)")
								column := e.TermAs[Fun[Nat, A]]("λr:num. Q(r, k)")
								entries := e.Have(
									"Q's entries lie in L",
									"∀i j:num. Q(i, j) ∈ L.carrier",
									By(overQ, padding, inside, set_basic.SubsetDef))
								whole := e.Have(
									"the shifted matrix is itself with column k put back",
									"«shifted»(suc(k), Q) = "+
										"matrix_replace_column(field_ring(L), "+
										"    n, "+
										"    «shifted»(suc(k), Q), "+
										"    k, "+
										"    λr:num. z * matrix_identity(field_ring(L), n, r, k) - Q(r, k))",
									Derive(func(f *Argument) {
										f.Do(Simp(Fwd(determinant.ColumnReplaceDef)), Funext())
										r, s := f.FixAs[Nat]("r"), f.FixAs[Nat]("s")
										f.Do(CondRewrite())
										f.Show(
											"entry by entry, inside and outside the block",
											By(
												zeroShift,
												kBelow,
												overQ,
												padding,
												determinant.MatrixIdentityDef.At(c, n, r, s),
												nat_order.LessThanSucClause.At(s, k),
												nat_order.NotLessThan.At(r, n),
												nat_order.NotLessThan.At(s, n)))
									}))
								split := e.Have(
									"its column k is z·e_k − Q_k",
									"(λr:num. z * matrix_identity(field_ring(L), n, r, k) - Q(r, k)) = "+
										"fun_add(fun_smul(z, delta_at(k)), fun_smul(-L.one, λr:num. Q(r, k)))",
									Derive(func(f *Argument) {
										f.Do(Funext())
										r := f.FixAs[Nat]("r")
										f.Do(Simp(
											Fwd(function_module.FunAddDef),
											Fwd(function_module.FunSmulDef),
											Fwd(free_module.DeltaAtDef),
											Fwd(determinant.MatrixIdentityDef)))
										f.Cases(Equal(r, k))
										f.When(
											"on the diagonal",
											func(g *Argument, atK Fact) {
												g.Show(
													"z·1 − Q(k, k)",
													ByArith(L, atK, kBelow, zIn, entries.At(r, k)))
											})
										f.Otherwise(
											"off the diagonal",
											func(g *Argument, offK Fact) {
												g.Show(
													"z·0 − Q(r, k)",
													ByArith(L, offK, zIn, entries.At(r, k)))
											})
									}))
								withUnit := e.Have(
									"with column k replaced by e_k, the matrix is shifted "+
										"k columns deep in Q with column k replaced by e_k",
									"matrix_replace_column(field_ring(L), n, «shifted»(suc(k), Q), k, delta_at(k)) = "+
										"«shifted»(k, matrix_replace_column(«R», n, Q, k, delta_at(k)))",
									Derive(func(f *Argument) {
										f.Do(Simp(Fwd(determinant.ColumnReplaceDef), Fwd(free_module.DeltaAtDef)), Funext())
										r, s := f.FixAs[Nat]("r"), f.FixAs[Nat]("s")
										f.Do(CondRewrite())
										f.Show(
											"entry by entry",
											By(
												zeroShift,
												kBelow,
												determinant.MatrixIdentityDef.At(c, n, r, s),
												nat_order.LessThanSucClause.At(s, k),
												nat_order.LessThanTrans.At(s, k, n),
												nat_order.LessThanIrrefl.At(k),
												nat_order.NotLessThan.At(r, n),
												nat_order.NotLessThan.At(s, n)))
									}))
								withColumn := e.Have(
									"with column k replaced by Q_k, the matrix is Q shifted k columns deep",
									"matrix_replace_column(field_ring(L), n, «shifted»(suc(k), Q), k, λr:num. Q(r, k)) = "+
										"«shifted»(k, Q)",
									Derive(func(f *Argument) {
										f.Do(Simp(Fwd(determinant.ColumnReplaceDef)), Funext())
										r, s := f.FixAs[Nat]("r"), f.FixAs[Nat]("s")
										f.Do(CondRewrite())
										f.Show(
											"entry by entry, Q vanishing outside the block",
											By(
												zeroShift,
												kBelow,
												overQ,
												padding,
												determinant.MatrixIdentityDef.At(c, n, r, s),
												nat_order.LessThanSucClause.At(s, k),
												nat_order.LessThanTrans.At(s, k, n),
												nat_order.LessThanIrrefl.At(k),
												nat_order.NotLessThan.At(r, n),
												nat_order.NotLessThan.At(s, n)))
									}))
								shiftedEntries := e.Have(
									"the shifted matrix has its entries in L",
									"∀i j:num. «shifted»(suc(k), Q, i, j) ∈ L.carrier",
									Derive(func(f *Argument) {
										i, j := f.FixAs[Nat]("i"), f.FixAs[Nat]("j")
										f.Do(CondRewrite())
										f.Show(
											"differences and products of members of L",
											By(
												entries.At(i, j),
												zIn,
												comm_ring.SubIn.Read(ring),
												comm_ring.MulIn.Read(ring),
												determinant.MatrixIdentityDef.At(c, n, i, j),
												comm_ring.OneIn.Read(ring),
												comm_ring.ZeroIn.Read(ring)))
									}))
								shiftedPadding := e.Have(
									"and vanishes outside the block",
									"∀i j:num. n ≤ i ∨ n ≤ j ⇒ «shifted»(suc(k), Q, i, j) = L.zero",
									Derive(func(f *Argument) {
										i, j := f.FixAs[Nat]("i"), f.FixAs[Nat]("j")
										outside := f.Assume()
										f.Do(CondRewrite())
										f.Show(
											"Q and the identity vanish there, and z·0 − 0 = 0",
											By(
												zeroShift,
												kBelow,
												outside,
												overQ,
												padding,
												determinant.MatrixIdentityDef.At(c, n, i, j),
												nat_order.LessThanSucIffLessEq.At(j, k),
												nat_order.NotLessThan.At(i, n),
												nat_order.NotLessThan.At(k, n),
												nat_order.LessEqTrans.At(n, j, k)))
									}))
								shiftedOver := e.Have(
									"so it is a matrix over L",
									"matrix_over(field_ring(L), n, «shifted»(suc(k), Q))",
									By(shiftedEntries, shiftedPadding, determinant.MatrixOverEntries.Read(ring).At(n, X)))
								support := e.Have(
									"column k of Q vanishes from row n on",
									"fun_support(L.zero, λx:num. Q(x, k)) ⊆ {i:num | i < n}",
									BySets(overQ, padding, nat_order.NotLessThan))
								columnIn := e.Have(
									"so it is a vector over L on the points below n",
									"(λr:num. Q(r, k)) ∈ finite_supp(L.zero, L.carrier, {i:num | i < n})",
									By(
										entries,
										support,
										function_module.FiniteSuppMember,
										finite_set.FiniteSubset,
										num_segment.FiniteBelowStrict.At(n)))
								unitIn := free_module.DeltaAtIn.Read(ring).At(below, k)
								additive := e.Have(
									"the determinant adds over column k = z·e_k + (−1)·Q_k",
									"determinant(field_ring(L), "+
										"    n, "+
										"    matrix_replace_column(field_ring(L), "+
										"        n, "+
										"        «shifted»(suc(k), Q), "+
										"        k, "+
										"        fun_add(fun_smul(z, delta_at(k)), fun_smul(-L.one, λr:num. Q(r, k))))) = "+
										"determinant(field_ring(L), "+
										"    n, "+
										"    matrix_replace_column(field_ring(L), "+
										"        n, "+
										"        «shifted»(suc(k), Q), "+
										"        k, "+
										"        fun_smul(z, delta_at(k)))) + "+
										"determinant(field_ring(L), "+
										"    n, "+
										"    matrix_replace_column(field_ring(L), "+
										"        n, "+
										"        «shifted»(suc(k), Q), "+
										"        k, "+
										"        fun_smul(-L.one, λr:num. Q(r, k))))",
									By(
										multilinear[1].At(
											X,
											k,
											e.TermAs[Fun[Nat, A]]("fun_smul(z, delta_at(k))"),
											e.TermAs[Fun[Nat, A]]("fun_smul(-L.one, λr:num. Q(r, k))")),
										free,
										zIn,
										columnIn,
										kBelow,
										shiftedOver,
										unitIn,
										module.SmulIn.Read(free),
										comm_ring.NegIn.Read(ring),
										comm_ring.OneIn.Read(ring)))
								homogeneous := e.Have(
									"and takes the scalars z and −1 out",
									"determinant(field_ring(L), "+
										"    n, "+
										"    matrix_replace_column(field_ring(L), "+
										"        n, "+
										"        «shifted»(suc(k), Q), "+
										"        k, "+
										"        fun_smul(z, delta_at(k)))) = "+
										"z * "+
										"determinant(field_ring(L), "+
										"    n, "+
										"    matrix_replace_column(field_ring(L), n, «shifted»(suc(k), Q), k, delta_at(k))) ∧ "+
										"determinant(field_ring(L), "+
										"    n, "+
										"    matrix_replace_column(field_ring(L), "+
										"        n, "+
										"        «shifted»(suc(k), Q), "+
										"        k, "+
										"        fun_smul(-L.one, λr:num. Q(r, k)))) = "+
										"-L.one * "+
										"determinant(field_ring(L), "+
										"    n, "+
										"    matrix_replace_column(field_ring(L), n, «shifted»(suc(k), Q), k, λr:num. Q(r, k)))",
									By(
										multilinear[2].At(X, k, unit, z),
										multilinear[2].At(X, k, column, e.TermAs[A]("-L.one")),
										zIn,
										columnIn,
										kBelow,
										shiftedOver,
										unitIn,
										comm_ring.NegIn.Read(ring),
										comm_ring.OneIn.Read(ring)))
								withUnitMatrix := e.TermAs[Fun2[Nat, Nat, A]](
									"matrix_replace_column(field_ring(L), n, «shifted»(suc(k), Q), k, delta_at(k))")
								withColumnMatrix := e.TermAs[Fun2[Nat, Nat, A]](
									"matrix_replace_column(field_ring(L), n, «shifted»(suc(k), Q), k, λr:num. Q(r, k))")
								partsIn := e.Have(
									"both determinants lie in L",
									"determinant(field_ring(L), "+
										"    n, "+
										"    matrix_replace_column(field_ring(L), n, «shifted»(suc(k), Q), k, delta_at(k))) ∈ "+
										"L.carrier ∧ "+
										"determinant(field_ring(L), "+
										"    n, "+
										"    matrix_replace_column(field_ring(L), n, «shifted»(suc(k), Q), k, λr:num. Q(r, k))) ∈ "+
										"L.carrier",
									By(
										multilinear[0].At(withUnitMatrix),
										multilinear[0].At(withColumnMatrix),
										columnIn,
										shiftedOver,
										kBelow,
										unitIn,
										determinant.ReplaceColumnMatrixOver.At(c, n, X, k, unit),
										determinant.ReplaceColumnMatrixOver.At(c, n, X, k, column)))
								rewritten := e.Have(
									"read through the column identities",
									"determinant(field_ring(L), n, «shifted»(suc(k), Q)) = "+
										"determinant(field_ring(L), "+
										"    n, "+
										"    matrix_replace_column(field_ring(L), "+
										"        n, "+
										"        «shifted»(suc(k), Q), "+
										"        k, "+
										"        fun_add(fun_smul(z, delta_at(k)), fun_smul(-L.one, λr:num. Q(r, k))))) ∧ "+
										"determinant(field_ring(L), "+
										"    n, "+
										"    matrix_replace_column(field_ring(L), n, «shifted»(suc(k), Q), k, delta_at(k))) = "+
										"determinant(field_ring(L), n, «shifted»(k, matrix_replace_column(«R», n, Q, k, delta_at(k)))) ∧ "+
										"determinant(field_ring(L), "+
										"    n, "+
										"    matrix_replace_column(field_ring(L), n, «shifted»(suc(k), Q), k, λr:num. Q(r, k))) = "+
										"determinant(field_ring(L), n, «shifted»(k, Q))",
									By(split, withUnit, withColumn, whole))
								unitValue := e.TermAs[A](
									"determinant(field_ring(L), " +
										"    n, " +
										"    matrix_replace_column(field_ring(L), n, «shifted»(suc(k), Q), k, delta_at(k)))")
								columnValue := e.TermAs[A](
									"determinant(field_ring(L), " +
										"    n, " +
										"    matrix_replace_column(field_ring(L), n, «shifted»(suc(k), Q), k, λr:num. Q(r, k)))")
								e.Show(
									"z times the first determinant plus −1 times the second",
									By(
										additive,
										zIn,
										homogeneous,
										partsIn,
										rewritten,
										comm_ring.NegOneMulOn.Read(ring).AsFact().At(columnValue),
										comm_ring.SubAddNegOn.Read(ring).AsFact().At(
											e.TermAs[A](
												"z * "+
													"determinant(field_ring(L), "+
													"    n, "+
													"    matrix_replace_column(field_ring(L), n, «shifted»(suc(k), Q), k, delta_at(k)))"),
											columnValue),
										comm_ring.MulIn.Read(ring).AsFact().At(z, unitValue)))
							}))
						nextOver := d.Have(
							"Q with column k replaced by e_k is a matrix over S",
							"matrix_over(«R», n, matrix_replace_column(«R», n, Q, k, delta_at(k)))",
							By(
								kBelow,
								overQ,
								free_module.DeltaAtIn.Read(ringS).At(below, k),
								determinant.ReplaceColumnMatrixOver.At(cS, n, Q, k, unit)))
						shallowRoom := nat_order.LessEqOfLessThan.At(k, n)
						unitPolynomial, unitRelation := d.ObtainAs[Fun[Nat, A]](
							"shifted k deep, Q with column k replaced by e_k gives a polynomial g₁",
							"∃g:(num → A). "+
								"    polynomial_over(S, g) ∧ "+
								"    vec⟨suc(k)⟩(g) ∧ "+
								"    g(k) = "+
								"    determinant(field_ring(L), "+
								"        n, "+
								"        «leading»(k, matrix_replace_column(«R», n, Q, k, delta_at(k)))) ∧ "+
								"    polynomial_eval(g, z) = "+
								"    determinant(field_ring(L), n, «shifted»(k, matrix_replace_column(«R», n, Q, k, delta_at(k))))",
							By(kBelow, nextOver, shallowRoom, shallower.At(next)),
							Named("g₁"))
						columnPolynomial, columnRelation := d.ObtainAs[Fun[Nat, A]](
							"and Q itself gives a polynomial g₂",
							"∃g:(num → A). "+
								"    polynomial_over(S, g) ∧ "+
								"    vec⟨suc(k)⟩(g) ∧ "+
								"    g(k) = determinant(field_ring(L), n, «leading»(k, Q)) ∧ "+
								"    polynomial_eval(g, z) = determinant(field_ring(L), n, «shifted»(k, Q))",
							By(kBelow, overQ, shallowRoom, shallower.At(Q)),
							Named("g₂"))
						unitParts := d.Conjuncts(
							unitRelation,
							"g₁ is over S",
							"g₁ vanishes past k",
							"its k-th coefficient",
							"its value at z")
						columnParts := d.Conjuncts(
							columnRelation,
							"g₂ is over S",
							"g₂ vanishes past k",
							"its k-th coefficient",
							"its value at z")
						unitCoefficients := d.Have(
							"g₁ has its coefficients in L",
							"∀i:num. g₁(i) ∈ L.carrier",
							By(
								subS,
								unitParts[0],
								polynomial.PolynomialOverDef,
								comm_ring.SubringSubset.Read(subS),
								set_basic.SubsetDef))
						overL := d.Have(
							"g₁ and g₂ are polynomials over L",
							"polynomial_over(L.carrier, g₁) ∧ polynomial_over(L.carrier, g₂)",
							By(inside, unitParts[0], columnParts[0], polynomial.PolynomialOverMono))
						step := d.TermAs[Fun[Nat, A]]("vec_sub(polynomial_mul(g₁, basis_vector(1)), g₂)")
						stepOver := d.Have(
							"X·g₁ − g₂ is over S",
							"polynomial_over(S, vec_sub(polynomial_mul(g₁, basis_vector(1)), g₂))",
							By(
								unitParts[0],
								columnParts[0],
								comm_ring.SubIn.Read(polynomials),
								comm_ring.MulIn.Read(polynomials),
								polynomial.PolynomialRingDef,
								module_record.RestrictRingDef,
								polynomial.BasisVectorOver.Read(ringS).At(d.TermAs[Nat]("1"))))
						unitPast := d.Unfolded(unitParts[1], vec_space.VecDef)
						columnPast := d.Unfolded(columnParts[1], vec_space.VecDef)
						stepShort := d.Have(
							"it vanishes past k + 1",
							"vec⟨suc(suc(k))⟩(vec_sub(polynomial_mul(g₁, basis_vector(1)), g₂))",
							Simp(Fwd(vec_space.VecDef)),
							Derive(func(e *Argument) {
								i := e.FixAs[Nat]("i")
								past := e.Assume()
								indices := e.Have(
									"i − 1 and i are past k",
									"1 ≤ i ∧ suc(k) ≤ i - 1 ∧ suc(k) ≤ i",
									ByArith(past))
								vanish := e.Have(
									"zero minus zero",
									"L.zero - L.zero = L.zero",
									ByArith(L))
								e.Show(
									"both terms vanish there",
									By(
										unitPast.At(e.TermAs[Nat]("i - 1")),
										columnPast.At(i),
										vanish,
										indices,
										unitCoefficients,
										vec_space.VecSubDef,
										polynomial.PolynomialMulBasisVector.Read(ring).At(unitPolynomial, e.TermAs[Nat]("1"), i)))
							}))
						stepLeading := d.Have(
							"its coefficient k + 1 is g₁(k), the leading determinant one column deeper",
							"vec_sub(polynomial_mul(g₁, basis_vector(1)), g₂, suc(k)) = "+
								"determinant(field_ring(L), n, «leading»(suc(k), Q))",
							Derive(func(e *Argument) {
								leadingNext := e.Have(
									"the leading matrix one column deeper is the leading matrix of Q with column k replaced by e_k",
									"«leading»(suc(k), Q) = «leading»(k, matrix_replace_column(«R», n, Q, k, delta_at(k)))",
									Derive(func(f *Argument) {
										f.Do(Simp(Fwd(determinant.ColumnReplaceDef), Fwd(free_module.DeltaAtDef)), Funext())
										r, s := f.FixAs[Nat]("r"), f.FixAs[Nat]("s")
										f.Do(CondRewrite())
										f.Show(
											"entry by entry",
											By(
												zeroShift,
												kBelow,
												overQ,
												padding,
												determinant.MatrixIdentityDef.At(c, n, r, s),
												nat_order.LessThanSucClause.At(s, k),
												nat_order.NotLessThan.At(r, n),
												nat_order.NotLessThan.At(s, n)))
									}))
								next := e.TermAs[Nat]("suc(k)")
								shift := e.Have(
									"k + 1 shifted back by one is k",
									"suc(k) - 1 = k ∧ 1 ≤ suc(k)",
									ByArith())
								gone := e.Have(
									"g₂ vanishes at k + 1",
									"g₂(suc(k)) = L.zero",
									By(columnPast.At(next), nat_order.LessEqRefl.At(next)))
								e.Show(
									"X·g₁ − g₂ at k + 1",
									ByArith(
										L,
										unitCoefficients.At(k),
										unitCoefficients,
										unitParts[2],
										leadingNext,
										shift,
										gone,
										vec_space.VecSubDef,
										polynomial.PolynomialMulBasisVector.Read(ring).At(
											unitPolynomial, e.TermAs[Nat]("1"), e.TermAs[Nat]("suc(k)"))))
							}))
						zm := d.MemberOf[on.L](z, zIn)
						variable := d.TermAs[Fun[Nat, A]]("basis_vector(1)")
						product := d.TermAs[Fun[Nat, A]]("polynomial_mul(g₁, basis_vector(1))")
						expanded := d.Have(
							"its value at z is g₁(z)·z − g₂(z)",
							"polynomial_eval(vec_sub(polynomial_mul(g₁, basis_vector(1)), g₂), z) = "+
								"polynomial_eval(g₁, z) * monoid_pow(L.mul, L.one, z, 1) - polynomial_eval(g₂, z) ∧ "+
								"polynomial_eval(g₁, z) ∈ L.carrier ∧ "+
								"polynomial_eval(g₂, z) ∈ L.carrier",
							By(
								overL,
								polynomial.BasisVectorOver.Read(ring).At(d.TermAs[Nat]("1")),
								polynomial.PolynomialMulOver.Read(ring).AsFact().At(unitPolynomial, variable),
								polynomial_evaluation.EvalSub.Read(ring).At(product, columnPolynomial, zm),
								polynomial_evaluation.EvalMul.Read(ring).At(unitPolynomial, variable, zm),
								polynomial_evaluation.EvalBasisVector.Read(ring).At(d.TermAs[Nat]("1"), zm),
								polynomial_evaluation.EvalIn.Read(ring).At(unitPolynomial, zm),
								polynomial_evaluation.EvalIn.Read(ring).At(columnPolynomial, zm)))
						commuted := d.Have(
							"z commutes past g₁(z)",
							"polynomial_eval(g₁, z) * monoid_pow(L.mul, L.one, z, 1) = z * polynomial_eval(g₁, z)",
							ByArith(L, zIn, expanded))
						stepValue := d.Have(
							"so its value at z is the determinant one column deeper",
							"polynomial_eval(vec_sub(polynomial_mul(g₁, basis_vector(1)), g₂), z) = "+
								"determinant(field_ring(L), n, «shifted»(suc(k), Q))",
							By(recursion, commuted, unitParts[3], columnParts[3], expanded))
						d.Take(step)
						d.Show(
							"X·g₁ − g₂ is the polynomial one column deeper",
							By(stepOver, stepShort, stepLeading, stepValue))
					})
			}))

		// At k = n: the shifted matrix is z·I − P, the leading one I.
		polynomialOf, relation := a.ObtainAs[Fun[Nat, A]](
			"with every column shifted, P gives a polynomial g",
			"∃g:(num → A). "+
				"    polynomial_over(S, g) ∧ "+
				"    vec⟨suc(n)⟩(g) ∧ "+
				"    g(n) = determinant(field_ring(L), n, «leading»(n, P)) ∧ "+
				"    polynomial_eval(g, z) = determinant(field_ring(L), n, «shifted»(n, P))",
			By(overS, nat_order.LessEqRefl.At(n), columns.At(n, P)),
			Named("g"))
		parts := a.Conjuncts(
			relation,
			"g is over S",
			"g vanishes past n",
			"its n-th coefficient",
			"its value at z")
		paddingP := determinant.MatrixOverEntries.Read(ringS).At(n, P)
		leadingIdentity := a.Have(
			"with every column the identity's, the leading matrix is I",
			"«leading»(n, P) = matrix_identity(field_ring(L), n)",
			Derive(func(b *Argument) {
				b.Do(Funext())
				r, s := b.FixAs[Nat]("r"), b.FixAs[Nat]("s")
				b.Do(CondRewrite())
				b.Show(
					"past the block both vanish",
					By(overS, paddingP, determinant.MatrixIdentityDef.At(c, n, r, s), nat_order.NotLessThan.At(s, n)))
			}))
		shiftedAll := a.Have(
			"and the shifted matrix is z·I − P",
			"«shifted»(n, P) = (λr:num. λs:num. z * matrix_identity(field_ring(L), n, r, s) - P(r, s))",
			Derive(func(b *Argument) {
				b.Do(Funext())
				r, s := b.FixAs[Nat]("r"), b.FixAs[Nat]("s")
				b.Do(CondRewrite())
				outside := b.Assume()
				vanish := b.Have(
					"P and I vanish past the block",
					"P(r, s) = L.zero ∧ matrix_identity(field_ring(L), n, r, s) = L.zero",
					By(
						outside,
						overS,
						paddingP,
						determinant.MatrixIdentityDef.At(c, n, r, s),
						nat_order.NotLessThan.At(s, n),
						nat_order.LessThanTrans.At(r, s, n)))
				b.Show(
					"so z·0 − 0 = 0",
					ByArith(L, zIn, vanish))
			}))
		leadingOne := a.Have(
			"so g(n) = det I = 1",
			"g(n) = L.one",
			By(leadingIdentity, parts[2], determinant.DeterminantIdentity.Read(ring).At(n)))
		degree := a.Have(
			"g has degree n",
			"polynomial_degree(g) = n",
			By(
				leadingOne,
				parts[0],
				parts[1],
				field.OneNotZeroOn.Read(L),
				polynomial.DegreeExact.At(a.TermAs[A]("L.zero"), S, polynomialOf, n)))
		a.Take(polynomialOf)
		a.Show(
			"g is monic of degree n over S with value det(z·I − P) at z",
			By(leadingOne, degree, shiftedAll, parts[0], parts[3], polynomial.PolynomialMonicDef))
	}),
})}

// EigenvalueIntegral — an eigenvalue z of a square matrix P over a subring S
// of a field, with an eigenvector e in the field that is not zero, is integral
// over S: the matrix z·I − P kills e, so its determinant is zero
// (determinant.DeterminantDependentColumns), and that determinant is the value
// at z of the characteristic polynomial, monic over S of degree n ≥ 1.
var EigenvalueIntegral = eigenvalueIntegralThm{family.Add(registry.ProofEntry{
	Name: "EigenvalueIntegral",
	Key:  "prop_6734e750a2fe29e3",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S:set(A). ∀n:num. ∀P:(num → num → A). ∀z:A. ∀e:(num → A). ∀j:num.",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"matrix_over(restrict_ring(field_ring(L), S), n, P)",
			"z ∈ L.carrier",
			"∀i:num. i < n ⇒ e(i) ∈ L.carrier",
			"j < n",
			"e(j) ≠ L.zero",
			"∀i:num. i < n ⇒ z * e(i) = module_sum(L.add, L.zero, {k:num | k < n}, λk:num. P(i, k) * e(k))",
		},
		Conclusion: "integral_over(restrict_ring(field_ring(L), S), z)",
		Abbrev: Abbrev{
			{Name: "zI − P", Text: "λr:num. λs:num. z * matrix_identity(field_ring(L), n, r, s) - P(r, s)"},
		},
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		S *Expr[Set[A]],
		n *Expr[Nat],
		P *Arrow2[Nat, Nat, A],
		z *Expr[A],
		e *Arrow[Nat, A],
		j *Expr[Nat],
		subS, overS, zIn, vectorIn, jBelow, nonzero, eigen Fact,
	) {
		ring := field.RingOn.Read(L)
		regular := module.RegularModuleOn.Read(ring)
		identity := a.TermAs[Fun2[Nat, Nat, A]]("matrix_identity(field_ring(L), n)")
		shifted := a.TermAs[Fun2[Nat, Nat, A]]("«zI − P»")
		below := a.TermAs[Set[Nat]]("{k:num | k < n}")
		zm := a.MemberOf[on.L](z, zIn)
		g, characteristic := a.ObtainAs[Fun[Nat, A]](
			"the characteristic polynomial: monic over S of degree n, with value det(z·I − P) at z",
			"∃g:(num → A). "+
				"    polynomial_over(S, g) ∧ "+
				"    polynomial_monic(g) ∧ "+
				"    polynomial_degree(g) = n ∧ "+
				"    polynomial_eval(g, z) = determinant(field_ring(L), n, «zI − P»)",
			By(subS, overS, CharacteristicPolynomial.Read(L).At(S, n, P, zm)),
			Named("g"))
		ringS := a.Have(
			"S is a ring under L's operations",
			"comm_ring_on(restrict_ring(field_ring(L), S))",
			By(subS, comm_ring.SubringRingOn.Read(ring).At(S)))
		entriesP := a.Have(
			"P's entries lie in L and vanish past the block",
			"∀i k:num. P(i, k) ∈ L.carrier ∧ (n ≤ i ∨ n ≤ k ⇒ P(i, k) = L.zero)",
			By(
				subS,
				overS,
				determinant.MatrixOverEntries.Read(ringS).At(n, P),
				comm_ring.SubringSubset.Read(subS),
				set_basic.SubsetDef))
		entriesI := a.Have(
			"so do the identity's",
			"∀i k:num. "+
				"    matrix_identity(field_ring(L), n, i, k) ∈ L.carrier ∧ "+
				"    (n ≤ i ∨ n ≤ k ⇒ matrix_identity(field_ring(L), n, i, k) = L.zero)",
			By(
				determinant.MatrixOverEntries.Read(ring).At(n, identity),
				determinant.MatrixIdentityOver.Read(ring).At(n)))
		zeroShift := a.Have(
			"shifting zero by z leaves zero",
			"z * L.zero - L.zero = L.zero",
			ByArith(L, zIn))
		shiftedOver := a.Have(
			"z·I − P is a matrix over L",
			"matrix_over(field_ring(L), n, «zI − P»)",
			Simp(Fwd(determinant.MatrixOverEntries.Read(ring))),
			By(zIn, entriesP, entriesI, zeroShift, comm_ring.SubIn.Read(ring), comm_ring.MulIn.Read(ring)))
		kernel := a.Have(
			"z·I − P kills e",
			Statement{
				Binders:    "∀r:num.",
				Hypotheses: []string{"r < n"},
				Conclusion: "module_sum(L.add, " +
					"    L.zero, " +
					"    {k:num | k < n}, " +
					"    λk:num. (z * matrix_identity(field_ring(L), n, r, k) - P(r, k)) * e(k)) = " +
					"L.zero",
			},
			Derive(func(b *Argument) {
				r := b.FixAs[Nat]("r")
				rBelow := b.Assume()
				atoms := b.Have(
					"the entries of row r and the coordinates of e lie in L",
					Statement{
						Binders:    "∀k:num.",
						Hypotheses: []string{"k < n"},
						Conclusion: "P(r, k) ∈ L.carrier ∧ " +
							"matrix_identity(field_ring(L), n, r, k) ∈ L.carrier ∧ " +
							"e(k) ∈ L.carrier",
					},
					By(entriesP, entriesI, vectorIn))
				terms := b.Have(
					"each term of row r of z·I − P against e, and of row r of P against e, lies in L",
					Statement{
						Binders:    "∀k:num.",
						Hypotheses: []string{"k < n"},
						Conclusion: "(z * matrix_identity(field_ring(L), n, r, k) - P(r, k)) * e(k) ∈ L.carrier ∧ " +
							"P(r, k) * e(k) ∈ L.carrier",
					},
					Derive(func(d *Argument) {
						k := d.FixAs[Nat]("k")
						d.Show(
							"products and differences of members of L",
							By(d.Assume(), atoms.At(k), zIn, comm_ring.MulIn.Read(ring), comm_ring.SubIn.Read(ring)))
					}))
				recombined := b.Have(
					"the two terms add to z times the identity term",
					Statement{
						Binders:    "∀k:num.",
						Hypotheses: []string{"k < n"},
						Conclusion: "(z * matrix_identity(field_ring(L), n, r, k) - P(r, k)) * e(k) + P(r, k) * e(k) = " +
							"z * (matrix_identity(field_ring(L), n, r, k) * e(k))",
					},
					Derive(func(d *Argument) {
						k := d.FixAs[Nat]("k")
						d.Show(
							"a ring identity",
							ByArith(L, d.Assume(), zIn, atoms.At(k)))
					}))
				unitTerms := b.Have(
					"each identity term lies in L",
					"∀k:num. k < n ⇒ matrix_identity(field_ring(L), n, r, k) * e(k) ∈ L.carrier",
					Derive(func(d *Argument) {
						k := d.FixAs[Nat]("k")
						d.Show(
							"a product of members of L",
							By(d.Assume(), atoms.At(k), comm_ring.MulIn.Read(ring)))
					}))
				offTerms := b.Have(
					"and vanishes off the diagonal",
					"∀k:num. k < n ∧ k ≠ r ⇒ matrix_identity(field_ring(L), n, r, k) * e(k) = L.zero",
					By(Normalized, vectorIn, determinant.MatrixIdentityDef, comm_ring.MulLeftZeroOn.Read(ring)))
				unitTerm := b.TermAs[Fun[Nat, A]]("λk:num. matrix_identity(field_ring(L), n, r, k) * e(k)")
				unitSum := b.Have(
					"so the identity row against e is e(r)",
					"module_sum(L.add, "+
						"    L.zero, "+
						"    {k:num | k < n}, "+
						"    λk:num. matrix_identity(field_ring(L), n, r, k) * e(k)) = "+
						"e(r)",
					ByArith(
						L,
						rBelow,
						vectorIn.At(r),
						unitTerms,
						offTerms,
						num_segment.FiniteBelowStrict.At(n),
						module.ModuleSumSingle.Read(regular).At(below, r, unitTerm),
						determinant.MatrixIdentityDef.At(a.TermAs[RingOps[A]]("field_ring(L)"), n, r, r)))
				shiftedRow := b.TermAs[Fun[Nat, A]](
					"λk:num. (z * matrix_identity(field_ring(L), n, r, k) - P(r, k)) * e(k)")
				row := b.TermAs[Fun[Nat, A]]("λk:num. P(r, k) * e(k)")
				split := b.Have(
					"the two row sums add to z·e(r)",
					"module_sum(L.add, "+
						"    L.zero, "+
						"    {k:num | k < n}, "+
						"    λk:num. (z * matrix_identity(field_ring(L), n, r, k) - P(r, k)) * e(k)) + "+
						"module_sum(L.add, L.zero, {k:num | k < n}, λk:num. P(r, k) * e(k)) = "+
						"z * e(r)",
					By(
						recombined,
						unitTerms,
						terms,
						unitSum,
						zIn,
						num_segment.FiniteBelowStrict.At(n),
						module.ModuleSumAdd.Read(regular).At(below, shiftedRow, row),
						module.ModuleSumCongruence.At(
							b.TermAs[Op[A]]("L.add"),
							b.TermAs[A]("L.zero"),
							below,
							b.TermAs[Fun[Nat, A]](
								"λk:num. (z * matrix_identity(field_ring(L), n, r, k) - P(r, k)) * e(k) + P(r, k) * e(k)"),
							b.TermAs[Fun[Nat, A]]("λk:num. z * (matrix_identity(field_ring(L), n, r, k) * e(k))")),
						module.ModuleSumSmul.Read(regular).AsFact().At(below, z, unitTerm)))
				sums := b.Have(
					"both row sums lie in L",
					"module_sum(L.add, "+
						"    L.zero, "+
						"    {k:num | k < n}, "+
						"    λk:num. (z * matrix_identity(field_ring(L), n, r, k) - P(r, k)) * e(k)) ∈ "+
						"L.carrier ∧ "+
						"module_sum(L.add, L.zero, {k:num | k < n}, λk:num. P(r, k) * e(k)) ∈ L.carrier",
					By(
						terms,
						num_segment.FiniteBelowStrict.At(n),
						module.ModuleSumIn.Read(regular).At(below, shiftedRow),
						module.ModuleSumIn.Read(regular).At(below, row)))
				b.Show(
					"z·e(r) is also the row sum of P against e, so the other sum is zero",
					ByArith(L, eigen.At(r), rBelow, vectorIn.At(r), zIn, split, sums))
			}))
		singular := a.Have(
			"so det(z·I − P) = 0",
			"determinant(field_ring(L), n, «zI − P») = L.zero",
			By(
				shiftedOver,
				vectorIn,
				jBelow,
				nonzero,
				kernel,
				determinant.DeterminantDependentColumns.Read(integral_domain.FieldIntegralDomain.Read(L)).At(
					n, shifted, e, j)))
		parts := a.Conjuncts(
			characteristic,
			"g is over S",
			"g is monic",
			"g has degree n",
			"its value at z is det(z·I − P)")
		a.Do(Unfold(IntegralOverDef))
		a.Take(g)
		a.Show(
			"g is a monic relation of positive degree for z",
			ByArith(jBelow, singular, parts[0], parts[1], parts[2], parts[3]))
	}),
})}

// FinitelySpannedIntegral — an element z of a field is integral over a
// subring S when multiplication by z keeps a nonzero S-module N that a finite
// subset E of the field spans. Enumerate E as e(0), …, e(m − 1). Each z·e(i)
// lies in N, so it is an S-combination of the e(k): a matrix P over S with
// z·e = P·e. Some e(j) is not zero, for their span N has a nonzero member; so
// z is an eigenvalue of P with an eigenvector in the field.
var FinitelySpannedIntegral = finitelySpannedIntegralThm{family.Add(registry.ProofEntry{
	Name: "FinitelySpannedIntegral",
	Key:  "prop_13d14be268f8acae",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S N E:set(A). ∀z:A.",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"finite(E)",
			"E ⊆ L.carrier",
			"module_span(restrict_ring(field_ring(L), S), regular_module(field_ring(L)), E) = N",
			"z ∈ L.carrier",
			"image(L.mul(z), N) ⊆ N",
			"∃v:A. v ∈ N ∧ v ≠ L.zero",
		},
		Conclusion: "integral_over(restrict_ring(field_ring(L), S), z)",
		Abbrev: Abbrev{
			{Name: "R", Text: "restrict_ring(field_ring(L), S)"},
		},
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		S, N, E *Expr[Set[A]],
		z *Expr[A],
		subS, finiteE, inField, spans, zIn, stable, nonzero Fact,
	) {
		ring := field.RingOn.Read(L)
		regular := module.RegularModuleOn.Read(ring)
		c := a.TermAs[RingOps[A]]("field_ring(L)")
		scalars := a.TermAs[RingOps[A]]("«R»")
		vectors := a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))")
		indices := a.TermAs[Set[Nat]]("{i:num | i < card(E)}")
		size := a.TermAs[Nat]("card(E)")
		space := a.Have(
			"L is a module over S",
			"module_on(«R», regular_module(field_ring(L)))",
			By(subS, module.RegularModuleOverSubring.Read(ring).At(S)))
		counted := a.Have(
			"the numbers below card(E) are finite and as many as E",
			"finite({i:num | i < card(E)}) ∧ card({i:num | i < card(E)}) = card(E)",
			By(num_segment.HasSizeBelowStrict.At(size), cardinality.HasSizeDef.Inst[Nat]().At(indices, size)))
		e, enumeration := a.ObtainAs[Fun[Nat, A]](
			"enumerate E one to one by the numbers below card(E)",
			"∃e:(num → A). "+
				"    (∀i:num. i ∈ {k:num | k < card(E)} ⇒ e(i) ∈ E) ∧ "+
				"    (∀v:A. v ∈ E ⇒ ∃i:num. i ∈ {k:num | k < card(E)} ∧ e(i) = v) ∧ "+
				"    injective_on({i:num | i < card(E)}, e)",
			By(finiteE, counted, cardinality.CardEqBijection.At(indices, E)),
			Named("e"))
		image := a.Have(
			"E is the image of the enumeration",
			"E = image(e, {i:num | i < card(E)})",
			BySets(enumeration))
		combinations := a.Have(
			"every member of N is an S-combination of the e(k)",
			Statement{
				Binders:    "∀v:A.",
				Hypotheses: []string{"v ∈ N"},
				Conclusion: "∃c:(num → A). " +
					"    (∀k:num. c(k) ∈ S) ∧ " +
					"    v = module_sum(L.add, L.zero, {k:num | k < card(E)}, λk:num. c(k) * e(k))",
			},
			Derive(func(b *Argument) {
				v := b.FixAs[A]("v")
				vIn := b.Assume()
				T, _, finitely := b.Obtain2As[Set[A], Fun[A, A]](
					"v is a combination of finitely many members of E",
					"∃T:set(A). ∃t:(A → A). "+
						"    finite(T) ∧ "+
						"    T ⊆ E ∧ "+
						"    (∀x:A. x ∈ T ⇒ t(x) ∈ S) ∧ "+
						"    v = module_sum(L.add, L.zero, T, λx:A. t(x) * x)",
					By(spans, space, vIn, inField, linear_independence.SpanMembership.At(scalars, vectors, E, v)),
					Named("T", "t"))
				parts := b.Conjuncts(
					finitely,
					"T is finite",
					"T lies in E",
					"t is a scalar on T",
					"v is the combination")
				extended := b.TermAs[Fun[A, A]]("λx:A. COND(x ∈ T, t(x), L.zero) * x")
				extendedIn := b.Have(
					"extended by zero off T, the terms over E lie in L",
					"∀x:A. x ∈ E ⇒ COND(x ∈ T, t(x), L.zero) * x ∈ L.carrier",
					By(
						parts[2],
						subS,
						inField,
						comm_ring.SubringSubset.At(c, S),
						set_basic.SubsetDef,
						comm_ring.MulIn.Read(ring),
						comm_ring.ZeroIn.Read(ring)))
				extendedOff := b.Have(
					"and vanish off T",
					"∀x:A. x ∈ E ∧ x ∉ T ⇒ COND(x ∈ T, t(x), L.zero) * x = L.zero",
					By(inField, set_basic.SubsetDef, comm_ring.MulLeftZeroOn.Read(ring)))
				reindexed := b.Have(
					"over the enumeration the extended sum is the sum over E",
					"module_sum(L.add, "+
						"    L.zero, "+
						"    {k:num | k < card(E)}, "+
						"    λk:num. COND(e(k) ∈ T, t(e(k)), L.zero) * e(k)) = "+
						"module_sum(L.add, L.zero, E, λx:A. COND(x ∈ T, t(x), L.zero) * x)",
					By(
						extendedIn,
						image,
						counted,
						enumeration,
						module.ModuleSumImage.Read(regular).At(indices, e, extended)))
				restricted := b.Have(
					"which is the sum over T",
					"module_sum(L.add, L.zero, E, λx:A. COND(x ∈ T, t(x), L.zero) * x) = "+
						"module_sum(L.add, L.zero, T, λx:A. COND(x ∈ T, t(x), L.zero) * x)",
					By(
						finiteE,
						extendedIn,
						extendedOff,
						parts[1],
						module.ModuleSumSupport.Read(regular).At(E, T, extended)))
				b.Take(b.TermAs[Fun[Nat, A]]("λk:num. COND(e(k) ∈ T, t(e(k)), L.zero)"))
				scalarsIn := b.Have(
					"the coefficients lie in S",
					"∀k:num. COND(e(k) ∈ T, t(e(k)), L.zero) ∈ S",
					By(subS, parts[2], comm_ring.SubringZero.At(c, S)))
				b.Show(
					"and on T the extended terms are v's",
					By(
						scalarsIn,
						parts[3],
						reindexed,
						restricted,
						module.ModuleSumCongruence.At(
							b.TermAs[Op[A]]("L.add"),
							b.TermAs[A]("L.zero"),
							T,
							extended,
							b.TermAs[Fun[A, A]]("λx:A. t(x) * x"))))
			}))
		rows := a.Have(
			"each z·e(i) lies in N, so it is an S-combination of the e(k)",
			Statement{
				Binders:    "∀i:num.",
				Hypotheses: []string{"i < card(E)"},
				Conclusion: "∃c:(num → A). " +
					"    (∀k:num. c(k) ∈ S) ∧ " +
					"    z * e(i) = module_sum(L.add, L.zero, {k:num | k < card(E)}, λk:num. c(k) * e(k))",
			},
			Derive(func(b *Argument) {
				b.FixAs[Nat]("i")
				iBelow := b.Assume()
				product := b.Have(
					"e(i) lies in E, so in its span N, and z keeps N",
					"z * e(i) ∈ N",
					BySets(stable, iBelow, enumeration, spans, submodule.SubsetSpan.At(scalars, vectors, E)))
				b.Show(
					"expand it",
					By(product, combinations.At(b.TermAs[A]("z * e(i)"))))
			}))
		_, matrixRows := a.ObtainAs[Fun2[Nat, Nat, A]](
			"choose the coefficients row by row",
			"∃P:(num → num → A). ∀i:num. "+
				"    i < card(E) ⇒ "+
				"    (∀k:num. P(i, k) ∈ S) ∧ "+
				"    z * e(i) = module_sum(L.add, L.zero, {k:num | k < card(E)}, λk:num. P(i, k) * e(k))",
			By(rows),
			Named("P"))
		j, generator := a.ObtainAs[Nat](
			"some e(j) is not zero, for N holds one",
			"∃j:num. j < card(E) ∧ e(j) ≠ L.zero",
			Derive(func(b *Argument) {
				none := b.SupposeNot()
				collapsed := b.Have(
					"otherwise E would be {0}",
					"E ⊆ {L.zero}",
					BySets(none, image))
				trivial := b.Have(
					"and so would N, the span",
					"N ⊆ {L.zero}",
					By(
						Normalized,
						spans,
						collapsed,
						submodule.ZeroSubmodule.Read(space),
						submodule.SpanLeast.At(scalars, vectors, E, a.TermAs[Set[A]]("{L.zero}"))))
				b.Show(
					"but N has a nonzero member",
					BySets(trivial, nonzero))
			}),
			Named("j"))
		ringS := a.Have(
			"S is a ring under L's operations",
			"comm_ring_on(«R»)",
			By(subS, comm_ring.SubringRingOn.Read(ring).At(S)))
		padded := a.TermAs[Fun2[Nat, Nat, A]](
			"λi:num. λk:num. COND(i < card(E) ∧ k < card(E), P(i, k), L.zero)")
		paddedOver := a.Have(
			"cut off past the block, P is a matrix over S",
			"matrix_over(«R», card(E), λi:num. λk:num. COND(i < card(E) ∧ k < card(E), P(i, k), L.zero))",
			Simp(Fwd(determinant.MatrixOverEntries.Read(ringS))),
			By(matrixRows, subS, comm_ring.SubringZero.At(c, S), nat_order.NotLessThan))
		eigen := a.Have(
			"and z·e is still P·e",
			Statement{
				Binders:    "∀i:num.",
				Hypotheses: []string{"i < card(E)"},
				Conclusion: "z * e(i) = " +
					"module_sum(L.add, " +
					"    L.zero, " +
					"    {k:num | k < card(E)}, " +
					"    λk:num. COND(i < card(E) ∧ k < card(E), P(i, k), L.zero) * e(k))",
			},
			Derive(func(b *Argument) {
				i := b.FixAs[Nat]("i")
				iBelow := b.Assume()
				b.Show(
					"inside the block the cut-off matrix is P",
					By(
						matrixRows.At(i),
						iBelow,
						module.ModuleSumCongruence.At(
							b.TermAs[Op[A]]("L.add"),
							b.TermAs[A]("L.zero"),
							b.TermAs[Set[Nat]]("{k:num | k < card(E)}"),
							b.TermAs[Fun[Nat, A]]("λk:num. COND(i < card(E) ∧ k < card(E), P(i, k), L.zero) * e(k)"),
							b.TermAs[Fun[Nat, A]]("λk:num. P(i, k) * e(k)"))))
			}))
		coordinates := a.Have(
			"the e(i) lie in L",
			"∀i:num. i < card(E) ⇒ e(i) ∈ L.carrier",
			BySets(inField, enumeration))
		zm := a.MemberOf[on.L](z, zIn)
		a.Show(
			"z is an eigenvalue of a matrix over S with a nonzero eigenvector",
			By(
				subS,
				eigen,
				generator,
				coordinates,
				paddedOver,
				EigenvalueIntegral.Read(L).At(S, size, padded, zm, e, j)))
	}),
})}
