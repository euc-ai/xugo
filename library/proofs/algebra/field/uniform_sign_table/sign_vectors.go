// sign_vectors.go — the uniform sign tables over the parameter ring read at a
// list of integer polynomials: one rule of parameter signs gives its ordered
// tables and its realizable sign vectors in every real closed field.

package uniform_sign_table

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/ordered_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/parametric_sign_table"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/polynomial_sign_table"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/real_closed_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_formula"
	"github.com/euc-ai/xugo/library/proofs/datatypes/first_order"
	"github.com/euc-ai/xugo/library/proofs/datatypes/list"
	"github.com/euc-ai/xugo/library/registry"
)

// ParameterizedSignTable — one parameter-polynomial sign rule determines
// ordered tables in every real closed field on the host. Each member of P is
// a polynomial in v whose coefficients are parameter polynomials in U ∖ {v}
// (polynomial_formula.CoefficientsOverParameters), so ParameterRingSignTable
// at the trivial condition gives the coefficient family a uniform table. In a
// model its cuts serve P, since a member evaluated at ρ updated at v by x is
// its coefficient family specialized at ρ and evaluated at x
// (polynomial_formula.CoefficientEvaluation); the rows, read as lists in the
// order of P, are the sign vectors of P on the cells.
var ParameterizedSignTable = parameterizedSignTableThm{family.Add(registry.ProofEntry{
	Name: "ParameterizedSignTable",
	Key:  "prop_c056e1c570b86a4",
	Reading: "E, N and T are chosen before every model and environment; only the cut locations " +
		"are model-dependent. Redundant cuts are allowed; a cut count N(polynomial_signs(F, lt, ρ, " +
		"E)) of 0 leaves one cell, the whole carrier, which serves the empty list.",
	Build: family.Theorem(Statement{
		Binders: "∀U:set(num). ∀v:num. ∀P:list((num → num) → int).",
		Hypotheses: []string{
			"polynomial_list_over(U ∪ {v}, P)",
		},
		Conclusion: "∃E:list((num → num) → int). ∃N:(list(int) → num). ∃T:(list(int) → num → list(int)). " +
			"    polynomial_list_over(U, E) ∧ " +
			"    (∀F:field_ops(A). ∀lt:(A → A → bool). ∀ρ:(num → A). " +
			"        real_closed_field(F, lt) ∧ fo_env_ok(F.carrier, U, ρ) ⇒ " +
			"        ∃r:(num → A). " +
			"            polynomial_sign_table(F, lt, ρ, v, P, N(polynomial_signs(F, lt, ρ, E)), r) ∧ " +
			"            (∀j:num. ∀x:A. " +
			"                j ≤ 2 * N(polynomial_signs(F, lt, ρ, E)) ∧ " +
			"                x ∈ polynomial_sign_cell(F, lt, N(polynomial_signs(F, lt, ρ, E)), r, j) ⇒ " +
			"                polynomial_signs(F, lt, fo_update(ρ, v, x), P) = " +
			"                T(polynomial_signs(F, lt, ρ, E), j)))",
	}, func(
		a *Argument,
		U *Expr[Set[Nat]],
		v *Expr[Nat],
		P *Expr[List[IntegerPolynomial]],
		listed Fact,
	) {
		members := a.Have(
			"each member of P is an integer polynomial in the variables U and v",
			Statement{
				Binders: "∀i:num.",
				Hypotheses: []string{
					"i < list_length(P)",
				},
				Conclusion: "integer_polynomial(list_nth(P, i)) ∧ " +
					"integer_polynomial_vars(list_nth(P, i)) ⊆ U ∪ {v}",
			},
			Derive(func(b *Argument) {
				b.FixAs[Nat]("i")
				below := b.Assume()
				b.Show(
					"a member of a list of polynomials over U ∪ {v}",
					By(below, listed, polynomial_formula.PolynomialListOverDef, list.MemberNth))
			}))
		coefficients := a.Have(
			"read as polynomials in v, the members have parameter polynomials in U ∖ {v} as coefficients",
			Statement{
				Binders: "∀i:num.",
				Hypotheses: []string{
					"i < list_length(P)",
				},
				Conclusion: "polynomial_over(integer_polynomial_ring.zero, " +
					"    polynomial_algebra(int_ring, U ∖ {v}), " +
					"    λn:num. integer_polynomial_coefficient(v, list_nth(P, i), n))",
			},
			Derive(func(b *Argument) {
				i := b.FixAs[Nat]("i")
				below := b.Assume()
				member := b.Conjuncts(
					GroupPremises(below, members.At(i)),
					"the member is an integer polynomial",
					"in the variables U and v")
				p := b.TermAs[IntegerPolynomial]("list_nth(P, i)")
				variables := b.Have(
					"the member's variables other than v lie in U ∖ {v}",
					"integer_polynomial_vars(list_nth(P, i)) ∖ {v} ⊆ U ∖ {v}",
					BySets(member[1]))
				b.Show(
					"its coefficients in v are polynomials in its other variables, so in U ∖ {v}",
					By(
						GroupPremises(
							variables,
							polynomial_algebra.PolynomialAlgebraSubset.At(
								b.TermAs[module_record.RingOps[Int]]("int_ring"),
								b.TermAs[Set[Nat]]("integer_polynomial_vars(list_nth(P, i)) ∖ {v}"),
								b.TermAs[Set[Nat]]("U ∖ {v}"))),
						GroupPremises(member[0], polynomial_formula.CoefficientsOverParameters.At(v, p)),
						polynomial.PolynomialOverMono))
			}))
		table := a.Have(
			"so the coefficient family has a uniform table over the parameters U ∖ {v}, under no condition",
			"parametric_sign_table(U ∖ {v}, "+
				"    λF:field_ops(A). λlt:(A → A → bool). λρ:(num → A). ⊤, "+
				"    list_length(P), "+
				"    λi:num. λn:num. integer_polynomial_coefficient(v, list_nth(P, i), n))",
			By(coefficients, ParameterRingSignTable))
		E, N, _, rule := a.Unpack3As[List[IntegerPolynomial], Fun[List[Int], Nat], Fun3[List[Int], Nat, Nat, Int]](
			a.Unfolded(table, parametric_sign_table.ParametricSignTableDef),
			"E",
			"N",
			"T")
		given := a.Conjuncts(
			rule,
			"E lists parameter polynomials in U ∖ {v}",
			"in every real closed field and environment, the signs s of E "+
				"give the coefficient family a table with N(s) cuts and rows T(s)")
		perRow := a.Have(
			"each row T(s, j) is read as a list in the order of P",
			"∀s:list(int). ∀j:num. ∃l:list(int). "+
				"    list_length(l) = list_length(P) ∧ (∀i:num. i < list_length(P) ⇒ list_nth(l, i) = T(s, j, i))",
			Derive(func(b *Argument) {
				b.FixAs[List[Int]]("s")
				b.FixAs[Nat]("j")
				b.Show(
					"tabulate the entries T(s, j, i), i < list_length(P)",
					By(list.TabulatedList.At(
						b.TermAs[Fun[Nat, Int]]("λi:num. T(s, j, i)"), b.TermAs[Nat]("list_length(P)"))))
			}))
		R, rows := a.ObtainAs[Fun2[List[Int], Nat, List[Int]]](
			"choose those lists R(s, j)",
			"∃R:(list(int) → num → list(int)). ∀s:list(int). ∀j:num. "+
				"    list_length(R(s, j)) = list_length(P) ∧ "+
				"    (∀i:num. i < list_length(P) ⇒ list_nth(R(s, j), i) = T(s, j, i))",
			By(perRow))
		a.Take(E)
		a.Take(N)
		a.Take(R)
		a.Show(
			"E lists parameter polynomials in U, and in every model "+
				"the coefficient family's cuts give P its table with rows R",
			SplitConjAll(
				Case(
					"E lists parameter polynomials in U ∖ {v}, so in U",
					BySets(given[0], polynomial_formula.PolynomialListOverDef)),
				Case(
					"in every model the coefficient family's cuts give P its table, with rows R",
					Derive(func(b *Argument) {
						F := b.FixAs[FieldOps[A]]("F")
						lt := b.FixAs[Fun2[A, A, Bool]]("lt")
						ρ := b.FixAs[Fun[Nat, A]]("ρ")
						model := b.Conjuncts(
							b.Assume(),
							"F with lt is a real closed field",
							"ρ gives carrier points to U")
						ordered := real_closed_field.OrderedFieldOn.Read(model[0])
						fieldOn := ordered_field.FieldOn.Read(ordered)
						smaller := b.Have(
							"ρ gives carrier points to U ∖ {v}",
							"fo_env_ok(F.carrier, U ∖ {v}, ρ)",
							BySets(model[1], first_order.EnvOKDef))
						r, familyTable := b.UnpackAs[Fun[Nat, A]](
							b.Have(
								"so the coefficient family has its table in this model",
								"∃r:(num → A). "+
									"    polynomial_family_sign_table(F, "+
									"        lt, "+
									"        list_length(P), "+
									"        λi:num. λn:num. "+
									"            integer_polynomial_eval(field_ring(F), "+
									"                ρ, "+
									"                integer_polynomial_coefficient(v, list_nth(P, i), n)), "+
									"        N(polynomial_signs(F, lt, ρ, E)), "+
									"        r, "+
									"        T(polynomial_signs(F, lt, ρ, E)))",
								By(model[0], smaller, given[1].At(F, lt, ρ))),
							"r")
						tableParts := b.Conjuncts(
							b.Unfolded(familyTable, polynomial_sign_table.PolynomialFamilySignTableDef),
							"the cuts increase in the carrier",
							"every cell is nonempty",
							"the coefficient family's i-th member has sign T(s, j, i) on cell j")
						values := b.Have(
							"a member of P at ρ updated at v by x is its "+
								"coefficient family specialized at ρ and evaluated at x",
							Statement{
								Binders: "∀i:num. ∀x:A.",
								Hypotheses: []string{
									"i < list_length(P)",
									"x ∈ F.carrier",
								},
								Conclusion: "integer_polynomial_eval(field_ring(F), fo_update(ρ, v, x), list_nth(P, i)) = " +
									"polynomial_eval(F.add, " +
									"    F.zero, " +
									"    F.mul, " +
									"    F.one, " +
									"    λn:num. " +
									"        integer_polynomial_eval(field_ring(F), " +
									"            ρ, " +
									"            integer_polynomial_coefficient(v, list_nth(P, i), n)), " +
									"    x)",
							},
							Derive(func(c *Argument) {
								i := c.FixAs[Nat]("i")
								x := c.FixAs[A]("x")
								indexAndPoint := c.Conjuncts(
									c.Assume(),
									"i indexes a member of P",
									"x lies in F")
								member := c.Conjuncts(
									GroupPremises(indexAndPoint[0], members.At(i)),
									"the member is an integer polynomial",
									"in the variables U and v")
								environment := c.Have(
									"ρ gives carrier points to the variables of the member other than v",
									"fo_env_ok(F.carrier, integer_polynomial_vars(list_nth(P, i)) ∖ {v}, ρ)",
									BySets(model[1], member[1], first_order.EnvOKDef))
								c.Show(
									"by grouping the monomials of the member by their exponent of v",
									By(
										field.RingOn.Read(fieldOn),
										member[0],
										environment,
										indexAndPoint[1],
										polynomial_formula.CoefficientEvaluation.At(
											c.TermAs[module_record.RingOps[A]]("field_ring(F)"),
											ρ,
											c.TermAs[IntegerPolynomial]("list_nth(P, i)"),
											v,
											x)))
							}))
						signRows := b.Have(
							"on cell j the sign vector of P is R(s, j)",
							Statement{
								Binders: "∀j:num. ∀x:A.",
								Hypotheses: []string{
									"j ≤ 2 * N(polynomial_signs(F, lt, ρ, E))",
									"x ∈ polynomial_sign_cell(F, lt, N(polynomial_signs(F, lt, ρ, E)), r, j)",
								},
								Conclusion: "polynomial_signs(F, lt, fo_update(ρ, v, x), P) = R(polynomial_signs(F, lt, ρ, E), j)",
							},
							Derive(func(c *Argument) {
								j := c.FixAs[Nat]("j")
								x := c.FixAs[A]("x")
								cell := c.Conjuncts(
									c.Assume(),
									"j is a cell index",
									"x lies in cell j")
								xIn := c.Have(
									"x lies in the carrier",
									"x ∈ F.carrier",
									By(
										cell[1],
										polynomial_sign_table.SignCellInCarrier.At(
											F, lt, c.TermAs[Nat]("N(polynomial_signs(F, lt, ρ, E))"), r, j, x)))
								s := c.TermAs[List[Int]]("polynomial_signs(F, lt, ρ, E)")
								row := c.Conjuncts(
									rows.At(s, j),
									"R(s, j) has the length of P",
									"its i-th entry is T(s, j, i)")
								entries := c.Have(
									"entry by entry, the sign of the i-th member at x is T(s, j, i)",
									Statement{
										Binders: "∀i:num.",
										Hypotheses: []string{
											"i < list_length(polynomial_signs(F, lt, fo_update(ρ, v, x), P))",
										},
										Conclusion: "list_nth(polynomial_signs(F, lt, fo_update(ρ, v, x), P), i) = " +
											"list_nth(R(polynomial_signs(F, lt, ρ, E), j), i)",
									},
									Derive(func(d *Argument) {
										i := d.FixAs[Nat]("i")
										below := d.Have(
											"i indexes a member of P",
											"i < list_length(P)",
											By(d.Assume(), polynomial_sign_table.SignsDef, list.LengthMap))
										d.Show(
											"the member's value at x is that of the i-th member of the coefficient family",
											By(
												polynomial_sign_table.SignsDef,
												GroupPremises(
													below,
													list.NthMap.At(
														d.TermAs[Fun[IntegerPolynomial, Int]](
															"λp:((num → num) → int). "+
																"    ordered_sign(F, lt, integer_polynomial_eval(field_ring(F), fo_update(ρ, v, x), p))"),
														P,
														i)),
												GroupPremises(below, xIn, values.At(i, x)),
												GroupPremises(cell[0], below, cell[1], tableParts[2].At(j, i, x)),
												GroupPremises(below, row[1].At(i))))
									}))
								c.Show(
									"two lists of one length with the same entries are equal",
									By(GroupPremises(
										c.Have(
											"both have the length of P",
											"list_length(polynomial_signs(F, lt, fo_update(ρ, v, x), P)) = "+
												"list_length(R(polynomial_signs(F, lt, ρ, E), j))",
											By(
												row[0],
												polynomial_sign_table.SignsDef.At(F, lt, c.TermAs[Fun[Nat, A]]("fo_update(ρ, v, x)"), P),
												list.LengthMap.At(
													c.TermAs[Fun[IntegerPolynomial, Int]](
														"λp:((num → num) → int). "+
															"    ordered_sign(F, lt, integer_polynomial_eval(field_ring(F), fo_update(ρ, v, x), p))"),
													P))),
										entries,
										list.NthExtensionality.At(
											c.TermAs[List[Int]]("polynomial_signs(F, lt, fo_update(ρ, v, x), P)"),
											c.TermAs[List[Int]]("R(polynomial_signs(F, lt, ρ, E), j)")))))
							}))
						b.Take(r)
						b.Show(
							"the cuts are the coefficient family's, and the "+
								"sign vector of P is constant, R(s, j), on each cell",
							Simp(Fwd(polynomial_sign_table.SignTableDef)),
							By(tableParts[0], tableParts[1], signRows))
					}))))
	}),
})}

// RealizableSignControl — realizable sign vectors are determined uniformly
// by finitely many parameter signs: B(s) is the set of rows T(s, j),
// j ≤ 2·N(s), of the ParameterizedSignTable rule. In a model every point of
// the carrier lies in some cell (polynomial_sign_table.SignCellsCover),
// where P has the sign vector of the cell's row, and every cell holds a
// point, so every row is realized.
var RealizableSignControl = realizableSignControlThm{family.Add(registry.ProofEntry{
	Name: "RealizableSignControl",
	Key:  "prop_fe4463df6f32db20",
	Reading: "E and B come before the quantifiers over fields and environments, " +
		"so one rule serves every model on the host type. The equality says which " +
		"sign vectors occur and which do not. P may be empty or specialize to zero.",
	Build: family.Theorem(Statement{
		Binders: "∀U:set(num). ∀v:num. ∀P:list((num → num) → int).",
		Hypotheses: []string{
			"polynomial_list_over(U ∪ {v}, P)",
		},
		Conclusion: "∃E:list((num → num) → int). ∃B:(list(int) → set(list(int))). " +
			"    polynomial_list_over(U, E) ∧ " +
			"    (∀F:field_ops(A). ∀lt:(A → A → bool). ∀ρ:(num → A). " +
			"        real_closed_field(F, lt) ∧ fo_env_ok(F.carrier, U, ρ) ⇒ " +
			"        realizable_polynomial_signs(F, lt, ρ, v, P) = B(polynomial_signs(F, lt, ρ, E)))",
	}, func(
		a *Argument,
		U *Expr[Set[Nat]],
		v *Expr[Nat],
		P *Expr[List[IntegerPolynomial]],
		listed Fact,
	) {
		E, _, _, rule := a.Unpack3As[List[IntegerPolynomial], Fun[List[Int], Nat], Fun2[List[Int], Nat, List[Int]]](
			GroupPremises(listed, ParameterizedSignTable.Inst[A]().At(U, v, P)),
			"E",
			"N",
			"T")
		given := a.Conjuncts(
			rule,
			"E lists parameter polynomials in U",
			"in every model, the signs s of E give P a table with N(s) cuts whose rows are T(s)")
		a.Take(E)
		a.Take(a.TermAs[Fun[List[Int], Set[List[Int]]]](
			"λs:list(int). {T(s, j):list(int) | j:num | j ≤ 2 * N(s)}"))
		a.Show(
			"E lists parameter polynomials in U, and in every model "+
				"the realizable sign vectors are the rows of the table",
			SplitConjAll(
				Case(
					"E lists parameter polynomials in U",
					By(given[0])),
				Case(
					"in every model the realizable sign vectors are the rows T(s, j), j ≤ 2·N(s)",
					Derive(func(b *Argument) {
						F := b.FixAs[FieldOps[A]]("F")
						lt := b.FixAs[Fun2[A, A, Bool]]("lt")
						ρ := b.FixAs[Fun[Nat, A]]("ρ")
						model := b.Assume()
						r, tableFacts := b.UnpackAs[Fun[Nat, A]](
							GroupPremises(model, given[1].At(F, lt, ρ)),
							"r")
						parts := b.Conjuncts(
							tableFacts,
							"the cuts r give P a sign table",
							"on cell j the sign vector of P is T(s, j)")
						table := b.Conjuncts(
							b.Unfolded(parts[0], polynomial_sign_table.SignTableDef),
							"the cuts increase in the carrier",
							"every cell is nonempty",
							"the sign vector of P is constant on each cell")
						closed := b.Conjuncts(
							model,
							"F with lt is a real closed field",
							"ρ gives carrier points to U")[0]
						ordered := real_closed_field.OrderedFieldOn.Read(closed)
						count := b.TermAs[Nat]("N(polynomial_signs(F, lt, ρ, E))")
						covered := b.Have(
							"each point of the carrier lies in a cell, where P has the sign vector of the cell's row",
							Statement{
								Binders: "∀x:A.",
								Hypotheses: []string{
									"x ∈ F.carrier",
								},
								Conclusion: "∃j:num. " +
									"    j ≤ 2 * N(polynomial_signs(F, lt, ρ, E)) ∧ " +
									"    polynomial_signs(F, lt, fo_update(ρ, v, x), P) = T(polynomial_signs(F, lt, ρ, E), j)",
							},
							Derive(func(c *Argument) {
								x := c.FixAs[A]("x")
								xIn := c.Assume()
								j, inCell := c.UnpackAs[Nat](
									GroupPremises(ordered, table[0], xIn, polynomial_sign_table.SignCellsCover.At(F, lt, count, r, x)),
									"j")
								cell := c.Conjuncts(
									inCell,
									"j is a cell index",
									"x lies in cell j")
								c.Take(j)
								c.Show(
									"the row of cell j",
									By(cell[0], GroupPremises(cell[0], cell[1], parts[1].At(j, x))))
							}))
						realized := b.Have(
							"each row is the sign vector of P at a point of its cell",
							Statement{
								Binders: "∀j:num.",
								Hypotheses: []string{
									"j ≤ 2 * N(polynomial_signs(F, lt, ρ, E))",
								},
								Conclusion: "∃x:A. " +
									"    x ∈ F.carrier ∧ " +
									"    polynomial_signs(F, lt, fo_update(ρ, v, x), P) = T(polynomial_signs(F, lt, ρ, E), j)",
							},
							Derive(func(c *Argument) {
								j := c.FixAs[Nat]("j")
								index := c.Assume()
								x, inCell := c.ObtainAs[A](
									"cell j holds a point",
									"∃x:A. x ∈ polynomial_sign_cell(F, lt, N(polynomial_signs(F, lt, ρ, E)), r, j)",
									BySets(GroupPremises(index, table[1].At(j))))
								xIn := c.Have(
									"x lies in the carrier",
									"x ∈ F.carrier",
									By(inCell, polynomial_sign_table.SignCellInCarrier.At(F, lt, count, r, j, x)))
								c.Take(x)
								c.Show(
									"a point of the carrier where P has the sign vector of the row",
									By(xIn, GroupPremises(index, inCell, parts[1].At(j, x))))
							}))
						b.Show(
							"a sign vector is realized exactly when it is a row",
							BySets(polynomial_sign_table.RealizableSignsDef.At(F, lt, ρ, v, P), covered, realized))
					}))))
	}),
})}
