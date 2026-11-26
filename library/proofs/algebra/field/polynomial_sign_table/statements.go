package polynomial_sign_table

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/ordered_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/real_closed_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_formula"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_roots"
	"github.com/euc-ai/xugo/library/proofs/datatypes/first_order"
	"github.com/euc-ai/xugo/library/proofs/datatypes/list"
	_ "github.com/euc-ai/xugo/library/proofs/int_num/int_construction"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_parity"
	_ "github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/listing"
	_ "github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// SignsDef — Evaluate the polynomials and retain their signs in list order.
var SignsDef = signsDefThm{family.Define(registry.DefEntry{
	Name:  "SignsDef",
	Const: "polynomial_signs",
	Type:  "field_ops(A) → (A → A → bool) → (num → A) → list((num → num) → int) → list(int)",
	Key:   "prop_a3066cb1fe869f45",
	Equations: []string{
		"∀F:field_ops(A). ∀lt:(A → A → bool). ∀ρ:(num → A). ∀P:list((num → num) → int). " +
			"    polynomial_signs(F, lt, ρ, P) = " +
			"    list_map(λp:((num → num) → int). " +
			"            ordered_sign(F, lt, integer_polynomial_eval(field_ring(F), ρ, p)), " +
			"        P)",
	},
})}

// RealizableSignsDef — All sign vectors obtained by varying the eliminated variable over the carrier.
var RealizableSignsDef = realizableSignsDefThm{family.Define(registry.DefEntry{
	Name:  "RealizableSignsDef",
	Const: "realizable_polynomial_signs",
	Type: "field_ops(A) → " +
		"(A → A → bool) → " +
		"(num → A) → " +
		"num → " +
		"list((num → num) → int) → " +
		"set(list(int))",
	Key: "prop_ba8d5d0be46d4ba6",
	Equations: []string{
		"∀F:field_ops(A). ∀lt:(A → A → bool). ∀ρ:(num → A). ∀v:num. ∀P:list((num → num) → int). " +
			"    realizable_polynomial_signs(F, lt, ρ, v, P) = " +
			"    {polynomial_signs(F, lt, fo_update(ρ, v, x), P) | x:A | x ∈ F.carrier}",
	},
	Deps: []registry.EntryLike{SignsDef},
})}

// SignCellDef — Odd cells are the successive cuts and even cells the open intervals between them, including the two rays.
var SignCellDef = signCellDefThm{family.Define(registry.DefEntry{
	Name:  "SignCellDef",
	Const: "polynomial_sign_cell",
	Type:  "field_ops(A) → (A → A → bool) → num → (num → A) → num → set(A)",
	Key:   "prop_b858b1b4d420720f",
	Equations: []string{
		"∀F:field_ops(A). ∀lt:(A → A → bool). ∀k:num. ∀r:(num → A). ∀j:num. " +
			"    polynomial_sign_cell(F, lt, k, r, j) = " +
			"    {x:A | " +
			"        x ∈ F.carrier ∧ " +
			"        ((∃i:num. i < k ∧ j = 2 * i + 1 ∧ x = r(i)) ∨ " +
			"            (∃i:num. i ≤ k ∧ j = 2 * i ∧ (i = 0 ∨ lt(r(i - 1), x)) ∧ (i = k ∨ lt(x, r(i)))))}",
	},
})}

// SignTableDef — A finite ordered partition into nonempty cells on each of which the entire sign vector is constant.
var SignTableDef = signTableDefThm{family.Define(registry.DefEntry{
	Name:  "SignTableDef",
	Const: "polynomial_sign_table",
	Type: "field_ops(A) → " +
		"(A → A → bool) → " +
		"(num → A) → " +
		"num → " +
		"list((num → num) → int) → " +
		"num → " +
		"(num → A) → " +
		"bool",
	Key: "prop_430c3d6058a8128",
	Equations: []string{
		"∀F:field_ops(A). " +
			"∀lt:(A → A → bool). " +
			"∀ρ:(num → A). " +
			"∀v:num. " +
			"∀P:list((num → num) → int). " +
			"∀k:num. " +
			"∀r:(num → A). " +
			"    polynomial_sign_table(F, lt, ρ, v, P, k, r) ⇔ " +
			"    increasing_cuts(F, lt, k, r) ∧ " +
			"    (∀j:num. j ≤ 2 * k ⇒ polynomial_sign_cell(F, lt, k, r, j) ≠ ∅) ∧ " +
			"    (∀j:num. ∀x y:A. " +
			"        j ≤ 2 * k ∧ " +
			"        x ∈ polynomial_sign_cell(F, lt, k, r, j) ∧ " +
			"        y ∈ polynomial_sign_cell(F, lt, k, r, j) ⇒ " +
			"        polynomial_signs(F, lt, fo_update(ρ, v, x), P) = " +
			"        polynomial_signs(F, lt, fo_update(ρ, v, y), P))",
	},
	Deps: []registry.EntryLike{SignCellDef, SignsDef},
})}

// SignTableExists — every specialized polynomial list has a finite ordered
// sign table: the roots of the nonzero univariate specializations lie in a
// finite subset Z of the carrier, and the increasing enumeration of Z gives
// the cuts. Every cell of increasing cuts holds a point, and a cut cell is a
// single point; no cut lies inside an open cell, so a nonzero specialization
// has no root there and keeps one sign on it.
var SignTableExists = signTableExistsThm{family.Add(registry.ProofEntry{
	Name: "SignTableExists",
	Key:  "prop_fe6004b6fdc23755",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). " +
			"∀lt:(A → A → bool). " +
			"∀U:set(num). " +
			"∀ρ:(num → A). " +
			"∀v:num. " +
			"∀P:list((num → num) → int).",
		Hypotheses: []string{
			"real_closed_field(F, lt)",
			"polynomial_list_over(U ∪ {v}, P)",
			"fo_env_ok(F.carrier, U, ρ)",
		},
		Conclusion: "∃k:num. ∃r:(num → A). polynomial_sign_table(F, lt, ρ, v, P, k, r)",
		Abbrev: Abbrev{
			{Name: "nonzeroMembers", Text: "{p:((num → num) → int) | p ∈ set_of_list(P) ∧ Q(p) ≠ vec_zero}"},
		},
	}, func(
		a *Argument,
		F *Expr[FieldOps[A]],
		lt *Arrow2[A, A, Bool],
		U *Expr[Set[Nat]],
		ρ *Arrow[Nat, A],
		v *Expr[Nat],
		P *Expr[List[IntegerPolynomial]],
		rcf, over, env Fact,
	) {
		ordered := real_closed_field.OrderedFieldOn.Read(rcf)
		fieldF := ordered_field.FieldOn.Read(ordered)
		irreflexive := ordered_field.Irreflexive.Read(ordered).AsFact()
		transitive := ordered_field.Transitive.Read(ordered).AsFact()
		ring := field.RingOn.Read(fieldF)
		members := a.Unfolded(over, polynomial_formula.PolynomialListOverDef)

		specializes := a.Have(
			"each member of P specializes along v to a polynomial over the carrier",
			Statement{
				Binders: "∀p:((num → num) → int).",
				Hypotheses: []string{
					"list_member(p, P)",
				},
				Conclusion: "∃q:(num → A). " +
					"    polynomial_over(F.carrier, q) ∧ " +
					"    (∀x:A. " +
					"        x ∈ F.carrier ⇒ " +
					"        integer_polynomial_eval(field_ring(F), fo_update(ρ, v, x), p) = polynomial_eval(q, x))",
			},
			Derive(func(b *Argument) {
				p := b.FixAs[IntegerPolynomial]("p")
				member := b.Assume()
				parts := b.Conjuncts(
					GroupPremises(member, members.At(p)),
					"p is an integer polynomial",
					"the variables of p lie among U and v")
				others := b.Have(
					"ρ gives carrier points to the variables of p other than v",
					"fo_env_ok(F.carrier, integer_polynomial_vars(p) ∖ {v}, ρ)",
					BySets(parts[1], env, first_order.EnvOKDef))
				b.Show(
					"fixing those variables at ρ leaves a polynomial in v",
					By(parts[0], others, polynomial_formula.SpecializeOneVariable.Read(ring).At(ρ, p, v)))
			}))
		_, specialized := a.ObtainAs[Fun[IntegerPolynomial, Fun[Nat, A]]](
			"choose a specialization Q(p) for every member p",
			"∃Q:(((num → num) → int) → num → A). ∀p:((num → num) → int). "+
				"    list_member(p, P) ⇒ "+
				"    polynomial_over(F.carrier, Q(p)) ∧ "+
				"    (∀x:A. "+
				"        x ∈ F.carrier ⇒ "+
				"        integer_polynomial_eval(field_ring(F), fo_update(ρ, v, x), p) = polynomial_eval(Q(p), x))",
			By(specializes))

		// The roots of the nonzero specializations: a finite subset of the carrier.
		Z, zDef := a.LetAs[Set[A]](
			"Z", "⋃(image(λp:((num → num) → int). polynomial_roots(F.carrier, Q(p)), «nonzeroMembers»))")
		fewMembers := a.Have(
			"finitely many members of P specialize to nonzero polynomials",
			"finite(«nonzeroMembers»)",
			By(finite_set.FiniteRestrict, listing.FiniteSetOfList))
		fewRoots := a.Have(
			"a nonzero specialization has finitely many roots",
			Statement{
				Binders: "∀p:((num → num) → int).",
				Hypotheses: []string{
					"p ∈ set_of_list(P)",
					"Q(p) ≠ vec_zero",
				},
				Conclusion: "finite(polynomial_roots(F.carrier, Q(p)))",
			},
			Derive(func(b *Argument) {
				p := b.FixAs[IntegerPolynomial]("p")
				given := b.Assume()
				b.Show(
					"the field is an integral domain, where a nonzero polynomial has finitely many roots",
					By(
						specialized.At(p),
						given,
						listing.InSetOfList,
						polynomial_roots.RootBound.Read(integral_domain.FieldIntegralDomain.Read(fieldF)).At(
							b.TermAs[Fun[Nat, A]]("Q(p)"))))
			}))
		rootSets := a.Have(
			"each of those finitely many root sets is finite",
			Statement{
				Binders: "∀t:set(A).",
				Hypotheses: []string{
					"t ∈ image(λp:((num → num) → int). polynomial_roots(F.carrier, Q(p)), «nonzeroMembers»)",
				},
				Conclusion: "finite(t)",
			},
			BySets(fewRoots))
		finiteZ := a.Have(
			"Z is finite",
			"finite(Z)",
			zDef.Rw(),
			By(fewMembers, rootSets, finite_set.FiniteUnions, finite_set.FiniteImage))
		zSubset := a.Have(
			"Z lies in the carrier",
			"Z ⊆ F.carrier",
			zDef.Rw(),
			BySets(polynomial_roots.PolynomialRootsDef))
		rootsInZ := a.Have(
			"every root of a nonzero specialization lies in Z",
			Statement{
				Binders: "∀p:((num → num) → int). ∀x:A.",
				Hypotheses: []string{
					"list_member(p, P)",
					"Q(p) ≠ vec_zero",
					"x ∈ F.carrier",
					"polynomial_eval(Q(p), x) = F.zero",
				},
				Conclusion: "x ∈ Z",
			},
			zDef.Rw(),
			BySets(polynomial_roots.PolynomialRootsDef, listing.InSetOfList))

		// The cuts: Z listed in increasing order.
		k, r, enumeration := a.Unpack2As[Nat, Fun[Nat, A]](
			GroupPremises(finiteZ, zSubset, ordered_field.IncreasingEnumeration.Read(ordered).At(Z)), "k", "r")
		listed := a.Conjuncts(
			enumeration,
			"every r(i) lies in Z",
			"r increases",
			"every point of Z is some r(i)")
		inZ, increasing, covers := listed[0], listed[1], listed[2]
		a.Take(k)
		a.Take(r)
		cutsIn := a.Have(
			"the cuts lie in the carrier",
			"∀i:num. i < k ⇒ r(i) ∈ F.carrier",
			BySets(inZ, zSubset))
		cuts := a.Have(
			"so the cuts increase in the carrier",
			"increasing_cuts(F, lt, k, r)",
			By(cutsIn, increasing, ordered_field.IncreasingCutsDef))

		nonempty := a.Have(
			"every cell of the increasing cuts holds a point",
			"∀j:num. j ≤ 2 * k ⇒ polynomial_sign_cell(F, lt, k, r, j) ≠ ∅",
			a.ForEach(func(j *Expr[Nat]) Action {
				return By(SignCellsNonempty.At(F, lt, k, r, j), ordered, cuts)
			}))

		// Every cell has one sign vector.
		reflect := a.Have(
			"the increasing cuts reflect their order to their indices",
			"∀i j:num. i < k ∧ j < k ∧ lt(r(i), r(j)) ⇒ i < j",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("i")
				b.FixAs[Nat]("j")
				given := b.Assume()
				distinct := b.Have(
					"irreflexivity separates the indices",
					"i ≠ j",
					By(given, irreflexive, cutsIn))
				notAfter := b.Have(
					"j before i would put r(j) below r(i) as well",
					"¬(j < i)",
					By(given, transitive, irreflexive, increasing, cutsIn))
				b.Show(
					"so i comes first",
					ByArith(distinct, notAfter))
			}))
		noCut := a.Have(
			"no cut lies inside an open cell",
			"∀i j:num. i ≤ k ∧ j < k ∧ (i = 0 ∨ lt(r(i - 1), r(j))) ∧ (i = k ∨ lt(r(j), r(i))) ⇒ ⊥",
			Derive(func(b *Argument) {
				i := b.FixAs[Nat]("i")
				j := b.FixAs[Nat]("j")
				given := b.Conjuncts(
					b.Assume(),
					"i is at most k",
					"j is a cut index",
					"r(j) lies above the cell's lower cut",
					"r(j) lies below the cell's upper cut")
				iLe, jLt, above, below := given[0], given[1], given[2], given[3]
				b.Cases(b.TermAs[Bool]("i = 0"))
				b.When(
					"in the first cell r(j) would lie below r(0)",
					func(c *Argument, first Fact) {
						c.Show(
							"reflecting the order puts j below 0",
							ByArith(reflect.At(j, i), jLt, iLe, first, below))
					})
				b.Otherwise(
					"in a later cell j would lie strictly between i − 1 and i",
					func(c *Argument, notFirst Fact) {
						c.Show(
							"reflecting both comparisons leaves no index between i − 1 and i",
							ByArith(reflect.At(c.TermAs[Nat]("i - 1"), j), reflect.At(j, i), notFirst, jLt, iLe, below, above))
					})
			}))
		noRoot := a.Have(
			"a nonzero specialization has no root in an open cell",
			Statement{
				Binders: "∀i:num. ∀p:((num → num) → int). ∀z:A.",
				Hypotheses: []string{
					"i ≤ k",
					"list_member(p, P)",
					"Q(p) ≠ vec_zero",
					"z ∈ polynomial_sign_cell(F, lt, k, r, 2 * i)",
				},
				Conclusion: "polynomial_eval(Q(p), z) ≠ F.zero",
			},
			Derive(func(b *Argument) {
				i := b.FixAs[Nat]("i")
				p := b.FixAs[IntegerPolynomial]("p")
				z := b.FixAs[A]("z")
				given := b.Conjuncts(
					b.Assume(),
					"i is at most k",
					"p is a member",
					"Q(p) is not zero",
					"z lies in the open cell")
				zOpen := b.Have(
					"z lies in the carrier between the cell's cuts",
					"z ∈ F.carrier ∧ (i = 0 ∨ lt(r(i - 1), z)) ∧ (i = k ∨ lt(z, r(i)))",
					By(given[0], given[3], OpenCellMember.At(F, lt, k, r, i, z)))
				root := b.SupposeNot()
				j, zAt := b.ObtainAs[Nat](
					"then z lies in Z, so it is a cut r(j)",
					"∃j:num. j < k ∧ z = r(j)",
					By(rootsInZ.At(p, z), covers.At(z), root, given[1], given[2], zOpen))
				b.Show(
					"and the cut r(j) would lie inside the open cell",
					By(Normalized, noCut.At(i, j), given[0], zOpen, zAt))
			}))
		openSigns := a.Have(
			"two points of one open cell have one sign vector",
			Statement{
				Binders: "∀i:num. ∀x y:A.",
				Hypotheses: []string{
					"i ≤ k",
					"x ∈ polynomial_sign_cell(F, lt, k, r, 2 * i)",
					"y ∈ polynomial_sign_cell(F, lt, k, r, 2 * i)",
				},
				Conclusion: "polynomial_signs(F, lt, fo_update(ρ, v, x), P) = " +
					"polynomial_signs(F, lt, fo_update(ρ, v, y), P)",
			},
			Derive(func(b *Argument) {
				i := b.FixAs[Nat]("i")
				x := b.FixAs[A]("x")
				y := b.FixAs[A]("y")
				given := b.Conjuncts(
					b.Assume(),
					"i is at most k",
					"x lies in the open cell",
					"y lies in the open cell")
				iLe, xCell, yCell := given[0], given[1], given[2]
				points := b.Have(
					"x and y lie in the carrier",
					"x ∈ F.carrier ∧ y ∈ F.carrier",
					By(
						xCell,
						yCell,
						SignCellInCarrier.At(F, lt, k, r, b.TermAs[Nat]("2 * i"), x),
						SignCellInCarrier.At(F, lt, k, r, b.TermAs[Nat]("2 * i"), y)))
				eachSign := b.Have(
					"every member of P takes one sign at x and at y",
					Statement{
						Binders: "∀p:((num → num) → int).",
						Hypotheses: []string{
							"list_member(p, P)",
						},
						Conclusion: "ordered_sign(F, " +
							"    lt, " +
							"    integer_polynomial_eval(field_ring(F), fo_update(ρ, v, x), p)) = " +
							"ordered_sign(F, lt, integer_polynomial_eval(field_ring(F), fo_update(ρ, v, y), p))",
					},
					Derive(func(c *Argument) {
						p := c.FixAs[IntegerPolynomial]("p")
						member := c.Assume()
						spec := c.Conjuncts(
							GroupPremises(member, specialized.At(p)),
							"Q(p) is a polynomial over the carrier",
							"Q(p) computes p along v")
						overQ, along := spec[0], spec[1]
						c.Cases(c.TermAs[Bool]("Q(p) = vec_zero"))
						c.When(
							"a zero specialization vanishes at x and at y alike",
							func(d *Argument, zero Fact) {
								d.Show(
									"both values are zero",
									By(
										along.At(x),
										along.At(y),
										zero,
										points,
										polynomial_evaluation.EvalVecZero.Read(ring).AsFact().At(x),
										polynomial_evaluation.EvalVecZero.Read(ring).AsFact().At(y)))
							})
						c.Otherwise(
							"a nonzero specialization has no root in the open cell",
							func(d *Argument, nonzero Fact) {
								same := d.Have(
									"so Q(p) has one sign on the cell, at x and at y",
									"ordered_sign(F, lt, polynomial_eval(Q(p), x)) = ordered_sign(F, lt, polynomial_eval(Q(p), y))",
									By(
										RootFreeCellSign.At(F, lt, k, r, i, d.TermAs[Fun[Nat, A]]("Q(p)"), x, y),
										rcf,
										cutsIn,
										iLe,
										overQ,
										noRoot.At(i, p),
										member,
										nonzero,
										xCell,
										yCell))
								d.Show(
									"and so does p along v",
									By(same, along.At(x), along.At(y), points))
							})
					}))
				b.Show(
					"the sign vectors agree entry by entry",
					By(
						eachSign,
						SignsDef,
						list.MapCongruence.At(
							b.TermAs[Fun[IntegerPolynomial, Int]](
								"λp:((num → num) → int). "+
									"    ordered_sign(F, lt, integer_polynomial_eval(field_ring(F), fo_update(ρ, v, x), p))"),
							b.TermAs[Fun[IntegerPolynomial, Int]](
								"λp:((num → num) → int). "+
									"    ordered_sign(F, lt, integer_polynomial_eval(field_ring(F), fo_update(ρ, v, y), p))"),
							P)))
			}))
		constant := a.Have(
			"two points of one cell have one sign vector",
			Statement{
				Binders: "∀j:num. ∀x y:A.",
				Hypotheses: []string{
					"j ≤ 2 * k",
					"x ∈ polynomial_sign_cell(F, lt, k, r, j)",
					"y ∈ polynomial_sign_cell(F, lt, k, r, j)",
				},
				Conclusion: "polynomial_signs(F, lt, fo_update(ρ, v, x), P) = " +
					"polynomial_signs(F, lt, fo_update(ρ, v, y), P)",
			},
			Derive(func(b *Argument) {
				j := b.FixAs[Nat]("j")
				x := b.FixAs[A]("x")
				y := b.FixAs[A]("y")
				given := b.Conjuncts(
					b.Assume(),
					"j is at most 2k",
					"x lies in cell j",
					"y lies in cell j")
				b.Do(GroupPremises(given[0], nat_parity.DoubleOrSucDoubleBelow.At(k, j)).SplitDisj(
					LeftHolds(
						"an even index names an open cell",
						Given(func(c *Argument, even Fact) {
							i, shape := c.UnpackAs[Nat](even, "i")
							c.Show(
								"the open cell keeps the sign vector",
								By(openSigns.At(i, x, y), shape, given[1], given[2]))
						})),
					RightHolds(
						"an odd index names a cut",
						Given(func(c *Argument, odd Fact) {
							i, index := c.UnpackAs[Nat](odd, "i")
							equal := c.Have(
								"x and y are both the cut r(i)",
								"x = y",
								By(
									index,
									given[1],
									given[2],
									CutCellMember.At(F, lt, k, r, i, x),
									CutCellMember.At(F, lt, k, r, i, y)))
							c.Show(
								"one point has one sign vector",
								By(Normalized, equal))
						}))))
			}))
		a.Show(
			"the cuts, the nonempty cells and the constant sign vectors: a sign table",
			By(cuts, nonempty, constant, SignTableDef))
	}),
})}

// SignCellsCover — the cells of increasing cuts in an ordered field cover its
// carrier: by induction on the number of cuts, a point below the new last
// cut keeps the cell it had among the earlier cuts, a point on it is the new
// cut cell, and a point above it lies on the new right ray.
var SignCellsCover = signCellsCoverThm{family.Add(registry.ProofEntry{
	Name: "SignCellsCover",
	Key:  "prop_a29d8e7cd67369f7",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). ∀lt:(A → A → bool). ∀k:num. ∀r:(num → A). ∀x:A.",
		Hypotheses: []string{
			"ordered_field_on(F, lt)",
			"increasing_cuts(F, lt, k, r)",
			"x ∈ F.carrier",
		},
		Conclusion: "∃j:num. j ≤ 2 * k ∧ x ∈ polynomial_sign_cell(F, lt, k, r, j)",
	}, func(a *Argument, F *Expr[FieldOps[A]], lt *Arrow2[A, A, Bool]) {
		a.Induct("k")
		a.Base(
			"with no cuts, cell 0 is the whole carrier",
			func(b *Argument) {
				b.FixAs[Fun[Nat, A]]("r")
				b.FixAs[A]("x")
				xIn := b.Conjuncts(
					b.Assume(),
					"F with lt is an ordered field",
					"there are no cuts",
					"x lies in the carrier")[2]
				b.Take(b.TermAs[Nat]("0"))
				b.Show(
					"x lies in the one open cell, of index 2 · 0 = 0",
					Simp(Fwd(SignCellDef)),
					By(
						Normalized,
						xIn,
						nat_arith.MulZero.At(b.TermAs[Nat]("2")),
						nat_order.LessEqRefl.At(b.TermAs[Nat]("0"))))
			})
		a.Step(
			"x lies below the new last cut r(k), on it, or above it",
			func(b *Argument, ih Fact) {
				r := b.FixAs[Fun[Nat, A]]("r")
				x := b.FixAs[A]("x")
				given := b.Conjuncts(
					b.Assume(),
					"F with lt is an ordered field",
					"the k + 1 cuts increase in the carrier",
					"x lies in the carrier")
				ordered, xIn := given[0], given[2]
				bounds := b.Conjuncts(
					b.Unfolded(given[1], ordered_field.IncreasingCutsDef),
					"the k + 1 cuts lie in the carrier",
					"the k + 1 cuts increase")
				cutsIn, increasing := bounds[0], bounds[1]
				comparable := ordered_field.Trichotomy.Read(ordered).AsFact()
				b.Cases(b.TermAs[Bool]("lt(x, r(k))"))
				b.When(
					"below r(k), x keeps the cell it has among the first k cuts",
					func(c *Argument, below Fact) {
						earlier := c.Have(
							"the first k cuts increase in the carrier",
							"increasing_cuts(F, lt, k, r)",
							Unfold(ordered_field.IncreasingCutsDef),
							ByArith(cutsIn, increasing))
						j, placed := c.UnpackAs[Nat](
							GroupPremises(ordered, earlier, xIn, ih.At(r, x)),
							"j")
						jParts := c.Conjuncts(
							placed,
							"j is at most 2k",
							"x lies in cell j of the first k cuts")
						jLe := jParts[0]
						where := c.Have(
							"x is the cut of cell j or lies in its open interval",
							"(∃i:num. i < k ∧ j = 2 * i + 1 ∧ x = r(i)) ∨ "+
								"(∃i:num. i ≤ k ∧ j = 2 * i ∧ (i = 0 ∨ lt(r(i - 1), x)) ∧ (i = k ∨ lt(x, r(i))))",
							By(c.Unfolded(jParts[1], SignCellDef)))
						c.Take(j)
						c.Show(
							"adding r(k) above x leaves x in cell j",
							where.SplitDisj(
								LeftHolds(
									"x is the cut r(i) of cell j, still a cut among k + 1",
									Given(func(d *Argument, cut Fact) {
										_, at := d.UnpackAs[Nat](cut, "i")
										bound := d.Have(
											"i is a cut index of the k + 1 cuts and j is at most 2(k + 1)",
											"i < suc(k) ∧ j ≤ 2 * suc(k)",
											ByArith(at, jLe))
										d.Show(
											"so x is the cut cell j of the k + 1 cuts",
											Simp(Fwd(SignCellDef)),
											By(at, bound, xIn))
									})),
								RightHolds(
									"x lies in the open interval of index i, which r(k) now closes when i = k",
									Given(func(d *Argument, open Fact) {
										_, at := d.UnpackAs[Nat](open, "i")
										bound := d.Have(
											"i is at most k + 1 and j is at most 2(k + 1)",
											"i ≤ suc(k) ∧ j ≤ 2 * suc(k)",
											ByArith(at, jLe))
										d.Show(
											"so x lies in the open cell j of the k + 1 cuts",
											Simp(Fwd(SignCellDef)),
											By(at, bound, below, xIn))
									}))))
					})
				b.Otherwise(
					"not below r(k)",
					func(c *Argument, notBelow Fact) {
						c.Cases(c.TermAs[Bool]("x = r(k)"))
						c.When(
							"on r(k), x is the new cut cell 2k + 1",
							func(d *Argument, on Fact) {
								d.Take(d.TermAs[Nat]("2 * k + 1"))
								bound := d.Have(
									"k is a cut index of the k + 1 cuts and 2k + 1 is at most 2(k + 1)",
									"k < suc(k) ∧ 2 * k + 1 ≤ 2 * suc(k)",
									ByArith())
								d.Show(
									"x is the cut r(k)",
									Simp(Fwd(SignCellDef)),
									By(on, bound, xIn))
							})
						c.Otherwise(
							"above r(k), x lies on the new right ray, cell 2(k + 1)",
							func(d *Argument, off Fact) {
								last := d.Have(
									"the new cut r(k) lies in the carrier",
									"r(k) ∈ F.carrier",
									ByArith(cutsIn))
								above := d.Have(
									"so by trichotomy r(k) lies below x",
									"lt(r(k), x)",
									By(notBelow, off, comparable.At(x, d.TermAs[A]("r(k)")), xIn, last))
								d.Take(d.TermAs[Nat]("2 * suc(k)"))
								bound := d.Have(
									"the ray's index suc(k) is at most k + 1 and follows the cut k",
									"suc(k) ≤ suc(k) ∧ suc(k) - 1 = k ∧ 2 * suc(k) ≤ 2 * suc(k)",
									ByArith())
								d.Show(
									"x lies above the last cut",
									Simp(Fwd(SignCellDef)),
									By(above, bound, xIn))
							})
					})
			})
	}),
})}

// PolynomialFamilySignTableDef — cuts r(0) < … < r(k − 1) in the carrier
// and a sign t(j, i) for the i-th of m polynomials on the j-th cell: every
// cell is nonempty and each polynomial keeps its sign there.
var PolynomialFamilySignTableDef = polynomialFamilySignTableDefThm{family.Define(registry.DefEntry{
	Name:  "PolynomialFamilySignTableDef",
	Const: "polynomial_family_sign_table",
	Type: "field_ops(A) → " +
		"(A → A → bool) → " +
		"num → " +
		"(num → num → A) → " +
		"num → " +
		"(num → A) → " +
		"(num → num → int) → " +
		"bool",
	Key: "prop_f0ba2f89b708c5e9",
	Equations: []string{
		"∀F:field_ops(A). " +
			"∀lt:(A → A → bool). " +
			"∀m:num. " +
			"∀f:(num → num → A). " +
			"∀k:num. " +
			"∀r:(num → A). " +
			"∀t:(num → num → int). " +
			"    polynomial_family_sign_table(F, lt, m, f, k, r, t) ⇔ " +
			"    increasing_cuts(F, lt, k, r) ∧ " +
			"    (∀j:num. j ≤ 2 * k ⇒ polynomial_sign_cell(F, lt, k, r, j) ≠ ∅) ∧ " +
			"    (∀j i:num. ∀x:A. " +
			"        j ≤ 2 * k ∧ i < m ∧ x ∈ polynomial_sign_cell(F, lt, k, r, j) ⇒ " +
			"        ordered_sign(F, lt, polynomial_eval(F.add, F.zero, F.mul, F.one, f(i), x)) = t(j, i))",
	},
	Deps: []registry.EntryLike{SignCellDef},
})}
