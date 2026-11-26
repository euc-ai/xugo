// statements.go — sign tables uniform in the parameters: the table a family
// of polynomials over the parameter ring has when one list of parameter
// signs gives it in every model, the ways such tables combine, and the
// Cohen–Hörmander step that adds a polynomial to a family.

package parametric_sign_table

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/ordered_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/ordered_field_polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/polynomial_sign_table"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/real_closed_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_formula"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/datatypes/list"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// ParametricSignTableDef — m polynomials in one variable over the parameter
// ring have a sign table given, in every real closed field and environment
// meeting C, by the signs of one fixed list of parameter polynomials.
var ParametricSignTableDef = parametricSignTableDefThm{family.Define(registry.DefEntry{
	Name:  "ParametricSignTableDef",
	Const: "parametric_sign_table",
	Type: "set(num) → " +
		"(field_ops(A) → (A → A → bool) → (num → A) → bool) → " +
		"num → " +
		"(num → num → ((num → num) → int)) → " +
		"bool",
	Key: "prop_f798f5902489b858",
	Equations: []string{
		"∀U:set(num). " +
			"∀C:(field_ops(A) → (A → A → bool) → (num → A) → bool). " +
			"∀m:num. " +
			"∀g:(num → num → ((num → num) → int)). " +
			"    parametric_sign_table(U, C, m, g) ⇔ " +
			"    (∃E:list((num → num) → int). ∃N:(list(int) → num). ∃T:(list(int) → num → num → int). " +
			"        polynomial_list_over(U, E) ∧ " +
			"        (∀F:field_ops(A). ∀lt:(A → A → bool). ∀ρ:(num → A). " +
			"            «model»(U, C, F, lt, ρ) ⇒ " +
			"            (∃r:(num → A). " +
			"                polynomial_family_sign_table(F, " +
			"                    lt, " +
			"                    m, " +
			"                    λi:num. «specialized»(field_ring(F), ρ, g(i)), " +
			"                    N(polynomial_signs(F, lt, ρ, E)), " +
			"                    r, " +
			"                    T(polynomial_signs(F, lt, ρ, E))))))",
	},
})}

// ModelSpecialization — a model of a condition, a real closed field F
// ordered by lt with ρ assigning elements of F to the parameters U, is an
// ordered field, so a field, and specialization at ρ is a ring homomorphism
// from the parameter polynomials into F
// (polynomial_formula.IntegerPolynomialEvalHom), which keeps zero.
var ModelSpecialization = modelSpecializationThm{family.Add(registry.ProofEntry{
	Name: "ModelSpecialization",
	Key:  "prop_2a32a49c566c0d20",
	Build: family.Theorem(Statement{
		Binders: "∀U:set(num). " +
			"∀C:(field_ops(A) → (A → A → bool) → (num → A) → bool). " +
			"∀F:field_ops(A). " +
			"∀lt:(A → A → bool). " +
			"∀ρ:(num → A).",
		Hypotheses: []string{
			"«model»(U, C, F, lt, ρ)",
		},
		Conclusion: "field_on(F) ∧ " +
			"ordered_field_on(F, lt) ∧ " +
			"fo_env_ok(F.carrier, U, ρ) ∧ " +
			"ring_homomorphism(«parameterRing»(U), " +
			"    field_ring(F), " +
			"    λq:((num → num) → int). integer_polynomial_eval(field_ring(F), ρ, q)) ∧ " +
			"integer_polynomial_eval(field_ring(F), ρ, integer_polynomial_ring.zero) = F.zero",
	}, func(
		a *Argument,
		U *Expr[Set[Nat]],
		C *Expr[Fun3[FieldOps[A], Fun2[A, A, Bool], Fun[Nat, A], Bool]],
		F *Expr[FieldOps[A]],
		lt *Arrow2[A, A, Bool],
		ρ *Arrow[Nat, A],
		closed, environment, _ Fact,
	) {
		ordered := real_closed_field.OrderedFieldOn.Read(closed)
		fieldOn := ordered_field.FieldOn.Read(ordered)
		specialization := a.Have(
			"at the ring of F, a field, specialization at ρ is a ring homomorphism",
			"ring_homomorphism(«parameterRing»(U), "+
				"    field_ring(F), "+
				"    λq:((num → num) → int). integer_polynomial_eval(field_ring(F), ρ, q))",
			By(
				environment,
				polynomial_formula.IntegerPolynomialEvalHom.Read(field.RingOn.Read(fieldOn)).At(U, ρ)))
		a.Show(
			"a real closed field is an ordered field, so a field, and the homomorphism keeps zero",
			By(fieldOn, ordered, environment, specialization, ring_homomorphism.MapZero.Read(specialization)))
	}),
})}

// SignTableByCases — a family whose table is uniform under each sign of a
// parameter polynomial c has a uniform table: its parameter list is c
// followed by the three branch lists, and the rule reads the sign of c at the
// head of the sign vector and applies the matching branch's rule to its
// slice of the vector.
var SignTableByCases = signTableByCasesThm{family.Add(registry.ProofEntry{
	Name: "SignTableByCases",
	Key:  "prop_98258d642977e868",
	Build: family.Theorem(Statement{
		Binders: "∀U:set(num). " +
			"∀C:(field_ops(A) → (A → A → bool) → (num → A) → bool). " +
			"∀c:((num → num) → int). " +
			"∀m:num. " +
			"∀g:(num → num → ((num → num) → int)).",
		Hypotheses: []string{
			"c ∈ polynomial_algebra(int_ring, U)",
			"∀σ:int. " +
				"    σ = -&1 ∨ σ = &0 ∨ σ = &1 ⇒ " +
				"    parametric_sign_table(U, " +
				"        λF:field_ops(A). λlt:(A → A → bool). λρ:(num → A). " +
				"            C(F, lt, ρ) ∧ " +
				"            ordered_sign(F, lt, integer_polynomial_eval(field_ring(F), ρ, c)) = σ, " +
				"        m, " +
				"        g)",
		},
		Conclusion: "parametric_sign_table(U, C, m, g)",
	}, func(
		a *Argument,
		U *Expr[Set[Nat]],
		C *Expr[Fun3[FieldOps[A], Fun2[A, A, Bool], Fun[Nat, A], Bool]],
		c *Expr[IntegerPolynomial],
		m *Expr[Nat],
		g *Expr[Fun3[Nat, Nat, Fun[Nat, Nat], Int]],
		cIn, branches Fact,
	) {
		negativeTable := a.Have(
			"under C with c negative, g has a uniform table",
			"parametric_sign_table(U, "+
				"    λF:field_ops(A). λlt:(A → A → bool). λρ:(num → A). "+
				"        C(F, lt, ρ) ∧ ordered_sign(F, lt, integer_polynomial_eval(field_ring(F), ρ, c)) = -&1, "+
				"    m, "+
				"    g)",
			By(branches))
		zeroTable := a.Have(
			"under C with c zero, g has a uniform table",
			"parametric_sign_table(U, "+
				"    λF:field_ops(A). λlt:(A → A → bool). λρ:(num → A). "+
				"        C(F, lt, ρ) ∧ ordered_sign(F, lt, integer_polynomial_eval(field_ring(F), ρ, c)) = &0, "+
				"    m, "+
				"    g)",
			By(branches))
		positiveTable := a.Have(
			"under C with c positive, g has a uniform table",
			"parametric_sign_table(U, "+
				"    λF:field_ops(A). λlt:(A → A → bool). λρ:(num → A). "+
				"        C(F, lt, ρ) ∧ ordered_sign(F, lt, integer_polynomial_eval(field_ring(F), ρ, c)) = &1, "+
				"    m, "+
				"    g)",
			By(branches))
		_, _, _, negativeRule := a.Unpack3As[list.List[IntegerPolynomial], Fun[list.List[Int], Nat], Fun3[list.List[Int], Nat, Nat, Int]](
			a.Unfolded(negativeTable, ParametricSignTableDef),
			"E₁",
			"N₁",
			"T₁")
		negativeParts := a.Conjuncts(
			negativeRule,
			"E₁ lists parameter polynomials",
			"under C with c negative, the signs s of E₁ give g a table with N₁(s) cuts and rows T₁(s)")
		_, _, _, zeroRule := a.Unpack3As[list.List[IntegerPolynomial], Fun[list.List[Int], Nat], Fun3[list.List[Int], Nat, Nat, Int]](
			a.Unfolded(zeroTable, ParametricSignTableDef),
			"E₂",
			"N₂",
			"T₂")
		zeroParts := a.Conjuncts(
			zeroRule,
			"E₂ lists parameter polynomials",
			"under C with c zero, the signs s of E₂ give g a table with N₂(s) cuts and rows T₂(s)")
		_, _, _, positiveRule := a.Unpack3As[list.List[IntegerPolynomial], Fun[list.List[Int], Nat], Fun3[list.List[Int], Nat, Nat, Int]](
			a.Unfolded(positiveTable, ParametricSignTableDef),
			"E₃",
			"N₃",
			"T₃")
		positiveParts := a.Conjuncts(
			positiveRule,
			"E₃ lists parameter polynomials",
			"under C with c positive, the signs s of E₃ give g a table with N₃(s) cuts and rows T₃(s)")
		E, EDef := a.LetAs[list.List[IntegerPolynomial]](
			"E", "cons(c, list_append(E₁, list_append(E₂, E₃)))")
		_, sliceDef := a.LetAs[Fun3[list.List[Int], Nat, Nat, list.List[Int]]](
			"slice",
			"λs:list(int). λo:num. λn:num. εx:list(int). "+
				"    list_length(x) = n ∧ (∀i:num. i < n ⇒ list_nth(x, i) = list_nth(s, o + i))")
		sliced := a.Have(
			"a list l of length n whose entries are those of s from offset o on is the slice of s at o",
			Statement{
				Binders: "∀s l:list(int). ∀o n:num.",
				Hypotheses: []string{
					"list_length(l) = n",
					"∀i:num. i < n ⇒ list_nth(s, o + i) = list_nth(l, i)",
				},
				Conclusion: "slice(s, o, n) = l",
			},
			Derive(func(b *Argument) {
				b.FixAs[list.List[Int]]("s")
				l := b.FixAs[list.List[Int]]("l")
				b.FixAs[Nat]("o")
				b.FixAs[Nat]("n")
				assumed := b.Assume()
				exists := b.Have(
					"l is such a list",
					"∃x:list(int). list_length(x) = n ∧ (∀i:num. i < n ⇒ list_nth(x, i) = list_nth(s, o + i))",
					Derive(func(c *Argument) {
						c.Take(l)
						c.Show(
							"l has the length n and the entries of s from o on",
							By(assumed))
					}))
				_, chosen := b.ObtainChosen(
					"the slice of s at offset o",
					"∃x:list(int). list_length(x) = n ∧ (∀i:num. i < n ⇒ list_nth(x, i) = list_nth(s, o + i))",
					exists)
				property := b.Have(
					"so does the slice",
					"list_length(slice(s, o, n)) = n ∧ "+
						"(∀i:num. i < n ⇒ list_nth(slice(s, o, n), i) = list_nth(s, o + i))",
					Simp(Fwd(sliceDef)),
					By(chosen))
				b.Show(
					"two lists of one length with the same entries are equal",
					By(list.NthExtensionality.At(b.TermAs[list.List[Int]]("slice(s, o, n)"), l), property, assumed))
			}))
		count, countDef := a.LetAs[Fun[list.List[Int], Nat]](
			"count",
			"λs:list(int). "+
				"    COND(list_nth(s, 0) = -&1, "+
				"        N₁(slice(s, 1, list_length(E₁))), "+
				"        COND(list_nth(s, 0) = &0, "+
				"            N₂(slice(s, suc(list_length(E₁)), list_length(E₂))), "+
				"            N₃(slice(s, suc(list_length(E₁) + list_length(E₂)), list_length(E₃)))))")
		rows, rowsDef := a.LetAs[Fun3[list.List[Int], Nat, Nat, Int]](
			"rows",
			"λs:list(int). "+
				"    COND(list_nth(s, 0) = -&1, "+
				"        T₁(slice(s, 1, list_length(E₁))), "+
				"        COND(list_nth(s, 0) = &0, "+
				"            T₂(slice(s, suc(list_length(E₁)), list_length(E₂))), "+
				"            T₃(slice(s, suc(list_length(E₁) + list_length(E₂)), list_length(E₃)))))")
		listed := a.Have(
			"E lists parameter polynomials: c and the members of the three branch lists",
			"polynomial_list_over(U, E)",
			Derive(func(b *Argument) {
				b.Do(Unfold(polynomial_formula.PolynomialListOverDef))
				p := b.FixAs[IntegerPolynomial]("p")
				member := b.Assume()
				where := b.Have(
					"p is c or a member of one of the three lists",
					"p = c ∨ list_member(p, E₁) ∨ list_member(p, E₂) ∨ list_member(p, E₃)",
					By(member, EDef, list.ListMemberDef, list.MemberAppend))
				b.Show(
					"each lists parameter polynomials, and c is one",
					By(
						Normalized,
						where,
						cIn,
						polynomial_formula.PolynomialOnVariables.At(U, c),
						negativeParts[0].At(p),
						zeroParts[0].At(p),
						positiveParts[0].At(p)))
			}))
		perModel := a.Have(
			"in every model meeting C, the branch of the sign of c gives g its table",
			Statement{
				Binders: "∀F:field_ops(A). ∀lt:(A → A → bool). ∀ρ:(num → A).",
				Hypotheses: []string{
					"«model»(U, C, F, lt, ρ)",
				},
				Conclusion: "∃r:(num → A). " +
					"    polynomial_family_sign_table(F, " +
					"        lt, " +
					"        m, " +
					"        λi:num. «specialized»(field_ring(F), ρ, g(i)), " +
					"        count(polynomial_signs(F, lt, ρ, E)), " +
					"        r, " +
					"        rows(polynomial_signs(F, lt, ρ, E)))",
			},
			Derive(func(b *Argument) {
				F := b.FixAs[FieldOps[A]]("F")
				lt := b.FixAs[Fun2[A, A, Bool]]("lt")
				ρ := b.FixAs[Fun[Nat, A]]("ρ")
				model := b.Assume()
				head := b.TermAs[Int]("ordered_sign(F, lt, integer_polynomial_eval(field_ring(F), ρ, c))")
				signs := b.TermAs[list.List[Int]]("polynomial_signs(F, lt, ρ, E)")
				decomposition := b.Have(
					"the signs of E are the sign of c followed by the three branch sign lists",
					"polynomial_signs(F, lt, ρ, E) = "+
						"cons(ordered_sign(F, lt, integer_polynomial_eval(field_ring(F), ρ, c)), "+
						"    list_append(polynomial_signs(F, lt, ρ, E₁), "+
						"        list_append(polynomial_signs(F, lt, ρ, E₂), polynomial_signs(F, lt, ρ, E₃))))",
					EDef.Rw(),
					Simp(Fwd(polynomial_sign_table.SignsDef), Fwd(list.ListMapDef), Fwd(list.MapAppend)),
					By(EDef))
				lengths := b.Have(
					"each branch sign list is as long as its parameter list",
					"list_length(polynomial_signs(F, lt, ρ, E₁)) = list_length(E₁) ∧ "+
						"list_length(polynomial_signs(F, lt, ρ, E₂)) = list_length(E₂) ∧ "+
						"list_length(polynomial_signs(F, lt, ρ, E₃)) = list_length(E₃)",
					Simp(Fwd(polynomial_sign_table.SignsDef), Fwd(list.LengthMap)),
					By(EDef))
				first := b.Have(
					"the head of the sign vector is the sign of c",
					"list_nth(polynomial_signs(F, lt, ρ, E), 0) = "+
						"ordered_sign(F, lt, integer_polynomial_eval(field_ring(F), ρ, c))",
					decomposition.Rw(),
					By(list.NthHead))
				negativeEntries := b.Have(
					"the entries of the sign vector at offset 1 are the signs of E₁",
					Statement{
						Binders: "∀i:num.",
						Hypotheses: []string{
							"i < list_length(E₁)",
						},
						Conclusion: "list_nth(polynomial_signs(F, lt, ρ, E), 1 + i) = " +
							"list_nth(polynomial_signs(F, lt, ρ, E₁), i)",
					},
					Derive(func(c *Argument) {
						i := c.FixAs[Nat]("i")
						iLt := c.Assume()
						c.Show(
							"through the head and the appends",
							By(
								decomposition,
								c.Have(
									"past the head, the entry at 1 + i is the tail's at i",
									"1 + i = suc(i)",
									ByArith()),
								list.NthTail.At(
									head,
									c.TermAs[list.List[Int]](
										"list_append(polynomial_signs(F, lt, ρ, E₁), "+
											"    list_append(polynomial_signs(F, lt, ρ, E₂), polynomial_signs(F, lt, ρ, E₃)))"),
									i),
								list.NthAppendLeft.At(
									c.TermAs[list.List[Int]]("polynomial_signs(F, lt, ρ, E₁)"),
									c.TermAs[list.List[Int]](
										"list_append(polynomial_signs(F, lt, ρ, E₂), polynomial_signs(F, lt, ρ, E₃))"),
									i),
								lengths,
								iLt))
					}))
				negativeSlice := b.Have(
					"so the slice at offset 1 is the sign vector of E₁",
					"slice(polynomial_signs(F, lt, ρ, E), 1, list_length(E₁)) = polynomial_signs(F, lt, ρ, E₁)",
					By(GroupPremises(
						lengths,
						negativeEntries,
						sliced.At(
							signs,
							b.TermAs[list.List[Int]]("polynomial_signs(F, lt, ρ, E₁)"),
							b.TermAs[Nat]("1"),
							b.TermAs[Nat]("list_length(E₁)")))))
				zeroEntries := b.Have(
					"the entries of the sign vector at offset suc(list_length(E₁)) are the signs of E₂",
					Statement{
						Binders: "∀i:num.",
						Hypotheses: []string{
							"i < list_length(E₂)",
						},
						Conclusion: "list_nth(polynomial_signs(F, lt, ρ, E), suc(list_length(E₁)) + i) = " +
							"list_nth(polynomial_signs(F, lt, ρ, E₂), i)",
					},
					Derive(func(c *Argument) {
						i := c.FixAs[Nat]("i")
						iLt := c.Assume()
						c.Show(
							"through the head and the appends",
							By(
								decomposition,
								c.Have(
									"past the head, the entry at |E₁| + 1 + i is the tail's at |E₁| + i",
									"suc(list_length(E₁)) + i = suc(list_length(E₁) + i)",
									ByArith()),
								list.NthTail.At(
									head,
									c.TermAs[list.List[Int]](
										"list_append(polynomial_signs(F, lt, ρ, E₁), "+
											"    list_append(polynomial_signs(F, lt, ρ, E₂), polynomial_signs(F, lt, ρ, E₃)))"),
									c.TermAs[Nat]("list_length(E₁) + i")),
								list.NthAppendRight.At(
									c.TermAs[list.List[Int]]("polynomial_signs(F, lt, ρ, E₁)"),
									c.TermAs[list.List[Int]](
										"list_append(polynomial_signs(F, lt, ρ, E₂), polynomial_signs(F, lt, ρ, E₃))"),
									i),
								list.NthAppendLeft.At(
									c.TermAs[list.List[Int]]("polynomial_signs(F, lt, ρ, E₂)"),
									c.TermAs[list.List[Int]]("polynomial_signs(F, lt, ρ, E₃)"),
									i),
								lengths,
								iLt))
					}))
				zeroSlice := b.Have(
					"so the slice at offset suc(list_length(E₁)) is the sign vector of E₂",
					"slice(polynomial_signs(F, lt, ρ, E), suc(list_length(E₁)), list_length(E₂)) = "+
						"polynomial_signs(F, lt, ρ, E₂)",
					By(GroupPremises(
						lengths,
						zeroEntries,
						sliced.At(
							signs,
							b.TermAs[list.List[Int]]("polynomial_signs(F, lt, ρ, E₂)"),
							b.TermAs[Nat]("suc(list_length(E₁))"),
							b.TermAs[Nat]("list_length(E₂)")))))
				positiveEntries := b.Have(
					"the entries of the sign vector at offset "+
						"suc(list_length(E₁) + list_length(E₂)) are the signs of E₃",
					Statement{
						Binders: "∀i:num.",
						Hypotheses: []string{
							"i < list_length(E₃)",
						},
						Conclusion: "list_nth(polynomial_signs(F, lt, ρ, E), " +
							"    suc(list_length(E₁) + list_length(E₂)) + i) = " +
							"list_nth(polynomial_signs(F, lt, ρ, E₃), i)",
					},
					Derive(func(c *Argument) {
						i := c.FixAs[Nat]("i")
						iLt := c.Assume()
						c.Show(
							"through the head and the appends",
							By(
								decomposition,
								c.Have(
									"past the head, the entry at |E₁| + |E₂| + 1 + i is the tail's at |E₁| + (|E₂| + i)",
									"suc(list_length(E₁) + list_length(E₂)) + i = suc(list_length(E₁) + (list_length(E₂) + i))",
									ByArith()),
								list.NthTail.At(
									head,
									c.TermAs[list.List[Int]](
										"list_append(polynomial_signs(F, lt, ρ, E₁), "+
											"    list_append(polynomial_signs(F, lt, ρ, E₂), polynomial_signs(F, lt, ρ, E₃)))"),
									c.TermAs[Nat]("list_length(E₁) + (list_length(E₂) + i)")),
								list.NthAppendRight.At(
									c.TermAs[list.List[Int]]("polynomial_signs(F, lt, ρ, E₁)"),
									c.TermAs[list.List[Int]](
										"list_append(polynomial_signs(F, lt, ρ, E₂), polynomial_signs(F, lt, ρ, E₃))"),
									c.TermAs[Nat]("list_length(E₂) + i")),
								list.NthAppendRight.At(
									c.TermAs[list.List[Int]]("polynomial_signs(F, lt, ρ, E₂)"),
									c.TermAs[list.List[Int]]("polynomial_signs(F, lt, ρ, E₃)"),
									i),
								lengths,
								iLt))
					}))
				positiveSlice := b.Have(
					"so the slice at offset suc(list_length(E₁) + list_length(E₂)) is the sign vector of E₃",
					"slice(polynomial_signs(F, lt, ρ, E), suc(list_length(E₁) + list_length(E₂)), list_length(E₃)) = "+
						"polynomial_signs(F, lt, ρ, E₃)",
					By(GroupPremises(
						lengths,
						positiveEntries,
						sliced.At(
							signs,
							b.TermAs[list.List[Int]]("polynomial_signs(F, lt, ρ, E₃)"),
							b.TermAs[Nat]("suc(list_length(E₁) + list_length(E₂))"),
							b.TermAs[Nat]("list_length(E₃)")))))
				signCases := b.Have(
					"the sign of c is −1, 0 or 1",
					"ordered_sign(F, lt, integer_polynomial_eval(field_ring(F), ρ, c)) = -&1 ∨ "+
						"ordered_sign(F, lt, integer_polynomial_eval(field_ring(F), ρ, c)) = &0 ∨ "+
						"ordered_sign(F, lt, integer_polynomial_eval(field_ring(F), ρ, c)) = &1",
					By(ordered_field.OrderedSignDef))
				distinct := b.Have(
					"the three signs are distinct",
					"¬(0 = -int_of_num(1)) ∧ ¬(1 = -int_of_num(1)) ∧ ¬(1 = int_of_num(0))",
					ByArith())
				branchTable := func(d *Argument, sign Fact, rule Fact, slice Fact) {
					d.Show(
						"the branch's rule, applied to the slice of the sign vector that is its own",
						Simp(Fwd(countDef), Fwd(rowsDef)),
						By(GroupPremises(model, sign, rule.At(F, lt, ρ)), first, slice, distinct))
				}
				b.Cases(b.TermAs[Bool]("ordered_sign(F, lt, integer_polynomial_eval(field_ring(F), ρ, c)) = -&1"))
				b.When(
					"c is negative: the first branch",
					func(d *Argument, sign Fact) {
						branchTable(d, sign, negativeParts[1], negativeSlice)
					})
				b.Otherwise(
					"c is not negative",
					func(d *Argument, notNegative Fact) {
						d.Cases(d.TermAs[Bool]("ordered_sign(F, lt, integer_polynomial_eval(field_ring(F), ρ, c)) = &0"))
						d.When(
							"c is zero: the second branch",
							func(e *Argument, sign Fact) {
								branchTable(e, sign, zeroParts[1], zeroSlice)
							})
						d.Otherwise(
							"c is positive: the third branch",
							func(e *Argument, notZero Fact) {
								sign := e.Have(
									"so the sign of c is 1",
									"ordered_sign(F, lt, integer_polynomial_eval(field_ring(F), ρ, c)) = &1",
									By(signCases, notNegative, notZero))
								branchTable(e, sign, positiveParts[1], positiveSlice)
							})
					})
			}))
		a.Do(Unfold(ParametricSignTableDef))
		a.Take(E)
		a.Take(count)
		a.Take(rows)
		a.Show(
			"E with the rule read through the sign of c gives g a uniform table",
			By(listed, perModel))
	}),
})}

// SignTableByAgreement — a family whose members take, point by point, the
// signs of chosen members of a family with a uniform table has one too: the
// same parameter list E and cut count N serve, the same cuts serve in every
// model, and the row of the i-th new member is that of the π(i)-th old one.
var SignTableByAgreement = signTableByAgreementThm{family.Add(registry.ProofEntry{
	Name: "SignTableByAgreement",
	Key:  "prop_5d1560572cdf1d19",
	Build: family.Theorem(Statement{
		Binders: "∀U:set(num). " +
			"∀C:(field_ops(A) → (A → A → bool) → (num → A) → bool). " +
			"∀m n:num. " +
			"∀g k:(num → num → ((num → num) → int)). " +
			"∀π:(num → num).",
		Hypotheses: []string{
			"∀i:num. i < n ⇒ π(i) < m",
			"∀F:field_ops(A). ∀lt:(A → A → bool). ∀ρ:(num → A). ∀i:num. ∀x:A. " +
				"    «model»(U, C, F, lt, ρ) ∧ i < n ∧ x ∈ F.carrier ⇒ " +
				"    ordered_sign(F, lt, «value»(F, ρ, k(i), x)) = ordered_sign(F, lt, «value»(F, ρ, g(π(i)), x))",
			"parametric_sign_table(U, C, m, g)",
		},
		Conclusion: "parametric_sign_table(U, C, n, k)",
	}, func(
		a *Argument,
		U *Expr[Set[Nat]],
		C *Expr[Fun3[FieldOps[A], Fun2[A, A, Bool], Fun[Nat, A], Bool]],
		m, n *Expr[Nat],
		g, k *Expr[Fun3[Nat, Nat, Fun[Nat, Nat], Int]],
		π *Arrow[Nat, Nat],
		into, agree, table Fact,
	) {
		E, N, _, rule := a.Unpack3As[list.List[IntegerPolynomial], Fun[list.List[Int], Nat], Fun3[list.List[Int], Nat, Nat, Int]](
			a.Unfolded(table, ParametricSignTableDef),
			"E",
			"N",
			"T")
		given := a.Conjuncts(
			rule,
			"E lists parameter polynomials",
			"in every model meeting C, the signs s of E give g a table with N(s) cuts and rows T(s)")
		listed, tables := given[0], given[1]
		readThrough := a.Have(
			"in every model meeting C, the same cuts give k a table whose row entry for k(i) is T(s, j, π(i))",
			Statement{
				Binders: "∀F:field_ops(A). ∀lt:(A → A → bool). ∀ρ:(num → A).",
				Hypotheses: []string{
					"«model»(U, C, F, lt, ρ)",
				},
				Conclusion: "∃r:(num → A). " +
					"    polynomial_family_sign_table(F, " +
					"        lt, " +
					"        n, " +
					"        λi:num. «specialized»(field_ring(F), ρ, k(i)), " +
					"        N(polynomial_signs(F, lt, ρ, E)), " +
					"        r, " +
					"        λj:num. λi:num. T(polynomial_signs(F, lt, ρ, E), j, π(i)))",
			},
			Derive(func(b *Argument) {
				F := b.FixAs[FieldOps[A]]("F")
				lt := b.FixAs[Fun2[A, A, Bool]]("lt")
				ρ := b.FixAs[Fun[Nat, A]]("ρ")
				model := b.Assume()
				r, oldTable := b.UnpackAs[Fun[Nat, A]](GroupPremises(model, tables.At(F, lt, ρ)), "r")
				old := b.Conjuncts(
					b.Unfolded(oldTable, polynomial_sign_table.PolynomialFamilySignTableDef),
					"the cuts increase in the carrier",
					"every cell is nonempty",
					"g(i) has sign T(s, j, i) on cell j")
				cuts, nonempty, oldRows := old[0], old[1], old[2]
				rows := b.Have(
					"k(i) has the sign of g(π(i)) on every cell",
					Statement{
						Binders: "∀j i:num. ∀x:A.",
						Hypotheses: []string{
							"j ≤ 2 * N(polynomial_signs(F, lt, ρ, E))",
							"i < n",
							"x ∈ polynomial_sign_cell(F, lt, N(polynomial_signs(F, lt, ρ, E)), r, j)",
						},
						Conclusion: "ordered_sign(F, lt, «value»(F, ρ, k(i), x)) = " +
							"T(polynomial_signs(F, lt, ρ, E), j, π(i))",
					},
					Derive(func(c *Argument) {
						j := c.FixAs[Nat]("j")
						i := c.FixAs[Nat]("i")
						x := c.FixAs[A]("x")
						point := c.Conjuncts(
							c.Assume(),
							"j is a cell index",
							"i indexes a member of k",
							"x lies in cell j")
						jLe, iLt, inCell := point[0], point[1], point[2]
						xIn := c.Have(
							"x lies in the carrier",
							"x ∈ F.carrier",
							By(
								inCell,
								polynomial_sign_table.SignCellInCarrier.At(
									F, lt, c.TermAs[Nat]("N(polynomial_signs(F, lt, ρ, E))"), r, j, x)))
						c.Show(
							"k(i) agrees in sign with g(π(i)), whose sign on cell j is T(s, j, π(i))",
							By(
								agree.At(F, lt, ρ, i, x),
								model,
								iLt,
								xIn,
								into.At(i),
								oldRows.At(j, π.Apply(i), x),
								jLe,
								inCell))
					}))
				b.Take(r)
				b.Show(
					"the cuts are g's, and the rows are read through π",
					Simp(Fwd(polynomial_sign_table.PolynomialFamilySignTableDef)),
					By(cuts, nonempty, rows))
			}))
		a.Do(Unfold(ParametricSignTableDef))
		a.Take(E)
		a.Take(N)
		a.Take(a.TermAs[Fun3[list.List[Int], Nat, Nat, Int]]("λs:list(int). λj:num. λi:num. T(s, j, π(i))"))
		a.Show(
			"E, N and the rows read through π give k a uniform table",
			By(listed, readThrough))
	}),
})}

// ConstantFamilySignTable — a family of constants has a uniform table with
// one cell: the parameter list E lists the constant coefficients g(0, 0), …,
// g(m − 1, 0), there are no cuts, and on the one cell, the carrier, the i-th
// member has the sign of its specialized constant, the i-th entry of the
// sign vector of E.
var ConstantFamilySignTable = constantFamilySignTableThm{family.Add(registry.ProofEntry{
	Name: "ConstantFamilySignTable",
	Key:  "prop_d3b426e87dfb8e7b",
	Build: family.Theorem(Statement{
		Binders: "∀U:set(num). " +
			"∀C:(field_ops(A) → (A → A → bool) → (num → A) → bool). " +
			"∀m:num. " +
			"∀g:(num → num → ((num → num) → int)).",
		Hypotheses: []string{
			"∀i:num. i < m ⇒ g(i, 0) ∈ polynomial_algebra(int_ring, U)",
			"∀i n:num. i < m ∧ 0 < n ⇒ g(i, n) = integer_polynomial_ring.zero",
		},
		Conclusion: "parametric_sign_table(U, C, m, g)",
	}, func(
		a *Argument,
		U *Expr[Set[Nat]],
		C *Expr[Fun3[FieldOps[A], Fun2[A, A, Bool], Fun[Nat, A], Bool]],
		m *Expr[Nat],
		g *Expr[Fun3[Nat, Nat, Fun[Nat, Nat], Int]],
		constants, vanishing Fact,
	) {
		E, tabulated := a.UnpackAs[list.List[IntegerPolynomial]](
			list.TabulatedList.At(a.TermAs[Fun[Nat, IntegerPolynomial]]("λi:num. g(i, 0)"), m),
			"E")
		entries := a.Conjuncts(
			tabulated,
			"E has m entries",
			"its i-th entry is g(i, 0)")
		listed := a.Have(
			"E lists parameter polynomials, the constants g(i, 0)",
			"polynomial_list_over(U, E)",
			Derive(func(b *Argument) {
				b.Do(Unfold(polynomial_formula.PolynomialListOverDef))
				p := b.FixAs[IntegerPolynomial]("p")
				member := b.Assume()
				i, at := b.ObtainAs[Nat](
					"p is an entry of E",
					"∃i:num. i < list_length(E) ∧ list_nth(E, i) = p",
					By(member, list.MemberNth.At(p, E)))
				place := b.Conjuncts(
					at,
					"i lies below the length of E",
					"p is the i-th entry")
				b.Show(
					"p = g(i, 0), a parameter polynomial",
					By(
						Normalized,
						constants.At(i),
						entries[0],
						entries[1].At(i),
						place[0],
						place[1],
						polynomial_formula.PolynomialOnVariables.At(U, p)))
			}))
		zeroIn := a.Have(
			"the zero polynomial is a parameter polynomial, having no variable",
			"fun_zero(int_of_num(0)) ∈ polynomial_algebra(int_ring, U)",
			BySets(
				polynomial_formula.ZeroPolynomialValid,
				polynomial_formula.PolynomialOnVariables.At(
					U, a.TermAs[IntegerPolynomial]("fun_zero(int_of_num(0))"))))
		overParameters := a.Have(
			"each member is a constant polynomial over the parameters",
			"∀i:num. i < m ⇒ «overParameters»(g(i))",
			Derive(func(b *Argument) {
				i := b.FixAs[Nat]("i")
				iLt := b.Assume()
				constant := b.Have(
					"g(i) vanishes from 1 on",
					"vec⟨1⟩(fun_zero(int_of_num(0)), g(i))",
					Derive(func(c *Argument) {
						c.Do(Simp(Fwd(vec_space.VecDef)))
						n := c.FixAs[Nat]("n")
						past := c.Assume()
						c.Show(
							"a coefficient past 0 is zero",
							By(
								vanishing.At(i, n),
								iLt,
								c.Have(
									"n is positive",
									"0 < n",
									ByArith(past))))
					}))
				coefficients := b.Have(
					"its coefficients are g(i, 0) and zeros, all parameter polynomials",
					"∀k:num. g(i, k) ∈ polynomial_algebra(int_ring, U)",
					Derive(func(c *Argument) {
						k := c.FixAs[Nat]("k")
						c.Cases(c.TermAs[Bool]("k = 0"))
						c.When(
							"the constant coefficient",
							func(d *Argument, isZero Fact) {
								d.Show(
									"g(i, 0) is a parameter polynomial",
									By(Normalized, constants.At(i), iLt, isZero))
							})
						c.Otherwise(
							"a higher coefficient is the zero polynomial",
							func(d *Argument, positive Fact) {
								d.Show(
									"which is a parameter polynomial",
									By(
										Normalized,
										vanishing.At(i, k),
										iLt,
										d.Have(
											"k is positive",
											"0 < k",
											ByArith(positive)),
										zeroIn))
							})
					}))
				b.Do(Unfold(polynomial.PolynomialOverDef))
				b.Show(
					"a polynomial: it vanishes from 1 on, and its coefficients are parameter polynomials",
					By(Normalized, constant, coefficients))
			}))
		perModel := a.Have(
			"in every model, the one cell carries the signs of the specialized constants",
			Statement{
				Binders: "∀F:field_ops(A). ∀lt:(A → A → bool). ∀ρ:(num → A).",
				Hypotheses: []string{
					"«model»(U, C, F, lt, ρ)",
				},
				Conclusion: "∃r:(num → A). " +
					"    polynomial_family_sign_table(F, " +
					"        lt, " +
					"        m, " +
					"        λi:num. «specialized»(field_ring(F), ρ, g(i)), " +
					"        0, " +
					"        r, " +
					"        λj:num. λi:num. list_nth(polynomial_signs(F, lt, ρ, E), i))",
			},
			Derive(func(b *Argument) {
				F := b.FixAs[FieldOps[A]]("F")
				lt := b.FixAs[Fun2[A, A, Bool]]("lt")
				ρ := b.FixAs[Fun[Nat, A]]("ρ")
				opened := b.Conjuncts(
					GroupPremises(b.Assume(), ModelSpecialization.At(U, C, F, lt, ρ)),
					"F is a field",
					"F with lt is an ordered field",
					"ρ gives carrier points to the parameters",
					"specialization at ρ is a ring homomorphism",
					"that keeps zero")
				ordered, environment, keepsZero := opened[1], opened[2], opened[4]
				ring := field.RingOn.Read(opened[0])
				constantValue := b.Have(
					"each member takes the value of its specialized constant",
					Statement{
						Binders: "∀i:num. ∀x:A.",
						Hypotheses: []string{
							"i < m",
							"x ∈ F.carrier",
						},
						Conclusion: "«value»(F, ρ, g(i), x) = integer_polynomial_eval(field_ring(F), ρ, g(i, 0))",
					},
					Derive(func(c *Argument) {
						i := c.FixAs[Nat]("i")
						x := c.FixAs[A]("x")
						given := c.Conjuncts(
							c.Assume(),
							"i indexes a member",
							"x lies in the carrier")
						member := c.TermAs[Fun[Nat, A]]("«specialized»(field_ring(F), ρ, g(i))")
						over := c.Have(
							"the member is a polynomial over F",
							"polynomial_over(F.zero, F.carrier, «specialized»(field_ring(F), ρ, g(i)))",
							By(
								polynomial_formula.SpecializedPolynomial.Read(ring).At(
									U, ρ, c.TermAs[Fun2[Nat, Fun[Nat, Nat], Int]]("g(i)")),
								environment,
								overParameters.At(i),
								given[0]))
						constant := c.Have(
							"it vanishes from 1 on",
							"vec⟨1⟩(F.zero, «specialized»(field_ring(F), ρ, g(i)))",
							Derive(func(d *Argument) {
								d.Do(Simp(Fwd(vec_space.VecDef)))
								n := d.FixAs[Nat]("n")
								past := d.Assume()
								d.Show(
									"its coefficients past 0 specialize the zero polynomial",
									By(
										Normalized,
										vanishing.At(i, n),
										given[0],
										d.Have(
											"n is positive",
											"0 < n",
											ByArith(past)),
										keepsZero))
							}))
						degreeZero := c.Have(
							"so it has degree 0",
							"polynomial_degree(F.zero, «specialized»(field_ring(F), ρ, g(i))) = 0",
							By(
								polynomial.DegreeZeroIff.At(c.TermAs[A]("F.zero"), c.TermAs[Set[A]]("F.carrier"), member),
								over,
								constant))
						c.Show(
							"a polynomial of degree 0 takes its constant coefficient as its value",
							By(
								polynomial_evaluation.DegreeZeroEval.Read(ring).At(member, c.MemberOf[on.Any](x, given[1])),
								over,
								degreeZero))
					}))
				noCuts := b.TermAs[Fun[Nat, A]]("λi:num. F.zero")
				vacuous := b.Have(
					"there are no cuts, so the cut condition holds vacuously",
					"increasing_cuts(F, lt, 0, λi:num. F.zero)",
					Unfold(ordered_field.IncreasingCutsDef),
					ByArith())
				rows := b.Have(
					"on the one cell each member has the sign of its constant, the i-th entry of the sign vector",
					Statement{
						Binders: "∀j i:num. ∀x:A.",
						Hypotheses: []string{
							"j ≤ 2 * 0",
							"i < m",
							"x ∈ polynomial_sign_cell(F, lt, 0, λi:num. F.zero, j)",
						},
						Conclusion: "ordered_sign(F, lt, «value»(F, ρ, g(i), x)) = " +
							"list_nth(polynomial_signs(F, lt, ρ, E), i)",
					},
					Derive(func(c *Argument) {
						j := c.FixAs[Nat]("j")
						i := c.FixAs[Nat]("i")
						x := c.FixAs[A]("x")
						given := c.Conjuncts(
							c.Assume(),
							"j is the one cell",
							"i indexes a member",
							"x lies in the cell")
						xIn := c.Have(
							"x lies in the carrier",
							"x ∈ F.carrier",
							By(given[2], polynomial_sign_table.SignCellInCarrier.At(F, lt, c.TermAs[Nat]("0"), noCuts, j, x)))
						c.Show(
							"the i-th entry of the sign vector of E is the sign of g(i, 0)",
							By(
								constantValue.At(i, x),
								given[1],
								xIn,
								polynomial_sign_table.SignsDef,
								list.NthMap.At(
									c.TermAs[Fun[IntegerPolynomial, Int]](
										"λp:((num → num) → int). ordered_sign(F, lt, integer_polynomial_eval(field_ring(F), ρ, p))"),
									E,
									i),
								entries[0],
								entries[1].At(i)))
					}))
				nonempty := b.Have(
					"the one cell is nonempty",
					"∀j:num. j ≤ 2 * 0 ⇒ polynomial_sign_cell(F, lt, 0, λi:num. F.zero, j) ≠ ∅",
					Derive(func(c *Argument) {
						j := c.FixAs[Nat]("j")
						bound := c.Assume()
						c.Show(
							"cells of no cuts are nonempty",
							By(
								polynomial_sign_table.SignCellsNonempty.At(F, lt, c.TermAs[Nat]("0"), noCuts, j),
								ordered,
								vacuous,
								bound))
					}))
				b.Take(noCuts)
				b.Show(
					"no cuts, one nonempty cell, and its row",
					Simp(Fwd(polynomial_sign_table.PolynomialFamilySignTableDef)),
					By(vacuous, nonempty, rows))
			}))
		a.Do(Unfold(ParametricSignTableDef))
		a.Take(E)
		a.Take(a.TermAs[Fun[list.List[Int], Nat]]("λs:list(int). 0"))
		a.Take(
			a.TermAs[Fun3[list.List[Int], Nat, Nat, Int]]("λs:list(int). λj:num. λi:num. list_nth(s, i)"))
		a.Show(
			"E with one cell and the entries of its sign vector",
			By(listed, perModel))
	}),
})}

// SignTableUnderStrongerCondition — a table under a condition K is a table
// under every condition C that implies K in each model: the parameter list,
// the cut count and the rows that serve K serve C.
var SignTableUnderStrongerCondition = signTableUnderStrongerConditionThm{family.Add(registry.ProofEntry{
	Name: "SignTableUnderStrongerCondition",
	Key:  "prop_d90a80e54fddc913",
	Build: family.Theorem(Statement{
		Binders: "∀U:set(num). " +
			"∀C K:(field_ops(A) → (A → A → bool) → (num → A) → bool). " +
			"∀m:num. " +
			"∀g:(num → num → ((num → num) → int)).",
		Hypotheses: []string{
			"∀F:field_ops(A). ∀lt:(A → A → bool). ∀ρ:(num → A). «model»(U, C, F, lt, ρ) ⇒ K(F, lt, ρ)",
			"parametric_sign_table(U, K, m, g)",
		},
		Conclusion: "parametric_sign_table(U, C, m, g)",
	}, func(
		a *Argument,
		U *Expr[Set[Nat]],
		C, K *Expr[Fun3[FieldOps[A], Fun2[A, A, Bool], Fun[Nat, A], Bool]],
		m *Expr[Nat],
		g *Expr[Fun3[Nat, Nat, Fun[Nat, Nat], Int]],
		implies, table Fact,
	) {
		a.Show(
			"every model meeting C meets K, so the rule that gives g its table under K gives it under C",
			By(implies, table, ParametricSignTableDef))
	}),
})}

// SignTableBySigns — a family whose table is uniform under every assignment
// s of signs to finitely many parameter polynomials q(j), j ∈ I, has a
// uniform table: by induction over the finite set I, one more index x is
// split on the sign σ of q(x) (SignTableByCases), and under each sign the
// tables for the other indices come from those for I with s extended by σ
// at x.
var SignTableBySigns = signTableBySignsThm{family.Add(registry.ProofEntry{
	Name: "SignTableBySigns",
	Key:  "prop_8d9d0ea18743dcf3",
	Build: family.Theorem(Statement{
		Binders: "∀U:set(num). " +
			"∀I:set(B). " +
			"∀q:(B → ((num → num) → int)). " +
			"∀m:num. " +
			"∀g:(num → num → ((num → num) → int)). " +
			"∀C:(field_ops(A) → (A → A → bool) → (num → A) → bool).",
		Hypotheses: []string{
			"finite(I)",
			"∀j:B. j ∈ I ⇒ q(j) ∈ polynomial_algebra(int_ring, U)",
			"∀s:(B → int). " +
				"    parametric_sign_table(U, " +
				"        λF:field_ops(A). λlt:(A → A → bool). λρ:(num → A). " +
				"            C(F, lt, ρ) ∧ " +
				"            (∀j:B. " +
				"                j ∈ I ⇒ " +
				"                ordered_sign(F, lt, integer_polynomial_eval(field_ring(F), ρ, q(j))) = s(j)), " +
				"        m, " +
				"        g)",
		},
		Conclusion: "parametric_sign_table(U, C, m, g)",
	}, func(
		a *Argument,
		U *Expr[Set[Nat]],
		I *Expr[Set[B]],
		q *Arrow[B, IntegerPolynomial],
		m *Expr[Nat],
		g *Expr[Fun3[Nat, Nat, Fun[Nat, Nat], Int]],
		finiteI, inParameters Fact,
	) {
		a.Show(
			"by induction over the finite set I, for every condition at once",
			ByInduction(
				finite_set.FiniteInduct,
				finiteI,
				Generalizing(inParameters),
				Case(
					"over no index the sign condition is empty, so any sign function gives the table under K",
					Derive(func(b *Argument) {
						b.Assume()
						K := b.FixAs[Fun3[FieldOps[A], Fun2[A, A, Bool], Fun[Nat, A], Bool]]("K")
						split := b.Assume()
						empty := b.Have(
							"a model meeting K meets K with no further sign condition",
							Statement{
								Binders: "∀F:field_ops(A). ∀lt:(A → A → bool). ∀ρ:(num → A).",
								Hypotheses: []string{
									"«model»(U, K, F, lt, ρ)",
								},
								Conclusion: "K(F, lt, ρ) ∧ " +
									"(∀j:B. j ∈ ∅ ⇒ ordered_sign(F, lt, integer_polynomial_eval(field_ring(F), ρ, q(j))) = &0)",
							},
							BySets())
						b.Show(
							"the table under K with the empty condition at the sign function 0 is one under K",
							By(
								empty,
								split.At(b.TermAs[Fun[B, Int]]("λj:B. &0")),
								SignTableUnderStrongerCondition.At(
									U,
									K,
									b.TermAs[Fun3[FieldOps[A], Fun2[A, A, Bool], Fun[Nat, A], Bool]](
										"λF:field_ops(A). λlt:(A → A → bool). λρ:(num → A). "+
											"    K(F, lt, ρ) ∧ "+
											"    (∀j:B. j ∈ ∅ ⇒ ordered_sign(F, lt, integer_polynomial_eval(field_ring(F), ρ, q(j))) = &0)"),
									m,
									g)))
					})),
				Case(
					"one more index x: split on the sign σ of q(x), and "+
						"under each sign use the induction hypothesis for the rest",
					Derive(func(b *Argument) {
						x := b.FixAs[B]("x")
						J := b.FixAs[Set[B]]("J")
						ih := b.Assume()
						inserted := b.Assume()
						K := b.FixAs[Fun3[FieldOps[A], Fun2[A, A, Bool], Fun[Nat, A], Bool]]("K")
						split := b.Assume()
						xIn := b.Have(
							"q(x) is a parameter polynomial",
							"q(x) ∈ polynomial_algebra(int_ring, U)",
							By(inserted.At(x), set_basic.InInsert.At(J, x, x)))
						rest := b.Have(
							"so is every q(j), j ∈ J",
							"∀j:B. j ∈ J ⇒ q(j) ∈ polynomial_algebra(int_ring, U)",
							By(inserted, set_basic.InInsert))
						branches := b.Have(
							"under K with q(x) of sign σ, for each sign σ, g has a uniform table",
							Statement{
								Binders: "∀σ:int.",
								Hypotheses: []string{
									"σ = -&1 ∨ σ = &0 ∨ σ = &1",
								},
								Conclusion: "parametric_sign_table(U, " +
									"    λF:field_ops(A). λlt:(A → A → bool). λρ:(num → A). " +
									"        K(F, lt, ρ) ∧ ordered_sign(F, lt, integer_polynomial_eval(field_ring(F), ρ, q(x))) = σ, " +
									"    m, " +
									"    g)",
							},
							Derive(func(c *Argument) {
								c.FixAs[Int]("σ")
								c.Assume()
								perSigns := c.Have(
									"every sign function t on J, extended by σ at x, is one on insert(x, J), so it gives a table",
									"∀t:(B → int). "+
										"    parametric_sign_table(U, "+
										"        λF:field_ops(A). λlt:(A → A → bool). λρ:(num → A). "+
										"            K(F, lt, ρ) ∧ "+
										"            ordered_sign(F, lt, integer_polynomial_eval(field_ring(F), ρ, q(x))) = σ ∧ "+
										"            (∀j:B. "+
										"                j ∈ J ⇒ "+
										"                ordered_sign(F, lt, integer_polynomial_eval(field_ring(F), ρ, q(j))) = t(j)), "+
										"        m, "+
										"        g)",
									Derive(func(d *Argument) {
										d.FixAs[Fun[B, Int]]("t")
										extended := d.TermAs[Fun[B, Int]]("λj:B. COND(j = x, σ, t(j))")
										implies := d.Have(
											"in a model meeting K where q(x) has sign σ and each q(j), j ∈ "+
												"J, sign t(j), each q(j), j ∈ insert(x, J), has the extended sign",
											Statement{
												Binders: "∀F:field_ops(A). ∀lt:(A → A → bool). ∀ρ:(num → A).",
												Hypotheses: []string{
													"«model»(U, K, F, lt, ρ)",
													"ordered_sign(F, lt, integer_polynomial_eval(field_ring(F), ρ, q(x))) = σ",
													"∀j:B. j ∈ J ⇒ ordered_sign(F, lt, integer_polynomial_eval(field_ring(F), ρ, q(j))) = t(j)",
												},
												Conclusion: "K(F, lt, ρ) ∧ " +
													"(∀j:B. " +
													"    j ∈ insert(x, J) ⇒ " +
													"    ordered_sign(F, lt, integer_polynomial_eval(field_ring(F), ρ, q(j))) = COND(j = x, σ, t(j)))",
											},
											By(set_basic.InInsert))
										d.Show(
											"the table at the extended sign function is one under the stronger condition",
											By(
												implies,
												split.At(extended),
												SignTableUnderStrongerCondition.At(
													U,
													d.TermAs[Fun3[FieldOps[A], Fun2[A, A, Bool], Fun[Nat, A], Bool]](
														"λF:field_ops(A). λlt:(A → A → bool). λρ:(num → A). "+
															"    K(F, lt, ρ) ∧ "+
															"    ordered_sign(F, lt, integer_polynomial_eval(field_ring(F), ρ, q(x))) = σ ∧ "+
															"    (∀j:B. j ∈ J ⇒ ordered_sign(F, lt, integer_polynomial_eval(field_ring(F), ρ, q(j))) = t(j))"),
													d.TermAs[Fun3[FieldOps[A], Fun2[A, A, Bool], Fun[Nat, A], Bool]](
														"λF:field_ops(A). λlt:(A → A → bool). λρ:(num → A). "+
															"    K(F, lt, ρ) ∧ "+
															"    (∀j:B. "+
															"        j ∈ insert(x, J) ⇒ "+
															"        ordered_sign(F, lt, integer_polynomial_eval(field_ring(F), ρ, q(j))) = "+
															"        COND(j = x, σ, t(j)))"),
													m,
													g)))
									}))
								c.Show(
									"the induction hypothesis for J at the condition K with q(x) of sign σ",
									By(
										ih.At(c.TermAs[Fun3[FieldOps[A], Fun2[A, A, Bool], Fun[Nat, A], Bool]](
											"λF:field_ops(A). λlt:(A → A → bool). λρ:(num → A). "+
												"    K(F, lt, ρ) ∧ ordered_sign(F, lt, integer_polynomial_eval(field_ring(F), ρ, q(x))) = σ")),
										rest,
										perSigns))
							}))
						b.Show(
							"by cases on the sign of q(x)",
							By(xIn, branches, SignTableByCases.At(U, K, q.Apply(x), m, g)))
					}))))
	}),
})}

// DerivativeRemainderStep — the Cohen–Hörmander step: the table of a family
// whose first member p has a fixed degree d > 0 and leading sign τ follows
// from the table of the other members, p′ and the remainders of p by each of
// those. In a model, the cuts where one of h(0), …, h(m) that does not
// specialize to zero vanishes carry a table of those (VanishingCutsTable);
// at such a cut p has the sign of the matching remainder, far out it has the
// signs τ and τ·(−1)^d, and between two such cuts p′ keeps one nonzero sign,
// so MonotoneRefinement splits each interval at one point, the root of p
// there when it has one. The listing of those cuts, its count and the new
// rows are read off N(s) and T(s) alone, so the new rule comes before every
// model. Three devices make that possible:
//   - "h(i) does not specialize to zero" is read as a nonzero sign T(s, 0, i)
//     on cell 0, an open cell, where only the zero polynomial has sign zero;
//   - each of the count(s) + 1 coarse open cells gets one split point, so
//     the new table has 2·count(s) + 1 cuts;
//   - the new rows are «refined» at the coarse rows coarse(s), the cut
//     signs cutSign(s), L = τ·(−1)^d and R = τ.
var DerivativeRemainderStep = derivativeRemainderStepThm{family.Add(registry.ProofEntry{
	Name: "DerivativeRemainderStep",
	Key:  "prop_3e0667e7fbca4f1e",
	Build: family.Theorem(Statement{
		Binders: "∀U:set(num). " +
			"∀C:(field_ops(A) → (A → A → bool) → (num → A) → bool). " +
			"∀m d:num. " +
			"∀τ:int. " +
			"∀g h:(num → num → ((num → num) → int)).",
		Hypotheses: []string{
			"∀i:num. i < suc(m) ⇒ «overParameters»(g(i))",
			"∀i:num. i < m ⇒ h(i) = g(suc(i))",
			"0 < d",
			"∀F:field_ops(A). ∀lt:(A → A → bool). ∀ρ:(num → A). " +
				"    «model»(U, C, F, lt, ρ) ⇒ " +
				"    polynomial_degree(F.zero, «specialized»(field_ring(F), ρ, g(0))) = d ∧ " +
				"    ordered_sign(F, lt, integer_polynomial_eval(field_ring(F), ρ, g(0, d))) = τ",
			"∀F:field_ops(A). ∀lt:(A → A → bool). ∀ρ:(num → A). " +
				"    «model»(U, C, F, lt, ρ) ⇒ " +
				"    «specialized»(field_ring(F), ρ, h(m)) = " +
				"    polynomial_derivative(F.add, F.zero, F.mul, F.one, «specialized»(field_ring(F), ρ, g(0)))",
			"∀F:field_ops(A). ∀lt:(A → A → bool). ∀ρ:(num → A). ∀i:num. ∀x:A. " +
				"    «model»(U, C, F, lt, ρ) ∧ " +
				"    i < suc(m) ∧ " +
				"    «specialized»(field_ring(F), ρ, h(i)) ≠ vec_zero(F.zero) ∧ " +
				"    x ∈ F.carrier ∧ " +
				"    «value»(F, ρ, h(i), x) = F.zero ⇒ " +
				"    ordered_sign(F, lt, «value»(F, ρ, h(suc(m) + i), x)) = " +
				"    ordered_sign(F, lt, «value»(F, ρ, g(0), x))",
			"parametric_sign_table(U, C, suc(m) + suc(m), h)",
		},
		Conclusion: "parametric_sign_table(U, C, suc(m), g)",
	}, func(
		a *Argument,
		U *Expr[Set[Nat]],
		C *Expr[Fun3[FieldOps[A], Fun2[A, A, Bool], Fun[Nat, A], Bool]],
		m, d *Expr[Nat],
		τ *Expr[Int],
		g, h *Expr[Fun3[Nat, Nat, Fun[Nat, Nat], Int]],
		parameters, shifted, positive, leading, derivative, remainders, table Fact,
	) {
		E, _, _, rule := a.Unpack3As[list.List[IntegerPolynomial], Fun[list.List[Int], Nat], Fun3[list.List[Int], Nat, Nat, Int]](
			a.Unfolded(table, ParametricSignTableDef),
			"E",
			"N",
			"T")
		given := a.Conjuncts(
			rule,
			"E lists parameter polynomials",
			"in every model meeting C, the signs s of E give h a table with N(s) cuts and rows T(s)")
		listed, tables := given[0], given[1]
		// count(s) and index(s): how many cuts of h's table are «vanishing»,
		// and their listing in increasing order.
		_, countDef := a.LetAs[Fun[list.List[Int], Nat]](
			"count",
			"λs:list(int). εq:num. ∃e:(num → num). "+
				"    (∀a b:num. a < b ∧ b < q ⇒ e(a) < e(b)) ∧ "+
				"    (∀a:num. a < q ⇒ «vanishing»(suc(m), N(s), T(s), e(a))) ∧ "+
				"    (∀l:num. «vanishing»(suc(m), N(s), T(s), l) ⇒ ∃a:num. a < q ∧ e(a) = l)")
		_, indexDef := a.LetAs[Fun2[list.List[Int], Nat, Nat]](
			"index",
			"λs:list(int). εe:(num → num). "+
				"    (∀a b:num. a < b ∧ b < count(s) ⇒ e(a) < e(b)) ∧ "+
				"    (∀a:num. a < count(s) ⇒ «vanishing»(suc(m), N(s), T(s), e(a))) ∧ "+
				"    (∀l:num. «vanishing»(suc(m), N(s), T(s), l) ⇒ ∃a:num. a < count(s) ∧ e(a) = l)")
		_, coarseDef := a.LetAs[Fun3[list.List[Int], Nat, Nat, Int]](
			"coarse",
			"λs:list(int). «coarse»(T(s), index(s))")
		// cutSign(s, a): the sign of p at the a-th listed cut, that of its
		// remainder h(suc(m) + i) by a member h(i) chosen to vanish there.
		_, cutSignDef := a.LetAs[Fun2[list.List[Int], Nat, Int]](
			"cutSign",
			"λs:list(int). λa:num. "+
				"    T(s, "+
				"        2 * index(s, a) + 1, "+
				"        suc(m) + (εi:num. i < suc(m) ∧ ¬(T(s, 0, i) = &0) ∧ T(s, 2 * index(s, a) + 1, i) = &0))")
		rows, rowsDef := a.LetAs[Fun3[list.List[Int], Nat, Nat, Int]](
			"rows",
			"λs:list(int). «refined»(count(s), coarse(s), cutSign(s), τ * (-&1) ^ d, τ)")
		perModel := a.Have(
			"in every model meeting C, the vanishing cuts of h(0), …, h(m) "+
				"and the roots of p between them give g the table of count and rows",
			Statement{
				Binders: "∀F:field_ops(A). ∀lt:(A → A → bool). ∀ρ:(num → A).",
				Hypotheses: []string{
					"«model»(U, C, F, lt, ρ)",
				},
				Conclusion: "∃r:(num → A). " +
					"    polynomial_family_sign_table(F, " +
					"        lt, " +
					"        suc(m), " +
					"        λi:num. «specialized»(field_ring(F), ρ, g(i)), " +
					"        2 * count(polynomial_signs(F, lt, ρ, E)) + 1, " +
					"        r, " +
					"        rows(polynomial_signs(F, lt, ρ, E)))",
			},
			Derive(func(b *Argument) {
				F := b.FixAs[FieldOps[A]]("F")
				lt := b.FixAs[Fun2[A, A, Bool]]("lt")
				ρ := b.FixAs[Fun[Nat, A]]("ρ")
				model := b.Assume()
				opened := b.Conjuncts(
					GroupPremises(model, ModelSpecialization.At(U, C, F, lt, ρ)),
					"F is a field",
					"F with lt is an ordered field",
					"ρ gives carrier points to the parameters",
					"specialization at ρ is a ring homomorphism",
					"that keeps zero")
				fieldOn, ordered, environment := opened[0], opened[1], opened[2]
				ring := field.RingOn.Read(fieldOn)
				signValues := ordered_field.SignValues.Read(ordered).AsFact()
				r, hTable := b.UnpackAs[Fun[Nat, A]](GroupPremises(model, tables.At(F, lt, ρ)), "r")
				hParts := b.Conjuncts(
					b.Unfolded(hTable, polynomial_sign_table.PolynomialFamilySignTableDef),
					"h's cuts increase in the carrier",
					"every cell of h's table is nonempty",
					"each member of h keeps the sign T(s, j, i) on cell j")
				hNonempty, hRows := hParts[1], hParts[2]
				hCutsIn := b.Conjuncts(
					b.Unfolded(hParts[0], ordered_field.IncreasingCutsDef),
					"h's cuts lie in the carrier",
					"h's cuts increase")[0]
				b.LetAs[list.List[Int]]("s", "polynomial_signs(F, lt, ρ, E)")
				p := b.TermAs[Fun[Nat, A]]("«specialized»(field_ring(F), ρ, g(0))")
				hs := b.TermAs[Fun2[Nat, Nat, A]]("λi:num. «specialized»(field_ring(F), ρ, h(i))")
				gs := b.TermAs[Fun2[Nat, Nat, A]]("λi:num. «specialized»(field_ring(F), ρ, g(i))")
				firstIndex := b.Have(
					"0 indexes a member of g",
					"0 < suc(m)",
					ByArith())
				pOver := b.Have(
					"p, the specialization of g(0), is a polynomial over F",
					"polynomial_over(F.carrier, «specialized»(field_ring(F), ρ, g(0)))",
					By(
						polynomial_formula.SpecializedPolynomial.Read(ring).At(
							U, ρ, b.TermAs[Fun2[Nat, Fun[Nat, Nat], Int]]("g(0)")),
						environment,
						parameters.At(b.TermAs[Nat]("0")),
						firstIndex))
				shape := b.Conjuncts(
					GroupPremises(model, leading.At(F, lt, ρ)),
					"p has degree d",
					"its leading coefficient has the sign τ")
				slope := b.Have(
					"h(m) specializes to p′",
					"«specialized»(field_ring(F), ρ, h(m)) = "+
						"polynomial_derivative(«specialized»(field_ring(F), ρ, g(0)))",
					By(GroupPremises(model, derivative.At(F, lt, ρ))))
				bound := b.TermAs[Nat]("N(s)")
				rowSigns := b.TermAs[Fun2[Nat, Nat, Int]]("T(s)")
				enumeration := b.Have(
					"the vanishing cut indices have an increasing listing",
					"∃q:num. ∃e:(num → num). "+
						"    (∀a b:num. a < b ∧ b < q ⇒ e(a) < e(b)) ∧ "+
						"    (∀a:num. a < q ⇒ «vanishing»(suc(m), N(s), T(s), e(a))) ∧ "+
						"    (∀l:num. «vanishing»(suc(m), N(s), T(s), l) ⇒ ∃a:num. a < q ∧ e(a) = l)",
					By(
						nat_order.BoundedIndexEnumeration.At(bound, b.TermAs[Set[Nat]]("«vanishing»(suc(m), N(s), T(s))"))))
				_, countChosen := b.ObtainChosen(
					"count(s) is the chosen length of such a listing",
					"∃q:num. ∃e:(num → num). "+
						"    (∀a b:num. a < b ∧ b < q ⇒ e(a) < e(b)) ∧ "+
						"    (∀a:num. a < q ⇒ «vanishing»(suc(m), N(s), T(s), e(a))) ∧ "+
						"    (∀l:num. «vanishing»(suc(m), N(s), T(s), l) ⇒ ∃a:num. a < q ∧ e(a) = l)",
					enumeration)
				countListed := b.Have(
					"so a listing of length count(s) exists",
					"∃e:(num → num). "+
						"    (∀a b:num. a < b ∧ b < count(s) ⇒ e(a) < e(b)) ∧ "+
						"    (∀a:num. a < count(s) ⇒ «vanishing»(suc(m), N(s), T(s), e(a))) ∧ "+
						"    (∀l:num. «vanishing»(suc(m), N(s), T(s), l) ⇒ ∃a:num. a < count(s) ∧ e(a) = l)",
					By(countChosen, countDef))
				_, indexChosen := b.ObtainChosen(
					"index(s) is the chosen listing of that length",
					"∃e:(num → num). "+
						"    (∀a b:num. a < b ∧ b < count(s) ⇒ e(a) < e(b)) ∧ "+
						"    (∀a:num. a < count(s) ⇒ «vanishing»(suc(m), N(s), T(s), e(a))) ∧ "+
						"    (∀l:num. «vanishing»(suc(m), N(s), T(s), l) ⇒ ∃a:num. a < count(s) ∧ e(a) = l)",
					countListed)
				listing := b.Conjuncts(
					b.Have(
						"so index(s) lists the vanishing cut indices in increasing order",
						"(∀a b:num. a < b ∧ b < count(s) ⇒ index(s, a) < index(s, b)) ∧ "+
							"(∀a:num. a < count(s) ⇒ «vanishing»(suc(m), N(s), T(s), index(s, a))) ∧ "+
							"(∀l:num. «vanishing»(suc(m), N(s), T(s), l) ⇒ ∃a:num. a < count(s) ∧ index(s, a) = l)",
						indexDef.Rw(),
						By(indexChosen)),
					"index(s) increases",
					"it lists vanishing cut indices",
					"it lists all of them")
				hOver := b.Have(
					"h(0), …, h(m) specialize to polynomials over F",
					"∀i:num. i < suc(m) ⇒ polynomial_over(F.carrier, «specialized»(field_ring(F), ρ, h(i)))",
					Derive(func(c *Argument) {
						i := c.FixAs[Nat]("i")
						iLt := c.Assume()
						c.Cases(c.TermAs[Bool]("i < m"))
						c.When(
							"h(i) is g(i + 1), a polynomial over the parameters",
							func(e *Argument, early Fact) {
								next := e.TermAs[Nat]("suc(i)")
								e.Show(
									"its specialization is a polynomial over F",
									By(
										Normalized,
										shifted.At(i),
										early,
										polynomial_formula.SpecializedPolynomial.Read(ring).At(
											U, ρ, e.TermAs[Fun2[Nat, Fun[Nat, Nat], Int]]("g(suc(i))")),
										environment,
										parameters.At(next),
										e.Have(
											"i + 1 indexes a member of g",
											"suc(i) < suc(m)",
											ByArith(early))))
							})
						c.Otherwise(
							"h(m) specializes to p′, a polynomial over F",
							func(e *Argument, last Fact) {
								e.Show(
									"the derivative of a polynomial over F",
									By(
										slope,
										e.Have(
											"i is m",
											"i = m",
											ByArith(iLt, last)),
										pOver,
										polynomial.DerivativeOverCarrier.Read(ring).At(p)))
							})
					}))
				coarseTable := b.Have(
					"the listed cuts carry a table of h(0), …, h(m) with rows coarse(s)",
					"polynomial_family_sign_table(F, "+
						"    lt, "+
						"    suc(m), "+
						"    λi:num. «specialized»(field_ring(F), ρ, h(i)), "+
						"    count(s), "+
						"    λa:num. r(index(s, a)), "+
						"    coarse(s))",
					Simp(Fwd(coarseDef)),
					By(
						VanishingCutsTable.At(
							F,
							lt,
							b.TermAs[Nat]("suc(m) + suc(m)"),
							b.TermAs[Nat]("suc(m)"),
							hs,
							bound,
							r,
							rowSigns,
							b.TermAs[Nat]("count(s)"),
							b.TermAs[Fun[Nat, Nat]]("index(s)")),
						model,
						hTable,
						b.Have(
							"suc(m) ≤ suc(m) + suc(m)",
							"suc(m) ≤ suc(m) + suc(m)",
							ByArith()),
						hOver,
						listing[0],
						listing[1],
						listing[2]))
				zero := b.TermAs[A]("F.zero")
				carrier := b.TermAs[Set[A]]("F.carrier")
				pNonzero := b.Have(
					"p is not the zero polynomial, its degree d being positive",
					"«specialized»(field_ring(F), ρ, g(0)) ≠ vec_zero(F.zero)",
					Derive(func(c *Argument) {
						flat := c.Have(
							"suppose p were zero",
							"«specialized»(field_ring(F), ρ, g(0)) = vec_zero(F.zero)",
							By(c.SupposeNot()))
						degreeZero := c.Have(
							"then its degree would be 0",
							"polynomial_degree(F.zero, «specialized»(field_ring(F), ρ, g(0))) = 0",
							flat.Rw(),
							By(polynomial.DegreeVecZero.At(zero)))
						c.Show(
							"while it is d > 0",
							ByArith(degreeZero, shape[0], positive))
					}))
				leadIn := b.Have(
					"the leading coefficient p(d) lies in F and is not zero",
					"integer_polynomial_eval(field_ring(F), ρ, g(0, d)) ∈ F.carrier ∧ "+
						"¬(integer_polynomial_eval(field_ring(F), ρ, g(0, d)) = F.zero)",
					By(polynomial.LeadingCoefficientNonzero.At(zero, carrier, p), pOver, pNonzero, shape[0]))
				slopeNonzero := b.Have(
					"p′ is not the zero polynomial: its coefficient at d − 1 is "+
						"d·1 times p(d), and an ordered field has characteristic zero",
					"polynomial_derivative(«specialized»(field_ring(F), ρ, g(0))) ≠ vec_zero(F.zero)",
					Derive(func(c *Argument) {
						flat := c.Have(
							"suppose p′ were zero",
							"polynomial_derivative(«specialized»(field_ring(F), ρ, g(0))) = vec_zero(F.zero)",
							By(c.SupposeNot()))
						numeral := c.TermAs[A]("monoid_pow(F.add, F.zero, F.one, d)")
						positiveNumeral := c.Have(
							"d·1 is positive",
							"lt(F.zero, monoid_pow(F.add, F.zero, F.one, d))",
							By(ordered_field.MultipleOfOnePositive.At(F, lt, d), ordered, positive))
						numeralIn := c.Have(
							"d·1 lies in F and is not zero",
							"monoid_pow(F.add, F.zero, F.one, d) ∈ F.carrier ∧ ¬(monoid_pow(F.add, F.zero, F.one, d) = F.zero)",
							By(
								positiveNumeral,
								ordered_field.Irreflexive.Read(ordered).AsFact().At(zero),
								comm_ring.ZeroIn.Read(ring),
								comm_ring.OneIn.Read(ring),
								comm_monoid.PowIn.Read(comm_ring.AddMonoidOn.Read(ring)).AsFact().At(c.TermAs[A]("F.one"), d)))
						previous := c.TermAs[Nat]("d - 1")
						coefficient := c.Have(
							"the coefficient of p′ at d − 1 is (d·1)·p(d), and p′ = 0 has none there",
							"monoid_pow(F.add, F.zero, F.one, d) * integer_polynomial_eval(field_ring(F), ρ, g(0, d)) = F.zero",
							By(
								flat,
								polynomial.PolynomialDerivativeDef.At(
									c.TermAs[Op[A]]("F.add"), zero, c.TermAs[Op[A]]("F.mul"), c.TermAs[A]("F.one"), p, previous),
								c.Have(
									"suc(d − 1) = d",
									"suc(d - 1) = d",
									ByArith(positive)),
								vec_space.VecZeroDef.At(zero, previous)))
						domain := integral_domain.FieldIntegralDomain.Read(fieldOn)
						c.Show(
							"a product of nonzero elements of a field is not zero",
							By(
								coefficient,
								numeralIn,
								leadIn,
								integral_domain.NoZeroDivisors.Read(domain).AsFact().At(
									numeral, c.TermAs[A]("integer_polynomial_eval(field_ring(F), ρ, g(0, d))"))))
					}))
				arithmetic := b.Have(
					"2 · 0 = 0 and 0 ≤ 2N(s)",
					"2 * 0 = 0 ∧ 0 ≤ N(s) ∧ 0 ≤ 2 * N(s)",
					ByArith())
				w, firstPoint := b.ObtainAs[A](
					"a point w of h's first cell",
					"∃w:A. w ∈ polynomial_sign_cell(F, lt, N(s), r, 0)",
					BySets(hNonempty, arithmetic))
				wIn := b.Have(
					"w lies in the carrier",
					"w ∈ F.carrier",
					By(firstPoint, polynomial_sign_table.SignCellInCarrier.At(F, lt, bound, r, b.TermAs[Nat]("0"), w)))
				cutSigns := b.Have(
					"at the a-th listed cut, p has the sign cutSign(s, a), the "+
						"sign there of the remainder by a member that vanishes there",
					"∀a:num. a < count(s) ⇒ ordered_sign(F, lt, «value»(F, ρ, g(0), r(index(s, a)))) = cutSign(s, a)",
					Derive(func(c *Argument) {
						aIndex := c.FixAs[Nat]("a")
						aLt := c.Assume()
						vanishing := c.Conjuncts(
							GroupPremises(aLt, listing[1].At(aIndex)),
							"index(s, a) is a cut index of h's table",
							"a nonzero one of h(0), …, h(m) vanishes there")
						_, chosen := c.ObtainChosen(
							"the chosen member that vanishes there",
							"∃i:num. i < suc(m) ∧ ¬(T(s, 0, i) = &0) ∧ T(s, 2 * index(s, a) + 1, i) = &0",
							vanishing[1])
						props := c.Conjuncts(
							chosen,
							"it is one of h(0), …, h(m)",
							"its sign on h's first cell is not zero",
							"its sign at the cut is zero")
						chosenIndex, chosenDef := c.LetAs[Nat](
							"k", "εi:num. i < suc(m) ∧ ¬(T(s, 0, i) = &0) ∧ T(s, 2 * index(s, a) + 1, i) = &0")
						cut := c.TermAs[A]("r(index(s, a))")
						cutIndex := c.TermAs[Nat]("2 * index(s, a) + 1")
						cutIn := c.Have(
							"the cut lies in the carrier and in its cut cell",
							"r(index(s, a)) ∈ F.carrier ∧ "+
								"r(index(s, a)) ∈ polynomial_sign_cell(F, lt, N(s), r, 2 * index(s, a) + 1)",
							By(
								hCutsIn.At(c.TermAs[Nat]("index(s, a)")),
								vanishing[0],
								polynomial_sign_table.CutCellMember.At(F, lt, bound, r, c.TermAs[Nat]("index(s, a)"), cut)))
						bounds := c.Have(
							"the cut cell is a cell of h's table, and the chosen member and its remainder are members of h",
							"2 * index(s, a) + 1 ≤ 2 * N(s) ∧ k < suc(m) + suc(m) ∧ suc(m) + k < suc(m) + suc(m)",
							ByArith(vanishing[0], props[0]))
						member := c.TermAs[Fun[Nat, A]]("«specialized»(field_ring(F), ρ, h(k))")
						atCut := c.Have(
							"the chosen member vanishes at the cut",
							"«value»(F, ρ, h(k), r(index(s, a))) = F.zero",
							By(
								hRows.At(cutIndex, chosenIndex, cut),
								cutIn,
								bounds,
								props[2],
								signValues.At(c.TermAs[A]("«value»(F, ρ, h(k), r(index(s, a)))")),
								polynomial_evaluation.EvalIn.Read(ring).AsFact().At(member, cut),
								hOver.At(chosenIndex),
								props[0]))
						nonzeroMember := c.Have(
							"the chosen member does not specialize to zero, its sign on the first cell being nonzero",
							"«specialized»(field_ring(F), ρ, h(k)) ≠ vec_zero(F.zero)",
							Derive(func(e *Argument) {
								flat := e.Have(
									"suppose it did",
									"«specialized»(field_ring(F), ρ, h(k)) = vec_zero(F.zero)",
									By(e.SupposeNot()))
								e.Show(
									"then its sign at w would be zero",
									By(
										hRows.At(e.TermAs[Nat]("0"), chosenIndex, w),
										firstPoint,
										arithmetic,
										bounds,
										props[1],
										flat,
										wIn,
										polynomial_evaluation.EvalVecZero.Read(ring).AsFact().At(w),
										signValues.At(zero),
										comm_ring.ZeroIn.Read(ring)))
							}))
						c.Show(
							"p has the sign of the remainder by the chosen member, which is cutSign(s, a)",
							Simp(Fwd(cutSignDef)),
							By(
								remainders.At(F, lt, ρ, chosenIndex, cut),
								model,
								props[0],
								nonzeroMember,
								cutIn,
								atCut,
								hRows.At(cutIndex, c.TermAs[Nat]("suc(m) + k"), cut),
								bounds,
								chosenDef))
					}))
				ends := b.Conjuncts(
					GroupPremises(ordered, pOver, pNonzero, ordered_field_polynomial.SignsAtBothEnds.At(F, lt, p)),
					"far to the right p has the sign of its leading coefficient",
					"far to the left that sign times (−1)^deg")
				farRight := b.Have(
					"far to the right p has the sign τ",
					"∃b:A. "+
						"    b ∈ F.carrier ∧ "+
						"    (∀x:A. x ∈ F.carrier ∧ lt(b, x) ⇒ ordered_sign(F, lt, «value»(F, ρ, g(0), x)) = τ)",
					By(ends[0], shape[0], shape[1]))
				farLeft := b.Have(
					"far to the left p has the sign τ·(−1)^d",
					"∃b:A. "+
						"    b ∈ F.carrier ∧ "+
						"    (∀x:A. "+
						"        x ∈ F.carrier ∧ lt(x, b) ⇒ ordered_sign(F, lt, «value»(F, ρ, g(0), x)) = τ * (-&1) ^ d)",
					By(ends[1], shape[0], shape[1]))
				laterMembers := b.Have(
					"each later member g(i + 1) specializes as h(i)",
					Statement{
						Binders:    "∀i:num.",
						Hypotheses: []string{"i < m"},
						Conclusion: "«specialized»(field_ring(F), ρ, g(suc(i))) = «specialized»(field_ring(F), ρ, h(i))",
					},
					Derive(func(c *Argument) {
						i := c.FixAs[Nat]("i")
						iLt := c.Assume()
						c.Show(
							"h(i) is g(i + 1)",
							By(Normalized, shifted.At(i), iLt))
					}))
				b.Show(
					"MonotoneRefinement inserts the roots of p into the listed cuts",
					Simp(Fwd(rowsDef)),
					By(
						MonotoneRefinement.At(
							F,
							lt,
							m,
							p,
							hs,
							gs,
							b.TermAs[Nat]("count(s)"),
							b.TermAs[Fun[Nat, A]]("λa:num. r(index(s, a))"),
							b.TermAs[Fun2[Nat, Nat, Int]]("coarse(s)"),
							b.TermAs[Fun[Nat, Int]]("cutSign(s)"),
							b.TermAs[Int]("τ * (-&1) ^ d"),
							τ),
						model,
						pOver,
						coarseTable,
						slope,
						slopeNonzero,
						laterMembers,
						cutSigns,
						farLeft,
						farRight))
			}))
		a.Do(Unfold(ParametricSignTableDef))
		a.Take(E)
		a.Take(a.TermAs[Fun[list.List[Int], Nat]]("λs:list(int). 2 * count(s) + 1"))
		a.Take(rows)
		a.Show(
			"E with the refined count and rows gives g a uniform table",
			By(listed, perModel))
	}),
})}
