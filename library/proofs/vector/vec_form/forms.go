// The degree carriers, their real module structure, and the readings
// in degree zero, top degree and degrees above the dimension.

package vec_form

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/vector/determinant"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var FormLocal = formLocalThm{family.Add(registry.ProofEntry{
	Name: "FormLocal",
	Key:  "prop_2215a8bfdb5aeab0",
	Reading: "Local tests constrain only values in U. The conclusion " +
		"explicitly normalizes the candidate outside U; without that " +
		"normalization arbitrary exterior values would violate FormOnDef.",
	Deps: []registry.EntryLike{
		FormOnDef,
		vec_smooth.SmoothLocal,
		vec_smooth.ContinuouslyDifferentiableCongruence,
	},
	Build: family.Card(Statement{
		Binders: "∀n k:num. ∀U:set(num → real). ∀ω:((num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"U ∈ euclidean_topology(n)",
			"∀x:(num → real). " +
				"    x ∈ U ⇒ " +
				"    ∃V:set(num → real). " +
				"        V ∈ euclidean_topology(n) ∧ " +
				"        x ∈ V ∧ " +
				"        V ⊆ U ∧ " +
				"        vec_form_on⟨n⟩(V, k, normalize_on(V, λP:(num → num → real). &0, ω))",
		},
		Conclusion: "vec_form_on⟨n⟩(U, k, normalize_on(U, λP:(num → num → real). &0, ω))",
	},
		"On each neighbourhood the candidate's increasing-coordinate coefficients agree "+
			"with smooth coefficients of the local normalized form. SmoothLocal glues their "+
			"smoothness, and the minor expansion holds pointwise by the same local formula. "+
			"The outer normalization supplies zero values off U, including when U is empty."),
})}

var FormModule = formModuleThm{family.Add(registry.ProofEntry{
	Name: "FormModule",
	Key:  "prop_69469aa674193642",
	Deps: []registry.EntryLike{
		FormModuleDef,
		function_module.FunctionModuleDef,
		vec_smooth.SmoothConst,
		vec_smooth.SmoothAdd,
		vec_smooth.SmoothMul,
	},
	Build: family.Card(Statement{
		Binders:    "∀n k:num. ∀U:set(num → real).",
		Hypotheses: []string{"U ∈ euclidean_topology(n)"},
		Conclusion: "module_on(real_ring, vec_form_module⟨n⟩(U, k))",
	},
		"The coefficient expansion and zero normalization are preserved by pointwise addition "+
			"and scalar multiplication; SmoothConst, SmoothAdd and SmoothMul preserve the "+
			"coefficient conditions. Thus the form carrier is a submodule of the iterated function "+
			"module, with the same zero, addition, negation and scalar action in every degree."),
})}

// FormZeroDegree — a zero-form is its smooth scalar coefficient on the
// open set, with the same value on every frame and zero off the set.
var FormZeroDegree = formZeroDegreeThm{family.Add(registry.ProofEntry{
	Name: "FormZeroDegree",
	Key:  "prop_86ffc03e6e4991c4",
	Reading: "A degree-zero form is independent of every matrix argument. The coefficient " +
		"is smooth only on U; zero extension is not asserted smooth across the boundary of U.",
	Build: family.Sections(Statement{
		Binders:    "∀n:num. ∀U:set(num → real). ∀ω:((num → real) → (num → num → real) → real).",
		Hypotheses: []string{"U ∈ euclidean_topology(n)"},
		Conclusion: "vec_form_on⟨n⟩(U, 0, ω) ⇔ " +
			"vec_smooth_on⟨n⟩(U, λx:(num → real). ω(x, «empty frame»)) ∧ " +
			"ω = (λx:(num → real). λP:(num → num → real). COND(x ∈ U, ω(x, «empty frame»), &0))",
	}, func(ctx *Script, headline string) *GoalStackNode {
		singleIndex := ctx.Lemma("∀n:num. vec_form_indices(n, 0) = {λj:num. 0}",
			func(a *Argument, n *Expr[Nat]) {
				a.Show(
					"at degree zero the tail condition makes every index entry zero",
					Simp(Fwd(FormIndicesDef), Fwd(nat_order.LessThanZeroClause), Fwd(nat_order.ZeroLessEq)),
					BySets())
			})
		emptyBasis := ctx.Lemma(
			"∀n:num. ∀a:(num → num). vec_form_basis⟨n, 0⟩(a) = «empty frame»",
			func(arg *Argument, n *Expr[Nat], a *Arrow[Nat, Nat]) {
				arg.Show(
					"every column of the frame lies outside the active block",
					Funext(),
					Simp(Fwd(formBasisDef), Fwd(nat_order.LessThanZeroClause)),
					Basic())
			})
		emptyMinor := ctx.Lemma(
			"∀P:(num → num → real). ∀a:(num → num). "+
				"    (λi:num. λj:num. COND(i < 0 ∧ j < 0, P(a(i), j), &0)) = «empty frame»",
			func(arg *Argument, P *Arrow2[Nat, Nat, Real], a *Arrow[Nat, Nat]) {
				arg.Show(
					"no entry lies in the active block of a zero minor",
					Funext(),
					Simp(Fwd(nat_order.LessThanZeroClause)),
					Basic())
			})
		emptyDeterminant := ctx.Lemma("determinant(real_ring, 0, «empty frame») = &1",
			func(a *Argument) {
				identity := a.Have(
					"every entry of the identity in dimension zero is outside its active block",
					"matrix_identity(real_ring, 0) = «empty frame»",
					Funext(),
					Simp(
						Fwd(determinant.MatrixIdentityDef),
						Fwd(nat_order.LessThanZeroClause),
						Fwd(real_ring.RealRingDef)),
					Basic())
				a.Show(
					"the empty frame has determinant one",
					identity.RwRev(),
					Simp(Fwd(determinant.DeterminantIdentity.Read(real_ring.CommRingOn))),
					Refl())
			})
		expansion := ctx.Lemma(
			"∀n:num. ∀ω:((num → real) → (num → num → real) → real). ∀x:(num → real). ∀P:(num → num → real). "+
				"    module_sum(real_ring.add, "+
				"        &0, "+
				"        vec_form_indices(n, 0), "+
				"        λa:(num → num). "+
				"            ω(x, vec_form_basis⟨n, 0⟩(a)) * "+
				"            determinant(real_ring, 0, λi:num. λj:num. COND(i < 0 ∧ j < 0, P(a(i), j), &0))) = "+
				"    ω(x, «empty frame»)",
			func(a *Argument, n *Expr[Nat], ω *Arrow2[Fun[Nat, Real], Fun2[Nat, Nat, Real], Real],
				x *Arrow[Nat, Real], P *Arrow2[Nat, Nat, Real]) {
				addition := comm_ring.AddMonoidOn.Read(real_ring.CommRingOn)
				a.Show(
					"the single term is the coefficient times the empty minor's unit determinant",
					Simp(Fwd(singleIndex), Fwd(emptyBasis), Fwd(emptyMinor)),
					Simp(Fwd(emptyDeterminant), Fwd(real_ring.MulRightId)),
					BySets(module.ModuleSumSingleMonoid.Read(addition).At(
						a.TermAs[Set[Fun[Nat, Nat]]]("{λj:num. 0}"),
						a.TermAs[Fun[Nat, Nat]]("λj:num. 0"),
						a.TermAs[Fun[Fun[Nat, Nat], Real]]("λa:(num → num). ω(x, «empty frame»)"))))
			})
		return ctx.Theorem(headline,
			func(a *Argument, n *Expr[Nat], U *Expr[Set[Fun[Nat, Real]]],
				ω *Arrow2[Fun[Nat, Real], Fun2[Nat, Nat, Real], Real], open Fact) {
				a.Do(Unfold(FormOnDef))
				a.Iff()
				a.Forward(
					"the coordinate expansion reads one smooth coefficient",
					func(b *Argument, form Fact) {
						b.Show(
							"smoothness and normalized evaluation",
							SplitConj(
								Case(
									"the coefficient at the sole index is smooth",
									Derive(func(c *Argument) {
										inIndex := c.Have(
											"the zero sequence is the degree-zero index",
											"(λj:num. 0) ∈ vec_form_indices(n, 0)",
											BySets(At(singleIndex, n)))
										zeroIndex := c.TermAs[Fun[Nat, Nat]]("λj:num. 0")
										c.Show(
											"its basis is the empty frame",
											By(inIndex, form, At(emptyBasis, n, zeroIndex)))
									})),
								Case(
									"the form's value is the normalized scalar coefficient",
									Funext(),
									Derive(func(c *Argument) {
										x := c.FixAs[Fun[Nat, Real]]()
										P := c.FixAs[Fun2[Nat, Nat, Real]]()
										c.Show(
											"collapse the degree-zero expansion",
											By(form, At(expansion, n, ω, x, P)))
									}))))
					})
				a.Backward(
					"the smooth normalized coefficient satisfies the form conditions",
					func(b *Argument, scalar Fact) {
						parts := b.Conjuncts(
							scalar,
							"the scalar coefficient is smooth",
							"the form has normalized values")
						b.Show(
							"the domain, coefficients and expansion satisfy the definition",
							SplitConjAll(
								Case(
									"the domain is open",
									By(open)),
								Case(
									"each basis coefficient is the given smooth function",
									Derive(func(c *Argument) {
										index := c.FixAs[Fun[Nat, Nat]]()
										c.Show(
											"degree-zero bases are empty",
											By(Normalized, parts[0], At(emptyBasis, n, index)))
									})),
								Case(
									"the normalized value agrees with the coordinate expansion",
									Derive(func(c *Argument) {
										x := c.FixAs[Fun[Nat, Real]]()
										P := c.FixAs[Fun2[Nat, Nat, Real]]()
										c.Show(
											"the single term recovers the coefficient",
											By(parts[1], At(expansion, n, ω, x, P)))
									}))))
					})
			})
	}),
})}

var FormAboveDimension = formAboveDimensionThm{family.Add(registry.ProofEntry{
	Name: "FormAboveDimension",
	Key:  "prop_5d9061fb368aaaad",
	Deps: []registry.EntryLike{FormOnDef, FormIndicesDef},
	Build: family.Card(Statement{
		Binders:    "∀n k:num. ∀U:set(num → real). ∀ω:((num → real) → (num → num → real) → real).",
		Hypotheses: []string{"vec_form_on⟨n⟩(U, k, ω)", "n < k"},
		Conclusion: "ω = «zero»",
	},
		"An increasing list of k indices below n cannot exist when n < k. The coordinate expansion is an "+
			"empty sum on U and the defining normalization is zero off U, giving equality as total functions."),
})}

var TopDegreeDeterminant = topDegreeDeterminantThm{family.Add(registry.ProofEntry{
	Name: "TopDegreeDeterminant",
	Key:  "prop_3826a24d833144c9",
	Reading: "P may have arbitrary entries outside its n×n block; the determinant and " +
		"the form both ignore them. The equation also holds off U and in dimension zero.",
	Deps: []registry.EntryLike{FormOnDef, FormIndicesDef, determinant.DeterminantDef},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀U:set(num → real). " +
			"∀ω:((num → real) → (num → num → real) → real). " +
			"∀x:(num → real). " +
			"∀P:(num → num → real).",
		Hypotheses: []string{"vec_form_on⟨n⟩(U, n, ω)"},
		Conclusion: "ω(x, P) = ω(x, matrix_identity(real_ring, n)) * determinant(real_ring, n, P)",
	},
		"The only increasing n-list below n is the identity list with a zero tail. Its "+
			"frame is the identity matrix and its minor is P's active block; FormOnDef "+
			"therefore has one term, while off U its coefficient and the form both vanish."),
})}

var FormRestrict = formRestrictThm{family.Add(registry.ProofEntry{
	Name: "FormRestrict",
	Key:  "prop_a62caec7aec75534",
	Deps: []registry.EntryLike{FormOnDef, vec_smooth.SmoothSubset, vec_smooth.SmoothLocal},
	Build: family.Card(Statement{
		Binders:    "∀n k:num. ∀U V:set(num → real). ∀ω:((num → real) → (num → num → real) → real).",
		Hypotheses: []string{"vec_form_on⟨n⟩(U, k, ω)", "V ∈ euclidean_topology(n)", "V ⊆ U"},
		Conclusion: "vec_form_on⟨n⟩(V, k, normalize_on(V, λP:(num → num → real). &0, ω))",
	},
		"On V the coefficients agree locally with those of ω, so SmoothSubset "+
			"and SmoothLocal retain smoothness. The same coordinate expansion "+
			"holds on V, and normalize_on makes every value outside V zero."),
})}
