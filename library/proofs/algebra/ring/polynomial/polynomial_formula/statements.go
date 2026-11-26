// statements.go — integer polynomials and the formulas over them: a valid polynomial, its
// variables and its value in a ring along the integer map, the ring of integer polynomials, and
// the formulas whose atoms are valid polynomials, their free variables and their sentences; the
// atoms of a quantifier-free formula listed, and the finitely many variables of a polynomial and
// of a formula; a polynomial as a member of the polynomial algebra on its variables; evaluation in
// the carrier, depending only on the variables, natural in ring homomorphisms and a ring
// homomorphism on the polynomials on U; and the variable, zero, one, negation and difference
// polynomials and their values.

package polynomial_formula

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/characteristic_zero"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/datatypes/first_order"
	"github.com/euc-ai/xugo/library/proofs/datatypes/list"
	_ "github.com/euc-ai/xugo/library/proofs/int_num/int_construction"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_real_lift"
	_ "github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// IntegerPolynomialDef — valid atomic polynomials have finite coefficient and monomial support.
var IntegerPolynomialDef = integerPolynomialDefThm{family.Define(registry.DefEntry{
	Name: "IntegerPolynomialDef", Const: "integer_polynomial", Type: "((num → num) → int) → bool",
	Key: "prop_9f3651d782bdf38e",
	Equations: []string{
		"∀p:((num → num) → int). integer_polynomial(p) ⇔ p ∈ polynomial_algebra(int_ring, 𝕌)",
	},
})}

// PolynomialVarsDef — the variables appearing in a nonzero coefficient monomial.
var PolynomialVarsDef = polynomialVarsDefThm{family.Define(registry.DefEntry{
	Name: "PolynomialVarsDef", Const: "integer_polynomial_vars", Type: "((num → num) → int) → set(num)",
	Key: "prop_9501d728c2b1d2b",
	Equations: []string{
		"∀p:((num → num) → int). " +
			"    integer_polynomial_vars(p) = {v:num | ∃m:(num → num). p(m) ≠ 0 ∧ m(v) ≠ 0}",
	},
})}

// IntegerPolynomialEvalDef — evaluate integer coefficients through their canonical ring map.
var IntegerPolynomialEvalDef = integerPolynomialEvalDefThm{family.Define(registry.DefEntry{
	Name:  "IntegerPolynomialEvalDef",
	Const: "integer_polynomial_eval",
	Type:  "ring_ops(A) → (num → A) → ((num → num) → int) → A",
	Key:   "prop_a0521d1ab7f7c893",
	Equations: []string{
		"∀R:ring_ops(A). ∀ρ:(num → A). ∀p:((num → num) → int). " +
			"    integer_polynomial_eval(R, ρ, p) = polynomial_algebra_eval(int_ring, R, integer_map(R), ρ, p)",
	},
})}

// IntegerPolynomialRingDef — the polynomial algebra over the integers on all natural-number
// variable names.
var IntegerPolynomialRingDef = integerPolynomialRingDefThm{family.Define(registry.DefEntry{
	Name:      "IntegerPolynomialRingDef",
	Const:     "integer_polynomial_ring",
	Type:      "ring_ops((num → num) → int)",
	Key:       "prop_7c208138e065d18",
	Equations: []string{"integer_polynomial_ring = polynomial_algebra_ring(int_ring, 𝕌)"},
})}

// FormulaValidDef — a polynomial formula has valid polynomial atoms.
var FormulaValidDef = formulaValidDefThm{family.Define(registry.DefEntry{
	Name:  "FormulaValidDef",
	Const: "polynomial_formula_wf",
	Type:  "fo_formula((num → num) → int) → bool",
	Key:   "prop_edcf509a3b8e89be",
	Equations: []string{
		"∀φ:fo_formula((num → num) → int). polynomial_formula_wf(φ) ⇔ fo_wf(integer_polynomial, φ)",
	},
	Deps: []registry.EntryLike{IntegerPolynomialDef},
})}

// FormulaVarsDef — free variables of a polynomial formula.
var FormulaVarsDef = formulaVarsDefThm{family.Define(registry.DefEntry{
	Name:  "FormulaVarsDef",
	Const: "polynomial_formula_fv",
	Type:  "fo_formula((num → num) → int) → set(num)",
	Key:   "prop_ad0c22a0d8d9d958",
	Equations: []string{
		"∀φ:fo_formula((num → num) → int). polynomial_formula_fv(φ) = fo_fv(integer_polynomial_vars, φ)",
	},
	Deps: []registry.EntryLike{PolynomialVarsDef},
})}

// FormulaClosedDef — a sentence is well formed and has empty free-variable support.
var FormulaClosedDef = formulaClosedDefThm{family.Define(registry.DefEntry{
	Name:  "FormulaClosedDef",
	Const: "polynomial_formula_closed",
	Type:  "fo_formula((num → num) → int) → bool",
	Key:   "prop_54eefa268df43b5e",
	Equations: []string{
		"∀φ:fo_formula((num → num) → int). " +
			"    polynomial_formula_closed(φ) ⇔ polynomial_formula_wf(φ) ∧ polynomial_formula_fv(φ) = ∅",
	},
	Deps: []registry.EntryLike{FormulaValidDef, FormulaVarsDef},
})}

// PolynomialListOverDef — a finite polynomial list whose variable names lie in U.
var PolynomialListOverDef = polynomialListOverDefThm{family.Define(registry.DefEntry{
	Name:  "PolynomialListOverDef",
	Const: "polynomial_list_over",
	Type:  "set(num) → list((num → num) → int) → bool",
	Key:   "prop_2ed8f449f02b5456",
	Equations: []string{
		"∀U:set(num). ∀P:list((num → num) → int). " +
			"    polynomial_list_over(U, P) ⇔ " +
			"    ∀p:((num → num) → int). " +
			"        list_member(p, P) ⇒ integer_polynomial(p) ∧ integer_polynomial_vars(p) ⊆ U",
	},
	Deps: []registry.EntryLike{IntegerPolynomialDef, PolynomialVarsDef},
})}

// AtomList — the atoms of a valid quantifier-free polynomial formula are listed by a list of valid
// polynomials in its free variables: by induction on the formula, an atom is listed by itself, a
// negation by the list of its body, and a conjunction by the lists of its conjuncts joined.
var AtomList = atomListThm{family.Add(registry.ProofEntry{
	Name: "AtomList",
	Key:  "prop_2d962345990efea6",
	Build: family.Theorem(Statement{
		Binders: "∀φ:fo_formula((num → num) → int).",
		Hypotheses: []string{
			"polynomial_formula_wf(φ)",
			"fo_qf(φ)",
		},
		Conclusion: "∃P:list((num → num) → int). " +
			"    polynomial_list_over(polynomial_formula_fv(φ), P) ∧ " +
			"    fo_wf(λp:((num → num) → int). list_member(p, P), φ)",
		Abbrev: Abbrev{
			{Name: "AtomsListed", Text: "λψ:fo_formula((num → num) → int). ∃Q:list((num → num) → int). " +
				"    polynomial_list_over(fo_fv(integer_polynomial_vars, ψ), Q) ∧ " +
				"    fo_wf(λp:((num → num) → int). list_member(p, Q), ψ)"},
		},
	}, func(a *Argument, φ *Expr[Formula[IntegerPolynomial]], wf, qf Fact) {
		valid := a.Unfolded(wf, FormulaValidDef)
		listed := a.TermAs[Set[Formula[IntegerPolynomial]]](
			"λψ:fo_formula((num → num) → int). fo_wf(integer_polynomial, ψ) ∧ fo_qf(ψ) ⇒ «AtomsListed»(ψ)")
		// Each case reads validity, quantifier-freeness and the free variables at its constructor.
		clauses := Simp(
			Fwd(first_order.WellFormedDef),
			Fwd(first_order.QuantifierFreeDef),
			Fwd(first_order.FreeVarsDef))
		a.Show(
			"every valid quantifier-free formula has its atoms listed, by induction on its shape",
			Simp(Fwd(FormulaVarsDef)),
			ByInduction(first_order.FormulaInduction.At(listed, φ), valid, qf,
				Case(
					"an atom is listed by itself",
					clauses,
					Derive(func(b *Argument) {
						b.FixAs[IntegerPolynomial]("q")
						atom := b.Assume()
						b.Take(b.TermAs[List[IntegerPolynomial]]("cons(q, nil)"))
						over := b.Have(
							"the one-element list holds q alone, a valid polynomial in its own variables",
							"polynomial_list_over(integer_polynomial_vars(q), cons(q, nil))",
							Unfold(PolynomialListOverDef),
							Derive(func(c *Argument) {
								c.FixAs[IntegerPolynomial]("p")
								member := c.Assume()
								c.Show(
									"a member of the one-element list is q",
									By(atom, member, list.ListMemberDef, set_order.SubsetRefl))
							}))
						b.Show(
							"and q is its member",
							Simp(Fwd(list.ListMemberDef)),
							By(over))
					})),
				Case(
					"a negation is listed by the list of its body",
					clauses,
					Basic()),
				Case(
					"a conjunction is listed by the lists of its conjuncts joined",
					clauses,
					Derive(func(b *Argument) {
						ψ := b.FixAs[Formula[IntegerPolynomial]]("ψ")
						χ := b.FixAs[Formula[IntegerPolynomial]]("χ")
						ihψ, ihχ := b.Assume(), b.Assume()
						both := b.Assume()
						_, listedψ := b.Obtain(
							"the induction hypothesis lists the atoms of ψ",
							"«AtomsListed»(ψ)",
							By(ihψ, both),
							Named("Q₁"))
						_, listedχ := b.Obtain(
							"and the atoms of χ",
							"«AtomsListed»(χ)",
							By(ihχ, both),
							Named("Q₂"))
						partsψ := b.Conjuncts(
							listedψ,
							"Q₁ lists valid polynomials in the variables of ψ",
							"Q₁ holds every atom of ψ")
						partsχ := b.Conjuncts(
							listedχ,
							"Q₂ lists valid polynomials in the variables of χ",
							"Q₂ holds every atom of χ")
						overψ := b.Unfolded(partsψ[0], PolynomialListOverDef)
						overχ := b.Unfolded(partsχ[0], PolynomialListOverDef)
						b.Take(b.TermAs[List[IntegerPolynomial]]("list_append(Q₁, Q₂)"))
						over := b.Have(
							"the joined list holds valid polynomials in the variables of ψ or of χ",
							"polynomial_list_over(fo_fv(integer_polynomial_vars, ψ) ∪ fo_fv(integer_polynomial_vars, χ), "+
								"    list_append(Q₁, Q₂))",
							Unfold(PolynomialListOverDef),
							Derive(func(c *Argument) {
								c.FixAs[IntegerPolynomial]("p")
								member := c.Simplified(c.Assume(), Fwd(list.MemberAppend))
								c.Show(
									"a member of the joined list is a member of Q₁ or of Q₂",
									BySets(member, overψ, overχ))
							}))
						joined := b.TermAs[Set[IntegerPolynomial]](
							"λp:((num → num) → int). list_member(p, list_append(Q₁, Q₂))")
						b.Show(
							"and the joined list holds the atoms of each conjunct",
							By(
								over,
								partsψ[1],
								partsχ[1],
								list.MemberAppend,
								first_order.WellFormedMono.At(
									b.TermAs[Set[IntegerPolynomial]]("λp:((num → num) → int). list_member(p, Q₁)"), joined, ψ),
								first_order.WellFormedMono.At(
									b.TermAs[Set[IntegerPolynomial]]("λp:((num → num) → int). list_member(p, Q₂)"), joined, χ)))
					})),
				Case(
					"an existential is not quantifier-free",
					clauses,
					Basic())))
	}),
})}

// PolynomialVarsFinite — a valid polynomial has finitely many variable names:
// a variable of p is a nonzero exponent of a monomial where p is nonzero, so
// the variables lie in the union of the supports of those monomials, a finite
// union of finite sets.
var PolynomialVarsFinite = polynomialVarsFiniteThm{family.Add(registry.ProofEntry{
	Name: "PolynomialVarsFinite",
	Key:  "prop_776f5754b74faeae",
	Build: family.Theorem(Statement{
		Binders: "∀p:((num → num) → int).",
		Hypotheses: []string{
			"integer_polynomial(p)",
		},
		Conclusion: "finite(integer_polynomial_vars(p))",
		Abbrev: Abbrev{
			{Name: "supports", Text: "image(λm:(num → num). fun_support(0, m), fun_support(int_of_num(0), p))"},
		},
	},
		func(a *Argument, p *Arrow[Fun[Nat, Nat], Int], polynomial Fact) {
			support := a.TermAs[Set[Fun[Nat, Nat]]]("fun_support(int_of_num(0), p)")
			exponents := a.TermAs[Fun[Fun[Nat, Nat], Set[Nat]]]("λm:(num → num). fun_support(0, m)")
			supports := a.TermAs[Set[Set[Nat]]]("«supports»")
			parts := a.Conjuncts(
				a.Simplified(
					polynomial,
					Fwd(IntegerPolynomialDef),
					Fwd(polynomial_algebra.PolynomialAlgebraMember)),
				"p is nonzero at finitely many monomials",
				"every monomial where p is nonzero is a monomial on all the variable names",
				"every coefficient of p is an integer")
			finiteExponents := a.Have(
				"a monomial where p is nonzero has finitely many nonzero exponents",
				"∀m:(num → num). m ∈ fun_support(int_of_num(0), p) ⇒ finite(fun_support(0, m))",
				By(parts[1], set_basic.SubsetDef, polynomial_algebra.MonomialsMember))
			finiteUnion := a.Have(
				"so the supports of those monomials have a finite union",
				"finite(⋃«supports»)",
				By(
					finiteExponents,
					parts[0],
					finite_set.FiniteImage.At(exponents, support),
					finite_set.FiniteFiniteUnions.At(supports),
					set_image.ForallInImage.At(
						exponents, support, a.TermAs[Fun[Set[Nat], Bool]]("λt:set(num). finite(t)"))))
			covered := a.Have(
				"which holds every variable of p, a nonzero exponent of a monomial where p is nonzero",
				"integer_polynomial_vars(p) ⊆ ⋃«supports»",
				Unfold(set_basic.SubsetDef),
				Derive(func(b *Argument) {
					w := b.FixAs[Nat]("w")
					m, witness := b.UnpackAs[Fun[Nat, Nat]](b.Unfolded(b.Assume(), PolynomialVarsDef), "m")
					b.Show(
						"the support of that monomial holds w",
						By(
							witness,
							set_basic.InUnions.At(supports, w),
							set_basic.InImage.At(exponents, support, b.TermAs[Set[Nat]]("fun_support(0, m)")),
							functions.InFunSupport.At(b.TermAs[Int]("0"), p, m),
							functions.InFunSupport.At(b.TermAs[Nat]("0"), m, w)))
				}))
			a.Show(
				"a part of a finite set is finite",
				By(
					finiteUnion,
					covered,
					finite_set.FiniteSubset.At(
						a.TermAs[Set[Nat]]("integer_polynomial_vars(p)"),
						a.TermAs[Set[Nat]]("⋃«supports»"))))
		}),
})}

// FormulaVarsFinite — a well-formed polynomial formula has finite free support:
// each of its atoms is a valid polynomial, which has finitely many variables,
// and a formula over atoms of finite support has finite support.
var FormulaVarsFinite = formulaVarsFiniteThm{family.Add(registry.ProofEntry{
	Name: "FormulaVarsFinite",
	Key:  "prop_9f293e666eb1eb85",
	Build: family.Theorem(Statement{
		Binders: "∀φ:fo_formula((num → num) → int).",
		Hypotheses: []string{
			"polynomial_formula_wf(φ)",
		},
		Conclusion: "finite(polynomial_formula_fv(φ))",
	}, func(a *Argument, φ *Expr[Formula[IntegerPolynomial]], wf Fact) {
		a.Do(Simp(Fwd(FormulaVarsDef)))
		a.Show(
			"the first-order support theorem, read at the polynomial atoms",
			By(
				a.Unfolded(wf, FormulaValidDef),
				first_order.FreeVarsFinite.At(
					a.TermAs[Set[IntegerPolynomial]]("integer_polynomial"),
					a.TermAs[Fun2[IntegerPolynomial, Nat, Bool]]("integer_polynomial_vars"),
					φ),
				PolynomialVarsFinite))
	}),
})}

// PolynomialOnOwnVariables — a valid polynomial is a polynomial on its own
// variable names: a monomial with a nonzero coefficient has finitely many
// nonzero exponents, and each sits at a variable of p, since that monomial
// itself witnesses the variable.
var PolynomialOnOwnVariables = polynomialOnOwnVariablesThm{family.Add(registry.ProofEntry{
	Name: "PolynomialOnOwnVariables",
	Key:  "prop_4bfe5ada7d2921d3",
	Build: family.Theorem(Statement{
		Binders: "∀p:((num → num) → int).",
		Hypotheses: []string{
			"integer_polynomial(p)",
		},
		Conclusion: "p ∈ polynomial_algebra(int_ring, integer_polynomial_vars(p))",
	},
		func(a *Argument, p *Arrow[Fun[Nat, Nat], Int], polynomial Fact) {
			parts := a.Conjuncts(
				a.Simplified(
					polynomial,
					Fwd(IntegerPolynomialDef),
					Fwd(polynomial_algebra.PolynomialAlgebraMember)),
				"p is nonzero at finitely many monomials",
				"every monomial where p is nonzero is a monomial on all the variable names",
				"every coefficient of p is an integer")
			finiteExponents := a.Have(
				"a monomial where p is nonzero has finitely many nonzero exponents",
				"∀m:(num → num). m ∈ fun_support(int_of_num(0), p) ⇒ finite(fun_support(0, m))",
				By(parts[1], set_basic.SubsetDef, polynomial_algebra.MonomialsMember))
			variables := a.Have(
				"and its nonzero exponents sit at variables of p",
				Statement{
					Binders:    "∀m:(num → num).",
					Hypotheses: []string{"m ∈ fun_support(int_of_num(0), p)"},
					Conclusion: "fun_support(0, m) ⊆ integer_polynomial_vars(p)",
				},
				Simp(Fwd(PolynomialVarsDef), Fwd(set_basic.SubsetDef), Fwd(functions.InFunSupport)),
				Derive(func(b *Argument) {
					b.FixAs[Fun[Nat, Nat]]("m")
					coefficient := b.Assume()
					b.FixAs[Nat]("v")
					exponent := b.Assume()
					b.Show(
						"the monomial itself witnesses the variable",
						By(coefficient, exponent))
				}))
			support := a.Have(
				"so every monomial where p is nonzero is a monomial of p's own variables",
				"fun_support(int_of_num(0), p) ⊆ monomials(integer_polynomial_vars(p))",
				By(finiteExponents, variables, set_basic.SubsetDef, polynomial_algebra.MonomialsMember))
			a.Show(
				"a finitely supported integer coefficient function "+
					"on those monomials is a polynomial on p's variables",
				By(parts[0], parts[2], support, polynomial_algebra.PolynomialAlgebraMember))
		}),
})}

// PolynomialSupportFinite — a valid polynomial is nonzero at finitely many
// monomials, each a monomial of its own variables: it is a polynomial on its
// own variables, a finitely supported coefficient function on their
// monomials.
var PolynomialSupportFinite = polynomialSupportFiniteThm{family.Add(registry.ProofEntry{
	Name: "PolynomialSupportFinite",
	Key:  "prop_31efe7f230cf817d",
	Build: family.Theorem(Statement{
		Binders: "∀p:((num → num) → int).",
		Hypotheses: []string{
			"integer_polynomial(p)",
		},
		Conclusion: "finite(fun_support(int_of_num(0), p)) ∧ " +
			"fun_support(int_of_num(0), p) ⊆ monomials(integer_polynomial_vars(p))",
	},
		func(a *Argument, p *Arrow[Fun[Nat, Nat], Int], polynomial Fact) {
			a.Show(
				"a polynomial on its own variables is finitely supported on their monomials",
				By(a.Simplified(
					GroupPremises(polynomial, PolynomialOnOwnVariables.At(p)),
					Fwd(polynomial_algebra.PolynomialAlgebraMember))))
		}),
})}

// PolynomialOnVariables — the polynomials of the integer polynomial algebra
// on U are the integer polynomials whose variables lie in U: a polynomial on U
// is one on all the variables, and a variable of it is a nonzero exponent of a
// monomial where it is nonzero, which is a monomial of U; conversely an
// integer polynomial is a polynomial on its own variables, and so on every
// set holding them.
var PolynomialOnVariables = polynomialOnVariablesThm{family.Add(registry.ProofEntry{
	Name: "PolynomialOnVariables",
	Key:  "prop_3c94f612bff5e903",
	Build: family.Theorem("∀U:set(num). ∀q:((num → num) → int). "+
		"    q ∈ polynomial_algebra(int_ring, U) ⇔ integer_polynomial(q) ∧ integer_polynomial_vars(q) ⊆ U",
		func(a *Argument, U *Expr[Set[Nat]], q *Arrow[Fun[Nat, Nat], Int]) {
			integers := a.TermAs[RingOps[Int]]("int_ring")
			a.Iff()
			a.Forward(
				"a polynomial on U is an integer polynomial whose variables lie in U",
				func(b *Argument, onU Fact) {
					integer := b.Have(
						"a polynomial on U is one on all the variables",
						"integer_polynomial(q)",
						BySets(
							onU,
							IntegerPolynomialDef,
							polynomial_algebra.PolynomialAlgebraSubset.At(integers, U, b.TermAs[Set[Nat]]("𝕌"))))
					variables := b.Have(
						"a variable of q is a nonzero exponent of a monomial where q is nonzero, a monomial of U",
						"integer_polynomial_vars(q) ⊆ U",
						Unfold(set_basic.SubsetDef),
						Derive(func(c *Argument) {
							c.FixAs[Nat]("w")
							m, witness := c.UnpackAs[Fun[Nat, Nat]](c.Unfolded(c.Assume(), PolynomialVarsDef), "m")
							c.Show(
								"that monomial is a monomial of U, whose nonzero exponents sit at members of U",
								By(
									witness,
									onU,
									polynomial_algebra.PolynomialAlgebraMember.At(integers, U, q),
									set_basic.SubsetDef.At(
										c.TermAs[Set[Fun[Nat, Nat]]]("fun_support(int_of_num(0), q)"),
										c.TermAs[Set[Fun[Nat, Nat]]]("monomials(U)")),
									polynomial_algebra.MonomialSupport.At(U, m)))
						}))
					b.Show(
						"q is an integer polynomial, and its variables lie in U",
						By(integer, variables))
				})
			a.Backward(
				"an integer polynomial is one on its own variables, and so on U, which holds them",
				func(b *Argument, given Fact) {
					b.Show(
						"the polynomials on the variables of q lie among those on U",
						By(
							given,
							PolynomialOnOwnVariables.At(q),
							polynomial_algebra.PolynomialAlgebraSubset.At(
								integers,
								b.TermAs[Set[Nat]]("integer_polynomial_vars(q)"),
								U),
							set_basic.SubsetDef))
				})
		}),
})}

// PolynomialVariableSupport — the variable v is an integer polynomial in the variable v alone:
// its one nonzero coefficient sits at the monomial of v.
var PolynomialVariableSupport = polynomialVariableSupportThm{family.Add(registry.ProofEntry{
	Name: "PolynomialVariableSupport",
	Key:  "prop_d83f69fb8df64e0b",
	Build: family.Theorem(
		"∀v:num. "+
			"    integer_polynomial(polynomial_algebra_var(int_ring, v)) ∧ "+
			"    integer_polynomial_vars(polynomial_algebra_var(int_ring, v)) ⊆ {v}",
		func(a *Argument, v *Expr[Nat]) {
			polynomial := a.Have(
				"a variable is a polynomial over the integers",
				"integer_polynomial(polynomial_algebra_var(int_ring, v))",
				By(
					IntegerPolynomialDef,
					int_real_lift.CommRingOn,
					set_basic.InUniv,
					polynomial_algebra.PolynomialAlgebraVarIn.At(
						a.TermAs[RingOps[Int]]("int_ring"),
						a.TermAs[Set[Nat]]("𝕌"),
						v)))
			variables := a.Have(
				"its one nonzero coefficient sits at the monomial of v",
				"integer_polynomial_vars(polynomial_algebra_var(int_ring, v)) ⊆ {v}",
				Simp(
					Fwd(PolynomialVarsDef),
					Fwd(polynomial_algebra.PolynomialAlgebraVarDef),
					Fwd(free_module.DeltaAtDef),
					Fwd(polynomial_algebra.MonomialVarDef),
					Fwd(int_real_lift.IntRingDef)),
				BySets())
			a.Show(
				"an integer polynomial in the variable v alone",
				By(polynomial, variables))
		}),
})}

// EvaluationInCarrier — evaluation at carrier-valued active variables lies in
// the carrier: p is a polynomial on its own variables, where ρ takes values in
// R, and the integers map into R as a ring homomorphism, so the value of the
// polynomial algebra's evaluation lies in R.
var EvaluationInCarrier = evaluationInCarrierThm{family.Add(registry.ProofEntry{
	Name: "EvaluationInCarrier",
	Key:  "prop_e43eba44531fd685",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀ρ:(num → A). ∀p:((num → num) → int).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"integer_polynomial(p)",
			"fo_env_ok(R.carrier, integer_polynomial_vars(p), ρ)",
		},
		Conclusion: "integer_polynomial_eval(R, ρ, p) ∈ R.carrier",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			ring comm_ring.CommRingFact[on.R],
			ρ *Arrow[Nat, A],
			p *Arrow[Fun[Nat, Nat], Int],
			polynomial, environment Fact,
		) {
			integers := characteristic_zero.IntegerMapHomomorphism.Read(ring)
			a.Show(
				"the integer map is a ring homomorphism into R, so the value "+
					"of p, a polynomial on its own variables, at ρ lies in R",
				Simp(Fwd(IntegerPolynomialEvalDef)),
				By(
					integers,
					environment,
					polynomial,
					PolynomialOnOwnVariables.At(p),
					polynomial_algebra_evaluation.PolynomialAlgebraEvalIn,
					first_order.EnvOKDef))
		}),
})}

// EvaluationCongruence — evaluation depends only on the variables of nonzero
// monomials: the value of p is a sum over its support of coefficient times
// monomial value, and a monomial where p is nonzero is a product over its own
// variables, all of them variables of p, where ρ and σ agree; so the two sums
// agree term by term.
var EvaluationCongruence = evaluationCongruenceThm{family.Add(registry.ProofEntry{
	Name: "EvaluationCongruence",
	Key:  "prop_e6cd6fe5521d8b85",
	Reading: "No ring axioms, environment membership or validity of p " +
		"are needed: the finite-sum fold ignores indices outside its " +
		"summation set, and each monomial reads only its nonzero exponents.",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀ρ σ:(num → A). ∀p:((num → num) → int).",
		Hypotheses: []string{
			"∀v:num. v ∈ integer_polynomial_vars(p) ⇒ ρ(v) = σ(v)",
		},
		Conclusion: "integer_polynomial_eval(R, ρ, p) = integer_polynomial_eval(R, σ, p)",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			ρ, σ *Arrow[Nat, A],
			p *Arrow[Fun[Nat, Nat], Int],
			agree Fact,
		) {
			monomials := a.Have(
				"each monomial where p is nonzero takes one value "+
					"at ρ and at σ, its variables being variables of p",
				Statement{
					Binders:    "∀m:(num → num).",
					Hypotheses: []string{"m ∈ fun_support(int_of_num(0), p)"},
					Conclusion: "monomial_eval(R, ρ, m) = monomial_eval(R, σ, m)",
				},
				Simp(Fwd(polynomial_algebra_evaluation.MonomialEvalDef)),
				BySets(agree, module.ModuleSumCongruence, PolynomialVarsDef))
			a.Show(
				"so the two sums over the support of p agree term by term",
				Simp(Fwd(IntegerPolynomialEvalDef), Fwd(polynomial_algebra_evaluation.PolynomialAlgebraEvalDef)),
				By(monomials, module.ModuleSumCongruence))
		}),
})}

// EvaluationNatural — evaluation commutes with a ring homomorphism i: i after
// the integer map of R lands in S, keeps the one and sums, so it is the
// integer map of S, the only such map; and evaluation followed by a ring map
// is evaluation at the images of the values, read at p as a polynomial on its
// own variables, the integer maps of R and of S being ring homomorphisms.
var EvaluationNatural = evaluationNaturalThm{family.Add(registry.ProofEntry{
	Name: "EvaluationNatural",
	Key:  "prop_91b0b02505faef08",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀i:(A → B). ∀ρ:(num → A). ∀p:((num → num) → int).",
		Hypotheses: []string{
			"ring_homomorphism(R, S, i)",
			"integer_polynomial(p)",
			"fo_env_ok(R.carrier, integer_polynomial_vars(p), ρ)",
		},
		Conclusion: "i(integer_polynomial_eval(R, ρ, p)) = integer_polynomial_eval(S, λv:num. i(ρ(v)), p)",
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		S *Expr[RingOps[B]],
		i *Arrow[A, B],
		hom ring_homomorphism.RingHomomorphismFact[on.R, on.S],
		ρ *Arrow[Nat, A],
		p *Arrow[Fun[Nat, Nat], Int],
		polynomial, environment Fact,
	) {
		source := ring_homomorphism.Source.Read(hom)
		target := ring_homomorphism.Target.Read(hom)
		imageIn := a.Have(
			"i after the integer map of R lands in S",
			"image(λz:int. i(integer_map(R, z)), 𝕌) ⊆ S.carrier",
			BySets(ring_homomorphism.MapIn.Read(hom), characteristic_zero.IntegerMapInCarrier.Read(source)))
		additive := a.Have(
			"and is additive, as both maps are",
			"∀a b:int. i(integer_map(R, a + b)) = S.add(i(integer_map(R, a)), i(integer_map(R, b)))",
			By(
				characteristic_zero.IntegerMapHom.Read(source),
				ring_homomorphism.MapAdd.Read(hom),
				characteristic_zero.IntegerMapInCarrier.Read(source)))
		transport := a.Have(
			"keeping the one as well, it is the integer map of S, the only such map",
			"∀z:int. i(integer_map(R, z)) = integer_map(S, z)",
			By(
				characteristic_zero.IntegerMapHom.Read(target),
				imageIn,
				additive,
				characteristic_zero.IntegerMapHom.Read(source),
				ring_homomorphism.MapOne.Read(hom)))
		a.Show(
			"evaluation at ρ followed by i is evaluation at i ∘ ρ, read at p on its own variables",
			Simp(Fwd(IntegerPolynomialEvalDef)),
			By(
				hom,
				source,
				target,
				characteristic_zero.IntegerMapHomomorphism.Read(source),
				characteristic_zero.IntegerMapHomomorphism.Read(target),
				transport,
				environment,
				polynomial,
				PolynomialOnOwnVariables.At(p),
				polynomial_algebra_evaluation.PolynomialAlgebraEvalNatural,
				first_order.EnvOKDef))
	}),
})}

// IntegerPolynomialEvalHom — evaluating integer polynomials at an environment carrier-valued on the
// variables U is a ring homomorphism from the integer polynomials in those variables into the ring:
// it is the evaluation of the polynomial algebra on U along the integers' own map.
var IntegerPolynomialEvalHom = integerPolynomialEvalHomThm{family.Add(registry.ProofEntry{
	Name: "IntegerPolynomialEvalHom",
	Key:  "prop_1bc45dc3e3111470",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀U:set(num). ∀ρ:(num → A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"fo_env_ok(R.carrier, U, ρ)",
		},
		Conclusion: "ring_homomorphism(«parameterRing»(U), " +
			"    R, " +
			"    λq:((num → num) → int). integer_polynomial_eval(R, ρ, q))",
	},
		func(a *Argument, R *Expr[RingOps[A]], U *Expr[Set[Nat]], ρ *Arrow[Nat, A], ring, env Fact) {
			a.Show(
				"the polynomials of U over the integers evaluate along "+
					"the integers' map into R at the values ρ takes on U",
				Simp(
					Fwd(IntegerPolynomialRingDef),
					Fwd(polynomial_algebra.PolynomialAlgebraRingRestrictVariables),
					Fwd(IntegerPolynomialEvalDef)),
				By(
					ring,
					env,
					characteristic_zero.IntegerMapHomomorphism.At(R),
					polynomial_algebra_evaluation.PolynomialAlgebraEvalHom.At(
						a.TermAs[RingOps[Int]]("int_ring"),
						R,
						a.TermAs[Fun[Int, A]]("integer_map(R)"),
						ρ,
						U),
					first_order.EnvOKDef))
		}),
})}

// VariableValue — evaluating the integer polynomial of the variable v reads the environment at v:
// the evaluation is the polynomial evaluation along the integer map, a ring homomorphism, and that
// sends a variable to its value.
var VariableValue = variableValueThm{family.Add(registry.ProofEntry{
	Name: "VariableValue",
	Key:  "prop_e1a3be554bda6a3b",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀ρ:(num → A). ∀v:num.",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"ρ(v) ∈ R.carrier",
		},
		Conclusion: "integer_polynomial_eval(R, ρ, polynomial_algebra_var(int_ring, v)) = ρ(v)",
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		ρ *Arrow[Nat, A],
		v *Expr[Nat],
		ring comm_ring.CommRingFact[on.R],
		value Fact,
	) {
		a.Show(
			"the integer map is a ring homomorphism, and evaluation along it sends a variable to its value",
			By(
				value,
				IntegerPolynomialEvalDef,
				characteristic_zero.IntegerMapHomomorphism.Read(ring),
				polynomial_algebra_evaluation.PolynomialAlgebraEvalVar))
	}),
})}

// ZeroPolynomialValid — the zero polynomial is a valid polynomial with no variable: it is the
// zero of the integer polynomials in no variables, which form a commutative ring.
//
// The claim carries an annotation, ∅⟨A:num⟩. polynomial_algebra_ring takes its variable names
// from a set of any type, so written bare the empty set leaves its letter unpinned and the claim
// is refused; ⟨A:num⟩ pins it at num, the type of the variable names.
var ZeroPolynomialValid = zeroPolynomialValidThm{family.Add(registry.ProofEntry{
	Name: "ZeroPolynomialValid",
	Key:  "prop_7584767622394b25",
	Build: family.Theorem("integer_polynomial(fun_zero(int_of_num(0))) ∧ "+
		"integer_polynomial_vars(fun_zero(int_of_num(0))) = ∅",
		func(a *Argument) {
			constants := a.Have(
				"the integer polynomials in no variables form a commutative ring",
				"comm_ring_on(polynomial_algebra_ring(int_ring, ∅⟨A:num⟩))",
				By(
					int_real_lift.CommRingOn,
					polynomial_algebra.PolynomialAlgebraCommRingOn.At(
						a.TermAs[RingOps[Int]]("int_ring"),
						a.TermAs[Set[Nat]]("∅"))))
			a.Show(
				"its zero is the zero polynomial, a polynomial in no variables",
				BySets(comm_ring.ZeroIn.Read(constants), PolynomialOnVariables))
		}),
})}

// ZeroPolynomialValue — the zero polynomial evaluates to the zero of a ring at every environment:
// it is nonzero at no monomial, so its value is the empty sum.
//
// The statement annotates the zero function's domain, fun_zero⟨D:(num → num)⟩. Under the ring
// binder R, fun_zero(int_of_num(0)) written bare reads R.zero as the implicit zero and
// int_of_num(0) as the point; the domain of monomials pins the zero function on them.
var ZeroPolynomialValue = zeroPolynomialValueThm{family.Add(registry.ProofEntry{
	Name: "ZeroPolynomialValue",
	Key:  "prop_388a24ca598bcacc",
	Build: family.Theorem("∀R:ring_ops(A). ∀ρ:(num → A). "+
		"    integer_polynomial_eval(R, ρ, fun_zero⟨D:(num → num)⟩(int_of_num(0))) = R.zero",
		func(a *Argument, R *Expr[RingOps[A]], ρ *Arrow[Nat, A]) {
			support := a.Have(
				"the zero polynomial is nonzero at no monomial",
				"fun_support(int_of_num(0), λm:(num → num). 0) = ∅",
				BySets())
			a.Show(
				"so its value is the empty sum, zero",
				Simp(
					Fwd(function_module.FunZeroDef),
					Fwd(IntegerPolynomialEvalDef),
					Fwd(polynomial_algebra_evaluation.PolynomialAlgebraEvalDef),
					Fwd(int_real_lift.IntRingDef),
					Fwd(support),
					Fwd(module.ModuleSumEmpty)),
				Refl())
		}),
})}

// OnePolynomialSupport — the one polynomial is an integer polynomial without variables: it is the
// unit of the integer polynomials in no variables, which form a commutative ring. The claim's
// ∅⟨A:num⟩ is annotated as in ZeroPolynomialValid.
var OnePolynomialSupport = onePolynomialSupportThm{family.Add(registry.ProofEntry{
	Name: "OnePolynomialSupport",
	Key:  "prop_b43da219317154ca",
	Build: family.Theorem("integer_polynomial(polynomial_algebra_one(int_ring)) ∧ "+
		"integer_polynomial_vars(polynomial_algebra_one(int_ring)) = ∅",
		func(a *Argument) {
			constants := a.Have(
				"the integer polynomials in no variables form a commutative ring",
				"comm_ring_on(polynomial_algebra_ring(int_ring, ∅⟨A:num⟩))",
				By(
					int_real_lift.CommRingOn,
					polynomial_algebra.PolynomialAlgebraCommRingOn.At(
						a.TermAs[RingOps[Int]]("int_ring"),
						a.TermAs[Set[Nat]]("∅"))))
			a.Show(
				"its unit is the one polynomial, a polynomial in no variables",
				BySets(comm_ring.OneIn.Read(constants), PolynomialOnVariables))
		}),
})}

// OnePolynomialValue — the one polynomial evaluates to the one of a commutative ring at every
// environment: it is the constant one, which the integer map, a ring homomorphism, sends to one.
var OnePolynomialValue = onePolynomialValueThm{family.Add(registry.ProofEntry{
	Name: "OnePolynomialValue",
	Key:  "prop_17f37966649b37d9",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀ρ:(num → A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
		},
		Conclusion: "integer_polynomial_eval(R, ρ, polynomial_algebra_one(int_ring)) = R.one",
	}, func(a *Argument, R *Expr[RingOps[A]], ρ *Arrow[Nat, A], ring comm_ring.CommRingFact[on.R]) {
		integers := a.TermAs[RingOps[Int]]("int_ring")
		integerMap := a.Have(
			"the integer map is a ring homomorphism into R",
			"ring_homomorphism(int_ring, R, integer_map(R))",
			By(characteristic_zero.IntegerMapHomomorphism.Read(ring)))
		a.Show(
			"the one polynomial is the constant one, which the integer map sends to the one of R",
			Simp(
				Fwd(IntegerPolynomialEvalDef),
				Fwd(polynomial_algebra.PolynomialAlgebraOneDef),
				Rev(polynomial_algebra.PolynomialAlgebraConstDef)),
			By(
				ring_homomorphism.MapOne.Read(integerMap),
				polynomial_algebra_evaluation.PolynomialAlgebraEvalConst.At(
					integers,
					R,
					a.TermAs[Fun[Int, A]]("integer_map(R)"),
					ρ,
					a.TermAs[Int]("1")),
				int_real_lift.IntRingDef,
				set_basic.InUniv))
	}),
})}

// PolynomialNegation — negating every coefficient of a valid integer polynomial gives a valid
// integer polynomial in the same variables: the negation in the commutative ring of integer
// polynomials negates each coefficient and keeps a polynomial among them, and a coefficient's
// negation is zero exactly where the coefficient is, so the negation's coefficients vanish where
// those of p do.
var PolynomialNegation = polynomialNegationThm{family.Add(registry.ProofEntry{
	Name: "PolynomialNegation",
	Key:  "prop_989afd8eb5649724",
	Build: family.Theorem(Statement{
		Binders: "∀p:((num → num) → int).",
		Hypotheses: []string{
			"integer_polynomial(p)",
		},
		Conclusion: "integer_polynomial(λm:(num → num). -p(m)) ∧ " +
			"integer_polynomial_vars(λm:(num → num). -p(m)) = integer_polynomial_vars(p)",
	}, func(a *Argument, p *Arrow[Fun[Nat, Nat], Int], polynomial Fact) {
		zeros := a.Have(
			"a coefficient's negation is zero exactly where the coefficient is",
			"∀m:(num → num). -p(m) = &0 ⇔ p(m) = &0",
			a.ForEach(func(m *Expr[Fun[Nat, Nat]]) Action { return ByArith() }))
		coefficientwise := a.Have(
			"the negation in the ring of integer polynomials negates each coefficient",
			"fun_neg(int_neg, p) = λm:(num → num). -p(m)",
			By(function_module.FunNegDef))
		a.Show(
			"the negation is valid in the variables of p",
			SplitConj(
				Case(
					"the negation in the ring of integer polynomials keeps a polynomial among them",
					By(
						polynomial,
						coefficientwise,
						IntegerPolynomialDef,
						IntegerPolynomialRingDef,
						comm_ring.NegIn,
						polynomial_algebra.PolynomialAlgebraCommRingOn,
						int_real_lift.CommRingOn)),
				Case(
					"and its coefficients vanish where those of p do, so it has the variables of p",
					Simp(Fwd(PolynomialVarsDef)),
					By(zeros))))
	}),
})}

// EvaluationNegation — the value of a valid integer polynomial with its coefficients negated is the
// negation of its value: the polynomial lies among the polynomials on its own variables,
// evaluation there along the integers' map into the ring is a ring homomorphism, a ring
// homomorphism keeps negation, and the negation of the integer polynomials negates each
// coefficient.
var EvaluationNegation = evaluationNegationThm{family.Add(registry.ProofEntry{
	Name: "EvaluationNegation",
	Key:  "prop_29adbd9561304827",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀ρ:(num → A). ∀p:((num → num) → int).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"integer_polynomial(p)",
			"fo_env_ok(R.carrier, integer_polynomial_vars(p), ρ)",
		},
		Conclusion: "integer_polynomial_eval(R, ρ, λm:(num → num). -p(m)) = " +
			"R.neg(integer_polynomial_eval(R, ρ, p))",
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		ring comm_ring.CommRingFact[on.R],
		ρ *Arrow[Nat, A],
		p *Arrow[Fun[Nat, Nat], Int],
		polynomial, environment Fact,
	) {
		variables := a.TermAs[Set[Nat]]("integer_polynomial_vars(p)")
		evaluation := a.Have(
			"evaluation is a ring homomorphism on the integer polynomials in the variables of p",
			"ring_homomorphism(«parameterRing»(integer_polynomial_vars(p)), "+
				"    R, "+
				"    λr:((num → num) → int). integer_polynomial_eval(R, ρ, r))",
			By(environment, ring, IntegerPolynomialEvalHom.At(R, variables, ρ)))
		coefficientwise := a.Have(
			"the negation in the ring of integer polynomials negates each coefficient",
			"fun_neg(int_neg, p) = λm:(num → num). -p(m)",
			By(function_module.FunNegDef))
		a.Show(
			"p is a polynomial in its own variables, and a ring homomorphism keeps negation",
			By(
				polynomial,
				coefficientwise,
				PolynomialOnOwnVariables.At(p),
				ring_homomorphism.MapNeg.Read(evaluation).AsFact().At(p),
				IntegerPolynomialRingDef))
	}),
})}

// PolynomialDifference — the difference of two valid integer polynomials is a valid integer
// polynomial in their variables: it is nonzero only on monomials where one of them is, finitely
// many monomials, and a variable of it occurs in a nonzero term of one of them.
var PolynomialDifference = polynomialDifferenceThm{family.Add(registry.ProofEntry{
	Name: "PolynomialDifference",
	Key:  "prop_611285804e006c32",
	Build: family.Theorem(Statement{
		Binders: "∀p q:((num → num) → int).",
		Hypotheses: []string{
			"integer_polynomial(p)",
			"integer_polynomial(q)",
		},
		Conclusion: "integer_polynomial(λm:(num → num). p(m) - q(m)) ∧ " +
			"integer_polynomial_vars(λm:(num → num). p(m) - q(m)) ⊆ " +
			"integer_polynomial_vars(p) ∪ integer_polynomial_vars(q)",
	}, func(a *Argument, p, q *Arrow[Fun[Nat, Nat], Int], pPolynomial, qPolynomial Fact) {
		difference := a.Have(
			"a nonzero difference has a nonzero term",
			"∀m:(num → num). p(m) - q(m) ≠ 0 ⇒ p(m) ≠ 0 ∨ q(m) ≠ 0",
			ByArith())
		support := a.Have(
			"so the difference is nonzero only where p or q is",
			"fun_support(int_of_num(0), λm:(num → num). p(m) - q(m)) ⊆ "+
				"fun_support(int_of_num(0), p) ∪ fun_support(int_of_num(0), q)",
			BySets(difference))
		supports := a.Have(
			"p and q are nonzero on finitely many monomials",
			"finite(fun_support(int_of_num(0), p)) ∧ "+
				"fun_support(int_of_num(0), p) ⊆ monomials(𝕌⟨A:num⟩) ∧ "+
				"finite(fun_support(int_of_num(0), q)) ∧ "+
				"fun_support(int_of_num(0), q) ⊆ monomials(𝕌⟨A:num⟩)",
			By(
				pPolynomial,
				qPolynomial,
				IntegerPolynomialDef,
				polynomial_algebra.PolynomialAlgebraMember,
				int_real_lift.IntRingDef))
		finiteSupport := a.Have(
			"the difference is nonzero on finitely many monomials",
			"finite(fun_support(int_of_num(0), λm:(num → num). p(m) - q(m)))",
			By(support, supports, finite_set.FiniteUnionImp, finite_set.FiniteSubset))
		monomialSupport := a.Have(
			"and on monomials only",
			"fun_support(int_of_num(0), λm:(num → num). p(m) - q(m)) ⊆ monomials(𝕌⟨A:num⟩)",
			By(support, supports, set_order.UnionSubset, set_order.SubsetTrans))
		polynomial := a.Have(
			"so the difference is an integer polynomial",
			"integer_polynomial(λm:(num → num). p(m) - q(m))",
			Simp(
				Fwd(IntegerPolynomialDef),
				Fwd(polynomial_algebra.PolynomialAlgebraMember),
				Fwd(int_real_lift.IntRingDef)),
			BySets(finiteSupport, monomialSupport))
		variables := a.Have(
			"a variable of the difference occurs in a nonzero term of p or of q",
			"integer_polynomial_vars(λm:(num → num). p(m) - q(m)) ⊆ "+
				"integer_polynomial_vars(p) ∪ integer_polynomial_vars(q)",
			Simp(Fwd(PolynomialVarsDef)),
			Unfold(set_basic.SubsetDef),
			Derive(func(b *Argument) {
				b.FixAs[Nat]("v")
				m, term := b.UnpackAs[Fun[Nat, Nat]](b.Assume(), "m")
				b.Show(
					"the term at m is a nonzero term of p or of q",
					BySets(difference.At(m), term))
			}))
		a.Show(
			"the difference is an integer polynomial in the variables of p and q",
			By(polynomial, variables))
	}),
})}

// EvaluationDifference — the value of the difference of two valid integer polynomials is the
// difference of their values: both lie among the polynomials on the variables of the two, where
// evaluation along the integers' map into the ring is a ring homomorphism, and a ring homomorphism
// keeps differences.
var EvaluationDifference = evaluationDifferenceThm{family.Add(registry.ProofEntry{
	Name: "EvaluationDifference",
	Key:  "prop_c84656c287a7cc4c",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀ρ:(num → A). ∀p q:((num → num) → int).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"integer_polynomial(p)",
			"integer_polynomial(q)",
			"fo_env_ok(R.carrier, integer_polynomial_vars(p) ∪ integer_polynomial_vars(q), ρ)",
		},
		Conclusion: "integer_polynomial_eval(R, ρ, λm:(num → num). p(m) - q(m)) = " +
			"R.sub(integer_polynomial_eval(R, ρ, p), integer_polynomial_eval(R, ρ, q))",
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		ring comm_ring.CommRingFact[on.R],
		ρ *Arrow[Nat, A],
		p, q *Arrow[Fun[Nat, Nat], Int],
		pPolynomial, qPolynomial, environment Fact,
	) {
		U := a.TermAs[Set[Nat]]("integer_polynomial_vars(p) ∪ integer_polynomial_vars(q)")
		evaluation := a.Have(
			"evaluation is a ring homomorphism on the integer polynomials in the variables of p and q",
			"ring_homomorphism(«parameterRing»(integer_polynomial_vars(p) ∪ integer_polynomial_vars(q)), "+
				"    R, "+
				"    λr:((num → num) → int). integer_polynomial_eval(R, ρ, r))",
			By(environment, ring, IntegerPolynomialEvalHom.At(R, U, ρ)))
		members := a.Have(
			"p and q are polynomials in those variables",
			"p ∈ polynomial_algebra(int_ring, integer_polynomial_vars(p) ∪ integer_polynomial_vars(q)) ∧ "+
				"q ∈ polynomial_algebra(int_ring, integer_polynomial_vars(p) ∪ integer_polynomial_vars(q))",
			BySets(pPolynomial, qPolynomial, PolynomialOnVariables.At(U, p), PolynomialOnVariables.At(U, q)))
		a.Show(
			"and a ring homomorphism keeps differences",
			By(members, ring_homomorphism.MapSub.Read(evaluation).AsFact().At(p, q), IntegerPolynomialRingDef))
	}),
})}

// VariableFreeEvaluation — a polynomial with integer coefficients in which no
// variable occurs takes, in any commutative ring and at every environment,
// the image of its constant coefficient under the integer map. A monomial
// where the polynomial is nonzero has every exponent zero, since a nonzero
// exponent would make its variable occur; so the polynomial is the constant
// at its coefficient of the monomial with no variables, and a constant
// evaluates to its image.
var VariableFreeEvaluation = variableFreeEvaluationThm{family.Add(registry.ProofEntry{
	Name: "VariableFreeEvaluation",
	Key:  "prop_47e92d53c5a0dc95",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀ρ:(num → A). ∀p:((num → num) → int).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"integer_polynomial_vars(p) = ∅",
		},
		Conclusion: "integer_polynomial_eval(R, ρ, p) = integer_map(R, p(λi:num. 0))",
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		ρ *Arrow[Nat, A],
		p *Arrow[Fun[Nat, Nat], Int],
		ring comm_ring.CommRingFact[on.R],
		noVariables Fact,
	) {
		integers := characteristic_zero.IntegerMapHomomorphism.Read(ring)
		onlyConstantMonomial := a.Have(
			"a monomial where p is nonzero is the monomial with no variables",
			"∀m:(num → num). p(m) ≠ &0 ⇒ m = λi:num. 0",
			Derive(func(b *Argument) {
				b.FixAs[Fun[Nat, Nat]]("m")
				nonzero := b.Assume()
				b.Do(Funext())
				b.Show(
					"a nonzero exponent of m would make its variable a variable of p, and p has none",
					BySets(nonzero, noVariables, PolynomialVarsDef))
			}))
		constant := a.Have(
			"so p is the constant polynomial at its coefficient of the monomial with no variables",
			"p = polynomial_algebra_const(int_ring, p(λi:num. 0))",
			Funext(),
			Simp(
				Fwd(polynomial_algebra.PolynomialAlgebraConstDef),
				Fwd(free_module.DeltaAtDef),
				Fwd(int_real_lift.IntRingDef)),
			By(onlyConstantMonomial))
		a.Show(
			"and a constant evaluates to its image under the integer map",
			By(
				constant,
				integers,
				IntegerPolynomialEvalDef,
				polynomial_algebra_evaluation.PolynomialAlgebraEvalConst.At(
					a.TermAs[RingOps[Int]]("int_ring"),
					R,
					a.TermAs[Fun[Int, A]]("integer_map(R)"),
					ρ,
					a.TermAs[Int]("p(λi:num. 0)")),
				int_real_lift.IntRingDef,
				set_basic.InUniv))
	}),
})}
