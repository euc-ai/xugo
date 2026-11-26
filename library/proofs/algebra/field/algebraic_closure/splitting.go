// splitting.go — splitting inside an algebraically closed field: every
// polynomial splits over it, and the field a subfield K generates with the
// roots of one polynomial over K is a finite extension over which the
// polynomial splits, lying in every subfield holding K over which it splits.

package algebraic_closure

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_division"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_roots"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/separable_polynomial"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ClosedFieldSplits — over an algebraically closed field every
// polynomial splits: an irreducible polynomial has a root in the field,
// and so is linear.
var ClosedFieldSplits = closedFieldSplitsThm{family.Add(registry.ProofEntry{
	Name: "ClosedFieldSplits",
	Key:  "prop_ab8062020d7f7fd9",
	Reading: "No hypothesis on p: polynomial_splits reads only the " +
		"irreducible polynomials dividing p, and over a closed field every " +
		"irreducible polynomial has degree one, so even the zero polynomial splits.",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀p:(num → A).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
		},
		Conclusion: "polynomial_splits(field_ring(M), p)",
	}, func(a *Argument, M field.FieldFact[on.M], p *Arrow[Nat, A], closed Fact) {
		fieldRecord := a.TermAs[FieldOps[A]]("M")
		coefficients := a.TermAs[module_record.RingOps[A]]("field_ring(M)")
		domain := integral_domain.FieldIntegralDomain.Read(M)
		irreduciblesLinear := a.Have(
			"every irreducible polynomial over M is linear",
			"∀q:(num → A). polynomial_irreducible(field_ring(M), q) ⇒ polynomial_degree(q) = 1",
			Derive(func(b *Argument) {
				q := b.FixAs[Fun[Nat, A]]("q")
				irreducible := b.Assume()
				data := b.Conjuncts(
					b.Unfolded(irreducible, polynomial_division.PolynomialIrreducibleDef),
					"q is a polynomial over M",
					"q has positive degree",
					"one factor of every factorization of q has degree zero")
				r, root := b.ObtainAs[A](
					"q has a root in the closed field",
					"∃r:A. r ∈ M.carrier ∧ polynomial_eval(q, r) = M.zero",
					By(closed, data[1], data[0], AlgebraicallyClosedDef.At(fieldRecord)))
				rootParts := b.Conjuncts(
					root,
					"r lies in M",
					"q vanishes at r")
				b.Show(
					"an irreducible polynomial with a root in the field is linear",
					By(
						irreducible,
						rootParts[1],
						polynomial_roots.IrreducibleRootLinear.Read(domain).At(q, b.MemberOf[on.M](r, rootParts[0]))))
			}))
		a.Show(
			"every irreducible divisor has degree one, so p splits",
			By(irreduciblesLinear, separable_polynomial.PolynomialSplitsDef.At(coefficients, p)))
	}),
})}

// SplittingFieldInClosed — inside an algebraically closed field, adjoining
// a polynomial's roots gives a finite splitting field, contained in every
// intermediate field over which the polynomial splits. Finite: the nonzero
// polynomial has finitely many roots, each algebraic over K. Splits: an
// irreducible divisor q over the root field E has a root r in the closed
// field, which is a root of p and so lies in E, and an irreducible
// polynomial with a root in its field is linear. Least: by induction on a
// degree bound, a nonzero polynomial that splits over a subfield S has all
// its roots in S — splitting gives a root in S, and the cofactor left by its
// linear factor splits over S with smaller degree; so S, holding K and every
// root of p, holds the field they generate.
var SplittingFieldInClosed = splittingFieldInClosedThm{family.Add(registry.ProofEntry{
	Name: "SplittingFieldInClosed",
	Key:  "prop_6a5418e7c2dcad3e",
	Reading: "p ≠ 0 is load-bearing for finiteness: the zero polynomial has every point as a " +
		"root. A nonzero constant has no roots, and E is K. Minimality reads splitting over S as a " +
		"factorization into linear factors over S, whose roots are all the roots in M, M having no " +
		"zero divisors. K ⊆ S is load-bearing for minimality: a p not over S has no irreducible " +
		"divisor over S and splits there vacuously. The splitting field exists for every polynomial " +
		"over every field, through the algebraic closure of the field (AlgebraicClosureFieldOn).",
	Build: family.Sections(Statement{
		Binders: "∀M:field_on(A). ∀K:set(A). ∀p:(num → A).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"subfield(M, K)",
			"polynomial_over(K, p)",
			"p ≠ vec_zero",
		},
		Conclusion: "finite_extension(M, K, «E») ∧ " +
			"polynomial_splits(restrict_ring(field_ring(M), «E»), p) ∧ " +
			"(∀S:set(A). " +
			"    subfield(M, S) ∧ K ⊆ S ∧ polynomial_splits(restrict_ring(field_ring(M), S), p) ⇒ «E» ⊆ S)",
		Abbrev: Abbrev{
			{Name: "E", Text: "field_adjoin(M, K, polynomial_roots(M.carrier, p))"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		linearProductRoots := ctx.Lemma(Statement{
			Binders: "∀M:field_on(A). ∀p q:(num → A). ∀r:A.",
			Hypotheses: []string{
				"polynomial_over(M.carrier, q)",
				"r ∈ M.carrier",
				"p = polynomial_mul(«linear»(r), q)",
			},
			Conclusion: "polynomial_roots(M.carrier, p) ⊆ insert(r, polynomial_roots(M.carrier, q))",
		}, func(a *Argument, M field.FieldFact[on.M], p, q *Arrow[Nat, A], r *Expr[A], given Fact) {
			ring := field.RingOn.Read(M)
			linear := a.TermAs[Fun[Nat, A]]("«linear»(r)")
			forced := a.Have(
				"a root of a linear product is the linear root or a cofactor root",
				"∀x:A. x ∈ M.carrier ∧ polynomial_eval(p, x) = M.zero ⇒ x = r ∨ polynomial_eval(q, x) = M.zero",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					atRoot := b.Conjuncts(
						b.Assume(),
						"x lies in M",
						"p vanishes at x")
					linearValue := b.Have(
						"the linear polynomial evaluates as x minus r",
						"polynomial_over(M.carrier, «linear»(r)) ∧ polynomial_eval(«linear»(r), x) = x - r",
						By(atRoot[0], given, polynomial_roots.LinearFactor.Read(ring).AsFact().At(r)))
					values := b.Have(
						"evaluation multiplies the two factor values in M",
						"polynomial_eval(«linear»(r), x) ∈ M.carrier ∧ "+
							"polynomial_eval(q, x) ∈ M.carrier ∧ "+
							"polynomial_eval(p, x) = polynomial_eval(«linear»(r), x) * polynomial_eval(q, x)",
						By(
							atRoot[0],
							given,
							linearValue,
							polynomial_evaluation.EvalIn.Read(ring).AsFact().At(q, x),
							polynomial_evaluation.EvalIn.Read(ring).AsFact().At(linear, x),
							polynomial_evaluation.EvalMul.Read(ring).AsFact().At(linear, q, x)))
					eitherZero := b.Have(
						"one factor value vanishes in a field",
						"polynomial_eval(«linear»(r), x) = M.zero ∨ polynomial_eval(q, x) = M.zero",
						By(
							atRoot[1],
							values,
							field.MulEqZeroOn.Read(M).AsFact().At(
								b.TermAs[A]("polynomial_eval(«linear»(r), x)"),
								b.TermAs[A]("polynomial_eval(q, x)"))))
					b.Show(
						"a vanishing linear factor forces x to equal r",
						ByArith(ring, atRoot[0], values, given, linearValue, eitherZero))
				}))
			add, mul := a.TermAs[Op[A]]("M.add"), a.TermAs[Op[A]]("M.mul")
			zero, one := a.TermAs[A]("M.zero"), a.TermAs[A]("M.one")
			carrier := a.TermAs[Set[A]]("M.carrier")
			a.Show(
				"the product roots lie among the linear root and the cofactor roots",
				BySets(
					forced,
					polynomial_roots.PolynomialRootsDef.At(add, zero, mul, one, carrier, p),
					polynomial_roots.PolynomialRootsDef.At(add, zero, mul, one, carrier, q)))
		})
		containedRoots := ctx.Lemma(Statement{
			Binders: "∀M:field_on(A). ∀S:set(A). ∀n:num. ∀q:(num → A).",
			Hypotheses: []string{
				"subfield(M, S)",
				"polynomial_over(S, q)",
				"q ≠ vec_zero",
				"polynomial_splits(restrict_ring(field_ring(M), S), q)",
				"polynomial_degree(q) ≤ n",
			},
			Conclusion: "polynomial_roots(M.carrier, q) ⊆ S",
		}, func(a *Argument, M field.FieldFact[on.M], S *Expr[Set[A]], subfieldS Fact) {
			fieldM := a.TermAs[FieldOps[A]]("M")
			zero := a.TermAs[A]("M.zero")
			carrier := a.TermAs[Set[A]]("M.carrier")
			ringM := field.RingOn.Read(M)
			a.Induct("n")
			a.Base(
				"a nonzero constant polynomial has no roots",
				func(b *Argument) {
					q := b.FixAs[Fun[Nat, A]]("q")
					data := b.Assume()
					constant := b.Have(
						"q is a degree-zero polynomial over M",
						"polynomial_over(M.carrier, q) ∧ polynomial_degree(q) = 0",
						ByArith(
							subfieldS,
							data,
							field.SubfieldSubset.At(fieldM, S),
							polynomial.PolynomialOverMono.At(zero, S, carrier, q)))
					b.Show(
						"its empty root set lies in S",
						BySets(data, constant, polynomial_roots.DegreeZeroNoRoots.Read(ringM).At(q)))
				})
			a.Step(
				"remove one linear factor and use the smaller degree bound",
				func(b *Argument, ih Fact) {
					q := b.FixAs[Fun[Nat, A]]("q")
					data := b.Assume()
					b.Cases(b.TermAs[Bool]("polynomial_degree(q) ≤ n"))
					b.When(
						"the degree is already within the previous bound",
						func(c *Argument, bound Fact) {
							c.Show(
								"the induction hypothesis already contains every root",
								By(ih.At(q), bound, data))
						})
					b.Otherwise(
						"the polynomial has the next positive degree",
						func(c *Argument, above Fact) {
							positive := c.Have(
								"the remaining polynomial has positive degree",
								"0 < polynomial_degree(q)",
								ByArith(above))
							fieldS := c.Have(
								"S inherits its field structure from M",
								"field_on(restrict_field(M, S))",
								By(subfieldS, field.SubfieldFieldOn.Read(M).At(S)))
							r, root := c.ObtainAs[A](
								"splitting supplies a root in S",
								"∃r:A. r ∈ S ∧ polynomial_eval(q, r) = M.zero",
								By(
									positive,
									data,
									field.RestrictFieldRing.At(fieldM, S),
									separable_polynomial.SplitsRoot.Read(fieldS).At(q)))
							s, factor := c.ObtainAs[Fun[Nat, A]](
								"remove this root over S",
								"∃s:(num → A). "+
									"    polynomial_over(S, s) ∧ "+
									"    s ≠ vec_zero ∧ "+
									"    q = polynomial_mul(«linear»(r), s) ∧ "+
									"    polynomial_degree(q) = suc(polynomial_degree(s))",
								By(
									root,
									data,
									polynomial_roots.RootFactorization.Read(
										integral_domain.FieldIntegralDomain.Read(fieldS)).AsFact().At(
										q, r)))
							restrictedRing := field.RingOn.Read(fieldS)
							polynomialRing := polynomial.PolynomialRingOn.Read(restrictedRing)
							polynomialProducts := comm_ring.MulMonoidOn.Read(polynomialRing)
							linear := c.Have(
								"the linear factor is a polynomial over S",
								"polynomial_over(S, «linear»(r))",
								By(root, polynomial_roots.LinearFactor.Read(restrictedRing).AsFact().At(r)))
							commuted := c.Have(
								"commute the factors to exhibit the cofactor as a divisor",
								"q = polynomial_mul(s, «linear»(r))",
								By(
									factor,
									linear,
									comm_monoid.CommOn.Read(polynomialProducts).AsFact().At(s, c.TermAs[Fun[Nat, A]]("«linear»(r)"))))
							divides := c.Have(
								"the cofactor divides q over S",
								"polynomial_divides(restrict_ring(field_ring(M), S), s, q)",
								By(
									commuted,
									linear,
									polynomial_division.PolynomialDividesDef.At(
										c.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(M), S)"), s, q)))
							smaller := c.Have(
								"the cofactor splits and has degree at most n",
								"polynomial_splits(restrict_ring(field_ring(M), S), s) ∧ polynomial_degree(s) ≤ n",
								Derive(func(d *Argument) {
									ringS := d.Have(
										"the restricted coefficient ring is commutative",
										"comm_ring_on(restrict_ring(field_ring(M), S))",
										By(subfieldS, field.SubfieldCommRing.Read(M).At(S)))
									d.Show(
										"divisors inherit splitting, and removing a root lowers degree",
										ByArith(data, factor, divides, separable_polynomial.SplitsDivisor.Read(ringS).At(s, q)))
								}))
							cofactorRoots := c.Have(
								"induction puts every cofactor root in S",
								"polynomial_roots(M.carrier, s) ⊆ S",
								By(ih.At(s), smaller, factor))
							ambient := c.Have(
								"the root and cofactor also lie over M",
								"polynomial_over(M.carrier, s) ∧ r ∈ M.carrier",
								BySets(
									root,
									subfieldS,
									factor,
									field.SubfieldSubset.At(fieldM, S),
									polynomial.PolynomialOverMono.At(zero, S, carrier, s)))
							c.Show(
								"every root is the chosen root or a cofactor root, hence belongs to S",
								BySets(M, cofactorRoots, root, factor, ambient, At(linearProductRoots, fieldM, q, s, r)))
						})
				})
		})
		return ctx.Theorem(headline, func(
			a *Argument,
			M field.FieldFact[on.M],
			K *Expr[Set[A]],
			p *Arrow[Nat, A],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"M is algebraically closed",
				"K is a subfield",
				"p is over K",
				"p is not zero")
			closed, subK, overK, nonzero := parts[0], parts[1], parts[2], parts[3]
			fieldM := a.TermAs[FieldOps[A]]("M")
			zero := a.TermAs[A]("M.zero")
			carrier := a.TermAs[Set[A]]("M.carrier")
			add, mul, one := a.TermAs[Op[A]]("M.add"), a.TermAs[Op[A]]("M.mul"), a.TermAs[A]("M.one")
			roots := a.TermAs[Set[A]]("polynomial_roots(M.carrier, p)")
			E := a.TermAs[Set[A]]("«E»")
			ringM := field.RingOn.Read(M)
			rootDescription := polynomial_roots.PolynomialRootsDef.At(add, zero, mul, one, carrier, p)
			insideM := a.Have(
				"the base field and all the roots lie in M",
				"K ⊆ M.carrier ∧ polynomial_roots(M.carrier, p) ⊆ M.carrier",
				BySets(subK, field.SubfieldSubset.At(fieldM, K), rootDescription))
			ambientPolynomial := a.Have(
				"p is a nonzero polynomial over M",
				"polynomial_over(M.carrier, p) ∧ p ≠ vec_zero",
				By(nonzero, insideM, overK, polynomial.PolynomialOverMono.At(zero, K, carrier, p)))
			algebraicRoots := a.Have(
				"there are finitely many roots, each algebraic over K",
				"finite(polynomial_roots(M.carrier, p)) ∧ "+
					"(∀x:A. x ∈ polynomial_roots(M.carrier, p) ⇒ algebraic_over(M, K, x))",
				SplitConj(
					Case(
						"the nonzero polynomial has finitely many roots",
						By(
							ambientPolynomial,
							polynomial_roots.RootBound.Read(integral_domain.FieldIntegralDomain.Read(M)).At(p))),
					Case(
						"p witnesses algebraicity of every root",
						BySets(
							ambientPolynomial,
							overK,
							rootDescription,
							At(algebraic_element.AlgebraicOverDef.Inst[A](), fieldM, K)))))
			a.Show(
				"the root field is finite, splits p, and is least",
				SplitConjAll(
					Case(
						"finitely many algebraic generators give a finite extension",
						By(subK, algebraicRoots, insideM, algebraic_element.FiniteAlgebraicAdjoin.Read(M).At(K, roots))),
					Case(
						"p splits over the field generated by its roots",
						Derive(func(b *Argument) {
							adjoin := b.Have(
								"the root field contains K and every root",
								"subfield(M, «E») ∧ K ⊆ «E» ∧ polynomial_roots(M.carrier, p) ⊆ «E»",
								By(insideM, algebraic_element.AdjoinSubfield.Read(M).At(K, roots)))
							adjoinParts := b.Conjuncts(
								adjoin,
								"E is a subfield of M",
								"E contains K",
								"E contains all roots of p")
							b.Do(Unfold(separable_polynomial.PolynomialSplitsDef))
							q := b.FixAs[Fun[Nat, A]]("q")
							divisor := b.Conjuncts(
								b.Assume(),
								"q is irreducible over E",
								"q divides p over E")
							irreducible := b.Unfolded(divisor[0], polynomial_division.PolynomialIrreducibleDef)
							irrParts := b.Conjuncts(
								irreducible,
								"q is a polynomial over E",
								"q has positive degree",
								"an irreducible factorization has a constant factor")
							qAmbient := b.Have(
								"q is a polynomial over the ambient closed field",
								"polynomial_over(M.carrier, q)",
								By(
									adjoinParts[0],
									irrParts[0],
									field.SubfieldSubset.At(fieldM, E),
									polynomial.PolynomialOverMono.At(zero, E, carrier, q)))
							r, root := b.ObtainAs[A](
								"q has a root in M",
								"∃r:A. r ∈ M.carrier ∧ polynomial_eval(q, r) = M.zero",
								By(closed, irrParts[1], qAmbient, AlgebraicallyClosedDef.At(fieldM)))
							rootOfP := b.Have(
								"a root of the divisor is a root of p",
								"polynomial_eval(p, r) = M.zero",
								Derive(func(c *Argument) {
									s, product := c.UnpackAs[Fun[Nat, A]](
										c.Unfolded(divisor[1], polynomial_division.PolynomialDividesDef), "s")
									sAmbient := c.Have(
										"the cofactor is also a polynomial over M",
										"polynomial_over(M.carrier, s)",
										By(
											adjoinParts[0],
											product,
											field.SubfieldSubset.At(fieldM, E),
											polynomial.PolynomialOverMono.At(zero, E, carrier, s)))
									c.Show(
										"the vanishing factor makes the product vanish",
										By(
											Normalized,
											root,
											product,
											qAmbient,
											sAmbient,
											polynomial_evaluation.EvalMulRoot.Read(ringM).AsFact().At(q, s, r)))
								}))
							inE := b.Have(
								"this root belongs to the root field",
								"r ∈ «E»",
								BySets(rootOfP, adjoinParts[2], root, rootDescription))
							fieldE := b.Have(
								"the restriction to E is a field",
								"field_on(restrict_field(M, «E»))",
								By(adjoinParts[0], field.SubfieldFieldOn.Read(M).At(E)))
							b.Show(
								"an irreducible polynomial over E with a root in E is linear",
								By(
									divisor[0],
									root,
									field.RestrictFieldRing.At(fieldM, E),
									polynomial_roots.IrreducibleRootLinear.Read(integral_domain.FieldIntegralDomain.Read(fieldE)).At(
										q, b.MemberOf[on.Any](r, inE))))
						})),
					Case(
						"every subfield containing K over which p splits contains the root field",
						Derive(func(b *Argument) {
							S := b.FixAs[Set[A]]("S")
							candidate := b.Assume()
							overS := b.Have(
								"p is a polynomial over S since S contains K",
								"polynomial_over(S, p)",
								By(candidate, overK, polynomial.PolynomialOverMono.At(zero, K, S, p)))
							b.Show(
								"adjoining all the roots gives a subfield of S",
								By(
									candidate,
									ambientPolynomial,
									overS,
									At(containedRoots, fieldM, S, b.TermAs[Nat]("polynomial_degree(p)"), p),
									nat_order.LessEqRefl,
									algebraic_element.AdjoinLeast.Read(M).At(K, roots, S)))
						}))))
		})
	}),
})}
