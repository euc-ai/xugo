// fundamental_theorem.go — the modulus of a complex polynomial attains a
// global minimum, and that minimum is a root.

package complex_polynomial

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_closure"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_archimedean"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_topology"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/product_topology"
	"github.com/euc-ai/xugo/library/proofs/topology/real_valued"
	"github.com/euc-ai/xugo/library/registry"
)

// PolynomialPartsContinuous — a polynomial preserves continuity
// of the two complex parts: powers and finite sums preserve it.
var PolynomialPartsContinuous = polynomialPartsContinuousThm{family.Add(registry.ProofEntry{
	Name: "PolynomialPartsContinuous",
	Key:  "prop_d75d5d974236edc0",
	Build: family.Sections(Statement{
		Binders: "∀T:set(set(A)). ∀f:(A → complex). ∀P:(num → complex).",
		Hypotheses: []string{
			"is_topology(T)",
			"continuous_map(T, real_topology, λx:A. re(f(x)))",
			"continuous_map(T, real_topology, λx:A. im(f(x)))",
			"polynomial_over(𝕌, P)",
		},
		Conclusion: "continuous_map(T, real_topology, λx:A. re(polynomial_eval(P, f(x)))) ∧ " +
			"continuous_map(T, real_topology, λx:A. im(polynomial_eval(P, f(x))))",
	}, func(ctx *Script, headline string) *GoalStackNode {
		addParts := ctx.Lemma(Statement{
			Binders: "∀T:set(set(A)). ∀f g:(A → complex).",
			Hypotheses: []string{
				"is_topology(T)",
				"continuous_map(T, real_topology, λx:A. re(f(x)))",
				"continuous_map(T, real_topology, λx:A. im(f(x)))",
				"continuous_map(T, real_topology, λx:A. re(g(x)))",
				"continuous_map(T, real_topology, λx:A. im(g(x)))",
			},
			Conclusion: "continuous_map(T, real_topology, λx:A. re(f(x) + g(x))) ∧ " +
				"continuous_map(T, real_topology, λx:A. im(f(x) + g(x)))",
		}, func(a *Argument, T *Expr[Set[Set[A]]], f, g *Arrow[A, Complex], h Fact) {
			a.Do(Simp(Fwd(complex_field.ComplexAddDef)))
			a.Show(
				"addition is componentwise",
				By(h, real_valued.ContinuousRealAdd))
		})
		mulParts := ctx.Lemma(Statement{
			Binders: "∀T:set(set(A)). ∀f g:(A → complex).",
			Hypotheses: []string{
				"is_topology(T)",
				"continuous_map(T, real_topology, λx:A. re(f(x)))",
				"continuous_map(T, real_topology, λx:A. im(f(x)))",
				"continuous_map(T, real_topology, λx:A. re(g(x)))",
				"continuous_map(T, real_topology, λx:A. im(g(x)))",
			},
			Conclusion: "continuous_map(T, real_topology, λx:A. re(f(x) * g(x))) ∧ " +
				"continuous_map(T, real_topology, λx:A. im(f(x) * g(x)))",
		}, func(a *Argument, T *Expr[Set[Set[A]]], f, g *Arrow[A, Complex], h Fact) {
			a.Do(Simp(Fwd(complex_field.ComplexMulDef)), Simp(Fwd(real_ring.RealSubDef)))
			a.Show(
				"each part is a sum of products of continuous real maps",
				By(h, real_valued.ContinuousRealAdd, real_valued.ContinuousRealMul, real_valued.ContinuousRealNeg))
		})
		powers := ctx.Lemma(Statement{
			Binders: "∀T:set(set(A)). ∀f:(A → complex). ∀n:num.",
			Hypotheses: []string{
				"is_topology(T)",
				"continuous_map(T, real_topology, λx:A. re(f(x)))",
				"continuous_map(T, real_topology, λx:A. im(f(x)))",
			},
			Conclusion: "continuous_map(T, real_topology, λx:A. re(f(x) ^ n)) ∧ " +
				"continuous_map(T, real_topology, λx:A. im(f(x) ^ n))",
		}, func(a *Argument, T *Expr[Set[Set[A]]], f *Arrow[A, Complex], n *Expr[Nat], h Fact) {
			a.Induct(n)
			a.Base(
				"the zeroth power is constant",
				Simp(Fwd(comm_monoid.MonoidPowDef), Fwd(complex_field.ComplexOfRealDef)),
				By(Normalized, h, continuous.Constant, real_topology.RealSpace, set_basic.InUniv))
			a.Step(
				"multiply by one more copy of the map",
				func(b *Argument, ih Fact) {
					b.Do(Simp(Fwd(comm_monoid.MonoidPowDef)))
					b.Show(
						"the product has continuous parts",
						By(h, ih, mulParts))
				})
		})
		sums := ctx.Lemma(Statement{
			Binders: "∀T:set(set(A)). ∀F:(num → A → complex). ∀s:set(num).",
			Hypotheses: []string{
				"is_topology(T)", "finite(s)",
				"∀i:num. " +
					"    i ∈ s ⇒ " +
					"    continuous_map(T, real_topology, λx:A. re(F(i, x))) ∧ " +
					"    continuous_map(T, real_topology, λx:A. im(F(i, x)))",
			},
			Conclusion: "continuous_map(T, " +
				"    real_topology, " +
				"    λx:A. re(module_sum(complex_add, &0, s, λi:num. F(i, x)))) ∧ " +
				"continuous_map(T, real_topology, λx:A. im(module_sum(complex_add, &0, s, λi:num. F(i, x))))",
		}, func(a *Argument, T *Expr[Set[Set[A]]], F *Arrow2[Nat, A, Complex], s *Expr[Set[Nat]], h Fact) {
			a.Show(
				"finite sums preserve continuity of both parts",
				ByInduction(finite_set.FiniteInductFreshOn, h,
					Case(
						"the empty sum is constant zero",
						Simp(Fwd(module.ModuleSumEmpty), Fwd(complex_field.ComplexOfRealDef)),
						By(Normalized, h, continuous.Constant, real_topology.RealSpace, set_basic.InUniv)),
					Case(
						"insert one further continuous summand",
						Derive(func(b *Argument) {
							i := b.FixAs[Nat]("i")
							U := b.FixAs[Set[Nat]]("U")
							step := b.Assume()
							additive := comm_ring.AddMonoidOn.Read(complex_field.CommRingOn)
							inserted := b.Have(
								"the fresh sum is its new term plus the old sum",
								"∀y:A. "+
									"    module_sum(complex_add, &0, insert(i, U), λj:num. F(j, y)) = "+
									"    F(i, y) + module_sum(complex_add, &0, U, λj:num. F(j, y))",
								Derive(func(c *Argument) {
									c.FixAs[A]("y")
									c.Show(
										"the sum recursion holds at each source point",
										By(
											step,
											module.ModuleSumInsertMonoid.Read(additive).At(
												U, i, c.TermAs[Fun[Nat, Complex]]("λj:num. F(j, y)")),
											set_basic.InUniv.Inst[Complex]()))
								}))
							b.Do(Simp(Fwd(inserted)))
							b.Show(
								"addition preserves the two continuous parts",
								By(h, step, addParts))
						}))))
		})
		return ctx.Theorem(headline, func(
			a *Argument,
			T *Expr[Set[Set[A]]],
			f *Arrow[A, Complex],
			P *Arrow[Nat, Complex],
			h Fact,
		) {
			topology := a.TermAs[Set[Set[Real]]]("real_topology")
			support := a.Have(
				"only finitely many coefficients are nonzero",
				"finite(fun_support⟨A:num, B:complex⟩(&0, P))",
				By(
					h,
					polynomial.PolynomialFiniteSupport.At(
						a.TermAs[Complex]("complex_of_real(&0)"), a.TermAs[Set[Complex]]("𝕌"), P)))
			monomials := a.Have(
				"every monomial has continuous real and imaginary parts",
				"∀i:num. "+
					"    continuous_map(T, real_topology, λx:A. re(P(i) * f(x) ^ i)) ∧ "+
					"    continuous_map(T, real_topology, λx:A. im(P(i) * f(x) ^ i))",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					coefficient := b.Have(
						"each coefficient gives two constant real maps",
						"continuous_map(T, real_topology, λx:A. re(P(i))) ∧ "+
							"continuous_map(T, real_topology, λx:A. im(P(i)))",
						By(
							h,
							continuous.Constant.At(T, topology, b.TermAs[Real]("re(P(i))")),
							continuous.Constant.At(T, topology, b.TermAs[Real]("im(P(i))")),
							real_topology.RealSpace,
							set_basic.InUniv.Inst[Real]()))
					b.Show(
						"a coefficient times a continuous power has continuous parts",
						By(
							h,
							coefficient,
							At(powers, T, f, i),
							At(mulParts, T, b.TermAs[Fun[A, Complex]]("λx:A. P(i)"),
								b.TermAs[Fun[A, Complex]]("λx:A. f(x) ^ i"))))
				}))
			a.Do(Simp(Fwd(polynomial_evaluation.PolynomialEvalDef)))
			a.Show(
				"polynomial evaluation is the finite sum of its monomials",
				By(
					support,
					monomials,
					h,
					At(sums, T,
						a.TermAs[Fun[Nat, Fun[A, Complex]]]("λi:num. λx:A. P(i) * f(x) ^ i"),
						a.TermAs[Set[Nat]]("fun_support⟨A:num, B:complex⟩(&0, P)"))))
		})
	}),
})}

// PolynomialModulusSquareContinuous — the squared modulus of a
// complex polynomial is continuous on the real coordinate plane.
var PolynomialModulusSquareContinuous = polynomialModulusSquareContinuousThm{family.Add(registry.ProofEntry{
	Name: "PolynomialModulusSquareContinuous",
	Key:  "prop_72da30b3fc33b3dd",
	Build: family.Theorem(Statement{
		Binders:    "∀P:(num → complex).",
		Hypotheses: []string{"polynomial_over(𝕌, P)"},
		Conclusion: "continuous_map(product_topology(real_topology, real_topology), " +
			"    real_topology, " +
			"    λu:prod(real, real). |«value»(u)| * |«value»(u)|)",
		Abbrev: Abbrev{
			{Name: "value", Text: "λu:prod(real, real). polynomial_eval(P, complex(fst(u), snd(u)))"},
		},
	}, func(a *Argument, P *Arrow[Nat, Complex], over Fact) {
		topology := a.TermAs[Set[Set[Real]]]("real_topology")
		parts := a.Have(
			"the coordinate projections give continuous polynomial parts",
			"continuous_map(product_topology(real_topology, real_topology), "+
				"    real_topology, "+
				"    λu:prod(real, real). re(«value»(u))) ∧ "+
				"continuous_map(product_topology(real_topology, real_topology), "+
				"    real_topology, "+
				"    λu:prod(real, real). im(«value»(u)))",
			By(
				over,
				product_topology.ProductTopology.At(topology, topology),
				real_topology.RealTopology,
				product_topology.FstContinuous.At(topology, topology),
				product_topology.SndContinuous.At(topology, topology),
				PolynomialPartsContinuous.At(
					a.TermAs[Set[Set[Prod[Real, Real]]]]("product_topology(real_topology, real_topology)"),
					a.TermAs[Fun[Prod[Real, Real], Complex]]("λu:prod(real, real). complex(fst(u), snd(u))"),
					P)))
		a.Do(Simp(Fwd(complex_abs.AbsSquare)))
		a.Show(
			"the squared modulus is the sum of the squared parts",
			By(
				parts,
				product_topology.ProductTopology.At(topology, topology),
				real_topology.RealTopology,
				real_valued.ContinuousRealAdd,
				real_valued.ContinuousRealMul))
	}),
})}

// PolynomialCoercive — the modulus of a positive-degree complex
// polynomial eventually exceeds any prescribed real bound: its leading
// term grows one power faster than the sum of all lower terms.
var PolynomialCoercive = polynomialCoerciveThm{family.Add(registry.ProofEntry{
	Name: "PolynomialCoercive",
	Key:  "prop_ca036251b78626d8",
	Build: family.Sections(Statement{
		Binders: "∀P:(num → complex). ∀B:real.",
		Hypotheses: []string{
			"polynomial_over(𝕌, P)",
			"0 < polynomial_degree(P)",
		},
		Conclusion: "∃R:real. &0 < R ∧ (∀z:complex. R ≤ |z| ⇒ B ≤ |polynomial_eval(P, z)|)",
	}, func(ctx *Script, headline string) *GoalStackNode {
		leadingPlusLower := ctx.Lemma(Statement{
			Binders:    "∀P:(num → complex). ∀d:num. ∀z:complex.",
			Hypotheses: []string{"polynomial_over(𝕌, P)", "polynomial_degree(P) = d"},
			Conclusion: "polynomial_eval(P, z) = " +
				"P(d) * z ^ d + module_sum(complex_add, &0, {i:num | i < d}, λi:num. P(i) * z ^ i)",
		}, func(arg *Argument, P *Arrow[Nat, Complex], d *Expr[Nat], z *Expr[Complex], h Fact) {
			throughLeading := arg.Have(
				"evaluation sums every coefficient through the leading one",
				"polynomial_eval(P, z) = module_sum(complex_add, &0, {i:num | i < suc(d)}, λi:num. P(i) * z ^ i)",
				By(
					h,
					polynomial_evaluation.EvalBelowDegree.Read(complex_field.CommRingOn).AsFact().At(P, z),
					complex_field.ComplexRingDef,
					set_basic.InUniv.Inst[Complex]()))
			arg.Show(
				"split the leading coefficient from the lower terms",
				throughLeading.Simp(Fwd(num_segment.BelowStrictClauses)),
				By(
					throughLeading,
					num_segment.FiniteBelowStrict.At(d),
					set_basic.InUniv.Inst[Complex](),
					nat_order.LessThanIrrefl.At(d),
					module.ModuleSumInsertMonoid.Read(comm_ring.AddMonoidOn.Read(complex_field.CommRingOn)).At(
						arg.TermAs[Set[Nat]]("{i:num | i < d}"), d,
						arg.TermAs[Fun[Nat, Complex]]("λi:num. P(i) * z ^ i"))))
		})
		return ctx.Theorem(headline, func(arg *Argument, P *Arrow[Nat, Complex], B *Expr[Real], poly Fact) {
			zero := arg.TermAs[Complex]("complex_of_real(&0)")
			universe := arg.TermAs[Set[Complex]]("𝕌")
			d, degreeDef := arg.LetAs[Nat]("d", "polynomial_degree(P)")
			nonzero := arg.Have(
				"positive degree rules out the zero polynomial",
				"P ≠ vec_zero(complex_of_real(&0))",
				ByArith(degreeDef, poly, polynomial.DegreeVecZero.At(zero)))
			leadingNonzero := arg.Have(
				"the leading coefficient of the nonzero polynomial is nonzero",
				"P(d) ≠ &0",
				By(Normalized, nonzero, degreeDef, poly, polynomial.DegreeLeading.At(zero, universe, P)))
			leading, leadingDef := arg.LetAs[Real]("a", "|P(d)|")
			positive := arg.Have(
				"the leading coefficient has positive modulus",
				"&0 < a",
				By(Normalized, leadingNonzero, leadingDef, complex_abs.AbsPosIffNonzero.At(P.Apply(d))))
			_, coefficientsDef := arg.LetAs[Real]("C", "sum({i:num | i < d}, λi:num. |P(i)|)")
			_, threshold := arg.ObtainAs[Nat](
				"an Archimedean multiple of the leading modulus dominates the lower coefficients and target",
				"∃N:num. C + |B| < &N * a",
				By(positive, real_archimedean.Archimedean.At(leading, arg.TermAs[Real]("C + |B|"))))
			arg.Take(arg.TermAs[Real]("&N + &1"))
			arg.Do(SplitConj(
				Case(
					"the chosen radius is positive",
					ByArith()),
				Case(
					"outside that radius the leading term dominates",
					Derive(func(b *Argument) {
						z := b.FixAs[Complex]("z")
						far := b.Assume()
						radius, radiusDef := b.LetAs[Real]("r", "|z|")
						_, leadDef := b.LetAs[Complex]("lead", "P(d) * z ^ d")
						tail, tailDef := b.LetAs[Complex](
							"tail", "module_sum(complex_add, complex_of_real(&0), {i:num | i < d}, λi:num. P(i) * z ^ i)")
						value, valueDef := b.LetAs[Complex]("v", "polynomial_eval(P, z)")
						decomposition := b.Have(
							"the value is the leading term plus the lower terms",
							"v = lead + tail",
							By(leadDef, tailDef, valueDef, degreeDef, poly, At(leadingPlusLower, P, d, z)))
						withoutTail := b.Have(
							"subtracting the tail recovers the leading term",
							"v + -tail = lead",
							ByArith(decomposition, complex_field.CommRing))
						triangle := b.Have(
							"the leading modulus is at most the value modulus plus the tail modulus",
							"|lead| ≤ |v| + |tail|",
							By(
								Normalized,
								withoutTail,
								complex_abs.AbsTriangle.At(value, b.TermAs[Complex]("-tail")),
								complex_abs.AbsNeg.At(tail)))
						outside := b.Have(
							"the radius is at least one",
							"&1 ≤ r",
							ByArith(far))
						leadModulus := b.Have(
							"the leading modulus is its coefficient modulus times the degree power",
							"|lead| = a * r ^ d",
							leadDef.Rw(),
							ByArith(leadingDef, radiusDef))
						tailBound := b.Have(
							"all lower terms grow at most as the preceding power",
							"|tail| ≤ C * r ^ (d - 1)",
							ByArith(tailDef, coefficientsDef, radiusDef, outside, PolynomialLowerTermsBound.At(d, P, z)))
						predecessor := b.Have(
							"the positive degree has a predecessor",
							"d = (d - 1) + 1",
							ByArith(poly))
						factor := b.Have(
							"the leading power has one more factor of the radius",
							"r ^ d = r * r ^ (d - 1)",
							By(predecessor, real_pow.PowAddOne))
						remaining := b.Have(
							"the remaining power is at least one",
							"&1 ≤ r ^ (d - 1)",
							By(outside, real_pow.OneLessEqPow.At(radius, b.TermAs[Nat]("d - 1"))))
						gap := b.Have(
							"the leading coefficient times the radius dominates the lower coefficients and target",
							"|B| < a * r - C",
							ByArith(far, positive, threshold))
						lower := b.Have(
							"the leading-minus-tail estimate gives the scaled coefficient gap",
							"(a * r - C) * r ^ (d - 1) ≤ |v|",
							ByArith(leadModulus, Scaled(leading, factor), triangle, tailBound))
						amplified := b.Have(
							"the remaining power enlarges the positive coefficient gap",
							"a * r - C ≤ (a * r - C) * r ^ (d - 1)",
							ByArith(
								remaining,
								gap,
								real_order_ring.LessEqMulLeft.At(
									b.TermAs[Real]("a * r - C"), b.TermAs[Real]("&1"), b.TermAs[Real]("r ^ (d - 1)"))))
						b.Show(
							"the polynomial modulus exceeds the prescribed bound",
							ByArith(lower, amplified, gap))
					}))))
		})
	}),
})}

// PolynomialGlobalMinimum — the modulus of a nonconstant complex polynomial
// attains a global minimum. The squared modulus is what is minimized on a
// coordinate square: it is a polynomial expression in the two parts, so its
// continuity comes from PolynomialModulusSquareContinuous without a
// continuity law for the modulus. Outside a large enough square some part
// exceeds the radius, so the modulus there is at least the value at zero, a
// point of the square.
var PolynomialGlobalMinimum = polynomialGlobalMinimumThm{family.Add(registry.ProofEntry{
	Name: "PolynomialGlobalMinimum",
	Key:  "prop_753775c6924db98a",
	Build: family.Sections(Statement{
		Binders:    "∀P:(num → complex).",
		Hypotheses: []string{"polynomial_over(𝕌, P)", "0 < polynomial_degree(P)"},
		Conclusion: "∃a:complex. ∀w:complex. |«value»(a)| ≤ |«value»(w)|",
		Abbrev: Abbrev{
			{Name: "value", Text: "λz:complex. polynomial_eval(P, z)"},
			{Name: "modulusSquare", Text: "λz:complex. |«value»(z)| * |«value»(z)|"},
			{Name: "square", Text: "set_cross(⟦-R, R⟧, ⟦-R, R⟧)"},
			{Name: "planeValue", Text: "λu:prod(real, real). «modulusSquare»(complex(fst(u), snd(u)))"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		compareSquares := ctx.Lemma(Statement{
			Binders:    "∀x y:complex.",
			Hypotheses: []string{"|x| * |x| ≤ |y| * |y|"},
			Conclusion: "|x| ≤ |y|",
		}, func(arg *Argument, x, y *Expr[Complex], squares Fact) {
			arg.Show(
				"squaring is strictly increasing on nonnegative moduli",
				ByArith(
					squares,
					complex_abs.AbsNonneg.At(x),
					complex_abs.AbsNonneg.At(y),
					real_pow.PowMonoBaseStrict.At(
						arg.TermAs[Real]("|y|"), arg.TermAs[Real]("|x|"), arg.TermAs[Nat]("2")),
					real_pow.PowTwo.At(arg.TermAs[Real]("|y|")),
					real_pow.PowTwo.At(arg.TermAs[Real]("|x|"))))
		})
		return ctx.Theorem(headline, func(arg *Argument, P *Arrow[Nat, Complex], h Fact) {
			topology := arg.TermAs[Set[Set[Real]]]("real_topology")
			R, growth := arg.ObtainAs[Real](
				"outside a positive radius the modulus reaches the value at zero",
				"∃R:real. &0 < R ∧ (∀z:complex. R ≤ |z| ⇒ |«value»(complex_of_real(&0))| ≤ |«value»(z)|)",
				By(h, PolynomialCoercive.At(P, arg.TermAs[Real]("|«value»(complex_of_real(&0))|"))))
			parts := arg.Conjuncts(
				growth,
				"the radius is positive",
				"and beyond it the modulus reaches the value at zero")
			positive, beyond := parts[0], parts[1]
			corner := arg.Have(
				"the upper corner lies in the square",
				"(R, R) ∈ «square»",
				Simp(Fwd(set_product.InCross)),
				ByArith(positive))
			nonempty := arg.Have(
				"so the square is nonempty",
				"«square» ≠ ∅",
				BySets(corner))
			_, attained := arg.ObtainAs[Prod[Real, Real]](
				"the squared modulus attains a least value on the compact square",
				"∃u:prod(real, real). "+
					"    u ∈ «square» ∧ (∀v:prod(real, real). v ∈ «square» ⇒ «planeValue»(u) ≤ «planeValue»(v))",
				By(
					h,
					nonempty,
					PolynomialModulusSquareContinuous.At(P),
					product_topology.CompactProduct.At(topology, topology,
						arg.TermAs[Set[Real]]("⟦-R, R⟧"), arg.TermAs[Set[Real]]("⟦-R, R⟧")),
					real_topology.RealTopology,
					real_topology.ClosedIntervalCompact.At(arg.TermAs[Real]("-R"), R),
					real_valued.ContinuousCompactMinimum.At(
						arg.TermAs[Set[Set[Prod[Real, Real]]]]("product_topology(real_topology, real_topology)"),
						arg.TermAs[Fun[Prod[Real, Real], Real]]("«planeValue»"),
						arg.TermAs[Set[Prod[Real, Real]]]("«square»"))),
				Named("u"))
			a, _ := arg.LetAs[Complex]("a", "complex(fst(u), snd(u))")
			onSquare := arg.Have(
				"on the square a minimizes the modulus itself",
				"∀w:complex. |re(w)| ≤ R ∧ |im(w)| ≤ R ⇒ |«value»(a)| ≤ |«value»(w)|",
				Derive(func(b *Argument) {
					b.FixAs[Complex]("w")
					bounds := b.Assume()
					coordinates := b.Have(
						"the coordinates of w lie in the square",
						"(re(w), im(w)) ∈ «square»",
						By(
							bounds,
							set_product.InCross.At(b.TermAs[Set[Real]]("⟦-R, R⟧"), b.TermAs[Set[Real]]("⟦-R, R⟧"),
								b.TermAs[Real]("re(w)"), b.TermAs[Real]("im(w)")),
							real_sgn_abs.AbsBounds.At(b.TermAs[Real]("re(w)"), R),
							real_sgn_abs.AbsBounds.At(b.TermAs[Real]("im(w)"), R)))
					reconstruct := b.Have(
						"the parts reconstruct w",
						"complex(re(w), im(w)) = w",
						By(complex_field.ComplexEq, complex_field.ComplexReDef, complex_field.ComplexImDef))
					compared := b.Have(
						"the least value is at most the value at those coordinates",
						"«modulusSquare»(a) ≤ «planeValue»((re(w), im(w)))",
						By(coordinates, attained))
					b.Do(compared.Simp(Fwd(pairs.Fst), Fwd(pairs.Snd), Fwd(reconstruct)))
					b.Show(
						"comparing squares compares the moduli",
						By(
							compared,
							At(compareSquares, arg.TermAs[Complex]("«value»(a)"), b.TermAs[Complex]("«value»(w)"))))
				}))
			zeroInSquare := arg.Have(
				"zero lies in the square",
				"|re(&0)| ≤ R ∧ |im(&0)| ≤ R",
				Simp(
					Fwd(complex_field.ComplexOfRealDef),
					Fwd(complex_field.ComplexReDef),
					Fwd(complex_field.ComplexImDef)),
				ByArith(positive))
			atZero := arg.Have(
				"so the minimum is at most the value at zero",
				"|«value»(a)| ≤ |«value»(complex_of_real(&0))|",
				By(zeroInSquare, onSquare.At(arg.TermAs[Complex]("complex_of_real(&0)"))))
			arg.Take(a)
			w := arg.FixAs[Complex]("w")
			arg.Cases(arg.TermAs[Bool]("|re(w)| ≤ R ∧ |im(w)| ≤ R"))
			arg.When(
				"a point of the square compares by the square minimum",
				func(b *Argument, inside Fact) {
					b.Show(
						"the minimum on the square",
						By(inside, onSquare.At(w)))
				})
			arg.Otherwise(
				"outside the square some part exceeds the radius",
				func(b *Argument, outside Fact) {
					far := b.Have(
						"so the modulus of w reaches the radius",
						"R ≤ |w|",
						ByArith(outside, complex_abs.ReLessEqAbs.At(w), complex_abs.ImLessEqAbs.At(w)))
					b.Show(
						"and the value at w reaches the value at zero, which the minimum does not exceed",
						ByArith(atZero, beyond.At(w), far))
				})
		})
	}),
})}

// PolynomialHasRoot — the modulus attains a global minimum, and a nonzero
// minimum contradicts the inward perturbation of the translated polynomial's
// first nonconstant term.
var PolynomialHasRoot = polynomialHasRootThm{family.Add(registry.ProofEntry{
	Name: "PolynomialHasRoot",
	Key:  "prop_c3f7f21eca68fc27",
	Build: family.Sections(Statement{
		Binders:    "∀P:(num → complex).",
		Hypotheses: []string{"polynomial_over(𝕌, P)", "0 < polynomial_degree(P)"},
		Conclusion: "∃z:complex. «value»(z) = &0",
		Abbrev:     Abbrev{{Name: "value", Text: "λz:complex. polynomial_eval(P, z)"}},
	}, func(ctx *Script, headline string) *GoalStackNode {
		nonconstantTranslate := ctx.Lemma(Statement{
			Binders: "∀P Q:(num → complex). ∀a:complex.",
			Hypotheses: []string{
				"polynomial_over(𝕌, P)",
				"0 < polynomial_degree(P)",
				"polynomial_over(𝕌, Q)",
				"∀w:complex. polynomial_eval(Q, w) = «value»(a + w)",
			},
			Conclusion: "0 < polynomial_degree(Q)",
		}, func(
			arg *Argument,
			P, Q *Arrow[Nat, Complex],
			a *Expr[Complex],
			over, positive, qOver, translation Fact,
		) {
			notPositive := arg.SupposeNot()
			degreeZero := arg.Have(
				"a nonpositive natural degree is zero",
				"polynomial_degree(Q) = 0",
				ByArith(notPositive))
			constant := arg.Have(
				"a polynomial of degree zero takes its constant coefficient everywhere",
				"∀w:complex. polynomial_eval(Q, w) = Q(0)",
				arg.ForEach(func(w *Expr[Complex]) Action {
					return By(
						qOver,
						degreeZero,
						polynomial_evaluation.DegreeZeroEval.Read(complex_field.CommRingOn).AsFact().At(Q, w),
						complex_field.ComplexRingDef,
						set_basic.InUniv.At(w))
				}))
			_, growth := arg.ObtainAs[Real](
				"far enough out the modulus exceeds the modulus at a by a margin",
				"∃R:real. &0 < R ∧ (∀z:complex. R ≤ |z| ⇒ |«value»(a)| + &1 ≤ |«value»(z)|)",
				By(over, positive, PolynomialCoercive.At(P, arg.TermAs[Real]("|«value»(a)| + &1"))))
			outside := arg.Have(
				"the real point R reaches that radius",
				"R ≤ |complex_of_real(R)|",
				Simp(Fwd(complex_abs.AbsOfReal)),
				ByArith())
			comparison := arg.Have(
				"so its modulus exceeds the modulus at a",
				"|«value»(a)| + &1 ≤ |«value»(complex_of_real(R))|",
				By(outside, growth))
			shift := arg.TermAs[Complex]("complex_of_real(R) - a")
			zero := arg.TermAs[Complex]("complex_of_real(&0)")
			zeroShift := arg.Have(
				"translation by zero fixes a",
				"a + &0 = a",
				ByArith(complex_field.CommRing))
			cancel := arg.Have(
				"translation by R − a reaches R",
				"a + (complex_of_real(R) - a) = complex_of_real(R)",
				ByArith(complex_field.CommRing))
			equalValues := arg.Have(
				"a constant translate equates the two values",
				"«value»(complex_of_real(R)) = «value»(a)",
				By(
					zeroShift,
					cancel,
					constant.At(shift),
					constant.At(zero),
					translation.At(shift),
					translation.At(zero)))
			margin := arg.Simplified(comparison, Fwd(equalValues))
			arg.Show(
				"which leaves no margin",
				ByArith(margin))
		})
		return ctx.Theorem(headline, func(arg *Argument, P *Arrow[Nat, Complex], h Fact) {
			a, minimum := arg.ObtainAs[Complex](
				"the modulus attains a global minimum",
				"∃a:complex. ∀w:complex. |«value»(a)| ≤ |«value»(w)|",
				By(h, PolynomialGlobalMinimum.At(P)))
			arg.Cases(arg.TermAs[Bool]("«value»(a) = &0"))
			arg.When(
				"a zero minimum supplies the root",
				func(b *Argument, root Fact) {
					b.Take(a)
					b.Show(
						"the minimizing point is a root",
						By(root))
				})
			arg.Otherwise(
				"a nonzero minimum is impossible",
				func(b *Argument, nonzeroMinimum Fact) {
					Q, translation := b.ObtainAs[Fun[Nat, Complex]](
						"translate the polynomial to its minimizing point",
						"∃Q:(num → complex). polynomial_over(𝕌, Q) ∧ (∀w:complex. polynomial_eval(Q, w) = «value»(a + w))",
						By(
							h,
							polynomial_evaluation.EvalTranslate.Read(complex_field.CommRingOn).AsFact().At(P, a),
							complex_field.ComplexRingDef,
							set_basic.InUniv.Inst[Complex]()))
					zeroShift := b.Have(
						"translation by zero fixes the minimizing point",
						"a + &0 = a",
						ByArith(complex_field.CommRing))
					constant := b.Have(
						"the translated constant coefficient is the minimum value",
						"Q(0) = «value»(a)",
						By(
							zeroShift,
							translation,
							polynomial_evaluation.EvalAtZero.Read(complex_field.CommRingOn).At(Q),
							complex_field.ComplexRingDef,
							set_basic.InUniv.Inst[Complex]()))
					_, decrease := b.ObtainAs[Complex](
						"perturb the nonconstant translate to decrease its modulus",
						"∃w:complex. |polynomial_eval(Q, w)| < |Q(0)|",
						By(
							nonzeroMinimum,
							constant,
							translation,
							At(nonconstantTranslate, P, Q, a),
							h,
							PolynomialStrictDecrease.At(Q)))
					translatedDecrease := b.Simplified(decrease, Fwd(translation), Fwd(constant))
					b.Show(
						"strict decrease contradicts global minimality",
						ByArith(translatedDecrease, minimum.At(b.TermAs[Complex]("a + w"))))
				})
		})
	}),
})}

// AlgebraicallyClosed — the fundamental theorem of algebra in the form the
// algebraic closure chapter states it, the complex field being algebraically
// closed: the definition unfolds to a root of each nonconstant polynomial,
// and PolynomialHasRoot supplies it.
var AlgebraicallyClosed = algebraicallyClosedThm{family.Add(registry.ProofEntry{
	Name: "AlgebraicallyClosed",
	Key:  "prop_829859f807b0eca1",
	Build: family.Theorem("algebraically_closed_field(complex_field_ops)", func(arg *Argument) {
		arg.Do(Simp(Fwd(algebraic_closure.AlgebraicallyClosedDef), Fwd(complex_field.ComplexFieldOpsDef)))
		Q := arg.FixAs[Fun[Nat, Complex]]("Q")
		over := arg.Assume()
		z, root := arg.ObtainAs[Complex](
			"root existence applies to this nonconstant complex polynomial",
			"∃z:complex. polynomial_eval(Q, z) = &0",
			By(over, PolynomialHasRoot.At(Q)))
		arg.Take(z)
		arg.Show(
			"the chosen root belongs to the whole complex carrier",
			By(root, set_basic.InUniv.At(z)))
	}),
})}
