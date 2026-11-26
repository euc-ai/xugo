// closure.go — the elements of a field integral over a subring form a
// subring holding it, and a root of a monic polynomial over the field,
// scaled by a member of the subring that clears its coefficients, is
// integral over it. An element algebraic over a subfield is integral over
// the subfield, and one integral over a set is integral over any larger
// set.

package integral_element

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// IntegralAddNegMul — the sum, the negative and the product of two elements
// of a field integral over a subring S are integral over S. The powers of x
// below the degree of its monic relation span S[x] over S, and those of y
// span S[x][y] over S[x]; so the finitely many products of the two span
// S[x][y] over S, and every element of that subring, x + y, −x and x·y among
// them, is integral over S (FinitelySpannedIntegral).
var IntegralAddNegMul = integralAddNegMulThm{family.Add(registry.ProofEntry{
	Name: "IntegralAddNegMul",
	Key:  "prop_de03d9454bff0568",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S:set(A). ∀x y:A.",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"x ∈ L.carrier",
			"y ∈ L.carrier",
			"integral_over(«R», x)",
			"integral_over(«R», y)",
		},
		Conclusion: "integral_over(«R», x + y) ∧ integral_over(«R», -x) ∧ integral_over(«R», x * y)",
		Abbrev: Abbrev{
			{Name: "R", Text: "restrict_ring(field_ring(L), S)"},
			{Name: "Sx", Text: "polynomial_image(field_ring(L), S, x)"},
			{Name: "Sxy", Text: "polynomial_image(field_ring(L), «Sx», y)"},
			{Name: "powers", Text: "λw:A. λf:(num → A). " +
				"    {monoid_pow(L.mul, L.one, w, i) | i:num | i < polynomial_degree(f)}"},
			{Name: "products", Text: "λU:set(A). λV:set(A). {b * c | b:A, c:A | b ∈ U ∧ c ∈ V}"},
		},
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		S *Expr[Set[A]],
		x, y *Expr[A],
		subS, xIn, yIn, integralX, integralY Fact,
	) {
		ring := field.RingOn.Read(L)
		c := a.TermAs[RingOps[A]]("field_ring(L)")
		scalars := a.TermAs[RingOps[A]]("«R»")
		vectors := a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))")
		xm := a.MemberOf[on.L](x, xIn)
		ym := a.MemberOf[on.L](y, yIn)
		Sx, Sxy := a.TermAs[Set[A]]("«Sx»"), a.TermAs[Set[A]]("«Sxy»")
		adjoinedX := a.Conjuncts(
			GroupPremises(subS, algebraic_element.PolynomialImageSubring.Read(L).At(S, xm)),
			"S[x] is a subring of L",
			"S lies in S[x]",
			"x lies in S[x]")
		subSx, SInSx := adjoinedX[0], adjoinedX[1]
		adjoinedY := a.Conjuncts(
			GroupPremises(subSx, algebraic_element.PolynomialImageSubring.Read(L).At(Sx, ym)),
			"S[x][y] is a subring of L",
			"S[x] lies in S[x][y]",
			"y lies in S[x][y]")
		subSxy := adjoinedY[0]
		p, relationX := a.UnpackAs[Fun[Nat, A]](a.Unfolded(integralX, IntegralOverDef), "p")
		q, relationY := a.UnpackAs[Fun[Nat, A]](a.Unfolded(integralY, IntegralOverDef), "q")
		powersX, powersY := a.TermAs[Set[A]]("«powers»(x, p)"), a.TermAs[Set[A]]("«powers»(y, q)")
		products := a.TermAs[Set[A]]("«products»(«powers»(x, p), «powers»(y, q))")

		spanX := a.Have(
			"the powers of x below the degree of p span S[x] over S",
			"«Sx» = module_span(«R», regular_module(field_ring(L)), «powers»(x, p))",
			By(subS, xIn, relationX, IntegralPowerSpan.Read(L).At(S, xm, p)))
		overSx := a.Have(
			"q, over S, is over S[x]",
			"polynomial_over(«Sx», q)",
			By(relationY, SInSx, polynomial.PolynomialOverMono.At(a.TermAs[A]("L.zero"), S, Sx, q)))
		spanY := a.Have(
			"the powers of y below the degree of q span S[x][y] over S[x]",
			"«Sxy» = "+
				"module_span(restrict_ring(field_ring(L), «Sx»), regular_module(field_ring(L)), «powers»(y, q))",
			By(subSx, yIn, overSx, relationY, IntegralPowerSpan.Read(L).At(Sx, ym, q)))
		space := a.Have(
			"L is a module over S",
			"module_on(«R», regular_module(field_ring(L)))",
			By(subS, module.RegularModuleOverSubring.Read(ring).At(S)))
		restrictedX := a.Have(
			"S[x], a submodule of L over S, is spanned by the powers of x as a module of its own",
			"module_span(«R», restrict_module(regular_module(field_ring(L)), «Sx»), «powers»(x, p)) = «Sx»",
			By(
				space,
				subS,
				spanX,
				PolynomialImageSubmodule.Read(L).At(S, xm),
				submodule.SubsetSpan.At(scalars, vectors, powersX),
				linear_independence.SpanRestrict.At(scalars, vectors, Sx, powersX)))
		powersYIn := a.Have(
			"the powers of y lie in L",
			"«powers»(y, q) ⊆ L.carrier",
			BySets(comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ring)), yIn))
		tower := a.Have(
			"so the products of a power of x and a power of y span S[x][y] over S",
			"module_span(«R», regular_module(field_ring(L)), «products»(«powers»(x, p), «powers»(y, q))) = "+
				"«Sxy»",
			By(
				SInSx,
				subS,
				subSx,
				powersYIn,
				restrictedX,
				spanY,
				fractional_ideal.SubringTowerSpan.Read(L).At(S, Sx, Sxy, powersX, powersY)))
		finitePowers := a.Have(
			"an element has finitely many powers below the degree of a polynomial",
			"∀w:A. ∀f:(num → A). finite(«powers»(w, f))",
			Derive(func(b *Argument) {
				b.FixAs[A]("w")
				b.FixAs[Fun[Nat, A]]("f")
				segment := b.Have(
					"they are the image of an initial segment of the exponents",
					"«powers»(w, f) = "+
						"image(λi:num. monoid_pow(L.mul, L.one, w, i), {i:num | i < polynomial_degree(f)})",
					BySets())
				b.Show(
					"a finite image is finite",
					segment.Rw(),
					By(num_segment.FiniteBelowStrict, finite_set.FiniteImage))
			}))
		finiteProducts := a.Have(
			"so there are finitely many products of a power of x and a power of y",
			"finite(«products»(«powers»(x, p), «powers»(y, q)))",
			By(
				finitePowers.At(x, p),
				finitePowers.At(y, q),
				finite_set.FiniteProductDependent.At(
					a.TermAs[Op[A]]("L.mul"), powersX, a.TermAs[Fun[A, Set[A]]]("λb:A. «powers»(y, q)"))))
		productsIn := a.Have(
			"a product of a power of x and a power of y lies in L",
			"«products»(«powers»(x, p), «powers»(y, q)) ⊆ L.carrier",
			BySets(
				comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ring)),
				xIn,
				yIn,
				comm_ring.MulIn.Read(ring)))
		nonzeroSxy := a.Have(
			"S[x][y] holds one, which is not zero",
			"∃v:A. v ∈ «Sxy» ∧ v ≠ L.zero",
			By(comm_ring.SubringOne.Read(subSxy), field.OneNotZeroOn.Read(L)))
		integral := a.Have(
			"every element of S[x][y] is integral over S",
			"∀w:A. w ∈ «Sxy» ⇒ integral_over(«R», w)",
			Derive(func(b *Argument) {
				w := b.FixAs[A]("w")
				wIn := b.Assume()
				stable := b.Have(
					"multiplication by w keeps the subring S[x][y]",
					"image(L.mul(w), «Sxy») ⊆ «Sxy»",
					BySets(wIn, comm_ring.SubringMul.Read(subSxy)))
				wm := b.MemberOf[on.L](w, b.Have(
					"w lies in L",
					"w ∈ L.carrier",
					BySets(wIn, comm_ring.SubringSubset.Read(subSxy))))
				b.Show(
					"S[x][y] is spanned over S by finitely many products",
					By(
						subS,
						finiteProducts,
						productsIn,
						tower,
						stable,
						nonzeroSxy,
						FinitelySpannedIntegral.Read(L).At(S, Sxy, products, wm)))
			}))
		xInSxy := a.Have(
			"x lies in S[x][y]",
			"x ∈ «Sxy»",
			BySets(adjoinedX[2], adjoinedY[1]))
		a.Show(
			"x + y, −x and x·y lie in the subring S[x][y]",
			By(
				integral.At(a.TermAs[A]("x + y")),
				integral.At(a.TermAs[A]("-x")),
				integral.At(a.TermAs[A]("x * y")),
				comm_ring.SubringAdd.At(c, Sxy, x, y),
				comm_ring.SubringNeg.At(c, Sxy, x),
				comm_ring.SubringMul.At(c, Sxy, x, y),
				subSxy,
				xInSxy,
				adjoinedY[2]))
	}),
})}

// IntegralModuleSum — a finite sum of integral elements over a subring is
// integral: zero is a root of X, and one more index adds an integral element to
// an integral sum.
var IntegralModuleSum = integralModuleSumThm{family.Add(registry.ProofEntry{
	Name: "IntegralModuleSum",
	Key:  "prop_5e04de7d74cd9ab5",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "scalars", Text: "restrict_ring(field_ring(L), S)"},
		},
		Binders: "∀L:field_on(A). ∀S:set(A). ∀I:set(D). ∀f:(D → A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"finite(I)",
			"∀i:D. i ∈ I ⇒ f(i) ∈ L.carrier ∧ integral_over(«scalars», f(i))",
		},
		Conclusion: "integral_over(«scalars», module_sum(L.add, L.zero, I, f))",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			S *Expr[Set[A]],
			I *Expr[Set[D]],
			f *Arrow[D, A],
			subS, finiteI, terms Fact,
		) {
			l := a.TermAs[FieldOps[A]]("L")
			ring := field.RingOn.Read(L)
			additive := comm_ring.AddMonoidOn.Read(ring)
			linear := a.TermAs[Nat]("1")
			zero := a.TermAs[A]("L.zero")
			one := a.TermAs[A]("L.one")
			variable := a.TermAs[Fun[Nat, A]]("basis_vector(1)")
			baseRing := a.Have(
				"S is a ring under the operations of L",
				"comm_ring_on(«scalars»)",
				By(comm_ring.SubringRingOn.Read(ring), subS))
			degree := a.Have(
				"X has degree one",
				"polynomial_degree(basis_vector(1)) = 1",
				By(field.OneNotZeroOn.Read(L), polynomial.DegreeBasisVector.Read(baseRing).At(linear)))
			monic := a.Have(
				"X is monic",
				"polynomial_monic(basis_vector(1))",
				Simp(Fwd(polynomial.PolynomialMonicDef), Fwd(degree)),
				By(vec_space.BasisVectorDef.At(zero, one, linear, linear)))
			positiveDegree := a.Have(
				"of positive degree",
				"0 < polynomial_degree(basis_vector(1))",
				ByArith(degree))
			zeroIntegral := a.Have(
				"zero is a root of X",
				"integral_over(«scalars», L.zero)",
				Simp(Fwd(IntegralOverDef)),
				Witness(variable),
				By(
					positiveDegree,
					monic,
					polynomial.BasisVectorOver.Read(baseRing).At(linear),
					comm_ring.ZeroIn.Read(ring),
					polynomial_evaluation.EvalBasisVector.Read(ring).AsFact().At(linear, zero),
					comm_monoid.PowOneOn.Read(comm_ring.MulMonoidOn.Read(ring)).AsFact().At(zero)))
			a.Show(
				"the induction carries integrality to every finite index set of integral terms",
				ByInduction(finite_set.FiniteInductFreshOn, finiteI, terms,
					Case(
						"the empty sum is zero",
						By(zeroIntegral, module.ModuleSumEmpty)),
					Case(
						"one more index adds an integral element to an integral sum",
						Derive(func(b *Argument) {
							x := b.FixAs[D]()
							t := b.FixAs[Set[D]]()
							carried := b.Conjuncts(
								b.Assume(),
								"the sum over t is integral",
								"x is a new index of t",
								"t is finite",
								"f(x) lies in L",
								"f(x) is integral",
								"f is integral on t")
							rest, notIn, finT, fxIn, fxIntegral, onT :=
								carried[0], carried[1], carried[2], carried[3], carried[4], carried[5]
							sumT := b.TermAs[A]("module_sum(L.add, L.zero, t, f)")
							sumIn := b.Have(
								"the sum over t lies in L",
								"module_sum(L.add, L.zero, t, f) ∈ L.carrier",
								By(finT, onT, module.ModuleSumInMonoid.Read(additive).AsFact().At(t, f)))
							peel := b.Have(
								"the sum over insert(x, t) adds f(x) to the sum over t",
								"module_sum(L.add, L.zero, insert(x, t), f) = f(x) + module_sum(L.add, L.zero, t, f)",
								By(notIn, finT, fxIn, onT, module.ModuleSumInsertMonoid.Read(additive).AsFact().At(t, x, f)))
							b.Do(peel.Rw())
							b.Show(
								"a sum of two integral elements is integral",
								By(L, subS, fxIn, sumIn, fxIntegral, rest, IntegralAddNegMul.At(l, S, f.Apply(x), sumT)))
						}))))
		}),
})}

// IntegralElementsSubring — the elements of a field L integral over a
// subring S form a subring of L holding S: a member of S is integral, S being
// a subring that one spans over S (FinitelySpannedIntegral), and the sum,
// negative and product of two integral elements are integral
// (IntegralAddNegMul).
var IntegralElementsSubring = integralElementsSubringThm{family.Add(registry.ProofEntry{
	Name: "IntegralElementsSubring",
	Key:  "prop_c74d9b6367658852",
	Reading: "No hypothesis on S beyond being a subring: the determinant trick needs no principal " +
		"ideal domain, only that L, a field, has no zero divisors to cancel a nonzero generator.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S:set(A).",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
		},
		Conclusion: "subring(field_ring(L), " +
			"    integral_closure(restrict_ring(field_ring(L), S), L.carrier)) ∧ " +
			"S ⊆ integral_closure(restrict_ring(field_ring(L), S), L.carrier)",
	}, func(a *Argument, L field.FieldFact[on.L], S *Expr[Set[A]], subS Fact) {
		ring := field.RingOn.Read(L)
		c := a.TermAs[RingOps[A]]("field_ring(L)")
		_, closureDef := a.LetAs[Set[A]](
			"C", "integral_closure(restrict_ring(field_ring(L), S), L.carrier)")
		members := a.Have(
			"C holds the members of L integral over S",
			"∀x:A. x ∈ C ⇔ x ∈ L.carrier ∧ integral_over(restrict_ring(field_ring(L), S), x)",
			BySets(closureDef, IntegralClosureDef))
		one := a.TermAs[Set[A]]("{L.one}")
		oneIn := a.Have(
			"one lies in S",
			"{L.one} ⊆ S ∧ L.one ∈ {L.one}",
			BySets(comm_ring.SubringOne.At(c, S), subS))
		spannedByOne := a.Have(
			"so S is spanned over itself by one",
			"module_span(restrict_ring(field_ring(L), S), regular_module(field_ring(L)), {L.one}) = S",
			By(subS, oneIn, fractional_ideal.SpanHoldingOne.Read(L).At(S, one)))
		oneInL := a.Have(
			"one lies in L",
			"{L.one} ⊆ L.carrier",
			BySets(comm_ring.OneIn.Read(ring)))
		nonzeroS := a.Have(
			"S holds one, which is not zero",
			"∃v:A. v ∈ S ∧ v ≠ L.zero",
			By(comm_ring.SubringOne.Read(subS), field.OneNotZeroOn.Read(L)))
		integralS := a.Have(
			"each member of S is integral over S",
			"∀s:A. s ∈ S ⇒ integral_over(restrict_ring(field_ring(L), S), s)",
			Derive(func(b *Argument) {
				s := b.FixAs[A]("s")
				sIn := b.Assume()
				stable := b.Have(
					"multiplication by s keeps the subring S",
					"image(L.mul(s), S) ⊆ S",
					BySets(sIn, comm_ring.SubringMul.Read(subS)))
				sm := b.MemberOf[on.L](s, b.Have(
					"s lies in L",
					"s ∈ L.carrier",
					BySets(sIn, comm_ring.SubringSubset.Read(subS))))
				b.Show(
					"S is spanned over S by one element",
					By(
						subS,
						spannedByOne,
						oneInL,
						stable,
						nonzeroS,
						finite_set.FiniteSing.At(b.TermAs[A]("L.one")),
						FinitelySpannedIntegral.Read(L).At(S, S, one, sm)))
			}))
		holdsS := a.Have(
			"so C holds S",
			"S ⊆ C",
			BySets(integralS, members, comm_ring.SubringSubset.At(c, S), subS))
		inField := a.Have(
			"C lies in L",
			"C ⊆ L.carrier",
			BySets(members))
		constants := a.Have(
			"C holds zero and one, as S does",
			"L.zero ∈ C ∧ L.one ∈ C",
			BySets(holdsS, subS, comm_ring.SubringZero.At(c, S), comm_ring.SubringOne.At(c, S)))
		operations := a.Have(
			"C is closed under sums, negatives and products",
			"∀x y:A. x ∈ C ∧ y ∈ C ⇒ x + y ∈ C ∧ -x ∈ C ∧ x * y ∈ C",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				y := b.FixAs[A]("y")
				given := b.Conjuncts(
					b.Assume(),
					"x lies in C",
					"y lies in C")
				ofX := b.Conjuncts(
					b.Have(
						"x lies in L and is integral over S",
						"x ∈ L.carrier ∧ integral_over(restrict_ring(field_ring(L), S), x)",
						By(given[0], members.At(x))),
					"x lies in L",
					"x is integral over S")
				ofY := b.Conjuncts(
					b.Have(
						"so does y",
						"y ∈ L.carrier ∧ integral_over(restrict_ring(field_ring(L), S), y)",
						By(given[1], members.At(y))),
					"y lies in L",
					"y is integral over S")
				xm := b.MemberOf[on.L](x, ofX[0])
				ym := b.MemberOf[on.L](y, ofY[0])
				b.Show(
					"x + y, −x and x·y lie in L and are integral over S",
					By(
						members.At(b.TermAs[A]("x + y")),
						members.At(b.TermAs[A]("-x")),
						members.At(b.TermAs[A]("x * y")),
						comm_ring.AddIn.Read(ring).At(xm, ym),
						comm_ring.NegIn.Read(ring).At(xm),
						comm_ring.MulIn.Read(ring).At(xm, ym),
						subS,
						ofX[1],
						ofY[1],
						IntegralAddNegMul.Read(L).At(S, xm, ym)))
			}))
		subringC := a.Have(
			"so C is a subring of L",
			"subring(field_ring(L), C)",
			Simp(Fwd(comm_ring.SubringDef)),
			By(inField, constants, operations))
		a.Show(
			"C is a subring of L holding S",
			By(subringC, holdsS))
	}),
})}

// ScaledRootIntegral — a root x of a monic polynomial p over L, scaled by an
// element d of a subring S that brings every coefficient of p into S, is
// integral over S. With n the degree of p, the polynomial whose i-th
// coefficient is d^(n−i)·p(i) up to n and zero past it takes at d·x the
// value dⁿ·p(x) = 0 (polynomial_evaluation.EvalRescaled); below n its coefficient is
// d^(n−i−1)·(d·p(i)), a product of members of S, and at n it is p(n) = 1, so
// it is a monic polynomial over S of degree n.
var ScaledRootIntegral = scaledRootIntegralThm{family.Add(registry.ProofEntry{
	Name: "ScaledRootIntegral",
	Key:  "prop_4db7256e9d998056",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀S:set(A). ∀p:(num → A). ∀d x:A.",
		Hypotheses: []string{
			"subring(field_ring(L), S)",
			"polynomial_over(L.carrier, p)",
			"polynomial_monic(p)",
			"0 < polynomial_degree(p)",
			"x ∈ L.carrier",
			"polynomial_eval(p, x) = L.zero",
			"d ∈ S",
			"∀i:num. d * p(i) ∈ S",
		},
		Conclusion: "integral_over(restrict_ring(field_ring(L), S), d * x)",
		Abbrev: Abbrev{
			{Name: "scaled", Text: "λi:num. " +
				"    COND(i ≤ polynomial_degree(p), " +
				"        monoid_pow(L.mul, L.one, d, polynomial_degree(p) - i) * p(i), " +
				"        L.zero)"},
		},
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		S *Expr[Set[A]],
		p *Arrow[Nat, A],
		d, x *Expr[A],
		subring, pOver, monic, positive, xIn, root, dInS, cleared Fact,
	) {
		ring := field.RingOn.Read(L)
		zero := a.TermAs[A]("L.zero")
		degree := a.TermAs[Nat]("polynomial_degree(p)")
		scaled := a.TermAs[Fun[Nat, A]]("«scaled»")
		xm := a.MemberOf[on.L](x, xIn)
		dm := a.MemberOf[on.L](d, a.Have(
			"d lies in L, S being a subring of L",
			"d ∈ L.carrier",
			BySets(dInS, comm_ring.SubringSubset.Read(subring))))
		ringS := a.Have(
			"S is a ring under the operations of L",
			"comm_ring_on(restrict_ring(field_ring(L), S))",
			By(subring, comm_ring.SubringRingOn.Read(ring).At(S)))

		// The value at d·x.
		rescaled := a.Simplified(
			GroupPremises(
				pOver, polynomial_evaluation.EvalRescaled.Read(ring).At(p, degree, a.TermAs[Nat]("1"), dm, xm)),
			Fwd(nat_arith.OneMul),
			Fwd(comm_monoid.PowOneOn.Read(comm_ring.MulMonoidOn.Read(ring))))
		value := a.Have(
			"d·x is a root of the scaled polynomial: its value there is dⁿ·p(x) = 0",
			"polynomial_eval(«scaled», d * x) = L.zero",
			ByArith(L, rescaled, pOver, dm, xm, root))

		// The coefficients lie in S.
		one := a.TermAs[A]("L.one")
		top := a.Have(
			"its coefficient at n is d⁰·p(n) = 1, p being monic",
			"«scaled»(polynomial_degree(p)) = L.one",
			ByArith(L, dm, monic, polynomial.PolynomialMonicDef.At(zero, one, p)))
		coefficients := a.Have(
			"every coefficient of the scaled polynomial lies in S",
			"∀i:num. «scaled»(i) ∈ S",
			Derive(func(b *Argument) {
				i := b.FixAs[Nat]("i")
				b.Cases(b.TermAs[Bool]("i < polynomial_degree(p)"))
				b.When(
					"below n the coefficient is d^(n−i−1)·(d·p(i)), a product of members of S",
					func(c *Argument, below Fact) {
						exponent := c.Have(
							"n − i is the successor of n − (i + 1)",
							"polynomial_degree(p) - i = suc(polynomial_degree(p) - suc(i))",
							ByArith(below))
						power := c.Have(
							"so d^(n−i) = d·d^(n−i−1)",
							"monoid_pow(L.mul, L.one, d, polynomial_degree(p) - i) = "+
								"d * monoid_pow(L.mul, L.one, d, polynomial_degree(p) - suc(i))",
							exponent.Rw(),
							Simp(Fwd(comm_monoid.MonoidPowDef)),
							Refl())
						coefficient := c.MemberOf[on.L](p.Apply(i), c.Have(
							"p(i) lies in L",
							"p(i) ∈ L.carrier",
							By(pOver, polynomial.PolynomialOverDef)))
						regrouped := c.Have(
							"d^(n−i)·p(i) = d^(n−i−1)·(d·p(i))",
							"monoid_pow(L.mul, L.one, d, polynomial_degree(p) - i) * p(i) = "+
								"monoid_pow(L.mul, L.one, d, polynomial_degree(p) - suc(i)) * (d * p(i))",
							ByArith(L, Scaled(p.Apply(i), power), dm, coefficient))
						remaining := c.TermAs[Nat]("polynomial_degree(p) - suc(i)")
						dS := proof.MemberOf(d, dInS)
						c.Show(
							"so the coefficient lies in S, both factors lying in S",
							By(
								below,
								regrouped,
								nat_order.LessEqOfLessThan.At(i, degree),
								comm_ring.MulIn.Read(ringS).At(
									comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ringS)).At(dS, remaining),
									c.MemberOf[on.Any](c.TermAs[A]("d * p(i)"), cleared.At(i)))))
					})
				b.Otherwise(
					"from n on the coefficient is one or zero",
					func(c *Argument, notBelow Fact) {
						c.Cases(c.TermAs[Bool]("i = polynomial_degree(p)"))
						c.When(
							"at n it is one, which S holds",
							func(e *Argument, atDegree Fact) {
								e.Show(
									"S holds one",
									By(Normalized, atDegree, top, comm_ring.SubringOne.Read(subring)))
							})
						c.Otherwise(
							"past n it is zero, which S holds",
							func(e *Argument, pastDegree Fact) {
								e.Show(
									"S holds zero",
									ByArith(notBelow, pastDegree, comm_ring.SubringZero.Read(subring)))
							})
					})
			}))

		// A monic polynomial over S of degree n.
		vanishesPast := a.Have(
			"the scaled polynomial vanishes past n",
			"vec⟨suc(polynomial_degree(p))⟩(«scaled»)",
			ByArith(vec_space.VecDef))
		overS := a.Have(
			"so it is a polynomial over S",
			"polynomial_over(S, «scaled»)",
			By(coefficients, vanishesPast, polynomial.PolynomialOverDef))
		sameDegree := a.Have(
			"its degree is n, its coefficient at n being one and not zero",
			"polynomial_degree(«scaled») = polynomial_degree(p)",
			By(
				overS,
				vanishesPast,
				top,
				field.OneNotZeroOn.Read(L),
				polynomial.DegreeExact.At(zero, S, scaled, degree)))
		a.Show(
			"so it is a monic equation of positive degree for d·x over S",
			Unfold(IntegralOverDef),
			Witness(scaled),
			By(overS, top, sameDegree, positive, value, polynomial.PolynomialMonicDef.At(zero, one, scaled)))
	}),
})}

// AlgebraicIntegral — an element x of L algebraic over a subfield k is
// integral over k: its minimal polynomial over k has its coefficients in k,
// is monic and of positive degree, and vanishes at x.
var AlgebraicIntegral = algebraicIntegralThm{family.Add(registry.ProofEntry{
	Name: "AlgebraicIntegral",
	Key:  "prop_c30090be2690f864",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x:A.",
		Hypotheses: []string{
			"subfield(L, k)",
			"x ∈ L.carrier",
			"algebraic_over(L, k, x)",
		},
		Conclusion: "integral_over(restrict_ring(field_ring(L), k), x)",
	}, func(
		a *Argument,
		L field.FieldFact[on.L],
		k *Expr[Set[A]],
		x *Expr[A],
		subfield, xIn, algebraic Fact,
	) {
		xm := a.MemberOf[on.L](x, xIn)
		a.Show(
			"its minimal polynomial over k is a monic equation of positive degree for x",
			Simp(Fwd(IntegralOverDef)),
			Witness(a.TermAs[Fun[Nat, A]]("minimal_polynomial(L, k, x)")),
			By(
				subfield,
				algebraic,
				algebraic_element.MinimalPolynomialSpec.Read(L).At(k, xm),
				algebraic_element.MinimalPolynomialPositive.Read(L).At(k, xm)))
	}),
})}

// IntegralOverMono — a monic relation over a smaller set of coefficients is
// one over a larger set.
var IntegralOverMono = integralOverMonoThm{family.Add(registry.ProofEntry{
	Name: "IntegralOverMono",
	Key:  "prop_346ddcf7302c2236",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀S B:set(A). ∀x:A.",
		Hypotheses: []string{
			"S ⊆ B",
			"integral_over(restrict_ring(R, S), x)",
		},
		Conclusion: "integral_over(restrict_ring(R, B), x)",
	},
		func(a *Argument, R *Expr[RingOps[A]], S, B *Expr[Set[A]], x *Expr[A], inclusion, integral Fact) {
			zero := a.TermAs[A]("R.zero")
			p, relation := a.UnpackAs[Fun[Nat, A]](a.Unfolded(integral, IntegralOverDef), "p")
			a.Do(Simp(Fwd(IntegralOverDef)))
			a.Take(p)
			a.Show(
				"the same monic relation, its coefficients in the larger set",
				By(inclusion, relation, polynomial.PolynomialOverMono.At(zero, S, B, p)))
		}),
})}
