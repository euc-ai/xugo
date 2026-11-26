// jacobian.go — the smoothness condition of a projective equation curve read
// at one field in the vocabulary of the elementarity step: at a point, the
// gradients of the listed equations span n − 1 dimensions exactly when the
// tuples their partials annihilate form a plane, said with two independent
// tuples and no three.

package projective_transfer

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_closure"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/partial_derivative"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/homogeneous_polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_encoding"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/scheme/projective_curve"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// JacobianKernelCriterion — the smoothness condition of the curve cut out by
// a listed family P(0), …, P(r − 1) of polynomials over k (at every point the
// gradients span n − 1 dimensions) holds exactly when, at every normalized
// zero x of the family, the tuples of length n + 1 killed by the partials of
// the family at x form a plane: two of them have only the trivial relation,
// and any three a nontrivial one. The right side is written for the
// elementarity step that carries it from one closed field to another
// (CarriedSmoothness): that step quantifies over listed polynomial parameters
// only, and partial differentiation is not in its vocabulary, so the partials
// are a second listed family Q, the hypothesis setting each row
// Q(j·(n + 1) + c) equal to ∂_c P(j); and a dimension is not first-order
// there, so "a plane" is said by those two clauses. The points are the
// normalized zeros (projective_curve.PointsAsNormalizedZeros). At a point, the
// span of the gradients and the vectors they annihilate have dimensions adding
// to n + 1 (AnnihilatorDimension), so the span has dimension n − 1 exactly when
// the annihilator, a subspace (AnnihilatorSubspace), has dimension two, which
// DimTwo says in the two clauses. The annihilator's vectors are the tuples
// (polynomial_encoding.TuplesAsVectors) killed by the partials at x, each
// gradient's entries being the values of the partials of its equation at x; and
// a relation among vectors of it is the relation at every coordinate below
// n + 1, since past n all of them vanish.
var JacobianKernelCriterion = jacobianKernelCriterionThm{family.Add(registry.ProofEntry{
	Name: "JacobianKernelCriterion",
	Key:  "prop_e990488c5f25e809",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). ∀k:set(A). ∀n r:num. ∀P Q:(num → (num → num) → A).",
		Hypotheses: []string{
			"subfield(M, k)",
			"∀j:num. j < r ⇒ P(j) ∈ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})",
			"∀j c:num. " +
				"    j < r ∧ c ≤ n ⇒ " +
				"    Q(j * (n + 1) + c) = polynomial_algebra_partial(«hilbertCoefficients», c, P(j))",
		},
		Conclusion: "(∀x:(num → A). " +
			"    x ∈ projective_equation_points(field_ring(M), k, M.carrier, n, image(P, {j:num | j < r})) ⇒ " +
			"    module_dim(field_ring(M), " +
			"        restrict_module(«space», module_span(field_ring(M), «space», «gradients»(x)))) + " +
			"    1 = " +
			"    n) ⇔ " +
			"(∀x:(num → A). «normalizedZero»(x) ⇒ «pairs»(x) ∧ «triples»(x))",
		Abbrev: Abbrev{
			{Name: "space", Text: "free_module_record(field_ring(M), {i:num | i ≤ n})"},
			{Name: "gradient", Text: "λx:(num → A). λG:((num → num) → A). λi:num. " +
				"    COND(i ≤ n, " +
				"        polynomial_algebra_eval(«hilbertCoefficients», " +
				"            field_ring(M), " +
				"            λa:A. a, " +
				"            x, " +
				"            polynomial_algebra_partial(«hilbertCoefficients», i, G)), " +
				"        M.zero)"},
			{Name: "gradients", Text: "λx:(num → A). " +
				"    {«gradient»(x, G) | G:(num → num) → A | G ∈ image(P, {j:num | j < r})}"},
			{Name: "annihilator", Text: "λx:(num → A). " +
				"    {a:num → A | " +
				"        a ∈ finite_supp(M.zero, M.carrier, {i:num | i ≤ n}) ∧ " +
				"        (∀v:num → A. " +
				"            v ∈ «gradients»(x) ⇒ " +
				"            module_sum(M.add, M.zero, {i:num | i ≤ n}, λi:num. v(i) * a(i)) = M.zero)}"},
			{Name: "normalizedZero", Text: "λx:(num → A). " +
				"    ring_tuple(field_ring(M), n + 1, x) ∧ " +
				"    (∃j:num. j < n + 1 ∧ x(j) = M.one ∧ (∀i:num. i < j ⇒ x(i) = M.zero)) ∧ " +
				"    (∀j:num. j < r ⇒ polynomial_value(field_ring(M), P(j), x) = M.zero)"},
			{Name: "kills", Text: "λx:(num → A). λa:(num → A). ∀j:num. " +
				"    j < r ⇒ " +
				"    module_sum(M.add, " +
				"        M.zero, " +
				"        {c:num | c < n + 1}, " +
				"        λc:num. polynomial_value(field_ring(M), Q(j * (n + 1) + c), x) * a(c)) = " +
				"    M.zero"},
			{Name: "pairs", Text: "λx:(num → A). ∃a b:(num → A). " +
				"    ring_tuple(field_ring(M), n + 1, a) ∧ " +
				"    ring_tuple(field_ring(M), n + 1, b) ∧ " +
				"    «kills»(x, a) ∧ " +
				"    «kills»(x, b) ∧ " +
				"    (∀s t:A. " +
				"        s ∈ M.carrier ∧ t ∈ M.carrier ∧ (∀c:num. c < n + 1 ⇒ s * a(c) + t * b(c) = M.zero) ⇒ " +
				"        s = M.zero ∧ t = M.zero)"},
			{Name: "triples", Text: "λx:(num → A). ∀a b d:(num → A). " +
				"    ring_tuple(field_ring(M), n + 1, a) ∧ " +
				"    ring_tuple(field_ring(M), n + 1, b) ∧ " +
				"    ring_tuple(field_ring(M), n + 1, d) ∧ " +
				"    «kills»(x, a) ∧ " +
				"    «kills»(x, b) ∧ " +
				"    «kills»(x, d) ⇒ " +
				"    (∃s t u:A. " +
				"        s ∈ M.carrier ∧ " +
				"        t ∈ M.carrier ∧ " +
				"        u ∈ M.carrier ∧ " +
				"        ¬(s = M.zero ∧ t = M.zero ∧ u = M.zero) ∧ " +
				"        (∀c:num. c < n + 1 ⇒ s * a(c) + t * b(c) + u * d(c) = M.zero))"},
		},
	}, func(
		arg *Argument,
		M field.FieldFact[on.M],
		k *Expr[Set[A]],
		n, r *Expr[Nat],
		P, Q *Arrow[Nat, Fun[Fun[Nat, Nat], A]],
		subK, listedOverK, partials Fact,
	) {
		fieldOps := arg.TermAs[FieldOps[A]]("M")
		ring := field.RingOn.Read(M)
		R := arg.TermAs[module_record.RingOps[A]]("field_ring(M)")
		inv := arg.TermAs[Fun[A, A]]("M.inv")
		indices := arg.TermAs[Set[Nat]]("{i:num | i ≤ n}")
		space := arg.TermAs[module_record.ModuleOps[A, Fun[Nat, A]]]("«space»")
		next := arg.TermAs[Nat]("n + 1")
		below := arg.TermAs[Set[Nat]]("{j:num | j < r}")
		listed := arg.TermAs[Set[Fun[Fun[Nat, Nat], A]]]("image(P, {j:num | j < r})")
		zero := comm_ring.ZeroIn.Read(ring)
		sumZero := group.RightIdentityOn.Read(abelian_group.GroupOn.Read(comm_ring.AddGroupOn.Read(ring)))
		timesZero := comm_ring.MulRightZeroOn.Read(ring)
		scalarsField := arg.Have(
			"M is a field on its own carrier",
			"ring_subfield(field_ring(M), M.inv, field_ring(M).carrier)",
			By(field.FieldRingSubfield.Read(M)))
		moduleS := arg.Have(
			"the tuples of M^{0..n} form a vector space over M",
			"module_on(field_ring(M), «space»)",
			By(free_module.FreeModuleOn.Read(ring).At(indices)))
		finiteS := arg.Conjuncts(
			GroupPremises(
				scalarsField,
				num_segment.FiniteBelow.At(n),
				module_dimension.FreeModuleFiniteDim.At(R, inv, indices)),
			"M^{0..n} is finite-dimensional",
			"of dimension card({i | i ≤ n})")

		pairRelation := arg.Have(
			"a relation between two tuples, as vectors, is the relation "+
				"at every coordinate below n + 1, past which both vanish",
			Statement{
				Binders: "∀a b:(num → A). ∀s t:A.",
				Hypotheses: []string{
					"ring_tuple(field_ring(M), n + 1, a)",
					"ring_tuple(field_ring(M), n + 1, b)",
					"s ∈ M.carrier",
					"t ∈ M.carrier",
				},
				Conclusion: "fun_add(M.add, fun_smul(M.mul, s, a), fun_smul(M.mul, t, b)) = fun_zero(M.zero) ⇔ " +
					"∀c:num. c < n + 1 ⇒ s * a(c) + t * b(c) = M.zero",
			},
			Derive(func(b *Argument) {
				b.FixAs[Fun[Nat, A]]("a")
				b.FixAs[Fun[Nat, A]]("b")
				b.FixAs[A]("s")
				b.FixAs[A]("t")
				given := b.Conjuncts(
					b.Assume(),
					"a is a tuple of length n + 1",
					"so is b",
					"s is a scalar",
					"so is t")
				b.Iff()
				b.Forward(
					"read at a coordinate c, the vector relation is the relation at c",
					func(c *Argument, relation Fact) {
						c.FixAs[Nat]("c")
						atC := c.Have(
							"the two sides agree at c",
							"fun_add(M.add, fun_smul(M.mul, s, a), fun_smul(M.mul, t, b), c) = fun_zero(M.zero, c)",
							By(relation))
						c.Show(
							"which is s a(c) + t b(c) = 0",
							By(c.Simplified(
								atC,
								Fwd(function_module.FunAddDef),
								Fwd(function_module.FunSmulDef),
								Fwd(function_module.FunZeroDef))))
					})
				b.Backward(
					"below n + 1 the relation holds by hypothesis, and past n both tuples vanish",
					func(c *Argument, coordinates Fact) {
						everywhere := c.Have(
							"s a(c) + t b(c) = 0 at every coordinate c",
							"∀c:num. s * a(c) + t * b(c) = M.zero",
							c.ForEach(func(i *Expr[Nat]) Action {
								return By(
									coordinates,
									given[0],
									given[1],
									given[2],
									given[3],
									polynomial_encoding.RingTupleDef,
									vec_space.VecDef,
									nat_order.NotLessThan.At(i, next),
									timesZero,
									sumZero,
									zero)
							}))
						c.Show(
							"so the two functions agree",
							Funext(),
							Simp(
								Fwd(function_module.FunAddDef),
								Fwd(function_module.FunSmulDef),
								Fwd(function_module.FunZeroDef)),
							By(everywhere))
					})
			}))
		tripleRelation := arg.Have(
			"so is a relation among three tuples",
			Statement{
				Binders: "∀a b d:(num → A). ∀s t u:A.",
				Hypotheses: []string{
					"ring_tuple(field_ring(M), n + 1, a)",
					"ring_tuple(field_ring(M), n + 1, b)",
					"ring_tuple(field_ring(M), n + 1, d)",
					"s ∈ M.carrier",
					"t ∈ M.carrier",
					"u ∈ M.carrier",
				},
				Conclusion: "fun_add(M.add, " +
					"    fun_add(M.add, fun_smul(M.mul, s, a), fun_smul(M.mul, t, b)), " +
					"    fun_smul(M.mul, u, d)) = " +
					"fun_zero(M.zero) ⇔ " +
					"∀c:num. c < n + 1 ⇒ s * a(c) + t * b(c) + u * d(c) = M.zero",
			},
			Derive(func(b *Argument) {
				b.FixAs[Fun[Nat, A]]("a")
				b.FixAs[Fun[Nat, A]]("b")
				b.FixAs[Fun[Nat, A]]("d")
				b.FixAs[A]("s")
				b.FixAs[A]("t")
				b.FixAs[A]("u")
				given := b.Conjuncts(
					b.Assume(),
					"a is a tuple of length n + 1",
					"so is b",
					"and d",
					"s is a scalar",
					"so is t",
					"and u")
				b.Iff()
				b.Forward(
					"read at a coordinate c, the vector relation is the relation at c",
					func(c *Argument, relation Fact) {
						c.FixAs[Nat]("c")
						atC := c.Have(
							"the two sides agree at c",
							"fun_add(M.add, "+
								"    fun_add(M.add, fun_smul(M.mul, s, a), fun_smul(M.mul, t, b)), "+
								"    fun_smul(M.mul, u, d), "+
								"    c) = "+
								"fun_zero(M.zero, c)",
							By(relation))
						c.Show(
							"which is s a(c) + t b(c) + u d(c) = 0",
							By(c.Simplified(
								atC,
								Fwd(function_module.FunAddDef),
								Fwd(function_module.FunSmulDef),
								Fwd(function_module.FunZeroDef))))
					})
				b.Backward(
					"below n + 1 the relation holds by hypothesis, and past n the three tuples vanish",
					func(c *Argument, coordinates Fact) {
						everywhere := c.Have(
							"s a(c) + t b(c) + u d(c) = 0 at every coordinate c",
							"∀c:num. s * a(c) + t * b(c) + u * d(c) = M.zero",
							c.ForEach(func(i *Expr[Nat]) Action {
								return By(
									coordinates,
									given[0],
									given[1],
									given[2],
									given[3],
									given[4],
									given[5],
									polynomial_encoding.RingTupleDef,
									vec_space.VecDef,
									nat_order.NotLessThan.At(i, next),
									timesZero,
									sumZero,
									zero)
							}))
						c.Show(
							"so the two functions agree",
							Funext(),
							Simp(
								Fwd(function_module.FunAddDef),
								Fwd(function_module.FunSmulDef),
								Fwd(function_module.FunZeroDef)),
							By(everywhere))
					})
			}))

		perPoint := arg.Have(
			"at a point x the gradients span n − 1 dimensions exactly "+
				"when the tuples the partials at x kill form a plane",
			Statement{
				Binders: "∀x:(num → A).",
				Hypotheses: []string{
					"x ∈ projective_equation_points(field_ring(M), k, M.carrier, n, image(P, {j:num | j < r}))",
				},
				Conclusion: "module_dim(field_ring(M), " +
					"    restrict_module(«space», module_span(field_ring(M), «space», «gradients»(x)))) + " +
					"1 = " +
					"n ⇔ " +
					"«pairs»(x) ∧ «triples»(x)",
			},
			Derive(func(b *Argument) {
				x := b.FixAs[Fun[Nat, A]]("x")
				point := b.Assume()
				gradients := b.TermAs[Set[Fun[Nat, A]]]("«gradients»(x)")
				annihilator := b.TermAs[Set[Fun[Nat, A]]]("«annihilator»(x)")
				gradientAt := b.TermAs[Fun[Fun[Fun[Nat, Nat], A], Fun[Nat, A]]]("«gradient»(x)")
				asImage := b.Have(
					"the gradients at x are the image of the indices below r under the gradient of P(j) at x",
					"«gradients»(x) = image(«gradient»(x) ∘ P, {j:num | j < r})",
					By(set_image.SimpleImage.At(gradientAt, listed), set_image.ImageCompose.At(gradientAt, P, below)))
				coordinates := b.Have(
					"the coordinates of x up to n lie in M",
					"∀i:num. i ≤ n ⇒ x(i) ∈ M.carrier",
					By(point, projective_curve.PointCoordinatesIn))
				inSpace := b.Have(
					"the gradient of each listed equation at x is a vector of M^{0..n}",
					"«gradients»(x) ⊆ «space».carrier",
					asImage.Rw(),
					Simp(Fwd(set_image.ImageSubsetIff), Fwd(functions.ComposeApply)),
					b.ForEach(func(j *Expr[Nat]) Action {
						return By(
							subK,
							coordinates,
							listedOverK.At(j),
							homogeneous_polynomial.GradientCoordinateVector.Read(M).At(k, n, P.Apply(j), x))
					}))
				dimensions := b.Have(
					"the span of the gradients and the vectors they annihilate have dimensions adding to n + 1",
					"module_dim(field_ring(M), "+
						"    restrict_module(«space», module_span(field_ring(M), «space», «gradients»(x)))) + "+
						"module_dim(field_ring(M), restrict_module(«space», «annihilator»(x))) = "+
						"n + 1",
					By(
						inSpace,
						num_segment.FiniteBelow.At(n),
						num_segment.HasSizeBelow.At(n),
						cardinality.CardOfSized.At(indices, next),
						module_dimension.AnnihilatorDimension.Read(M).At(indices, gradients)))
				rank := b.Have(
					"so the span has dimension n − 1 exactly when the annihilator has dimension two",
					"module_dim(field_ring(M), "+
						"    restrict_module(«space», module_span(field_ring(M), «space», «gradients»(x)))) + "+
						"1 = "+
						"n ⇔ "+
						"module_dim(field_ring(M), restrict_module(«space», «annihilator»(x))) = 2",
					ByArith(dimensions))
				subspace := b.Have(
					"the annihilator is a subspace of M^{0..n}",
					"submodule(field_ring(M), «space», «annihilator»(x))",
					By(
						inSpace,
						num_segment.FiniteBelow.At(n),
						module_dimension.AnnihilatorSubspace.Read(ring).At(indices, gradients)))
				moduleW := b.Have(
					"so a vector space over M",
					"module_on(field_ring(M), restrict_module(«space», «annihilator»(x)))",
					By(moduleS, subspace, submodule.SubmoduleModuleOn.At(R, space, annihilator)))
				finiteW := b.Have(
					"of finite dimension",
					"finite_dimensional(field_ring(M), restrict_module(«space», «annihilator»(x)))",
					By(
						scalarsField,
						finiteS[0],
						subspace,
						module_dimension.SubmoduleDim.Read(moduleS).At(inv, annihilator)))
				plane := b.Simplified(
					GroupPremises(scalarsField, finiteW, module_dimension.DimTwo.Read(moduleW).At(inv)))

				entries := b.Have(
					"up to n, the gradient of P(j) at x has the entries the partials Q(j·(n + 1) + i) take at x",
					Statement{
						Binders: "∀j i:num.",
						Hypotheses: []string{
							"j < r",
							"i ≤ n",
						},
						Conclusion: "«gradient»(x, P(j), i) = polynomial_value(field_ring(M), Q(j * (n + 1) + i), x)",
					},
					By(
						partials,
						polynomial_algebra_evaluation.PolynomialAlgebraEvalRestrictCoefficients,
						polynomial_encoding.PolynomialValueDef))
				indexSets := b.Have(
					"the indices below n + 1 are those up to n",
					"{c:num | c < n + 1} = {i:num | i ≤ n}",
					BySets(nat_order.LessThanSucIffLessEq, nat_arith.Add1))
				pairings := b.Have(
					"so pairing a vector w with the gradient of P(j) is the sum of w against the partials of P(j) at x",
					Statement{
						Binders: "∀w:(num → A). ∀j:num.",
						Hypotheses: []string{
							"j < r",
						},
						Conclusion: "module_sum(M.add, M.zero, {i:num | i ≤ n}, λi:num. «gradient»(x, P(j), i) * w(i)) = " +
							"module_sum(M.add, " +
							"    M.zero, " +
							"    {c:num | c < n + 1}, " +
							"    λc:num. polynomial_value(field_ring(M), Q(j * (n + 1) + c), x) * w(c))",
					},
					Derive(func(c *Argument) {
						c.FixAs[Fun[Nat, A]]("w")
						j := c.FixAs[Nat]("j")
						below := c.Assume()
						terms := c.Have(
							"term by term, up to n",
							Statement{
								Binders: "∀i:num.",
								Hypotheses: []string{
									"i ∈ {i:num | i ≤ n}",
								},
								Conclusion: "«gradient»(x, P(j), i) * w(i) = " +
									"polynomial_value(field_ring(M), Q(j * (n + 1) + i), x) * w(i)",
							},
							c.ForEach(func(i *Expr[Nat]) Action {
								return By(below, entries.At(j, i))
							}))
						c.Show(
							"so the two sums over one index set agree",
							indexSets.Rw(),
							By(terms, module.ModuleSumCongruence))
					}))
				members := b.Have(
					"a vector lies in the annihilator exactly when it is "+
						"a tuple of length n + 1 killed by the partials at x",
					"∀w:(num → A). w ∈ «annihilator»(x) ⇔ ring_tuple(field_ring(M), n + 1, w) ∧ «kills»(x, w)",
					Derive(func(c *Argument) {
						w := c.FixAs[Fun[Nat, A]]("w")
						tuple := polynomial_encoding.TuplesAsVectors.Read(ring).At(n, w)
						c.Do(asImage.Rw(), Simp(Fwd(set_image.ForallInImage), Fwd(functions.ComposeApply)))
						c.Iff()
						c.Forward(
							"a vector of the annihilator is a tuple, and its pairing with "+
								"the gradient of P(j) is its sum against the partials of P(j)",
							func(d *Argument, inW Fact) {
								parts := d.Conjuncts(
									inW,
									"w lies in M^{0..n}",
									"w pairs to zero with every gradient")
								isTuple := d.Have(
									"w is a tuple of length n + 1",
									"ring_tuple(field_ring(M), n + 1, w)",
									By(parts[0], tuple))
								killed := d.Have(
									"killed by the partials at x",
									"«kills»(x, w)",
									d.ForEach(func(j *Expr[Nat]) Action {
										return By(parts[1].At(j), pairings.At(w, j))
									}))
								d.Show(
									"both",
									By(isTuple, killed))
							})
						c.Backward(
							"a tuple killed by the partials at x pairs to zero with every gradient",
							func(d *Argument, given Fact) {
								parts := d.Conjuncts(
									given,
									"w is a tuple of length n + 1",
									"killed by the partials at x")
								vector := d.Have(
									"w lies in M^{0..n}",
									"w ∈ finite_supp(M.zero, M.carrier, {i:num | i ≤ n})",
									By(parts[0], tuple))
								paired := d.Have(
									"w pairs to zero with the gradient of each P(j)",
									Statement{
										Binders: "∀j:num.",
										Hypotheses: []string{
											"j ∈ {j:num | j < r}",
										},
										Conclusion: "module_sum(M.add, M.zero, {i:num | i ≤ n}, λi:num. «gradient»(x, P(j), i) * w(i)) = " +
											"M.zero",
									},
									d.ForEach(func(j *Expr[Nat]) Action {
										return By(parts[1].At(j), pairings.At(w, j))
									}))
								d.Show(
									"so w lies in the annihilator",
									By(vector, paired))
							})
					}))

				b.Iff()
				b.Forward(
					"an annihilator of dimension two holds two independent tuples and no three",
					func(c *Argument, smooth Fact) {
						planar := c.Have(
							"the annihilator has dimension two",
							"module_dim(field_ring(M), restrict_module(«space», «annihilator»(x))) = 2",
							By(smooth, rank))
						clauses := c.Conjuncts(
							c.Simplified(planar, Fwd(plane)),
							"the annihilator holds two vectors with only the trivial relation",
							"any three of its vectors satisfy a nontrivial one")
						p, q, pair := c.Unpack2As[Fun[Nat, A], Fun[Nat, A]](clauses[0], "p", "q")
						onPair := c.Conjuncts(
							pair,
							"p lies in the annihilator",
							"so does q",
							"in a relation between p and q the coefficient of p is zero",
							"and so is that of q")
						pIs := c.Conjuncts(
							c.Simplified(onPair[0], Fwd(members)),
							"p is a tuple of length n + 1",
							"killed by the partials at x")
						qIs := c.Conjuncts(
							c.Simplified(onPair[1], Fwd(members)),
							"q is a tuple of length n + 1",
							"killed by the partials at x")
						pairs := c.Have(
							"p and q are two tuples killed by the partials with only the trivial coordinatewise relation",
							"«pairs»(x)",
							Derive(func(d *Argument) {
								d.Take(p)
								d.Take(q)
								trivial := d.Have(
									"a relation of p and q at every coordinate below n + 1 is a vector relation, so trivial",
									Statement{
										Binders: "∀s t:A.",
										Hypotheses: []string{
											"s ∈ M.carrier",
											"t ∈ M.carrier",
											"∀c:num. c < n + 1 ⇒ s * p(c) + t * q(c) = M.zero",
										},
										Conclusion: "s = M.zero ∧ t = M.zero",
									},
									Derive(func(e *Argument) {
										s := e.FixAs[A]("s")
										t := e.FixAs[A]("t")
										relation := e.Conjuncts(
											e.Assume(),
											"s is a scalar",
											"so is t",
											"s p + t q vanishes below n + 1")
										e.Show(
											"as a vector relation it forces s = t = 0",
											By(
												relation[0],
												relation[1],
												relation[2],
												pIs[0],
												qIs[0],
												onPair[2].At(s, t),
												onPair[3].At(s, t),
												pairRelation.At(p, q, s, t)))
									}))
								d.Show(
									"the two tuples, killed by the partials, with only the trivial relation",
									By(pIs[0], qIs[0], pIs[1], qIs[1], trivial))
							}))
						triples := c.Have(
							"three tuples killed by the partials lie in the annihilator, "+
								"so satisfy a nontrivial relation, coordinatewise",
							"«triples»(x)",
							Derive(func(d *Argument) {
								a := d.FixAs[Fun[Nat, A]]("a")
								bb := d.FixAs[Fun[Nat, A]]("b")
								dd := d.FixAs[Fun[Nat, A]]("d")
								given := d.Conjuncts(
									d.Assume(),
									"a is a tuple of length n + 1",
									"so is b",
									"and d",
									"a is killed by the partials at x",
									"so is b",
									"and d")
								aIn := d.Have(
									"a lies in the annihilator",
									"a ∈ «annihilator»(x)",
									By(given[0], given[3], members.At(a)))
								bIn := d.Have(
									"so does b",
									"b ∈ «annihilator»(x)",
									By(given[1], given[4], members.At(bb)))
								dIn := d.Have(
									"and d",
									"d ∈ «annihilator»(x)",
									By(given[2], given[5], members.At(dd)))
								s, t, u, relation := d.Obtain3As[A, A, A](
									"a, b and d satisfy a nontrivial vector relation",
									"∃s t u:A. "+
										"    s ∈ M.carrier ∧ "+
										"    t ∈ M.carrier ∧ "+
										"    u ∈ M.carrier ∧ "+
										"    ¬(s = M.zero ∧ t = M.zero ∧ u = M.zero) ∧ "+
										"    fun_add(M.add, "+
										"        fun_add(M.add, fun_smul(M.mul, s, a), fun_smul(M.mul, t, b)), "+
										"        fun_smul(M.mul, u, d)) = "+
										"    fun_zero(M.zero)",
									By(aIn, bIn, dIn, clauses[1].At(a, bb, dd)))
								parts := d.Conjuncts(
									relation,
									"s is a scalar",
									"so is t",
									"and u",
									"not all three are zero",
									"s a + t b + u d = 0")
								d.Take(s)
								d.Take(t)
								d.Take(u)
								d.Show(
									"which holds at every coordinate below n + 1",
									By(
										parts[0],
										parts[1],
										parts[2],
										parts[3],
										parts[4],
										given[0],
										given[1],
										given[2],
										tripleRelation.At(a, bb, dd, s, t, u)))
							}))
						c.Show(
							"both clauses hold at x",
							By(pairs, triples))
					})
				b.Backward(
					"two independent tuples killed by the partials, and no three, make the annihilator a plane",
					func(c *Argument, both Fact) {
						given := c.Conjuncts(
							both,
							"two tuples killed by the partials with only the trivial relation",
							"any three such tuples satisfy a nontrivial relation")
						p, q, pair := c.Unpack2As[Fun[Nat, A], Fun[Nat, A]](given[0], "p", "q")
						onPair := c.Conjuncts(
							pair,
							"p is a tuple of length n + 1",
							"so is q",
							"p is killed by the partials at x",
							"so is q",
							"p and q have only the trivial coordinatewise relation")
						pairInW := c.Have(
							"so the annihilator holds two vectors with only the trivial relation",
							"∃u v:(num → A). "+
								"    u ∈ «annihilator»(x) ∧ "+
								"    v ∈ «annihilator»(x) ∧ "+
								"    (∀s t:A. "+
								"        s ∈ M.carrier ∧ "+
								"        t ∈ M.carrier ∧ "+
								"        fun_add(M.add, fun_smul(M.mul, s, u), fun_smul(M.mul, t, v)) = fun_zero(M.zero) ⇒ "+
								"        s = M.zero ∧ t = M.zero)",
							Derive(func(d *Argument) {
								d.Take(p)
								d.Take(q)
								trivial := d.Have(
									"a vector relation between p and q holds at every coordinate, so is trivial",
									Statement{
										Binders: "∀s t:A.",
										Hypotheses: []string{
											"s ∈ M.carrier",
											"t ∈ M.carrier",
											"fun_add(M.add, fun_smul(M.mul, s, p), fun_smul(M.mul, t, q)) = fun_zero(M.zero)",
										},
										Conclusion: "s = M.zero ∧ t = M.zero",
									},
									Derive(func(e *Argument) {
										s := e.FixAs[A]("s")
										t := e.FixAs[A]("t")
										relation := e.Conjuncts(
											e.Assume(),
											"s is a scalar",
											"so is t",
											"s p + t q = 0")
										e.Show(
											"read coordinatewise, it forces s = t = 0",
											By(
												relation[0],
												relation[1],
												relation[2],
												onPair[0],
												onPair[1],
												onPair[4].At(s, t),
												pairRelation.At(p, q, s, t)))
									}))
								d.Show(
									"p and q lie in the annihilator with only the trivial relation",
									By(onPair[0], onPair[1], onPair[2], onPair[3], members.At(p), members.At(q), trivial))
							}))
						tripleInW := c.Have(
							"and any three vectors of it, tuples killed by the partials, satisfy a nontrivial relation",
							Statement{
								Binders: "∀a b d:(num → A).",
								Hypotheses: []string{
									"a ∈ «annihilator»(x)",
									"b ∈ «annihilator»(x)",
									"d ∈ «annihilator»(x)",
								},
								Conclusion: "∃s t u:A. " +
									"    s ∈ M.carrier ∧ " +
									"    t ∈ M.carrier ∧ " +
									"    u ∈ M.carrier ∧ " +
									"    ¬(s = M.zero ∧ t = M.zero ∧ u = M.zero) ∧ " +
									"    fun_add(M.add, " +
									"        fun_add(M.add, fun_smul(M.mul, s, a), fun_smul(M.mul, t, b)), " +
									"        fun_smul(M.mul, u, d)) = " +
									"    fun_zero(M.zero)",
							},
							Derive(func(d *Argument) {
								a := d.FixAs[Fun[Nat, A]]("a")
								bb := d.FixAs[Fun[Nat, A]]("b")
								dd := d.FixAs[Fun[Nat, A]]("d")
								inW := d.Conjuncts(
									d.Assume(),
									"a lies in the annihilator",
									"so does b",
									"and d")
								aIs := d.Conjuncts(
									d.Simplified(inW[0], Fwd(members)),
									"a is a tuple of length n + 1",
									"killed by the partials at x")
								bIs := d.Conjuncts(
									d.Simplified(inW[1], Fwd(members)),
									"b is a tuple of length n + 1",
									"killed by the partials at x")
								dIs := d.Conjuncts(
									d.Simplified(inW[2], Fwd(members)),
									"d is a tuple of length n + 1",
									"killed by the partials at x")
								s, t, u, relation := d.Obtain3As[A, A, A](
									"a, b and d satisfy a nontrivial coordinatewise relation",
									"∃s t u:A. "+
										"    s ∈ M.carrier ∧ "+
										"    t ∈ M.carrier ∧ "+
										"    u ∈ M.carrier ∧ "+
										"    ¬(s = M.zero ∧ t = M.zero ∧ u = M.zero) ∧ "+
										"    (∀c:num. c < n + 1 ⇒ s * a(c) + t * b(c) + u * d(c) = M.zero)",
									By(aIs[0], bIs[0], dIs[0], aIs[1], bIs[1], dIs[1], given[1].At(a, bb, dd)))
								parts := d.Conjuncts(
									relation,
									"s is a scalar",
									"so is t",
									"and u",
									"not all three are zero",
									"s a + t b + u d vanishes below n + 1")
								d.Take(s)
								d.Take(t)
								d.Take(u)
								d.Show(
									"which is the vector relation s a + t b + u d = 0",
									By(
										parts[0],
										parts[1],
										parts[2],
										parts[3],
										parts[4],
										aIs[0],
										bIs[0],
										dIs[0],
										tripleRelation.At(a, bb, dd, s, t, u)))
							}))
						c.Show(
							"so the annihilator has dimension two, and the span n − 1",
							By(rank, plane, pairInW, tripleInW))
					})
			}))

		arg.Iff()
		arg.Forward(
			"the plane condition holds at every normalized zero x of the family: "+
				"x is a point of the curve, where the gradients span n − 1 dimensions",
			func(b *Argument, smooth Fact) {
				x := b.FixAs[Fun[Nat, A]]("x")
				zeroOfP := b.Assume()
				point := b.Have(
					"x is a point of the curve",
					"x ∈ projective_equation_points(field_ring(M), k, M.carrier, n, image(P, {j:num | j < r}))",
					By(zeroOfP, projective_curve.PointsAsNormalizedZeros.At(fieldOps, k, n, r, P, x)))
				b.Show(
					"so the plane condition holds there",
					By(Normalized, point, smooth.At(x), perPoint.At(x)))
			})
		arg.Backward(
			"the gradients span n − 1 dimensions at every point x of the curve: "+
				"x is a normalized zero of the family, where the plane condition holds",
			func(b *Argument, planes Fact) {
				x := b.FixAs[Fun[Nat, A]]("x")
				point := b.Assume()
				zeroOfP := b.Have(
					"x is a normalized zero of the family",
					"«normalizedZero»(x)",
					By(point, projective_curve.PointsAsNormalizedZeros.At(fieldOps, k, n, r, P, x)))
				b.Show(
					"so the gradients span n − 1 dimensions there",
					By(point, zeroOfP, planes.At(x), perPoint.At(x)))
			})
	}),
})}

// CarriedSmoothness — along a ring homomorphism ι of an algebraically closed
// field M into another, N, a curve given by finitely many polynomials E over
// a subfield k of M meets the Jacobian condition (at every point the
// gradients span n − 1 dimensions) over M exactly when the carried curve
// meets it over N. The finite set E is listed as P(0), …, P(r − 1), with
// r = card(E), and the partials of the list are flattened into one family,
// Q(j·(n + 1) + c) = ∂_c P(j), division by n + 1 recovering j and c. Over M
// the condition is JacobianKernelCriterion's at P and Q; over N it is the
// criterion's at the carried families λj. λm. ι(P(j, m)) and
// λl. λm. ι(Q(l, m)), the second listing the partials of the first since a
// partial derivative commutes with carrying the coefficients
// (PolynomialPartialMap). The criterion's other side is a first-order
// sentence in the coefficients of P and Q, polynomials over M in n + 1
// variables, and ι, an embedding of one algebraically closed field into
// another, is elementary (ByElementarity, the embedding mode).
var CarriedSmoothness = carriedSmoothnessThm{family.Add(registry.ProofEntry{
	Name: "CarriedSmoothness",
	Key:  "prop_bd6a1ee2f36a3f2e",
	Reading: "Both fields algebraically closed is what makes ι elementary, the one step " +
		"that crosses from M to N. E finite is what lists the equations as P(0), …, P(r − 1), " +
		"so that the condition is a sentence about finitely many coefficients. E over k is what " +
		"makes ι a ring homomorphism on the coefficients of every equation, so that the carried " +
		"gradients are the gradients of the carried equations. Nothing asks k to be finite.",
	Build: family.Theorem(Statement{
		Binders: "∀M:field_on(A). " +
			"∀N:field_on(B). " +
			"∀ι:(A → B). " +
			"∀k:set(A). " +
			"∀n:num. " +
			"∀E:set((num → num) → A).",
		Hypotheses: []string{
			"algebraically_closed_field(M)",
			"algebraically_closed_field(N)",
			"ring_homomorphism(field_ring(M), field_ring(N), ι)",
			"subfield(M, k)",
			"finite(E)",
			"E ⊆ «polynomials».carrier",
		},
		Conclusion: "(∀x:(num → B). " +
			"    x ∈ " +
			"    projective_equation_points(field_ring(N), image(ι, k), N.carrier, n, image(«carried», E)) ⇒ " +
			"    module_dim(field_ring(N), " +
			"        restrict_module(«carriedSpace», " +
			"            module_span(field_ring(N), " +
			"                «carriedSpace», " +
			"                «carriedGradients»(x, image(«carried», E))))) + " +
			"    1 = " +
			"    n) ⇔ " +
			"(∀x:(num → A). " +
			"    x ∈ projective_equation_points(field_ring(M), k, M.carrier, n, E) ⇒ " +
			"    module_dim(field_ring(M), " +
			"        restrict_module(«space», module_span(field_ring(M), «space», «gradients»(x, E)))) + " +
			"    1 = " +
			"    n)",
		Abbrev: Abbrev{
			{Name: "space", Text: "free_module_record(field_ring(M), {i:num | i ≤ n})"},
			{Name: "carriedSpace", Text: "free_module_record(field_ring(N), {i:num | i ≤ n})"},
			{Name: "gradients", Text: "λx:(num → A). λS:set((num → num) → A). " +
				"    {λi:num. " +
				"        COND(i ≤ n, polynomial_algebra_eval(«hilbertCoefficients», field_ring(M), λa:A. a, x, polynomial_algebra_partial(«hilbertCoefficients», i, G)), M.zero):num → " +
				"        A | " +
				"    G:(num → num) → A | " +
				"    G ∈ S}"},
			{Name: "carriedGradients", Text: "λx:(num → B). λS:set((num → num) → B). " +
				"    {λi:num. " +
				"        COND(i ≤ n, polynomial_algebra_eval(«carriedCoefficients», field_ring(N), λa:B. a, x, polynomial_algebra_partial(«carriedCoefficients», i, G)), N.zero):num → " +
				"        B | " +
				"    G:(num → num) → B | " +
				"    G ∈ S}"},
			{Name: "normalizedZero", Text: "λx:(num → A). " +
				"    ring_tuple(field_ring(M), n + 1, x) ∧ " +
				"    (∃j:num. j < n + 1 ∧ x(j) = M.one ∧ (∀i:num. i < j ⇒ x(i) = M.zero)) ∧ " +
				"    (∀j:num. j < r ⇒ polynomial_value(field_ring(M), P(j), x) = M.zero)"},
			{Name: "kills", Text: "λx:(num → A). λa:(num → A). ∀j:num. " +
				"    j < r ⇒ " +
				"    module_sum(M.add, " +
				"        M.zero, " +
				"        {c:num | c < n + 1}, " +
				"        λc:num. polynomial_value(field_ring(M), Q(j * (n + 1) + c), x) * a(c)) = " +
				"    M.zero"},
			{Name: "pairs", Text: "λx:(num → A). ∃a b:(num → A). " +
				"    ring_tuple(field_ring(M), n + 1, a) ∧ " +
				"    ring_tuple(field_ring(M), n + 1, b) ∧ " +
				"    «kills»(x, a) ∧ " +
				"    «kills»(x, b) ∧ " +
				"    (∀s t:A. " +
				"        s ∈ M.carrier ∧ t ∈ M.carrier ∧ (∀c:num. c < n + 1 ⇒ s * a(c) + t * b(c) = M.zero) ⇒ " +
				"        s = M.zero ∧ t = M.zero)"},
			{Name: "triples", Text: "λx:(num → A). ∀a b d:(num → A). " +
				"    ring_tuple(field_ring(M), n + 1, a) ∧ " +
				"    ring_tuple(field_ring(M), n + 1, b) ∧ " +
				"    ring_tuple(field_ring(M), n + 1, d) ∧ " +
				"    «kills»(x, a) ∧ " +
				"    «kills»(x, b) ∧ " +
				"    «kills»(x, d) ⇒ " +
				"    (∃s t u:A. " +
				"        s ∈ M.carrier ∧ " +
				"        t ∈ M.carrier ∧ " +
				"        u ∈ M.carrier ∧ " +
				"        ¬(s = M.zero ∧ t = M.zero ∧ u = M.zero) ∧ " +
				"        (∀c:num. c < n + 1 ⇒ s * a(c) + t * b(c) + u * d(c) = M.zero))"},
			{Name: "carriedNormalizedZero", Text: "λx:(num → B). " +
				"    ring_tuple(field_ring(N), n + 1, x) ∧ " +
				"    (∃j:num. j < n + 1 ∧ x(j) = N.one ∧ (∀i:num. i < j ⇒ x(i) = N.zero)) ∧ " +
				"    (∀j:num. " +
				"        j < r ⇒ " +
				"        polynomial_value(field_ring(N), (λj:num. λm:(num → num). ι(P(j, m)))(j), x) = N.zero)"},
			{Name: "carriedKills", Text: "λx:(num → B). λa:(num → B). ∀j:num. " +
				"    j < r ⇒ " +
				"    module_sum(N.add, " +
				"        N.zero, " +
				"        {c:num | c < n + 1}, " +
				"        λc:num. " +
				"            polynomial_value(field_ring(N), " +
				"                (λl:num. λm:(num → num). ι(Q(l, m)))(j * (n + 1) + c), " +
				"                x) * " +
				"            a(c)) = " +
				"    N.zero"},
			{Name: "carriedPairs", Text: "λx:(num → B). ∃a b:(num → B). " +
				"    ring_tuple(field_ring(N), n + 1, a) ∧ " +
				"    ring_tuple(field_ring(N), n + 1, b) ∧ " +
				"    «carriedKills»(x, a) ∧ " +
				"    «carriedKills»(x, b) ∧ " +
				"    (∀s t:B. " +
				"        s ∈ N.carrier ∧ t ∈ N.carrier ∧ (∀c:num. c < n + 1 ⇒ s * a(c) + t * b(c) = N.zero) ⇒ " +
				"        s = N.zero ∧ t = N.zero)"},
			{Name: "carriedTriples", Text: "λx:(num → B). ∀a b d:(num → B). " +
				"    ring_tuple(field_ring(N), n + 1, a) ∧ " +
				"    ring_tuple(field_ring(N), n + 1, b) ∧ " +
				"    ring_tuple(field_ring(N), n + 1, d) ∧ " +
				"    «carriedKills»(x, a) ∧ " +
				"    «carriedKills»(x, b) ∧ " +
				"    «carriedKills»(x, d) ⇒ " +
				"    (∃s t u:B. " +
				"        s ∈ N.carrier ∧ " +
				"        t ∈ N.carrier ∧ " +
				"        u ∈ N.carrier ∧ " +
				"        ¬(s = N.zero ∧ t = N.zero ∧ u = N.zero) ∧ " +
				"        (∀c:num. c < n + 1 ⇒ s * a(c) + t * b(c) + u * d(c) = N.zero))"},
		},
	}, func(
		a *Argument,
		M field.FieldFact[on.M],
		N field.FieldFact[on.N],
		ι *Arrow[A, B],
		k *Expr[Set[A]],
		n *Expr[Nat],
		E *Expr[Set[Fun[Fun[Nat, Nat], A]]],
		given Fact,
	) {
		type polynomial = Fun[Fun[Nat, Nat], A]
		type carriedPolynomial = Fun[Fun[Nat, Nat], B]
		parts := a.Conjuncts(
			given,
			"M is algebraically closed",
			"N is algebraically closed",
			"ι is a ring homomorphism of M into N",
			"k is a subfield of M",
			"E is finite",
			"the equations are polynomials over k")
		closedM, closedN, hom, subK, finite, equationsOverK :=
			parts[0], parts[1], parts[2], parts[3], parts[4], parts[5]
		fieldM := a.TermAs[FieldOps[A]]("M")
		fieldN := a.TermAs[FieldOps[B]]("N")
		ringM := a.TermAs[module_record.RingOps[A]]("field_ring(M)")
		ringN := a.TermAs[module_record.RingOps[B]]("field_ring(N)")
		kRing := a.TermAs[module_record.RingOps[A]]("«hilbertCoefficients»")
		carriedKRing := a.TermAs[module_record.RingOps[B]]("«carriedCoefficients»")
		carriedK := a.TermAs[Set[B]]("image(ι, k)")
		variables := a.TermAs[Set[Nat]]("{i:num | i ≤ n}")
		next := a.TermAs[Nat]("n + 1")
		r, P, listing := a.Obtain2As[Nat, Fun[Nat, polynomial]](
			"E is finite, so it is the image of the numbers below its size",
			"∃r:num. ∃P:(num → (num → num) → A). E = image(P, {j:num | j < r})",
			Derive(func(b *Argument) {
				count := b.TermAs[Nat]("card(E)")
				below := b.TermAs[Set[Nat]]("{j:num | j < card(E)}")
				size := b.Have(
					"the numbers below card(E) are card(E) many",
					"finite({j:num | j < card(E)}) ∧ card({j:num | j < card(E)}) = card(E)",
					By(num_segment.HasSizeBelowStrict.At(count), cardinality.HasSizeDef.At(below, count)))
				P, enumeration := b.UnpackAs[Fun[Nat, polynomial]](
					GroupPremises(finite, size, cardinality.CardEqBijection.At(below, E)),
					"P")
				b.Take(count)
				b.Take(P)
				b.Show(
					"P maps the numbers below card(E) onto E",
					BySets(enumeration))
			}))
		listedOverK := a.Have(
			"each P(j), j < r, is a polynomial over k",
			"∀j:num. j < r ⇒ P(j) ∈ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})",
			By(
				listing,
				equationsOverK,
				set_image.ImageSubsetIff.At(
					P,
					a.TermAs[Set[Nat]]("{j:num | j < r}"),
					a.TermAs[Set[polynomial]]("polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})"))))
		onK := a.Have(
			"ι is a ring homomorphism on k",
			"ring_homomorphism(«hilbertCoefficients», field_ring(N), ι)",
			By(
				hom,
				subK,
				field.SubfieldSubring.Read(M).At(k),
				ring_homomorphism.RingHomRestrictSource.At(ringM, ringN, ι, k)))
		carriedSubfield := a.Have(
			"so ι(k) is a subfield of N",
			"subfield(N, image(ι, k))",
			By(N, subK, onK, ring_homomorphism.SubfieldHomomorphismEmbedding.Read(M).At(fieldN, k, ι)))
		coefficientMap := a.Have(
			"ι is an isomorphism of k onto ι(k), so a ring homomorphism of k into ι(k)",
			"ring_homomorphism(«hilbertCoefficients», «carriedCoefficients», ι)",
			By(
				hom,
				subK,
				N,
				CarriedPolynomials.Read(M).At(fieldN, ι, k, n),
				ring_homomorphism.RingIsomorphismDef.At(kRing, carriedKRing, ι)))
		polynomialMap := a.Have(
			"so carrying the coefficients is a ring homomorphism "+
				"of the polynomials over k into those over ι(k)",
			"ring_homomorphism(«polynomials», «carriedPolynomials», «carried»)",
			By(
				coefficientMap,
				polynomial_algebra.PolynomialAlgebraMapHomomorphism.At(kRing, carriedKRing, ι, variables)))
		carriedOverK := a.Have(
			"and each carried equation λm. ι(P(j, m)) is a polynomial over ι(k)",
			Statement{
				Binders: "∀j:num.",
				Hypotheses: []string{
					"j < r",
				},
				Conclusion: "(λm:(num → num). ι(P(j, m))) ∈ " +
					"polynomial_algebra(«carriedCoefficients», {i:num | i ≤ n})",
			},
			By(listedOverK, ring_homomorphism.MapIn.Read(polynomialMap)))
		Q, flatDef := a.LetAs[Fun[Nat, polynomial]](
			"Q",
			"λl:num. polynomial_algebra_partial(«hilbertCoefficients», rem(l, n + 1), P(div(l, n + 1)))")
		flattening := a.Have(
			"Q lists the partials of P: j·(n + 1) + c, for c ≤ n, has quotient j and remainder c by n + 1",
			Statement{
				Binders: "∀j c:num.",
				Hypotheses: []string{
					"j < r",
					"c ≤ n",
				},
				Conclusion: "Q(j * (n + 1) + c) = polynomial_algebra_partial(«hilbertCoefficients», c, P(j))",
			},
			Derive(func(b *Argument) {
				j := b.FixAs[Nat]("j")
				c := b.FixAs[Nat]("c")
				bounds := b.Assume()
				division := b.Have(
					"dividing j·(n + 1) + c by n + 1 leaves j and c",
					"div(j * (n + 1) + c, n + 1) = j ∧ rem(j * (n + 1) + c, n + 1) = c",
					ByArith(bounds, nat_div_mod.DivModUniq.At(b.TermAs[Nat]("j * (n + 1) + c"), next, j, c)))
				b.Show(
					"so Q there is the partial of P(j) in the variable c",
					By(flatDef, division))
			}))
		carriedFlattening := a.Have(
			"and carried, Q lists the partials of the carried equations: "+
				"a partial derivative commutes with carrying the coefficients",
			Statement{
				Binders: "∀j c:num.",
				Hypotheses: []string{
					"j < r",
					"c ≤ n",
				},
				Conclusion: "(λm:(num → num). ι(Q(j * (n + 1) + c, m))) = " +
					"polynomial_algebra_partial(«carriedCoefficients», c, λm:(num → num). ι(P(j, m)))",
			},
			Derive(func(b *Argument) {
				j := b.FixAs[Nat]("j")
				c := b.FixAs[Nat]("c")
				bounds := b.Assume()
				equation := b.TermAs[polynomial]("P(j)")
				b.Show(
					"the coefficients of P(j) lie in k, where ι is a ring homomorphism",
					By(
						bounds,
						flattening.At(j, c),
						listedOverK.At(j),
						polynomial_algebra.PolynomialAlgebraMember.At(kRing, variables, equation),
						partial_derivative.PolynomialPartialMap.Read(coefficientMap).At(c, equation)))
			}))
		inclusion := a.Have(
			"a polynomial over k in the variables up to n is one over M in the variables below n + 1",
			"polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n}) ⊆ "+
				"polynomial_algebra(field_ring(M), {i:num | i < n + 1})",
			Simp(Rev(nat_arith.Add1), Fwd(nat_order.LessThanSucIffLessEq)),
			By(
				subK,
				field.SubfieldSubset.At(fieldM, k),
				polynomial_algebra.PolynomialAlgebraOverMono.At(ringM, k, variables)))
		partialsOverK := a.Have(
			"each Q(l), l < r·(n + 1), is a partial of an equation, so a polynomial over k",
			"∀l:num. l < r * (n + 1) ⇒ Q(l) ∈ polynomial_algebra(«hilbertCoefficients», {i:num | i ≤ n})",
			Derive(func(b *Argument) {
				l := b.FixAs[Nat]("l")
				bound := b.Assume()
				quotient := b.TermAs[Nat]("div(l, n + 1)")
				below := b.Have(
					"its quotient by n + 1 is below r",
					"div(l, n + 1) < r",
					ByArith(bound, nat_div_mod.LessEqRightDivEq.At(next, l, r)))
				b.Show(
					"it is the partial of P(div(l, n + 1)) in the variable rem(l, n + 1)",
					By(
						flatDef,
						below,
						listedOverK.At(quotient),
						ring_homomorphism.Source.Read(coefficientMap),
						partial_derivative.PolynomialPartialIn.At(
							kRing, variables, b.TermAs[Nat]("rem(l, n + 1)"), b.TermAs[polynomial]("P(div(l, n + 1))"))))
			}))
		equationBound := a.Have(
			"so each P(j), j < r, is a polynomial over M in the variables below n + 1",
			"∀j:num. j < r ⇒ P(j) ∈ polynomial_algebra(field_ring(M), {i:num | i < n + 1})",
			BySets(listedOverK, inclusion))
		partialBound := a.Have(
			"and so is each Q(l), l < r·(n + 1)",
			"∀l:num. l < r * (n + 1) ⇒ Q(l) ∈ polynomial_algebra(field_ring(M), {i:num | i < n + 1})",
			BySets(partialsOverK, inclusion))
		closedFieldM := a.Have(
			"M is an algebraically closed field",
			"algebraically_closed_field_on(M)",
			By(M, closedM, algebraic_closure.AlgebraicallyClosedFieldOnIff.At(fieldM)))
		closedFieldN := a.Have(
			"N is an algebraically closed field",
			"algebraically_closed_field_on(N)",
			By(N, closedN, algebraic_closure.AlgebraicallyClosedFieldOnIff.At(fieldN)))
		criterionM := a.Have(
			"over M, the listed equations meet the Jacobian condition "+
				"exactly when their partials kill a plane at every normalized zero",
			"(∀x:(num → A). "+
				"    x ∈ projective_equation_points(field_ring(M), k, M.carrier, n, image(P, {j:num | j < r})) ⇒ "+
				"    module_dim(field_ring(M), "+
				"        restrict_module(«space», "+
				"            module_span(field_ring(M), «space», «gradients»(x, image(P, {j:num | j < r}))))) + "+
				"    1 = "+
				"    n) ⇔ "+
				"(∀x:(num → A). «normalizedZero»(x) ⇒ «pairs»(x) ∧ «triples»(x))",
			By(subK, listedOverK, flattening, JacobianKernelCriterion.Read(M).At(k, n, r, P, Q)))
		transfer := a.Have(
			"the partials of P kill a plane at every normalized zero over "+
				"M exactly when the carried partials do over N: ι is elementary",
			"(∀x:(num → A). «normalizedZero»(x) ⇒ «pairs»(x) ∧ «triples»(x)) ⇔ "+
				"(∀x:(num → B). «carriedNormalizedZero»(x) ⇒ «carriedPairs»(x) ∧ «carriedTriples»(x))",
			ByElementarity(nil, closedFieldM, closedFieldN, hom, equationBound, partialBound))
		carriedP := a.TermAs[Fun[Nat, carriedPolynomial]]("λj:num. λm:(num → num). ι(P(j, m))")
		carriedQ := a.TermAs[Fun[Nat, carriedPolynomial]]("λl:num. λm:(num → num). ι(Q(l, m))")
		criterionN := a.Have(
			"over N, the carried equations meet the Jacobian condition exactly "+
				"when the carried partials kill a plane at every normalized zero",
			"(∀x:(num → B). "+
				"    x ∈ "+
				"    projective_equation_points(field_ring(N), "+
				"        image(ι, k), "+
				"        N.carrier, "+
				"        n, "+
				"        image(λj:num. λm:(num → num). ι(P(j, m)), {j:num | j < r})) ⇒ "+
				"    module_dim(field_ring(N), "+
				"        restrict_module(«carriedSpace», "+
				"            module_span(field_ring(N), "+
				"                «carriedSpace», "+
				"                «carriedGradients»(x, "+
				"                    image(λj:num. λm:(num → num). ι(P(j, m)), {j:num | j < r}))))) + "+
				"    1 = "+
				"    n) ⇔ "+
				"(∀x:(num → B). «carriedNormalizedZero»(x) ⇒ «carriedPairs»(x) ∧ «carriedTriples»(x))",
			By(
				carriedSubfield,
				carriedOverK,
				carriedFlattening,
				JacobianKernelCriterion.Read(N).At(carriedK, n, r, carriedP, carriedQ)))
		carriedListing := a.Have(
			"listed, the carried equations are the carried family λj. λm. ι(P(j, m))",
			"image(«carried», E) = image(λj:num. λm:(num → num). ι(P(j, m)), {j:num | j < r})",
			listing.Rw(),
			Simp(Rev(set_image.ImageCompose), Fwd(functions.ComposeApply)),
			Refl())
		a.Show(
			"listed, either curve meets the condition exactly when "+
				"its family kills a plane, and the transfer equates the two",
			carriedListing.Rw(),
			listing.Rw(),
			By(criterionM, transfer, criterionN))
	}),
})}
