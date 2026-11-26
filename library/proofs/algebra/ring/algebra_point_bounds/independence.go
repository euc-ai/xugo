// Linear independence of normalized algebra maps, and the resulting point
// bound for finite-dimensional algebras.

package algebra_point_bounds

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/hom_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/algebra_points"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/registry"
)

// AlgebraModuleOn — a ring map from a field makes a commutative ring a
// module over the field: its regular module, with the scalars carried over.
var AlgebraModuleOn = algebraModuleOnThm{family.Add(registry.ProofEntry{
	Name: "AlgebraModuleOn",
	Key:  "prop_df47a17ece4bddeb",
	Build: family.Theorem(Statement{
		Binders:    "∀K:field_on(A). ∀S:ring_ops(B). ∀i:(A → B).",
		Hypotheses: []string{"comm_ring_on(S)", "ring_homomorphism(field_ring(K), S, i)"},
		Conclusion: "module_on(field_ring(K), «algebraModule»)",
	}, func(a *Argument, K field.FieldFact[on.K], S *Expr[RingOps[B]], i *Arrow[A, B], h Fact) {
		parts := a.Conjuncts(
			h,
			"S is a ring",
			"i is a ring map")
		a.Show(
			"S is a module over itself, and the coefficient map restricts its scalars",
			By(
				module.RegularModuleOn.Read(parts[0]),
				parts[1],
				hom_module.RestrictScalarsModuleOn.At(
					a.TermAs[RingOps[A]]("field_ring(K)"),
					S,
					i,
					a.TermAs[module_record.ModuleOps[B, B]]("regular_module(S)"))))
	}),
})}

// AlgebraPointsIndependent — normalized algebra maps fixing their coefficient
// field are independent in the linear dual. They are characters of S with
// values in the field, and a relation among them, evaluated at each point of
// S, is a combination CharactersIndependent clears.
// The empty prescription leaves algebra_points its ring-map and support
// conditions, so its value map λb:B. K.zero is never read; fixing the field
// is a conjunct of its own, since that slot would need an inverse of i.
var AlgebraPointsIndependent = algebraPointsIndependentThm{family.Add(registry.ProofEntry{
	Name: "AlgebraPointsIndependent",
	Key:  "prop_a7d516820fc493a2",
	Build: family.Theorem(Statement{
		Binders:    "∀K:field_on(A). ∀S:ring_ops(B). ∀i:(A → B).",
		Hypotheses: []string{"comm_ring_on(S)", "ring_homomorphism(field_ring(K), S, i)"},
		Conclusion: "module_independent(field_ring(K), «dual», «points»)",
	}, func(a *Argument, K field.FieldFact[on.K], S *Expr[RingOps[B]], i *Arrow[A, B], h Fact) {
		parts := a.Conjuncts(
			h,
			"S is a ring",
			"i is a ring map")
		ring, scalars := parts[0], parts[1]
		R := a.TermAs[RingOps[A]]("field_ring(K)")
		M := a.TermAs[module_record.ModuleOps[A, B]]("«algebraModule»")
		regular := a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(K))")
		fieldRing := field.RingOn.Read(K)
		regularModule := module.RegularModuleOn.Read(fieldRing)
		space := a.Have(
			"S is a K-module by the coefficient map",
			"module_on(field_ring(K), «algebraModule»)",
			By(ring, scalars, AlgebraModuleOn.Read(K).At(S, i)))
		inDual := a.Have(
			"each normalized point belongs to the dual and is a ring map with values in K, zero outside S",
			Statement{
				Binders: "∀p:(B → A).", Hypotheses: []string{"p ∈ «points»"},
				Conclusion: "p ∈ «dual».carrier ∧ " +
					"(∀x:B. p(x) ∈ K.carrier) ∧ " +
					"ring_homomorphism(S, field_ring(K), p) ∧ " +
					"(∀x:B. x ∉ S.carrier ⇒ p(x) = K.zero)",
			},
			Derive(func(b *Argument) {
				p := b.FixAs[Fun[B, A]]("p")
				point := b.Assume()
				data := b.Have(
					"an algebra point fixes scalars and is normalized",
					"ring_homomorphism(S, field_ring(K), p) ∧ "+
						"(∀a:A. a ∈ K.carrier ⇒ p(i(a)) = a) ∧ "+
						"(∀x:B. x ∉ S.carrier ⇒ p(x) = K.zero)",
					BySets(
						point,
						algebra_points.AlgebraPointsDef.At(
							S, R, b.TermAs[Set[B]]("∅"), b.TermAs[Fun[B, A]]("λb:B. K.zero"))))
				clauses := b.Conjuncts(
					data,
					"p is a ring map",
					"p fixes the scalars",
					"p vanishes outside S")
				linear := b.Have(
					"fixing the scalars makes p linear",
					"module_homomorphism(field_ring(K), «algebraModule», regular_module(field_ring(K)), p)",
					By(
						regularModule,
						ring_homomorphism.MapIn.Read(clauses[0]),
						ring_homomorphism.MapAdd.Read(clauses[0]),
						ring_homomorphism.MapMul.Read(clauses[0]),
						ring_homomorphism.MapIn.Read(scalars),
						space,
						clauses[1],
						module_homomorphism.ModuleHomomorphismDef.At(R, M, regular, p)))
				b.Show(
					"normalization gives a dual member and field values everywhere",
					BySets(
						clauses[0],
						ring_homomorphism.MapIn.Read(clauses[0]),
						comm_ring.ZeroIn.Read(fieldRing),
						linear,
						clauses[2],
						hom_module.InHomSet.At(R, M, regular, p)))
			}))
		a.Do(Unfold(linear_independence.ModuleIndependentDef))
		a.Do(SplitConj(
			Case(
				"the points lie in the dual carrier",
				BySets(inDual)),
			Case(
				"a vanishing finite relation has zero coefficients",
				Derive(func(b *Argument) {
					T := b.FixAs[Set[Fun[B, A]]]("T")
					c := b.FixAs[Fun[Fun[B, A], A]]("c")
					relationParts := b.Conjuncts(
						b.Assume(),
						"the relation is finite",
						"its maps are points",
						"its coefficients lie in K",
						"the linear combination is zero")
					finite, subset, coefficients, relation :=
						relationParts[0], relationParts[1], relationParts[2], relationParts[3]
					p := b.FixAs[Fun[B, A]]("p")
					inT := b.Assume()
					summands := b.Have(
						"all evaluated summands lie in K",
						"∀f:(B → A). ∀z:B. f ∈ T ⇒ c(f) * f(z) ∈ K.carrier",
						BySets(comm_ring.MulIn.Read(fieldRing), coefficients, inDual, subset))
					vanishes := b.Have(
						"evaluate the zero relation at each point",
						"∀x:B. module_sum(K.add, K.zero, T, λf:(B → A). c(f) * f(x)) = K.zero",
						Derive(func(d *Argument) {
							x := d.FixAs[B]("x")
							d.Do(relation.CongrArg(d.TermAs[Fun[Fun[B, A], A]]("λh:(B → A). h(x)").Core()))
							evaluated := d.Unfolded(
								d.Hyp(
									"(λh:(B → A). h(x))( "+
										"    module_sum(fun_add(K.add), fun_zero(K.zero), T, λf:(B → A). fun_smul(c(f), f))) = "+
										"(λh:(B → A). h(x))(fun_zero(K.zero))"),
								function_module.FunSmulDef)
							d.Show(
								"evaluation commutes with this finite sum",
								By(
									regularModule,
									finite,
									summands,
									evaluated,
									function_module.ModuleSumApply.At(
										R, regular, T, d.TermAs[Fun2[Fun[B, A], B, A]]("λf:(B → A). λz:B. c(f) * f(z)"), x),
									function_module.FunZeroDef.At(d.TermAs[A]("K.zero"), x)))
						}))
					characters := b.Have(
						"each map of T fixes one and keeps the product on S, with values in K",
						Statement{
							Binders: "∀f:(B → A).", Hypotheses: []string{"f ∈ T"},
							Conclusion: "f(S.one) = K.one ∧ " +
								"(∀x:B. x ∈ S.carrier ⇒ f(x) ∈ K.carrier) ∧ " +
								"(∀x y:B. x ∈ S.carrier ∧ y ∈ S.carrier ⇒ f(x * y) = f(x) * f(y))",
						},
						Derive(func(d *Argument) {
							d.FixAs[Fun[B, A]]("f")
							inMap := d.Assume()
							values := d.Have(
								"f is a ring map with values in K",
								"ring_homomorphism(S, field_ring(K), f) ∧ (∀x:B. f(x) ∈ K.carrier)",
								BySets(inMap, subset, inDual))
							facts := d.Conjuncts(
								values,
								"f is a ring map",
								"its values lie in K")
							d.Show(
								"a ring map fixes one and keeps the product",
								By(facts[1], ring_homomorphism.MapOne.Read(facts[0]), ring_homomorphism.MapMul.Read(facts[0])))
						}))
					separated := b.Have(
						"two distinct maps of T differ on S, both vanishing outside it",
						"∀f g:(B → A). f ∈ T ∧ g ∈ T ∧ f ≠ g ⇒ ∃x:B. x ∈ S.carrier ∧ f(x) ≠ g(x)",
						Derive(func(d *Argument) {
							d.FixAs[Fun[B, A]]("f")
							d.FixAs[Fun[B, A]]("g")
							members := d.Assume()
							outside := d.Have(
								"both vanish outside S",
								"∀x:B. x ∉ S.carrier ⇒ f(x) = K.zero ∧ g(x) = K.zero",
								BySets(members, subset, inDual))
							d.Show(
								"maps agreeing on S and outside it are equal",
								By(members, outside))
						}))
					b.Show(
						"the maps of T are independent characters of S over the domain K",
						By(
							comm_ring.OneIn.Read(ring),
							comm_ring.MulIn.Read(ring),
							finite,
							characters,
							separated,
							coefficients,
							vanishes,
							inT,
							linear_independence.CharactersIndependent.Read(
								integral_domain.FieldIntegralDomain.Read(K)).AsFact().At(
								b.TermAs[Op[B]]("S.mul"),
								b.TermAs[B]("S.one"),
								b.TermAs[Set[B]]("S.carrier"),
								T,
								b.TermAs[Fun2[Fun[B, A], B, A]]("λf:(B → A). λx:B. f(x)"),
								c,
								p)))
				}))))
	}),
})}

// AlgebraPointsBound — a finite-dimensional algebra has finitely many
// normalized maps to its coefficient field, at most its dimension: the maps
// are independent in the dual, whose dimension equals the algebra's.
var AlgebraPointsBound = algebraPointsBoundThm{family.Add(registry.ProofEntry{
	Name: "AlgebraPointsBound",
	Key:  "prop_8296c9cec034f03",
	Build: family.Theorem(Statement{
		Binders: "∀K:field_on(A). ∀S:ring_ops(B). ∀i:(A → B).",
		Hypotheses: []string{
			"comm_ring_on(S)",
			"ring_homomorphism(field_ring(K), S, i)",
			"finite_dimensional(field_ring(K), «algebraModule»)",
		},
		Conclusion: "finite(«points») ∧ card(«points») ≤ module_dim(field_ring(K), «algebraModule»)",
	}, func(a *Argument, K field.FieldFact[on.K], S *Expr[RingOps[B]], i *Arrow[A, B], h Fact) {
		parts := a.Conjuncts(
			h,
			"S is a ring",
			"i is a ring map",
			"S has finite dimension over K")
		ring, scalarMap, finite := parts[0], parts[1], parts[2]
		R := a.TermAs[RingOps[A]]("field_ring(K)")
		M := a.TermAs[module_record.ModuleOps[A, B]]("«algebraModule»")
		regular := a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(K))")
		inv := a.TermAs[Fun[A, A]]("K.inv")
		a.Show(
			"independent points are bounded by the equal dimensions of the algebra and its dual",
			By(
				module.RegularModuleOn.Read(field.RingOn.Read(K)),
				ring,
				scalarMap,
				AlgebraModuleOn.Read(K).At(S, i),
				field.FieldRingSubfield.Read(K),
				finite,
				hom_module.HomSetModuleOn.At(R, M, regular),
				module_dimension.DualDim.At(R, M, inv),
				AlgebraPointsIndependent.Read(K).At(S, i),
				module_dimension.IndependentBound.At(
					R,
					a.TermAs[module_record.ModuleOps[A, Fun[B, A]]]("«dual»"),
					inv,
					a.TermAs[Set[Fun[B, A]]]("«points»"))))
	}),
})}
