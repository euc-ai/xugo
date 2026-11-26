package multilinear_polynomial

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// MultilinearReconstruction recovers a function value by summing its alternating
// subset coefficients. In the new coordinate the two sums recover the old value
// and the finite difference, whose sum is the new value.
var MultilinearReconstruction = multilinearReconstructionThm{family.Add(registry.ProofEntry{
	Name: "MultilinearReconstruction",
	Key:  "prop_cbf6ecd82da5f035",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀U:set(B). ∀f:(set(B) → A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"finite(U)",
			"∀T:set(B). T ⊆ U ⇒ f(T) ∈ R.carrier",
		},
		Conclusion: "multilinear_eval(R, multilinear_coeff(R, f), U) = f(U)",
		Abbrev: Abbrev{
			{Name: "differenceAt", Text: "λg:(set(B) → A). λx:B. λT:set(B). g(insert(x, T)) - g(T)"},
			{Name: "shifted", Text: "λg:(set(B) → A). λx:B. λT:set(B). multilinear_coeff(R, g, insert(x, T))"},
		},
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		U *Expr[Set[B]],
		f *Arrow[Set[B], A],
		ring comm_ring.CommRingFact[on.R],
		finiteU, valuesOfF Fact,
	) {
		onCube := a.Have(
			"reconstruct all ring-valued functions together so the induction applies to finite differences",
			Statement{
				Binders:    "∀g:(set(B) → A).",
				Hypotheses: []string{"∀T:set(B). T ⊆ U ⇒ g(T) ∈ R.carrier"},
				Conclusion: "multilinear_eval(R, multilinear_coeff(R, g), U) = g(U)",
			},
			ByInduction(finite_set.FiniteInductFresh, finiteU,
				Case(
					"at the origin there is only the constant coefficient",
					Derive(func(b *Argument) {
						g := b.FixAs[Fun[Set[B], A]]("g")
						values := b.Assume()
						atOrigin := b.Have(
							"the value at the origin belongs to the ring",
							"g(∅) ∈ R.carrier",
							By(values, set_order.SubsetRefl.At(b.TermAs[Set[B]]("∅"))))
						constant := b.Have(
							"the constant coefficient is that value",
							"multilinear_coeff(R, g, ∅) = g(∅)",
							By(ring, atOrigin, MultilinearCoeffEmpty.At(R, g)))
						b.Show(
							"evaluation reads the constant coefficient",
							By(
								Normalized,
								ring,
								atOrigin,
								constant,
								MultilinearEvalEmpty.At(R, b.TermAs[Fun[Set[B], A]]("multilinear_coeff(R, g)"))))
					})),
				Case(
					"adjoin a fresh variable and reconstruct its two slices",
					Derive(func(b *Argument) {
						x := b.FixAs[B]("x")
						S := b.FixAs[Set[B]]("S")
						induction := b.Conjuncts(
							b.Assume(),
							"reconstruction on S",
							"x is fresh",
							"S is finite")
						reconstruction, xFresh, finiteS := induction[0], induction[1], induction[2]
						g := b.FixAs[Fun[Set[B], A]]("g")
						values := b.Assume()
						sides := b.Have(
							"both slices take their values in the ring",
							"∀T:set(B). T ⊆ S ⇒ g(T) ∈ R.carrier ∧ g(insert(x, T)) ∈ R.carrier",
							BySets(values))
						diffValues := b.Have(
							"their difference is ring-valued",
							"∀T:set(B). T ⊆ S ⇒ «differenceAt»(g, x, T) ∈ R.carrier",
							By(sides, comm_ring.SubIn.Read(ring)))
						finiteBig := b.Have(
							"the additional variable preserves finiteness",
							"finite(insert(x, S))",
							By(finiteS, finite_set.FiniteRules))
						finiteFaces := b.Have(
							"every face of the enlarged cube is finite",
							"∀T:set(B). T ⊆ insert(x, S) ⇒ finite(T)",
							By(finiteBig, finite_set.FiniteSubset))
						coefficients := b.Have(
							"every coefficient on the enlarged cube lies in the ring",
							"∀T:set(B). T ⊆ insert(x, S) ⇒ multilinear_coeff(R, g, T) ∈ R.carrier",
							Derive(func(d *Argument) {
								T := d.FixAs[Set[B]]("T")
								within := d.Assume()
								smaller := d.Have(
									"the values below T stay in the given cube",
									"∀Y:set(B). Y ⊆ T ⇒ g(Y) ∈ R.carrier",
									By(within, values, set_order.SubsetTrans))
								d.Do(By(ring, smaller, within, finiteFaces, MultilinearCoeffIn.At(R, g, T)))
							}))
						split := b.Have(
							"group the evaluation terms by the new coordinate",
							"multilinear_eval(R, multilinear_coeff(R, g), insert(x, S)) = "+
								"multilinear_eval(R, multilinear_coeff(R, g), S) + multilinear_eval(R, «shifted»(g, x), S)",
							By(
								ring,
								finiteS,
								xFresh,
								coefficients,
								MultilinearEvalInsert.At(R, b.TermAs[Fun[Set[B], A]]("multilinear_coeff(R, g)"), S, x)))
						change := b.Have(
							"coefficients containing x are the coefficients of the finite difference",
							Statement{
								Binders:    "∀T:set(B).",
								Hypotheses: []string{"T ⊆ S"},
								Conclusion: "multilinear_coeff(R, g, insert(x, T)) = multilinear_coeff(R, «differenceAt»(g, x), T)",
							},
							Derive(func(d *Argument) {
								T := d.FixAs[Set[B]]("T")
								within := d.Assume()
								shiftedValues := d.Have(
									"adjoining x to T keeps its subsets in the cube",
									"∀Y:set(B). Y ⊆ insert(x, T) ⇒ g(Y) ∈ R.carrier",
									BySets(within, values))
								fresh := d.Have(
									"x is fresh for T",
									"x ∉ T",
									BySets(xFresh, within))
								d.Do(By(
									ring,
									shiftedValues,
									fresh,
									finiteS,
									within,
									MultilinearCoeffInsert.At(R, g, T, x),
									finite_set.FiniteSubset.At(T, S)))
							}))
						same := b.Have(
							"these coefficients give the same evaluation on S",
							"multilinear_eval(R, «shifted»(g, x), S) = "+
								"multilinear_eval(R, multilinear_coeff(R, «differenceAt»(g, x)), S)",
							Unfold(MultilinearEvalDef),
							By(
								change,
								module.ModuleSumCongruence.At(
									b.TermAs[Op[A]]("R.add"),
									b.TermAs[A]("R.zero"),
									b.TermAs[Set[Set[B]]]("{T:set(B) | T ⊆ S}"),
									b.TermAs[Fun[Set[B], A]]("«shifted»(g, x)"),
									b.TermAs[Fun[Set[B], A]]("multilinear_coeff(R, «differenceAt»(g, x))"))))
						old := b.Have(
							"reconstruct the slice without x",
							"multilinear_eval(R, multilinear_coeff(R, g), S) = g(S)",
							By(reconstruction.At(g), sides))
						difference := b.Have(
							"reconstruct the finite difference on S",
							"multilinear_eval(R, multilinear_coeff(R, «differenceAt»(g, x)), S) = g(insert(x, S)) - g(S)",
							By(reconstruction.At(b.TermAs[Fun[Set[B], A]]("«differenceAt»(g, x)")), diffValues))
						endpoints := b.Have(
							"the two endpoint values lie in the ring",
							"g(S) ∈ R.carrier ∧ g(insert(x, S)) ∈ R.carrier",
							By(sides, set_order.SubsetRefl.At(S)))
						restore := b.Have(
							"adding the finite difference gives the value with x",
							"g(S) + (g(insert(x, S)) - g(S)) = g(insert(x, S))",
							ByArith(ring, endpoints))
						b.Show(
							"the two slices reconstruct that value",
							By(old, split, difference, same, restore))
					}))))
		a.Show(
			"apply reconstruction to the given function",
			By(valuesOfF, onCube.At(f)))
	}),
})}

// MultilinearEvalInjective recovers each coefficient from the values on its subsets.
// The value at X contains c(X) once. Every other term has already been determined
// by the values on proper subsets of X, so its contribution cancels.
var MultilinearEvalInjective = multilinearEvalInjectiveThm{family.Add(registry.ProofEntry{
	Name: "MultilinearEvalInjective",
	Key:  "prop_5bdbe1326ff6d5ce",
	Build: family.Sections(Statement{
		Binders: "∀R:ring_ops(A). ∀c d:(set(B) → A). ∀U S:set(B).",
		Hypotheses: []string{
			"comm_ring_on(R)", "finite(U)",
			"∀T:set(B). " +
				"    T ⊆ U ⇒ " +
				"    c(T) ∈ R.carrier ∧ d(T) ∈ R.carrier ∧ multilinear_eval(R, c, T) = multilinear_eval(R, d, T)",
			"S ⊆ U",
		},
		Conclusion: "c(S) = d(S)",
		Abbrev: Abbrev{
			{Name: "proper", Text: "λX:set(B). delete({Y:set(B) | Y ⊆ X}, X)"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		peel := ctx.Lemma(Statement{
			Binders: "∀R:ring_ops(A). ∀c:(set(B) → A). ∀S:set(B).",
			Hypotheses: []string{
				"comm_ring_on(R)",
				"finite(S)",
				"∀T:set(B). T ⊆ S ⇒ c(T) ∈ R.carrier",
			},
			Conclusion: "multilinear_eval(R, c, S) = c(S) + module_sum(R.add, R.zero, «proper»(S), c)",
		}, func(
			a *Argument,
			R *Expr[RingOps[A]],
			c *Arrow[Set[B], A],
			S *Expr[Set[B]],
			ring comm_ring.CommRingFact[on.R],
			finite, values Fact,
		) {
			a.Do(Unfold(MultilinearEvalDef), By(
				finite,
				values,
				finite_set.FinitePowerset.At(S),
				set_order.SubsetRefl.At(S),
				module.ModuleSumDeleteMonoid.Read(comm_ring.AddMonoidOn.Read(ring)).At(
					a.TermAs[Set[Set[B]]]("{T:set(B) | T ⊆ S}"),
					S,
					c)))
		})
		return ctx.Theorem(headline, func(
			a *Argument,
			R *Expr[RingOps[A]],
			c, d *Arrow[Set[B], A],
			U, S *Expr[Set[B]],
			ring comm_ring.CommRingFact[on.R],
			finiteU, sameValues, within Fact,
		) {
			finiteS := a.Have(
				"S is a subset of the finite variable set",
				"finite(S)",
				By(finiteU, within, finite_set.FiniteSubset.At(S, U)))
			a.Do(ByInduction(finite_set.FiniteInductProperSubset, finiteS, Generalizing(within),
				Case(
					"recover the coefficient at X once the proper subsets agree",
					Derive(func(b *Argument) {
						X := b.FixAs[Set[B]]("X")
						descent := b.Assume()
						inU := b.Assume()
						values := b.Have(
							"both coefficient families take ring values below X",
							"∀T:set(B). T ⊆ X ⇒ c(T) ∈ R.carrier ∧ d(T) ∈ R.carrier",
							By(sameValues, inU, set_order.SubsetTrans))
						proper := b.TermAs[Set[Set[B]]]("«proper»(X)")
						lesser := b.Have(
							"the induction hypothesis identifies every proper-subset coefficient",
							"∀T:set(B). T ∈ «proper»(X) ⇒ c(T) = d(T)",
							BySets(descent, inU))
						sameSum := b.Have(
							"the proper subsets contribute the same sum",
							"module_sum(R.add, R.zero, «proper»(X), c) = module_sum(R.add, R.zero, «proper»(X), d)",
							By(
								lesser,
								module.ModuleSumCongruence.At(b.TermAs[Op[A]]("R.add"), b.TermAs[A]("R.zero"), proper, c, d)))
						first := b.Have(
							"separate c(X) from the common contribution",
							"multilinear_eval(R, c, X) = c(X) + module_sum(R.add, R.zero, «proper»(X), c)",
							By(ring, descent, values, At(peel, R, c, X)))
						second := b.Have(
							"separate d(X) from the same contribution",
							"multilinear_eval(R, d, X) = d(X) + module_sum(R.add, R.zero, «proper»(X), d)",
							By(ring, descent, values, At(peel, R, d, X)))
						finiteProper := b.Have(
							"X has finitely many proper subsets",
							"finite(«proper»(X))",
							By(
								descent,
								finite_set.FinitePowerset.At(X),
								finite_set.FiniteDeleteImp.At(b.TermAs[Set[Set[B]]]("{Y:set(B) | Y ⊆ X}"), X)))
						summands := b.Have(
							"the common summands lie in the carrier",
							"∀T:set(B). T ∈ «proper»(X) ⇒ c(T) ∈ R.carrier",
							BySets(values))
						inRing := b.Have(
							"their sum can be cancelled in the additive group",
							"module_sum(R.add, R.zero, «proper»(X), c) ∈ R.carrier",
							By(
								finiteProper,
								summands,
								module.ModuleSumInMonoid.Read(comm_ring.AddMonoidOn.Read(ring)).At(proper, c)))
						b.Show(
							"cancel the common sum from the equal evaluations",
							By(
								inU,
								sameValues,
								first,
								second,
								sameSum,
								inRing,
								At(
									group.RightCancelOn.Read(abelian_group.GroupOn.Read(comm_ring.AddGroupOn.Read(ring))),
									b.TermAs[A]("module_sum(R.add, R.zero, «proper»(X), c)"),
									c.Apply(X),
									d.Apply(X))))
					}))))
		})
	}),
})}

// MultilinearRepresentation characterizes the unique normalized polynomial on the finite cube.
// Its coefficients on the cube are alternating subset sums and all other coefficients vanish.
var MultilinearRepresentation = multilinearRepresentationThm{family.Add(registry.ProofEntry{
	Name: "MultilinearRepresentation",
	Key:  "prop_4ce70d90fcbae168",
	Build: family.Theorem(Statement{
		Binders: "∀R:ring_ops(A). ∀U:set(B). ∀f c:(set(B) → A).",
		Hypotheses: []string{
			"comm_ring_on(R)",
			"finite(U)",
			"∀T:set(B). T ⊆ U ⇒ f(T) ∈ R.carrier",
		},
		Conclusion: "(∀T:set(B). T ⊆ U ⇒ c(T) ∈ R.carrier ∧ multilinear_eval(R, c, T) = f(T)) ∧ " +
			"(∀T:set(B). ¬(T ⊆ U) ⇒ c(T) = R.zero) ⇔ " +
			"c = λT:set(B). COND(T ⊆ U, multilinear_coeff(R, f, T), R.zero)",
	}, func(
		a *Argument,
		R *Expr[RingOps[A]],
		U *Expr[Set[B]],
		f, c *Arrow[Set[B], A],
		ring comm_ring.CommRingFact[on.R],
		finite, values Fact,
	) {
		coeff := a.TermAs[Fun[Set[B], A]]("multilinear_coeff(R, f)")
		canonical := a.Have(
			"the alternating coefficients reconstruct f on each subset of U",
			Statement{
				Binders:    "∀T:set(B).",
				Hypotheses: []string{"T ⊆ U"},
				Conclusion: "multilinear_coeff(R, f, T) ∈ R.carrier ∧ " +
					"multilinear_eval(R, multilinear_coeff(R, f), T) = f(T)",
			},
			Derive(func(b *Argument) {
				T := b.FixAs[Set[B]]("T")
				within := b.Assume()
				finiteT := b.Have(
					"T is finite",
					"finite(T)",
					By(finite, within, finite_set.FiniteSubset.At(T, U)))
				smaller := b.Have(
					"the values below T lie in the carrier",
					"∀Y:set(B). Y ⊆ T ⇒ f(Y) ∈ R.carrier",
					By(values, within, set_order.SubsetTrans))
				b.Do(By(
					ring,
					finiteT,
					smaller,
					MultilinearCoeffIn.At(R, f, T),
					MultilinearReconstruction.At(R, T, f)))
			}))
		a.Do(SplitIff(Forward(
			"a normalized representative agrees with the alternating coefficients",
			Given(func(b *Argument, rep Fact) {
				pieces := b.Conjuncts(
					rep,
					"the evaluations recover f on the cube",
					"the remaining coefficients vanish")
				recovers, vanishes := pieces[0], pieces[1]
				b.Do(Funext())
				T := b.FixAs[Set[B]]("T")
				b.Cases(b.Term("T ⊆ U"))
				b.When(
					"on the cube the evaluations determine the coefficients",
					func(d *Argument, within Fact) {
						same := d.Have(
							"both families have the same evaluations and take values in the ring",
							Statement{
								Binders:    "∀Y:set(B).",
								Hypotheses: []string{"Y ⊆ U"},
								Conclusion: "c(Y) ∈ R.carrier ∧ " +
									"multilinear_coeff(R, f, Y) ∈ R.carrier ∧ " +
									"multilinear_eval(R, c, Y) = multilinear_eval(R, multilinear_coeff(R, f), Y)",
							},
							By(Normalized, recovers, canonical))
						d.Do(By(ring, finite, within, same, MultilinearEvalInjective.At(R, c, coeff, U, T)))
					})
				b.Otherwise(
					"outside the cube normalization determines the coefficient",
					func(d *Argument, outside Fact) {
						d.Do(By(outside, vanishes))
					})
			})), Backward(
			"the normalized alternating coefficients represent f",
			Given(func(b *Argument, formula Fact) {
				inside := b.Have(
					"normalization preserves every coefficient below U",
					"∀Y:set(B). Y ⊆ U ⇒ c(Y) = multilinear_coeff(R, f, Y)",
					By(formula))
				same := b.Have(
					"each evaluation below U reads only the preserved coefficients",
					"∀T:set(B). T ⊆ U ⇒ multilinear_eval(R, c, T) = multilinear_eval(R, multilinear_coeff(R, f), T)",
					Derive(func(d *Argument) {
						d.FixAs[Set[B]]("T")
						within := d.Assume()
						onTerms := d.Have(
							"every summand is indexed below U",
							"∀Y:set(B). Y ∈ {W:set(B) | W ⊆ T} ⇒ c(Y) = multilinear_coeff(R, f, Y)",
							By(within, inside, set_order.SubsetTrans))
						d.Do(Unfold(MultilinearEvalDef), By(
							onTerms,
							module.ModuleSumCongruence.At(
								d.TermAs[Op[A]]("R.add"),
								d.TermAs[A]("R.zero"),
								d.TermAs[Set[Set[B]]]("{W:set(B) | W ⊆ T}"),
								c,
								coeff)))
					}))
				b.Do(By(Normalized, inside, same, canonical, formula))
			}))))
	}),
})}
