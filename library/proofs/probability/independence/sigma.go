// sigma.go — independence of σ-algebras: from generating π-systems, for disjoint
// blocks of an independent family, in either order, down to sub-σ-algebras, and for variable
// families, to Borel images at a subfamily.

package independence

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_product"
	"github.com/euc-ai/xugo/library/proofs/measure/borel_function"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	"github.com/euc-ai/xugo/library/proofs/probability/probability_space"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_algebra"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/sets/sigma_algebra"
	"github.com/euc-ai/xugo/library/registry"
)

// EventIndependentGeneratedSigma — an event independent of every member of a
// π-system is independent of every event of the σ-algebra the π-system
// generates. On σ(D) the set functions U ↦ μ(U ∩ E) and U ↦ μ(E)·μ(U) are
// measures of the same finite total mass μ(E) that agree on D, and two such
// measures agree on the σ-algebra a π-system generates.
var EventIndependentGeneratedSigma = eventIndependentGeneratedSigmaThm{family.Add(registry.ProofEntry{
	Name: "EventIndependentGeneratedSigma",
	Key:  "prop_238f7f610657676f",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀E:set(A). " +
			"∀D:set(set(A)). " +
			"∀V:set(A).",
		Hypotheses: []string{
			"probability_on(Ω, S, μ)",
			"E ∈ S",
			"pi_system_on(Ω, D)",
			"D ⊆ S",
			"∀U:set(A). U ∈ D ⇒ μ(E ∩ U) = μ(E) * μ(U)",
			"V ∈ generated_sigma(Ω, D)",
		},
		Conclusion: "μ(E ∩ V) = μ(E) * μ(V)",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		probability Fact,
		E *Expr[Set[A]],
		event Fact,
		D *Expr[Set[Set[A]]],
		pi, events, product Fact,
		V *Expr[Set[A]],
		generatedV Fact,
	) {
		laws := a.Conjuncts(
			a.Unfolded(probability, probability_space.ProbabilityOnDef),
			"μ is a measure on S",
			"Ω has mass one")
		measure, unitMass := laws[0], laws[1]
		measureLaws := a.Conjuncts(
			a.Unfolded(measure, measure_space.MeasureOn),
			"the events form a σ-algebra on Ω",
			"the empty event has mass zero",
			"μ adds over a disjoint sequence of events")
		sigma, emptyMass, countable := measureLaws[0], measureLaws[1], measureLaws[2]
		massE := μ.Apply(E)
		finite := a.Have(
			"E is an event of a probability, so its mass is finite, the embedding of its real value",
			"μ(E) ≠ extended_infinity ∧ μ(E) = extended_of_real(extended_to_real(μ(E)))",
			By(probability, event, probability_space.ProbabilityEventFinite.At(Ω, S, μ, E)))
		scaled := a.TermAs[Fun[Set[A], ExtendedNonnegReal]]("λU:set(A). μ(E) * μ(U)")
		scaledMeasure := a.Have(
			"U ↦ μ(E)·μ(U) is a measure on S",
			"measure_on(Ω, S, λU:set(A). μ(E) * μ(U))",
			measure_space.MeasureOn.Intro(
				Case(
					"its events are those of μ",
					By(sigma)),
				Case(
					"the empty event has mass μ(E)·0 = 0",
					By(Normalized, emptyMass, extended_nonneg_real.MulZero.At(massE))),
				Case(
					"the finite factor μ(E) passes through the series of a disjoint sequence",
					Derive(func(b *Argument) {
						sequence := b.FixAs[Fun[Nat, Set[A]]]("a")
						disjoint := b.Assume()
						masses := b.TermAs[Fun[Nat, ExtendedNonnegReal]]("λn:num. μ(a(n))")
						b.Show(
							"μ(E) is finite, the embedding of a nonnegative real, and such a factor scales a series termwise",
							By(
								disjoint,
								countable.At(sequence),
								finite,
								extended_nonneg_real.SeriesScale.At(b.TermAs[Real]("extended_to_real(μ(E))"), masses),
								extended_nonneg_real.ToRealNonneg.At(massE)))
					}))))
		restricted := a.TermAs[Fun[Set[A], ExtendedNonnegReal]]("restricted_measure(μ, E)")
		onGenerated := a.Have(
			"both set functions are measures on σ(D)",
			"measure_on(Ω, generated_sigma(Ω, D), restricted_measure(μ, E)) ∧ "+
				"measure_on(Ω, generated_sigma(Ω, D), λU:set(A). μ(E) * μ(U))",
			By(
				measure,
				event,
				sigma,
				events,
				sigma_algebra.GeneratedSigmaInside.At(Ω, S, D),
				scaledMeasure,
				measure_space.RestrictMeasureOnCarrier.At(Ω, S, μ, E),
				measure_space.SubSigmaMeasure))
		insideΩ := a.Have(
			"E is an event, so it lies inside Ω",
			"Ω ∩ E = E",
			BySets(event, sigma, sigma_algebra.SigmaAlgebraOnDef.At(Ω, S)))
		totalMass := a.Have(
			"both give Ω the finite mass μ(E), since μ(Ω) = 1",
			"restricted_measure(μ, E, Ω) = μ(E) * μ(Ω) ∧ restricted_measure(μ, E, Ω) ≠ extended_infinity",
			By(
				Normalized,
				finite,
				unitMass,
				insideΩ,
				measure_space.RestrictMeasureDef.At(μ, E, Ω),
				extended_nonneg_real.MulOne.At(massE)))
		agree := a.Have(
			"they agree on D, where E is independent of each member",
			"∀U:set(A). U ∈ D ⇒ restricted_measure(μ, E, U) = μ(E) * μ(U)",
			Derive(func(b *Argument) {
				U := b.FixAs[Set[A]]("U")
				inD := b.Assume()
				b.Show(
					"the restriction measures U ∩ E, which is E ∩ U",
					By(
						Normalized,
						inD,
						product.At(U),
						measure_space.RestrictMeasureDef.At(μ, E, U),
						set_algebra.InterComm.At(U, E)))
			}))
		a.Show(
			"two measures of equal finite mass that agree on the π-system D agree on σ(D)",
			By(
				Normalized,
				onGenerated,
				totalMass,
				agree,
				pi,
				generatedV,
				measure_space.MeasureDeterminedByPi.At(
					Ω, D, a.TermAs[Set[Set[A]]]("generated_sigma(Ω, D)"), restricted, scaled, V),
				measure_space.RestrictMeasureDef.At(μ, E, V),
				set_algebra.InterComm.At(V, E)))
	}),
})}

// eventsSigmaAlgebra reads the σ-algebra of events off a probability on it:
// a probability is a measure on S, and the events of a measure form a
// σ-algebra on Ω.
func eventsSigmaAlgebra(
	a *Argument,
	Ω *Expr[Set[A]],
	S *Expr[Set[Set[A]]],
	μ *Arrow[Set[A], ExtendedNonnegReal],
	probability Fact,
) Fact {
	return a.Have(
		"the events form a σ-algebra on Ω",
		"sigma_algebra_on(Ω, S)",
		By(
			probability,
			probability_space.ProbabilityOnDef.At(Ω, S, μ),
			measure_space.MeasureOn.At(Ω, S, μ)))
}

// IndependentGeneratedSigma — two π-systems of events, each member of one
// independent of each member of the other, generate independent σ-algebras.
// An event of C is independent of D, hence of σ(D) (EventIndependentGeneratedSigma);
// then an event of σ(D) is independent of C, hence of σ(C), by the same lemma
// with the roles of the two π-systems exchanged. So σ(D) and σ(C) are
// independent, and independence holds in either order.
var IndependentGeneratedSigma = independentGeneratedSigmaThm{family.Add(registry.ProofEntry{
	Name:    "IndependentGeneratedSigma",
	Reading: "Neither generating π-system must contain the carrier.",
	Key:     "prop_3bcb60f090c81091",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀C D:set(set(A)).",
		Hypotheses: []string{
			"probability_on(Ω, S, μ)",
			"pi_system_on(Ω, C)",
			"pi_system_on(Ω, D)",
			"C ⊆ S",
			"D ⊆ S",
			"∀E V:set(A). E ∈ C ∧ V ∈ D ⇒ μ(E ∩ V) = μ(E) * μ(V)",
		},
		Conclusion: "independent_sigma(Ω, S, μ, generated_sigma(Ω, C), generated_sigma(Ω, D))",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		C, D *Expr[Set[Set[A]]],
		probability, piC, piD, eventsC, eventsD, product Fact,
	) {
		sigma := eventsSigmaAlgebra(a, Ω, S, μ, probability)
		σC := a.TermAs[Set[Set[A]]]("generated_sigma(Ω, C)")
		σD := a.TermAs[Set[Set[A]]]("generated_sigma(Ω, D)")
		generatedD := a.Have(
			"σ(D) is a σ-algebra on Ω of events",
			"sigma_algebra_on(Ω, generated_sigma(Ω, D)) ∧ generated_sigma(Ω, D) ⊆ S",
			By(sigma, eventsD, sigma_algebra.GeneratedSigmaInside.At(Ω, S, D)))
		fromC := a.Have(
			"each event of C is independent of every event of σ(D)",
			"∀E V:set(A). E ∈ C ∧ V ∈ generated_sigma(Ω, D) ⇒ μ(E ∩ V) = μ(E) * μ(V)",
			Derive(func(b *Argument) {
				E := b.FixAs[Set[A]]("E")
				V := b.FixAs[Set[A]]("V")
				given := b.Assume()
				b.Show(
					"E is an event independent of every member of D, hence of σ(D)",
					By(
						probability,
						eventsC,
						set_basic.SubsetDef.At(C, S),
						product,
						piD,
						eventsD,
						given,
						EventIndependentGeneratedSigma.At(Ω, S, μ, E, D, V)))
			}))
		fromGeneratedD := a.Have(
			"each event of σ(D) is independent of every event of σ(C)",
			"∀V E:set(A). V ∈ generated_sigma(Ω, D) ∧ E ∈ generated_sigma(Ω, C) ⇒ μ(V ∩ E) = μ(V) * μ(E)",
			Derive(func(b *Argument) {
				V := b.FixAs[Set[A]]("V")
				E := b.FixAs[Set[A]]("E")
				given := b.Assume()
				toC := b.Have(
					"V is independent of every member of C",
					"∀U:set(A). U ∈ C ⇒ μ(V ∩ U) = μ(V) * μ(U)",
					Derive(func(c *Argument) {
						U := c.FixAs[Set[A]]("U")
						inC := c.Assume()
						c.Show(
							"the independence of U from V, read with the factors exchanged",
							By(
								Normalized,
								inC,
								given,
								fromC.At(U, V),
								set_algebra.InterComm.At(U, V),
								extended_nonneg_real.MulComm.At(μ.Apply(U), μ.Apply(V))))
					}))
				b.Show(
					"V is an event of σ(D) ⊆ S independent of C, hence of σ(C), E among its events",
					By(
						probability,
						generatedD,
						set_basic.SubsetDef.At(σD, S),
						toC,
						piC,
						eventsC,
						given,
						EventIndependentGeneratedSigma.At(Ω, S, μ, V, C, E)))
			}))
		reversed := a.Have(
			"σ(D) and σ(C) are σ-algebras of events whose events multiply, so they are independent",
			"independent_sigma(Ω, S, μ, generated_sigma(Ω, D), generated_sigma(Ω, C))",
			By(
				probability,
				sigma,
				eventsC,
				sigma_algebra.GeneratedSigmaInside.At(Ω, S, C),
				generatedD,
				fromGeneratedD,
				IndependentSigmaDef.At(Ω, S, μ, σD, σC)))
		a.Show(
			"and two independent σ-algebras are independent in either order",
			By(reversed, IndependentSigmaSymmetric.At(Ω, S, μ, σD, σC)))
	}),
})}

// IndependentFamilyGroups — two disjoint blocks of an independent family of
// σ-algebras join to independent σ-algebras. The rectangles of a block, the
// intersections within Ω of one event from each of finitely many of its
// members, form a π-system of events that generates the block's join. A
// rectangle over K and one over L are the rectangles over M and P of one
// family of events, M and P disjoint, so the product rule over M ∪ P splits
// into the products over M and over P; IndependentGeneratedSigma carries the
// factorization from the two π-systems to the σ-algebras they generate.
var IndependentFamilyGroups = independentFamilyGroupsThm{family.Add(registry.ProofEntry{
	Name: "IndependentFamilyGroups",
	Reading: "K ∩ L = ∅ is load-bearing. K and L may be infinite: the π-system uses " +
		"finite subfamilies only. An empty K gives {∅, Ω}, independent of everything.",
	Key: "prop_76fc84577abce524",
	Build: family.Sections(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀J K L:set(I). " +
			"∀F:(I → set(set(A))).",
		Hypotheses: []string{"independent_sigma_family(Ω, S, μ, J, F)", "K ⊆ J", "L ⊆ J", "K ∩ L = ∅"},
		Conclusion: "independent_sigma(Ω, S, μ, sigma_join(Ω, F, K), sigma_join(Ω, F, L))",
		Abbrev: Abbrev{
			{Name: "rectangles", Text: "λN:set(I). " +
				"    {Ω ∩ ⋂image(E, M) | " +
				"        M:set(I), " +
				"        E:(I → set(A)) | " +
				"        finite(M) ∧ M ⊆ N ∧ (∀i:I. i ∈ M ⇒ E(i) ∈ F(i))}"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		rectanglesInside := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). ∀T:set(set(A)). ∀F:(I → set(set(A))). ∀N:set(I).",
			Hypotheses: []string{
				"sigma_algebra_on(Ω, T)",
				"∀i:I. i ∈ N ⇒ F(i) ⊆ T",
			},
			Conclusion: "«rectangles»(N) ⊆ T",
		}, func(
			a *Argument,
			Ω *Expr[Set[A]],
			T *Expr[Set[Set[A]]],
			F *Arrow[I, Set[Set[A]]],
			N *Expr[Set[I]],
			sigma, members Fact,
		) {
			a.Show(
				"a rectangle, the intersection within Ω of finitely many sets of T, lies in T",
				Unfold(set_basic.SubsetDef),
				Derive(func(b *Argument) {
					b.FixAs[Set[A]]("R")
					M, E, data := b.Unpack2As[Set[I], Fun[I, Set[A]]](b.Assume(), "M", "E")
					parts := b.Conjuncts(
						data,
						"M is finite",
						"M lies in N",
						"E(i) is an event of F(i) at each index of M",
						"R is the intersection of the E(i) within Ω")
					inT := b.Have(
						"each E(i), i ∈ M, lies in T",
						"∀i:I. i ∈ M ⇒ E(i) ∈ T",
						BySets(parts[2], members, parts[1]))
					b.Show(
						"T holds finite intersections within Ω",
						By(
							Normalized,
							parts[0],
							inT,
							parts[3],
							sigma,
							sigma_algebra.SigmaFiniteIntersection.At(Ω, T, M, E)))
				}))
		})
		rectanglesPiSystem := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀F:(I → set(set(A))). ∀N:set(I).",
			Hypotheses: []string{
				"sigma_algebra_on(Ω, S)",
				"∀i:I. i ∈ N ⇒ sigma_algebra_on(Ω, F(i)) ∧ F(i) ⊆ S",
			},
			Conclusion: "pi_system_on(Ω, «rectangles»(N)) ∧ «rectangles»(N) ⊆ S",
		}, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			F *Arrow[I, Set[Set[A]]],
			N *Expr[Set[I]],
			sigma, blocks Fact,
		) {
			inside := a.Have(
				"the rectangles are events",
				"«rectangles»(N) ⊆ S",
				By(sigma, blocks, At(rectanglesInside, Ω, S, F, N)))
			meets := a.Have(
				"two rectangles meet in a rectangle",
				"∀s t:set(A). s ∈ «rectangles»(N) ∧ t ∈ «rectangles»(N) ⇒ s ∩ t ∈ «rectangles»(N)",
				Derive(func(b *Argument) {
					b.FixAs[Set[A]]("s")
					b.FixAs[Set[A]]("t")
					both := b.Conjuncts(
						b.Assume(),
						"s is a rectangle",
						"t is a rectangle")
					M, _, sData := b.Unpack2As[Set[I], Fun[I, Set[A]]](both[0], "M", "E")
					sParts := b.Conjuncts(
						sData,
						"M is finite",
						"M lies in N",
						"E(i) is an event of F(i) at each index of M",
						"s is the intersection of the E(i) within Ω")
					P, _, tData := b.Unpack2As[Set[I], Fun[I, Set[A]]](both[1], "P", "D")
					tParts := b.Conjuncts(
						tData,
						"P is finite",
						"P lies in N",
						"D(i) is an event of F(i) at each index of P",
						"t is the intersection of the D(i) within Ω")
					_, padded := b.LetAs[Fun[I, Set[A]]]("H", "λi:I. COND(i ∈ M, E(i), Ω) ∩ COND(i ∈ P, D(i), Ω)")
					eventsH := b.Have(
						"E and D padded by Ω meet in an event of F(i) at each index of M ∪ P",
						"∀i:I. i ∈ M ∪ P ⇒ H(i) ∈ F(i)",
						Derive(func(c *Argument) {
							i := c.FixAs[I]("i")
							index := c.Assume()
							sigmaI := c.Have(
								"F(i) is a σ-algebra on Ω, i lying in N",
								"sigma_algebra_on(Ω, F(i))",
								BySets(blocks.At(i), index, sParts[1], tParts[1]))
							paddedE := c.Have(
								"E(i) on M and Ω off it is an event of F(i)",
								"COND(i ∈ M, E(i), Ω) ∈ F(i)",
								By(sParts[2].At(i), sigmaI, sigma_algebra.SigmaAlgebraOnDef))
							paddedD := c.Have(
								"D(i) on P and Ω off it is an event of F(i)",
								"COND(i ∈ P, D(i), Ω) ∈ F(i)",
								By(tParts[2].At(i), sigmaI, sigma_algebra.SigmaAlgebraOnDef))
							c.Show(
								"F(i) is closed under intersections",
								padded.Rw(),
								By(paddedE, paddedD, sigmaI, sigma_algebra.SigmaFiniteOperations.At(Ω, F.Apply(i))))
						}))
					meet := b.Have(
						"s ∩ t is the intersection of the H(i) within Ω over M ∪ P",
						"s ∩ t = Ω ∩ ⋂image(H, M ∪ P)",
						sParts[3].Rw(),
						tParts[3].Rw(),
						Simp(Fwd(set_image.IntersImage)),
						BySets(padded))
					b.Show(
						"so s ∩ t is a rectangle over the finite M ∪ P, which lies in N",
						By(
							sParts[0],
							tParts[0],
							eventsH,
							meet,
							sParts[1],
							tParts[1],
							finite_set.FiniteUnion.At(M, P),
							set_order.UnionSubset.At(M, P, N)))
				}))
			// The rectangles named C, a set the set driver keeps whole rather than open as its set-builder.
			a.Let("C", a.TermAs[Set[Set[A]]]("«rectangles»(N)"))
			a.Show(
				"so the rectangles C form a π-system of events on Ω",
				BySets(meets, inside, sigma, sigma_algebra.SigmaAlgebraOnDef.At(Ω, S), sigma_algebra.PiSystemDef))
		})
		rectanglesGenerateJoin := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). ∀F:(I → set(set(A))). ∀N:set(I).",
			Hypotheses: []string{
				"∀i:I. i ∈ N ⇒ sigma_algebra_on(Ω, F(i))",
			},
			Conclusion: "generated_sigma(Ω, «rectangles»(N)) = sigma_join(Ω, F, N)",
		}, func(a *Argument, Ω *Expr[Set[A]], F *Arrow[I, Set[Set[A]]], N *Expr[Set[I]], blocks Fact) {
			within := a.Have(
				"the events of each F(i) lie in Ω",
				"∀i:I. i ∈ N ⇒ F(i) ⊆ {s:set(A) | s ⊆ Ω}",
				By(blocks, sigma_algebra.SigmaAlgebraOnDef))
			generators := a.Have(
				"so do the generators of the join",
				"⋃image(F, N) ⊆ {s:set(A) | s ⊆ Ω}",
				Simp(Fwd(set_image.UnionsImage)),
				BySets(within))
			join := a.TermAs[Set[Set[A]]]("sigma_join(Ω, F, N)")
			joinLaws := a.Conjuncts(
				a.Have(
					"the join is a σ-algebra on Ω holding its generators",
					"sigma_algebra_on(Ω, sigma_join(Ω, F, N)) ∧ ⋃image(F, N) ⊆ sigma_join(Ω, F, N)",
					By(
						generators,
						sigma_algebra.SigmaJoinDef,
						sigma_algebra.GeneratedSigmaAlgebra.At(Ω, a.TermAs[Set[Set[A]]]("⋃image(F, N)")))),
				"the join is a σ-algebra on Ω",
				"the join holds its generators")
			membersInJoin := a.Have(
				"so it holds every event of each F(i), i ∈ N",
				"∀i:I. i ∈ N ⇒ F(i) ⊆ sigma_join(Ω, F, N)",
				BySets(joinLaws[1]))
			inJoin := a.Have(
				"each rectangle lies in the join",
				"«rectangles»(N) ⊆ sigma_join(Ω, F, N)",
				By(joinLaws[0], membersInJoin, At(rectanglesInside, Ω, join, F, N)))
			singles := a.Have(
				"each event of a member over N is a rectangle over one index",
				"∀i:I. ∀u:set(A). i ∈ N ∧ u ∈ F(i) ⇒ u ∈ «rectangles»(N)",
				Derive(func(b *Argument) {
					i := b.FixAs[I]("i")
					b.FixAs[Set[A]]("u")
					member := b.Conjuncts(
						b.Assume(),
						"i lies in N",
						"u is an event of F(i)")
					single := b.Have(
						"u, lying in Ω, is the intersection of the constant family u over {i}",
						"u = Ω ∩ ⋂image(λj:I. u, {i})",
						BySets(within.At(i), member[0], member[1], set_image.IntersImage))
					index := b.Have(
						"{i} lies in N, and u is an event of F(j) at its one index j",
						"{i} ⊆ N ∧ (∀j:I. j ∈ {i} ⇒ u ∈ F(j))",
						BySets(member[0], member[1]))
					b.Show(
						"so u is a rectangle over the finite {i}",
						By(single, index, finite_set.FiniteSing.At(i)))
				}))
			// The rectangles named C, a set the set driver below keeps whole rather than open as its set-builder.
			C, _ := a.LetAs[Set[Set[A]]]("C", "«rectangles»(N)")
			joinInside := a.Have(
				"the sets of the join lie in Ω",
				"sigma_join(Ω, F, N) ⊆ {s:set(A) | s ⊆ Ω}",
				By(joinLaws[0], sigma_algebra.SigmaAlgebraOnDef))
			generated := a.Have(
				"C, lying in the join, generates a σ-algebra on Ω holding it",
				"sigma_algebra_on(Ω, generated_sigma(Ω, C)) ∧ C ⊆ generated_sigma(Ω, C)",
				By(
					inJoin,
					joinInside,
					set_order.SubsetTrans.At(C, join, a.TermAs[Set[Set[A]]]("{s:set(A) | s ⊆ Ω}")),
					sigma_algebra.GeneratedSigmaAlgebra.At(Ω, C)))
			lower := a.Have(
				"the σ-algebra C generates lies in the join, which holds C",
				"generated_sigma(Ω, C) ⊆ sigma_join(Ω, F, N)",
				By(inJoin, joinLaws[0], sigma_algebra.GeneratedSigmaLeast.At(Ω, C, join)))
			generatorsInC := a.Have(
				"each event of a member over N lies in the σ-algebra C generates",
				"⋃image(F, N) ⊆ generated_sigma(Ω, C)",
				Simp(Fwd(set_image.UnionsImage)),
				BySets(singles, generated))
			upper := a.Have(
				"so the join lies in it",
				"sigma_join(Ω, F, N) ⊆ generated_sigma(Ω, C)",
				By(
					generatorsInC,
					generated,
					sigma_algebra.GeneratedSigmaLeast.At(
						Ω,
						a.TermAs[Set[Set[A]]]("⋃image(F, N)"),
						a.TermAs[Set[Set[A]]]("generated_sigma(Ω, C)")),
					sigma_algebra.SigmaJoinDef))
			a.Show(
				"the two σ-algebras coincide",
				By(lower, upper, set_order.SubsetAntisym))
		})
		rectanglesFactor := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). " +
				"∀S:set(set(A)). " +
				"∀μ:(set(A) → extended_nonneg_real). " +
				"∀J K L:set(I). " +
				"∀F:(I → set(set(A))). " +
				"∀U V:set(A).",
			Hypotheses: []string{
				"independent_sigma_family(Ω, S, μ, J, F)",
				"K ⊆ J",
				"L ⊆ J",
				"K ∩ L = ∅",
				"U ∈ «rectangles»(K)",
				"V ∈ «rectangles»(L)",
			},
			Conclusion: "μ(U ∩ V) = μ(U) * μ(V)",
		}, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			J, K, L *Expr[Set[I]],
			F *Arrow[I, Set[Set[A]]],
			U, V *Expr[Set[A]],
			independent, kInJ, lInJ, apart, uRectangle, vRectangle Fact,
		) {
			M, _, uData := a.Unpack2As[Set[I], Fun[I, Set[A]]](uRectangle, "M", "E")
			uParts := a.Conjuncts(
				uData,
				"M is finite",
				"M lies in K",
				"E(i) is an event of F(i) at each index of M",
				"U is the intersection of the E(i) within Ω")
			P, _, vData := a.Unpack2As[Set[I], Fun[I, Set[A]]](vRectangle, "P", "D")
			vParts := a.Conjuncts(
				vData,
				"P is finite",
				"P lies in L",
				"D(i) is an event of F(i) at each index of P",
				"V is the intersection of the D(i) within Ω")
			product := a.Conjuncts(
				a.Unfolded(independent, IndependentFamilyDef),
				"μ is a probability on S",
				"each F(i), i ∈ J, is a σ-algebra of events",
				"a finite intersection of events of the F(i) has the product of their probabilities")[2]
			disjoint := a.Have(
				"M and P are disjoint, as K and L are",
				"M ∩ P = ∅",
				BySets(apart, uParts[1], vParts[1]))
			inJ := a.Have(
				"M ∪ P lies in J",
				"M ∪ P ⊆ J",
				BySets(kInJ, lInJ, uParts[1], vParts[1]))
			G, joined := a.LetAs[Fun[I, Set[A]]]("G", "λi:I. COND(i ∈ M, E(i), D(i))")
			eventsG := a.Have(
				"G(i) is an event of F(i) at each index of M ∪ P",
				"∀i:I. i ∈ M ∪ P ⇒ G(i) ∈ F(i)",
				BySets(uParts[2], vParts[2], joined))
			uG := a.Have(
				"G agrees with E on M, so U is its intersection over M",
				"U = Ω ∩ ⋂image(G, M)",
				uParts[3].Rw(),
				Simp(Fwd(set_image.IntersImage)),
				BySets(joined))
			vG := a.Have(
				"G agrees with D on P, which M misses, so V is its intersection over P",
				"V = Ω ∩ ⋂image(G, P)",
				vParts[3].Rw(),
				Simp(Fwd(set_image.IntersImage)),
				BySets(disjoint, joined))
			union := a.Have(
				"the intersection over M ∪ P is the intersection over M and over P",
				"Ω ∩ ⋂image(G, M ∪ P) = (Ω ∩ ⋂image(G, M)) ∩ (Ω ∩ ⋂image(G, P))",
				Simp(Fwd(set_image.IntersImage)),
				BySets())
			productG := a.Have(
				"G has the product rule over each finite subset of M ∪ P, which lies in J",
				Statement{
					Binders:    "∀Q:set(I).",
					Hypotheses: []string{"finite(Q)", "Q ⊆ M ∪ P"},
					Conclusion: "μ(Ω ∩ ⋂image(G, Q)) = extended_of_real(Π_{i∈Q} extended_to_real(μ(G(i))))",
				},
				Derive(func(b *Argument) {
					Q := b.FixAs[Set[I]]("Q")
					sub := b.Conjuncts(
						b.Assume(),
						"Q is finite",
						"Q lies in M ∪ P")
					b.Show(
						"the given product rule at Q, a finite subset of J at whose indices G(i) is an event of F(i)",
						By(
							product.At(Q, G),
							sub[0],
							sub[1],
							eventsG,
							inJ,
							set_basic.SubsetDef,
							set_order.SubsetTrans.At(Q, b.TermAs[Set[I]]("M ∪ P"), J)))
				}))
			probabilities := a.TermAs[Fun[I, Real]]("λi:I. extended_to_real(μ(G(i)))")
			nonnegative := a.Have(
				"the product over M is nonnegative, each factor being a finite value of the extended reals",
				"&0 ≤ Π_{i∈M} extended_to_real(μ(G(i)))",
				By(extended_nonneg_real.ToRealNonneg, real_product.Nonneg.At(M, probabilities)))
			a.Show(
				"the product rule over M ∪ P splits into the products over M and over P",
				CalcEq(
					Leg(
						a.TermAs[ExtendedNonnegReal]("μ(Ω ∩ ⋂image(G, M ∪ P))"),
						"U ∩ V is the intersection of the G(i) within Ω over M ∪ P",
						By(uG, vG, union)),
					Leg(
						a.TermAs[ExtendedNonnegReal]("extended_of_real(Π_{i∈M ∪ P} extended_to_real(μ(G(i))))"),
						"the product rule at the finite M ∪ P itself",
						By(
							productG.At(a.TermAs[Set[I]]("M ∪ P")),
							uParts[0],
							vParts[0],
							finite_set.FiniteUnion.At(M, P),
							set_order.SubsetRefl.At(a.TermAs[Set[I]]("M ∪ P")))),
					Leg(
						a.TermAs[ExtendedNonnegReal](
							"extended_of_real((Π_{i∈M} extended_to_real(μ(G(i)))) * Π_{i∈P} extended_to_real(μ(G(i))))"),
						"the product over the disjoint union of M and P splits",
						By(
							uParts[0],
							vParts[0],
							disjoint,
							set_basic.DisjointDef,
							real_product.Union.At(M, P, probabilities))),
					Leg(
						a.TermAs[ExtendedNonnegReal](
							"extended_of_real(Π_{i∈M} extended_to_real(μ(G(i)))) * "+
								"extended_of_real(Π_{i∈P} extended_to_real(μ(G(i))))"),
						"the embedding carries a product with a nonnegative factor to the product",
						By(
							nonnegative,
							extended_nonneg_real.OfRealMul.At(
								a.TermAs[Real]("Π_{i∈M} extended_to_real(μ(G(i)))"),
								a.TermAs[Real]("Π_{i∈P} extended_to_real(μ(G(i)))")))),
					FinalLeg(
						"the product rule at M and at P",
						By(
							productG.At(M),
							productG.At(P),
							uParts[0],
							vParts[0],
							uG,
							vG,
							set_order.SubsetUnion.At(M, P),
							set_order.SubsetUnion.At(P, M)))))
		})
		return ctx.Theorem(headline, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			J, K, L *Expr[Set[I]],
			F *Arrow[I, Set[Set[A]]],
			independent, kInJ, lInJ, apart Fact,
		) {
			laws := a.Conjuncts(
				a.Unfolded(independent, IndependentFamilyDef),
				"μ is a probability on S",
				"each F(i), i ∈ J, is a σ-algebra of events",
				"a finite intersection of events of the F(i) has the product of their probabilities")
			probability, blocks := laws[0], laws[1]
			sigma := eventsSigmaAlgebra(a, Ω, S, μ, probability)
			blockK := a.Have(
				"each F(i), i ∈ K, is a σ-algebra of events",
				"∀i:I. i ∈ K ⇒ sigma_algebra_on(Ω, F(i)) ∧ F(i) ⊆ S",
				By(blocks, kInJ, set_basic.SubsetDef))
			blockL := a.Have(
				"each F(i), i ∈ L, is a σ-algebra of events",
				"∀i:I. i ∈ L ⇒ sigma_algebra_on(Ω, F(i)) ∧ F(i) ⊆ S",
				By(blocks, lInJ, set_basic.SubsetDef))
			piK := a.Have(
				"the rectangles over K form a π-system of events",
				"pi_system_on(Ω, «rectangles»(K)) ∧ «rectangles»(K) ⊆ S",
				By(At(rectanglesPiSystem, Ω, S, F, K), blockK, sigma))
			piL := a.Have(
				"the rectangles over L form a π-system of events",
				"pi_system_on(Ω, «rectangles»(L)) ∧ «rectangles»(L) ⊆ S",
				By(At(rectanglesPiSystem, Ω, S, F, L), blockL, sigma))
			joinK := a.Have(
				"they generate the join over K",
				"generated_sigma(Ω, «rectangles»(K)) = sigma_join(Ω, F, K)",
				By(At(rectanglesGenerateJoin, Ω, F, K), blockK))
			joinL := a.Have(
				"they generate the join over L",
				"generated_sigma(Ω, «rectangles»(L)) = sigma_join(Ω, F, L)",
				By(At(rectanglesGenerateJoin, Ω, F, L), blockL))
			factor := a.Have(
				"a rectangle over K and one over L have the product of their probabilities",
				"∀U V:set(A). U ∈ «rectangles»(K) ∧ V ∈ «rectangles»(L) ⇒ μ(U ∩ V) = μ(U) * μ(V)",
				By(At(rectanglesFactor, Ω, S, μ, J, K, L, F), apart, kInJ, lInJ, independent))
			a.Show(
				"so the σ-algebras the two π-systems generate, the two joins, are independent",
				By(
					factor,
					joinK,
					joinL,
					piK,
					piL,
					probability,
					IndependentGeneratedSigma.At(
						Ω,
						S,
						μ,
						a.TermAs[Set[Set[A]]]("«rectangles»(K)"),
						a.TermAs[Set[Set[A]]]("«rectangles»(L)"))))
		})
	}),
})}

// IndependentSigmaSubset — a σ-algebra inside the second of two
// independent σ-algebras is independent of the first.
var IndependentSigmaSubset = independentSigmaSubsetThm{family.Add(registry.ProofEntry{
	Name: "IndependentSigmaSubset",
	Key:  "prop_35201eb0de61afa6",
	Reading: "sigma_algebra_on(Ω, H') is load-bearing: a subfamily of a σ-algebra need " +
		"not be one, and independent_sigma asks both of its sides to be σ-algebras on Ω.",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀G H H':set(set(A)).",
		Hypotheses: []string{
			"independent_sigma(Ω, S, μ, G, H)",
			"sigma_algebra_on(Ω, H')",
			"H' ⊆ H",
		},
		Conclusion: "independent_sigma(Ω, S, μ, G, H')",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		G, H, HPrime *Expr[Set[Set[A]]],
		independent, sigma, inside Fact,
	) {
		laws := a.Unfolded(independent, IndependentSigmaDef)
		a.Show(
			"H' lies in S through H, and its events multiply against those of G as H's do",
			Simp(Fwd(IndependentSigmaDef)),
			BySets(laws, sigma, inside))
	}),
})}

// IndependentSigmaSymmetric — two independent σ-algebras are independent in
// either order: the definition asks the same of both sides, and the product
// rule for an event E of H and an event D of G is the given rule at D and E,
// as E ∩ D = D ∩ E and μ(D)·μ(E) = μ(E)·μ(D).
var IndependentSigmaSymmetric = independentSigmaSymmetricThm{family.Add(registry.ProofEntry{
	Name: "IndependentSigmaSymmetric",
	Key:  "prop_1a235f27365e406",
	Build: family.Theorem(Statement{
		Binders:    "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀G H:set(set(A)).",
		Hypotheses: []string{"independent_sigma(Ω, S, μ, G, H)"},
		Conclusion: "independent_sigma(Ω, S, μ, H, G)",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		G, H *Expr[Set[Set[A]]],
		independent Fact,
	) {
		laws := a.Conjuncts(
			a.Unfolded(independent, IndependentSigmaDef),
			"μ is a probability on S",
			"G is a σ-algebra on Ω",
			"H is a σ-algebra on Ω",
			"the events of G lie in S",
			"the events of H lie in S",
			"an event of G and one of H multiply")
		exchanged := a.Have(
			"an event of H and one of G multiply",
			"∀E D:set(A). E ∈ H ∧ D ∈ G ⇒ μ(E ∩ D) = μ(E) * μ(D)",
			Derive(func(b *Argument) {
				E := b.FixAs[Set[A]]("E")
				D := b.FixAs[Set[A]]("D")
				given := b.Assume()
				b.Show(
					"the product rule at D and E, read with the intersection and the product in the other order",
					By(
						Normalized,
						given,
						laws[5].At(D, E),
						set_algebra.InterComm.At(E, D),
						extended_nonneg_real.MulComm.At(μ.Apply(D), μ.Apply(E))))
			}))
		a.Show(
			"the definition asks of H and G what it asked of G and H",
			Unfold(IndependentSigmaDef),
			By(laws[0], laws[1], laws[2], laws[3], laws[4], exchanged))
	}),
})}

// IndependentVariableFamilyCompose — an independent family of random
// variables stays independent on a subset of its indices with a Borel
// function applied to each variable: h(i) ∘ X(i) is a random variable,
// measurable already for the σ-algebra X(i) generates, so the σ-algebra it
// generates lies inside that one, and the product rule over a finite
// subfamily of K is the given family's over the same subfamily of J.
var IndependentVariableFamilyCompose = independentVariableFamilyComposeThm{family.Add(registry.ProofEntry{
	Name: "IndependentVariableFamilyCompose",
	Key:  "prop_62a83b10581254b7",
	Reading: "K may be empty: the family over ∅ is independent as soon as μ is a probability, " +
		"which the given family supplies. The function h(i) may change with the index i and need be " +
		"Borel only for i ∈ K; K ⊆ J is what lets the given product rule speak of the subfamilies of K.",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀J K:set(I). " +
			"∀X:(I → A → real). " +
			"∀h:(I → real → real).",
		Hypotheses: []string{
			"independent_variable_family(Ω, S, μ, J, X)",
			"K ⊆ J",
			"∀i:I. i ∈ K ⇒ real_measurable(𝕌, borel_sets(real_topology), h(i))",
		},
		Conclusion: "independent_variable_family(Ω, S, μ, K, λi:I. λx:A. h(i, X(i, x)))",
	},
		func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			J, K *Expr[Set[I]],
			X *Arrow2[I, A, Real],
			h *Arrow2[I, Real, Real],
			independent, subfamily, hBorel Fact,
		) {
			variables := a.Conjuncts(
				a.Unfolded(independent, IndependentVariableFamilyDef),
				"each X(i) with i ∈ J is a random variable",
				"and the σ-algebras they generate form an independent family")
			law := a.Conjuncts(
				a.Unfolded(variables[1], IndependentFamilyDef),
				"μ is a probability",
				"each of those σ-algebras is one on Ω inside S",
				"and the product rule holds over every finite subfamily of J")
			composites := a.Have(
				"each h(i) ∘ X(i) with i ∈ K is a random variable, a Borel function of one",
				"∀i:I. i ∈ K ⇒ real_measurable(Ω, S, λx:A. h(i, X(i, x)))",
				Derive(func(b *Argument) {
					i := b.FixAs[I]("i")
					inK := b.Assume()
					b.Show(
						"X(i) is a random variable, i lying in J",
						By(
							variables[0].At(i),
							hBorel.At(i),
							inK,
							subfamily,
							set_basic.SubsetDef,
							borel_function.RealMeasurableCompose))
				}))
			coarser := a.Have(
				"the σ-algebra h(i) ∘ X(i) generates is one on Ω, inside the one X(i) generates and so inside S",
				Statement{
					Binders:    "∀i:I.",
					Hypotheses: []string{"i ∈ K"},
					Conclusion: "sigma_algebra_on(Ω, " +
						"    pullback_sigma(Ω, λx:A. h(i, X(i, x)), borel_sets(real_topology))) ∧ " +
						"pullback_sigma(Ω, λx:A. h(i, X(i, x)), borel_sets(real_topology)) ⊆ " +
						"pullback_sigma(Ω, X(i), borel_sets(real_topology)) ∧ " +
						"pullback_sigma(Ω, λx:A. h(i, X(i, x)), borel_sets(real_topology)) ⊆ S",
				},
				Derive(func(b *Argument) {
					i := b.FixAs[I]("i")
					inK := b.Assume()
					least := b.Have(
						"h(i) ∘ X(i) generates a σ-algebra on Ω, inside the one X(i) generates as h(i) is Borel",
						"sigma_algebra_on(Ω, pullback_sigma(Ω, λx:A. h(i, X(i, x)), borel_sets(real_topology))) ∧ "+
							"pullback_sigma(Ω, λx:A. h(i, X(i, x)), borel_sets(real_topology)) ⊆ "+
							"pullback_sigma(Ω, X(i), borel_sets(real_topology))",
						By(
							borel_function.RealPullbackSigma.At(Ω, b.TermAs[Fun[A, Real]]("λx:A. h(i, X(i, x))")),
							borel_function.RealPullbackCompose.At(
								Ω, b.TermAs[Fun[A, Real]]("X(i)"), b.TermAs[Fun[Real, Real]]("h(i)")),
							hBorel.At(i),
							inK))
					b.Show(
						"and the one X(i) generates lies in S, i lying in J",
						BySets(least, law[1].At(i), inK, subfamily))
				}))
			product := a.Have(
				"the product rule over a finite L ⊆ K is the given family's over L",
				Statement{
					Binders: "∀L:set(I). ∀E:(I → set(A)).",
					Hypotheses: []string{
						"finite(L)",
						"L ⊆ K",
						"∀i:I. i ∈ L ⇒ E(i) ∈ pullback_sigma(Ω, λx:A. h(i, X(i, x)), borel_sets(real_topology))",
					},
					Conclusion: "μ(Ω ∩ ⋂image(E, L)) = extended_of_real(Π_{i∈L} extended_to_real(μ(E(i))))",
				},
				Derive(func(b *Argument) {
					L := b.FixAs[Set[I]]("L")
					E := b.FixAs[Fun[I, Set[A]]]("E")
					events := b.Conjuncts(
						b.Assume(),
						"L is finite",
						"L lies in K",
						"each E(i) is an event of h(i) ∘ X(i)")
					wider := b.Have(
						"so each E(i) is an event of X(i)",
						"∀i:I. i ∈ L ⇒ E(i) ∈ pullback_sigma(Ω, X(i), borel_sets(real_topology))",
						BySets(coarser, events[2], events[1]))
					b.Show(
						"which is the given product rule at L, a finite subset of J",
						By(law[2].At(L, E), events[0], wider, subfamily, events[1], set_order.SubsetTrans))
				}))
			a.Show(
				"so the composites form an independent family over K",
				Unfold(IndependentVariableFamilyDef),
				Unfold(IndependentFamilyDef),
				By(composites, law[0], coarser, product))
		}),
})}

// IndependentVariableFamilyMeasurable — the variables of an independent
// family are random variables on a probability space: each is measurable by
// the first half of the definition, and the probability is read off the
// second, the independence of the σ-algebras they generate.
var IndependentVariableFamilyMeasurable = independentVariableFamilyMeasurableThm{family.Add(registry.ProofEntry{
	Name: "IndependentVariableFamilyMeasurable",
	Key:  "prop_9f411dfa604cb9d4",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀J:set(I). " +
			"∀X:(I → A → real).",
		Hypotheses: []string{"independent_variable_family(Ω, S, μ, J, X)"},
		Conclusion: "probability_on(Ω, S, μ) ∧ (∀i:I. i ∈ J ⇒ real_measurable(Ω, S, X(i)))",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		J *Expr[Set[I]],
		X *Arrow2[I, A, Real],
		independent Fact,
	) {
		variables := a.Conjuncts(
			a.Unfolded(independent, IndependentVariableFamilyDef),
			"each X(i) with i ∈ J is a random variable",
			"and the σ-algebras they generate form an independent family")
		law := a.Unfolded(variables[1], IndependentFamilyDef)
		a.Show(
			"an independent family of σ-algebras lives on a probability space",
			By(variables[0], law))
	}),
})}
