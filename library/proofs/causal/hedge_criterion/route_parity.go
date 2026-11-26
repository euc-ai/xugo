// route_parity.go — the parity sum of a family of routes. Signs sit on the
// vertices of N; routes run inside H ⊆ N along a step map τ, from their
// starts R to their ends T. Summed over the sign configurations, the parity
// of the ends times, at each start, its sign and the signs stepping to it,
// times the route factors, is 2 ^ card(N) · β ^ card(H ∖ R): the factors
// expand into products of signs, and every such product but the empty one is
// odd under the toggle of one vertex.

package hedge_criterion

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_product"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/relations/graph/dag"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_algebra"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// routeParitySum — the sum over the sign configurations of the parity of the
// ends times the starts' Φ and the route factors is
// 2 ^ card(N) · β ^ card(H ∖ R). Write Φ(v) for the sign of v times the signs
// stepping to v. The parity of the ends is the product of Φ over H
// (StepSignTelescope, read with the ends T as its roots and no vertex left out;
// R here is the starts), so with the starts' Φ it is the product of Φ over
// H ∖ R, which the route factors 1 + β·Φ(v) take in as β + Φ(v); a vertex off H
// has factor 1. The product of the β + Φ(v) expands over the choices S ⊆ H ∖ R
// of the vertices that take Φ (real_product.ProductOfBinomials). For S nonempty
// some vertex of S steps to no vertex of S, the steps being acyclic
// (dag.DagSinkExists): its sign occurs once in the product of Φ over S, and
// toggling it negates that product (real_sum.SubsetsSumToggleOdd). The choice
// S = ∅ leaves β ^ card(H ∖ R) at each of the 2 ^ card(N) configurations.
var routeParitySum = routeParitySumThm{family.Add(registry.ProofEntry{
	Name: "routeParitySum",
	Key:  "prop_868f35a0c6656d9c",
	Reading: "z is the set of vertices whose sign is −1. H is the set of vertices on the " +
		"routes, T their ends and R their starts; τ is the next step, read only on H ∖ T. A " +
		"start may lie on another route and an end may be a start. Each hypothesis is " +
		"load-bearing. Acyclicity makes every route end. A vertex of H off R with no " +
		"predecessor has factor 1, and its sign, in its successor's factor or in the ends' " +
		"parity, is never cancelled. A step leaving H, or an end or a start outside H, " +
		"leaves a sign unpaired. The hypotheses give H an end and a start once it is nonempty.",
	Build: family.Sections(Statement{
		Binders: "∀N H R T:set(I). ∀τ:(I → I). ∀β:real.",
		Hypotheses: []string{
			"finite(N)",
			"H ⊆ N",
			"R ⊆ H",
			"T ⊆ H",
			"∀u:I. u ∈ H ∧ u ∉ T ⇒ τ(u) ∈ H",
			"∀u:I. ¬transitive_closure(λa:I. λb:I. a ∈ H ∧ a ∉ T ∧ b = τ(a), u, u)",
			"∀v:I. v ∈ H ∧ v ∉ R ⇒ (∃w:I. w ∈ H ∧ w ∉ T ∧ τ(w) = v)",
		},
		Conclusion: "Σ_{z∈{z:set(I) | z ⊆ N}} (Π_{y∈T} «sgn»(y ∈ z)) * " +
			"(Π_{r∈R} («sgn»(r ∈ z) * Π_{w∈«into»(r)} «sgn»(w ∈ z))) * " +
			"(Π_{v∈N ∖ R} (&1 + «sgn»(v ∈ z) * COND(«into»(v) = ∅, &0, β * Π_{w∈«into»(v)} «sgn»(w ∈ z)))) = " +
			"&(2 ^ card(N)) * β ^ card(H ∖ R)",
		Abbrev: Abbrev{
			{Name: "into", Text: "λv:I. {w:I | w ∈ H ∧ w ∉ T ∧ τ(w) = v}"},
			{Name: "Φ", Text: "λz:set(I). λv:I. «sgn»(v ∈ z) * Π_{w∈«into»(v)} «sgn»(w ∈ z)"},
			{Name: "factor", Text: "λz:set(I). λv:I. " +
				"    &1 + «sgn»(v ∈ z) * COND(«into»(v) = ∅, &0, β * Π_{w∈«into»(v)} «sgn»(w ∈ z))"},
			{Name: "summand", Text: "λz:set(I). " +
				"    (Π_{y∈T} «sgn»(y ∈ z)) * (Π_{r∈R} «Φ»(z, r)) * Π_{v∈N ∖ R} «factor»(z, v)"},
			{Name: "configs", Text: "{z:set(I) | z ⊆ N}"},
			{Name: "choices", Text: "{S:set(I) | S ⊆ H ∖ R}"},
			{Name: "choiceTerm", Text: "λz:set(I). λS:set(I). (Π_{v∈(H ∖ R) ∖ S} β) * Π_{v∈S} «Φ»(z, v)"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		// At one configuration the summand is a product of binomials over
		// the vertices of H off R. No acyclicity is read.
		summandOf := ctx.Lemma(Statement{
			Binders: "∀N H R T:set(I). ∀τ:(I → I). ∀β:real. ∀z:set(I).",
			Hypotheses: []string{
				"finite(N)",
				"H ⊆ N",
				"R ⊆ H",
				"T ⊆ H",
				"∀u:I. u ∈ H ∧ u ∉ T ⇒ τ(u) ∈ H",
				"∀v:I. v ∈ H ∧ v ∉ R ⇒ (∃w:I. w ∈ H ∧ w ∉ T ∧ τ(w) = v)",
			},
			Conclusion: "«summand»(z) = Π_{v∈H ∖ R} (β + «Φ»(z, v))",
		}, func(
			a *Argument,
			N, H, R, T *Expr[Set[I]],
			τ *Arrow[I, I],
			β *Expr[Real],
			z *Expr[Set[I]],
			finiteN, inside, startsIn, endsIn, stepsIn, fed Fact,
		) {
			rest := a.TermAs[Set[I]]("H ∖ R")
			phi := a.TermAs[Fun[I, Real]]("λv:I. «Φ»(z, v)")
			factorAt := a.TermAs[Fun[I, Real]]("λv:I. «factor»(z, v)")
			signSquare := a.Have(
				"a sign squares to one",
				"∀b:bool. «sgn»(b) * «sgn»(b) = &1",
				ByArith())
			unit := a.Have(
				"so does Φ at each vertex, a sign times a product of signs",
				"∀v:I. «Φ»(z, v) * «Φ»(z, v) = &1",
				Derive(func(b *Argument) {
					b.FixAs[I]("v")
					b.Show(
						"the sign of v and the product of the signs stepping to v each square to one",
						ByArith(
							signSquare.At(b.TermAs[Bool]("v ∈ z")),
							real_product.ProductSquareOne.At(
								b.TermAs[Set[I]]("«into»(v)"),
								b.TermAs[Fun[I, Real]]("λw:I. «sgn»(w ∈ z)"))))
				}))
			finiteH := a.Have(
				"the routes have finitely many vertices",
				"finite(H)",
				By(finiteN, inside, finite_set.FiniteSubset.At(H, N)))
			telescope := a.Have(
				"the product of Φ over H is the parity of the ends",
				"Π_{v∈H} «Φ»(z, v) = Π_{y∈T} «sgn»(y ∈ z)",
				Derive(func(b *Argument) {
					raw := b.Have(
						"the signs telescope along τ to the ends, no vertex left out",
						"Π_{v∈H} («sgn»(v ∈ z) * Π_{w∈{w:I | w ∈ H ∧ w ∉ T ∧ w ∉ ∅ ∧ τ(w) = v}} «sgn»(w ∈ z)) = "+
							"(Π_{y∈T} «sgn»(y ∈ z)) * Π_{u∈∅⟨A:I⟩} «sgn»(u ∈ z)",
						By(
							finiteH,
							stepsIn,
							signSquare,
							endsIn,
							set_order.EmptySubset,
							StepSignTelescope.At(
								H,
								T,
								b.TermAs[Set[I]]("∅"),
								τ,
								b.TermAs[Fun[I, Real]]("λu:I. «sgn»(u ∈ z)"))))
					b.Show(
						"nothing is in ∅, and the empty product is one",
						raw.Simp(Fwd(set_basic.NotInEmpty), Fwd(real_product.ProductClauses), Fwd(real_ring.MulRightId)),
						By(raw))
				}))
			halves := a.Have(
				"H is R with the rest of H",
				"(Π_{v∈H ∖ R} «Φ»(z, v)) * (Π_{r∈R} «Φ»(z, r)) = Π_{v∈H} «Φ»(z, v)",
				By(finiteH, startsIn, real_product.Diff.At(H, R, phi)))
			startsSquare := a.Have(
				"the product of Φ over the starts squares to one",
				"(Π_{r∈R} «Φ»(z, r)) * (Π_{r∈R} «Φ»(z, r)) = &1",
				By(unit, real_product.ProductSquareOne.At(R, phi)))
			ends := a.Have(
				"so the ends' parity times the starts' product is the product of Φ over the rest",
				"(Π_{y∈T} «sgn»(y ∈ z)) * (Π_{r∈R} «Φ»(z, r)) = Π_{v∈H ∖ R} «Φ»(z, v)",
				telescope.RwRev(),
				halves.RwRev(),
				ByArith(Scaled(a.TermAs[Real]("Π_{v∈H ∖ R} «Φ»(z, v)"), startsSquare)))
			offRoutes := a.Have(
				"a vertex off the routes has factor one",
				"∀v:I. v ∈ N ∖ R ∧ v ∉ H ∖ R ⇒ «factor»(z, v) = &1",
				Derive(func(b *Argument) {
					b.FixAs[I]("v")
					off := b.Assume()
					none := b.Have(
						"no step lands off the routes",
						"«into»(v) = ∅",
						BySets(stepsIn, off))
					b.Show(
						"with no predecessor the factor is one",
						ByArith(none))
				}))
			restricted := a.Have(
				"so the factors off the routes drop out of the product",
				"Π_{v∈N ∖ R} «factor»(z, v) = Π_{v∈H ∖ R} «factor»(z, v)",
				Derive(func(b *Argument) {
					within := b.Have(
						"the routes' vertices off R are vertices of N off R",
						"H ∖ R ⊆ N ∖ R",
						BySets(inside))
					b.Show(
						"a product is unchanged by factors equal to one",
						By(offRoutes, within, real_product.Superset.At(rest, b.TermAs[Set[I]]("N ∖ R"), factorAt)))
				}))
			absorb := a.Have(
				"on the routes off R a factor takes its Φ in as β + Φ",
				"∀v:I. v ∈ H ∖ R ⇒ «Φ»(z, v) * «factor»(z, v) = β + «Φ»(z, v)",
				Derive(func(b *Argument) {
					v := b.FixAs[I]("v")
					onRoute := b.Assume()
					some := b.Have(
						"a vertex of H off R has a predecessor",
						"«into»(v) ≠ ∅",
						BySets(fed, onRoute))
					b.Show(
						"Φ(v) squares to one, so Φ(v)·(1 + β·Φ(v)) is β + Φ(v)",
						ByArith(some, Scaled(β, unit.At(v))))
				}))
			finiteRest := a.Have(
				"finitely many vertices of H lie off R",
				"finite(H ∖ R)",
				By(finiteH, finite_set.FiniteDiff.At(H, R)))
			paired := a.Have(
				"the product of Φ and the product of the factors pair up vertex by vertex",
				"Π_{v∈H ∖ R} («Φ»(z, v) * «factor»(z, v)) = (Π_{v∈H ∖ R} «Φ»(z, v)) * Π_{v∈H ∖ R} «factor»(z, v)",
				By(finiteRest, real_product.Pointwise.At(rest, phi, factorAt)))
			binomials := a.Have(
				"and each pair is β + Φ",
				"Π_{v∈H ∖ R} («Φ»(z, v) * «factor»(z, v)) = Π_{v∈H ∖ R} (β + «Φ»(z, v))",
				By(
					absorb,
					real_product.Congruence.At(
						rest,
						a.TermAs[Fun[I, Real]]("λv:I. «Φ»(z, v) * «factor»(z, v)"),
						a.TermAs[Fun[I, Real]]("λv:I. β + «Φ»(z, v)"))))
			a.Show(
				"the ends' parity and the starts' Φ fold into the product over the rest, which the factors absorb",
				By(ends, restricted, paired, binomials))
		})

		// A nonempty set S of vertices of H: the product of Φ over S sums
		// to zero over the configurations. The starts R are not read.
		vanishing := ctx.Lemma(Statement{
			Binders: "∀N H T:set(I). ∀τ:(I → I). ∀S:set(I).",
			Hypotheses: []string{
				"finite(N)",
				"H ⊆ N",
				"∀u:I. u ∈ H ∧ u ∉ T ⇒ τ(u) ∈ H",
				"∀u:I. ¬transitive_closure(λa:I. λb:I. a ∈ H ∧ a ∉ T ∧ b = τ(a), u, u)",
				"S ⊆ H",
				"S ≠ ∅",
			},
			Conclusion: "Σ_{z∈«configs»} Π_{v∈S} «Φ»(z, v) = &0",
		}, func(
			a *Argument,
			N, H, T *Expr[Set[I]],
			τ *Arrow[I, I],
			S *Expr[Set[I]],
			finiteN, inside, stepsIn, acyclic, chosen, nonempty Fact,
		) {
			finiteH := a.Have(
				"the routes have finitely many vertices",
				"finite(H)",
				By(finiteN, inside, finite_set.FiniteSubset.At(H, N)))
			steps := a.Have(
				"the steps form a DAG on H: finitely many vertices, each step inside H, no cycle",
				"dag_on(H, λa:I. λb:I. a ∈ H ∧ a ∉ T ∧ b = τ(a))",
				Unfold(dag.DagOn),
				By(finiteH, acyclic, stepsIn))
			x, sink := a.ObtainAs[I](
				"some vertex of S steps to no vertex of S",
				"∃x:I. x ∈ S ∧ (∀t:I. t ∈ S ⇒ ¬(x ∈ H ∧ x ∉ T ∧ t = τ(x)))",
				By(
					nonempty,
					steps,
					dag.DagSinkExists.At(
						H,
						S,
						a.TermAs[Fun2[I, I, Bool]]("λa:I. λb:I. a ∈ H ∧ a ∉ T ∧ b = τ(a)"))))
			atSink := a.Conjuncts(
				sink,
				"x is a vertex of S",
				"x steps to no vertex of S")
			xIn, noStep := atSink[0], atSink[1]
			finiteS := a.Have(
				"S is finite",
				"finite(S)",
				By(finiteH, chosen, finite_set.FiniteSubset.At(S, H)))
			apart := a.Have(
				"so x steps into no vertex of S, itself included",
				"∀v:I. v ∈ S ⇒ x ∉ «into»(v)",
				BySets(noStep))
			unmoved := a.Have(
				"toggling x leaves a product of signs over a set without x as it was",
				"∀Y U:set(I). x ∉ U ⇒ Π_{w∈U} «sgn»(w ∈ set_toggle(x, Y)) = Π_{w∈U} «sgn»(w ∈ Y)",
				Derive(func(b *Argument) {
					b.FixAs[Set[I]]("Y")
					U := b.FixAs[Set[I]]("U")
					outside := b.Assume()
					signs := b.Have(
						"toggling x moves the sign of no other vertex",
						"∀w:I. w ∈ U ⇒ «sgn»(w ∈ set_toggle(x, Y)) = «sgn»(w ∈ Y)",
						By(outside, set_basic.InToggle))
					b.Show(
						"so the two products agree factor by factor",
						By(
							signs,
							real_product.Congruence.At(
								U,
								b.TermAs[Fun[I, Real]]("λw:I. «sgn»(w ∈ set_toggle(x, Y))"),
								b.TermAs[Fun[I, Real]]("λw:I. «sgn»(w ∈ Y)"))))
				}))
			peeled := a.Have(
				"at every configuration the product over S splits off the factor at x",
				"∀Y:set(I). Π_{v∈S} «Φ»(Y, v) = «Φ»(Y, x) * Π_{v∈delete(S, x)} «Φ»(Y, v)",
				Derive(func(b *Argument) {
					b.FixAs[Set[I]]("Y")
					b.Show(
						"x is a vertex of the finite set S",
						By(finiteS, xIn, real_product.Delete.At(S, b.TermAs[Fun[I, Real]]("«Φ»(Y)"), x)))
				}))
			odd := a.Have(
				"toggling x negates the product of Φ over S",
				"∀Y:set(I). Π_{v∈S} «Φ»(set_toggle(x, Y), v) = -(Π_{v∈S} «Φ»(Y, v))",
				Derive(func(b *Argument) {
					Y := b.FixAs[Set[I]]("Y")
					others := b.Have(
						"the factor at another vertex of S reads no sign at x",
						"∀v:I. v ∈ delete(S, x) ⇒ «Φ»(set_toggle(x, Y), v) = «Φ»(Y, v)",
						Derive(func(c *Argument) {
							v := c.FixAs[I]("v")
							other := c.Assume()
							c.Show(
								"v is not x, and x does not step to v",
								By(
									other,
									apart.At(v),
									unmoved.At(Y, c.TermAs[Set[I]]("«into»(v)")),
									set_basic.InToggle.At(x, Y, v),
									set_basic.InDelete.At(S, v, x)))
						}))
					flipped := b.Have(
						"the factor at x changes sign: its own sign flips and no sign stepping to it moves",
						"«Φ»(set_toggle(x, Y), x) = -«Φ»(Y, x)",
						ByArith(
							xIn,
							apart.At(x),
							unmoved.At(Y, b.TermAs[Set[I]]("«into»(x)")),
							set_basic.InToggle.At(x, Y, x)))
					restSame := b.Have(
						"so the product over the other vertices of S is unmoved",
						"Π_{v∈delete(S, x)} «Φ»(set_toggle(x, Y), v) = Π_{v∈delete(S, x)} «Φ»(Y, v)",
						By(
							others,
							real_product.Congruence.At(
								b.TermAs[Set[I]]("delete(S, x)"),
								b.TermAs[Fun[I, Real]]("λv:I. «Φ»(set_toggle(x, Y), v)"),
								b.TermAs[Fun[I, Real]]("λv:I. «Φ»(Y, v)"))))
					b.Show(
						"both products split at x, where exactly one factor changes sign",
						ByArith(peeled.At(b.TermAs[Set[I]]("set_toggle(x, Y)")), peeled.At(Y), flipped, restSame))
				}))
			xInN := a.Have(
				"x is a vertex of N",
				"x ∈ N",
				BySets(inside, chosen, xIn))
			a.Show(
				"a function of the configuration that is odd under the toggle of x sums to zero",
				By(
					odd,
					xInN,
					real_sum.SubsetsSumToggleOdd.At(
						N,
						x,
						a.TermAs[Fun[Set[I], Real]]("λz:set(I). Π_{v∈S} «Φ»(z, v)"))))
		})

		// One choice S of the vertices that take Φ, summed over the
		// configurations: the empty choice counts them, every other
		// vanishes.
		choiceSum := ctx.Lemma(Statement{
			Binders: "∀N H R T:set(I). ∀τ:(I → I). ∀β:real. ∀S:set(I).",
			Hypotheses: []string{
				"finite(N)",
				"H ⊆ N",
				"∀u:I. u ∈ H ∧ u ∉ T ⇒ τ(u) ∈ H",
				"∀u:I. ¬transitive_closure(λa:I. λb:I. a ∈ H ∧ a ∉ T ∧ b = τ(a), u, u)",
				"S ⊆ H ∖ R",
			},
			Conclusion: "Σ_{z∈«configs»} «choiceTerm»(z, S) = " +
				"COND(S = ∅, &(2 ^ card(N)) * β ^ card(H ∖ R), &0)",
		}, func(
			a *Argument,
			N, H, R, T *Expr[Set[I]],
			τ *Arrow[I, I],
			β *Expr[Real],
			S *Expr[Set[I]],
			finiteN, inside, stepsIn, acyclic, chosen Fact,
		) {
			configs := a.TermAs[Set[Set[I]]]("«configs»")
			a.Cases(a.TermAs[Bool]("S = ∅"))
			a.When(
				"the empty choice leaves β ^ card(H ∖ R) at each of the 2 ^ card(N) configurations",
				func(b *Argument, none Fact) {
					b.Do(none.Rw())
					b.Do(Simp(Fwd(real_product.ProductClauses), Fwd(set_algebra.DiffEmpty), Fwd(real_ring.MulRightId)))
					finiteRest := b.Have(
						"finitely many vertices of H lie off R",
						"finite(H ∖ R)",
						By(finiteN, inside, finite_set.FiniteSubset.At(H, N), finite_set.FiniteDiff.At(H, R)))
					power := b.Have(
						"a product of the one constant β is its power",
						"Π_{v∈H ∖ R} β = β ^ card(H ∖ R)",
						By(finiteRest, real_product.ProductConst.At(b.TermAs[Set[I]]("H ∖ R"), β)))
					finiteConfigs := b.Have(
						"N has finitely many subsets",
						"finite(«configs»)",
						By(finiteN, finite_set.FinitePowerset.At(N)))
					b.Show(
						"a constant summed over the 2 ^ card(N) subsets of N",
						ByArith(
							finiteN,
							finiteConfigs,
							power,
							real_sum.Const.At(configs, b.TermAs[Real]("Π_{v∈H ∖ R} β")),
							cardinality.CardPowerset.At(N)))
				})
			a.Otherwise(
				"a nonempty choice sums to zero",
				func(b *Argument, some Fact) {
					scalar := b.Have(
						"the power of β does not depend on the configuration",
						"Σ_{z∈«configs»} «choiceTerm»(z, S) = (Π_{v∈(H ∖ R) ∖ S} β) * Σ_{z∈«configs»} Π_{v∈S} «Φ»(z, v)",
						By(real_sum.ScalarLeft.At(
							b.TermAs[Real]("Π_{v∈(H ∖ R) ∖ S} β"),
							b.TermAs[Fun[Set[I], Real]]("λz:set(I). Π_{v∈S} «Φ»(z, v)"),
							configs)))
					onRoutes := b.Have(
						"a choice lies on the routes",
						"S ⊆ H",
						BySets(chosen))
					zero := b.Have(
						"the product of Φ over a nonempty set of vertices sums to zero",
						"Σ_{z∈«configs»} Π_{v∈S} «Φ»(z, v) = &0",
						By(finiteN, inside, stepsIn, acyclic, onRoutes, some, At(vanishing, N, H, T, τ, S)))
					whole := b.Have(
						"so does its multiple",
						"Σ_{z∈«configs»} «choiceTerm»(z, S) = &0",
						ByArith(scalar, zero))
					b.Show(
						"and S is not the empty choice",
						By(whole, some))
				})
		})

		return ctx.Theorem(headline, func(
			a *Argument,
			N, H, R, T *Expr[Set[I]],
			τ *Arrow[I, I],
			β *Expr[Real],
			finiteN, inside, startsIn, endsIn, stepsIn, acyclic, fed Fact,
		) {
			configs := a.TermAs[Set[Set[I]]]("«configs»")
			choices := a.TermAs[Set[Set[I]]]("«choices»")
			finiteRest := a.Have(
				"finitely many vertices of H lie off R",
				"finite(H ∖ R)",
				By(finiteN, inside, finite_set.FiniteSubset.At(H, N), finite_set.FiniteDiff.At(H, R)))
			expanded := a.Have(
				"each summand expands over the choices S of the vertices of H off R that take Φ",
				"∀z:set(I). «summand»(z) = Σ_{S∈«choices»} «choiceTerm»(z, S)",
				Derive(func(b *Argument) {
					z := b.FixAs[Set[I]]("z")
					binomial := b.Have(
						"a product of binomials β + Φ is the sum of its mixed products",
						"Π_{v∈H ∖ R} (β + «Φ»(z, v)) = Σ_{S∈«choices»} «choiceTerm»(z, S)",
						By(
							finiteRest,
							real_product.ProductOfBinomials.At(
								b.TermAs[Set[I]]("H ∖ R"),
								b.TermAs[Fun[I, Real]]("λv:I. β"),
								b.TermAs[Fun[I, Real]]("λv:I. «Φ»(z, v)"))))
					b.Show(
						"and the summand is that product",
						By(finiteN, inside, startsIn, endsIn, stepsIn, fed, binomial, At(summandOf, N, H, R, T, τ, β, z)))
				}))
			finiteIndex := a.Have(
				"there are finitely many configurations and finitely many choices",
				"finite(«configs») ∧ finite(«choices»)",
				By(
					finiteN,
					finiteRest,
					finite_set.FinitePowerset.At(N),
					finite_set.FinitePowerset.At(a.TermAs[Set[I]]("H ∖ R"))))
			perChoice := a.Have(
				"summed over the configurations, the empty choice counts them and every other vanishes",
				Statement{
					Binders:    "∀S:set(I).",
					Hypotheses: []string{"S ∈ «choices»"},
					Conclusion: "Σ_{z∈«configs»} «choiceTerm»(z, S) = " +
						"COND(S = ∅, &(2 ^ card(N)) * β ^ card(H ∖ R), &0)",
				},
				Derive(func(b *Argument) {
					S := b.FixAs[Set[I]]("S")
					choice := b.Assume()
					b.Show(
						"a choice is a set of vertices of H off R",
						By(finiteN, inside, stepsIn, acyclic, choice, At(choiceSum, N, H, R, T, τ, β, S)))
				}))
			emptyChoice := a.Have(
				"choosing no vertex is a choice",
				"∅ ∈ «choices»",
				BySets())
			a.Show(
				"expand the summands, exchange the two sums, and keep the empty choice",
				CalcEq(
					Leg(
						a.TermAs[Real]("Σ_{z∈«configs»} Σ_{S∈«choices»} «choiceTerm»(z, S)"),
						"expand each summand over the choices",
						By(
							expanded,
							real_sum.CongruenceEverywhere.At(
								configs,
								a.TermAs[Fun[Set[I], Real]]("λz:set(I). «summand»(z)"),
								a.TermAs[Fun[Set[I], Real]]("λz:set(I). Σ_{S∈«choices»} «choiceTerm»(z, S)")))),
					Leg(
						a.TermAs[Real]("Σ_{S∈«choices»} Σ_{z∈«configs»} «choiceTerm»(z, S)"),
						"exchange the two finite sums",
						By(
							finiteIndex,
							real_sum.Swap.At(
								configs,
								choices,
								a.TermAs[Fun2[Set[I], Set[I], Real]]("λz:set(I). λS:set(I). «choiceTerm»(z, S)")))),
					Leg(
						a.TermAs[Real]("Σ_{S∈«choices»} COND(S = ∅, &(2 ^ card(N)) * β ^ card(H ∖ R), &0)"),
						"sum each choice over the configurations",
						By(
							perChoice,
							real_sum.Congruence.At(
								choices,
								a.TermAs[Fun[Set[I], Real]]("λS:set(I). Σ_{z∈«configs»} «choiceTerm»(z, S)"),
								a.TermAs[Fun[Set[I], Real]](
									"λS:set(I). COND(S = ∅, &(2 ^ card(N)) * β ^ card(H ∖ R), &0)")))),
					FinalLeg(
						"only the empty choice is left",
						By(
							emptyChoice,
							real_sum.Delta.At(
								a.TermAs[Real]("&(2 ^ card(N)) * β ^ card(H ∖ R)"),
								choices,
								a.TermAs[Set[I]]("∅"))))))
		})
	}),
})}
