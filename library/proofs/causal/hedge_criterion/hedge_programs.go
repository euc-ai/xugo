// hedge_programs.go — the two sign programs of a hedge: the forest
// programs on the data a hedge gives, their class laws, and a product
// of signs being a sign.

package hedge_criterion

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_product"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/relations/closure"
	"github.com/euc-ai/xugo/library/proofs/relations/graph/dag"
	"github.com/euc-ai/xugo/library/proofs/relations/graph/latent_projection"
	"github.com/euc-ai/xugo/library/proofs/relations/graph/mixed_graph"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/registry"
)

// signProductUnit — a product of signs is 1 or −1, over any index set:
// the two values are closed under multiplication and hold 1, so the fold
// stays among them.
var signProductUnit = signProductUnitThm{family.Add(registry.ProofEntry{
	Name: "signProductUnit",
	Key:  "prop_85bcd2aa27092a24",
	Build: family.Theorem("∀S z:set(I). Π_{w∈S} «sgn»(w ∈ z) = &1 ∨ Π_{w∈S} «sgn»(w ∈ z) = -&1",
		func(a *Argument, S, z *Expr[Set[I]]) {
			closed := a.Have(
				"the values 1 and −1 are closed under multiplication",
				"∀x y:real. (x = &1 ∨ x = -&1) ∧ (y = &1 ∨ y = -&1) ⇒ x * y = &1 ∨ x * y = -&1",
				ByArith())
			signs := a.Have(
				"each sign is one of them",
				"∀w:I. «sgn»(w ∈ z) = &1 ∨ «sgn»(w ∈ z) = -&1",
				ByArith())
			a.Show(
				"so the fold at multiplication, which starts from 1, stays among them",
				Simp(Fwd(real_product.RealProductDef)),
				By(
					signs,
					closed,
					real_ring.NeutralMul,
					monoidal.Closed.Read(real_ring.MonoidalMul).At(
						a.TermAs[Set[Real]]("λx:real. x = &1 ∨ x = -&1"),
						S,
						a.TermAs[Fun[I, Real]]("λw:I. «sgn»(w ∈ z)"))))
		}),
})}

// HedgeSpinProgramsExist — a hedge of the latent projection carries two
// sign programs that agree on every observation and differ under do(X):
// the forest programs of F and of F′ on the data the hedge gives, their
// class laws in closed form, and the parity of the route ends, which the
// two laws with X held weigh differently.
var HedgeSpinProgramsExist = hedgeSpinProgramsExistThm{family.Add(registry.ProofEntry{
	Name: "HedgeSpinProgramsExist",
	Key:  "prop_b92df1db5d102821",
	Reading: "The two programs share their labels: a fair bit for each bidirected edge " +
		"inside F and each set of re-entry vertices. Their class laws agree with nothing held, " +
		"and with X held at a their marginals on Y differ at some class configuration. F ∩ X ≠ " +
		"∅ is what removes the first program's correlation when X is held; F′ ∩ X = ∅, with F′ " +
		"among the ancestors of Y off the edges into X, keeps the second's and keeps the " +
		"routes off X. The bound by 1/2 keeps every conditional probability in [1/4, 3/4], " +
		"which is what makes the realized models positive. The hedge is for X itself.",
	Build: family.Theorem(Statement{
		Binders: "∀V:set(I). ∀E:(I → I → bool). ∀O X Y F F':set(I).",
		Hypotheses: []string{
			"dag_on(V, E)",
			"O ⊆ V",
			"X ⊆ O",
			"Y ⊆ O",
			"mixed_graph_hedge(latent_proj_directed(E, O), latent_proj_bidirected(E, O), X, Y, F, F')",
		},
		Conclusion: "∃Λ:set(prod(prod(I, I), set(I))). " +
			"∃N:(prod(prod(I, I), set(I)) → set(I)). " +
			"∃g h:(I → set(I) → set(prod(prod(I, I), set(I))) → real). " +
			"    latent_sign_program(E, O, Λ, N, g) ∧ " +
			"    latent_sign_program(E, O, Λ, N, h) ∧ " +
			"    (∀v:I. ∀z:set(I). ∀σ:set(prod(prod(I, I), set(I))). " +
			"        v ∈ O ⇒ " +
			"        -(&1 / &2) ≤ g(v, z, σ) ∧ " +
			"        g(v, z, σ) ≤ &1 / &2 ∧ " +
			"        -(&1 / &2) ≤ h(v, z, σ) ∧ " +
			"        h(v, z, σ) ≤ &1 / &2) ∧ " +
			"    (∀z:set(I). latent_sign_law(O, Λ, g, ∅, z) = latent_sign_law(O, Λ, h, ∅, z)) ∧ " +
			"    (∃z:set(I). «marginal»(Λ, g, z) ≠ «marginal»(Λ, h, z))",
		Abbrev: Abbrev{
			{Name: "marginal", Text: "λΛ:set(prod(prod(I, I), set(I))). " +
				"λg:(I → set(I) → set(prod(prod(I, I), set(I))) → real). " +
				"λz:set(I). " +
				"    Σ_{y∈{y:set(I) | y ⊆ O ∧ y ∩ X = ∅ ∧ y ∩ Y = z ∩ Y}} latent_sign_law(O, Λ, g, X, y)"},
		},
	}, func(
		a *Argument,
		V *Expr[Set[I]],
		E *Arrow2[I, I, Bool],
		O, X, Y, F, FPrime *Expr[Set[I]],
		isDag, inV, xObserved, yObserved, hedge Fact,
	) {
		// The graph data of the hedge.
		data := a.Conjuncts(
			GroupPremises(
				isDag, inV, xObserved, yObserved, hedge, HedgeForestData.At(V, E, O, X, Y, F, FPrime)),
			"F lies among the observed nodes",
			"F′ lies inside F",
			"F′ is nonempty",
			"F meets X",
			"F′ misses X",
			"the bidirected edges inside F are finitely many",
			"and they connect F",
			"the bidirected edges inside F′ are finitely many",
			"and they connect F′",
			"a step inside F leaves each vertex off F′ along a directed edge",
			"routes lead from F′ towards Y off X")
		tau, steps := a.UnpackAs[Fun[I, I]](data[9], "τ")
		rho, H, routeData := a.Unpack2As[Fun[I, I], Set[I]](data[10], "ρ", "H")
		routes := a.Conjuncts(
			routeData,
			"the routes start on F′",
			"they stay among the observed nodes",
			"they miss X",
			"off Y a route steps inside H along a directed edge",
			"every route vertex off F′ is entered from one off Y")
		finiteO := a.Have(
			"the observed nodes are finitely many",
			"finite(O)",
			By(isDag, inV, dag.DagOn, finite_set.FiniteSubset))
		projected := a.Have(
			"the directed edges of the projection form a DAG on O",
			"dag_on(O, latent_proj_directed(E, O))",
			By(isDag, inV, latent_projection.LatentProjectionAdmg.At(V, E, O), mixed_graph.AdmgOn))
		acyclic := a.Have(
			"so no directed path of the projection returns to its start",
			"∀u:I. ¬transitive_closure(latent_proj_directed(E, O), u, u)",
			By(projected, dag.DagOn))

		// The route data: the ends T, the vertices stepping to v, their sign
		// product κ and the route term W.
		Ed, edDef := a.LetAs[Set[Prod[I, I]]](
			"Ed",
			"{e:prod(I, I) | fst(e) ∈ F ∧ snd(e) ∈ F ∧ latent_proj_bidirected(E, O, fst(e), snd(e))}")
		EdPrime, edPrimeDef := a.LetAs[Set[Prod[I, I]]](
			"Ed'",
			"{e:prod(I, I) | fst(e) ∈ F' ∧ snd(e) ∈ F' ∧ latent_proj_bidirected(E, O, fst(e), snd(e))}")
		T, tDef := a.LetAs[Set[I]]("T", "H ∩ Y")
		_, intoDef := a.LetAs[Fun[I, Set[I]]]("into", "λv:I. {w:I | w ∈ H ∧ w ∉ T ∧ ρ(w) = v}")
		kappa, kappaDef := a.LetAs[Fun2[I, Set[I], Real]](
			"κ", "λv:I. λz:set(I). Π_{w∈into(v)} «sgn»(w ∈ z)")
		W, wDef := a.LetAs[Fun2[I, Set[I], Real]](
			"W",
			"λv:I. λz:set(I). COND(into(v) = ∅, &0, &1 / &4 * κ(v, z))")
		stepsOffT := a.Have(
			"off its ends a route steps inside H along a directed edge of the projection",
			"∀w:I. w ∈ H ∧ w ∉ T ⇒ ρ(w) ∈ H ∧ latent_proj_directed(E, O, w, ρ(w))",
			BySets(routes[3], tDef))
		entered := a.Have(
			"every route vertex off F′ is entered from a route vertex off the ends",
			"∀v:I. v ∈ H ∧ v ∉ F' ⇒ (∃w:I. w ∈ H ∧ w ∉ T ∧ ρ(w) = v)",
			BySets(routes[4], tDef))
		intoIff := a.Have(
			"into(v) holds the route vertices off the ends that step to v",
			"∀v w:I. w ∈ into(v) ⇔ w ∈ H ∧ w ∉ T ∧ ρ(w) = v",
			BySets(intoDef))
		kappaAt := a.Have(
			"κ(v, z) is the product of the signs of the vertices stepping to v",
			"∀v:I. ∀z:set(I). κ(v, z) = Π_{w∈into(v)} «sgn»(w ∈ z)",
			By(Normalized, kappaDef))
		kappaUnit := a.Have(
			"so κ takes the values 1 and −1 only",
			"∀v:I. ∀z:set(I). κ(v, z) = &1 ∨ κ(v, z) = -&1",
			Derive(func(b *Argument) {
				v := b.FixAs[I]()
				z := b.FixAs[Set[I]]()
				b.Show(
					"a product of signs is 1 or −1",
					By(kappaAt.At(v, z), signProductUnit.At(b.TermAs[Set[I]]("into(v)"), z)))
			}))
		wAt := a.Have(
			"W(v, z) is a quarter of κ(v, z) where some vertex steps to v, and 0 elsewhere",
			"∀v:I. ∀z:set(I). W(v, z) = COND(into(v) = ∅, &0, &1 / &4 * κ(v, z))",
			By(wDef))
		wValues := a.Have(
			"so W takes the values 0, 1/4 and −1/4 only",
			"∀v:I. ∀z:set(I). W(v, z) = &0 ∨ W(v, z) = &1 / &4 ∨ W(v, z) = -(&1 / &4)",
			Derive(func(b *Argument) {
				v := b.FixAs[I]()
				z := b.FixAs[Set[I]]()
				b.Show(
					"by the two values of κ",
					ByArith(wAt.At(v, z), kappaUnit.At(v, z)))
			}))
		bounded := a.Have(
			"W is at most 1/4 in size and κ at most 1",
			"∀v:I. ∀z:set(I). v ∈ O ⇒ -(&1 / &4) ≤ W(v, z) ∧ W(v, z) ≤ &1 / &4 ∧ -&1 ≤ κ(v, z) ∧ κ(v, z) ≤ &1",
			Derive(func(b *Argument) {
				v := b.FixAs[I]()
				z := b.FixAs[Set[I]]()
				b.Show(
					"by their values",
					ByArith(kappaUnit.At(v, z), wValues.At(v, z)))
			}))
		local := a.Have(
			"W and κ read the class set only at the parents of v in the projection",
			Statement{
				Binders: "∀v:I. ∀z z':set(I).",
				Hypotheses: []string{
					"v ∈ O",
					"∀u:I. latent_proj_directed(E, O, u, v) ⇒ (u ∈ z ⇔ u ∈ z')",
				},
				Conclusion: "W(v, z) = W(v, z') ∧ κ(v, z) = κ(v, z')",
			},
			Derive(func(b *Argument) {
				v := b.FixAs[I]()
				z := b.FixAs[Set[I]]()
				zp := b.FixAs[Set[I]]()
				agreeOnParents := b.Conjuncts(
					b.Assume(),
					"v is observed",
					"the two class sets agree at the parents of v")
				sameSigns := b.Have(
					"a vertex stepping to v is a parent of v, so its two signs agree",
					"∀w:I. w ∈ into(v) ⇒ «sgn»(w ∈ z) = «sgn»(w ∈ z')",
					By(intoIff, stepsOffT, agreeOnParents[1]))
				sameProduct := b.Have(
					"so the two products of signs over into(v) agree",
					"Π_{w∈into(v)} «sgn»(w ∈ z) = Π_{w∈into(v)} «sgn»(w ∈ z')",
					By(
						sameSigns,
						real_product.Congruence.At(
							b.TermAs[Set[I]]("into(v)"),
							b.TermAs[Fun[I, Real]]("λw:I. «sgn»(w ∈ z)"),
							b.TermAs[Fun[I, Real]]("λw:I. «sgn»(w ∈ z')"))))
				b.Show(
					"and W and κ are functions of that product",
					By(sameProduct, kappaAt.At(v, z), kappaAt.At(v, zp), wAt.At(v, z), wAt.At(v, zp)))
			}))
		dyadic := a.Have(
			"W and κ are dyadic at every exponent m ≥ 2",
			Statement{
				Binders: "∀m:num.",
				Hypotheses: []string{
					"2 ≤ m",
				},
				Conclusion: "∀v:I. ∀z:set(I). " +
					"    (∃n:num. W(v, z) = &n / &(2 ^ m) ∨ W(v, z) = -(&n / &(2 ^ m))) ∧ " +
					"    (∃n:num. κ(v, z) = &n / &(2 ^ m) ∨ κ(v, z) = -(&n / &(2 ^ m)))",
			},
			Derive(func(b *Argument) {
				b.FixAs[Nat]()
				atLeastTwo := b.Assume()
				shifted := b.Have(
					"m is two more than m − 2",
					"m - 2 + 2 = m",
					ByArith(atLeastTwo))
				splitPower := b.Have(
					"so 2^m is 2^(m − 2) times 2²",
					"2 ^ m = 2 ^ (m - 2) * 2 ^ 2",
					By(shifted, nat_arith.PowAdd.At(b.TermAs[Nat]("2"), b.TermAs[Nat]("m - 2"), b.TermAs[Nat]("2"))))
				fourfold := b.Have(
					"as a real, 2^m is four times 2^(m − 2)",
					"&(2 ^ m) = &4 * &(2 ^ (m - 2))",
					ByArith(splitPower))
				positive := b.Have(
					"a power of 2 is positive",
					"0 < 2 ^ (m - 2)",
					ByArith())
				atLeastOne := b.Have(
					"so 2^(m − 2) is at least 1 as a real",
					"&1 ≤ &(2 ^ (m - 2))",
					ByArith(positive))
				one := b.Have(
					"1 is 2^m over 2^m",
					"∃n:num. &1 = &n / &(2 ^ m)",
					Derive(func(c *Argument) {
						c.Take(c.TermAs[Nat]("2 ^ m"))
						c.Do(fourfold.Rw())
						c.Show(
							"the quotient of a positive real by itself",
							ByArith(atLeastOne))
					}))
				quarter := b.Have(
					"1/4 is 2^(m − 2) over 2^m",
					"∃n:num. &1 / &4 = &n / &(2 ^ m)",
					Derive(func(c *Argument) {
						c.Take(c.TermAs[Nat]("2 ^ (m - 2)"))
						c.Do(fourfold.Rw())
						c.Show(
							"cancel the positive factor 2^(m − 2)",
							ByArith(atLeastOne))
					}))
				zero := b.Have(
					"0 is 0 over 2^m",
					"&0 = &0 / &(2 ^ m)",
					ByArith())
				v := b.FixAs[I]()
				z := b.FixAs[Set[I]]()
				b.Show(
					"and W and κ take the values 0, ±1/4 and ±1",
					By(one, quarter, zero, kappaUnit.At(v, z), wValues.At(v, z)))
			}))

		// The forests' data: the re-entry vertices U, the coefficient a and
		// the labels Λ.
		U, uDef := a.LetAs[Set[I]]("U", "{u:I | u ∈ F ∧ u ∉ F' ∧ into(u) ≠ ∅}")
		coef, coefDef := a.LetAs[Real]("a", "&1 / &(2 ^ (card(U) + 2))")
		Lam, lamDef := a.LetAs[Set[Prod[Prod[I, I], Set[I]]]]("Λ", "set_cross(Ed, {A:set(I) | A ⊆ U})")
		uOffRoots := a.Have(
			"U lies in F off F′",
			"U ⊆ F ∖ F'",
			BySets(uDef))
		uObserved := a.Have(
			"so U lies among the observed nodes",
			"U ⊆ O",
			BySets(uOffRoots, data[0]))
		finiteU := a.Have(
			"and U is finite",
			"finite(U)",
			By(finiteO, uObserved, finite_set.FiniteSubset.At(U, O)))
		wOffU := a.Have(
			"W vanishes on F ∖ F′ off U, no vertex stepping there",
			"∀v:I. ∀z:set(I). v ∈ F ∧ v ∉ F' ∧ v ∉ U ⇒ W(v, z) = &0",
			BySets(uDef, wAt))
		twoMore := a.Have(
			"2^(card(U) + 2) is four times 2^card(U), which is positive",
			"2 ^ (card(U) + 2) = 2 ^ card(U) * 4 ∧ 0 < 2 ^ card(U)",
			ByArith(nat_arith.PowAdd.At(a.TermAs[Nat]("2"), a.TermAs[Nat]("card(U)"), a.TermAs[Nat]("2"))))
		twoMoreReal := a.Have(
			"the same as reals",
			"&(2 ^ (card(U) + 2)) = &4 * &(2 ^ card(U))",
			ByArith(twoMore))
		trackCount := a.Have(
			"2^card(U) is at least 1 as a real",
			"&1 ≤ &(2 ^ card(U))",
			ByArith(twoMore))
		coefSplit := a.Have(
			"a is one over four times 2^card(U)",
			"a = &1 / (&4 * &(2 ^ card(U)))",
			By(coefDef, twoMoreReal))
		coefQuarter := a.Have(
			"a is positive, and a · 2^card(U) is 1/4",
			"&0 < a ∧ a * &(2 ^ card(U)) = &1 / &4",
			ByArith(coefSplit, trackCount))
		coefSmall := a.Have(
			"so a is at most 1/4",
			"a ≤ &1 / &4",
			ByArith(coefQuarter, trackCount))
		finiteF := a.Have(
			"F is finite",
			"finite(F)",
			By(finiteO, data[0], finite_set.FiniteSubset.At(F, O)))
		finiteRoots := a.Have(
			"F′ is finite",
			"finite(F')",
			By(finiteF, data[1], finite_set.FiniteSubset.At(FPrime, F)))
		nonemptyF := a.Have(
			"F is nonempty, as F′ is",
			"F ≠ ∅",
			BySets(data[2], data[1]))
		sizes := a.Have(
			"F′ and F have a vertex each",
			"1 ≤ card(F') ∧ 1 ≤ card(F)",
			ByArith(
				finiteF,
				finiteRoots,
				nonemptyF,
				data[2],
				cardinality.CardEqZero.At(F),
				cardinality.CardEqZero.At(FPrime)))
		powersSmall := a.Have(
			"so the two coefficients are at most a",
			"a ^ card(F') ≤ a ∧ a ^ card(F) ≤ a",
			ByArith(
				coefQuarter,
				coefSmall,
				sizes,
				real_pow.PowMonoExpBelowOne.At(coef, a.TermAs[Nat]("1"), a.TermAs[Nat]("card(F')")),
				real_pow.PowMonoExpBelowOne.At(coef, a.TermAs[Nat]("1"), a.TermAs[Nat]("card(F)")),
				real_pow.PowOne.At(coef)))
		dyadicG := a.Have(
			"the coefficient of the first program is a power of 1/2",
			"a ^ card(F') = &1 / &(2 ^ ((card(U) + 2) * card(F')))",
			By(
				coefDef,
				real_pow.DivPow.At(
					a.TermAs[Real]("&1"), a.TermAs[Real]("&(2 ^ (card(U) + 2))"), a.TermAs[Nat]("card(F')")),
				real_pow.OnePow.At(a.TermAs[Nat]("card(F')")),
				real_pow.OfNumPow.At(a.TermAs[Nat]("2 ^ (card(U) + 2)"), a.TermAs[Nat]("card(F')")),
				nat_arith.PowPow.At(a.TermAs[Nat]("2"), a.TermAs[Nat]("card(U) + 2"), a.TermAs[Nat]("card(F')"))))
		dyadicH := a.Have(
			"and so is that of the second",
			"a ^ card(F) = &1 / &(2 ^ ((card(U) + 2) * card(F)))",
			By(
				coefDef,
				real_pow.DivPow.At(
					a.TermAs[Real]("&1"), a.TermAs[Real]("&(2 ^ (card(U) + 2))"), a.TermAs[Nat]("card(F)")),
				real_pow.OnePow.At(a.TermAs[Nat]("card(F)")),
				real_pow.OfNumPow.At(a.TermAs[Nat]("2 ^ (card(U) + 2)"), a.TermAs[Nat]("card(F)")),
				nat_arith.PowPow.At(a.TermAs[Nat]("2"), a.TermAs[Nat]("card(U) + 2"), a.TermAs[Nat]("card(F)"))))
		numeratorG := a.Have(
			"with numerator 1",
			"∃n:num. a ^ card(F') = &n / &(2 ^ ((card(U) + 2) * card(F')))",
			Derive(func(b *Argument) {
				b.Take(b.TermAs[Nat]("1"))
				b.Show(
					"the power of 1/2 above",
					By(dyadicG))
			}))
		numeratorH := a.Have(
			"and numerator 1 again",
			"∃n:num. a ^ card(F) = &n / &(2 ^ ((card(U) + 2) * card(F)))",
			Derive(func(b *Argument) {
				b.Take(b.TermAs[Nat]("1"))
				b.Show(
					"the power of 1/2 above",
					By(dyadicH))
			}))
		weightG := a.Have(
			"the first coefficient times the number of tracks is at most 1/4",
			"a ^ card(F') * &(2 ^ card(U)) ≤ &1 / &4",
			ByArith(powersSmall, coefQuarter, trackCount))
		weightH := a.Have(
			"and the second, which has one track, is at most 1/4",
			"a ^ card(F) * &(2 ^ card(∅⟨A:I⟩)) ≤ &1 / &4",
			ByArith(powersSmall, coefSmall, cardinality.CardClauses))
		exponents := a.Have(
			"both exponents are at least 2",
			"2 ≤ (card(U) + 2) * card(F') ∧ 2 ≤ (card(U) + 2) * card(F)",
			ByArith(sizes))
		products := a.Have(
			"the two products of coefficients are one power of a",
			"Π_{v∈F} a ^ card(F') = a ^ (card(F) * card(F')) ∧ Π_{v∈F'} a ^ card(F) = a ^ (card(F) * card(F'))",
			By(
				Normalized,
				finiteF,
				finiteRoots,
				real_product.ProductConst.At(F, a.TermAs[Real]("a ^ card(F')")),
				real_product.ProductConst.At(FPrime, a.TermAs[Real]("a ^ card(F)")),
				real_pow.PowPow.At(coef, a.TermAs[Nat]("card(F')"), a.TermAs[Nat]("card(F)")),
				real_pow.PowPow.At(coef, a.TermAs[Nat]("card(F)"), a.TermAs[Nat]("card(F')")),
				nat_arith.MulSym.At(a.TermAs[Nat]("card(F')"), a.TermAs[Nat]("card(F)"))))
		finiteLabels := a.Have(
			"the labels are finitely many",
			"finite(Λ)",
			By(
				lamDef,
				data[5],
				finiteU,
				finite_set.FinitePowerset.At(U),
				finite_set.FiniteProduct.At(Ed, a.TermAs[Set[Set[I]]]("{A:set(I) | A ⊆ U}"))))
		fewerEdges := a.Have(
			"the edges inside F′ are edges inside F",
			"Ed' ⊆ Ed",
			BySets(edDef, edPrimeDef, data[1]))
		fewerTracks := a.Have(
			"the one track of the second program is a track of the first",
			"{A:set(I) | A ⊆ ∅} ⊆ {A:set(I) | A ⊆ U}",
			BySets())
		labelsH := a.Have(
			"so the labels of the second program are among Λ",
			"set_cross(Ed', {A:set(I) | A ⊆ ∅}) ⊆ Λ",
			By(
				lamDef,
				fewerEdges,
				fewerTracks,
				set_product.CrossSubsetIff.At(
					EdPrime,
					Ed,
					a.TermAs[Set[Set[I]]]("{A:set(I) | A ⊆ ∅}"),
					a.TermAs[Set[Set[I]]]("{A:set(I) | A ⊆ U}"))))
		labelsG := a.Have(
			"and those of the first are Λ itself",
			"set_cross(Ed, {A:set(I) | A ⊆ U}) ⊆ Λ",
			BySets(lamDef))
		onEdges := a.Have(
			"every label lies on a bidirected edge of the projection",
			"∀p:prod(prod(I, I), set(I)). p ∈ Λ ⇒ latent_proj_bidirected(E, O, fst(fst(p)), snd(fst(p)))",
			Derive(func(b *Argument) {
				p := b.FixAs[Prod[Prod[I, I], Set[I]]]()
				isLabel := b.Assume()
				edge := b.Have(
					"the first component of a label is an edge inside F",
					"fst(p) ∈ Ed",
					By(
						isLabel,
						lamDef,
						set_product.InCrossProjections.At(Ed, b.TermAs[Set[Set[I]]]("{A:set(I) | A ⊆ U}"), p)))
				b.Show(
					"and those edges are bidirected",
					BySets(edge, edDef))
			}))
		edgesF := a.Have(
			"an edge of Ed joins two distinct vertices of F",
			"∀e:prod(I, I). e ∈ Ed ⇒ fst(e) ∈ F ∧ snd(e) ∈ F ∧ fst(e) ≠ snd(e)",
			BySets(edDef, latent_projection.LatentBidirectedDef))
		edgesRoots := a.Have(
			"and an edge of Ed' two distinct vertices of F′",
			"∀e:prod(I, I). e ∈ Ed' ⇒ fst(e) ∈ F' ∧ snd(e) ∈ F' ∧ fst(e) ≠ snd(e)",
			BySets(edPrimeDef, latent_projection.LatentBidirectedDef))
		inclusions := a.Have(
			"the inclusions the two forests ask for",
			"U ⊆ F ∧ F' ⊆ O ∧ F' ⊆ F' ∧ ∅ ⊆ F' ∧ ∅ ⊆ F' ∖ F'",
			BySets(uOffRoots, data[1], data[0]))
		stepsF := a.Have(
			"the step of the first forest follows a directed edge and stays in F",
			"(∀w:I. w ∈ F ∧ w ∉ F' ⇒ latent_proj_directed(E, O, w, τ(w))) ∧ (∀w:I. w ∈ F ∧ w ∉ F' ⇒ τ(w) ∈ F)",
			By(steps))
		stepsRoots := a.Have(
			"the second forest is all roots, and no vertex of it steps",
			"(∀w:I. w ∈ F' ∧ w ∉ F' ⇒ latent_proj_directed(E, O, w, τ(w))) ∧ "+
				"(∀w:I. w ∈ F' ∧ w ∉ F' ⇒ τ(w) ∈ F')",
			BySets())

		// The two programs: the forest means of F and of F′.
		N, nDef := a.LetAs[Fun[Prod[Prod[I, I], Set[I]], Set[I]]](
			"N",
			"λp:prod(prod(I, I), set(I)). {fst(fst(p)), snd(fst(p))}")
		g, gDef := a.LetAs[Fun3[I, Set[I], Set[Prod[Prod[I, I], Set[I]]], Real]](
			"g",
			"c_forest_sign_mean(W, κ, λv:I. a ^ card(F'), F, F', U, Ed, τ)")
		h, hDef := a.LetAs[Fun3[I, Set[I], Set[Prod[Prod[I, I], Set[I]]], Real]](
			"h",
			"c_forest_sign_mean(W, κ, λv:I. a ^ card(F), F', F', ∅, Ed', τ)")
		alphaG := a.TermAs[Fun[I, Real]]("λv:I. a ^ card(F')")
		alphaH := a.TermAs[Fun[I, Real]]("λv:I. a ^ card(F)")
		empty := a.TermAs[Set[I]]("∅")
		programG := a.Have(
			"the forest mean of F is a sign program bounded by 1/2",
			"latent_sign_program(E, O, Λ, N, g) ∧ "+
				"(∀v:I. ∀z:set(I). ∀σ:set(prod(prod(I, I), set(I))). "+
				"    v ∈ O ⇒ -(&1 / &2) ≤ g(v, z, σ) ∧ g(v, z, σ) ≤ &1 / &2)",
			By(
				gDef,
				nDef,
				finiteO,
				data[0],
				data[1],
				inclusions,
				finiteLabels,
				labelsG,
				onEdges,
				stepsF,
				local,
				dyadic.At(a.TermAs[Nat]("(card(U) + 2) * card(F')")),
				exponents,
				numeratorG,
				weightG,
				bounded,
				ForestSignProgram.At(
					E,
					O,
					F,
					FPrime,
					U,
					Ed,
					Lam,
					tau,
					W,
					kappa,
					alphaG,
					a.TermAs[Nat]("(card(U) + 2) * card(F')"))))
		programH := a.Have(
			"and so is the forest mean of F′",
			"latent_sign_program(E, O, Λ, N, h) ∧ "+
				"(∀v:I. ∀z:set(I). ∀σ:set(prod(prod(I, I), set(I))). "+
				"    v ∈ O ⇒ -(&1 / &2) ≤ h(v, z, σ) ∧ h(v, z, σ) ≤ &1 / &2)",
			By(
				hDef,
				nDef,
				finiteO,
				inclusions,
				finiteLabels,
				labelsH,
				onEdges,
				stepsRoots,
				local,
				dyadic.At(a.TermAs[Nat]("(card(U) + 2) * card(F)")),
				exponents,
				numeratorH,
				weightH,
				bounded,
				ForestSignProgram.At(
					E,
					O,
					FPrime,
					FPrime,
					empty,
					EdPrime,
					Lam,
					tau,
					W,
					kappa,
					alphaH,
					a.TermAs[Nat]("(card(U) + 2) * card(F)"))))

		// Their class laws in closed form, at any held set.
		lawG := a.Have(
			"the class law of the first program, with any set held",
			"∀X':set(I). ∀z:set(I). "+
				"    latent_sign_law(O, Λ, g, X', z) = "+
				"    (Π_{v∈O ∖ X'} (&1 + «sgn»(v ∈ z) * W(v, z)) + "+
				"        COND(F ∩ X' = ∅, "+
				"            (Π_{v∈F} a ^ card(F')) * "+
				"            (Π_{r∈F'} «sgn»(r ∈ z) * κ(r, z)) * "+
				"            (Π_{u∈U} (&1 + «sgn»(u ∈ z) * W(u, z))) * "+
				"            Π_{v∈(O ∖ X') ∖ F} (&1 + «sgn»(v ∈ z) * W(v, z)), "+
				"            &0)) / "+
				"    &(2 ^ card(O ∖ X'))",
			Derive(func(b *Argument) {
				held := b.FixAs[Set[I]]()
				z := b.FixAs[Set[I]]()
				b.Show(
					"the closed form of a forest law",
					By(
						gDef,
						finiteO,
						data[0],
						nonemptyF,
						data[5],
						edgesF,
						data[6],
						data[1],
						uOffRoots,
						stepsF,
						finiteLabels,
						labelsG,
						forestSignLaw.At(O, held, F, FPrime, U, Ed, Lam, tau, W, kappa, alphaG, z)))
			}))
		lawH := a.Have(
			"and that of the second",
			"∀X':set(I). ∀z:set(I). "+
				"    latent_sign_law(O, Λ, h, X', z) = "+
				"    (Π_{v∈O ∖ X'} (&1 + «sgn»(v ∈ z) * W(v, z)) + "+
				"        COND(F' ∩ X' = ∅, "+
				"            (Π_{v∈F'} a ^ card(F)) * "+
				"            (Π_{r∈F'} «sgn»(r ∈ z) * κ(r, z)) * "+
				"            (Π_{u∈∅⟨A:I⟩} (&1 + «sgn»(u ∈ z) * W(u, z))) * "+
				"            Π_{v∈(O ∖ X') ∖ F'} (&1 + «sgn»(v ∈ z) * W(v, z)), "+
				"            &0)) / "+
				"    &(2 ^ card(O ∖ X'))",
			Derive(func(b *Argument) {
				held := b.FixAs[Set[I]]()
				z := b.FixAs[Set[I]]()
				b.Show(
					"the closed form of a forest law",
					By(
						hDef,
						finiteO,
						inclusions,
						data[2],
						data[7],
						edgesRoots,
						data[8],
						stepsRoots,
						finiteLabels,
						labelsH,
						forestSignLaw.At(O, held, FPrime, FPrime, empty, EdPrime, Lam, tau, W, kappa, alphaH, z)))
			}))

		// Nothing held: the two laws are one closed form.
		pieces := a.Have(
			"O ∖ F′ is O ∖ F with F ∖ F′, the two apart",
			"O ∖ F' = (O ∖ F) ∪ (F ∖ F') ∧ disjoint(O ∖ F, F ∖ F')",
			BySets(data[1], data[0]))
		finitePieces := a.Have(
			"and both pieces are finite",
			"finite(O ∖ F) ∧ finite(F ∖ F')",
			By(finiteO, finiteF, finite_set.FiniteDiff.At(O, F), finite_set.FiniteDiff.At(F, FPrime)))
		split := a.Have(
			"off F′ the route factors are those of U times those off F",
			"∀z:set(I). "+
				"    Π_{v∈O ∖ F'} (&1 + «sgn»(v ∈ z) * W(v, z)) = "+
				"    (Π_{u∈U} (&1 + «sgn»(u ∈ z) * W(u, z))) * Π_{v∈O ∖ F} (&1 + «sgn»(v ∈ z) * W(v, z))",
			Derive(func(b *Argument) {
				b.FixAs[Set[I]]()
				factor := b.TermAs[Fun[I, Real]]("λx:I. &1 + «sgn»(x ∈ z) * W(x, z)")
				trivial := b.Have(
					"on F ∖ F′ off U the route factor is 1",
					"∀x:I. x ∈ F ∖ F' ∧ x ∉ U ⇒ &1 + «sgn»(x ∈ z) * W(x, z) = &1",
					Derive(func(c *Argument) {
						c.FixAs[I]()
						offU := c.Assume()
						silent := c.Have(
							"W vanishes there",
							"W(x, z) = &0",
							BySets(offU, wOffU))
						c.Show(
							"so the factor is 1",
							ByArith(silent))
					}))
				onU := b.Have(
					"so the product over U is that over F ∖ F′",
					"Π_{u∈U} (&1 + «sgn»(u ∈ z) * W(u, z)) = Π_{v∈F ∖ F'} (&1 + «sgn»(v ∈ z) * W(v, z))",
					By(uOffRoots, trivial, real_product.Superset.At(U, b.TermAs[Set[I]]("F ∖ F'"), factor)))
				parts := b.Have(
					"the product over the two pieces is the product of their products",
					"Π_{v∈(O ∖ F) ∪ (F ∖ F')} (&1 + «sgn»(v ∈ z) * W(v, z)) = "+
						"(Π_{v∈O ∖ F} (&1 + «sgn»(v ∈ z) * W(v, z))) * Π_{v∈F ∖ F'} (&1 + «sgn»(v ∈ z) * W(v, z))",
					By(
						finitePieces,
						pieces,
						real_product.Union.At(b.TermAs[Set[I]]("O ∖ F"), b.TermAs[Set[I]]("F ∖ F'"), factor)))
				whole := b.Have(
					"and O ∖ F′ is the two pieces",
					"Π_{v∈O ∖ F'} (&1 + «sgn»(v ∈ z) * W(v, z)) = "+
						"Π_{v∈(O ∖ F) ∪ (F ∖ F')} (&1 + «sgn»(v ∈ z) * W(v, z))",
					By(pieces))
				b.Show(
					"multiply the three equations out",
					ByArith(onU, parts, whole))
			}))
		atNothing := a.Have(
			"holding nothing removes nothing",
			"O ∖ ∅⟨A:I⟩ = O ∧ F ∩ ∅⟨A:I⟩ = ∅⟨A:I⟩ ∧ F' ∩ ∅⟨A:I⟩ = ∅⟨A:I⟩",
			BySets())
		powers := a.Conjuncts(
			products,
			"the product of the first program's coefficients is a power of a",
			"and that of the second is the same power")
		agree := a.Have(
			"with nothing held the two class laws agree",
			"∀z:set(I). latent_sign_law(O, Λ, g, ∅, z) = latent_sign_law(O, Λ, h, ∅, z)",
			Derive(func(b *Argument) {
				z := b.FixAs[Set[I]]()
				observedG := b.Have(
					"the first law with nothing held",
					"latent_sign_law(O, Λ, g, ∅, z) = "+
						"(Π_{v∈O} (&1 + «sgn»(v ∈ z) * W(v, z)) + "+
						"    (Π_{v∈F} a ^ card(F')) * "+
						"    (Π_{r∈F'} «sgn»(r ∈ z) * κ(r, z)) * "+
						"    (Π_{u∈U} (&1 + «sgn»(u ∈ z) * W(u, z))) * "+
						"    Π_{v∈O ∖ F} (&1 + «sgn»(v ∈ z) * W(v, z))) / "+
						"&(2 ^ card(O))",
					By(lawG.At(empty, z), atNothing))
				observedH := b.Have(
					"the second law with nothing held",
					"latent_sign_law(O, Λ, h, ∅, z) = "+
						"(Π_{v∈O} (&1 + «sgn»(v ∈ z) * W(v, z)) + "+
						"    (Π_{v∈F'} a ^ card(F)) * "+
						"    (Π_{r∈F'} «sgn»(r ∈ z) * κ(r, z)) * "+
						"    (Π_{u∈∅⟨A:I⟩} (&1 + «sgn»(u ∈ z) * W(u, z))) * "+
						"    Π_{v∈O ∖ F'} (&1 + «sgn»(v ∈ z) * W(v, z))) / "+
						"&(2 ^ card(O))",
					By(lawH.At(empty, z), atNothing))
				noTrack := b.Have(
					"the second program has no re-entry vertex",
					"Π_{u∈∅⟨A:I⟩} (&1 + «sgn»(u ∈ z) * W(u, z)) = &1",
					By(real_product.ProductClauses))
				b.Do(
					observedG.Rw(),
					observedH.Rw(),
					noTrack.Rw(),
					split.At(z).Rw(),
					powers[0].Rw(),
					powers[1].Rw())
				b.Show(
					"both sides are now one expression",
					ByArith())
			}))

		// X held: the first law loses its forest term, the second keeps it.
		heldG := a.Have(
			"with X held the first law is the route product alone, F meeting X",
			"∀y:set(I). "+
				"    latent_sign_law(O, Λ, g, X, y) = "+
				"    (Π_{v∈O ∖ X} (&1 + «sgn»(v ∈ y) * W(v, y))) / &(2 ^ card(O ∖ X))",
			Derive(func(b *Argument) {
				y := b.FixAs[Set[I]]()
				b.Show(
					"the forest term is switched off",
					ByArith(lawG.At(X, y), data[3]))
			}))
		heldH := a.Have(
			"and the second keeps its forest term, F′ missing X",
			"∀y:set(I). "+
				"    latent_sign_law(O, Λ, h, X, y) = "+
				"    (Π_{v∈O ∖ X} (&1 + «sgn»(v ∈ y) * W(v, y)) + "+
				"        (Π_{v∈F'} a ^ card(F)) * "+
				"        (Π_{r∈F'} «sgn»(r ∈ y) * κ(r, y)) * "+
				"        Π_{v∈(O ∖ X) ∖ F'} (&1 + «sgn»(v ∈ y) * W(v, y))) / "+
				"    &(2 ^ card(O ∖ X))",
			Derive(func(b *Argument) {
				y := b.FixAs[Set[I]]()
				noTrack := b.Have(
					"the second program has no re-entry vertex",
					"Π_{u∈∅⟨A:I⟩} (&1 + «sgn»(u ∈ y) * W(u, y)) = &1",
					By(real_product.ProductClauses))
				b.Show(
					"the forest term stays",
					ByArith(lawH.At(X, y), data[4], noTrack))
			}))
		finiteFree := a.Have(
			"the nodes off X are finitely many",
			"finite(O ∖ X)",
			By(finiteO, finite_set.FiniteDiff.At(O, X)))
		ends := a.Have(
			"the routes lie off X, and their ends are route vertices in Y",
			"H ⊆ O ∖ X ∧ T ⊆ H ∧ T ⊆ Y",
			BySets(routes[1], routes[2], tDef))
		stepEdges := a.Have(
			"a route step is a directed edge of the projection",
			"∀x y:I. x ∈ H ∧ x ∉ T ∧ y = ρ(x) ⇒ latent_proj_directed(E, O, x, y)",
			By(Normalized, stepsOffT))
		noLoop := a.Have(
			"so the route steps have no cycle, the projection having none",
			"∀u:I. ¬transitive_closure(λa:I. λb:I. a ∈ H ∧ a ∉ T ∧ b = ρ(a), u, u)",
			Derive(func(b *Argument) {
				u := b.FixAs[I]()
				b.Show(
					"a transitive closure is monotone in its relation",
					By(
						stepEdges,
						acyclic.At(u),
						closure.Monotone.At(
							b.TermAs[Fun2[I, I, Bool]]("λa:I. λb:I. a ∈ H ∧ a ∉ T ∧ b = ρ(a)"),
							b.TermAs[Fun2[I, I, Bool]]("latent_proj_directed(E, O)"),
							u,
							u)))
			}))
		routeSum := a.Have(
			"the parity of the ends against the route factors sums to a power of 1/4",
			"Σ_{z∈{z:set(I) | z ⊆ O ∖ X}} (Π_{t∈T} «sgn»(t ∈ z)) * "+
				"(Π_{r∈F'} «sgn»(r ∈ z) * κ(r, z)) * "+
				"Π_{v∈(O ∖ X) ∖ F'} (&1 + «sgn»(v ∈ z) * W(v, z)) = "+
				"&(2 ^ card(O ∖ X)) * (&1 / &4) ^ card(H ∖ F')",
			wDef.Rw(),
			kappaDef.Rw(),
			intoDef.Rw(),
			By(
				finiteFree,
				ends,
				routes[0],
				stepsOffT,
				noLoop,
				entered,
				routeParitySum.At(a.TermAs[Set[I]]("O ∖ X"), H, FPrime, T, rho, a.TermAs[Real]("&1 / &4"))))
		differ := a.Have(
			"so the marginals on Y of the two laws differ at some class set",
			"∃z:set(I). «marginal»(Λ, g, z) ≠ «marginal»(Λ, h, z)",
			Derive(func(b *Argument) {
				same := b.SupposeNot()
				parity := b.Have(
					"equal marginals give equal sums against the parity of the ends",
					"Σ_{y∈{y:set(I) | y ⊆ O ∧ y ∩ X = ∅}} (Π_{t∈T} «sgn»(t ∈ y)) * latent_sign_law(O, Λ, g, X, y) = "+
						"Σ_{y∈{y:set(I) | y ⊆ O ∧ y ∩ X = ∅}} (Π_{t∈T} «sgn»(t ∈ y)) * latent_sign_law(O, Λ, h, X, y)",
					By(
						finiteO,
						ends,
						same,
						ClassMarginalsParity.At(
							O,
							X,
							Y,
							T,
							b.TermAs[Fun[Set[I], Real]]("λy:set(I). latent_sign_law(O, Λ, g, X, y)"),
							b.TermAs[Fun[Set[I], Real]]("λy:set(I). latent_sign_law(O, Λ, h, X, y)"))))
				classSets := b.Have(
					"the class sets off X are the subsets of O ∖ X",
					"{y:set(I) | y ⊆ O ∧ y ∩ X = ∅} = {y:set(I) | y ⊆ O ∖ X}",
					BySets())
				parityFree := b.Have(
					"the same equation over the subsets of O ∖ X",
					"Σ_{y∈{y:set(I) | y ⊆ O ∖ X}} (Π_{t∈T} «sgn»(t ∈ y)) * latent_sign_law(O, Λ, g, X, y) = "+
						"Σ_{y∈{y:set(I) | y ⊆ O ∖ X}} (Π_{t∈T} «sgn»(t ∈ y)) * latent_sign_law(O, Λ, h, X, y)",
					By(parity, classSets))
				finiteSets := b.Have(
					"which are finitely many",
					"finite({y:set(I) | y ⊆ O ∖ X})",
					By(finiteFree, finite_set.FinitePowerset.At(b.TermAs[Set[I]]("O ∖ X"))))
				gap := b.Have(
					"at each class set the two weighted laws differ by the forest term of the second",
					"∀y:set(I). "+
						"    (Π_{t∈T} «sgn»(t ∈ y)) * latent_sign_law(O, Λ, h, X, y) - "+
						"    (Π_{t∈T} «sgn»(t ∈ y)) * latent_sign_law(O, Λ, g, X, y) = "+
						"    (Π_{v∈F'} a ^ card(F)) / "+
						"    &(2 ^ card(O ∖ X)) * "+
						"    ((Π_{t∈T} «sgn»(t ∈ y)) * "+
						"        (Π_{r∈F'} «sgn»(r ∈ y) * κ(r, y)) * "+
						"        Π_{v∈(O ∖ X) ∖ F'} (&1 + «sgn»(v ∈ y) * W(v, y)))",
					Derive(func(c *Argument) {
						y := c.FixAs[Set[I]]()
						c.Do(heldH.At(y).Rw(), heldG.At(y).Rw())
						c.Show(
							"the route products cancel",
							ByArith())
					}))
				difference := b.Have(
					"the sum of the differences is the difference of the sums",
					"Σ_{y∈{y:set(I) | y ⊆ O ∖ X}} ((Π_{t∈T} «sgn»(t ∈ y)) * latent_sign_law(O, Λ, h, X, y) - (Π_{t∈T} «sgn»(t ∈ y)) * latent_sign_law(O, Λ, g, X, y)) = "+
						"(Σ_{y∈{y:set(I) | y ⊆ O ∖ X}} (Π_{t∈T} «sgn»(t ∈ y)) * latent_sign_law(O, Λ, h, X, y)) - "+
						"Σ_{y∈{y:set(I) | y ⊆ O ∖ X}} (Π_{t∈T} «sgn»(t ∈ y)) * latent_sign_law(O, Λ, g, X, y)",
					By(finiteSets, real_sum.Sub))
				termwise := b.Have(
					"and, term by term, the sum of the scaled forest terms",
					"Σ_{y∈{y:set(I) | y ⊆ O ∖ X}} ((Π_{t∈T} «sgn»(t ∈ y)) * latent_sign_law(O, Λ, h, X, y) - (Π_{t∈T} «sgn»(t ∈ y)) * latent_sign_law(O, Λ, g, X, y)) = "+
						"Σ_{y∈{y:set(I) | y ⊆ O ∖ X}} (Π_{v∈F'} a ^ card(F)) / "+
						"&(2 ^ card(O ∖ X)) * "+
						"((Π_{t∈T} «sgn»(t ∈ y)) * "+
						"    (Π_{r∈F'} «sgn»(r ∈ y) * κ(r, y)) * "+
						"    Π_{v∈(O ∖ X) ∖ F'} (&1 + «sgn»(v ∈ y) * W(v, y)))",
					By(gap, real_sum.Congruence))
				scaled := b.Have(
					"the constant factor leaves the sum",
					"(Π_{v∈F'} a ^ card(F)) / "+
						"&(2 ^ card(O ∖ X)) * "+
						"(Σ_{y∈{y:set(I) | y ⊆ O ∖ X}} (Π_{t∈T} «sgn»(t ∈ y)) * "+
						"    (Π_{r∈F'} «sgn»(r ∈ y) * κ(r, y)) * "+
						"    Π_{v∈(O ∖ X) ∖ F'} (&1 + «sgn»(v ∈ y) * W(v, y))) = "+
						"Σ_{y∈{y:set(I) | y ⊆ O ∖ X}} (Π_{v∈F'} a ^ card(F)) / "+
						"&(2 ^ card(O ∖ X)) * "+
						"((Π_{t∈T} «sgn»(t ∈ y)) * "+
						"    (Π_{r∈F'} «sgn»(r ∈ y) * κ(r, y)) * "+
						"    Π_{v∈(O ∖ X) ∖ F'} (&1 + «sgn»(v ∈ y) * W(v, y)))",
					By(real_sum.ScalarLeft))
				weight := b.Have(
					"the product of the second program's coefficients is positive",
					"&0 < Π_{v∈F'} a ^ card(F)",
					ByArith(products, coefQuarter, real_pow.PowPos.At(coef, b.TermAs[Nat]("card(F) * card(F')"))))
				quarterPower := b.Have(
					"so is the power of 1/4",
					"&0 < (&1 / &4) ^ card(H ∖ F')",
					ByArith(real_pow.PowPos.At(b.TermAs[Real]("&1 / &4"), b.TermAs[Nat]("card(H ∖ F')"))))
				count := b.Have(
					"a power of 2 is positive",
					"0 < 2 ^ card(O ∖ X)",
					ByArith())
				countReal := b.Have(
					"as a real too",
					"&0 < &(2 ^ card(O ∖ X))",
					ByArith(count))
				value := b.Have(
					"by the route sum the scaled sum is the weight times a power of 1/4",
					"(Π_{v∈F'} a ^ card(F)) / "+
						"&(2 ^ card(O ∖ X)) * "+
						"(Σ_{y∈{y:set(I) | y ⊆ O ∖ X}} (Π_{t∈T} «sgn»(t ∈ y)) * "+
						"    (Π_{r∈F'} «sgn»(r ∈ y) * κ(r, y)) * "+
						"    Π_{v∈(O ∖ X) ∖ F'} (&1 + «sgn»(v ∈ y) * W(v, y))) = "+
						"(Π_{v∈F'} a ^ card(F)) * (&1 / &4) ^ card(H ∖ F')",
					routeSum.Rw(),
					ByArith(countReal))
				b.Show(
					"which is positive, while equal marginals make it zero",
					ByArith(parityFree, difference, termwise, scaled, value, quarterPower, weight))
			}))

		// The witnesses.
		a.Take(Lam)
		a.Take(N)
		a.Take(g)
		a.Take(h)
		a.Show(
			"the two forest programs, their agreement with nothing held and their difference with X held",
			By(programG, programH, agree, differ))
	}),
})}
