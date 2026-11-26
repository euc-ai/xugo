// exchange.go — the exchange argument, which runs over a field.
//
// A member of a family may be exchanged for a combination of the family
// in which its coefficient is nonzero without changing what the family
// spans, because the member is won back from the combination and the
// members that stay: it is the combination, less the other summands,
// scaled by the inverse of its coefficient. Winning it back divides,
// and over a ring that is not a field the inverse need not exist —
// which is why this part of the chapter states its laws under the field
// and not under the ring.
//
// One step of the replacement argument follows: an exchange followed by
// a re-indexing puts the next member of an independent family into a
// family whose span holds it, just past the members the two already
// share. Taken once for each member of the independent family, the step
// is the replacement theorem, which closes the file.

package basis

import (
	"github.com/euc-ai/xugo/ext"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// SolveForMember — a subspace holding a combination and every member
// but the j-th, whose coefficient is nonzero, holds the j-th member too:
// the relation can be solved for it.
//
// Split the j-th summand off the combination: what is left, r, is a sum
// of multiples of members the subspace holds, so the subspace holds r,
// and with it the combination less r — which is the j-th summand. That
// summand is the j-th member scaled by a nonzero coefficient, and in a
// field scaling by the coefficient's inverse undoes it, so the j-th
// member is a multiple of a vector the subspace holds.
var SolveForMember = solveForMemberThm{family.Add(registry.ProofEntry{
	Name: "SolveForMember",
	Key:  "prop_2fece092915ddc1",
	Build: field.Field.Law(
		Statement{
			Binders: "∀s:set(num → A). ∀k j:num. ∀e:(num → num → A). ∀c:(num → A).",
			Hypotheses: []string{
				"vec_subspace(s)",
				"j < k",
				"Σ_{i<k} c(i) • e(i) ∈ s",
				"∀i:num. i < k ∧ i ≠ j ⇒ e(i) ∈ s",
				"c(j) ≠ F.zero",
			},
			Conclusion: "e(j) ∈ s",
		},
		func(
			a *Argument,
			fld Fact,
			s *Expr[Set[Fun[Nat, A]]],
			k, j *Expr[Nat],
			e *Arrow2[Nat, Nat, A],
			c *Arrow[Nat, A],
			subspace, below, combinationIn, othersIn, invertible Fact,
		) {
			// The vector laws hold over any commutative ring, and a field
			// is one.
			ring := field.Ring.Read(fld)

			// Split the j-th summand off the combination: the fold takes
			// each index of its range once, and j is one of them.
			rDef := a.Let("r", a.Term("Σ_{i∈delete({i:num | i < k}, j)} c(i) • e(i)"))
			finite := a.Have(
				"the index range is finite",
				"finite({i:num | i < k})",
				By(num_segment.FiniteBelowStrict))
			inRange := a.Have(
				"and holds j",
				"j ∈ {i:num | i < k}",
				BySets(below))
			split := a.Have(
				"so the combination is its j-th summand plus the rest r",
				"Σ_{i<k} c(i) • e(i) = c(j) • e(j) + r",
				// The law's left side applies the fold's operation and its
				// summand, and the goal spells only what they produce — a
				// sum, and the family's term read at j — so both are pinned
				// by name.
				rDef.Rw(),
				Symm(),
				By(
					vec_space.MonoidalVecAdd.Read(ring),
					finite,
					inRange,
					Where(monoidal.Delete, "op", a.Term("vec_add")).Where("f", a.Term("λi:num. c(i) • e(i)"))))

			// Being a subspace is three conditions, and the scalar
			// action's is spent twice: on the summands of r, and at the
			// close.
			conditions := a.Unfolded(subspace, vec_space.VecSubspaceDef)
			summands := a.Have(
				"each summand of r is a multiple of a member s holds, so it lies in s",
				"∀i:num. i ∈ delete({i:num | i < k}, j) ⇒ c(i) • e(i) ∈ s",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					inRest := b.Assume()
					member := b.Have(
						"its index lies below k and is not j, so s holds the member there",
						"e(i) ∈ s",
						BySets(inRest, othersIn.At(i)))
					b.Show(
						"and a subspace is closed under the scalar action",
						By(member, conditions))
				}))
			rest := a.TermAs[Set[Nat]]("delete({i:num | i < k}, j)")
			summand := a.TermAs[Fun2[Nat, Nat, A]]("λi:num. c(i) • e(i)")
			restIn := a.Have(
				"so r lies in s, a subspace holding every sum of its own vectors",
				"r ∈ s",
				rDef.Rw(),
				By(subspace, summands, vec_space.SubspaceIterate.Read(ring).At(s, rest, summand)))
			difference := a.Have(
				"and so does the combination less r",
				"Σ_{i<k} c(i) • e(i) - r ∈ s",
				By(ring, subspace, combinationIn, restIn, vec_space.SubspaceSub))

			isolate := a.Have(
				"which is the j-th summand, r added and subtracted again",
				"Σ_{i<k} c(i) • e(i) - r = c(j) • e(j)",
				split.Rw(),
				By(vec_space.AddSubCancelRight, ring))

			solved := a.Have(
				"solving for e(j): the inverse of its coefficient undoes the scaling",
				"e(j) = F.inv(c(j)) • (Σ_{i<k} c(i) • e(i) - r)",
				CalcEq(
					Leg(
						a.Term("F.one • e(j)"),
						"one acts as the identity",
						Symm(),
						By(vec_space.SmulOne, ring)),
					Leg(
						a.Term("(F.inv(c(j)) * c(j)) • e(j)"),
						"and one is the coefficient's inverse times the coefficient, which is nonzero",
						Congr(),
						Symm(),
						By(invertible, fld, field.MulLeftInverse)),
					Leg(
						a.Term("F.inv(c(j)) • (c(j) • e(j))"),
						"scaling by a product is scaling by each factor in turn",
						By(vec_space.SmulMul, ring)),
					FinalLeg(
						"and the j-th summand is the combination less r",
						Congr(),
						Symm(),
						By(isolate)),
				))

			a.Show(
				"so e(j) is a multiple of a vector s holds, and a subspace is closed under the scalar action",
				solved.Rw(),
				By(difference, conditions))
		}),
})}

// Exchange — a vector whose expansion in a family has a nonzero
// coefficient at j may replace the j-th member without changing the
// span.
//
// Write g for the exchanged family: y at j, the family's own member
// everywhere else. Each inclusion is SpanSubset. Every member of g lies
// in the family's span: y is the combination with coefficients c, and
// the others are members of the family. Every member of the family lies
// in g's span: away from j it is g's own member there, and at j it is
// won back by SolveForMember — the combination is y, which g holds at j,
// every other member of the family is one g's span holds, and the
// coefficient at j is nonzero.
var Exchange = exchangeThm{family.Add(registry.ProofEntry{
	Name: "Exchange",
	Key:  "prop_7aaf1edadb59281d",
	Build: field.Field.Law(
		Statement{
			Binders: "∀k j:num. ∀e:(num → num → A). ∀c y:(num → A).",
			Hypotheses: []string{
				"j < k",
				"y = Σ_{i<k} c(i) • e(i)",
				"c(j) ≠ F.zero",
			},
			Conclusion: "vec_span(k, λi:num. COND(i = j, y, e(i))) = vec_span(k, e)",
		},
		func(a *Argument, fld Fact, k, j *Expr[Nat], e *Arrow2[Nat, Nat, A], c, y *Arrow[Nat, A],
			below, expansion, invertible Fact) {
			ring := field.Ring.Read(fld)

			// The exchanged family g, as a term: the goal spells it only
			// inside a span, and SpanMember is read at it.
			g := a.TermAs[Fun2[Nat, Nat, A]]("λl:num. COND(l = j, y, e(l))")

			gSpanIsSubspace := a.Have(
				"g's span is a subspace",
				"vec_subspace(vec_span(k, λl:num. COND(l = j, y, e(l))))",
				By(vec_space.SpanSubspace.Read(ring)))

			others := a.Have(
				"every member of the family below k other than the j-th lies in g's span",
				"∀i:num. i < k ∧ i ≠ j ⇒ e(i) ∈ vec_span(k, λl:num. COND(l = j, y, e(l)))",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					elsewhere := b.Assume()
					b.Show(
						"g's member at i lies in g's span, and away from j that member is e(i)",
						By(elsewhere, vec_space.SpanMember.Read(ring).At(k, i, g)))
				}))

			forward := a.Have(
				"g's span lies in the family's: every member of g is in the family's span",
				"vec_span(k, λl:num. COND(l = j, y, e(l))) ⊆ vec_span(k, e)",
				Derive(func(b *Argument) {
					yIn := b.Have(
						"y lies in the family's span, being its combination with coefficients c",
						"y ∈ vec_span(k, e)",
						expansion.Rw(),
						By(vec_space.CombinationInSpan.Read(ring).At(k, e, c)))
					members := b.Have(
						"each member of g below k lies in the family's span",
						"∀i:num. i < k ⇒ COND(i = j, y, e(i)) ∈ vec_span(k, e)",
						Derive(func(d *Argument) {
							d.Fix("i")
							iBelow := d.Assume()
							d.Cases(d.Term("i = j"))
							d.When(
								"at j the member is y",
								func(d *Argument, atJ Fact) {
									d.Show(
										"which lies in the family's span",
										By(atJ, yIn))
								})
							d.Otherwise(
								"elsewhere it is the family's own member",
								func(d *Argument, away Fact) {
									d.Show(
										"which lies in the family's span",
										By(away, iBelow, ring, vec_space.SpanMember))
								})
						}))
					b.Show(
						"so the whole of g's span lies inside",
						By(vec_space.SpanSubset.Read(ring).At(k, k, g, e), members))
				}))

			backward := a.Have(
				"the family's span lies in g's: every member of the family is in g's span",
				"vec_span(k, e) ⊆ vec_span(k, λl:num. COND(l = j, y, e(l)))",
				Derive(func(b *Argument) {
					combination := b.Have(
						"the combination is y, g's member at j, so g's span holds it",
						"Σ_{i<k} c(i) • e(i) ∈ vec_span(k, λl:num. COND(l = j, y, e(l)))",
						expansion.RwRev(),
						By(below, vec_space.SpanMember.Read(ring).At(k, j, g)))
					wonBack := b.Have(
						"so the j-th member is won back from the combination and the members g keeps",
						"e(j) ∈ vec_span(k, λl:num. COND(l = j, y, e(l)))",
						By(fld, gSpanIsSubspace, below, combination, others, invertible, SolveForMember))
					members := b.Have(
						"each member of the family below k lies in g's span",
						"∀i:num. i < k ⇒ e(i) ∈ vec_span(k, λl:num. COND(l = j, y, e(l)))",
						Derive(func(d *Argument) {
							d.Fix("i")
							iBelow := d.Assume()
							d.Cases(d.Term("i = j"))
							d.When(
								"at j it is the member just won back",
								func(d *Argument, atJ Fact) {
									d.Show(
										"which lies in g's span",
										atJ.Rw(),
										By(wonBack))
								})
							d.Otherwise(
								"elsewhere it is g's own member",
								func(d *Argument, away Fact) {
									d.Show(
										"which lies in g's span",
										By(away, iBelow, others))
								})
						}))
					b.Show(
						"so the whole of the family's span lies inside",
						By(vec_space.SpanSubset.Read(ring).At(k, k, e, g), members))
				}))

			a.Show(
				"so the two spans are equal",
				By(forward, backward, set_order.SubsetAntisym))
		}),
})}

// ReplacementStep — one step of replacement: from a family g whose first
// t members are e's and whose span holds e(t), a family with the same
// span is made whose first suc(t) members are e's — and there is room
// for them, suc(t) ≤ m. It is stated in the replacement theorem's own
// terms, so that each step of that induction is this lemma read at the
// family built so far, followed by one rewrite of that family's span to
// the original one.
//
// Expand e(t) in g. Since g agrees with the independent e below t,
// ReplacementPivot finds a nonzero coefficient at an index j with
// t ≤ j < m — so t < m. Exchange puts e(t) in at j, which gives f,
// without changing the span, and SpanSwap moves it on to t, re-indexing
// f along the transposition of t and j, again without changing the
// span. The re-indexed family holds e(t) at t; below t the
// transposition moves nothing, since j lies at or past t, so there it
// holds g's members, which are e's.
var ReplacementStep = replacementStepThm{family.Add(registry.ProofEntry{
	Name: "ReplacementStep",
	Key:  "prop_f87dee79cfc8dd22",
	Build: field.Field.Law(
		Statement{
			Binders: "∀k m t:num. ∀e g:(num → num → A).",
			Hypotheses: []string{
				"vec_independent(k, e)",
				"t < k",
				"t ≤ m",
				"∀i:num. i < t ⇒ g(i) = e(i)",
				"e(t) ∈ vec_span(m, g)",
			},
			Conclusion: "suc(t) ≤ m ∧ " +
				"(∃h:(num → num → A). vec_span(m, h) = vec_span(m, g) ∧ (∀i:num. i < suc(t) ⇒ h(i) = e(i)))",
		},
		func(a *Argument, fld Fact, k, m, t *Expr[Nat], e, g *Arrow2[Nat, Nat, A],
			independent, below, within, agree, inSpan Fact) {
			ring := field.Ring.Read(fld)

			// Membership in a span is the span's defining condition read
			// at the vector: e(t) is a combination of g's first m members.
			c, realizes := a.UnpackAs[Fun[Nat, A]](
				a.Unfolded(a.Unfolded(inSpan, set_basic.SetMemberDef), vec_space.VecSpanDef))

			pivot := a.Have(
				"g agrees with the independent e below t, so some coefficient at or past t is nonzero",
				"∃j:num. t ≤ j ∧ j < m ∧ c(j) ≠ F.zero",
				By(
					field.OneNotZero.Read(fld),
					independent,
					below,
					within,
					agree,
					realizes,
					ReplacementPivot.Read(ring).At(k, m, t, e, g, c)))
			j, pivotAt := a.UnpackAs[Nat](pivot)
			room := a.Have(
				"so there is room for e(t) at t: t ≤ j < m",
				"t < m",
				ByArith(pivotAt))

			// The exchanged family f: e(t) at j, g's own member everywhere
			// else.
			f, fDef := a.LetAs[Fun2[Nat, Nat, A]]("f", "λl:num. COND(l = j, e(t), g(l))")

			exchange := a.Have(
				"e(t) may replace g's member at j, its coefficient there being nonzero",
				"vec_span(m, f) = vec_span(m, g)",
				fDef.Rw(),
				By(Exchange.Read(fld).At(m, j, g, c, a.TermAs[Fun[Nat, A]]("e(t)")), pivotAt, realizes))
			swapped := a.Have(
				"and moved from j to t by re-indexing f along the transposition of t and j",
				"vec_span(m, λi:num. f(COND(i = t, j, COND(i = j, t, i)))) = vec_span(m, f)",
				By(vec_space.SpanSwap.Read(ring).At(m, t, j, f), room, pivotAt))

			agrees := a.Have(
				"the re-indexed family agrees with e up to t",
				"∀i:num. i < suc(t) ⇒ f(COND(i = t, j, COND(i = j, t, i))) = e(i)",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					upToT := b.Assume()
					notT := b.Unless(
						b.Term("i = t"),
						"at t the transposition reads j, where f holds e(t)",
						Given(func(d *Argument, atT Fact) {
							d.Show(
								"which is e(i), i being t",
								fDef.Rw(),
								By(atT))
						}))
					beforeT := b.Have(
						"so i lies below t",
						"i < t",
						ByArith(notT, upToT))
					notJ := b.Have(
						"and so it is not j, which lies at or past t",
						"i ≠ j",
						ByArith(beforeT, pivotAt))
					b.Show(
						"the transposition fixes i, where f is g, which agrees with e below t",
						fDef.Rw(),
						By(Normalized, notT, notJ, agree.At(i), beforeT))
				}))

			a.Do(SplitConj(
				Case(
					"there is room for e's first suc(t) members",
					ByArith(room)),
				Case(
					"and f re-indexed is the replaced family",
					Derive(func(b *Argument) {
						b.Take(b.Term("λi:num. f(COND(i = t, j, COND(i = j, t, i)))"))
						b.Show(
							"it spans what f does, which spans what g does, and it agrees with e up to t",
							By(Normalized, swapped, exchange, agrees))
					})),
			))
		}),
})}

// Steinitz — the replacement theorem: k independent vectors in the span
// of m vectors number at most m, and some m vectors with that same span
// have them as their first k.
//
// By induction, one member at a time. Before anything is replaced f
// itself will do. Once some family with f's span has e's first t members
// as its own first t, e(t) lies in f's span, which is the replacing
// family's, so ReplacementStep puts it in at t, keeping the span and
// finding room for it below m. After k steps that is the theorem.
var Steinitz = steinitzThm{family.Add(registry.ProofEntry{
	Name: "Steinitz",
	Key:  "prop_cc84619bd1911897",
	Build: field.Field.Law(
		Statement{
			Binders: "∀k m:num. ∀e f:(num → num → A).",
			Hypotheses: []string{
				"vec_independent(k, e)",
				"∀i:num. i < k ⇒ e(i) ∈ vec_span(m, f)",
			},
			Conclusion: "k ≤ m ∧ " +
				"(∃g:(num → num → A). vec_span(m, g) = vec_span(m, f) ∧ (∀i:num. i < k ⇒ g(i) = e(i)))",
		},
		func(a *Argument, fld Fact, k, m *Expr[Nat], e, f *Arrow2[Nat, Nat, A], independent, within Fact) {
			replaced := a.Have(
				"for each t up to k, t ≤ m, and some family with "+
					"f's span has e's first t members as its own first t",
				Statement{
					Binders: "∀t:num.",
					Hypotheses: []string{
						"t ≤ k",
					},
					Conclusion: "t ≤ m ∧ " +
						"(∃g:(num → num → A). vec_span(m, g) = vec_span(m, f) ∧ (∀i:num. i < t ⇒ g(i) = e(i)))",
				},
				Derive(func(b *Argument) {
					t := ext.As[Nat](b.Binder("t"))
					b.Induct(t)
					b.Base(
						"at 0 f itself will do",
						func(c *Argument) {
							c.Assume()
							c.Do(SplitConj(
								Case(
									"there is room for no members",
									By(nat_order.ZeroLessEq)),
								Case(
									"and f spans its own span and agrees with e below 0, where there is nothing",
									Derive(func(d *Argument) {
										d.Take(f)
										d.Show(
											"no index lies below 0",
											By(nat_order.LessThanZeroClause))
									})),
							))
						})
					b.Step(
						"past t, e(t) replaces one more of f's members",
						func(c *Argument, ih Fact) {
							bound := c.Assume()
							below := c.Have(
								"t lies below k",
								"t < k",
								ByArith(bound))
							upToK := c.Have(
								"so t is at most k, where the hypothesis applies",
								"t ≤ k",
								ByArith(below))
							room := c.Have(
								"there is room for t members",
								"t ≤ m",
								By(ih, upToK))
							g, replacing := c.ObtainAs[Fun2[Nat, Nat, A]](
								"and a family g spans f's span and holds e's first t members",
								"∃g:(num → num → A). vec_span(m, g) = vec_span(m, f) ∧ (∀i:num. i < t ⇒ g(i) = e(i))",
								By(ih, upToK))
							sameSpan := c.Have(
								"g spans what f spans",
								"vec_span(m, g) = vec_span(m, f)",
								By(replacing))
							inSpan := c.Have(
								"e(t) lies in f's span, which is g's",
								"e(t) ∈ vec_span(m, g)",
								sameSpan.Rw(),
								By(within.At(t), below))
							next := c.Have(
								"so ReplacementStep puts e(t) into g at t without changing g's span, and finds room for it",
								"suc(t) ≤ m ∧ "+
									"∃h:(num → num → A). vec_span(m, h) = vec_span(m, g) ∧ (∀i:num. i < suc(t) ⇒ h(i) = e(i))",
								By(ReplacementStep.Read(fld).At(k, m, t, e, g), independent, below, room, replacing, inSpan))
							c.Show(
								"and g's span is f's",
								sameSpan.RwRev(),
								By(next))
						})
				}))
			a.Show(
				"the invariant at k is the theorem",
				By(replaced.At(k), nat_order.LessEqRefl))
		}),
})}
