// subspace.go — what it is to be a subspace of the sequences, and the
// span of a family of them.
//
// `vec_span(k, e)` is the set of linear combinations of the first k
// members of a family: the values `Σ_{i<k} c(i) • e(i)` takes as the
// coefficient sequence c ranges over everything. Nothing is asked of
// the family — no dimension, no independence — so a span is available
// wherever a family is, and a dimension enters only where a member of
// the span is asked to have one. Membership in a span is the span's
// defining condition read at the vector (the definition is stated
// pointwise): opening it hands over a coefficient sequence, and proving
// it is naming one.
//
// A vector is put into a span one way, as a combination of the family
// (CombinationInSpan), and taken out one way, the definition read at the
// vector handing over its coefficients.
//
// The file runs from what a span holds to what it is. A span holds its
// family, grows with the bound, and is a subspace; the vectors of a
// dimension are a subspace too. Being a subspace is three conditions —
// the zero vector, the sum, the scalar action — and two more closures
// are read off them: under differences, and under sums of any length.
// The scalar action and the sums of any length make the span the least
// subspace holding its family. At the vectors of a dimension, the sums
// of any length keep a fold of n-vectors in dimension n, and leastness
// keeps a span of n-vectors there; at another span, leastness compares
// two spans by their families, and from that the span does not depend on
// the order of the family: a permutation of the range, a swap of two
// members in particular, keeps it. No proof here inducts on the bound.

package vec_space

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// CombinationInSpan — a combination of the family's first k members
// lies in their span: membership in a span is being such a combination,
// and the coefficients are the witness.
var CombinationInSpan = combinationInSpanThm{family.Add(registry.ProofEntry{
	Name: "CombinationInSpan",
	Key:  "prop_dab6902a69e1cba7",
	Build: comm_ring.CommRing.Law(
		"∀k:num. ∀e:(num → num → A). ∀c:(num → A). Σ_{i<k} c(i) • e(i) ∈ vec_span(k, e)",
		func(a *Argument, ring Fact, k *Expr[Nat], e *Arrow2[Nat, Nat, A], c *Arrow[Nat, A]) {
			a.Do(Unfold(VecSpanDef), Unfold(set_basic.SetMemberDef))
			a.Take(c)
			a.Show(
				"the combination is itself",
				Basic())
		}),
})}

// SpanMember — a member of the family below k lies in the span of the
// family's first k members.
//
// The combination that realizes it is the Kronecker one: the ring's one
// at the chosen index, its zero everywhere else. The unit law and the
// annihilation law read that summand as the family's vector where the
// index is chosen and as the zero vector everywhere else, which is
// exactly the shape the delta sum collapses. The hypothesis is spent once, placing the index inside
// the range, so that the term the delta sum keeps is the one wanted.
var SpanMember = spanMemberThm{family.Add(registry.ProofEntry{
	Name: "SpanMember",
	Key:  "prop_7bcf9d700f34af90",
	Build: comm_ring.CommRing.Law(Statement{
		Binders: "∀k j:num. ∀e:(num → num → A).",
		Hypotheses: []string{
			"j < k",
		},
		Conclusion: "e(j) ∈ vec_span(k, e)",
	},
		func(a *Argument, ring Fact, k, j *Expr[Nat], e *Arrow2[Nat, Nat, A], below Fact) {
			// The fold mechanism at pointwise addition, read off the ring:
			// that it folds at all, and from which element.
			folds := MonoidalVecAdd.Read(ring)
			startsAtZero := NeutralVecAdd.Read(ring)
			inRange := a.Have(
				"the chosen index lies in the range",
				"j ∈ {i:num | i < k}",
				BySets(below))

			silencing := a.Have(
				"at the chosen index the Kronecker coefficient leaves the "+
					"family's vector alone; elsewhere it silences the summand",
				"∀i:num. COND(i = j, R.one, R.zero) • e(i) = COND(i = j, e(i), neutral_elem(vec_add))",
				Derive(func(b *Argument) {
					b.Fix("i")
					b.Cases(b.Term("i = j"))
					b.When(
						"i = j: the coefficient is the ring's one, which acts as the identity",
						func(c *Argument, eq Fact) {
							c.Show(
								"so the summand is the family's vector at that index",
								By(Normalized, eq, SmulOne, ring))
						})
					b.Otherwise(
						"¬(i = j): the coefficient is the ring's zero, which sends every vector to the zero vector",
						func(c *Argument, neq Fact) {
							c.Show(
								"which is the element the fold starts from",
								By(neq, ZeroSmul, startsAtZero, ring))
						})
				}))

			combination := a.Have(
				"so that combination folds to the family's vector at the chosen index",
				"Σ_{i<k} COND(i = j, R.one, R.zero) • e(i) = e(j)",
				CalcEq(
					Leg(
						a.Term("Σ_{i<k} COND(i = j, e(i), neutral_elem(vec_add))"),
						"the summands are that Kronecker delta",
						Congr(),
						Funext(),
						By(silencing)),
					Leg(
						a.Term("COND(j ∈ {i:num | i < k}, e(j), neutral_elem(vec_add))"),
						"the delta sum keeps only the term at the chosen index, guarded by the range",
						// The value kept there is the family read at that
						// index, which the goal's β-reduct does not spell, so
						// Delta's summand binder is pinned by name.
						By(folds, Where(monoidal.Delta, "f", e))),
					FinalLeg(
						"and the index lies in the range, so that term survives",
						By(inRange)),
				))

			kronecker := a.TermAs[Fun[Nat, A]]("λi:num. COND(i = j, R.one, R.zero)")
			a.Show(
				"so the family's vector is the combination with the Kronecker coefficients, which lies in the span",
				combination.RwRev(),
				By(CombinationInSpan.Read(ring).At(k, e, kronecker)))
		}),
})}

// SpanMono — the spans of a family grow with the bound: taking more
// of the family to combine can only add combinations. That is what
// lets an argument stepping along a family carry forward what it has
// already built, instead of producing it again at the wider bound.
//
// The coefficients extend by zero. On the smaller range the extended
// sequence is the original one, so the two summand families agree
// there and the folds over that range are equal; on the part of the
// larger range the smaller one does not reach, the coefficient is the
// ring's zero, whose action on any vector is the zero vector — the
// element pointwise addition folds from — so the wider fold gains only
// silent summands and does not move: the fold mechanism's congruence
// and truncation laws say all of it.
var SpanMono = spanMonoThm{family.Add(registry.ProofEntry{
	Name: "SpanMono",
	Key:  "prop_81af8cf9733c0aca",
	Build: comm_ring.CommRing.Law(
		Statement{
			Binders: "∀k m:num. ∀e:(num → num → A). ∀x:(num → A).",
			Hypotheses: []string{
				"k ≤ m",
				"x ∈ vec_span(k, e)",
			},
			Conclusion: "x ∈ vec_span(m, e)",
		},
		func(a *Argument, ring Fact, k, m *Expr[Nat], e *Arrow2[Nat, Nat, A], x *Arrow[Nat, A],
			bound, member Fact) {
			// The hypothesis hands over a coefficient sequence c for the
			// smaller bound; the larger bound takes c extended by the
			// ring's zero.
			_, realizes := a.Unpack(a.Unfolded(a.Unfolded(member, set_basic.SetMemberDef), VecSpanDef))
			extended := a.TermAs[Fun[Nat, A]]("λi:num. COND(i < k, c(i), R.zero)")

			folds := MonoidalVecAdd.Read(ring)
			startsAtZero := NeutralVecAdd.Read(ring)
			agree := a.Have(
				"on the smaller range the extended coefficient is the original one, so the summands agree there",
				"∀j:num. j ∈ {i:num | i < k} ⇒ c(j) • e(j) = COND(j < k, c(j), R.zero) • e(j)",
				BySets())
			silent := a.Have(
				"from k on the extended coefficient is the ring's zero, and the "+
					"zero scalar sends every vector to the element the fold starts from",
				"∀j:num. k ≤ j ∧ j < m ⇒ COND(j < k, c(j), R.zero) • e(j) = neutral_elem(vec_add)",
				By(startsAtZero, ring, ZeroSmul, nat_order.NotLessThan))
			widened := a.Have(
				"so x is the combination of the family's first m members with the extended coefficients",
				"x = Σ_{i<m} COND(i < k, c(i), R.zero) • e(i)",
				CalcEq(
					Leg(
						a.Term("Σ_{i<k} c(i) • e(i)"),
						"x is the combination the smaller bound supplies",
						By(realizes)),
					Leg(
						a.Term("Σ_{i<k} COND(i < k, c(i), R.zero) • e(i)"),
						"whose summands the extended coefficients reproduce over that range",
						By(folds, agree, monoidal.Congruence)),
					FinalLeg(
						"and from k on they are silent, so the fold over the larger range is the same",
						Symm(),
						By(folds, bound, silent, monoidal.BelowTruncate)),
				))
			a.Show(
				"so x lies in the span of the family's first m members",
				widened.Rw(),
				By(CombinationInSpan.Read(ring).At(m, e, extended)))
		}),
})}

// SpanSubspace — a span is a subspace: it holds the zero vector and is
// closed under the pointwise sum and under the scalar action.
//
// Each part names the coefficient sequence that realizes the result —
// the constant zero sequence, the pointwise sum of the two sequences,
// the sequence scaled — so nothing is built up index by index and no
// induction on k is run. What is left in each part is an identity
// between summands — every summand silent, a sum of coefficients
// splitting, a product of scalars regrouping — and one law of the fold
// mechanism that consumes it: a fold of silent summands is the element
// it starts from, two folds over one range combine into a single fold
// of the sums, and a scalar passes through a fold. The last two need
// their summand identity carried under the fold first, which is the
// mechanism's congruence law; the first asks for the identity
// pointwise and needs nothing else.
var SpanSubspace = spanSubspaceThm{family.Add(registry.ProofEntry{
	Name: "SpanSubspace",
	Key:  "prop_6293078e34dd4bb0",
	Build: comm_ring.CommRing.Law("∀k:num. ∀e:(num → num → A). vec_subspace(vec_span(k, e))",
		func(a *Argument, ring Fact, k *Expr[Nat], e *Arrow2[Nat, Nat, A]) {
			// What the parts below spend of the fold mechanism, the first two
			// read off the ring: that it is available at pointwise addition
			// at all, which element the fold starts from, and that the range
			// it runs over is finite.
			folds := MonoidalVecAdd.Read(ring)
			startsAtZero := NeutralVecAdd.Read(ring)
			finite := a.Have(
				"the index range is finite",
				"finite({i:num | i < k})",
				By(num_segment.FiniteBelowStrict))

			// A subspace is three conditions, and each asks for a
			// membership. Every part names the coefficients that realize its
			// vector and puts it in the span by CombinationInSpan; the sum
			// and the scalar parts first read the coefficients of the
			// vectors they are given off the span's definition.
			a.Do(Unfold(VecSubspaceDef), SplitConjAll(
				Case(
					"the zero vector lies in the span: the constant zero coefficients realize it",
					Derive(func(b *Argument) {
						silent := b.Have(
							"every summand is the zero scalar acting, which is the element the fold starts from",
							"∀j:num. j ∈ {i:num | i < k} ⇒ R.zero • e(j) = neutral_elem(vec_add)",
							By(startsAtZero, ZeroSmul, ring))
						collapse := b.Have(
							"so the whole fold is that element",
							"Σ_{i<k} R.zero • e(i) = neutral_elem(vec_add)",
							By(folds, silent, monoidal.EqNeutral))
						zeroIsFold := b.Have(
							"which is the zero vector",
							"vec_zero = Σ_{i<k} R.zero • e(i)",
							By(startsAtZero, collapse))
						zeros := b.TermAs[Fun[Nat, A]]("λi:num. R.zero")
						b.Show(
							"so the zero vector is the combination with the zero coefficients",
							zeroIsFold.Rw(),
							By(CombinationInSpan.Read(ring).At(k, e, zeros)))
					})),

				Case(
					"the span is closed under the sum: the pointwise sum of the two coefficient sequences realizes it",
					Derive(func(b *Argument) {
						b.Fix("u")
						b.Fix("v")
						both := b.Conjuncts(
							b.Assume(),
							"u lies in the span",
							"and so does v")
						// Two combinations are read here, and the span's
						// definition calls both coefficient sequences c, so
						// they take names of their own, a and b.
						_, uReads := b.Unpack(b.Unfolded(b.Unfolded(both[0], set_basic.SetMemberDef), VecSpanDef), "a")
						_, vReads := b.Unpack(b.Unfolded(b.Unfolded(both[1], set_basic.SetMemberDef), VecSpanDef), "b")

						summands := b.Have(
							"at each index the sum of the two coefficients acts as the two actions do",
							"∀j:num. j ∈ {i:num | i < k} ⇒ (a(j) + b(j)) • e(j) = a(j) • e(j) + b(j) • e(j)",
							By(SmulAddRight, ring))
						splits := b.Have(
							"so the fold of the pointwise sum is the sum of the two folds",
							"Σ_{i<k} (a(i) + b(i)) • e(i) = Σ_{i<k} a(i) • e(i) + Σ_{i<k} b(i) • e(i)",
							CalcEq(
								Leg(
									b.Term("Σ_{i<k} (a(i) • e(i) + b(i) • e(i))"),
									"each summand splits into the two actions",
									By(folds, summands, monoidal.Congruence)),
								FinalLeg(
									"and one fold of two summands is the two folds",
									// The law's summand is the operation applied to
									// the two halves, and the goal spells that
									// application rather than the operation and the
									// halves, so all three are pinned by name.
									By(
										folds,
										finite,
										Where(monoidal.Pointwise, "op", b.Term("vec_add")).
											Where("f", b.Term("λi:num. a(i) • e(i)")).
											Where("g", b.Term("λi:num. b(i) • e(i)")))),
							))
						sumIsFold := b.Have(
							"so u + v is the combination with the summed "+
								"coefficients, each of u and v being the fold of its own",
							"u + v = Σ_{i<k} (a(i) + b(i)) • e(i)",
							By(uReads, vReads, splits))
						summed := b.TermAs[Fun[Nat, A]]("λi:num. a(i) + b(i)")
						b.Show(
							"which lies in the span",
							sumIsFold.Rw(),
							By(CombinationInSpan.Read(ring).At(k, e, summed)))
					})),

				Case(
					"the span is closed under the scalar action: the scaled coefficient sequence realizes it",
					Derive(func(b *Argument) {
						// The scalar is called d here: c is the span's own
						// name for the coefficient sequence u unpacks into.
						b.Fix("d")
						b.Fix("u")
						member := b.Assume()
						_, uReads := b.Unpack(b.Unfolded(b.Unfolded(member, set_basic.SetMemberDef), VecSpanDef))

						summands := b.Have(
							"at each index the two actions in turn are the action of the product of the scalars",
							"∀j:num. j ∈ {i:num | i < k} ⇒ d • (c(j) • e(j)) = (d * c(j)) • e(j)",
							By(SmulMul, ring))
						scaled := b.Have(
							"so scaling the fold scales each coefficient",
							"d • Σ_{i<k} c(i) • e(i) = Σ_{i<k} (d * c(i)) • e(i)",
							CalcEq(
								Leg(
									b.Term("Σ_{i<k} d • (c(i) • e(i))"),
									"the scalar passes through the fold",
									By(finite, ring, SmulIterate)),
								FinalLeg(
									"and each summand is one action, by the product of the two scalars",
									By(folds, summands, monoidal.Congruence)),
							))
						scaledIsFold := b.Have(
							"so d • u is the combination with the scaled coefficients, u being the fold of its own",
							"d • u = Σ_{i<k} (d * c(i)) • e(i)",
							By(uReads, scaled))
						scaledCoefficients := b.TermAs[Fun[Nat, A]]("λi:num. d * c(i)")
						b.Show(
							"which lies in the span",
							scaledIsFold.Rw(),
							By(CombinationInSpan.Read(ring).At(k, e, scaledCoefficients)))
					})),
			))
		}),
})}

// VecSubspace — the vectors of a dimension are a subspace of the
// sequences.
//
// Membership in that set IS the dimension predicate, so the three
// conditions a subspace must meet are the chapter's three closure laws
// read through the set-builder, one per arm. The predicate itself is
// never unfolded here: the closure laws are cited, not re-proved. What
// the statement buys is that everything said of a subspace in general
// is said of the vectors of a dimension, with nothing to restate.
var VecSubspace = vecSubspaceThm{family.Add(registry.ProofEntry{
	Name: "VecSubspace",
	Key:  "prop_eef23c47c5a18cdd",
	Build: comm_ring.CommRing.Law("∀n:num. vec_subspace({u:(num → A) | vec⟨n⟩(u)})",
		func(a *Argument, ring Fact, n Term) {
			a.Do(Unfold(VecSubspaceDef), SplitConjAll(
				// The zero vector's law is stated for an arbitrary zero,
				// so this arm spends no ring law at all.
				Case(
					"the zero vector lies in the set, being an n-vector for every n",
					BySets(VecZero)),
				Case(
					"the set is closed under the sum: two n-vectors add to an n-vector",
					BySets(ring, VecAdd)),
				Case(
					"and under the scalar action: a scalar multiple of an n-vector is an n-vector",
					BySets(ring, VecSmul)),
			))
		}),
})}

// SubspaceSub — a subspace is closed under differences.
//
// The definition asks for the zero vector, the sum and the scalar
// action, and deliberately not for the difference, because it does not
// have to: subtraction adds the negation, and the negation is the
// scalar action at minus one. So a difference is a sum of u with a
// scalar multiple of v, which is exactly what the two clauses the
// definition does ask for produce.
var SubspaceSub = subspaceSubThm{family.Add(registry.ProofEntry{
	Name: "SubspaceSub",
	Key:  "prop_7b07b931910a2f21",
	Build: comm_ring.CommRing.Law(
		Statement{
			Binders: "∀s:set(num → A). ∀u v:(num → A).",
			Hypotheses: []string{
				"vec_subspace(s)",
				"u ∈ s",
				"v ∈ s",
			},
			Conclusion: "u - v ∈ s",
		},
		func(a *Argument, _ Fact, s *Expr[Set[Fun[Nat, A]]], u, v *Arrow[Nat, A], subspace, uIn, vIn Fact) {
			// Both laws hold at the ring in hand, so the goal's difference
			// becomes a sum of u with a scalar multiple of v.
			a.Do(Simp(Fwd(SubAddNeg), Fwd(NegIsSmul)))

			scaled := a.Have(
				"the scalar action at minus one keeps v inside the subspace",
				"-R.one • v ∈ s",
				By(vIn, subspace, VecSubspaceDef))
			a.Show(
				"and the subspace holds the sum of u with it",
				By(uIn, scaled, subspace, VecSubspaceDef))
		}),
})}

// SubspaceIterate — a subspace is closed under sums of arbitrarily many
// of its vectors.
//
// The induction is not here. `monoidal.Closed` carries a property along
// a fold, and the property carried is membership in s: it must hold at
// the element the fold starts from, survive the operation folded, and
// hold at every summand the fold actually contributes. A subspace meets
// the first two by definition — pointwise addition folds from the zero
// vector, which a subspace holds, and a subspace is closed under the sum
// — and the third is this statement's own hypothesis, which is stronger
// than the law wants.
//
// No finiteness is asked of the index set. A fold over an infinite
// support is the element it starts from, and a subspace holds it.
var SubspaceIterate = subspaceIterateThm{family.Add(registry.ProofEntry{
	Name: "SubspaceIterate",
	Key:  "prop_b5342095f01ba9e7",
	Build: comm_ring.CommRing.Law(
		Statement{
			Binders: "∀s:set(num → A). ∀t:set(B). ∀F:(B → num → A).",
			Hypotheses: []string{
				"vec_subspace(s)",
				"∀i:B. i ∈ t ⇒ F(i) ∈ s",
			},
			Conclusion: "Σ_{i∈t} F(i) ∈ s",
		},
		func(a *Argument, ring Fact, s *Expr[Set[Fun[Nat, A]]], t *Expr[Set[B]], F *Arrow2[B, Nat, A],
			subspace, summands Fact) {
			// The property carried along the fold. The goal states its
			// β-reduct, so no slot of the goal spells it and it is pinned by
			// name where the law is applied.
			inSubspace := a.TermAs[Set[Fun[Nat, A]]]("λv:(num → A). v ∈ s")

			// Being a subspace is three conditions, and the law spends two.
			conditions := a.Unfolded(subspace, VecSubspaceDef)
			atNeutral := a.Have(
				"the fold starts from the zero vector, which the subspace holds",
				"neutral_elem(vec_add) ∈ s",
				Simp(Fwd(NeutralVecAdd.Read(ring))),
				By(conditions))
			acrossVecAdd := a.Have(
				"membership in s survives the operation folded, a subspace being closed under the sum",
				"∀u v:(num → A). u ∈ s ∧ v ∈ s ⇒ u + v ∈ s",
				By(conditions))
			live := a.Have(
				"and the law asks the hypothesis only where the summand is not silent",
				"∀i:B. i ∈ t ∧ F(i) ≠ neutral_elem(vec_add) ⇒ F(i) ∈ s",
				By(summands))

			a.Show(
				"so the closure law carries membership in s along the fold",
				By(
					MonoidalVecAdd.Read(ring),
					atNeutral,
					acrossVecAdd,
					live,
					Where(monoidal.Closed, "P", inSubspace)))
		}),
})}

// VecIterate — a fold of m-vectors is an m-vector: the vectors of a
// dimension are a subspace (VecSubspace), and a subspace holds every
// sum of its vectors (SubspaceIterate).
var VecIterate = vecIterateThm{family.Add(registry.ProofEntry{
	Name: "VecIterate",
	Key:  "prop_65522e15cfb6d7f2",
	Build: comm_ring.CommRing.Law(Statement{
		Binders: "∀m:num. ∀s:set(num). ∀F:(num → num → A).",
		Hypotheses: []string{
			"∀i:num. i ∈ s ⇒ vec⟨m⟩(F(i))",
		},
		Conclusion: "vec⟨m⟩(Σ_{i∈s} F(i))",
	},
		func(
			a *Argument,
			ring Fact,
			m *Expr[Nat],
			s *Expr[Set[Nat]],
			F *Arrow2[Nat, Nat, A],
			pointwise Fact,
		) {
			subspace := a.Have(
				"the m-vectors are a subspace",
				"vec_subspace({u:(num → A) | vec⟨m⟩(u)})",
				By(ring, VecSubspace))
			summands := a.Have(
				"which holds every summand",
				"∀i:num. i ∈ s ⇒ F(i) ∈ {u:(num → A) | vec⟨m⟩(u)}",
				BySets(pointwise))
			// Membership in that set normalizes to the dimension predicate,
			// so the goal does not spell the set, and the law's set is
			// pinned by name.
			vectors := a.Term("{u:(num → A) | vec⟨m⟩(u)}")
			sum := a.Have(
				"so it holds their sum",
				"Σ_{i∈s} F(i) ∈ {u:(num → A) | vec⟨m⟩(u)}",
				By(ring, subspace, summands, Where(SubspaceIterate, "s", vectors)))
			a.Show(
				"which is to say the sum is an m-vector",
				BySets(sum))
		}),
})}

// SpanLeast — the span of a family lies in every subspace holding it:
// any subspace holding the family's first k members holds everything
// they span. With SpanSubspace and SpanMember, the span is therefore
// the least subspace holding its family.
//
// An element of the span is a combination of those members, and a
// combination is built by the two operations a subspace is closed
// under: each summand is a scalar multiple of a family vector the
// subspace holds, so it lies in the subspace, and a subspace holds
// every sum of its own vectors, of any length (SubspaceIterate).
var SpanLeast = spanLeastThm{family.Add(registry.ProofEntry{
	Name: "SpanLeast",
	Key:  "prop_d75ff4a01ee608fe",
	Build: comm_ring.CommRing.Law(
		Statement{
			Binders: "∀s:set(num → A). ∀k:num. ∀e:(num → num → A).",
			Hypotheses: []string{
				"vec_subspace(s)",
				"∀i:num. i < k ⇒ e(i) ∈ s",
			},
			Conclusion: "vec_span(k, e) ⊆ s",
		},
		func(a *Argument, ring Fact, s *Expr[Set[Fun[Nat, A]]], k *Expr[Nat], e *Arrow2[Nat, Nat, A],
			subspace, familyIn Fact) {
			// An inclusion is a pointwise implication: take x in the span.
			a.Do(Unfold(set_basic.SubsetDef))
			a.Fix("x")
			member := a.Assume()

			// x is a combination of the family below k; the coefficients c
			// the condition only claims to exist are named.
			_, expansion := a.Unpack(a.Unfolded(a.Unfolded(member, set_basic.SetMemberDef), VecSpanDef))

			// Being a subspace is three conditions, and the summands spend
			// the scalar action's.
			conditions := a.Unfolded(subspace, VecSubspaceDef)
			summands := a.Have(
				"each summand of that combination lies in s",
				"∀i:num. i ∈ {i:num | i < k} ⇒ c(i) • e(i) ∈ s",
				Derive(func(b *Argument) {
					b.Fix("i")
					inRange := b.Assume()
					below := b.Have(
						"the index lies below the bound",
						"i < k",
						BySets(inRange))
					familyVec := b.Have(
						"so the family's vector there lies in s",
						"e(i) ∈ s",
						By(below, familyIn))
					b.Show(
						"and a subspace is closed under the scalar action",
						By(familyVec, conditions))
				}))

			foldMember := a.Have(
				"so the combination lies in s, a subspace holding every sum of its own vectors",
				"Σ_{i<k} c(i) • e(i) ∈ s",
				By(ring, subspace, summands, SubspaceIterate))

			a.Show(
				"and x is that combination",
				expansion.Rw(),
				By(foldMember))
		}),
})}

// SpanVec — a span of n-vectors is made of n-vectors: when every
// member of the family below the bound has dimension n, so does every
// element of the span.
//
// A span asks nothing of its family, so it carries no dimension of its
// own; a dimension reaches an element of the span only through the
// family it is combined from. The n-vectors are a subspace holding the
// family's first k members, so SpanLeast puts the whole span inside
// them.
var SpanVec = spanVecThm{family.Add(registry.ProofEntry{
	Name: "SpanVec",
	Key:  "prop_de91ef24434d3c4",
	Build: comm_ring.CommRing.Law(
		Statement{
			Binders: "∀n k:num. ∀e:(num → num → A). ∀x:(num → A).",
			Hypotheses: []string{
				"∀i:num. i < k ⇒ vec⟨n⟩(e(i))",
				"x ∈ vec_span(k, e)",
			},
			Conclusion: "vec⟨n⟩(x)",
		},
		func(a *Argument, ring Fact, n, k *Expr[Nat], e *Arrow2[Nat, Nat, A], x *Arrow[Nat, A],
			familyVecs Fact, inSpan Fact) {
			subspace := a.Have(
				"the n-vectors are a subspace",
				"vec_subspace({u:(num → A) | vec⟨n⟩(u)})",
				By(ring, VecSubspace))
			members := a.Have(
				"which holds the family's first k members",
				"∀i:num. i < k ⇒ e(i) ∈ {u:(num → A) | vec⟨n⟩(u)}",
				BySets(familyVecs))
			within := a.Have(
				"so it holds everything they span",
				"vec_span(k, e) ⊆ {u:(num → A) | vec⟨n⟩(u)}",
				By(ring, subspace, members, SpanLeast))
			inSet := a.Have(
				"so x lies among them",
				"x ∈ {u:(num → A) | vec⟨n⟩(u)}",
				By(a.Unfolded(within, set_basic.SubsetDef), inSpan))
			a.Show(
				"which is to say x is an n-vector",
				BySets(inSet))
		}),
})}

// SpanSubset — a span lies in another span as soon as the first
// family's members do: the second span is a subspace, and SpanLeast
// puts everything the first family spans inside it.
var SpanSubset = spanSubsetThm{family.Add(registry.ProofEntry{
	Name: "SpanSubset",
	Key:  "prop_cbfca227becd1d15",
	Build: comm_ring.CommRing.Law(
		Statement{
			Binders: "∀k m:num. ∀e f:(num → num → A).",
			Hypotheses: []string{
				"∀i:num. i < k ⇒ e(i) ∈ vec_span(m, f)",
			},
			Conclusion: "vec_span(k, e) ⊆ vec_span(m, f)",
		},
		func(a *Argument, ring Fact, k, m *Expr[Nat], e, f *Arrow2[Nat, Nat, A], members Fact) {
			isSubspace := a.Have(
				"the second span is a subspace",
				"vec_subspace(vec_span(m, f))",
				By(SpanSubspace.Read(ring)))
			a.Show(
				"which holds the first family's members, so everything they span",
				By(ring, isSubspace, members, SpanLeast))
		}),
})}

// SpanPermute — the span of a family does not depend on the order of
// its members: re-indexing the first k by a permutation of the range
// leaves their span unchanged.
//
// Each inclusion is SpanSubset, once every member of one family is
// known to lie in the other's span. One way, every member of the re-indexed family is a member of the
// family, p keeping its index inside the range. The other way needs
// every index of the range to be reached, and it is: an injective map
// of the numbers below k into themselves is onto them
// (num_segment.BelowStrictInjectiveOnto) — which is the whole reason the
// hypothesis asks for injectivity and not for a bijection.
var SpanPermute = spanPermuteThm{family.Add(registry.ProofEntry{
	Name: "SpanPermute",
	Key:  "prop_c359aa5a00d706d9",
	Build: comm_ring.CommRing.Law(
		Statement{
			Binders: "∀k:num. ∀e:(num → num → A). ∀p:(num → num).",
			Hypotheses: []string{
				"∀i:num. i < k ⇒ p(i) < k",
				"∀i j:num. i < k ∧ j < k ∧ p(i) = p(j) ⇒ i = j",
			},
			Conclusion: "vec_span(k, λi:num. e(p(i))) = vec_span(k, e)",
		},
		func(a *Argument, ring Fact, k *Expr[Nat], e *Arrow2[Nat, Nat, A], p *Arrow[Nat, Nat],
			into, injective Fact) {
			onto := a.Have(
				"p reaches every index below k, an injective self-map of the range being onto it",
				"∀j:num. j < k ⇒ ∃i:num. i < k ∧ p(i) = j",
				By(into, injective, num_segment.BelowStrictInjectiveOnto))

			forwardMembers := a.Have(
				"each member of the re-indexed family is a member of the family below k",
				"∀i:num. i < k ⇒ e(p(i)) ∈ vec_span(k, e)",
				Derive(func(b *Argument) {
					b.Fix("i")
					below := b.Assume()
					stays := b.Have(
						"p keeps the index inside the range",
						"p(i) < k",
						By(below, into))
					b.Show(
						"so the family's member there lies in its span",
						By(ring, stays, SpanMember))
				}))
			backwardMembers := a.Have(
				"each member of the family below k is a member of the re-indexed family",
				"∀j:num. j < k ⇒ e(j) ∈ vec_span(k, λi:num. e(p(i)))",
				Derive(func(b *Argument) {
					b.Fix("j")
					below := b.Assume()
					reached := b.Have(
						"some index below k is sent to j",
						"∃i:num. i < k ∧ p(i) = j",
						By(below, onto))
					_, hit := b.Unpack(reached)
					// The member is the re-indexed family read at i, which the
					// goal spells only through its β-reduct, so the family is
					// pinned by name.
					member := b.Have(
						"the re-indexed family's member at that index lies in its span",
						"e(p(i)) ∈ vec_span(k, λl:num. e(p(l)))",
						By(ring, hit, Where(SpanMember, "e", b.Term("λl:num. e(p(l))"))))
					b.Show(
						"and that member is e(j)",
						By(hit, member))
				}))
			reindexed := a.TermAs[Fun2[Nat, Nat, A]]("λi:num. e(p(i))")
			forward := a.Have(
				"so the re-indexed family's span lies in the family's",
				"vec_span(k, λi:num. e(p(i))) ⊆ vec_span(k, e)",
				By(SpanSubset.Read(ring).At(k, k, reindexed, e), forwardMembers))
			backward := a.Have(
				"and the family's span lies in the re-indexed family's",
				"vec_span(k, e) ⊆ vec_span(k, λi:num. e(p(i)))",
				By(SpanSubset.Read(ring).At(k, k, e, reindexed), backwardMembers))

			a.Show(
				"so the two spans are equal",
				By(forward, backward, set_order.SubsetAntisym))
		}),
})}

// SpanSwap — exchanging two members of a family leaves the span of its
// first m unchanged.
//
// The exchange re-indexes the family by the transposition of t and j,
// and the transposition is a permutation of the range: it sends t to j,
// j to t and every other index to itself, so it stays below m because t
// and j do, and two indices it sends to the same place are equal,
// whichever of t, j or neither each of them is. SpanPermute then keeps
// the span.
var SpanSwap = spanSwapThm{family.Add(registry.ProofEntry{
	Name: "SpanSwap",
	Key:  "prop_e59c63d4005600ee",
	Build: comm_ring.CommRing.Law(
		Statement{
			Binders: "∀m t j:num. ∀f:(num → num → A).",
			Hypotheses: []string{
				"t < m",
				"j < m",
			},
			Conclusion: "vec_span(m, λi:num. f(COND(i = t, j, COND(i = j, t, i)))) = vec_span(m, f)",
		},
		func(a *Argument, ring Fact, m, t, j *Expr[Nat], f *Arrow2[Nat, Nat, A], tBelow, jBelow Fact) {
			// The transposition. The goal states only its value inside the
			// family's λ, so it is pinned by name where the re-indexing law
			// is applied.
			swap := a.TermAs[Fun[Nat, Nat]]("λi:num. COND(i = t, j, COND(i = j, t, i))")

			into := a.Have(
				"the transposition keeps the range: t goes to j, j to t, the rest stay put",
				"∀i:num. i < m ⇒ COND(i = t, j, COND(i = j, t, i)) < m",
				By(tBelow, jBelow))
			injective := a.Have(
				"and it is one-to-one on it",
				Statement{
					Binders: "∀x y:num.",
					Hypotheses: []string{
						"x < m",
						"y < m",
						"COND(x = t, j, COND(x = j, t, x)) = COND(y = t, j, COND(y = j, t, y))",
					},
					Conclusion: "x = y",
				},
				Derive(func(b *Argument) {
					b.Fix()
					b.Fix()
					sameImage := b.Assume()
					b.Show(
						"whichever of t, j or neither each index is, equal images force equal indices",
						By(sameImage))
				}))

			a.Show(
				"so the exchange is a re-indexing by a permutation of the range, which keeps the span",
				By(ring, into, injective, Where(SpanPermute, "p", swap)))
		}),
})}
