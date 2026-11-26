// fold.go — the chapter's opening: what real addition contributes to
// the fold, the fold's own laws read at ℝ, and how a sum answers to a
// change of its index set.
//
// Three parts, marked by banners:
//
// - The bridge: real addition folds
// - The fold's laws at ℝ
// - Changing the index set

package real_sum

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The bridge: real addition folds
// ---------------------------------------------------------------------------
//
// The fold mechanism is carrier-free: it asks of an operation only that
// it commute, associate, and have a neutral element, and everything it
// proves is proved from those three. ℝ's ring chapter supplies them —
// real addition folds (real_ring.MonoidalAdd) and folds from zero
// (real_ring.NeutralAdd), each read off ℝ's additive monoid through
// the monoid chapter's bridge — so every law of the mechanism
// instantiates at `real_add` for the asking, and this chapter is what
// ℝ's own algebra adds on top.

// RealModuleSum — a finite sum in the real additive module is the usual
// real sum: the module chapter's fold from a monoid's identity is the
// iterated operation, and `real_sum` is that operation at real addition.
var RealModuleSum = realModuleSumThm{family.Add(registry.ProofEntry{
	Name: "RealModuleSum",
	Key:  "prop_c95c49f7203c4b07",
	Build: family.Theorem(Statement{
		Binders:    "∀f:(A → real). ∀s:set(A).",
		Hypotheses: []string{"finite(s)"},
		Conclusion: "module_sum(real_add, &0, s, f) = sum(s, f)",
	}, func(a *Argument, f *Arrow[A, Real], s *Expr[Set[A]], finite Fact) {
		a.Show(
			"Σ is the iterated operation at real addition, which the fold is",
			Unfold(RealSumDef),
			By(finite, module.ModuleSumIteratedOp.Read(real_ring.AddMonoid).At(s, f)))
	}),
})}

// RealOfNatSum — the cast of a finite sum of natural numbers is the sum of the
// casts: the transfer law for folds, read at the cast from addition on ℕ to
// addition on ℝ.
var RealOfNatSum = realOfNatSumThm{family.Add(registry.ProofEntry{
	Name: "RealOfNatSum",
	Key:  "prop_b9e0738d086c3839",
	Build: family.Theorem(Statement{
		Binders:    "∀s:set(A). ∀f:(A → num).",
		Hypotheses: []string{"finite(s)"},
		Conclusion: "real_of_num(sum(s, f)) = sum(s, λx:A. real_of_num(f(x)))",
	}, func(a *Argument, s *Expr[Set[A]], f *Arrow[A, Nat], finite Fact) {
		// Each sum is the fold at its carrier's addition.
		a.Do(Unfold(nat_sum.NatSumDef), Unfold(RealSumDef))
		fixesNeutral := a.Have(
			"the cast fixes the neutral element",
			"real_of_num(neutral_elem(λi:num. λj:num. i + j)) = neutral_elem(real_add)",
			Simp(Fwd(nat_sum.NeutralNatAdd), Fwd(real_ring.NeutralAdd)),
			Refl())
		a.Show(
			"so the transfer law carries the fold across the cast, which crosses addition",
			By(
				finite,
				fixesNeutral,
				monoidal.Homomorphic,
				nat_sum.MonoidalNatAdd,
				real_ring.MonoidalAdd,
				real_construction.OfNumAdd))
	}),
})}

// ---------------------------------------------------------------------------
// The fold's laws at ℝ
// ---------------------------------------------------------------------------
//
// The clauses and index laws here provide the real-valued interfaces
// used by this chapter and its consumers. Unfolding `real_sum` reads a
// sum as `iterated_op` at real addition; the corresponding monoidal law
// then applies, with real_ring.NeutralAdd identifying zero when needed.
//
// A law is applied, not searched for: the goal supplies its operation,
// index sets and summands, while the real addition bridge and the
// statement's hypotheses supply its antecedents. `Delete` also turns
// the additive deletion equation into a subtraction, and `Degenerate`
// identifies the nonzero set with the fold's support.

// Clauses — the fold's recursion, read at ℝ: the empty sum is zero,
// and inserting a point either changes nothing, because the point was
// already there, or contributes its own value.
var Clauses = clausesThm{family.Add(registry.ProofEntry{
	Name: "Clauses",
	Key:  "prop_78a0e3d2888abcc3",
	Build: family.Theorem(
		"(∀f:(A → real). sum(∅, f) = &0) ∧ "+
			"(∀g:(C → real). ∀x:C. ∀s:set(C). "+
			"    finite(s) ⇒ sum(insert(x, s), g) = COND(x ∈ s, sum(s, g), g(x) + sum(s, g)))",
		func(a *Argument) {
			a.Do(Unfold(RealSumDef), By(monoidal.Clauses, real_ring.MonoidalAdd, real_ring.NeutralAdd))
		}),
})}

// BelowClauses — Σ's recursion at the half-open range {i | i < n}: the
// empty range sums to zero, and one more index on top of the range adds
// that term. The fold's own clause at the range, read at real addition.
var BelowClauses = belowClausesThm{family.Add(registry.ProofEntry{
	Name: "BelowClauses",
	Key:  "prop_6fdb63a63908fcdf",
	Build: family.Theorem(
		"∀f:(num → real). "+
			"    sum({i:num | i < 0}, f) = &0 ∧ "+
			"    (∀k:num. sum({i:num | i < suc(k)}, f) = sum({i:num | i < k}, f) + f(k))",
		func(a *Argument) {
			a.Do(Unfold(RealSumDef), By(monoidal.BelowClauses, real_ring.MonoidalAdd, real_ring.NeutralAdd))
		}),
})}

// Congruence — a sum sees the summand only on the index set, so two
// summands agreeing there give the same sum.
var Congruence = congruenceThm{family.Add(registry.ProofEntry{
	Name: "Congruence",
	Key:  "prop_1551ce4e42553a24",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀g f:(A → real).",
			Hypotheses: []string{
				"∀x:A. x ∈ s ⇒ g(x) = f(x)",
			},
			Conclusion: "sum(s, g) = sum(s, f)",
		},
		func(a *Argument) {
			a.Do(Unfold(RealSumDef), By(monoidal.Congruence, real_ring.MonoidalAdd))
		}),
})}

// CongruenceEverywhere — two summands that agree at every point of the
// carrier, and not merely on the index set, give the same sum.
//
// Agreement everywhere is the most this trio asks of its summands, so
// as a theorem this is the least it says: Congruence proves it
// outright, in one step and with nothing added. What it buys is at the
// citation site. A consumer whose summand identity is an outright
// equation of functions has no side condition to supply, and citing
// Congruence — or, between the bounds, IntervalCongruence — makes it
// fix a point and discharge a membership the identity never reads.
var CongruenceEverywhere = congruenceEverywhereThm{family.Add(registry.ProofEntry{
	Name: "CongruenceEverywhere",
	Key:  "prop_bf8886191614687b",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀g f:(A → real).",
			Hypotheses: []string{
				"∀x:A. g(x) = f(x)",
			},
			Conclusion: "sum(s, g) = sum(s, f)",
		},
		func(a *Argument) {
			a.Do(By(Congruence))
		}),
})}

// Superset — enlarging the index set past the points where the summand
// vanishes does not change the sum.
var Superset = supersetThm{family.Add(registry.ProofEntry{
	Name: "Superset",
	Key:  "prop_23fcad2e3dcfa104",
	Build: family.Theorem(
		Statement{
			Binders: "∀u v:set(A). ∀f:(A → real).",
			Hypotheses: []string{
				"u ⊆ v",
				"∀x:A. x ∈ v ∧ x ∉ u ⇒ f(x) = &0",
			},
			Conclusion: "sum(u, f) = sum(v, f)",
		},
		func(a *Argument) {
			a.Do(Unfold(RealSumDef), By(monoidal.Superset, real_ring.MonoidalAdd, real_ring.NeutralAdd))
		}),
})}

// Union — a sum splits across two disjoint finite index sets.
var Union = unionThm{family.Add(registry.ProofEntry{
	Name: "Union",
	Key:  "prop_d108af9bbe40e4b1",
	Build: family.Theorem(
		Statement{
			Binders: "∀s t:set(A). ∀f:(A → real).",
			Hypotheses: []string{
				"finite(s)",
				"finite(t)",
				"disjoint(s, t)",
			},
			Conclusion: "sum(s ∪ t, f) = sum(s, f) + sum(t, f)",
		},
		func(a *Argument) {
			a.Do(Unfold(RealSumDef), By(monoidal.Union, real_ring.MonoidalAdd))
		}),
})}

// Delta — a summand supported at a single index contributes its value
// there and nothing anywhere else.
var Delta = deltaThm{family.Add(registry.ProofEntry{
	Name: "Delta",
	Key:  "prop_79bcd2a9954c823d",
	Build: family.Theorem(
		"∀b:real. ∀s:set(A). ∀a:A. sum(s, λx:A. COND(x = a, b, &0)) = COND(a ∈ s, b, &0)",
		func(arg *Argument, b *Expr[Real], s *Expr[Set[A]], a *Expr[A]) {
			// The mechanism's summand is f(x) at a point; here f is the
			// constant b, so the instance is pinned at that function.
			constant := arg.TermAs[Fun[A, Real]]("λx:A. b")
			arg.Do(Unfold(RealSumDef), By(
				monoidal.Delta.At(arg.TermAs[Op[Real]]("real_add"), s, constant, a),
				real_ring.MonoidalAdd,
				real_ring.NeutralAdd))
		}),
})}

// Delete — dropping a point from the index set drops its contribution.
// The mechanism states this additively — the removed value plus the
// smaller sum is the original — so the subtraction the ℝ statement is
// written with is the step this member adds.
var Delete = deleteThm{family.Add(registry.ProofEntry{
	Name: "Delete",
	Key:  "prop_f72da5b761def6ae",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀f:(A → real). ∀a:A.",
			Hypotheses: []string{
				"finite(s)",
				"a ∈ s",
			},
			Conclusion: "sum(delete(s, a), f) = sum(s, f) - f(a)",
		},
		func(a *Argument) {
			a.Do(Unfold(RealSumDef),
				By(monoidal.Delete, real_ring.MonoidalAdd, real_ring.EqSubRightAdd, real_construction.AddSym))
		}),
})}

// OnSupport — a sum may be taken over the support instead of the whole
// index set. This is the one law here that needs nothing of ℝ: the
// mechanism's own statement quantifies over the operation, so at
// real_add it lands whole.
var OnSupport = onSupportThm{family.Add(registry.ProofEntry{
	Name: "OnSupport",
	Key:  "prop_8cb9b62e05c8b842",
	Build: family.Theorem(
		"∀s:set(A). ∀f:(A → real). sum(s, f) = sum(op_support(real_add, f, s), f)",
		func(a *Argument) {
			a.Do(Unfold(RealSumDef), By(monoidal.OnSupport))
		}),
})}

// Degenerate — where the summand is nonzero at infinitely many points
// there is no sum to speak of, and the convention is that it is zero.
//
// This is the fold's own escape clause read at ℝ. The mechanism folds
// over a set only when the summand's support there is finite, and
// answers with the neutral element otherwise; zero being that neutral,
// the two conventions agree. So the whole content is the identification
// of the hypothesis's carve-out with the support.
var Degenerate = degenerateThm{family.Add(registry.ProofEntry{
	Name: "Degenerate",
	Key:  "prop_198ad069b0d46fe0",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀f:(A → real).",
			Hypotheses: []string{
				"¬finite({x:A | x ∈ s ∧ f(x) ≠ &0})",
			},
			Conclusion: "sum(s, f) = &0",
		},
		func(a *Argument, s *Expr[Set[A]], f *Arrow[A, Real], infinite Fact) {
			// Nothing below is about ℝ-summation as such — it is all
			// about the fold the sum is, so read the goal as one.
			a.Do(Unfold(RealSumDef))
			support := a.Have(
				"the set the hypothesis counts is the fold's support — where "+
					"the summand differs from the neutral, which here is zero",
				"op_support(real_add, f, s) = {x:A | x ∈ s ∧ f(x) ≠ &0}",
				Unfold(monoidal.OpSupportDef),
				By(real_ring.NeutralAdd))
			// The definition as an equation, at this sum: iterated_op(real_add,
			// s, f) is the fold over that support when it is finite, and
			// neutral_elem(real_add) when it is not.
			cases := monoidal.ExpandCases.At(s, f, a.TermAs[Op[Real]]("real_add"))
			a.Show(
				"so the guard fails, and the fold's other branch is the neutral element — zero",
				By(infinite, support, cases, real_ring.NeutralAdd))
		}),
})}

// ---------------------------------------------------------------------------
// Changing the index set
// ---------------------------------------------------------------------------
//
// A finite sum can be gathered into the fibres of a map, the fibre totals
// summed over its image or over any set covering it, and a sum over the
// image of a map one to one on the index set is a sum over that set. A
// double sum over two finite sets can be taken in either order.
// Restricting an index set by a test is the same as silencing the summand
// off it.
//
// These laws also combine: a double sum restricted by a relation swaps
// by silencing off the relation first. Counting a finite relation from
// both sides then gives a product when one side is regular.

// Fibres — a map that separates nothing still organises a sum: gather
// the points of `s` that `f` sends to a common place, sum over each such
// fibre, and sum those totals over the places `f` reaches.
//
// The map need not be injective. Finiteness of the index set makes
// both the image and every fibre finite.
var Fibres = fibresThm{family.Add(registry.ProofEntry{
	Name: "Fibres",
	Key:  "prop_bd947295a14116b5",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀f:(A → B). ∀g:(A → real).",
			Hypotheses: []string{
				"finite(s)",
			},
			Conclusion: "sum(s, g) = sum(image(f, s), λy:B. sum({x | x ∈ s ∧ f(x) = y}, g))",
		},
		func(a *Argument) {
			a.Do(Unfold(RealSumDef), By(monoidal.Fibres, real_ring.MonoidalAdd))
		}),
})}

// Regroup — the fibre totals of a finite sum may be summed over any set
// covering the image of the map, not only over the image: a place the map
// does not reach has an empty fibre, whose sum is zero.
var Regroup = regroupThm{family.Add(registry.ProofEntry{
	Name: "Regroup",
	Key:  "prop_aef39104dccd6d56",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀f:(A → B). ∀g:(A → real). ∀t:set(B).",
			Hypotheses: []string{
				"finite(s)",
				"image(f, s) ⊆ t",
			},
			Conclusion: "sum(s, g) = sum(t, λy:B. sum({x | x ∈ s ∧ f(x) = y}, g))",
		},
		func(a *Argument) {
			a.Do(Unfold(RealSumDef), By(monoidal.Regroup.Read(real_ring.MonoidalAdd)))
		}),
})}

// Image — a sum over the image of a map one to one on the index set is
// the sum over the index set itself, of the summand read after the map:
// reindexing a sum changes nothing as long as no two indices land on one
// point.
var Image = imageThm{family.Add(registry.ProofEntry{
	Name: "Image",
	Key:  "prop_5abcfc4a03e56c4e",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀f:(A → B). ∀g:(B → real).",
			Hypotheses: []string{
				"injective_on(s, f)",
			},
			Conclusion: "sum(image(f, s), g) = sum(s, g ∘ f)",
		},
		func(a *Argument) {
			a.Do(Unfold(RealSumDef), By(monoidal.Image, real_ring.MonoidalAdd))
		}),
})}

// Swap — a sum of sums does not care which of its two index sets is
// taken first. Both have to be finite, that being where the recursion
// reaches on either side.
var Swap = swapThm{family.Add(registry.ProofEntry{
	Name: "Swap",
	Key:  "prop_1bce85618a6389d1",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀t:set(B). ∀f:(A → B → real).",
			Hypotheses: []string{
				"finite(s)",
				"finite(t)",
			},
			Conclusion: "sum(s, λi:A. sum(t, f(i))) = sum(t, λj:B. sum(s, λi:A. f(i, j)))",
		},
		func(a *Argument) {
			a.Do(Unfold(RealSumDef), By(monoidal.Swap, real_ring.MonoidalAdd))
		}),
})}

// Restrict — summing over the part of an index set a test accepts is
// summing over the whole of it with the summand silenced where the test
// fails.
var Restrict = restrictThm{family.Add(registry.ProofEntry{
	Name: "Restrict",
	Key:  "prop_6e099906011b72e8",
	Build: family.Theorem(
		"∀s:set(A). ∀P:(A → bool). ∀f:(A → real). "+
			"    sum({x | x ∈ s ∧ P(x)}, f) = sum(s, λx:A. COND(P(x), f(x), &0))",
		func(a *Argument) {
			a.Do(Unfold(RealSumDef), By(monoidal.Restrict, real_ring.MonoidalAdd, real_ring.NeutralAdd))
		}),
})}

// SwapRestricted — `Swap` above for a double sum whose inner index set
// is carved out of a fixed set by a relation on the two indices: the
// same relation carves the other index set on the other side, and the
// two readings agree. Both fixed sets must be finite, as for `Swap`.
//
// Carving by the relation is silencing the summand off it, and that
// is `Restrict` read under the outer binder on each side. Once both
// inner sums run over their whole fixed sets the two are `Swap`'s two
// sides at the silenced summand.
var SwapRestricted = swapRestrictedThm{family.Add(registry.ProofEntry{
	Name: "SwapRestricted",
	Key:  "prop_75c1377e24a1b08d",
	Build: family.Theorem(
		Statement{
			Binders: "∀f:(A → B → real). ∀R:(A → B → bool). ∀s:set(A). ∀t:set(B).",
			Hypotheses: []string{
				"finite(s)",
				"finite(t)",
			},
			Conclusion: "sum(s, λx:A. sum({y:B | y ∈ t ∧ R(x, y)}, λy:B. f(x, y))) = " +
				"sum(t, λy:B. sum({x:A | x ∈ s ∧ R(x, y)}, λx:A. f(x, y)))",
		},
		func(a *Argument, f *Arrow2[A, B, Real], R *Arrow2[A, B, Bool],
			s *Expr[Set[A]], t *Expr[Set[B]], finite Fact) {
			// One copy of Restrict per index type; a Simp rule is read as
			// Restrict states it, the form the comprehensions here are
			// written in.
			a.Do(Simp(Fwd(Restrict.Inst[A]()), Fwd(Restrict.Inst[B]())))
			silenced := a.TermAs[Fun2[A, B, Real]]("λx:A. λy:B. COND(R(x, y), f(x, y), &0)")
			// Normalized: the law's summand is applied to its indices by
			// simplification.
			a.Show(
				"and two sums over fixed finite sets swap",
				By(finite, Swap.At(s, t, silenced)))
		}),
})}

// DoubleCounting — a relation between two finite sets, counted from
// both sides. Summing over s the number of partners each point has in
// t counts the related pairs once each; so does summing over t the
// number of partners each point has in s; and when every point of t
// has exactly k partners, the second count is k taken card(t) times.
//
// Each count of partners is a sum of ones over them (`CardAsSum`,
// the partners being a finite part of a finite set), so the first
// count is a double sum restricted by the relation, and
// `SwapRestricted` above reads it from the other side.
var DoubleCounting = doubleCountingThm{family.Add(registry.ProofEntry{
	Name: "DoubleCounting",
	Key:  "prop_d48731bb3972a79c",
	Build: family.Theorem(
		Statement{
			Binders: "∀R:(A → B → bool). ∀s:set(A). ∀t:set(B). ∀k:num.",
			Hypotheses: []string{
				"finite(s)",
				"finite(t)",
				"∀j:B. j ∈ t ⇒ card({i:A | i ∈ s ∧ R(i, j)}) = k",
			},
			Conclusion: "sum(s, λi:A. &card({j:B | j ∈ t ∧ R(i, j)})) = &(k * card(t))",
		},
		func(a *Argument, R *Arrow2[A, B, Bool], s *Expr[Set[A]], t *Expr[Set[B]],
			k *Expr[Nat], finiteAndRegular Fact) {
			rowCounts := a.Have(
				"any point's count of partners in t is the sum of 1 over those partners",
				"∀i:A. &card({j:B | j ∈ t ∧ R(i, j)}) = sum({j:B | j ∈ t ∧ R(i, j)}, λj:B. &1)",
				Derive(func(b *Argument) {
					b.FixAs[A]("i")
					partners := b.TermAs[Set[B]]("{j:B | j ∈ t ∧ R(i, j)}")
					related := b.TermAs[Set[B]]("λj:B. R(i, j)")
					b.Show(
						"the partners are a finite part of t, and a finite set's size is a sum of ones",
						By(finiteAndRegular, finite_set.FiniteRestrict.At(t, related), CardAsSum.At(partners)))
				}))
			columnCounts := a.Have(
				"over t the same sum of ones counts a point's partners in s, which is k",
				"∀j:B. j ∈ t ⇒ sum({i:A | i ∈ s ∧ R(i, j)}, λi:A. &1) = &k",
				Derive(func(b *Argument) {
					b.FixAs[B]("j")
					inT := b.Assume()
					partners := b.TermAs[Set[A]]("{i:A | i ∈ s ∧ R(i, j)}")
					related := b.TermAs[Set[A]]("λi:A. R(i, j)")
					b.Show(
						"the partners are a finite part of s, k of them by hypothesis",
						By(inT, finiteAndRegular, finite_set.FiniteRestrict.At(s, related), CardAsSum.At(partners)))
				}))

			// Normalized on the closing leg: the two laws read at the leg's
			// own point ARE the leg.
			ones := a.TermAs[Fun2[A, B, Real]]("λi:A. λj:B. &1")
			a.Do(CalcEq(
				Leg(
					a.Term("sum(s, λi:A. sum({j:B | j ∈ t ∧ R(i, j)}, λj:B. &1))"),
					"count each point's partners in t as a sum of ones",
					By(rowCounts, Congruence)),
				Leg(
					a.Term("sum(t, λj:B. sum({i:A | i ∈ s ∧ R(i, j)}, λi:A. &1))"),
					"the related pairs, counted from the side of t instead",
					By(finiteAndRegular, SwapRestricted.At(ones, R, s, t))),
				Leg(
					a.Term("sum(t, λj:B. &k)"),
					"where every point has k partners",
					By(columnCounts, Congruence)),
				Leg(
					a.Term("&(card(t)) * &k"),
					"a constant summand, once per point of t",
					By(finiteAndRegular, Const)),
				FinalLeg(
					"and the product reads back into ℕ, in the order the statement has it",
					By(Normalized, real_construction.OfNumMul, nat_arith.MulSym)),
			))
		}),
})}
