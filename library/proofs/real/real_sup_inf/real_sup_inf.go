// real_sup_inf.go — the chapter: sup and inf, and what pins them down.
//
// Five parts, marked by banners:
//
// - Max and min as a lattice on ℝ
// - ℕ's lattice transports along `&`
// - What sup and inf ARE
// - The comparison calculus: how sup and inf are used
// - The estimates: how sup and inf are APPROXIMATED

package real_sup_inf

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_completeness"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Max and min as a lattice on ℝ
// ---------------------------------------------------------------------------
//
// max and min as a lattice on ℝ: the bounds they satisfy unconditionally,
// the four equivalences that characterize them, the strict twins of the
// two min characterizations, and the pair that says which argument each
// operation becomes.
//
// Both operations are case definitions testing the same comparison —
// `max x y = COND(x ≤ y, y, x)` and `min x y = COND(x ≤ y, x, y)` — so
// every proof here is one argument, the operands exchanged between
// mirrors. Split on that guard; unfolding then replaces the operation
// by one of its two arguments, and what is left is order reasoning
// with no case definition in it. The failed guard is read as the
// reverse comparison through totality, which is the only place `¬`
// appears in the wing.
//
// The two groups differ in what the branches need. The bounds are
// closed by reflexivity, because after unfolding one side of each
// conjunct is the branch's own comparison. The equivalences are closed
// by transitivity, because the operation was replaced by ONE of its
// arguments and the claim still speaks about both: the guard is what
// carries a comparison from the argument that survived to the one that
// did not. For the strict twins that carrier is a mixed law — a strict
// comparison composed with the guard's weak one stays strict — and there
// are two of them, one per order: LessThanMin takes the strict step first
// (real_order_ring.LessThanLessEqTrans), MinLessThan the weak one
// (real_order_ring.LessEqLessThanTrans). The strict forms are stated for
// min only, because a radius is the smaller of two: nothing in the corpus
// compares strictly against a max.

// MaxUpperBound — the max of two reals is an upper bound for both.
// Together with MaxLessEq (which says nothing smaller is) this is the
// whole of "max is the least upper bound of a pair".
var MaxUpperBound = maxUpperBoundThm{family.Add(registry.ProofEntry{
	Name: "MaxUpperBound",
	Key:  "prop_3fc923ea92dbe358",
	Build: family.Theorem("∀x y:real. x ≤ max(x, y) ∧ y ≤ max(x, y)", func(a *Argument, x, y Term) {
		v := ops(a.Ctx())
		a.Cases(v.Guard(x, y))
		// Whichever argument the max becomes is reflexively below
		// itself; the OTHER bound is where the two branches differ.
		// When the guard holds it states that bound outright, so the
		// true branch closes on the guard and bare reflexivity. When
		// the guard fails it states nothing, only denies, so that
		// branch owes both bounds and has to turn the denial into a
		// comparison first.
		a.When(
			"x ≤ y, so the max is y and the bound on x is the guard itself",
			func(b *Argument, guard Fact) {
				b.Show(
					"x is below y by the guard, and y is below itself",
					Unfold(RealMaxDef),
					By(guard, real_order_ring.LessEqRefl))
			})
		a.Otherwise(
			"y is below x, so the max is x and the bound on y is the guard read backwards",
			func(b *Argument, guardFailed Fact) {
				b.Do(Unfold(RealMaxDef))
				b.Show(
					"x bounds itself and, since one of the two comparisons must hold, bounds y too",
					By(guardFailed, At(real_order_ring.LessEqRefl, x), At(real_construction.LessEqTotal, x, y)))
			})
	}),
})}

// MinLowerBound — the mirror: the min of two reals is a lower bound
// for both.
var MinLowerBound = minLowerBoundThm{family.Add(registry.ProofEntry{
	Name: "MinLowerBound",
	Key:  "prop_89664cdddb8c1e7d",
	Build: family.Theorem("∀x y:real. min(x, y) ≤ x ∧ min(x, y) ≤ y", func(a *Argument, x, y Term) {
		v := ops(a.Ctx())
		a.Cases(v.Guard(x, y))
		a.When(
			"x ≤ y, so the min is x and the bound below y is the guard itself",
			func(b *Argument, guard Fact) {
				b.Show(
					"x is below itself, and below y by the guard",
					Unfold(RealMinDef),
					By(guard, real_order_ring.LessEqRefl))
			})
		a.Otherwise(
			"y is below x, so the min is y and the bound below x is the guard read backwards",
			func(b *Argument, guardFailed Fact) {
				b.Do(Unfold(RealMinDef))
				b.Show(
					"y sits below itself and, since one of the two comparisons must hold, below x too",
					By(guardFailed, At(real_order_ring.LessEqRefl, y), At(real_construction.LessEqTotal, x, y)))
			})
	}),
})}

// MaxLessEq — a bound above the max is exactly a bound above both.
// This is the characterizing property: it says max is the LEAST of the
// common upper bounds, and it is the form every later use takes, since
// it turns one comparison against a compound term into two against
// atoms.
var MaxLessEq = maxLessEqThm{family.Add(registry.ProofEntry{
	Name: "MaxLessEq",
	Key:  "prop_6325228b8b661800",
	Build: family.Theorem("∀x y z:real. max(x, y) ≤ z ⇔ x ≤ z ∧ y ≤ z", func(
		a *Argument,
		x, y, z Term,
	) {
		v := ops(a.Ctx())
		a.Cases(v.Guard(x, y))
		// In each branch the max is one argument, so one half of the
		// conjunction is the goal verbatim; transitivity is what
		// supplies the other half, routing through the guard.
		a.When(
			"x ≤ y, so the max is y: a bound above y is above x through the guard",
			func(b *Argument, guard Fact) {
				b.Do(Unfold(RealMaxDef))
				b.Show(
					"x reaches z by way of y",
					By(guard, At(real_construction.LessEqTrans, x, y, z)))
			})
		a.Otherwise(
			"y is below x, so the max is x: a bound above x is above y through the reversed guard",
			func(b *Argument, guardFailed Fact) {
				b.Do(Unfold(RealMaxDef))
				b.Show(
					"y reaches z by way of x",
					By(
						guardFailed,
						At(real_construction.LessEqTotal, x, y),
						At(real_construction.LessEqTrans, y, x, z)))
			})
	}),
})}

// LessEqMin — the mirror characterization: a bound below the min is
// exactly a bound below both, so min is the GREATEST of the common
// lower bounds.
var LessEqMin = lessEqMinThm{family.Add(registry.ProofEntry{
	Name: "LessEqMin",
	Key:  "prop_4ff1010fcdba0a3c",
	Build: family.Theorem("∀x y z:real. z ≤ min(x, y) ⇔ z ≤ x ∧ z ≤ y", func(
		a *Argument,
		x, y, z Term,
	) {
		v := ops(a.Ctx())
		a.Cases(v.Guard(x, y))
		a.When(
			"x ≤ y, so the min is x: a bound below x is below y through the guard",
			func(b *Argument, guard Fact) {
				b.Do(Unfold(RealMinDef))
				b.Show(
					"z reaches y by way of x",
					By(guard, At(real_construction.LessEqTrans, z, x, y)))
			})
		a.Otherwise(
			"y is below x, so the min is y: a bound below y is below x through the reversed guard",
			func(b *Argument, guardFailed Fact) {
				b.Do(Unfold(RealMinDef))
				b.Show(
					"z reaches x by way of y",
					By(
						guardFailed,
						At(real_construction.LessEqTotal, x, y),
						At(real_construction.LessEqTrans, z, y, x)))
			})
	}),
})}

// LessThanMin — the strict form of LessEqMin: strictly below the min is
// exactly strictly below both. The carrier is the mixed law with the
// strict step first.
var LessThanMin = lessThanMinThm{family.Add(registry.ProofEntry{
	Name: "LessThanMin",
	Key:  "prop_8467939bdfcf4774",
	Build: family.Theorem("∀x y z:real. z < min(x, y) ⇔ z < x ∧ z < y", func(
		a *Argument,
		x, y, z Term,
	) {
		v := ops(a.Ctx())
		a.Cases(v.Guard(x, y))
		a.When(
			"x ≤ y, so the min is x: strictly below x is strictly below y through the guard",
			func(b *Argument, guard Fact) {
				b.Do(Unfold(RealMinDef))
				b.Show(
					"z stays strictly under y by way of x",
					By(guard, At(real_order_ring.LessThanLessEqTrans, z, x, y)))
			})
		a.Otherwise(
			"y is below x, so the min is y: strictly below y is strictly below x through the reversed guard",
			func(b *Argument, guardFailed Fact) {
				b.Do(Unfold(RealMinDef))
				b.Show(
					"z stays strictly under x by way of y",
					By(
						guardFailed,
						At(real_construction.LessEqTotal, x, y),
						At(real_order_ring.LessThanLessEqTrans, z, y, x)))
			})
	}),
})}

// MaxLessThan — the strict form of MaxLessEq, and the mirror of
// LessThanMin: the max is strictly under a value exactly when both are.
// The carrier is the mixed law with the weak step first.
var MaxLessThan = maxLessThanThm{family.Add(registry.ProofEntry{
	Name: "MaxLessThan",
	Key:  "prop_eba0fa53ae27f29",
	Build: family.Theorem("∀x y z:real. max(x, y) < z ⇔ x < z ∧ y < z", func(
		a *Argument,
		x, y, z Term,
	) {
		v := ops(a.Ctx())
		a.Cases(v.Guard(x, y))
		a.When(
			"x ≤ y, so the max is y: strictly under z by way of y, x is strictly under z through the guard",
			func(b *Argument, guard Fact) {
				b.Do(Unfold(RealMaxDef))
				b.Show(
					"x stays strictly under z by way of y",
					By(guard, At(real_order_ring.LessEqLessThanTrans, x, y, z)))
			})
		a.Otherwise(
			"y is below x, so the max is x: strictly under z by way "+
				"of x, y is strictly under z through the reversed guard",
			func(b *Argument, guardFailed Fact) {
				b.Do(Unfold(RealMaxDef))
				b.Show(
					"y stays strictly under z by way of x",
					By(
						guardFailed,
						At(real_construction.LessEqTotal, x, y),
						At(real_order_ring.LessEqLessThanTrans, y, x, z)))
			})
	}),
})}

// LessEqMax — reaching the max means reaching one of the two. Where
// MaxLessEq bounds the max from above and conjoins, this bounds it
// from below and disjoins: the max is attained by an argument, so
// anything under it is under that argument.
var LessEqMax = lessEqMaxThm{family.Add(registry.ProofEntry{
	Name: "LessEqMax",
	Key:  "prop_219dc63a00fd1efa",
	Build: family.Theorem("∀x y z:real. z ≤ max(x, y) ⇔ z ≤ x ∨ z ≤ y", func(
		a *Argument,
		x, y, z Term,
	) {
		v := ops(a.Ctx())
		a.Cases(v.Guard(x, y))
		// The disjunct naming the surviving argument is the goal
		// verbatim; transitivity is what discharges the OTHER
		// disjunct, which would otherwise claim nothing about the
		// term the max became.
		a.When(
			"x ≤ y, so the max is y: reaching x already reaches y through the guard",
			func(b *Argument, guard Fact) {
				b.Do(Unfold(RealMaxDef))
				b.Show(
					"z reaches y by way of x",
					By(guard, At(real_construction.LessEqTrans, z, x, y)))
			})
		a.Otherwise(
			"y is below x, so the max is x: reaching y already reaches x through the reversed guard",
			func(b *Argument, guardFailed Fact) {
				b.Do(Unfold(RealMaxDef))
				b.Show(
					"z reaches x by way of y",
					By(
						guardFailed,
						At(real_construction.LessEqTotal, x, y),
						At(real_construction.LessEqTrans, z, y, x)))
			})
	}),
})}

// MinLessEq — the mirror: the min is under a value exactly when one of
// the two is.
var MinLessEq = minLessEqThm{family.Add(registry.ProofEntry{
	Name: "MinLessEq",
	Key:  "prop_47f7fb88a687eb8c",
	Build: family.Theorem("∀x y z:real. min(x, y) ≤ z ⇔ x ≤ z ∨ y ≤ z", func(
		a *Argument,
		x, y, z Term,
	) {
		v := ops(a.Ctx())
		a.Cases(v.Guard(x, y))
		a.When(
			"x ≤ y, so the min is x: a value above y is above x through the guard",
			func(b *Argument, guard Fact) {
				b.Do(Unfold(RealMinDef))
				b.Show(
					"x reaches z by way of y",
					By(guard, At(real_construction.LessEqTrans, x, y, z)))
			})
		a.Otherwise(
			"y is below x, so the min is y: a value above x is above y through the reversed guard",
			func(b *Argument, guardFailed Fact) {
				b.Do(Unfold(RealMinDef))
				b.Show(
					"y reaches z by way of x",
					By(
						guardFailed,
						At(real_construction.LessEqTotal, x, y),
						At(real_construction.LessEqTrans, y, x, z)))
			})
	}),
})}

// MinLessThan — the strict form of MinLessEq: the min is strictly under
// a value exactly when one of the two is. The carrier is the mixed law
// with the weak step first: the comparison travels from the argument
// the min did not become to the one it did.
var MinLessThan = minLessThanThm{family.Add(registry.ProofEntry{
	Name: "MinLessThan",
	Key:  "prop_d7a7d724fbb57b23",
	Build: family.Theorem("∀x y z:real. min(x, y) < z ⇔ x < z ∨ y < z", func(
		a *Argument,
		x, y, z Term,
	) {
		v := ops(a.Ctx())
		a.Cases(v.Guard(x, y))
		a.When(
			"x ≤ y, so the min is x: a value strictly above y is strictly above x through the guard",
			func(b *Argument, guard Fact) {
				b.Do(Unfold(RealMinDef))
				b.Show(
					"x stays strictly under z by way of y",
					By(guard, At(real_order_ring.LessEqLessThanTrans, x, y, z)))
			})
		a.Otherwise(
			"y is below x, so the min is y: a value strictly "+
				"above x is strictly above y through the reversed guard",
			func(b *Argument, guardFailed Fact) {
				b.Do(Unfold(RealMinDef))
				b.Show(
					"y stays strictly under z by way of x",
					By(
						guardFailed,
						At(real_construction.LessEqTotal, x, y),
						At(real_order_ring.LessEqLessThanTrans, y, x, z)))
			})
	}),
})}

// ---------------------------------------------------------------------
// Which argument the operation becomes — the guard split on its own.
// ---------------------------------------------------------------------

// MaxIsArgument — the max is one of the two values it is taken over.
// It is the guard split with nothing built on top: each branch unfolds
// the max to the answer its own comparison selects, so the proof
// consults no order law at all, not even reflexivity.
//
// The equivalences above state the lattice through comparisons only,
// never that the operation returns an argument. The members that
// COMPUTE with max need exactly this and nothing else about it: an
// insertion or a two-point set has to know which point the max is
// before attainment can pin the supremum.
var MaxIsArgument = maxIsArgumentThm{family.Add(registry.ProofEntry{
	Name: "MaxIsArgument",
	Key:  "prop_4b692a8d0cb47183",
	Build: family.Theorem("∀x y:real. max(x, y) = x ∨ max(x, y) = y", func(a *Argument, x, y Term) {
		v := ops(a.Ctx())
		a.Cases(v.Guard(x, y))
		a.When(
			"x ≤ y, so the max is y",
			func(b *Argument, guard Fact) {
				isY := b.Have(
					"the comparison holds, so the conditional selects y",
					"max(x, y) = y",
					Unfold(RealMaxDef),
					By(guard))
				b.Show(
					"which is one of the two arguments",
					By(isY))
			})
		a.Otherwise(
			"y is below x, so the max is x",
			func(b *Argument, guardFailed Fact) {
				isX := b.Have(
					"the comparison fails, so the conditional selects x",
					"max(x, y) = x",
					Unfold(RealMaxDef),
					By(guardFailed))
				b.Show(
					"which is one of the two arguments",
					By(isX))
			})
	}),
})}

// MinIsArgument — the mirror: the min is one of its two arguments, by
// the same split and with the branches exchanged.
var MinIsArgument = minIsArgumentThm{family.Add(registry.ProofEntry{
	Name: "MinIsArgument",
	Key:  "prop_53d130be32896d3a",
	Build: family.Theorem("∀x y:real. min(x, y) = x ∨ min(x, y) = y", func(a *Argument, x, y Term) {
		v := ops(a.Ctx())
		a.Cases(v.Guard(x, y))
		a.When(
			"x ≤ y, so the min is x",
			func(b *Argument, guard Fact) {
				isX := b.Have(
					"the comparison holds, so the conditional selects x",
					"min(x, y) = x",
					Unfold(RealMinDef),
					By(guard))
				b.Show(
					"which is one of the two arguments",
					By(isX))
			})
		a.Otherwise(
			"y is below x, so the min is y",
			func(b *Argument, guardFailed Fact) {
				isY := b.Have(
					"the comparison fails, so the conditional selects y",
					"min(x, y) = y",
					Unfold(RealMinDef),
					By(guardFailed))
				b.Show(
					"which is one of the two arguments",
					By(isY))
			})
	}),
})}

// ClampRange — clamping x to ⟦a, b⟧, max(a, min(b, x)), lands in ⟦a, b⟧
// and leaves a point of ⟦a, b⟧ where it is: with max and min read as the
// comparisons that define them, this is order alone.
var ClampRange = clampRangeThm{family.Add(registry.ProofEntry{
	Name: "ClampRange",
	Key:  "prop_65c0eae826ba8517",
	Build: family.Theorem(Statement{
		Binders: "∀a b x:real.",
		Hypotheses: []string{
			"a ≤ b",
		},
		Conclusion: "a ≤ max(a, min(b, x)) ∧ " +
			"max(a, min(b, x)) ≤ b ∧ " +
			"(a ≤ x ∧ x ≤ b ⇒ max(a, min(b, x)) = x)",
	},
		func(arg *Argument, a, b, x *Expr[Real], ordered Fact) {
			arg.Show(
				"max(a, min(b, x)) lies in [a, b] and is x when x does",
				ByArith(ordered),
			)
		}),
})}

// ClampEnds — clamping x to ⟦a, b⟧ sends a point at or below a to a and a
// point at or above b to b. At or below a, x is below b too, so the min
// leaves x and the max takes a; at or above b, the min takes b, which the
// max keeps, b being at least a. As for ClampRange above, this is order
// alone.
var ClampEnds = clampEndsThm{family.Add(registry.ProofEntry{
	Name: "ClampEnds",
	Key:  "prop_2be498a60c7750b5",
	Build: family.Theorem(Statement{
		Binders: "∀a b x:real.",
		Hypotheses: []string{
			"a ≤ b",
		},
		Conclusion: "(x ≤ a ⇒ max(a, min(b, x)) = a) ∧ (b ≤ x ⇒ max(a, min(b, x)) = b)",
	},
		func(arg *Argument, a, b, x *Expr[Real], ordered Fact) {
			arg.Show(
				"max(a, min(b, x)) is a at or below a, and b at or above b",
				ByArith(ordered),
			)
		}),
})}

// ClampNonexpansive — clamping to ⟦a, b⟧ moves no two points further
// apart: min(b, ·) does not, and neither does max(a, ·) after it.
var ClampNonexpansive = clampNonexpansiveThm{family.Add(registry.ProofEntry{
	Name: "ClampNonexpansive",
	Key:  "prop_7fbca9ee1b24e636",
	Build: family.Theorem("∀a b x y:real. |max(a, min(b, x)) - max(a, min(b, y))| ≤ |x - y|",
		func(arg *Argument, a, b, x, y *Expr[Real]) {
			inner := arg.Have(
				"min(b, ·) moves its argument's differences by no more",
				"|min(b, x) - min(b, y)| ≤ |x - y|",
				ByArith(
					RealMinDef.At(b, x),
					RealMinDef.At(b, y),
					real_sgn_abs.AbsBounds.At(arg.TermAs[Real]("min(b, x) - min(b, y)"), arg.TermAs[Real]("|x - y|")),
					real_sgn_abs.AbsBounds.At(arg.TermAs[Real]("x - y"), arg.TermAs[Real]("|x - y|"))),
			)
			outer := arg.Have(
				"and neither does max(a, ·)",
				"|max(a, min(b, x)) - max(a, min(b, y))| ≤ |min(b, x) - min(b, y)|",
				ByArith(
					RealMaxDef.At(a, arg.TermAs[Real]("min(b, x)")),
					RealMaxDef.At(a, arg.TermAs[Real]("min(b, y)")),
					real_sgn_abs.AbsBounds.At(
						arg.TermAs[Real]("max(a, min(b, x)) - max(a, min(b, y))"),
						arg.TermAs[Real]("|min(b, x) - min(b, y)|")),
					real_sgn_abs.AbsBounds.At(
						arg.TermAs[Real]("min(b, x) - min(b, y)"), arg.TermAs[Real]("|min(b, x) - min(b, y)|"))),
			)
			arg.Show(
				"so clamping to [a, b] moves no two points further apart",
				By(
					inner,
					outer,
					real_construction.LessEqTrans.At(
						arg.TermAs[Real]("|max(a, min(b, x)) - max(a, min(b, y))|"),
						arg.TermAs[Real]("|min(b, x) - min(b, y)|"),
						arg.TermAs[Real]("|x - y|"))),
			)
		}),
})}

// ---------------------------------------------------------------------------
// ℕ's lattice transports along `&`
// ---------------------------------------------------------------------------
//
// `nat_max` and `nat_min` on ℕ are the same case definitions as `max` and `min`
// on ℝ, testing the same comparison one type down. So the transport is
// not a computation but an observation about the embedding: `&` carries
// `m ≤ n` to `&m ≤ &n` in both directions, which means the two
// definitions take the SAME branch, and the two sides of each statement
// are then literally the same embedded number.
//
// Both proofs are that sentence: split on ℕ's comparison, unfold both
// definitions, and hand the closer the branch's ℕ comparison together
// with the equivalence that turns it into ℝ's. Only ℕ's COND collapses
// on the split — ℝ's is guarded by the embedded comparison, and
// supplying that is the whole of what the equivalence is for. Nothing
// about max or min is used beyond their being defined by the same
// test.

// OfNumMax — embedding a ℕ-max gives the ℝ-max of the embeddings.
var OfNumMax = ofNumMaxThm{family.Add(registry.ProofEntry{
	Name: "OfNumMax",
	Key:  "prop_80ab62de1ace329d",
	Build: family.Theorem("∀m n:num. &max(m, n) = max(&m, &n)", func(a *Argument, m, n Term) {
		v := ops(a.Ctx())
		a.Cases(v.NumGuard(m, n))
		// Each branch unfolds both definitions. The ℕ one collapses
		// against the branch's own hypothesis; the ℝ one is still
		// guarded by `&m ≤ &n`, and that is exactly what the
		// embedding's order equivalence supplies.
		a.When(
			"m ≤ n, so both maxima take their second argument",
			func(b *Argument, guard Fact) {
				b.Do(Unfold(nat_order.NatMaxDef))
				b.Do(Unfold(RealMaxDef))
				b.Show(
					"the ℝ guard holds because the ℕ one does",
					By(guard, real_construction.OfNumLessEq))
			})
		a.Otherwise(
			"n is below m, so both maxima take their first argument",
			func(b *Argument, guardFailed Fact) {
				b.Do(Unfold(nat_order.NatMaxDef))
				b.Do(Unfold(RealMaxDef))
				b.Show(
					"the ℝ guard fails because the ℕ one does",
					By(guardFailed, real_construction.OfNumLessEq))
			})
	}),
})}

// OfNumMin — the mirror: embedding a ℕ-min gives the ℝ-min of the
// embeddings.
var OfNumMin = ofNumMinThm{family.Add(registry.ProofEntry{
	Name: "OfNumMin",
	Key:  "prop_ce07750e3cd04366",
	Build: family.Theorem("∀m n:num. &min(m, n) = min(&m, &n)", func(a *Argument, m, n Term) {
		v := ops(a.Ctx())
		a.Cases(v.NumGuard(m, n))
		a.When(
			"m ≤ n, so both minima take their first argument",
			func(b *Argument, guard Fact) {
				b.Do(Unfold(nat_order.NatMinDef))
				b.Do(Unfold(RealMinDef))
				b.Show(
					"the ℝ guard holds because the ℕ one does",
					By(guard, real_construction.OfNumLessEq))
			})
		a.Otherwise(
			"n is below m, so both minima take their second argument",
			func(b *Argument, guardFailed Fact) {
				b.Do(Unfold(nat_order.NatMinDef))
				b.Do(Unfold(RealMinDef))
				b.Show(
					"the ℝ guard fails because the ℕ one does",
					By(guardFailed, real_construction.OfNumLessEq))
			})
	}),
})}

// ---------------------------------------------------------------------------
// What sup and inf ARE
// ---------------------------------------------------------------------------
//
// Five statements per operator, mirrored: the value is determined by the
// bounds alone (SameBounds), it exists and is extremal for every nonempty
// bounded set (the lub/glb theorems), and then three ways to PIN it — by
// any value the set approaches (UniqueApproach), by any bound the set
// ATTAINS (UniqueAttained, the degenerate case of that first, where the
// approaching values may be dispensed with because the pin lies in the set
// itself), and by the bounds themselves (UniqueLeastBound, where the pin's
// upper set IS the set of upper bounds). The last is also the shape
// movement 7's `real_has_sup` relation is defined to have, so the relational
// wing enters through it.
//
// Both operators are ε-chosen, and the chapter's whole ε-discipline is
// visible here and nowhere else: a member first proves the
// characterization is SATISFIABLE — `∃a. Φ(a)` — and unfolding the
// definition then hands the same property to the chosen value, the
// engine consuming the choice axiom inside the unfold. No selection
// law is ever cited. UNCONDITIONAL existence has one source,
// completeness (`tower/real_completeness.RealComplete`): grounded at the
// membership predicate for sup, and for inf by the classical turn —
// the infimum of s is the supremum of the set of lower bounds of s,
// so the same theorem serves both operators, grounded the second time
// at the lower-bound predicate. (The UniqueApproach pair needs no
// completeness: there the pin b itself witnesses the existence.)
//
// The SameBounds pair needs none of that: with the bounds hypothesis
// resident, the two ε-descriptions are pointwise equal, so the values
// agree without either being computed.

// SupSameUpperBounds — two sets with the same upper bounds have the
// same supremum. This is extensionality one level up: sup never looks
// at the members, only at the bounds, so agreement there is all it
// can ever see.
var SupSameUpperBounds = supSameUpperBoundsThm{family.Add(registry.ProofEntry{
	Name: "SupSameUpperBounds",
	Key:  "prop_d153c34965e155ec",
	Build: family.Theorem(Statement{
		Binders: "∀s t:set(real).",
		Hypotheses: []string{
			"∀b:real. (∀x:real. x ∈ s ⇒ x ≤ b) ⇔ ∀x:real. x ∈ t ⇒ x ≤ b",
		},
		Conclusion: "sup(s) = sup(t)",
	},
		func(a *Argument, s, t Term, sameBounds Fact) {
			a.Do(Unfold(RealSupDef))
			a.Show(
				"the two ε-descriptions are pointwise equal under the hypothesis",
				By(sameBounds))
		}),
})}

// InfSameLowerBounds — the mirror: two sets with the same lower
// bounds have the same infimum.
var InfSameLowerBounds = infSameLowerBoundsThm{family.Add(registry.ProofEntry{
	Name: "InfSameLowerBounds",
	Key:  "prop_96dcd151adc785cd",
	Build: family.Theorem(Statement{
		Binders: "∀s t:set(real).",
		Hypotheses: []string{
			"∀a:real. (∀x:real. x ∈ s ⇒ a ≤ x) ⇔ ∀x:real. x ∈ t ⇒ a ≤ x",
		},
		Conclusion: "inf(s) = inf(t)",
	},
		func(a *Argument, s, t Term, sameBounds Fact) {
			a.Do(Unfold(RealInfDef))
			a.Show(
				"the two ε-descriptions are pointwise equal under the hypothesis",
				By(sameBounds))
		}),
})}

// SupLeastUpperBound — for a nonempty bounded set, sup s is an upper
// bound below every upper bound. This is where completeness enters
// the chapter, and the only work is bridging its surface: the axiom
// speaks a PREDICATE (`P(x)`), the chapter speaks MEMBERSHIP
// (`x ∈ s`), and Normalize does not identify the two — so the axiom
// is grounded at the membership predicate itself, `λx. x ∈ s`, and
// the ∈-form instance is what meets the hypothesis.
var SupLeastUpperBound = supLeastUpperBoundThm{family.Add(registry.ProofEntry{
	Name: "SupLeastUpperBound",
	Key:  "prop_ef2f941d6b2d5fe9",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(real).",
		Hypotheses: []string{
			"s ≠ ∅",
			"∃b:real. ∀x:real. x ∈ s ⇒ x ≤ b",
		},
		Conclusion: "(∀x:real. x ∈ s ⇒ x ≤ sup(s)) ∧ (∀b:real. (∀x:real. x ∈ s ⇒ x ≤ b) ⇒ sup(s) ≤ b)",
	},
		func(a *Argument, s Term, nonemptyBounded Fact) {
			ctx := a.Ctx()
			v := ops(ctx)
			x := ctx.Var("x", MakeType("real"))
			memberOf := x.To(v.In(x, s)) // λx. x ∈ s

			// The completeness axiom speaks an abstract predicate, and its
			// NORMALIZED surface buries that binder below two Skolem
			// slots — so the typed install cannot be grounded here. The
			// raw surface is the natural ∀P form, and one witness at the
			// membership λ is the whole bridge: the grounded raw cert
			// goes straight into the premise list, so nothing of the
			// axiom's statement is copied into this file.
			a.Have(
				"a least upper bound exists — completeness at the membership predicate",
				"∃a:real. (∀x:real. x ∈ s ⇒ x ≤ a) ∧ (∀b:real. (∀x:real. x ∈ s ⇒ x ≤ b) ⇒ a ≤ b)",
				By(
					At(real_completeness.RealComplete, memberOf),
					nonemptyBounded,
					set_basic.MemberNotEmpty.Inst[Real]()))
			// The existence above is consumed ambiently here: the unfold takes
			// the choice axiom against it, so it needs no premise slot.
			a.Show(
				"the chosen value inherits the property",
				Unfold(RealSupDef))
		}),
})}

// InfGreatestLowerBound — the mirror, by the classical construction:
// the infimum of s is the supremum of s's lower bounds. The set of
// lower bounds is nonempty (s is bounded below) and bounded above (by
// any member of s), so completeness applies to IT — and its least
// upper bound is s's greatest lower one: below every member because
// each member caps the lower bounds, above every lower bound because
// it caps them least.
var InfGreatestLowerBound = infGreatestLowerBoundThm{family.Add(registry.ProofEntry{
	Name: "InfGreatestLowerBound",
	Key:  "prop_f79b9aadde874993",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(real).",
		Hypotheses: []string{
			"s ≠ ∅",
			"∃b:real. ∀x:real. x ∈ s ⇒ b ≤ x",
		},
		Conclusion: "(∀x:real. x ∈ s ⇒ inf(s) ≤ x) ∧ (∀b:real. (∀x:real. x ∈ s ⇒ b ≤ x) ⇒ b ≤ inf(s))",
	},
		func(a *Argument, s Term, nonemptyBounded Fact) {
			ctx := a.Ctx()
			ctx.Var("b", MakeType("real"))
			ctx.Var("x", MakeType("real"))

			bounds := a.Have(
				"the lower bounds are nonempty and bounded above — "+
					"s is bounded below, and any member of s caps them",
				"(∃b:real. ∀x:real. x ∈ s ⇒ b ≤ x) ∧ (∃M:real. ∀c:real. (∀x:real. x ∈ s ⇒ c ≤ x) ⇒ c ≤ M)",
				By(nonemptyBounded, At(set_basic.MemberNotEmpty.Inst[Real](), s)))
			lub := a.Have(
				"so the lower bounds have a least upper bound",
				"∃M:real. "+
					"    (∀c:real. (∀x:real. x ∈ s ⇒ c ≤ x) ⇒ c ≤ M) ∧ "+
					"    (∀M':real. (∀c:real. (∀x:real. x ∈ s ⇒ c ≤ x) ⇒ c ≤ M') ⇒ M ≤ M')",
				By(bounds, ctx.Dep(real_completeness.RealComplete)))
			a.Have(
				"that value is s's greatest lower bound — under every member, over every lower bound",
				"∃a:real. (∀x:real. x ∈ s ⇒ a ≤ x) ∧ (∀c:real. (∀x:real. x ∈ s ⇒ c ≤ x) ⇒ c ≤ a)",
				By(lub))
			// The existence above is consumed ambiently here: the unfold takes
			// the choice axiom against it, so it needs no premise slot.
			a.Show(
				"the chosen value inherits the property",
				Unfold(RealInfDef))
		}),
})}

// SupUniqueApproach — a bound the set approaches from below IS the
// supremum: if b bounds s and every value under b is exceeded within
// s, then sup s = b. This is how a supremum is exhibited in practice —
// name the candidate, show nothing smaller survives.
var SupUniqueApproach = supUniqueApproachThm{family.Add(registry.ProofEntry{
	Name: "SupUniqueApproach",
	Key:  "prop_f951270b66663dea",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(real). ∀b:real.",
		Hypotheses: []string{
			"∀x:real. x ∈ s ⇒ x ≤ b",
			"∀b':real. b' < b ⇒ ∃x:real. x ∈ s ∧ b' < x",
		},
		Conclusion: "sup(s) = b",
	},
		func(a *Argument, s, b Term, pin Fact) {
			v := ops(a.Ctx())

			pinned := a.Have(
				"b bounds s, and any bound c is at or above it — "+
					"were c < b, the approach would put a member above c",
				"(∀x:real. x ∈ s ⇒ x ≤ b) ∧ (∀c:real. (∀x:real. x ∈ s ⇒ x ≤ c) ⇒ b ≤ c)",
				By(pin, real_order_ring.NotLessThan))
			a.Have(
				"so a least upper bound exists",
				"∃a:real. (∀x:real. x ∈ s ⇒ x ≤ a) ∧ (∀c:real. (∀x:real. x ∈ s ⇒ x ≤ c) ⇒ a ≤ c)",
				By(pinned))
			chosen := a.Have(
				"the chosen value satisfies it too — the unfold consumes the choice axiom",
				"(∀x:real. x ∈ s ⇒ x ≤ sup(s)) ∧ (∀c:real. (∀x:real. x ∈ s ⇒ x ≤ c) ⇒ sup(s) ≤ c)",
				Unfold(RealSupDef))
			a.Show(
				"two least upper bounds are equal — each is a bound the other minimally caps",
				By(pinned, chosen, At(real_construction.LessEqAntisym, v.RealSup.Apply(s), b)))
		}),
})}

// InfUniqueApproach — the mirror: a lower bound the set approaches
// from above is the infimum.
var InfUniqueApproach = infUniqueApproachThm{family.Add(registry.ProofEntry{
	Name: "InfUniqueApproach",
	Key:  "prop_9c6e92a85f4554c6",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(real). ∀b:real.",
		Hypotheses: []string{
			"∀x:real. x ∈ s ⇒ b ≤ x",
			"∀b':real. b < b' ⇒ ∃x:real. x ∈ s ∧ x < b'",
		},
		Conclusion: "inf(s) = b",
	},
		func(a *Argument, s, b Term, pin Fact) {
			v := ops(a.Ctx())

			pinned := a.Have(
				"b lies below s, and any lower bound c is at or below "+
					"it — were b < c, the approach would put a member under c",
				"(∀x:real. x ∈ s ⇒ b ≤ x) ∧ (∀c:real. (∀x:real. x ∈ s ⇒ c ≤ x) ⇒ c ≤ b)",
				By(pin, real_order_ring.NotLessThan))
			a.Have(
				"so a greatest lower bound exists",
				"∃a:real. (∀x:real. x ∈ s ⇒ a ≤ x) ∧ (∀c:real. (∀x:real. x ∈ s ⇒ c ≤ x) ⇒ c ≤ a)",
				By(pinned))
			chosen := a.Have(
				"the chosen value satisfies it too — the unfold consumes the choice axiom",
				"(∀x:real. x ∈ s ⇒ inf(s) ≤ x) ∧ (∀c:real. (∀x:real. x ∈ s ⇒ c ≤ x) ⇒ c ≤ inf(s))",
				Unfold(RealInfDef))
			a.Show(
				"two greatest lower bounds are equal — each is a bound the other maximally caps",
				By(pinned, chosen, At(real_construction.LessEqAntisym, v.RealInf.Apply(s), b)))
		}),
})}

// SupUniqueAttained — a bound the set CONTAINS is the supremum. This is
// `SupUniqueApproach` with its second hypothesis discharged rather than
// assumed: a value under b is exceeded within s by b itself, b being a
// member, so the approach clause costs nothing wherever the bound is
// attained. What is left is a bound that is also a member, which is to
// say a greatest element.
//
// It carries no finiteness and no nonemptiness hypothesis — `b ∈ s`
// supplies the latter — so it is a statement about attainment and not
// about finite sets, and it is the form every later exhibition of a
// supremum uses: name the greatest element, and the supremum is it.
var SupUniqueAttained = supUniqueAttainedThm{family.Add(registry.ProofEntry{
	Name: "SupUniqueAttained",
	Key:  "prop_4590a5d2fc19b5f7",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(real). ∀b:real.",
		Hypotheses: []string{
			"b ∈ s",
			"∀x:real. x ∈ s ⇒ x ≤ b",
		},
		Conclusion: "sup(s) = b",
	},
		func(a *Argument, s, b Term, greatest Fact) {
			approached := a.Have(
				"b is approached from inside s — by b itself, which lies there",
				"∀c:real. c < b ⇒ ∃x:real. x ∈ s ∧ c < x",
				Derive(func(a *Argument) {
					a.Fix()
					under := a.Assume()
					a.Take(b) // the exceeding member is b
					a.Show(
						"b lies in s, and above anything under it",
						By(greatest, under))
				}))
			// The raw surface: the approach clause quantifies over
			// the set, so normalization Skolemises the value being approached
			// and the clause form would leave that witness to be searched
			// for. Raw, the clause is an implication the fact above meets.
			a.Show(
				"a bound that is approached IS the supremum",
				By(greatest, approached, a.Ctx().Dep(SupUniqueApproach)))
		}),
})}

// InfUniqueAttained — the mirror: a lower bound the set contains is the
// infimum, which is to say a least element is the infimum.
var InfUniqueAttained = infUniqueAttainedThm{family.Add(registry.ProofEntry{
	Name: "InfUniqueAttained",
	Key:  "prop_8d38d645fea6f63b",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(real). ∀b:real.",
		Hypotheses: []string{
			"b ∈ s",
			"∀x:real. x ∈ s ⇒ b ≤ x",
		},
		Conclusion: "inf(s) = b",
	},
		func(a *Argument, s, b Term, least Fact) {
			approached := a.Have(
				"b is approached from inside s — by b itself, which lies there",
				"∀c:real. b < c ⇒ ∃x:real. x ∈ s ∧ x < c",
				Derive(func(a *Argument) {
					a.Fix()
					over := a.Assume()
					a.Take(b) // the undercutting member is b
					a.Show(
						"b lies in s, and below anything over it",
						By(least, over))
				}))
			a.Show(
				"a bound that is approached IS the infimum",
				By(least, approached, a.Ctx().Dep(InfUniqueApproach)))
		}),
})}

// SupUniqueLeastBound — a value whose upper set is exactly the upper
// bounds of s IS the supremum. This is the third and last of the
// pinning laws: UniqueApproach pins sup by what lies under it,
// UniqueAttained by a member, and this one by the bounds themselves —
// b is the supremum precisely when "c bounds s" and "c is at or above
// b" are the same condition on c.
//
// The hypothesis is read twice, and once each way. At c = b it says b
// itself bounds s, reflexivity supplying the right-hand side. At a
// c BELOW b it says the opposite: c does not bound s, so some member
// escapes c — which is exactly the approach clause, since escaping a
// bound is standing strictly above it. The sibling above then closes.
var SupUniqueLeastBound = supUniqueLeastBoundThm{family.Add(registry.ProofEntry{
	Name: "SupUniqueLeastBound",
	Key:  "prop_df32777d7a307a74",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(real). ∀b:real.",
		Hypotheses: []string{
			"∀c:real. (∀x:real. x ∈ s ⇒ x ≤ c) ⇔ b ≤ c",
		},
		Conclusion: "sup(s) = b",
	},
		func(a *Argument, s, b Term, bounds Fact) {
			caps := a.Have(
				"b bounds s — the hypothesis at c = b, whose right-hand side is reflexivity",
				"∀x:real. x ∈ s ⇒ x ≤ b",
				By(bounds.At(b), real_order_ring.LessEqRefl))
			approached := a.Have(
				"and s reaches above everything under b",
				"∀c:real. c < b ⇒ ∃x:real. x ∈ s ∧ c < x",
				Derive(func(a *Argument) {
					c := a.Fix()
					under := a.Assume()
					// `Normalized` because the claim is the hypothesis's own
					// left side NEGATED, and pushing ¬ through the ∀ into
					// the ∃ is what the normalization does; without it the
					// leaf reaches the refuter for a step no search is
					// needed for.
					w, escapes := a.Obtain(
						"c bounds nothing here — it would have to lie at or above b",
						"∃x:real. x ∈ s ∧ ¬(x ≤ c)",
						By(Normalized, bounds.At(c), under, At(real_order_ring.NotLessThan, c, b)))
					a.Take(w) // the member that escapes c is the one above it
					a.Show(
						"escaping a bound is standing strictly above it",
						By(escapes, At(real_order_ring.NotLessThan, c, w)))
				}))
			a.Show(
				"a bound that is approached IS the supremum",
				By(caps, approached, a.Ctx().Dep(SupUniqueApproach)))
		}),
})}

// InfUniqueGreatestBound — the mirror: a value whose lower set is
// exactly the lower bounds of s is the infimum.
var InfUniqueGreatestBound = infUniqueGreatestBoundThm{family.Add(registry.ProofEntry{
	Name: "InfUniqueGreatestBound",
	Key:  "prop_4784b834d3d6c61a",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(real). ∀b:real.",
		Hypotheses: []string{
			"∀c:real. (∀x:real. x ∈ s ⇒ c ≤ x) ⇔ c ≤ b",
		},
		Conclusion: "inf(s) = b",
	},
		func(a *Argument, s, b Term, bounds Fact) {
			floors := a.Have(
				"b lies below s — the hypothesis at c = b, whose right-hand side is reflexivity",
				"∀x:real. x ∈ s ⇒ b ≤ x",
				By(bounds.At(b), real_order_ring.LessEqRefl))
			approached := a.Have(
				"and s reaches below everything above b",
				"∀c:real. b < c ⇒ ∃x:real. x ∈ s ∧ x < c",
				Derive(func(a *Argument) {
					c := a.Fix()
					over := a.Assume()
					// `Normalized` for the reason its mirror gives: the claim
					// is the hypothesis's own left side negated.
					w, escapes := a.Obtain(
						"c bounds nothing here — it would have to lie at or below b",
						"∃x:real. x ∈ s ∧ ¬(c ≤ x)",
						By(Normalized, bounds.At(c), over, At(real_order_ring.NotLessThan, b, c)))
					a.Take(w) // the member that escapes c is the one below it
					a.Show(
						"escaping a bound is standing strictly below it",
						By(escapes, At(real_order_ring.NotLessThan, w, c)))
				}))
			a.Show(
				"a bound that is approached IS the infimum",
				By(floors, approached, a.Ctx().Dep(InfUniqueApproach)))
		}),
})}

// ---------------------------------------------------------------------------
// The comparison calculus: how sup and inf are used
// ---------------------------------------------------------------------------
//
// The part above says what the two operators ARE, but says it
// hypothetically: `real_sup s` is the least upper bound PROVIDED s is
// nonempty and bounded above, where bounded above is a bare existence.
// Every member here translates that into the terms a consumer actually
// argues in — a bound it already knows, a member it can exhibit, a set
// it knows sits inside another — and gets a comparison back.
//
// One of the file's two shapes — half its members — is two steps:
// unlock the characterization at s, then take one half of it at the
// value in hand. What varies within it is how the existence hypothesis
// gets met. A member holding a CONCRETE bound exhibits it and the
// existential never survives into the argument, so a reader sees a bound
// meeting a bound; a member whose own statement supplies
// `∃b. ∀x ∈ s. x ≤ b` receives it from outside. Some comparisons
// additionally run through a MEMBER:
// `real_sup s` caps every member, so a value below some member is below
// `real_sup s` by one use of transitivity, and that same member is what
// makes s nonempty.
//
// The other shape — the other half — assembles a member from siblings
// already in this file, citing no characterization at all.
// `SupBetweenBounds` is each of the two comparison directions used
// once, the upper against a cap and the lower through a member, its inf
// mirror the same two with the roles exchanged. `MemberLessEqSup` is
// the member direction at its degenerate waypoint — the value below a
// member IS that member. And the monotonicity pair chains the two: sup
// t caps t, so it caps every s inside t, so it caps sup s.
//
// Where a hypothesis bounds s on BOTH sides, the half a cited law wants
// is named as its own fact first. The reason is mechanical and worth
// stating once: a law whose antecedent reads `∀x ∈ s. x ≤ b` is met by
// simplification only when a resident says exactly that — negated, the
// antecedent is an existential, and matching it against a two-sided
// `∀x ∈ s. a ≤ x ∧ x ≤ b` would need the refuter to instantiate at a
// Skolem witness. Splitting keeps every close a simplification.
//
// The members that APPROXIMATE rather than compare — the ones that turn
// `c < real_sup s` into a witness above c — live in the estimates below:
// they argue by contraposition, which nothing here does.
//
// The wings never meet. Each wing's chain terminates at its own
// operator's entry, and neither is derived from the other through
// negation.
//
// Three mechanics hold file-wide.
//
// Every dep whose statement quantifies over the SET is cited in its RAW
// surface, and grounded there save for the goal-rewrite direction below
// (the plain order laws are ordinary typed cites). The shape that forces it is a hypothesis quantified over the
// set — `∀x ∈ s. …`, or the `s ≠ ∅ ∧ ∃b. …` of the characterizations.
// Normalization pointwise-expands and Skolemizes those ahead of the set
// binder, so on the installed form the set is no longer the outermost
// slot and a witness tuple naming it binds to a machine binder instead.
// The raw surface binds the set outermost and takes it directly.
// Citing unground would still close, but through the refuter rather
// than by simplification — slower, and it mints a recorded key.
//
// `set_basic.MemberNotEmpty` is used in BOTH directions, and the
// direction decides the spelling. Member ⇒ nonempty is a fact the
// argument needs, so it enters as a premise. Nonempty ⇒ member is a
// goal rewrite: cited bare, the equivalence rewrites the existence goal
// into the nonemptiness already in hand and closes it outright, where
// as a premise it would leave a funext leaf for the refuter.
//
// `Normalized` marks the leaves needing a normalization pass between
// the installs and the close. It is written only where it does work, so
// a close without one is deliberate rather than an oversight — and it
// does not follow the mirror symmetry: a site's need is settled per
// site, not by its twin.

// Six members below restate a bound already in hand as the bare
// EXISTENCE the characterizations ask for — `∃c. ∀x ∈ s. x ≤ c` where a
// particular bound is held. Each spells the witness with `Take` rather
// than leaving the closer to search for it, which is what would cost a
// recorded refutation.

// SupLessEqBound — a bound on the members bounds the supremum: if every
// member of a nonempty s lies at or below b, so does `real_sup s`. This is
// leastness in its working form — b is one upper bound among others,
// and sup s is below all of them.
var SupLessEqBound = supLessEqBoundThm{family.Add(registry.ProofEntry{
	Name: "SupLessEqBound",
	Key:  "prop_fd18e5b65619ca07",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(real). ∀b:real.",
		Hypotheses: []string{
			"s ≠ ∅",
			"∀x:real. x ∈ s ⇒ x ≤ b",
		},
		Conclusion: "sup(s) ≤ b",
	},
		func(a *Argument, s, b Term, nonemptyBounded Fact) {
			above := a.Have(
				"s is bounded above, b being a bound",
				"∃c:real. ∀x:real. x ∈ s ⇒ x ≤ c",
				Derive(func(a *Argument) {
					a.Take(b)
					a.Show(
						"which is the bound the hypothesis already states",
						By(nonemptyBounded))
				}))
			// The raw surface, grounded at s — the file header says why.
			least := a.Have(
				"so sup s lies below every upper bound of s — s is nonempty and now bounded above",
				"∀c:real. (∀x:real. x ∈ s ⇒ x ≤ c) ⇒ sup(s) ≤ c",
				By(nonemptyBounded, above, At(SupLeastUpperBound, s)))
			a.Show(
				"and b is one of those upper bounds",
				By(least.At(b), nonemptyBounded))
		}),
})}

// BoundLessEqInf — the mirror: a bound below the members lies below
// the infimum, since the infimum is the greatest of the lower bounds
// and b is one of them.
var BoundLessEqInf = boundLessEqInfThm{family.Add(registry.ProofEntry{
	Name: "BoundLessEqInf",
	Key:  "prop_81e34ad4ea518975",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(real). ∀b:real.",
		Hypotheses: []string{
			"s ≠ ∅",
			"∀x:real. x ∈ s ⇒ b ≤ x",
		},
		Conclusion: "b ≤ inf(s)",
	},
		func(a *Argument, s, b Term, nonemptyBounded Fact) {
			below := a.Have(
				"s is bounded below, b being a bound",
				"∃c:real. ∀x:real. x ∈ s ⇒ c ≤ x",
				Derive(func(a *Argument) {
					a.Take(b)
					a.Show(
						"which is the bound the hypothesis already states",
						By(nonemptyBounded))
				}))
			greatest := a.Have(
				"so inf s lies above every lower bound of s — s is nonempty and now bounded below",
				"∀c:real. (∀x:real. x ∈ s ⇒ c ≤ x) ⇒ c ≤ inf(s)",
				By(nonemptyBounded, below, At(InfGreatestLowerBound, s)))
			a.Show(
				"and b is one of those lower bounds",
				By(greatest.At(b), nonemptyBounded))
		}),
})}

// SupLessEqIff — for a nonempty bounded set, `real_sup s ≤ y` says nothing
// more or less than that y caps every member. Both halves of the
// characterization are used, one per direction: leastness turns a cap
// into the comparison, and the upper-bound half turns the comparison
// back into a cap by passing each member through `real_sup s`.
var SupLessEqIff = supLessEqIffThm{family.Add(registry.ProofEntry{
	Name: "SupLessEqIff",
	Key:  "prop_a1ec2b08933bae96",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(real). ∀y:real.",
		Hypotheses: []string{
			"s ≠ ∅",
			"∃b:real. ∀x:real. x ∈ s ⇒ x ≤ b",
		},
		Conclusion: "sup(s) ≤ y ⇔ ∀x:real. x ∈ s ⇒ x ≤ y",
	},
		func(a *Argument, s, y Term, nonemptyBounded Fact) {
			ctx := a.Ctx()
			// The raw surface, grounded at s — the file header says why.
			lub := At(SupLeastUpperBound, s)
			supS := ops(ctx).RealSup.Apply(s)

			caps := a.Have(
				"sup s caps s — the hypothesis is exactly what unlocks the characterization",
				"∀x:real. x ∈ s ⇒ x ≤ sup(s)",
				By(nonemptyBounded, lub))
			least := a.Have(
				"and it is the least cap",
				"∀c:real. (∀x:real. x ∈ s ⇒ x ≤ c) ⇒ sup(s) ≤ c",
				By(nonemptyBounded, lub))

			a.Iff()
			a.Forward(
				"a member lies below sup s, which lies below y",
				func(a *Argument, supLeY Fact) {
					x := a.Fix()
					inS := a.Assume()
					a.Show(
						"transitivity through sup s", // x ≤ sup s ≤ y
						By(caps.At(x), inS, supLeY, At(real_construction.LessEqTrans, x, supS, y)))
				})
			a.Backward(
				"y is a cap, and sup s lies below every cap",
				func(a *Argument, yCaps Fact) {
					a.Show(
						"leastness at y", // sup s ≤ y
						By(least.At(y), yCaps))
				})
		}),
})}

// LessEqInfIff — the mirror: `y ≤ real_inf s` says exactly that y lies under
// every member.
var LessEqInfIff = lessEqInfIffThm{family.Add(registry.ProofEntry{
	Name: "LessEqInfIff",
	Key:  "prop_f3ca8a4a40533354",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(real). ∀y:real.",
		Hypotheses: []string{
			"s ≠ ∅",
			"∃b:real. ∀x:real. x ∈ s ⇒ b ≤ x",
		},
		Conclusion: "y ≤ inf(s) ⇔ ∀x:real. x ∈ s ⇒ y ≤ x",
	},
		func(a *Argument, s, y Term, nonemptyBounded Fact) {
			ctx := a.Ctx()
			glb := At(InfGreatestLowerBound, s)
			infS := ops(ctx).RealInf.Apply(s)

			floors := a.Have(
				"inf s lies under s — the hypothesis unlocks the characterization",
				"∀x:real. x ∈ s ⇒ inf(s) ≤ x",
				By(nonemptyBounded, glb))
			greatest := a.Have(
				"and it is the greatest floor",
				"∀c:real. (∀x:real. x ∈ s ⇒ c ≤ x) ⇒ c ≤ inf(s)",
				By(nonemptyBounded, glb))

			a.Iff()
			a.Forward(
				"y lies below inf s, which lies below every member",
				func(a *Argument, yLeInf Fact) {
					x := a.Fix()
					inS := a.Assume()
					a.Show(
						"transitivity through inf s", // y ≤ inf s ≤ x
						By(floors.At(x), inS, yLeInf, At(real_construction.LessEqTrans, y, infS, x)))
				})
			a.Backward(
				"y is a floor, and inf s lies above every floor",
				func(a *Argument, yFloors Fact) {
					a.Show(
						"greatestness at y", // y ≤ inf s
						By(greatest.At(y), yFloors))
				})
		}),
})}

// LessEqSupThroughMember — a lower estimate for `real_sup s` obtained from a
// single member: anything at or below some y ∈ s is at or below sup s.
// The member does double duty — it is what makes s nonempty, and it is
// the waypoint the comparison passes through.
var LessEqSupThroughMember = lessEqSupThroughMemberThm{family.Add(registry.ProofEntry{
	Name: "LessEqSupThroughMember",
	Key:  "prop_4f79f98f4b544645",
	// The receiver is `arg` in the members whose statements bind `a`, and
	// `a` elsewhere.
	Build: family.Theorem(Statement{
		Binders: "∀s:set(real). ∀a b y:real.",
		Hypotheses: []string{
			"y ∈ s",
			"a ≤ y",
			"∀x:real. x ∈ s ⇒ x ≤ b",
		},
		Conclusion: "a ≤ sup(s)",
	},
		func(arg *Argument, s, a, b, y Term, memberBounded Fact) {
			ctx := arg.Ctx()
			supS := ops(ctx).RealSup.Apply(s)

			above := arg.Have(
				"s is bounded above, b being a bound",
				"∃c:real. ∀x:real. x ∈ s ⇒ x ≤ c",
				Derive(func(arg *Argument) {
					arg.Take(b)
					arg.Show(
						"which is the bound the hypothesis already states",
						By(memberBounded))
				}))
			caps := arg.Have(
				"so sup s caps s — y's membership supplies the nonemptiness",
				"∀x:real. x ∈ s ⇒ x ≤ sup(s)",
				By(
					Normalized,
					memberBounded,
					above,
					At(SupLeastUpperBound, s),
					At(set_basic.MemberNotEmpty.Inst[Real](), s)))
			arg.Show(
				"and a lies below y, which lies below the cap", // a ≤ y ≤ sup s
				By(caps.At(y), memberBounded, At(real_construction.LessEqTrans, a, y, supS)))
		}),
})}

// InfLessEqThroughMember — the mirror: anything at or above some y ∈ s
// is at or above inf s.
var InfLessEqThroughMember = infLessEqThroughMemberThm{family.Add(registry.ProofEntry{
	Name: "InfLessEqThroughMember",
	Key:  "prop_c6476abd51caeec3",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(real). ∀a b y:real.",
		Hypotheses: []string{
			"y ∈ s",
			"y ≤ a",
			"∀x:real. x ∈ s ⇒ b ≤ x",
		},
		Conclusion: "inf(s) ≤ a",
	},
		func(arg *Argument, s, a, b, y Term, memberBounded Fact) {
			ctx := arg.Ctx()
			infS := ops(ctx).RealInf.Apply(s)

			below := arg.Have(
				"s is bounded below, b being a bound",
				"∃c:real. ∀x:real. x ∈ s ⇒ c ≤ x",
				Derive(func(arg *Argument) {
					arg.Take(b)
					arg.Show(
						"which is the bound the hypothesis already states",
						By(memberBounded))
				}))
			floors := arg.Have(
				"so inf s lies under s — y's membership supplies the nonemptiness",
				"∀x:real. x ∈ s ⇒ inf(s) ≤ x",
				By(
					Normalized,
					memberBounded,
					below,
					At(InfGreatestLowerBound, s),
					At(set_basic.MemberNotEmpty.Inst[Real](), s)))
			arg.Show(
				"and the floor lies under y, which lies under a", // inf s ≤ y ≤ a
				By(floors.At(y), memberBounded, At(real_construction.LessEqTrans, infS, y, a)))
		}),
})}

// SupBetweenBounds — a set squeezed between a and b has its supremum
// there too. The two conjuncts are the chapter's two ways of comparing
// with `real_sup s` used once each: the upper one against the cap b, and the
// lower one through a member, which nonemptiness supplies.
var SupBetweenBounds = supBetweenBoundsThm{family.Add(registry.ProofEntry{
	Name: "SupBetweenBounds",
	Key:  "prop_7243a27d09d87970",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(real). ∀a b:real.",
		Hypotheses: []string{
			"s ≠ ∅",
			"∀x:real. x ∈ s ⇒ a ≤ x ∧ x ≤ b",
		},
		Conclusion: "a ≤ sup(s) ∧ sup(s) ≤ b",
	},
		func(arg *Argument, s, a, b Term, nonemptyBetween Fact) {
			twoSided := arg.Have(
				"s is bounded on both sides",
				"∀x:real. x ∈ s ⇒ a ≤ x ∧ x ≤ b",
				By(nonemptyBetween))
			caps := arg.Have(
				"its upper side alone: b caps s",
				"∀x:real. x ∈ s ⇒ x ≤ b",
				Derive(func(arg *Argument) {
					x := arg.Fix()
					inS := arg.Assume()
					arg.Show(
						"the two-sided bound at x",
						By(twoSided.At(x), inS))
				}))
			// ↦ s ≠ ∅ (the goal-rewrite direction; see the header).
			x, inS := arg.Obtain(
				"s is nonempty, so it holds a member",
				"∃x:real. x ∈ s",
				Cite(set_basic.MemberNotEmpty))
			lower := arg.Have(
				"a lies below sup s, passing through that member",
				"a ≤ sup(s)",
				By(
					caps,
					inS,
					twoSided.At(x),
					// LessEqSupThroughMember at (s, a, b, x): its (a, b, y) are our
					// (a, b, x) — the roles coincide here, unlike the mirror below.
					At(LessEqSupThroughMember, s, a, b, x)))
			arg.Show(
				"and sup s lies below b, b being a cap",
				By(caps, lower, nonemptyBetween, At(SupLessEqBound, s, b)))
		}),
})}

// InfBetweenBounds — the mirror, and the same two ways of comparing
// with the opposite roles: the lower conjunct is a floor comparison and
// needs no member, while the upper one goes through a member.
var InfBetweenBounds = infBetweenBoundsThm{family.Add(registry.ProofEntry{
	Name: "InfBetweenBounds",
	Key:  "prop_91dfe58650920493",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(real). ∀a b:real.",
		Hypotheses: []string{
			"s ≠ ∅",
			"∀x:real. x ∈ s ⇒ a ≤ x ∧ x ≤ b",
		},
		Conclusion: "a ≤ inf(s) ∧ inf(s) ≤ b",
	},
		func(arg *Argument, s, a, b Term, nonemptyBetween Fact) {
			ctx := arg.Ctx()

			twoSided := arg.Have(
				"s is bounded on both sides",
				"∀x:real. x ∈ s ⇒ a ≤ x ∧ x ≤ b",
				By(nonemptyBetween))
			floors := arg.Have(
				"its lower side alone: a floors s",
				"∀x:real. x ∈ s ⇒ a ≤ x",
				Derive(func(arg *Argument) {
					x := arg.Fix()
					inS := arg.Assume()
					arg.Show(
						"the two-sided bound at x",
						By(twoSided.At(x), inS))
				}))
			lower := arg.Have(
				"so a lies under inf s, a being one of the floors",
				"a ≤ inf(s)",
				By(floors, nonemptyBetween, ctx.Dep(BoundLessEqInf)))
			// ↦ s ≠ ∅ (the goal-rewrite direction; see the header).
			x, inS := arg.Obtain(
				"s is nonempty, so it holds a member",
				"∃x:real. x ∈ s",
				Cite(set_basic.MemberNotEmpty))
			arg.Show(
				"and inf s lies under b, passing through that member",
				By(
					floors,
					inS,
					lower,
					twoSided.At(x),
					// InfLessEqThroughMember at (s, b, a, x): its (a, b, y) are our
					// (b, a, x) — its second binder is the value inf is compared TO
					// and its third a floor of s, so our b and a enter swapped.
					At(InfLessEqThroughMember, s, b, a, x)))
		}),
})}

// MemberLessEqSup — a member of a bounded set lies at or below the
// set's supremum. It is the degenerate case of the member comparison:
// `LessEqSupThroughMember` reaches `real_sup s` from a value below some
// member, and here the value IS the member, so the waypoint is itself
// and reflexivity carries the passage.
var MemberLessEqSup = memberLessEqSupThm{family.Add(registry.ProofEntry{
	Name: "MemberLessEqSup",
	Key:  "prop_100823ce00fbef8e",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(real). ∀a:real.",
		Hypotheses: []string{
			"∃b:real. ∀x:real. x ∈ s ⇒ x ≤ b",
			"a ∈ s",
		},
		Conclusion: "a ≤ sup(s)",
	},
		func(arg *Argument, s, a Term, boundedMember Fact) {
			// The bound is asserted to exist rather than named, and the
			// member law wants it as a term — so it is named here, once.
			bounded := arg.Have(
				"s is bounded above by some b",
				"∃b:real. ∀x:real. x ∈ s ⇒ x ≤ b",
				By(boundedMember))
			// caps: ∀x ∈ s. x ≤ b.
			b, caps := arg.Unpack(bounded)
			arg.Show(
				"a reaches sup s through itself — a ∈ s and a ≤ a",
				By(
					caps,
					boundedMember,
					At(real_order_ring.LessEqRefl, a),
					// (s, a, b, y) at (s, a, b, a): the waypoint y is a itself.
					At(LessEqSupThroughMember, s, a, b, a)))
		}),
})}

// InfLessEqMember — the mirror: the infimum lies at or below every
// member.
var InfLessEqMember = infLessEqMemberThm{family.Add(registry.ProofEntry{
	Name: "InfLessEqMember",
	Key:  "prop_359dde31e4de2847",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(real). ∀a:real.",
		Hypotheses: []string{
			"∃b:real. ∀x:real. x ∈ s ⇒ b ≤ x",
			"a ∈ s",
		},
		Conclusion: "inf(s) ≤ a",
	},
		func(arg *Argument, s, a Term, boundedMember Fact) {
			bounded := arg.Have(
				"s is bounded below by some b",
				"∃b:real. ∀x:real. x ∈ s ⇒ b ≤ x",
				By(boundedMember))
			// floors: ∀x ∈ s. b ≤ x.
			b, floors := arg.Unpack(bounded)
			arg.Show(
				"inf s reaches a through a itself — a ∈ s and a ≤ a",
				By(
					floors,
					boundedMember,
					At(real_order_ring.LessEqRefl, a),
					// (s, a, b, y) at (s, a, b, a): the value inf is compared TO,
					// the floor, the member — the waypoint y is a itself.
					At(InfLessEqThroughMember, s, a, b, a)))
		}),
})}

// SupMonoSubset — sup is monotone under inclusion: a bigger set has a
// bigger supremum. The bound is on the LARGER set, which is what makes
// the argument go: `real_sup t` caps every member of t — t being bounded and
// inhabited by that member — so it caps s as well, and leastness at s
// turns that cap into the comparison.
//
// Reaching it through `MemberLessEqSup` rather than the characterization
// is what keeps it to two cites: the member law carries NO nonemptiness
// hypothesis, so citing it at t never obliges proving `t ≠ ∅` — which
// this statement does not give. It gives `s ≠ ∅`, and only leastness at
// s needs that.
var SupMonoSubset = supMonoSubsetThm{family.Add(registry.ProofEntry{
	Name: "SupMonoSubset",
	Key:  "prop_a5d3120db65727ae",
	Build: family.Theorem(Statement{
		Binders: "∀s t:set(real). ∀b:real.",
		Hypotheses: []string{
			"s ⊆ t",
			"s ≠ ∅",
			"∀x:real. x ∈ t ⇒ x ≤ b",
		},
		Conclusion: "sup(s) ≤ sup(t)",
	},
		func(a *Argument, s, t, b Term) {
			ctx := a.Ctx()
			v := ops(ctx)

			// An inclusion IS a pointwise implication by subset's defining
			// equation — so it is unfolded and not cited. The unfold discharges the antecedent along with it,
			// which is why this closure takes no `Fact` parameter and the three
			// conjuncts are named below instead.
			a.Do(Unfold(set_basic.SubsetDef)) // ↦ ∀x. x ∈ s ⇒ x ∈ t, the antecedent discharged
			inside := a.Hyp("∀x:real. x ∈ s ⇒ x ∈ t")
			nonempty := a.Hyp("s ≠ ∅")
			capsT := a.Hyp("∀x:real. x ∈ t ⇒ x ≤ b")

			above := a.Have(
				"t is bounded above, b being a bound",
				"∃c:real. ∀x:real. x ∈ t ⇒ x ≤ c",
				Derive(func(a *Argument) {
					a.Take(b)
					a.Show(
						"which is the bound the hypothesis already states",
						By(capsT))
				}))
			caps := a.Have(
				"so sup t caps s too, member by member",
				"∀x:real. x ∈ s ⇒ x ≤ sup(t)",
				Derive(func(a *Argument) {
					x := a.Fix()
					inS := a.Assume()
					// Named rather than left to the close: with `x ∈ t` resident the
					// member law's antecedent is met by simplification, and without
					// it the leaf reaches the refuter.
					inT := a.Have(
						"x lies in t as well",
						MakeProp(v.In(x, t)),
						By(inside.At(x), inS))
					a.Show(
						"and sup t caps every member of t",
						By(inT, above, ctx.Dep(MemberLessEqSup)))
				}))
			a.Show(
				"s is nonempty and sup t caps it, so sup s lies below sup t",
				By(caps, nonempty, ctx.Dep(SupLessEqBound)))
		}),
})}

// InfAntitoneSubset — inf runs the other way: a bigger set has a
// SMALLER infimum, so the conclusion compares `real_inf t` down to `real_inf s`
// where the sup member compared up. Everything else mirrors — the
// bound is again on the larger set, `real_inf t` floors t hence floors s,
// and greatestness at s turns that floor into the comparison.
var InfAntitoneSubset = infAntitoneSubsetThm{family.Add(registry.ProofEntry{
	Name: "InfAntitoneSubset",
	Key:  "prop_e964122391e06e9b",
	Build: family.Theorem(Statement{
		Binders: "∀s t:set(real). ∀b:real.",
		Hypotheses: []string{
			"s ⊆ t",
			"s ≠ ∅",
			"∀x:real. x ∈ t ⇒ b ≤ x",
		},
		Conclusion: "inf(t) ≤ inf(s)",
	},
		func(a *Argument, s, t, b Term) {
			ctx := a.Ctx()
			v := ops(ctx)

			a.Do(Unfold(set_basic.SubsetDef))
			inside := a.Hyp("∀x:real. x ∈ s ⇒ x ∈ t")
			nonempty := a.Hyp("s ≠ ∅")
			floorsT := a.Hyp("∀x:real. x ∈ t ⇒ b ≤ x")

			below := a.Have(
				"t is bounded below, b being a bound",
				"∃c:real. ∀x:real. x ∈ t ⇒ c ≤ x",
				Derive(func(a *Argument) {
					a.Take(b)
					a.Show(
						"which is the bound the hypothesis already states",
						By(floorsT))
				}))
			floors := a.Have(
				"so inf t lies under s too, member by member",
				"∀x:real. x ∈ s ⇒ inf(t) ≤ x",
				Derive(func(a *Argument) {
					x := a.Fix()
					inS := a.Assume()
					inT := a.Have(
						"x lies in t as well",
						MakeProp(v.In(x, t)),
						By(inside.At(x), inS))
					a.Show(
						"and inf t lies under every member of t",
						By(inT, below, ctx.Dep(InfLessEqMember)))
				}))
			a.Show(
				"s is nonempty and inf t floors it, so inf t lies below inf s",
				By(floors, nonempty, ctx.Dep(BoundLessEqInf)))
		}),
})}

// The supremum of a sequence is the supremum of its range, `sup(image(a,
// 𝕌))`, which is never empty and whose members are the terms: the two laws
// below are MemberLessEqSup and SupLessEqBound read over that range.

// TermLessEqSequenceSup — every term of a sequence bounded above lies at or
// below the supremum of its terms.
var TermLessEqSequenceSup = termLessEqSequenceSupThm{family.Add(registry.ProofEntry{
	Name: "TermLessEqSequenceSup",
	Key:  "prop_340af0bda230579c",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → real). ∀b:real. ∀n:num.",
		Hypotheses: []string{
			"∀m:num. a(m) ≤ b",
		},
		Conclusion: "a(n) ≤ sup(image(a, 𝕌))",
	}, func(arg *Argument, a *Arrow[Nat, Real], b *Expr[Real], n *Expr[Nat], bounded Fact) {
		naturals := arg.TermAs[Set[Nat]]("𝕌")
		arg.Show(
			"a(n) is a member of the range, which b bounds",
			By(
				Normalized,
				bounded,
				set_image.FunInImage.At(a, naturals, n),
				set_basic.InUniv.At(n),
				set_image.ForallInImage.At(a, naturals, arg.TermAs[Fun[Real, Bool]]("λy:real. y ≤ b")),
				real_order_ring.LessEqRefl.At(a.Apply(n)),
				LessEqSupThroughMember.At(arg.TermAs[Set[Real]]("image(a, 𝕌)"), a.Apply(n), b, a.Apply(n))))
	}),
})}

// SequenceSupLessEqBound — a bound of every term of a sequence bounds the
// supremum of its terms.
var SequenceSupLessEqBound = sequenceSupLessEqBoundThm{family.Add(registry.ProofEntry{
	Name: "SequenceSupLessEqBound",
	Key:  "prop_6871aad92058044b",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → real). ∀b:real.",
		Hypotheses: []string{
			"∀n:num. a(n) ≤ b",
		},
		Conclusion: "sup(image(a, 𝕌)) ≤ b",
	}, func(arg *Argument, a *Arrow[Nat, Real], b *Expr[Real], bounded Fact) {
		arg.Show(
			"b bounds the range, which is not empty",
			BySets(bounded, SupLessEqBound.At(arg.TermAs[Set[Real]]("image(a, 𝕌)"), b)))
	}),
})}

// ---------------------------------------------------------------------------
// The estimates: how sup and inf are APPROXIMATED
// ---------------------------------------------------------------------------
//
// The comparison calculus above turns a bound, a member or an inclusion into a
// comparison with `real_sup s`. The four members here answer the opposite
// question: given where the extremum is, where are the members.
//
// They are a separate reading unit because they are built on a
// different LAYER, not merely by a different trick: every member here
// cites the comparison calculus's laws and none cites a characterization
// directly, so the ε-layer that part unlocks is already spent by the
// time these begin, and nothing in the chapter cites back into this
// part. That one-directional dependency is the whole of the case.
//
// One move accounts for all four. `SupApproach` and its mirror argue by
// CONTRAPOSITION: a value strictly under `real_sup s` is exceeded inside s,
// because a c that capped every member would cap `real_sup s` too. The
// member is never constructed — it is read off c's failure to be a
// bound. `SupApproachWithin` and its mirror are that law read at
// `sup s − δ` and `inf s + δ`, the form an ε-argument consumes.
//
// Two mechanics carry over from the comparison calculus unchanged, and its
// header states them in full: a dep whose statement quantifies over
// the SET is cited in its RAW surface and grounded there, and
// `Normalized` is written only where deleting it and replaying strict
// turns the leaf red. Nothing here exhibits a member of s, so none of
// that file's `set_basic.MemberNotEmpty` traffic recurs — each member
// takes `s ≠ ∅` as a hypothesis and hands it on.

// SupApproach — the supremum is approached from inside: no value
// strictly below `real_sup s` caps s, so each of them is exceeded by some
// member. This is what makes `real_sup s` a limit rather than merely a
// bound, and it is the form every ε-argument above this chapter uses.
//
// The member is produced by contraposition and never built. Were c a
// cap, leastness would give `real_sup s ≤ c`; the hypothesis says
// `c < real_sup s`, so c is no cap — and a set that c fails to cap holds a
// member c fails to bound.
var SupApproach = supApproachThm{family.Add(registry.ProofEntry{
	Name: "SupApproach",
	Key:  "prop_dd879fc57c8e24bd",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(real). ∀c:real.",
		Hypotheses: []string{
			"s ≠ ∅",
			"c < sup(s)",
		},
		Conclusion: "∃x:real. x ∈ s ∧ c < x",
	},
		func(a *Argument, s, c Term, nonemptyUnderSup Fact) {
			ctx := a.Ctx()
			supS := ops(ctx).RealSup.Apply(s)

			x, escapes := a.Obtain(
				"c is no upper bound of s — a cap would put sup s at or below c",
				"∃x:real. x ∈ s ∧ ¬(x ≤ c)",
				By(
					Normalized,
					nonemptyUnderSup,
					// leastness at c
					At(SupLessEqBound, s, c),
					// ¬(c < sup s) ⇔ sup s ≤ c, the half the hypothesis denies
					At(real_order_ring.NotLessThan, c, supS)))
			a.Take(x)
			a.Show(
				"and a member the cap misses lies above c", // ¬(x ≤ c) ⇔ c < x
				By(escapes, At(real_order_ring.NotLessThan, c, x)))
		}),
})}

// InfApproach — the mirror: no value strictly above `real_inf s` lies
// under s, so each of them has a member beneath it.
var InfApproach = infApproachThm{family.Add(registry.ProofEntry{
	Name: "InfApproach",
	Key:  "prop_591e092a12a9dc06",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(real). ∀c:real.",
		Hypotheses: []string{
			"s ≠ ∅",
			"inf(s) < c",
		},
		Conclusion: "∃x:real. x ∈ s ∧ x < c",
	},
		func(a *Argument, s, c Term, nonemptyOverInf Fact) {
			ctx := a.Ctx()
			infS := ops(ctx).RealInf.Apply(s)

			x, escapes := a.Obtain(
				"c is no lower bound of s — a floor would put inf s at or above c",
				"∃x:real. x ∈ s ∧ ¬(c ≤ x)",
				By(
					Normalized,
					nonemptyOverInf,
					// greatestness at c
					At(BoundLessEqInf, s, c),
					// ¬(inf s < c) ⇔ c ≤ inf s, the half the hypothesis denies
					At(real_order_ring.NotLessThan, infS, c)))
			a.Take(x)
			a.Show(
				"and a member the floor misses lies below c", // ¬(c ≤ x) ⇔ x < c
				By(escapes, At(real_order_ring.NotLessThan, x, c)))
		}),
})}

// SupApproachWithin — within any positive margin below the supremum
// lies a member: SupApproach at sup s − δ, the member lying at or below
// sup s as every member does. It is the approximation law in the form
// an ε-argument reads it, a member within δ of the supremum.
var SupApproachWithin = supApproachWithinThm{family.Add(registry.ProofEntry{
	Name: "SupApproachWithin",
	Key:  "prop_6e94d44c8020e8d9",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(real). ∀δ:real.",
		Hypotheses: []string{
			"s ≠ ∅",
			"∃b:real. ∀x:real. x ∈ s ⇒ x ≤ b",
			"&0 < δ",
		},
		Conclusion: "∃x:real. x ∈ s ∧ sup(s) - δ < x ∧ x ≤ sup(s)",
	},
		func(a *Argument, s *Expr[Set[Real]], δ *Expr[Real], given Fact) {
			parts := a.Conjuncts(
				given,
				"s is not empty",
				"s is bounded above",
				"δ is positive")
			below := a.Have(
				"sup s − δ lies below sup s",
				"sup(s) - δ < sup(s)",
				ByArith(parts[2]))
			x, approach := a.ObtainAs[Real](
				"so a member x of s lies above sup s − δ",
				"∃x:real. x ∈ s ∧ sup(s) - δ < x",
				By(SupApproach.At(s, a.TermAs[Real]("sup(s) - δ")), parts[0], below))
			member := a.Conjuncts(
				approach,
				"x is a member of s",
				"above sup s − δ")
			a.Take(x)
			a.Show(
				"and at or below sup s, as every member is",
				By(member[0], member[1], MemberLessEqSup.At(s, x), parts[1]))
		}),
})}

// InfApproachWithin — the mirror: within any positive margin above the
// infimum lies a member.
var InfApproachWithin = infApproachWithinThm{family.Add(registry.ProofEntry{
	Name: "InfApproachWithin",
	Key:  "prop_25e20bc2f8b4f167",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(real). ∀δ:real.",
		Hypotheses: []string{
			"s ≠ ∅",
			"∃b:real. ∀x:real. x ∈ s ⇒ b ≤ x",
			"&0 < δ",
		},
		Conclusion: "∃x:real. x ∈ s ∧ inf(s) ≤ x ∧ x < inf(s) + δ",
	},
		func(a *Argument, s *Expr[Set[Real]], δ *Expr[Real], given Fact) {
			parts := a.Conjuncts(
				given,
				"s is not empty",
				"s is bounded below",
				"δ is positive")
			above := a.Have(
				"inf s + δ lies above inf s",
				"inf(s) < inf(s) + δ",
				ByArith(parts[2]))
			x, approach := a.ObtainAs[Real](
				"so a member x of s lies below inf s + δ",
				"∃x:real. x ∈ s ∧ x < inf(s) + δ",
				By(InfApproach.At(s, a.TermAs[Real]("inf(s) + δ")), parts[0], above))
			member := a.Conjuncts(
				approach,
				"x is a member of s",
				"below inf s + δ")
			a.Take(x)
			a.Show(
				"and at or above inf s, as every member is",
				By(member[0], InfLessEqMember.At(s, x), parts[1], member[1]))
		}),
})}
