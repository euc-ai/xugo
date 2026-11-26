// fold.go — the chapter's fold-well-definedness part.
//
// To fold a step function over a finite set one has to visit its
// elements in SOME order, and a set has none; the theorem that the
// answer does not depend on the order chosen is what cardinality's
// FiniteRecursion consumes, and this file is where it is established.
// The instrument is set_fold_stage: "a is what folding f from b over s in
// exactly n steps can produce". It is a relation, not a function — at
// each step ANY element of the set may be the one taken off — and the
// part's work is to show that for a finite set the relation is total
// and single-valued, so that a function can be chosen from it.
//
// The clauses of set_fold_stage are read off its definition (setFoldStageDef), then
// what they say at one step (SetFoldStageSingleton), then the rearrangement
// that makes order irrelevant (SetFoldStageStep: any element may be the one
// taken off first), and from it the two halves of well-definedness: the
// relation is single-valued (SetFoldStageUnique) and, on finite sets, total
// (SetFoldStageExists).

package finite_set

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	"github.com/euc-ai/xugo/library/proofs/sets/set_algebra"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// set_fold_stage's clauses, read off the definition
// ---------------------------------------------------------------------------

// setFoldStageZeroClause reads set_fold_stage's 0 clause off the definition as one
// ∀-fact — in zero steps the fold reaches p from q over t exactly when
// nothing was folded: t is empty and p is q — in the order the fold
// members cite it, (g, t, p, q): the set before the values. The
// definition states the clause under its own prefix in the order
// (f, b, s, a); it is the same clause, and the member that once
// restated the two clauses as a theorem of its own was the definition
// under another binder order.
func setFoldStageZeroClause(arg *Argument) Fact {
	return arg.Have(
		"the 0 clause of set_fold_stage",
		"∀g:(A → B → B). ∀t:set(A). ∀p q:B. set_fold_stage(g, q, t, p, 0) ⇔ t = ∅ ∧ p = q",
		By(arg.Ctx().Dep(setFoldStageDef)))
}

// setFoldStageSucClause reads set_fold_stage's suc clause off the definition as one
// ∀-fact: in suc k steps the fold reaches p exactly when some element x
// of t was taken off first, the remaining k steps fold t ∖ {x} to some
// c, and p is g(x, c). Cited at (g, t, p, q, k).
func setFoldStageSucClause(arg *Argument) Fact {
	return arg.Have(
		"the suc clause of set_fold_stage",
		"∀g:(A → B → B). ∀t:set(A). ∀p q:B. ∀k:num. "+
			"    set_fold_stage(g, q, t, p, suc(k)) ⇔ "+
			"    ∃x:A. ∃c:B. x ∈ t ∧ set_fold_stage(g, q, delete(t, x), c, k) ∧ p = g(x, c)",
		By(arg.Ctx().Dep(setFoldStageDef)))
}

// ---------------------------------------------------------------------------
// SetFoldStageSingleton — one step folds exactly the singletons
// ---------------------------------------------------------------------------

// SetFoldStageSingleton — in one step the fold reaches a from b over s exactly
// when s is a singleton {x} and a is f(x, b). One step means an element
// x of s comes off and what remains folds in zero steps, i.e. is empty
// with value b; a set with a member whose removal leaves nothing is that
// singleton, and conversely taking the point out of {x} leaves nothing.
// Both set facts are constructor facts, closed by the set driver.
var SetFoldStageSingleton = setFoldStageSingletonThm{family.Add(registry.ProofEntry{
	Name: "SetFoldStageSingleton",
	Key:  "prop_88dba4109eff3071",
	Build: family.Theorem(
		"∀f:(A → B → B). ∀b:B. ∀s:set(A). ∀a:B. "+
			"    set_fold_stage(f, b, s, a, suc(0)) ⇔ ∃x:A. s = {x} ∧ a = f(x, b)",
		func(arg *Argument, f, b, s, a Term) {
			v := ops(arg.Ctx())
			zero := arg.Ctx().Numeral(0)
			zeroClause, sucClause := setFoldStageZeroClause(arg), setFoldStageSucClause(arg)
			arg.Iff()
			arg.Forward(
				"the one step takes some x off and nothing is left, so s is {x} and a is f(x, b)",
				func(d *Argument, oneStep Fact) { // set_fold_stage(f, b, s, a, suc(0))
					x, c, step := d.Obtain2(
						"some x ∈ s comes off first and the rest folds to c in zero steps",
						"∃x:A. ∃c:B. x ∈ s ∧ set_fold_stage(f, b, delete(s, x), c, 0) ∧ a = f(x, c)",
						By(
							oneStep,
							sucClause.At(f, s, a, b, zero))) // the suc clause at (f, s, a, b, 0), read against the hypothesis
					rest := v.Delete.Apply(s, x)
					nothingLeft := d.Have(
						"a zero-step fold: nothing is left, and c₀ is b",
						"delete(s, x₀) = ∅ ∧ c₀ = b",
						By(step, zeroClause.At(f, rest, c, b))) // the 0 clause at (f, s ∖ {x₀}, c₀, b)
					isSingleton := d.Have(
						"a set with a member whose removal leaves nothing is that singleton",
						"s = {x₀}",
						BySets(step, nothingLeft))
					d.Take(x)
					d.Show(
						"x₀ is the point, and a = f(x₀, c₀) with c₀ = b",
						By(Normalized, isSingleton, nothingLeft, step))
				})
			arg.Backward(
				"over {x} the one step takes x off and folds nothing, so it reaches f(x, b)",
				func(d *Argument, sing Fact) { // ∃x. s = {x} ∧ a = f(x, b)
					x, h := d.Unpack(sing) // s = {x₀} ∧ a = f(x₀, b)
					rest := v.Delete.Apply(s, x)
					xIn := d.Have(
						"x₀ is in s",
						"x₀ ∈ s",
						BySets(h))
					emptied := d.Have(
						"taking x₀ off leaves nothing",
						"delete(s, x₀) = ∅",
						BySets(h))
					folded := d.Have(
						"and over nothing the zero-step fold reaches b",
						"set_fold_stage(f, b, delete(s, x₀), b, 0)",
						By(emptied, zeroClause.At(f, rest, b, b))) // the 0 clause at (f, s ∖ {x₀}, b, b)
					d.Show(
						"so x₀ and b witness the suc(0) clause",
						By(xIn, h, folded, sucClause.At(f, s, a, b, zero))) // the suc clause at (f, s, a, b, 0)
				})
		}),
})}

// ---------------------------------------------------------------------------
// SetFoldStageStep — any element of the set may be the one taken off first
// ---------------------------------------------------------------------------

// SetFoldStageStep — when the step function commutes on distinct elements, a
// fold of s in suc(n) steps can be rearranged to take any chosen x ∈ s
// off FIRST: the remaining n steps fold s ∖ {x} to some w, and the value
// is f(x, w). This is the whole of what commutation buys, and uniqueness
// (SetFoldStageUnique, below) is where it is spent.
//
// By induction on n. A one-step fold is over a singleton (SetFoldStageSingleton),
// so x is the one element and nothing remains. A longer fold took some y
// off first and folded s ∖ {y} to c; if y is x there is nothing to move,
// and otherwise x ∈ s ∖ {y}, the induction hypothesis moves x to the
// front of that shorter fold — s ∖ {y} ∖ {x} folds to some w with
// c = f(x, w) — and taking y off s ∖ {x} instead reaches the same remainder
// (DeleteComm), so s ∖ {x} folds to f(y, w), while a = f(y, f(x, w)) is
// f(x, f(y, w)) by the commutation.
var SetFoldStageStep = setFoldStageStepThm{family.Add(registry.ProofEntry{
	Name: "SetFoldStageStep",
	Key:  "prop_72f983ad6793403c",
	Build: family.Theorem(
		Statement{
			Binders: "∀f:(A → B → B). ∀b:B. ∀n:num. ∀s:set(A). ∀a:B. ∀x:A.",
			Hypotheses: []string{
				"∀u v:A. ∀z:B. u ≠ v ⇒ f(u, f(v, z)) = f(v, f(u, z))",
				"set_fold_stage(f, b, s, a, suc(n))",
				"x ∈ s",
			},
			Conclusion: "∃w:B. set_fold_stage(f, b, delete(s, x), w, n) ∧ a = f(x, w)",
		},
		func(arg *Argument, f, b Term, commutes Fact) {
			v := ops(arg.Ctx())
			zeroClause, sucClause := setFoldStageZeroClause(arg), setFoldStageSucClause(arg)
			// The step count stays bound for the induction. The goal spells
			// it n₀ once f and b are stripped off in front of it — Binder takes
			// the statement's name — and the claims below read it as n₀.
			n := arg.Binder("n")
			arg.Induct(n)
			arg.Base(
				"one step: the fold is over a singleton {y}, so x is y, nothing remains, and a = f(x, b)",
				func(d *Argument) {
					s, a, x := d.Fix(), d.Fix(), d.Fix()
					oneStep := d.Assume() // set_fold_stage(f, b, s, a, suc(0)) ∧ x ∈ s
					_, sing := d.Obtain(
						"a one-step fold is over a singleton: s = {y} with a = f(y, b)",
						"∃y:A. s = {y} ∧ a = f(y, b)",
						By(
							oneStep,
							// set_fold_stage(f, b, s, a, suc(0)) ⇔ ∃y. s = {y} ∧ a = f(y, b)
							At(SetFoldStageSingleton, f, b, s, a)))
					only := d.Have(
						"x is the one element, and taking it off leaves nothing",
						"x = y ∧ delete(s, x) = ∅",
						BySets(sing, oneStep))
					d.Take(b)
					d.Show(
						"over nothing the zero-step fold reaches b, and a = f(y, b) is f(x, b)",
						By(
							Normalized,
							only,
							sing,
							zeroClause.At(f, v.Delete.Apply(s, x), b, b))) // the 0 clause at (f, s ∖ {x}, b, b)
				})
			arg.Step(
				"one more step: some y came off first; if y is x nothing moves, else "+
					"the IH puts x first in the shorter fold and commutation recombines",
				func(d *Argument, ih Fact) {
					s, a, x := d.Fix(), d.Fix(), d.Fix()
					moreSteps := d.Assume() // set_fold_stage(f, b, s, a, suc(suc(n))) ∧ x ∈ s
					y, c, first := d.Obtain2(
						"some y ∈ s came off first, and the rest folded to c in suc(n) steps",
						"∃y:A. ∃c:B. y ∈ s ∧ set_fold_stage(f, b, delete(s, y), c, suc(n₀)) ∧ a = f(y, c)",
						By(
							moreSteps,
							sucClause.At(f, s, a, b, d.Term("suc(n₀)")))) // the suc clause at (f, s, a, b, suc(n₀))
					// Settled when y is x: the fold already took x off first.
					distinct := d.Unless(
						d.Term("x = y"),
						"y is x: the fold already took x off first, and c is the remainder's value",
						Given(func(e *Argument, same Fact) {
							e.Take(c)
							e.Show(
								"the first step's own witnesses, read at x",
								By(Normalized, same, first))
						}))
					// Otherwise move x to the front of the fold of s ∖ {y}, then
					// take y off s ∖ {x} instead.
					restY, restX := v.Delete.Apply(s, y), v.Delete.Apply(s, x)
					xInRestY := d.Have(
						"x survives the removal of y",
						"x ∈ delete(s, y)",
						BySets(distinct, moreSteps))
					w, moved := d.Obtain(
						"the induction hypothesis puts x first in the suc(n)-step fold of s ∖ {y}",
						"∃w:B. set_fold_stage(f, b, delete(delete(s, y), x), w, n₀) ∧ c = f(x, w)",
						By(ih.At(restY, c, x), first, xInRestY)) // the IH at (s ∖ {y}, c, x)
					yInRestX := d.Have(
						"and y survives the removal of x",
						"y ∈ delete(s, x)",
						BySets(distinct, first))
					value := d.Term("f(y, w)")
					refolded := d.Have(
						"removing y from s ∖ {x} leaves the same remainder, "+
							"so s ∖ {x} folds to f(y, w) by taking y off first",
						"set_fold_stage(f, b, delete(s, x), f(y, w), suc(n₀))",
						By(
							yInRestX,
							moved,
							At(set_algebra.DeleteComm, s, x, y),  // delete(delete(s, x), y) = delete(delete(s, y), x)
							sucClause.At(f, restX, value, b, n))) // the suc clause at (f, s ∖ {x}, f(y, w), b, n)
					commuted := d.Have(
						"a = f(y, c) = f(y, f(x, w)), and x ≠ y lets the two steps swap",
						"a = f(x, f(y, w))",
						By(Normalized, distinct, first, moved, commutes.At(x, y, w))) // f(x, f(y, w)) = f(y, f(x, w))
					d.Take(value)
					d.Show(
						"f(y, w) is the rearranged fold's remainder value",
						By(refolded, commuted))
				})
		}),
})}

// ---------------------------------------------------------------------------
// SetFoldStageUnique — two folds of one set agree in value and in length
// ---------------------------------------------------------------------------

// SetFoldStageUnique — when the step function commutes on distinct elements,
// any two folds of the same set reach the same value in the same number
// of steps: set_fold_stage is single-valued in (a, n).
//
// By induction on the first length, with the second split into 0 and
// suc(m) at each stage. Two zero-step folds both reach b. A zero-step
// fold says the set is empty, so a fold that takes a step off the same
// set names an element of ∅ — the two mixed cases are contradictions.
// When both take a step, the first took some x off; SetFoldStageStep rearranges
// the second to take that same x off first, and the induction hypothesis
// compares the two folds of s ∖ {x} that remain: same value w, same
// length m, so a₁ = f(x, w) = a₂ and suc(n₁) = suc(m) = n₂.
var SetFoldStageUnique = setFoldStageUniqueThm{family.Add(registry.ProofEntry{
	Name: "SetFoldStageUnique",
	Key:  "prop_77e7582f0c672e45",
	Build: family.Theorem(
		Statement{
			Binders: "∀f:(A → B → B). ∀b:B. ∀n₁ n₂:num. ∀s:set(A). ∀a₁ a₂:B.",
			Hypotheses: []string{
				"∀u v:A. ∀z:B. u ≠ v ⇒ f(u, f(v, z)) = f(v, f(u, z))",
				"set_fold_stage(f, b, s, a₁, n₁)",
				"set_fold_stage(f, b, s, a₂, n₂)",
			},
			Conclusion: "a₁ = a₂ ∧ n₁ = n₂",
		},
		func(arg *Argument, f, b Term, commutes Fact) {
			v := ops(arg.Ctx())
			zeroClause, sucClause := setFoldStageZeroClause(arg), setFoldStageSucClause(arg)
			// The first length stays bound for the induction. The parser reads
			// the headline's n1 as n₁ (a trailing digit is a subscript), and so
			// do the claims below.
			n1 := arg.Binder("n_1")
			arg.Induct(n1)
			arg.Base(
				"the first fold takes no step: s is empty, so the second "+
					"fold cannot take one either, and both values are b",
				func(d *Argument) {
					n2, s, a1, a2 := d.Fix(), d.Fix(), d.Fix(), d.Fix()
					both := d.Assume() // set_fold_stage(f, b, s, a₁, 0) ∧ set_fold_stage(f, b, s, a₂, n₂)
					// Settled when the second fold takes no step either.
					notZero := d.Unless(
						d.Term("n₂ = 0"),
						"two zero-step folds: the 0 clause says each value is b",
						Given(func(e *Argument, isZero Fact) {
							e.Show(
								"the 0 clause at (f, s, a₁, b) and at (f, s, a₂, b)",
								By(isZero, both, zeroClause.At(f, s, a1, b), zeroClause.At(f, s, a2, b)))
						}))
					// Otherwise the second fold takes a step off a set the first
					// fold says is empty.
					m, isSuc := d.Obtain(
						"n₂ is a successor suc(m)",
						"∃m:num. n₂ = suc(m)",
						By(Normalized, notZero, At(peano.Cases, n2))) // n₂ = 0 ∨ ∃m. n₂ = suc(m)
					empty := d.Have(
						"the zero-step fold says s is empty",
						"s = ∅",
						By(both, zeroClause.At(f, s, a1, b))) // the 0 clause at (f, s, a₁, b)
					x, _, second := d.Obtain2(
						"the suc(m)-step fold takes some x ∈ s off first",
						"∃x:A. ∃c:B. x ∈ s ∧ set_fold_stage(f, b, delete(s, x), c, m) ∧ a₂ = f(x, c)",
						By(both, isSuc, sucClause.At(f, s, a2, b, m))) // the suc clause at (f, s, a₂, b, m)
					d.Show(
						"but nothing is in ∅",
						By(empty, second, At(set_basic.NotInEmpty, x)))
				})
			arg.Step(
				"the first fold takes suc(n₁) steps, some x ∈ s first: "+
					"the second fold must take a step too, and can take x first",
				func(d *Argument, ih Fact) {
					n2, s, a1, a2 := d.Fix(), d.Fix(), d.Fix(), d.Fix()
					both := d.Assume() // set_fold_stage(f, b, s, a₁, suc(n₁)) ∧ set_fold_stage(f, b, s, a₂, n₂)
					x, c, first := d.Obtain2(
						"the first fold takes some x ∈ s off first and folds the rest to c in n₁ steps",
						"∃x:A. ∃c:B. x ∈ s ∧ set_fold_stage(f, b, delete(s, x), c, n₁) ∧ a₁ = f(x, c)",
						By(both, sucClause.At(f, s, a1, b, n1))) // the suc clause at (f, s, a₁, b, n₁)
					// Settled when the second fold takes no step: s would be empty.
					notZero := d.Unless(
						d.Term("n₂ = 0"),
						"the second fold takes no step, so s is empty — yet x ∈ s",
						Given(func(e *Argument, isZero Fact) {
							empty := e.Have(
								"the zero-step fold says s is empty",
								"s = ∅",
								By(isZero, both, zeroClause.At(f, s, a2, b))) // the 0 clause at (f, s, a₂, b)
							e.Show(
								"but nothing is in ∅",
								By(empty, first, At(set_basic.NotInEmpty, x)))
						}))
					// Otherwise the second fold takes suc(m) steps: rearrange it to
					// take x first, and compare the two folds of s ∖ {x}.
					m, isSuc := d.Obtain(
						"n₂ is a successor suc(m)",
						"∃m:num. n₂ = suc(m)",
						By(Normalized, notZero, At(peano.Cases, n2))) // n₂ = 0 ∨ ∃m. n₂ = suc(m)
					w, moved := d.Obtain(
						"SetFoldStageStep puts x first in the second fold: s "+
							"∖ {x} folds to some w in m steps, with a₂ = f(x, w)",
						"∃w:B. set_fold_stage(f, b, delete(s, x), w, m) ∧ a₂ = f(x, w)",
						By(
							commutes,
							isSuc,
							both,
							first,
							At(SetFoldStageStep, f, b, m, s, a2, x))) // SetFoldStageStep at (f, b, n := m, s, a := a₂, x)
					agree := d.Have(
						"the induction hypothesis compares the two folds of s ∖ {x}: c = w and n₁ = m",
						"c = w ∧ n₁ = m",
						By(ih.At(m, v.Delete.Apply(s, x), c, w), first, moved)) // the IH at (m, s ∖ {x}, c, w)
					d.Show(
						"so a₁ = f(x, c) = f(x, w) = a₂, and suc(n₁) = suc(m) = n₂",
						By(agree, first, moved, isSuc))
				})
		}),
})}

// ---------------------------------------------------------------------------
// SetFoldStageExists — a finite set has a fold
// ---------------------------------------------------------------------------

// SetFoldStageExists — every finite set is folded by set_fold_stage to some value in
// some number of steps: on finite sets the relation is total. Finite
// induction: ∅ folds to b in no steps, and if t folds to a in n steps
// then insert(x, t), for an x not in t, folds to f(x, a) in suc(n) steps
// by taking x off first — what is left is t again.
var SetFoldStageExists = setFoldStageExistsThm{family.Add(registry.ProofEntry{
	Name: "SetFoldStageExists",
	Key:  "prop_5c0c70f55ff154c",
	Build: family.Theorem(
		Statement{
			Binders: "∀f:(A → B → B). ∀b:B. ∀s:set(A).",
			Hypotheses: []string{
				"finite(s)",
			},
			Conclusion: "∃a:B. ∃n:num. set_fold_stage(f, b, s, a, n)",
		},
		func(arg *Argument, f, b, s Term, finite Fact) {
			v := ops(arg.Ctx())
			zero := arg.Ctx().Numeral(0)
			zeroClause, sucClause := setFoldStageZeroClause(arg), setFoldStageSucClause(arg)
			arg.Show(
				"finite induction carries the property to every finite set, and s is one",
				ByInduction(FiniteInductFresh, finite,
					Case(
						"∅ folds to b in no steps",
						Derive(func(d *Argument) {
							d.Take(b)
							d.Take(zero)
							d.Show(
								"the 0 clause at (f, ∅, b, b): ∅ = ∅ and b = b",
								By(zeroClause.At(f, v.EmptySet(), b, b)))
						})),
					Case(
						"insert(x, t) for a new x: fold t to a in n steps, then take x off first",
						Derive(func(d *Argument) {
							x, t := d.Fix(), d.Fix("t") // the principle's own `s` — a name the section already uses
							carried := d.Assume()       // (∃a n. set_fold_stage(f, b, t, a, n)) ∧ x ∉ t ∧ finite(t)
							_, n, folds := d.Obtain2(
								"t has a fold: to some a in some n steps",
								"∃a:B. ∃n:num. set_fold_stage(f, b, t, a, n)",
								By(carried))
							inserted := d.Have(
								"x is in the enlarged set",
								"x ∈ insert(x, t)",
								BySets())
							removed := d.Have(
								"and taking it back off leaves t, x being new to t",
								"delete(insert(x, t), x) = t",
								BySets(carried))
							value := d.Term("f(x, a)")
							d.Take(value)
							d.Take(d.Term("suc(n)"))
							d.Show(
								"the suc clause at (f, insert(x, t), f(x, a), b, n), "+
									"with x the element taken off and a the rest's value",
								By(folds, inserted, removed, sucClause.At(f, v.Insert.Apply(x, t), value, b, n)))
						})),
				))
		}),
})}

// ---------------------------------------------------------------------------
// SetFoldStageFold — the fold as a function
// ---------------------------------------------------------------------------

// SetFoldStageFold — when the step function commutes on distinct elements,
// the relation set_fold_stage is the graph of a FUNCTION g: the value at s is
// THE value some fold of s produces. g starts at b on ∅ and, at a
// finite set with a chosen element x, peels x off first: g(s) is
// f(x, g(s ∖ {x})).
//
// The function is chosen out of the relation: g(s) := εa. ∃n. a is what
// an n-step fold of s produces. This is well-defined because SetFoldStageExists
// gives a fold for every finite set, so the choice set is inhabited, and
// SetFoldStageUnique makes every fold of one set agree, so the chosen value is
// forced. Both obligations then read the same way: realise the ε against
// a concrete fold and let uniqueness identify the two.
//
// The ∅ clause takes the zero-step fold of ∅ (value b) as the concrete
// witness. The step clause takes the fold SetFoldStageExists supplies for s;
// its length is a successor (a zero-step fold would make s empty, against
// x ∈ s), so SetFoldStageStep rearranges it to take x off first — s ∖ {x} folds
// to some w with the value f(x, w) — and uniqueness identifies g(s) with
// that value and g(s ∖ {x}) with w.
var SetFoldStageFold = setFoldStageFoldThm{family.Add(registry.ProofEntry{
	Name: "SetFoldStageFold",
	Key:  "prop_2dcd37ef83a7f958",
	Build: family.Theorem(
		Statement{
			Binders: "∀f:(A → B → B). ∀b:B.",
			Hypotheses: []string{
				"∀u v:A. ∀z:B. u ≠ v ⇒ f(u, f(v, z)) = f(v, f(u, z))",
			},
			Conclusion: "∃g:(set(A) → B). " +
				"    g(∅) = b ∧ (∀s:set(A). ∀x:A. finite(s) ∧ x ∈ s ⇒ g(s) = f(x, g(delete(s, x))))",
		},
		func(a *Argument, f, b Term, commutes Fact) {
			v := ops(a.Ctx())
			zero := a.Ctx().Numeral(0)
			zeroClause := setFoldStageZeroClause(a)
			// g(t) := THE value some fold of t produces — a choice among the
			// folds of t, which SetFoldStageExists inhabits and SetFoldStageUnique pins.
			g := a.Term("λt:set(A). εa:B. ∃n:num. set_fold_stage(f, b, t, a, n)")
			a.Take(g)
			a.Do(SplitConj(
				Case(
					"∅ folds to b: the zero-step fold of ∅ has value b, and every fold of ∅ agrees with it",
					Derive(func(d *Argument) {
						emptyFold := d.Have(
							"∅ folds to b in no steps",
							"set_fold_stage(f, b, ∅, b, 0)",
							By(zeroClause.At(f, v.EmptySet(), b, b))) // the 0 clause at (f, ∅, b, b)
						// g(∅) is the chosen fold value; realise it against the
						// zero-step fold and let uniqueness force it to b.
						eps, chosen := d.ObtainChosen(
							"∅ has a fold, so the choice is realised",
							"∃a:B. ∃n:num. set_fold_stage(f, b, ∅, a, n)",
							emptyFold)
						len0, foldEps := d.Unpack(chosen) // set_fold_stage(f, b, ∅, g(∅), len0)
						d.Show(
							"so g(∅) and b are two folds of ∅, hence equal",
							By(
								commutes,
								foldEps,
								emptyFold,
								At(SetFoldStageUnique, f, b, len0, zero, v.EmptySet(), eps, b))) // g(∅)=b ∧ len0=0
					})),
				Case(
					"g(s) takes the chosen x off first, so it is f(x, g(s ∖ {x}))",
					Derive(func(d *Argument) {
						s := d.Fix()
						x := d.Fix()
						prem := d.Assume() // finite(s) ∧ x ∈ s
						xIn := d.Have(
							"x is in s",
							"x ∈ s",
							By(prem))
						rest := v.Delete.Apply(s, x)

						// s has a fold, being finite.
						av, nv, foldS := d.Obtain2(
							"s has a fold, being finite",
							"∃av:B. ∃nv:num. set_fold_stage(f, b, s, av, nv)",
							By(prem, At(SetFoldStageExists, f, b, s))) // finite(s) ⇒ ∃a n. set_fold_stage

						// Its length is a successor: a zero-step fold makes s empty,
						// against x ∈ s.
						notZero := d.Unless(
							nv.Eq(zero),
							"if s folded in no steps it would be empty, yet x ∈ s",
							Given(func(e *Argument, isZero Fact) {
								empty := e.Have(
									"a fold of s in no steps says s is empty, by the 0 clause",
									"s = ∅",
									By(Normalized, isZero, foldS, zeroClause.At(f, s, av, b)))
								e.Show(
									"but x ∈ s, and nothing is in ∅",
									By(empty, xIn, At(set_basic.NotInEmpty, x)))
							}))
						m, isSuc := d.Obtain(
							"nv is a successor",
							"∃m:num. nv = suc(m)",
							By(Normalized, notZero, At(peano.Cases, nv))) // nv = 0 ∨ ∃m. nv = suc(m)

						// SetFoldStageStep takes x off the front: s ∖ {x} folds to some w
						// in m steps, and av = f(x, w).
						w, moved := d.Obtain(
							"SetFoldStageStep puts x first: s ∖ {x} folds to w in m steps, with av = f(x, w)",
							"∃w:B. set_fold_stage(f, b, delete(s, x), w, m) ∧ av = f(x, w)",
							By(
								commutes,
								foldS,
								isSuc,
								xIn,
								At(SetFoldStageStep, f, b, m, s, av, x))) // SetFoldStageStep at (f, b, m, s, av, x)

						// g(s) is the chosen fold value of s; uniqueness forces g(s) = av.
						epsS, chosenS := d.ObtainChosen(
							"the chosen fold of s is realised",
							"∃a:B. ∃n:num. set_fold_stage(f, b, s, a, n)",
							foldS)
						lenS, foldEpsS := d.Unpack(chosenS)
						gsEq := d.Have(
							"g(s) is av — two folds of s agree",
							MakeProp(epsS.Eq(av)),
							By(commutes, foldEpsS, foldS, At(SetFoldStageUnique, f, b, lenS, nv, s, epsS, av)))

						// g(s ∖ {x}) is the chosen fold value of s ∖ {x}; uniqueness
						// forces g(s ∖ {x}) = w.
						epsD, chosenD := d.ObtainChosen(
							"the chosen fold of s ∖ {x} is realised",
							"∃a:B. ∃n:num. set_fold_stage(f, b, delete(s, x), a, n)",
							moved)
						lenD, foldEpsD := d.Unpack(chosenD)
						gdEq := d.Have(
							"g(s ∖ {x}) is w — two folds of s ∖ {x} agree",
							MakeProp(epsD.Eq(w)),
							By(commutes, foldEpsD, moved, At(SetFoldStageUnique, f, b, lenD, m, rest, epsD, w)))

						d.Show(
							"so g(s) = av = f(x, w) = f(x, g(s ∖ {x}))",
							By(Normalized, gsEq, gdEq, moved))
					})),
			))
		}),
})}

// ---------------------------------------------------------------------------
// FoldExists — the fold's clauses in insert form
// ---------------------------------------------------------------------------

// FoldExists — the same fold read the way a set is built: a function g
// starting at b on ∅, and reacting to insert by applying the step
// function once — unless the element was already there, in which case
// nothing changes. This is the surface cardinality's FiniteRecursion
// consumes; the delete form (SetFoldStageFold) is turned into the insert form
// here so that the recursion reads along the constructor that builds a
// finite set up rather than the one that takes it apart.
//
// Take SetFoldStageFold's g. Its ∅ clause is inherited. For the insert clause
// on a finite s, split on whether x is already in s: if it is, insert
// leaves s unchanged (InsertAbsorb) and COND selects g(s); if it is not,
// insert(x, s) is finite (FiniteRules), x belongs to it, and deleting x
// again leaves s — so SetFoldStageFold's step reads g(insert(x, s)) = f(x, g(s)),
// which COND selects.
var FoldExists = foldExistsThm{family.Add(registry.ProofEntry{
	Name: "FoldExists",
	Key:  "prop_418f02bcfcc6a446",
	Build: family.Theorem(
		Statement{
			Binders: "∀f:(A → B → B). ∀b:B.",
			Hypotheses: []string{
				"∀u v:A. ∀z:B. u ≠ v ⇒ f(u, f(v, z)) = f(v, f(u, z))",
			},
			Conclusion: "∃g:(set(A) → B). " +
				"    g(∅) = b ∧ (∀x:A. ∀s:set(A). finite(s) ⇒ g(insert(x, s)) = COND(x ∈ s, g(s), f(x, g(s))))",
		},
		func(a *Argument, f, b Term, commutes Fact) {
			v := ops(a.Ctx())
			// SetFoldStageFold hands over the fold as a function g.
			g, gProps := a.Obtain(
				"SetFoldStageFold provides the fold as a function",
				"∃g:(set(A) → B). g(∅) = b ∧ ∀s:set(A). ∀x:A. finite(s) ∧ x ∈ s ⇒ g(s) = f(x, g(delete(s, x)))",
				By(commutes, At(SetFoldStageFold, f, b)))
			a.Take(g)
			gStep := a.Have(
				"g peels a chosen element off a nonempty finite set",
				"∀s:set(A). ∀x:A. finite(s) ∧ x ∈ s ⇒ g₀(s) = f(x, g₀(delete(s, x)))",
				By(gProps))
			a.Do(SplitConj(
				Case(
					"g(∅) = b — inherited from SetFoldStageFold",
					By(gProps)),
				Case(
					"insert clause: how g reacts to adjoining x depends on whether x was already in s",
					Derive(func(d *Argument) {
						x := d.Fix()
						s := d.Fix()
						finite := d.Assume() // finite(s)
						d.Cases(v.SetMember.Apply(x, s))
						d.When(
							"x already in s: insert changes nothing, so COND selects g(s)",
							func(e *Argument, xIn Fact) {
								e.Show(
									"g(insert(x, s)) = g(s), which COND selects",
									By(Normalized, xIn, At(set_algebra.InsertAbsorb, s, x))) // x ∈ s ⇔ insert(x, s) = s
							})
						d.Otherwise(
							"x new to s: insert enlarges s, and g peels x back off",
							func(e *Argument, xNotIn Fact) {
								xInIns := e.Have(
									"x belongs to the enlarged set",
									"x ∈ insert(x, s)",
									BySets())
								delEq := e.Have(
									"deleting x again leaves s, x being new to s",
									"delete(insert(x, s), x) = s",
									BySets(xNotIn))
								peeled := e.Have(
									"g peels x off the enlarged set",
									"g₀(insert(x, s)) = f(x, g₀(delete(insert(x, s), x)))",
									By(
										finite,
										FiniteRules.Inst[element]().At(x, s), // the insert rule at (x, s)
										xInIns,
										gStep.At(v.Insert.Apply(x, s), x))) // gStep at (insert(x, s), x)
								e.Show(
									"so g(insert(x, s)) = f(x, g(s)), which COND selects",
									By(Normalized, xNotIn, peeled, delEq))
							})
					})),
			))
		}),
})}
