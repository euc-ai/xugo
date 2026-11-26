// monoidal.go — the chapter: the fold mechanism.
//
// Seven parts, marked by banners; the fold's interval laws stand in a
// file of their own:
//
// - The language layer
// - The recursion tier: what `iterated_op` IS
// - The evaluation tier: what a fold is actually worth
// - The fold is a HOMOMORPHISM, read on both of its arguments
// - A fold INHERITS a property of the values it combines
// - Carrying a fold from one index set to another
// - Folding a doubly-indexed family, one index at a time or both at
// once

package monoidal

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_algebra"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The language layer
// ---------------------------------------------------------------------------
//
// the language layer: what `monoidal_op op` gives you to compute with, and
// the support — where a function actually differs from the neutral.
// `op_support op f s` carves out of the index set `s` the points the fold
// cannot ignore, and most of this file is what that set is: its membership
// law first, then how it meets the set language. Everything the fold
// itself does with the support belongs to the recursion tier.

// MonoidalOp — the chapter's subject as a STRUCTURE: `monoidal_op(op)`,
// one component, the operation on the carrier, its identity named by
// choice (`neutral_elem(op)`) rather than carried. (The monoid with the
// identity as a second component is algebra/group/comm_monoid, and the
// bridge between the two readings lives there.) Every law below is
// stated over it through the structure door — `∀op:(B → B → B).
// monoidal_op(op) ⇒ <body>`, the body being what the member writes — and
// its proof names `op` before the hypothesis, since the chapter grounds
// its cites at the operation.
var MonoidalOp = family.StructureOf("monoidal_op", "op:(B → B → B)")

// MonoidalAC — what `monoidal_op op` licenses you to compute with: the
// three rearrangement laws AC-normalization runs on — left-commute,
// associativity, commutativity — and then the neutral element from
// either side. The definition carries three of the five (assoc, comm,
// left neutral); the other two are AC consequences of those three.
var MonoidalAC = monoidalACThm{family.Add(registry.ProofEntry{
	Name: "MonoidalAC",
	Key:  "prop_2bf3941d27e8a4b3",
	Build: MonoidalOp.Law(
		"(∀a b c:B. op(a, op(b, c)) = op(b, op(a, c))) ∧ "+
			"(∀a b c:B. op(op(a, b), c) = op(a, op(b, c))) ∧ "+
			"(∀a b:B. op(a, b) = op(b, a)) ∧ "+
			"(∀a:B. op(a, neutral_elem(op)) = a) ∧ "+
			"(∀a:B. op(neutral_elem(op), a) = a)",
		func(a *Argument, op *Arrow2[carrier, carrier, carrier], _ Fact) {
			// The hypothesis is spent where its content lives: unfolding
			// `monoidal_op` deposits the three defining clauses, and the
			// clauses that appear verbatim among the conjuncts discharge
			// on contact.
			a.Do(Unfold(MonoidalOpDef))
			assoc := a.Hyp("∀x y z:B. op(x, op(y, z)) = op(op(x, y), z)")
			comm := a.Hyp("∀x y:B. op(x, y) = op(y, x)")
			leftNeutral := a.Hyp("∀x:B. op(neutral_elem(op), x) = x")
			a.Show(
				"the remaining laws are AC consequences of these three",
				By(Normalized, assoc, comm, leftNeutral))
		}),
})}

// InSupport — membership in the support: the function must do
// something at the point, and the point must be in the index set.
// This is the law every other statement about `op_support` is read
// through.
var InSupport = inSupportThm{family.Add(registry.ProofEntry{
	Name: "InSupport",
	Key:  "prop_2800bc89f28d1d09",
	Build: family.Theorem(
		"∀s:set(A). ∀f:(A → B). ∀op:(B → B → B). ∀x:A. "+
			"    x ∈ op_support(op, f, s) ⇔ f(x) ≠ neutral_elem(op) ∧ x ∈ s",
		func(a *Argument) {
			// `op_support` is opaque to the membership driver: its
			// vocabulary is the set language, so the name has to become
			// a comprehension before the residual is about points.
			a.Do(Unfold(OpSupportDef), BySets())
		}),
})}

// SupportSubset — the support never leaves its index set: it is a
// carve-out, not a construction.
var SupportSubset = supportSubsetThm{family.Add(registry.ProofEntry{
	Name: "SupportSubset",
	Key:  "prop_2eb55d3f5fa12a57",
	Build: family.Theorem(
		"∀s:set(A). ∀f:(A → B). ∀op:(B → B → B). op_support(op, f, s) ⊆ s",
		func(a *Argument) {
			a.Do(Unfold(OpSupportDef), BySets())
		}),
})}

// SupportIdempotent — carving out a second time changes nothing:
// every point of the support already does something.
var SupportIdempotent = supportIdempotentThm{family.Add(registry.ProofEntry{
	Name: "SupportIdempotent",
	Key:  "prop_ac778080c02358c",
	Build: family.Theorem(
		"∀s:set(A). ∀f:(A → B). ∀op:(B → B → B). "+
			"    op_support(op, f, op_support(op, f, s)) = op_support(op, f, s)",
		func(a *Argument) {
			a.Do(Unfold(OpSupportDef), BySets())
		}),
})}

// SupportClauses — the support commutes with the set language: it
// vanishes on ∅, passes through delete, union, intersection and set_difference
// pointwise, insert feeds it a point that stays exactly when the
// function does something there, and an image's support pulls back
// along the map with the summand composed. Seven clauses, each at
// its own index type — one law per constructor, packed into one
// statement.
var SupportClauses = supportClausesThm{family.Add(registry.ProofEntry{
	Name: "SupportClauses",
	Key:  "prop_8b20e5876cf6d23e",
	Build: family.Theorem(
		// The letters here run A..I with the CARRIER as I, preserving
		// the relative order of the row's own type variables: the
		// identity check's bijection search is bounded away above four
		// type variables, so the normalized arrangements must agree
		// outright — and Normalize reads type-variable names into its
		// ordering keys.
		"∀op:(I → I → I). "+
			"    (∀f:(A → I). op_support(op, f, empty_set) = empty_set) ∧ "+
			"    (∀f:(B → I). ∀x:B. ∀s:set(B). "+
			"        op_support(op, f, insert(x, s)) = "+
			"        COND(f(x) = neutral_elem(op), op_support(op, f, s), insert(x, op_support(op, f, s)))) ∧ "+
			"    (∀f:(C → I). ∀x:C. ∀s:set(C). "+
			"        op_support(op, f, delete(s, x)) = delete(op_support(op, f, s), x)) ∧ "+
			"    (∀f:(D → I). ∀s:set(D). ∀t:set(D). "+
			"        op_support(op, f, union(s, t)) = union(op_support(op, f, s), op_support(op, f, t))) ∧ "+
			"    (∀f:(E → I). ∀s:set(E). ∀t:set(E). "+
			"        op_support(op, f, intersection(s, t)) = "+
			"        intersection(op_support(op, f, s), op_support(op, f, t))) ∧ "+
			"    (∀f:(F → I). ∀s:set(F). ∀t:set(F). "+
			"        op_support(op, f, set_difference(s, t)) = "+
			"        set_difference(op_support(op, f, s), op_support(op, f, t))) ∧ "+
			"    (∀f:(H → G). ∀g:(G → I). ∀s:set(H). "+
			"        op_support(op, g, image(f, s)) = image(f, op_support(op, o(g, f), s)))",
		func(a *Argument, op *Arrow2[I, I, I]) {
			a.Do(Expect(SplitConjAll(),
				Case(
					"∅: nothing to carve from",
					Unfold(OpSupportDef),
					BySets()),
				Case(
					"insert: the new point survives exactly when f does something there",
					Unfold(OpSupportDef),
					BySets()),
				Case(
					"delete: removing a point commutes with the carve-out",
					Unfold(OpSupportDef),
					BySets()),
				Case(
					"union: the carve-out distributes",
					Unfold(OpSupportDef),
					BySets()),
				Case(
					"intersection: likewise",
					Unfold(OpSupportDef),
					BySets()),
				Case(
					"set_difference: likewise",
					Unfold(OpSupportDef),
					BySets()),
				Case(
					"image: pulled back along the map, the summand composes",
					Unfold(OpSupportDef),
					Unfold(functions.ComposeApply),
					BySets())))
		}),
})}

// SupportFinite — a finite index set has a finite support. This is
// the guard every fold over a finite set discharges on the way in.
var SupportFinite = supportFiniteThm{family.Add(registry.ProofEntry{
	Name: "SupportFinite",
	Key:  "prop_248ec72b9736852b",
	Build: family.Theorem(
		Statement{
			Binders: "∀op:(B → B → B). ∀s:set(A). ∀f:(A → B).",
			Hypotheses: []string{
				"finite(s)",
			},
			Conclusion: "finite(op_support(op, f, s))",
		},
		func(
			a *Argument,
			op *Arrow2[carrier, carrier, carrier],
			s *Expr[indexSet],
			f *Arrow[index, carrier],
			fin Fact,
		) {
			v := ops(a.Ctx())
			a.Show(
				"the support sits inside s, and a subset of a finite set is finite",
				By(fin, At(SupportSubset, s, f, op), At(finite_set.FiniteSubset, v.OpSupport.Apply(op, f, s), s)))
		}),
})}

// SupportDelta — the support of a delta function: a function that is
// the neutral everywhere except possibly at one point `a` has its
// support inside `{a}` — exactly `op_support(op, f, {a})` when `a` is in
// the index set, and empty otherwise.
var SupportDelta = supportDeltaThm{family.Add(registry.ProofEntry{
	Name: "SupportDelta",
	Key:  "prop_e69f00a9796d4c44",
	Build: family.Theorem(
		"∀op:(B → B → B). ∀s:set(A). ∀f:(A → B). ∀a:A. "+
			"    op_support(op, λx:A. COND(x = a, f(x), neutral_elem(op)), s) = "+
			"    COND(a ∈ s, op_support(op, f, insert(a, empty_set)), empty_set)",
		func(a *Argument) {
			a.Do(Unfold(OpSupportDef), BySets())
		}),
})}

// SupportDeltaFinite — the delta function's support is finite with no
// finiteness asked of the index set: whatever `s` is, at most one
// point survives the carve-out.
var SupportDeltaFinite = supportDeltaFiniteThm{family.Add(registry.ProofEntry{
	Name: "SupportDeltaFinite",
	Key:  "prop_33f7ab9db44d991",
	Build: family.Theorem(
		"∀s:set(A). ∀f:(A → B). ∀op:(B → B → B). ∀a:A. "+
			"    finite(op_support(op, λx:A. COND(x = a, f(x), neutral_elem(op)), s))",
		func(
			arg *Argument,
			s *Expr[indexSet],
			f *Arrow[index, carrier],
			op *Arrow2[carrier, carrier, carrier],
			a *Expr[index],
		) {
			ctx := arg.Ctx()
			v := ops(ctx)
			sing := v.Insert.Apply(a, v.EmptySet)
			singletonFinite := arg.Have(
				"a one-point set is finite",
				"finite(insert(a, empty_set))",
				By(Normalized, finite_set.FiniteRules))
			// The delta law is applied as a DIRECTED rewrite: a plain
			// cite installs the set equation in pointwise-expanded form,
			// where nothing can fire on the finite argument. LeanRw
			// leaves the equation itself standing as its first leaf,
			// which the entry closes.
			arg.Show(
				"the delta law rewrites the support, and both branches of its guard are finite",
				Expect(LeanRw(ctx.Dep(SupportDelta)),
					Case(
						"the delta law itself",
						Cite(SupportDelta)),
					Case(
						"↦ finite(COND(a ∈ s, op_support(op, f, {a}), ∅)), and the guard splits",
						CondRewrite(),
						Expect(SplitConj(),
							Case(
								"a ∈ s: the carve-out of the one-point set",
								By(singletonFinite, At(SupportFinite, op, sing, f))),
							Case(
								"a ∉ s: the empty set",
								By(finite_set.FiniteRules))))))
		}),
})}

// ---------------------------------------------------------------------------
// The recursion tier: what `iterated_op` IS
// ---------------------------------------------------------------------------
//
// The definition folds over the support when that is finite and returns
// the neutral otherwise; this file exposes that case analysis
// (ExpandCases), shows the fold never sees more than the support
// (OnSupport), and derives the recursion clauses at ∅ and insert — first
// bounded at a finite support (ClausesGen), then in the form everything
// downstream uses, at a finite index set (Clauses).

// ClausesGen — the recursion clauses, bounded at a finite SUPPORT: a
// monoidal fold of nothing is the neutral, and inserting a point into
// a set whose support is finite either changes nothing (the point was
// already there) or contributes its factor. The finiteness asked here
// is the definition's own guard, which is what makes this the general
// form — Clauses below trades it for the plain finite(s) everything
// downstream carries.
//
// The engine substance is the recursion theorem for finite sets: its
// statement offers an escape disjunct — "or the operator fails
// left-commutativity somewhere" — and `monoidal_op op` is exactly what
// refutes it, through the AC pack. Everything else is support algebra
// from the language tier.
var ClausesGen = clausesGenThm{family.Add(registry.ProofEntry{
	Name: "ClausesGen",
	Key:  "prop_afd5e965ddf060bd",
	Build: MonoidalOp.Law(
		"∀f:(A → B). "+
			"    (iterated_op(op, empty_set, f) = neutral_elem(op)) ∧ "+
			"    (∀x:A. ∀s:set(A). "+
			"        finite(op_support(op, f, s)) ⇒ "+
			"        iterated_op(op, insert(x, s), f) = "+
			"        COND(x ∈ s, iterated_op(op, s, f), op(f(x), iterated_op(op, s, f))))",
		func(a *Argument, op *Arrow2[carrier, carrier, carrier], mon Fact, f *Arrow[index, carrier]) {
			ctx := a.Ctx()
			v := ops(ctx)
			// The fold operator `λxa. λaa. op(f(xa), aa)`, Go-built: the
			// text parser cannot type a bound closure parameter applied
			// inside a λ, while here the applications are the Arrow-typed
			// closure parameters' own, checked at the binders' declared
			// phantoms.
			xa := ctx.VarAs[index]("xa")
			aa := ctx.VarAs[carrier]("aa")
			lam := Lambda(xa, Lambda(aa, op.Apply(f.Apply(xa), aa)))
			neutralOp := v.NeutralElem.Apply(op)
			a.Do(Expect(SplitConj(),
				Case(
					"the fold of nothing is the neutral",
					Derive(func(b *Argument) {
						suppEmpty := b.Have(
							"the support of the empty set is empty",
							"op_support(op, f, empty_set) = empty_set",
							Unfold(OpSupportDef),
							BySets())
						itsetEmpty := b.Have(
							"the recursion theorem's base — monoidal_op(op) refutes its left-commutativity escape",
							"set_fold(λxa:A. λaa:B. op(f(xa), aa), empty_set, neutral_elem(op)) = neutral_elem(op)",
							By(mon, At(cardinality.FiniteRecursion, lam, v.EmptySet, neutralOp), At(MonoidalAC, op)))
						// The definition folds over the support where that is
						// finite: the support is ∅, finite by the rules, and
						// the fold over ∅ is the base.
						b.Show(
							"the definition's guard is finite(∅), so the fold collapses to the base",
							Unfold(IteratedOpDef),
							suppEmpty.Rw(),
							itsetEmpty.Rw(),
							By(finite_set.FiniteRules))
					})),
				Case(
					"the insert clause: the new point either changes nothing or contributes its factor",
					Derive(func(b *Argument) {
						x := b.FixAs[index]()
						s := b.FixAs[indexSet]()
						fin := b.Assume()
						suppS := v.OpSupport.Apply(op, f, s)
						b.Cases(Equal(f.Apply(x), v.NeutralElem.Apply(op)))
						b.When(
							"f is silent at x, so inserting x moves nothing into the support",
							func(c *Argument, silent Fact) {
								collapse := c.Have(
									"the silent point never enters the support",
									"op_support(op, f, insert(x, s)) = op_support(op, f, s)",
									Unfold(OpSupportDef),
									BySets(silent))
								toSupport := c.Have(
									"the extended fold only sees its support",
									"iterated_op(op, insert(x, s), f) = iterated_op(op, op_support(op, f, insert(x, s)), f)",
									By(OnSupport))
								acrossCollapse := c.Have(
									"which the silent point leaves unchanged",
									"iterated_op(op, op_support(op, f, insert(x, s)), f) = iterated_op(op, op_support(op, f, s), f)",
									By(Normalized, collapse))
								fromSupport := c.Have(
									"and s folds like its own support",
									"iterated_op(op, s, f) = iterated_op(op, op_support(op, f, s), f)",
									By(OnSupport))
								c.Show(
									"either arm of the guard is the same fold",
									CondRewrite(),
									Expect(SplitConj(),
										Case(
											"x ∈ s: both sides fold s",
											By(toSupport, acrossCollapse, fromSupport)),
										Case(
											"x ∉ s: the contributed factor is the neutral, which absorbs on the left",
											By(toSupport, acrossCollapse, fromSupport, silent, mon, At(MonoidalAC, op)))))
							})
						b.Otherwise(
							"f is live at x, so the point genuinely enters the support",
							func(c *Argument, live Fact) {
								extend := c.Have(
									"the live point extends the support",
									"op_support(op, f, insert(x, s)) = insert(x, op_support(op, f, s))",
									Unfold(OpSupportDef),
									BySets(live))
								c.Cases(v.SetMember.Apply(x, s))
								c.When(
									"x was already in s: the live point is already in the support",
									func(d *Argument, member Fact) {
										already := d.Have(
											"so inserting it changes nothing",
											"insert(x, op_support(op, f, s)) = op_support(op, f, s)",
											Unfold(OpSupportDef),
											BySets(live, member))
										toSupport := d.Have(
											"the extended fold only sees its support",
											"iterated_op(op, insert(x, s), f) = iterated_op(op, op_support(op, f, insert(x, s)), f)",
											By(OnSupport))
										acrossAbsorb := d.Have(
											"which absorbs the member",
											"iterated_op(op, op_support(op, f, insert(x, s)), f) = iterated_op(op, op_support(op, f, s), f)",
											By(Normalized, extend, already))
										fromSupport := d.Have(
											"and s folds like its own support",
											"iterated_op(op, s, f) = iterated_op(op, op_support(op, f, s), f)",
											By(OnSupport))
										d.Show(
											"the x ∈ s arm returns the fold over s",
											CondRewrite(),
											Expect(SplitConj(),
												Case(
													"x ∈ s: both sides fold s",
													By(toSupport, acrossAbsorb, fromSupport)),
												Case(
													"x ∉ s: contradicts membership",
													By(member))))
									})
								c.Otherwise(
									"x is new: the recursion step fires",
									func(d *Argument, fresh Fact) {
										step := d.Have(
											"a point outside s is outside the support, so this is the recursion "+
												"theorem's step at the support — monoidal_op(op) again refutes the escape",
											"set_fold(λxa:A. λaa:B. op(f(xa), aa), insert(x, op_support(op, f, s)), neutral_elem(op)) = "+
												"op(f(x), set_fold(λxa:A. λaa:B. op(f(xa), aa), op_support(op, f, s), neutral_elem(op)))",
											By(
												mon,
												fin,
												fresh,
												At(InSupport, s, f, op, x),
												At(cardinality.FiniteRecursion, lam, suppS, neutralOp, x),
												At(MonoidalAC, op)))
										lhsFold := d.Have(
											"the extended fold, expanded: its support is the extension, still finite",
											"iterated_op(op, insert(x, s), f) = "+
												"set_fold(λxa:A. λaa:B. op(f(xa), aa), insert(x, op_support(op, f, s)), neutral_elem(op))",
											// Carrying the extension across the expansion, the
											// resident step equation aligns both sides and the
											// guard resolves against the resident finiteness.
											Unfold(IteratedOpDef),
											extend.Rw(),
											CondRewrite(),
											By(Normalized, fin, finite_set.FiniteRules))
										rhsFold := d.Have(
											"the base fold, expanded at its finite support",
											"iterated_op(op, s, f) = "+
												"set_fold(λxa:A. λaa:B. op(f(xa), aa), op_support(op, f, s), neutral_elem(op))",
											// Expanded, the guard is the support's finiteness,
											// which is the hypothesis.
											Unfold(IteratedOpDef),
											By(fin))
										d.Show(
											"expand, step, contract: the new point contributes its factor",
											CondRewrite(),
											By(fresh, lhsFold, step, rhsFold))
									})
							})
					}))))
		}),
})}

// ExpandCases — the definition, as an equation the chapter can
// compute with: a fold is the fold over its support when that is
// finite, and the neutral otherwise.
var ExpandCases = expandCasesThm{family.Add(registry.ProofEntry{
	Name: "ExpandCases",
	Key:  "prop_57ff70154e2827f2",
	Build: family.Theorem(
		"∀s:set(A). ∀f:(A → B). ∀op:(B → B → B). "+
			"    iterated_op(op, s, f) = "+
			"    COND(finite(op_support(op, f, s)), "+
			"        iterated_op(op, op_support(op, f, s), f), "+
			"        neutral_elem(op))",
		func(a *Argument) {
			ctx := a.Ctx()
			// Unfolding `iterated_op` on both sides leaves the two
			// expansions differing only in a doubled carve-out, which
			// idempotence collapses. The rewrite goes through LeanRw: a
			// plain cite installs the set equation pointwise-expanded,
			// where nothing can fire on a set argument.
			a.Do(Unfold(IteratedOpDef),
				// The rewritten goal closes by reflexivity inside the
				// rewrite; the one leaf left is the law itself.
				Expect(LeanRw(ctx.Dep(SupportIdempotent)),
					Case(
						"idempotence itself",
						Cite(SupportIdempotent))))
		}),
})}

// OnSupport — the fold never sees the points it can ignore: folding
// over the index set and folding over its support are the same fold.
var OnSupport = onSupportThm{family.Add(registry.ProofEntry{
	Name: "OnSupport",
	Key:  "prop_8d713ddc1507f6fe",
	Build: family.Theorem(
		"∀s:set(A). ∀f:(A → B). ∀op:(B → B → B). "+
			"    iterated_op(op, s, f) = iterated_op(op, op_support(op, f, s), f)",
		func(a *Argument) {
			ctx := a.Ctx()
			// Same collapse as ExpandCases: both expansions are the
			// definition's COND, at `s` and at the support, and
			// idempotence identifies their guards and their folds.
			a.Do(Unfold(IteratedOpDef),
				// The rewritten goal closes by reflexivity inside the
				// rewrite; the one leaf left is the law itself.
				Expect(LeanRw(ctx.Dep(SupportIdempotent)),
					Case(
						"idempotence itself",
						Cite(SupportIdempotent))))
		}),
})}

// Clauses — the recursion clauses as everything downstream uses them:
// the guard is plain finiteness of the index set. ClausesGen carries
// the argument; what this member adds is one fact from the language
// tier — a finite set has a finite support — discharging the general
// form's guard. The two clauses quantify their functions separately
// because each lives at its own index type.
//
// Cite this one BARE. It is a packed clause pack, so its inner binders
// prenex-hoist out from under `monoidal_op(op) ⇒` and only `op` remains
// stated: a ground tuple would be a partial grounding binding
// positionally into the wrong slot. The instance a caller means belongs
// in that caller's own claim text instead.
var Clauses = clausesThm{family.Add(registry.ProofEntry{
	Name: "Clauses",
	Key:  "prop_dbcab6591a60860e",
	Build: MonoidalOp.Law(
		"(∀f:(A → B). iterated_op(op, empty_set, f) = neutral_elem(op)) ∧ "+
			"(∀g:(C → B). ∀x:C. ∀s:set(C). "+
			"    finite(s) ⇒ "+
			"    iterated_op(op, insert(x, s), g) = "+
			"    COND(x ∈ s, iterated_op(op, s, g), op(g(x), iterated_op(op, s, g))))",
		func(a *Argument, op *Arrow2[carrier, carrier, carrier], mon Fact) {
			a.Do(Expect(SplitConj(),
				Case(
					"the ∅ clause, inherited outright",
					Derive(func(b *Argument) {
						b.FixAs[Fun[index, carrier]]() // f, named by the statement for the claim texts
						b.Show(
							"the general form's ∅ clause needs no guard",
							By(mon, ClausesGen))
					})),
				Case(
					"the insert clause: a finite set has a finite support",
					Derive(func(b *Argument) {
						g := b.FixAs[Fun[C, carrier]]()
						b.FixAs[C]() // x — the refuter instantiates the general clause at it
						s := b.FixAs[Set[C]]()
						fin := b.Assume()
						b.Show(
							"the general clause, its guard discharged",
							By(mon, fin, At(SupportFinite, op, s, g), ClausesGen))
					}))))
		}),
})}

// OneTurn — the insert clause with its guard already decided. When the
// point laid in is NEW, the fold gives up its value there and folds the
// rest; the general clause states this behind a `COND` on whether the
// point was already present, and every consumer that walks a set one
// fresh point at a time has to settle that guard before it can use the
// clause at all.
var OneTurn = oneTurnThm{family.Add(registry.ProofEntry{
	Name: "OneTurn",
	Key:  "prop_3e5639c1b352dcc9",
	Build: MonoidalOp.Law(
		Statement{
			Binders: "∀s:set(A). ∀x:A. ∀f:(A → B).",
			Hypotheses: []string{
				"finite(s)",
				"x ∉ s",
			},
			Conclusion: "iterated_op(op, insert(x, s), f) = op(f(x), iterated_op(op, s, f))",
		},
		func(
			a *Argument,
			op *Arrow2[carrier, carrier, carrier],
			mon Fact,
			s *Expr[indexSet],
			x *Expr[index],
			f *Arrow[index, carrier],
			finite, fresh Fact,
		) {
			a.Show(
				"the clause's guard is decided by the point being new, and the else branch is the claim",
				By(Normalized, mon, finite, fresh, Clauses))
		}),
})}

// BelowClauses — the recursion clauses read along the naturals below a
// bound, as the bound grows by one: below 0 there is nothing, and
// raising the bound from k to suc k admits exactly the new index k. The
// index set is the half-open range {i | i < n} rather than the interval
// `0 .. n-1` because the interval cannot be empty — at n = 0 it still
// holds 0 — while the range is, so the recursion starts from the fold's
// own ∅ clause and needs no predecessor.
//
// Two recursions meet, as in IntervalClauses: the interval chapter says
// what each range IS as a set — the first is ∅, the second is the range
// below k with k laid in, and k is not already there since nothing is
// below itself — and the fold's recursion evaluates whatever set that
// turns out to be. OneTurn hands the shed factor back on the LEFT of the
// operation where the clause wants it on the right, so the last step is
// commutativity, which MonoidalAC carries.
var BelowClauses = belowClausesThm{family.Add(registry.ProofEntry{
	Name: "BelowClauses",
	Key:  "prop_684e0413fffd6ddc",
	Build: MonoidalOp.Law(Statement{
		Binders: "∀f:(num → B).",
		Conclusion: "iterated_op(op, {i:num | i < 0}, f) = neutral_elem(op) ∧ " +
			"(∀k:num. " +
			"    iterated_op(op, {i:num | i < suc(k)}, f) = op(iterated_op(op, {i:num | i < k}, f), f(k)))",
	},
		func(a *Argument, op *Arrow2[carrier, carrier, carrier], mon Fact, f *Arrow[Nat, carrier]) {
			a.Do(SplitConj(
				Case(
					"below 0: the range is ∅, and the fold over ∅ is the neutral",
					Derive(func(b *Argument) {
						noneBelow := b.Have(
							"no natural stands below 0",
							"{i:num | i < 0} = «emptyNumbers»",
							Cite(num_segment.BelowStrictClauses))
						b.Show(
							"and folding over ∅ returns the neutral — the recursion's ∅ clause",
							// The fold's own recursion, bare for the reason its
							// entry gives: its inner binders hoist out from under
							// `monoidal_op(op) ⇒`, leaving nothing a tuple could ground.
							By(noneBelow, mon, Clauses))
					})),
				Case(
					"below suc k: one new index, k, is laid into the finite range below k",
					Derive(func(b *Argument) {
						k := b.FixAs[Nat]()
						below := b.TermAs[Set[Nat]]("{i:num | i < k}") // the range before the bound is raised
						oneMore := b.Have(
							"the range below suc k is the range below k with k laid in",
							"{i:num | i < suc(k)} = insert(k, {i:num | i < k})",
							Cite(num_segment.BelowStrictClauses))
						finite := b.Have(
							"finitely many naturals stand below k",
							"finite({i:num | i < k})",
							Cite(num_segment.FiniteBelowStrict, k))
						fresh := b.Have(
							"and k is not among them, since nothing is below itself",
							"k ∉ {i:num | i < k}",
							BySets(nat_order.LessThanIrrefl.At(k)))
						b.Show(
							"one turn of the fold's recursion sheds f(k) on the "+
								"left, and the operation is read the other way round",
							By(
								oneMore,
								finite,
								fresh,
								mon,
								// iterated_op(op, insert(k, below), f) = op(f(k), iterated_op(op, below, f))
								OneTurn.At(op, below, k, f),
								// Ground at the operation alone: the five laws bind
								// their own factors.
								MonoidalAC.At(op)))
					})),
			))
		}),
})}

// ---------------------------------------------------------------------------
// The evaluation tier: what a fold is actually worth
// ---------------------------------------------------------------------------
//
// The recursion tier says what `iterated_op` IS; this file computes with it,
// and the laws fall into four groups, in the order they appear below.
//
// What a fold comes to outright, on an index set small or degenerate
// enough to read off: a single point, a set the summand is silent on,
// and a summand silent everywhere but one point.
//
// Which index set it really depends on — an enlargement the summand
// cannot see, the whole type as the limiting case of that, and the
// half-open ranges' own case, a fold below m cut back to below t. All
// three are the support tier read through the fold.
//
// A point pulled back out of a finite fold: the recursion clause run in
// the other direction.
//
// And the transfer laws: an arbitrary relation the operation respects
// is inherited by the fold, of which agreeing summands folding alike is
// the case everything downstream uses; and, across a map to a second
// monoidal carrier, the fold itself is carried.

// Sing — folding over a single point returns the function's value
// there. One turn of the recursion clauses does it: `{x}` is `x`
// inserted into ∅, a set that cannot already hold it, so the clause
// hands back the factor at `x` laid onto the fold of nothing. That fold
// is the neutral, which the operation leaves its other factor
// unchanged against.
var Sing = singThm{family.Add(registry.ProofEntry{
	Name: "Sing",
	Key:  "prop_d9974dd92354a02a",
	Build: MonoidalOp.Law(
		"∀f:(A → B). ∀x:A. iterated_op(op, insert(x, empty_set), f) = f(x)",
		func(
			a *Argument,
			op *Arrow2[carrier, carrier, carrier],
			mon Fact,
			f *Arrow[index, carrier],
			x *Expr[index],
		) {
			oneStep := a.Have(
				"one turn of the recursion, at a point ∅ cannot already hold, "+
					"lays f(x) onto the fold of nothing, which is the neutral",
				"iterated_op(op, insert(x, empty_set), f) = op(f(x), neutral_elem(op))",
				By(Normalized, mon, Clauses, finite_set.FiniteRules, At(set_basic.NotInEmpty, x)))
			a.Show(
				"the neutral on the right leaves the factor unchanged",
				By(mon, oneStep, At(MonoidalAC, op)))
		}),
})}

// EqNeutral — a summand that is the neutral everywhere on the index set
// contributes nothing: its fold is the neutral. The index set is
// arbitrary, and stays so: the recursion's ∅ clause carries no
// finiteness guard, so there is none to discharge.
//
// Two evaluation moves in sequence. The support is where `f` differs
// from the neutral, so the hypothesis says precisely that the carve-out
// is empty; and the fold ignores everything outside its support, so it
// is a fold over ∅ — where the recursion starts.
var EqNeutral = eqNeutralThm{family.Add(registry.ProofEntry{
	Name: "EqNeutral",
	Key:  "prop_3154c6c65a9efb7d",
	Build: MonoidalOp.Law(
		Statement{
			Binders: "∀s:set(A). ∀f:(A → B).",
			Hypotheses: []string{
				"∀x:A. x ∈ s ⇒ f(x) = neutral_elem(op)",
			},
			Conclusion: "iterated_op(op, s, f) = neutral_elem(op)",
		},
		func(
			a *Argument,
			op *Arrow2[carrier, carrier, carrier],
			mon Fact,
			s *Expr[indexSet],
			f *Arrow[index, carrier],
			silent Fact,
		) {
			empty := a.Have(
				"every point of s is silent, so nothing survives the carve-out",
				"op_support(op, f, s) = empty_set",
				Unfold(OpSupportDef),
				BySets(silent))
			overEmpty := a.Have(
				"so the fold is one over the empty set",
				"iterated_op(op, s, f) = iterated_op(op, empty_set, f)",
				// Normalized: the resident carve-out equation rewrites the
				// cited instance's right-hand side, and the two sides then
				// coincide.
				By(Normalized, empty, At(OnSupport, s, f, op)))
			a.Show(
				"which the recursion's ∅ clause answers with the neutral",
				By(mon, overEmpty, Clauses))
		}),
})}

// Delta — a summand that is the neutral everywhere except possibly at
// one point contributes nothing but its value there. The fold is first
// pushed onto its support, which the language tier already knows for
// such a summand: at most the one point `a` survives, and only when the
// index set holds it. That leaves a guard whose two branches the
// recursion tier evaluates outright — a fold over a one-point set on
// one side, a fold over nothing on the other.
var Delta = deltaThm{family.Add(registry.ProofEntry{
	Name: "Delta",
	Key:  "prop_20b377206afe6f4",
	Build: MonoidalOp.Law(Statement{
		Binders:    "∀s:set(A). ∀f:(A → B). ∀a:A.",
		Conclusion: "iterated_op(op, s, «deltaSummand») = COND(a ∈ s, f(a), neutral_elem(op))",
		Abbrev: Abbrev{
			{Name: "deltaSummand", Text: "λx:A. COND(x = a, f(x), neutral_elem(op))"},
		},
	},
		func(
			arg *Argument,
			op *Arrow2[carrier, carrier, carrier],
			mon Fact,
			s *Expr[indexSet],
			f *Arrow[index, carrier],
			a *Expr[index],
		) {
			v := ops(arg.Ctx())
			// The summand as a term, for the ground cites — parsed from
			// the SAME spelling the claims use, so the term and the text
			// cannot drift — and the one-point set it can survive on.
			delta := arg.TermAs[Fun[index, carrier]]("«deltaSummand»")
			onePoint := v.Insert.Apply(a, v.EmptySet)

			onSupport := arg.Have(
				"the fold never sees more than its support",
				"iterated_op(op, s, «deltaSummand») = "+
					"iterated_op(op, op_support(op, «deltaSummand», s), «deltaSummand»)",
				By(OnSupport))
			deltaSupport := arg.Have(
				"and this summand is silent off a, so its support is the "+
					"carve-out at {a} — or nothing, when the index set misses a",
				"op_support(op, «deltaSummand», s) = "+
					"COND(a ∈ s, op_support(op, f, insert(a, empty_set)), empty_set)",
				By(SupportDelta))
			arg.Show(
				"carrying the fold onto that support leaves the guard, and each of its branches evaluates",
				onSupport.Rw(),
				deltaSupport.Rw(),
				CondRewrite(),
				Expect(SplitConj(),
					Case(
						"a ∈ s: the surviving point is a, and the summand is f(a) there",
						Derive(func(b *Argument) {
							sameSupport := b.Have(
								"the summand and f carve the same support out of {a}: "+
									"the guard holds at a, and {a} has nowhere else to differ",
								"op_support(op, «deltaSummand», insert(a, empty_set)) = op_support(op, f, insert(a, empty_set))",
								Unfold(OpSupportDef),
								BySets())
							// Normalized: the one-point law arrives with its
							// summand still un-applied, and it is the β-step
							// that turns it into the guard at a — which holds.
							b.Show(
								"so the fold runs over {a} itself, and a one-point fold reads its summand there",
								By(Normalized, mon, sameSupport, At(OnSupport, onePoint, delta, op), Sing.At(op, delta, a)))
						})),
					Case(
						"a ∉ s: nothing survives, and the fold of nothing is the neutral",
						By(mon, Clauses))))
		}),
})}

// Superset — a fold cannot see an enlargement of its index set that
// the summand cannot see: if `u` sits inside `v` and `f` is the
// neutral at every point `v` gains, the two folds agree. All the
// content is that the two index sets carve out the SAME support;
// OnSupport then carries each fold onto that common set. That a fold
// depends on its support alone is definitional, not monoidal.
var Superset = supersetThm{family.Add(registry.ProofEntry{
	Name: "Superset",
	Key:  "prop_d657dcb93b8d522",
	Build: family.Theorem(
		Statement{
			Binders: "∀op:(B → B → B). ∀u v:set(A). ∀f:(A → B).",
			Hypotheses: []string{
				"u ⊆ v",
				"∀x:A. x ∈ v ∧ x ∉ u ⇒ f(x) = neutral_elem(op)",
			},
			Conclusion: "iterated_op(op, u, f) = iterated_op(op, v, f)",
		},
		func(
			a *Argument,
			op *Arrow2[carrier, carrier, carrier],
			u, v *Expr[indexSet],
			f *Arrow[index, carrier],
			sub, silent Fact,
		) {
			// Both inclusions are about which points survive the
			// carve-out, so the membership driver settles them once
			// `op_support` is a comprehension — with the two hypotheses
			// passed as premises, since BySets clears the context.
			sameSupport := a.Have(
				"the supports coincide — u ⊆ v gives one inclusion, and "+
					"a point of v outside u is silent, so it lies in neither",
				"op_support(op, f, u) = op_support(op, f, v)",
				Unfold(OpSupportDef),
				BySets(sub, silent))
			a.Show(
				"each fold sees only its own support, and those two supports are one set",
				By(
					sameSupport,
					At(OnSupport, u, f, op), // iterated_op(op, u, f) = iterated_op(op, op_support(op, f, u), f)
					At(OnSupport, v, f, op), // iterated_op(op, v, f) = iterated_op(op, op_support(op, f, v), f)
				))
		}),
})}

// Univ — an index set that already holds every point the function
// speaks at folds to the same value as the whole type does. The
// enlargement law does all the work: a fold is unchanged by points the
// function is silent at, and here the enlargement is `s` up to `𝕌`,
// which costs nothing since `𝕌` is above everything. What the
// hypothesis buys is the silence — read through `InSupport`, a point of
// `𝕌` lying outside `s` cannot be in the support, so the function is
// neutral there.
var Univ = univThm{family.Add(registry.ProofEntry{
	Name: "Univ",
	Key:  "prop_54316ae2f248ffdd",
	Build: MonoidalOp.Law(
		Statement{
			Binders: "∀s:set(A). ∀f:(A → B).",
			Hypotheses: []string{
				"op_support(op, f, 𝕌) ⊆ s",
			},
			Conclusion: "iterated_op(op, s, f) = iterated_op(op, 𝕌, f)",
		},
		func(
			a *Argument,
			op *Arrow2[carrier, carrier, carrier],
			mon Fact,
			s *Expr[indexSet],
			f *Arrow[index, carrier],
			sub Fact,
		) {
			v := ops(a.Ctx())
			// `InSupport` is cited bare: the claim quantifies over the
			// point, so there is no witness to hand it.
			silent := a.Have(
				"outside s the function is silent — a point it speaks at "+
					"would be in the support, and the support sits inside s",
				"∀x:A. x ∈ 𝕌 ∧ x ∉ s ⇒ f(x) = neutral_elem(op)",
				BySets(sub, InSupport))
			a.Show(
				"so widening s to 𝕌 adds only silent points, and the fold does not move",
				By(
					mon,
					silent,
					At(set_order.SubsetUniv, s), // s ⊆ 𝕌
					At(Superset, op, s, v.Universe, f)))
		}),
})}

// BelowTruncate — a fold over the numbers below m whose summands from t
// on are all the neutral element is the fold over the numbers below t.
//
// The range below t sits inside the range below m, and what the larger
// range adds are the indices from t on, where the summands are silent;
// Superset says exactly that such summands do not move a fold.
var BelowTruncate = belowTruncateThm{family.Add(registry.ProofEntry{
	Name: "BelowTruncate",
	Key:  "prop_607fe660a4a3642f",
	Build: family.Theorem(
		Statement{
			Binders: "∀op:(B → B → B). ∀m t:num. ∀f:(num → B).",
			Hypotheses: []string{
				"t ≤ m",
				"∀i:num. t ≤ i ∧ i < m ⇒ f(i) = neutral_elem(op)",
			},
			Conclusion: "iterated_op(op, {i:num | i < m}, f) = iterated_op(op, {i:num | i < t}, f)",
		},
		func(a *Argument, op *Arrow2[carrier, carrier, carrier], m, t *Expr[Nat], f *Arrow[Nat, carrier],
			within, silentFromT Fact) {
			narrower := a.Have(
				"the range below t sits inside the range below m",
				"{i:num | i < t} ⊆ {i:num | i < m}",
				Derive(func(b *Argument) {
					b.Do(Unfold(set_basic.SubsetDef))
					b.Fix("j")
					inRange := b.Assume()
					belowT := b.Have(
						"j lies below t",
						"j < t",
						BySets(inRange))
					belowM := b.Have(
						"so below m",
						"j < m",
						By(belowT, within, nat_order.LessThanLessEqTrans))
					b.Show(
						"which is membership in the wider range",
						BySets(belowM))
				}))
			silent := a.Have(
				"what the wider range adds are the indices from t on, where the summands are silent",
				"∀j:num. j ∈ {i:num | i < m} ∧ j ∉ {i:num | i < t} ⇒ f(j) = neutral_elem(op)",
				Derive(func(b *Argument) {
					b.Fix("j")
					past := b.Assume()
					between := b.Have(
						"j lies from t on and below m",
						"t ≤ j ∧ j < m",
						BySets(past, nat_order.NotLessThan))
					b.Show(
						"so its summand is the neutral element",
						By(silentFromT, between))
				}))
			a.Show(
				"so the wider fold is the narrower one",
				Symm(),
				By(narrower, silent, Superset))
		}),
})}

// Delete — a fold takes each point of its index set exactly once, so a
// point the set already holds can be split off: fold what is left, and
// multiply that point's factor back in by hand.
//
// The recursion clause says how a fold grows when a point is INSERTed,
// and this law is that clause read in the other direction. All the work
// is arranging for it to apply at the smaller set: it has to be finite,
// and the point has to be genuinely new in it — which it is, having just
// been removed.
var Delete = deleteThm{family.Add(registry.ProofEntry{
	Name: "Delete",
	Key:  "prop_165dbc559b005e74",
	Build: MonoidalOp.Law(
		Statement{
			Binders: "∀s:set(A). ∀f:(A → B). ∀a:A.",
			Hypotheses: []string{
				"finite(s)",
				"a ∈ s",
			},
			Conclusion: "op(f(a), iterated_op(op, delete(s, a), f)) = iterated_op(op, s, f)",
		},
		func(
			arg *Argument,
			op *Arrow2[carrier, carrier, carrier],
			mon Fact,
			s *Expr[indexSet],
			f *Arrow[index, carrier],
			a *Expr[index],
			holds Fact,
		) {
			// `holds` carries both facts about the index set — its
			// finiteness and that it has `a` — one spent on each step
			// below. Freshness picks the operation branch of the clause's
			// COND.
			grow := arg.Have(
				"what is left of s is finite and a is new there, so the "+
					"recursion clause puts a back, at the cost of the factor f(a)",
				"op(f(a), iterated_op(op, delete(s, a), f)) = iterated_op(op, insert(a, delete(s, a)), f)",
				By(mon, holds, finite_set.FiniteDelete, At(set_basic.InDelete, s, a, a), OneTurn))

			arg.Show(
				"and the set it puts a back into is s, which held a all "+
					"along, so the split fold and the whole fold are the same fold",
				By(grow, holds, At(set_algebra.InsertDelete, s, a)))
		}),
})}

// Related — what a relation has to survive to reach the fold: the
// neutral, and the operation in both arguments at once. Given those,
// two summands related at every point of a finite index set have
// related folds.
//
// Almost everything the fold's algebra says about a PAIR of folds is
// one choice of R here, so this is the chapter's transfer principle
// rather than one more clause. Its proof is the induction the recursion
// clauses were built for, run in the STRONG form because the step wants
// exactly what that form grants and ordinary induction does not: the
// point being laid in is new, which is what decides the insert clause's
// guard, and the set it is laid into is finite, which is that clause's
// own hypothesis.
//
// The pointwise premise travels INSIDE the induction property rather
// than beside it, and that is forced: the step spends it at the smaller
// set to reach the inductive conclusion, and must read it again at the
// enlarged one, so it cannot be discharged before the induction starts.
//
// `Closed` (below) is this member's UNARY companion: the same
// transfer architecture at a property the operation survives, where
// this one carries a relation it respects.
var Related = relatedThm{family.Add(registry.ProofEntry{
	Name: "Related",
	Key:  "prop_a69565d8fbf75079",
	Build: MonoidalOp.Law(Statement{
		Binders: "∀R:(B → B → bool). ∀s:set(A). ∀f g:(A → B).",
		Hypotheses: []string{
			"∀x₁ y₁ x₂ y₂:B. R(x₁, x₂) ∧ R(y₁, y₂) ⇒ R(op(x₁, y₁), op(x₂, y₂))",
			"R(neutral_elem(op), neutral_elem(op))",
			"finite(s)",
			"∀x:A. x ∈ s ⇒ R(f(x), g(x))",
		},
		Conclusion: "R(iterated_op(op, s, f), iterated_op(op, s, g))",
	},
		func(
			a *Argument,
			op *Arrow2[carrier, carrier, carrier],
			mon Fact,
			R *Arrow2[carrier, carrier, Bool],
			s *Expr[indexSet],
			f, g *Arrow[index, carrier],
			opCarriesR, neutralsRelated, sFinite, related Fact,
		) {
			reached := a.Have(
				"so the property reaches every finite index set, and s is one of them",
				"(∀y:A. y ∈ s ⇒ R(f(y), g(y))) ⇒ R(iterated_op(op, s, f), iterated_op(op, s, g))",
				// `sFinite` names the set the property is read at, and
				// discharges the principle's own guard.
				ByInduction(finite_set.FiniteInductFresh,
					sFinite,

					Case(
						"∅: each side folds to the neutral, and R relates the neutral to itself",
						// The pointwise premise has nothing to say about ∅ and is
						// spent nowhere in this case.
						By(Normalized, neutralsRelated, mon, Clauses)),

					Case(
						"insert: the point laid in contributes R-related factors to R-related folds",
						Derive(func(b *Argument) {
							// The principle's own set binder is `s`, which the
							// section holds — so the induction set is NAMED.
							x, u := b.FixAs[index](), b.FixAs[indexSet]("u")
							carried := b.Assume() // the property at u, x ∉ u, and finite(u)
							agree := b.Assume()   // R between f and g everywhere on insert(x, u)

							here := b.Have(
								"f and g are related at the point laid in",
								"R(f(x), g(x))",
								By(agree.At(x), At(set_basic.InInsert, u, x, x)))

							below := b.Have(
								"and at every point u already had",
								"∀y:A. y ∈ u ⇒ R(f(y), g(y))",
								// Bare: the membership law is wanted at the point
								// the negated claim names, which nothing here spells.
								By(agree, set_basic.InInsert))

							smaller := b.Have(
								"so the property does apply at u, and the two folds over u are related",
								"R(iterated_op(op, u, f), iterated_op(op, u, g))",
								By(carried, below))

							splitF := b.Have(
								"the enlarged fold of f factors out the new point",
								"iterated_op(op, insert(x, u), f) = op(f(x), iterated_op(op, u, f))",
								// `carried` supplies both conditions the insert
								// clause asks for: finite(u), and the x ∉ u that
								// settles its guard the way this branch needs.
								By(mon, carried, OneTurn))
							splitG := b.Have(
								"and so does the enlarged fold of g",
								"iterated_op(op, insert(x, u), g) = op(g(x), iterated_op(op, u, g))",
								By(mon, carried, OneTurn))

							b.Show(
								"and op carries R from those two factors to their two products",
								By(
									opCarriesR.At(
										b.TermAs[carrier]("f(x)"), b.TermAs[carrier]("iterated_op(op, u, f)"),
										b.TermAs[carrier]("g(x)"), b.TermAs[carrier]("iterated_op(op, u, g)")),
									here,
									smaller,
									splitF,
									splitG))
						}))))
			a.Show(
				"and f and g are related everywhere on s",
				By(reached, related))
		}),
})}

// Congruence — two summands agreeing at every point of the index set
// have the same fold. No finiteness is asked anywhere, and that is what
// shapes the proof: Related, the transfer principle this would otherwise
// be one instance of, needs a finite set, so it cannot carry the theorem
// on its own.
//
// What the hypothesis supplies for free is that `g` and `f` are silent
// at exactly the same points — so the two folds are already folds over
// ONE set, the common support. From there the definition's own case
// analysis splits the work: when that support is finite Related carries
// equality across it, equality being a relation `op` respects; when it
// is not, the definition returns the neutral on both sides and there is
// nothing to compare.
var Congruence = congruenceThm{family.Add(registry.ProofEntry{
	Name: "Congruence",
	Key:  "prop_9aba5e7b995ba4d2",
	Build: MonoidalOp.Law(
		Statement{
			Binders: "∀s:set(A). ∀g f:(A → B).",
			Hypotheses: []string{
				"∀x:A. x ∈ s ⇒ g(x) = f(x)",
			},
			Conclusion: "iterated_op(op, s, g) = iterated_op(op, s, f)",
		},
		func(
			a *Argument,
			op *Arrow2[carrier, carrier, carrier],
			mon Fact,
			s *Expr[indexSet],
			g, f *Arrow[index, carrier],
			agree Fact,
		) {
			v := ops(a.Ctx())

			// The set both folds are really taken over, named once: it is
			// what the split below asks finiteness of, and the set Related
			// is grounded at.
			common := v.OpSupport.Apply(op, g, s)

			// The relation Related is taken at. Its two standing premises —
			// that R relates the neutral to itself, and that `op` carries R
			// in both arguments — are reflexivity and congruence at this R,
			// so they ride along inside the cite rather than being proved.
			equality := a.TermAs[Fun2[carrier, carrier, Bool]]("λu:B. λv:B. u = v")

			sameSupport := a.Have(
				"agreeing on s, g and f are silent at exactly the same points of it",
				"op_support(op, g, s) = op_support(op, f, s)",
				Unfold(OpSupportDef),
				BySets(agree))

			finite := a.Assuming(
				v.Finite.Apply(common),
				"an infinite common support: the definition's guard fails on both sides at once",
				Given(func(b *Argument, infinite Fact) {
					b.Show(
						"so each fold is the else branch of the definition's own case analysis — the neutral",
						By(infinite, sameSupport, At(ExpandCases, s, g, op), At(ExpandCases, s, f, op)))
				}))

			foldsAgree := a.Have(
				"across a finite support the transfer principle applies, and equality transfers",
				"iterated_op(op, op_support(op, g, s), g) = iterated_op(op, op_support(op, g, s), f)",
				// InSupport is cited BARE: what the transfer principle asks
				// is that g and f agree at every point of the support, and
				// the point its negation names is one nothing here spells.
				By(finite, mon, agree, At(Related, op, equality, common, g, f), InSupport))

			a.Show(
				"and each side folds like its own support, which is that same set",
				By(foldsAgree, sameSupport, At(OnSupport, s, g, op), At(OnSupport, s, f, op)))
		}),
})}

// Homomorphic — a map to a second monoidal carrier that fixes the
// neutral and carries the operation to the operation carries the fold:
// the image of a fold at `op` is the fold of the images at `op2`.
//
// This is `Related` read at TWO operations, and the argument shows why
// the two hypotheses are the ones a homomorphism is asked for: the
// fold's recursion has exactly two clauses, and each spends one of them
// — the ∅ clause that `h` fixes the neutral, the insert clause that `h`
// crosses the operation. Nothing else about `h` is used.
//
// The two hypotheses on `h` do NOT travel inside the induction
// property, where `Related` and `Closed` must carry theirs: they speak
// of `h` alone and never of the index set, so they stay resident and
// the property is the bare equation. That is the whole difference, and
// the reason this member is the shorter one.
//
// The induction is run in the STRONG form because the insert step wants
// precisely what that form grants: the point laid in is new, which
// decides the recursion clause's guard, and the set it is laid into is
// finite, which is that clause's own hypothesis.
var Homomorphic = homomorphicThm{family.Add(registry.ProofEntry{
	Name: "Homomorphic",
	Key:  "prop_2aa8410cec9d0fb4",
	Build: MonoidalOp.Law(
		Statement{
			Binders: "∀op₂:(C → C → C). ∀h:(B → C). ∀s:set(A). ∀F:(A → B).",
			Hypotheses: []string{
				"monoidal_op(op₂)",
				"h(neutral_elem(op)) = neutral_elem(op₂)",
				"∀a b:B. h(op(a, b)) = op₂(h(a), h(b))",
				"finite(s)",
			},
			Conclusion: "h(iterated_op(op, s, F)) = iterated_op(op₂, s, λi:A. h(F(i)))",
		},
		func(a *Argument, op *Arrow2[carrier, carrier, carrier], mon Fact,
			op2 *Arrow2[C, C, C], h *Arrow[carrier, C], s *Expr[indexSet], F *Arrow[index, carrier],
			mon2, fixesNeutral, crossesOp, finite Fact) {
			a.Show(
				"so h carries the fold over every finite index set, and s is one of them",
				// `finite` names the set the property is read at, and
				// discharges the principle's own guard.
				ByInduction(finite_set.FiniteInductFresh, finite,

					Case(
						"∅: each fold is the neutral its own operation starts "+
							"from, and h carries one to the other by hypothesis",
						Derive(func(b *Argument) {
							emptyLeft := b.Have(
								"the fold of F over nothing is op's neutral",
								"iterated_op(op, empty_set, F) = neutral_elem(op)",
								By(mon, Clauses))
							emptyRight := b.Have(
								"and the fold of the images over nothing is op2's",
								"iterated_op(op₂, empty_set, λi:A. h(F(i))) = neutral_elem(op₂)",
								By(mon2, Clauses))
							b.Show(
								"so the two sides are those two neutrals, which h was assumed to identify",
								By(Normalized, fixesNeutral, emptyLeft, emptyRight))
						})),

					Case(
						"insert: the new point's factor comes out of both folds, "+
							"and h crosses the operation between it and the rest",
						Derive(func(b *Argument) {
							b.FixAs[index]("x")    // the point laid in
							b.FixAs[indexSet]("u") // the set it enlarges
							carried := b.Assume()  // h carries the fold over u, x ∉ u, finite(u)

							leftTurn := b.Have(
								"the enlarged fold of F gives up the new point's factor",
								"iterated_op(op, insert(x, u), F) = op(F(x), iterated_op(op, u, F))",
								// `carried` supplies both conditions the insert
								// clause asks for: finite(u), and the x ∉ u that
								// settles its guard the way this branch needs.
								By(mon, carried, OneTurn))
							rightTurn := b.Have(
								"and the enlarged fold of the images gives up that factor's image",
								"iterated_op(op₂, insert(x, u), λi:A. h(F(i))) = op₂(h(F(x)), iterated_op(op₂, u, λi:A. h(F(i))))",
								By(mon2, carried, OneTurn))

							b.Show(
								"and h splits across the operation, leaving the fold it already carried over u",
								By(crossesOp, carried, leftTurn, rightTurn))
						}))))
		}),
})}

// ---------------------------------------------------------------------------
// The fold is a HOMOMORPHISM, read on both of its arguments
// ---------------------------------------------------------------------------
//
// On the index set: `Union` splits a fold across two sets that share
// nothing, `Diff` gets the same splitting at a subset by making the
// two halves itself, `Split` at the two halves a test cuts, and
// `UnionIntersection` at two sets that need not be apart at all — the
// overlap's fold being exactly what the two separate folds
// double-count. On the summand: `Pointwise` splits a fold across two
// summands combined at each point, and `Swap` is that reading carried
// to a double fold, where either index set may be taken first. The
// four index-set laws land at `op(fold, fold)`, which is what makes
// them one subject rather than four theorems; `Pointwise` lands there
// too, on the other argument. `Swap` is the odd one and worth the
// notice: it equates two double folds, with no `op` at either root,
// being the summand-side reading iterated rather than applied.
//
// The other face of the fold — that it INHERITS a property of the
// values it combines — is the subject of the part below.
//
// Three habits recur below and are stated here rather than at each
// member.
//
// Statements and claims are written as LITERALS — a misspelled name
// fails loudly (the claim path's undeclared-free assert), and a
// drifted phrase fails at replay. A named Go const carries a spelling
// only where several sites must agree character for character
// (`acceptedHalf`, `choosingSummand`, `emptySecond`); everything else
// is written where it is read.
//
// Where a member runs the strong induction at a claim that IS the
// principle's conclusion — its ∀ over index sets still standing — the
// principle is cited bare, its property is read off the claim, and the
// two obligations ride along beside it with nothing else needed: ByInduction installs the
// principle as its file states it, and the terminal close is the
// discharge of that implication (naming the property with `DenotedAs`
// measured inert at both such sites).
//
// And where a member takes one turn of the recursion, the fact it
// needs is the insert clause with its guard already decided — so the
// premise list carries the point's freshness beside the finiteness,
// the first settling the clause's `COND` and the second being the
// clause's own hypothesis.
//
// Three of the six walk the index set through the strong finite
// induction. `Diff`, `Split` and `UnionIntersection` do not, and are
// worth reading first for it: each is `Union` read at a decomposition
// it builds itself — once for `Diff`, twice for the other two, which
// additionally spend `Congruence` on the halves. Which decomposition
// is not free: `UnionIntersection` cuts `t` rather than `s` precisely
// because that leaves ONE monoid law standing at the end, where the
// other cut leaves a rearrangement the refuter does not finish.

// Union — two index sets with no point in common fold to the two folds
// combined. Both have to be finite, that being where the recursion
// reaches; and they have to be apart, or a shared point would be
// counted twice.
//
// The induction is on the LEFT set with the right one held fixed, and
// that choice is what keeps the argument short: growing the left set by
// a point is exactly the shape `set_algebra.DisjointInsert` and
// `set_algebra.InsertUnionEq` are stated at, so neither commutativity of
// ∪ nor symmetry of disjoint is wanted anywhere. It runs in the STRONG
// form because the step wants precisely what that form grants — the
// point laid in is new, which is what decides the recursion clause's
// guard, and the set it is laid into is finite, which is that clause's
// own hypothesis.
//
// The disjointness travels INSIDE the induction property rather than
// beside it, and that is forced: the step spends it at the smaller set
// to reach the inductive conclusion, and must read it again at the
// enlarged one, so it cannot be discharged before the induction starts.
var Union = unionThm{family.Add(registry.ProofEntry{
	Name: "Union",
	Key:  "prop_d783d15bd5476e90",
	Build: MonoidalOp.Law(
		Statement{
			Binders: "∀s t:set(A). ∀f:(A → B).",
			Hypotheses: []string{
				"finite(s)",
				"finite(t)",
				"disjoint(s, t)",
			},
			Conclusion: "iterated_op(op, s ∪ t, f) = op(iterated_op(op, s, f), iterated_op(op, t, f))",
		},
		func(
			a *Argument,
			op *Arrow2[carrier, carrier, carrier],
			mon Fact,
			s, t *Expr[indexSet],
			f *Arrow[index, carrier],
			finiteS, finiteT, disjoint Fact,
		) {
			a.Show(
				"so every finite index set splits off from t, and s is one of them",
				ByInduction(finite_set.FiniteInductFresh, finiteS, Generalizing(disjoint),

					Case(
						"∅: there is nothing to split off — the fold of nothing is the neutral, which the operation drops",
						Derive(func(b *Argument) {
							b.Assume() // the disjointness, vacuous at ∅ and spent nowhere

							// Named, then rewritten with: a cited set equation
							// installs pointwise-expanded, and in that form it
							// cannot fire on a fold's set argument.
							absorb := b.Have(
								"joining nothing to t leaves t",
								"∅ ∪ t = t",
								By(At(set_algebra.UnionEmpty, t)))

							b.Show(
								"so the left side is the fold over t, and on the right the empty fold contributes the neutral",
								absorb.Rw(),
								By(mon, Clauses, At(MonoidalAC, op)))
						})),

					Case(
						"insert: a point laid into the left set misses the "+
							"right one too, so it comes back out of both folds alike",
						Derive(func(b *Argument) {
							// The principle's own set binder is `s`, which the
							// section holds — so the induction set is NAMED.
							x := b.FixAs[index]()
							u := b.FixAs[indexSet]("u")
							carried := b.Assume() // the property at u, x ∉ u, and finite(u)
							grown := b.Assume()   // insert(x, u) is apart from t

							split := b.Have(
								"the disjointness splits at the point laid in: x misses "+
									"t, and what is left of the left set is still apart from it",
								"x ∉ t ∧ disjoint(u, t)",
								By(grown, set_algebra.DisjointInsert))

							fresh := b.Have(
								"the point is new in the join as well — new in u by the "+
									"strong rule's own strengthening, outside t by disjointness",
								"x ∉ u ∪ t",
								By(carried, split, At(set_basic.InUnion, u, t, x)))

							joinFinite := b.Have(
								"and the join is finite, both halves being so",
								"finite(u ∪ t)",
								By(carried, finiteT, At(finite_set.FiniteUnion, u, t)))

							b.Show(
								"so the new point travels out of the joint fold, across "+
									"the split, and back into the fold over insert(x, u)",
								CalcEq(
									Leg(
										b.Term("iterated_op(op, insert(x, u ∪ t), f)"),
										"joining t onto insert(x, u) is laying x into the join",
										By(Normalized, At(set_algebra.InsertUnionEq, u, t, x))),
									Leg(
										b.Term("op(f(x), iterated_op(op, u ∪ t, f))"),
										"and there x is new, over a finite index set, so the recursion clause hands its factor back",
										By(mon, fresh, joinFinite, OneTurn)),
									Leg(
										b.Term("op(f(x), op(iterated_op(op, u, f), iterated_op(op, t, f)))"),
										"the induction hypothesis, u being apart from t, splits what is left of the join",
										By(carried, split)),
									Leg(
										b.Term("op(op(f(x), iterated_op(op, u, f)), iterated_op(op, t, f))"),
										"associativity carries the recovered factor onto the left side",
										By(mon, At(MonoidalAC, op))),
									FinalLeg(
										"where the recursion clause, read backwards, folds it into insert(x, u)",
										By(Normalized, mon, carried, OneTurn))))
						}))))
		}),
})}

// Diff — a fold over a finite index set splits at any subset of it:
// what the subset contributes, combined with what is left over,
// rebuilds the whole fold.
//
// There is no induction here and no recursion clause. `t ⊆ s` says
// precisely that s is t together with the part outside t, sharing
// nothing, so the theorem is `Union` read at that one decomposition,
// and the argument's whole job is to produce the decomposition and
// then recognize the join as s again.
//
// Two choices worth naming. Finiteness of the part outside t is taken
// from `finite_set.FiniteDiff` in one step rather than routed through
// inclusion: a cut-out of a finite set is finite outright, which is one
// named law where going by way of `s ∖ t ⊆ s` costs two.
//
// And the decomposition goes to the membership driver. Both of its
// halves are statements about points once ⊆, ∖ and ∪ are unfolded, and
// unfolding them together is exactly what the driver is; by hand it
// would mean expanding what ⊆ abbreviates and then citing the
// membership laws for the two constructors separately. Spelling it by
// hand costs more named rows for no less search, and the decomposition
// is one mathematical fact, so it is asked for as one.
var Diff = diffThm{family.Add(registry.ProofEntry{
	Name: "Diff",
	Key:  "prop_35e9814124f2f996",
	Build: MonoidalOp.Law(
		Statement{
			Binders: "∀s t:set(A). ∀f:(A → B).",
			Hypotheses: []string{
				"finite(s)",
				"t ⊆ s",
			},
			Conclusion: "op(iterated_op(op, s ∖ t, f), iterated_op(op, t, f)) = iterated_op(op, s, f)",
		},
		func(
			a *Argument,
			op *Arrow2[carrier, carrier, carrier],
			mon Fact,
			s, t *Expr[indexSet],
			f *Arrow[index, carrier],
			withinFinite Fact,
		) {
			outside := a.Term("s ∖ t")

			// One fact, not two: the decomposition is what `t ⊆ s` says,
			// and asking the driver for both halves at once is also what
			// keeps it to a single refutation. (∖ and ∪ share a precedence
			// level and associate left, so `s ∖ t ∪ t` is the rejoined
			// whole.)
			cut := a.Have(
				"t cuts s in two: what is left outside t meets t "+
					"nowhere, and the two put back together are s again",
				"disjoint(s ∖ t, t) ∧ s ∖ t ∪ t = s",
				BySets(withinFinite))

			a.Show(
				"so the two halves' folds combine into the fold over their join, and that join is s",
				CalcEq(
					Leg(
						a.Term("iterated_op(op, s ∖ t ∪ t, f)"),
						"both parts of a finite set are finite, and finite and "+
							"apart is exactly what `Union` asks of two index sets",
						By(
							mon,
							withinFinite,
							At(finite_set.FiniteDiff, s, t),
							At(finite_set.FiniteSubset, t, s),
							cut,
							At(Union, op, outside, t, f))),
					FinalLeg(
						"and a fold sees only its index set, which here is s again",
						// Normalized: the leg is the join rewritten by the
						// equation the cut already carries, so simplifying
						// against it is the whole step — measured, dropping
						// this sends the leg to the refuter.
						By(Normalized, cut))))
		}),
})}

// Split — a summand that decides between two others by a test on the
// index folds as the two folds, each taken over the half of the index
// set its own summand answers for. The index set has to be finite,
// that being what the union law reaches.
//
// The mathematics is that the test PARTITIONS the index set, and the
// proof is that reading: the two halves meet in nothing, together they
// are `s`, and each is finite, being a restriction of a finite set.
// `Union` then splits the fold across them — still at the choosing
// summand, which it carries along untouched — and what is left is that
// on either half the choice never wavers. That last step is
// `Congruence`, and its premise is the one genuinely pointwise fact
// here: where the test holds the choice IS f's value, and where it
// fails, g's.
//
// So the proof falls in two, either side of a naming. Up to it every
// claim is about membership in `{x | x ∈ s ∧ P(x)}`, which is the set
// driver's own subject — the four facts that need it each close under
// a bare `BySets()`. Past it nothing asks what the halves
// are, only that they are finite, apart, and cover `s`; so they are
// named there and the three fold laws are read over the names.
var Split = splitThm{family.Add(registry.ProofEntry{
	Name: "Split",
	Key:  "prop_affd59826abe1543",
	Build: MonoidalOp.Law(Statement{
		Binders: "∀s:set(A). ∀P:(A → bool). ∀f g:(A → B).",
		Hypotheses: []string{
			"finite(s)",
		},
		Conclusion: "iterated_op(op, s, «choosingSummand») = " +
			"op(iterated_op(op, «acceptedHalf», f), iterated_op(op, «rejectedHalf», g))",
		Abbrev: Abbrev{
			{Name: "rejectedHalf", Text: "{x | x ∈ s ∧ ¬P(x)}"},
			{Name: "choosingSummand", Text: "λx:A. COND(P(x), f(x), g(x))"},
		},
	},
		func(
			a *Argument,
			op *Arrow2[carrier, carrier, carrier],
			mon Fact,
			s, P *Expr[indexSet],
			f, g *Arrow[index, carrier],
			sFinite Fact,
		) {
			ctx := a.Ctx()

			// The two halves and the choosing summand as terms — the same
			// three spellings the headline is built from.
			acceptedSet, rejectedSet := a.Term("«acceptedHalf»"), a.Term("«rejectedHalf»")
			chooses := a.Term("«choosingSummand»")

			// The names the halves will carry from the midpoint on —
			// declared here as the typed witnesses the cites below want
			// (`Denote` registers the spellings too, idempotently).
			accepted := ctx.VarAs[indexSet]("accepted")
			rejected := ctx.VarAs[indexSet]("rejected")

			// The six facts below are each read TWICE — at the
			// comprehension here, and again at the name the half is given
			// halfway through; a drift between the readings fails loudly
			// at the Hyp lookup.
			a.Have(
				"the accepted half is a restriction of s, so finitely many points",
				"finite(«acceptedHalf»)",
				By(sFinite, At(finite_set.FiniteRestrict, s, P)))

			a.Have(
				"and the rejected half is that same restriction, taken at the negated test",
				"finite(«rejectedHalf»)",
				By(sFinite, At(finite_set.FiniteRestrict, s, a.Term("λx:A. ¬P(x)"))))

			a.Have(
				"no point answers the test both ways, so the halves meet in nothing",
				"disjoint(«acceptedHalf», «rejectedHalf»)",
				BySets())

			a.Have(
				"and every point of s answers it one way or the other, so together they are s",
				"«acceptedHalf» ∪ «rejectedHalf» = s",
				BySets())

			a.Have(
				"across the accepted half the choice never wavers: it is f's value there",
				"∀y:A. y ∈ «acceptedHalf» ⇒ COND(P(y), f(y), g(y)) = f(y)",
				BySets())

			a.Have(
				"and across the rejected half it is g's",
				"∀y:A. y ∈ «rejectedHalf» ⇒ COND(P(y), f(y), g(y)) = g(y)",
				BySets())

			// Everything the comprehensions were needed for has now been
			// said, so the halves are named and never opened again.
			//
			// The naming is load-bearing rather than cosmetic. A
			// comprehension still standing in a leaf the refuter reaches
			// gets opened into its ∃/comprehension_spec form and searched there, and
			// the search does not come back. Measured on the union step
			// below, where one named half is no better than none.
			// Membership is the set driver's business and it reads
			// comprehensions natively; the refuter is not asked to.
			a.Denote("accepted", acceptedSet)
			a.Denote("rejected", rejectedSet)

			// The six facts again, at the names. A denote rewrites every
			// hypothesis in one step, which leaves no fact handle a unique
			// successor to follow, so each is named afresh on this side.
			acceptedFinite := a.Hyp("finite(accepted)")
			rejectedFinite := a.Hyp("finite(rejected)")
			apart := a.Hyp("disjoint(accepted, rejected)")
			partition := a.Hyp("accepted ∪ rejected = s")
			acceptedAgrees := a.Hyp("∀y:A. y ∈ accepted ⇒ COND(P(y), f(y), g(y)) = f(y)")
			rejectedAgrees := a.Hyp("∀y:A. y ∈ rejected ⇒ COND(P(y), f(y), g(y)) = g(y)")

			onAccepted := a.Have(
				"so over the accepted half the choosing summand folds exactly as f does",
				"iterated_op(op, accepted, «choosingSummand») = iterated_op(op, accepted, f)",
				By(mon, acceptedAgrees, At(Congruence, op, accepted, chooses, f)))

			onRejected := a.Have(
				"and over the rejected half exactly as g does",
				"iterated_op(op, rejected, «choosingSummand») = iterated_op(op, rejected, g)",
				By(mon, rejectedAgrees, At(Congruence, op, rejected, chooses, g)))

			split := a.Have(
				"while being finite and apart is what lets the fold over their union come apart",
				"iterated_op(op, accepted ∪ rejected, «choosingSummand») = "+
					"op(iterated_op(op, accepted, «choosingSummand»), iterated_op(op, rejected, «choosingSummand»))",
				By(mon, acceptedFinite, rejectedFinite, apart, At(Union, op, accepted, rejected, chooses)))

			// Naming the halves puts the spine in ⊥-form — the conclusion
			// is negated into the hypotheses, as after a "suppose not" —
			// so the close is a refutation, and the supposition is one of
			// its named premises.
			differ := a.Hyp(
				"iterated_op(op, s, «choosingSummand») ≠ " +
					"op(iterated_op(op, accepted, f), iterated_op(op, rejected, g))")

			// Normalized: the four equations meet by simplification, and
			// the refutation left over is the one that does not have to
			// chain them. This is the only site in the member where the
			// shaping earns anything; at the three fold steps above it
			// changes nothing, so none is written there.
			a.Show(
				"and their union is s, so those two folds ARE the fold over s — the supposition cannot stand",
				By(Normalized, differ, partition, split, onAccepted, onRejected))
		}),
})}

// UnionIntersection — folding two finite index sets separately and
// combining agrees with folding their union and their overlap and
// combining those. The union takes each shared point once where the two
// separate folds take it twice, and the overlap's fold is exactly the
// difference. This is inclusion–exclusion at two sets, for the fold of
// any monoid; the sieve over a finite family of sets, counted, is
// `nat_sum.InclusionExclusion`.
//
// There is no induction here and no recursion clause. The whole argument
// is one set — `t ∖ s`, what t adds to s — read twice. Laid alongside s
// it makes the union, and laid alongside the overlap it makes t; neither
// join shares a point, so `Union` splits the fold at both. Each side of
// the equation is then s's fold, the new part's fold and the overlap's
// fold in that order, and they differ only in which two are grouped —
// which is associativity, once.
//
// That the cut is taken at t, and not at s, is what keeps it to that one
// associativity. Cutting s at the overlap instead — where the statement's
// own left-hand side points — puts both fold
// laws on the same side of the equation, and what is left over is a
// rearrangement of three factors wanting associativity twice with a
// commutation between. Measured, the refuter does not finish that inside
// its search budget; cut this way the same step closes at once.
var UnionIntersection = unionIntersectionThm{family.Add(registry.ProofEntry{
	Name: "UnionIntersection",
	Key:  "prop_be7d75f7a50932bb",
	Build: MonoidalOp.Law(
		Statement{
			Binders: "∀s t:set(A). ∀f:(A → B).",
			Hypotheses: []string{
				"finite(s)",
				"finite(t)",
			},
			Conclusion: "op(iterated_op(op, s, f), iterated_op(op, t, f)) = " +
				"op(iterated_op(op, s ∪ t, f), iterated_op(op, s ∩ t, f))",
		},
		func(
			a *Argument,
			op *Arrow2[carrier, carrier, carrier],
			mon Fact,
			s, t *Expr[indexSet],
			f *Arrow[index, carrier],
			finite Fact,
		) {
			// The two sets the argument is about, as terms for the `Union`
			// witnesses below. `newPart` is what t contributes beyond s;
			// `overlap` is what both carry. In the claim texts their
			// compound spellings carry their own parentheses: ∪, ∩ and ∖
			// share one precedence level and associate to the left, so an
			// unparenthesized `s ∪ t ∖ s` would be the difference of the
			// union rather than the union with the difference.
			newPart := a.Term("t ∖ s")
			overlap := a.Term("s ∩ t")

			newFinite := a.Have(
				"the new part is finite, being cut out of t",
				"finite(t ∖ s)",
				By(finite, At(finite_set.FiniteDiff, t, s)))

			overlapFinite := a.Have(
				"and so is the overlap, being carved out of s",
				"finite(s ∩ t)",
				By(finite, At(finite_set.FiniteInter, s, t)))

			// Two decompositions, two facts: each is spent at its own
			// reading of the union law below, and the driver reads both
			// off membership in one step apiece.
			widens := a.Have(
				"s and the new part share no point, and together they are the union",
				"disjoint(s, t ∖ s) ∧ s ∪ (t ∖ s) = s ∪ t",
				BySets())

			splits := a.Have(
				"nor do the new part and the overlap, and together they are t",
				"disjoint(t ∖ s, s ∩ t) ∧ (t ∖ s) ∪ (s ∩ t) = t",
				BySets())

			overUnion := a.Have(
				"so the fold over the union comes apart into s's and the new part's",
				"iterated_op(op, s ∪ t, f) = op(iterated_op(op, s, f), iterated_op(op, t ∖ s, f))",
				By(mon, finite, newFinite, widens, At(Union, op, s, newPart, f)))

			overT := a.Have(
				"and the fold over t into that same new part's and the overlap's",
				"iterated_op(op, t, f) = op(iterated_op(op, t ∖ s, f), iterated_op(op, s ∩ t, f))",
				By(mon, newFinite, overlapFinite, splits, At(Union, op, newPart, overlap, f)))

			a.Show(
				"leaving both sides s, then the new part, then the overlap, grouped two ways",
				By(mon, overUnion, overT, At(MonoidalAC, op)))
		}),
})}

// Pointwise — a fold distributes over a summand assembled pointwise
// from two others: combining first and folding once agrees with
// folding twice and combining last. The index set has to be finite,
// because the argument walks the recursion clauses along it.
//
// The induction is the strong one, for the reason any use of those
// clauses needs it: the insert clause asks that the point laid in be
// new and that the set it joins be finite, and those are exactly the
// two premises the strong rule grants.
//
// Each case turns on ONE fact about the fold at an ARBITRARY summand,
// which is what lets the three folds step together rather than three
// times over — at ∅ every fold is the neutral, and at insert every
// fold gives up its value at the new point. What is left is the
// regrouping, and it is the mathematical content of the member: with
// F and G the two folds over the smaller set, the enlarged fold of the
// combination carries the two new factors side by side, where the two
// enlarged folds carry one each, so what has to hold is
//
//	op(op(f x, g x), op(F, G)) = op(op(f x, F), op(g x, G)).
//
// Sorting each summand's value at the new point back onto its own fold
// is what `monoidal_op op` buys — associativity and commutativity, which
// the AC pack states.
var Pointwise = pointwiseThm{family.Add(registry.ProofEntry{
	Name: "Pointwise",
	Key:  "prop_d7ddfc2b97cf0d0f",
	Build: MonoidalOp.Law(Statement{
		Binders: "∀f g:(A → B). ∀s:set(A).",
		Hypotheses: []string{
			"finite(s)",
		},
		Conclusion: "iterated_op(op, s, «combinedSummand») = " +
			"op(iterated_op(op, s, f), iterated_op(op, s, g))",
		Abbrev: Abbrev{
			{Name: "combinedSummand", Text: "λx:A. op(f(x), g(x))"},
		},
	},
		func(
			a *Argument,
			op *Arrow2[carrier, carrier, carrier],
			mon Fact,
			f, g *Arrow[index, carrier],
			s *Expr[indexSet],
			sFinite Fact,
		) {
			combined := a.Term("«combinedSummand»")

			a.Show(
				"so the law reaches every finite index set, and s is one of those",
				ByInduction(finite_set.FiniteInductFresh, sFinite,

					Case(
						"∅: every side folds to the neutral, and joining the neutral to itself returns it",
						Derive(func(b *Argument) {
							emptyFold := b.Have(
								"folding nothing returns the neutral, whatever the summand",
								"∀h:(A → B). iterated_op(op, empty_set, h) = neutral_elem(op)",
								By(mon, Clauses))
							b.Show(
								"so both sides come to that one neutral, which is its own join",
								By(mon, At(MonoidalAC, op), emptyFold.At(combined), emptyFold.At(f), emptyFold.At(g)))
						})),

					Case(
						"insert: the new point hands one factor to each fold, and the four sort out",
						Derive(func(b *Argument) {
							// The principle's own set binder is `s`, which the
							// section holds — so the induction set is NAMED.
							b.FixAs[index]() // x — the claims below spell it by name
							b.FixAs[indexSet]("u")
							carried := b.Assume() // the law at u, x ∉ u, and finite(u)

							oneTurn := b.Have(
								"one turn of the recursion at the new point: any summand gives up its value there",
								"∀h:(A → B). iterated_op(op, insert(x, u), h) = op(h(x), iterated_op(op, u, h))",
								By(mon, carried, OneTurn))

							regroup := b.Have(
								"and the four factors sort — each summand's value at the new point onto its own fold",
								"op(op(f(x), g(x)), op(iterated_op(op, u, f), iterated_op(op, u, g))) = "+
									"op(op(f(x), iterated_op(op, u, f)), op(g(x), iterated_op(op, u, g)))",
								By(mon, At(MonoidalAC, op)))

							b.Show(
								"that one turn splits all three enlarged folds, the "+
									"law at u joins their tails, and the sort finishes it",
								By(carried, regroup, oneTurn.At(combined), oneTurn.At(f), oneTurn.At(g)))
						}))))
		}),
})}

// Swap — a double fold does not care which of its two index sets is
// taken first. Both have to be finite, that being where the recursion
// reaches on either side.
//
// This member has TWO index types: the carrier stays at the chapter's
// `B`, so `A` and `C` are the two — the arrangement every doubly-indexed
// member of the chapter shares.
//
// The induction is on the SECOND index set, with the first held fixed,
// and the BASE case is what decides that. Taken the other way the step
// is the same length and wants the same laws, but the summand of the
// inner fold is then written `λi. f(i, j)` under the outer binder rather
// than the section `f(i)`, so recognising it as the neutral everywhere
// asks for the empty-fold fact at a λ-abstraction over the enclosing
// bound variable — which the refuter does not reach. Stated this way
// round the same premise list closes at once.
//
// Each case turns on ONE fact about the fold over the second index set
// at an ARBITRARY summand, which is what lets both sides of the equation
// step together. At ∅ that fact is that every fold is the neutral, and
// the left side then folds the neutral over the whole first index set —
// which is where `EqNeutral` earns its place: the outer fold runs over a
// general `s` the recursion clauses cannot read, so what settles it is
// that its summand is the neutral at every point. At insert it is
// that every fold gives up its value at the new point, and the argument
// is a chain: the point leaves the inner folds on the left (under the
// outer fold, so `Congruence` carries it), the summand that remains is
// assembled pointwise from two others and `Pointwise` splits it, the
// induction hypothesis swaps what is left, and the same recursion clause
// read backwards folds the point onto the right.
var Swap = swapThm{family.Add(registry.ProofEntry{
	Name: "Swap",
	Key:  "prop_c322a7b924160396",
	Build: MonoidalOp.Law(Statement{
		Binders: "∀s:set(A). ∀t:set(C). ∀f:(A → C → B).",
		Hypotheses: []string{
			"finite(s)",
			"finite(t)",
		},
		Conclusion: "iterated_op(op, s, λi:A. iterated_op(op, t, f(i))) = " +
			"iterated_op(op, t, λj:C. iterated_op(op, s, λi:A. f(i, j)))",
	},
		func(
			a *Argument,
			op *Arrow2[B, B, B],
			mon Fact,
			s *Expr[Set[A]],
			t *Expr[Set[C]],
			f *Arrow2[A, C, B],
			finiteS, finiteT Fact,
		) {
			a.Show(
				"so the swap reaches every finite second index set, and t is one of those",
				ByInduction(finite_set.FiniteInductFresh, finiteT,

					Case(
						"∅: the inner folds all collapse to the neutral, and so then does the fold of them",
						Derive(func(b *Argument) {
							emptyFold := b.Have(
								"folding nothing over the second index set returns the neutral, whatever the summand",
								"∀h:(C → B). iterated_op(op, «emptySecond», h) = neutral_elem(op)",
								By(mon, Clauses))

							collapses := b.Have(
								"so on the left every summand the outer fold sees is the neutral, "+
									"and a summand that is silent everywhere contributes nothing",
								"iterated_op(op, s, λi:A. iterated_op(op, «emptySecond», f(i))) = neutral_elem(op)",
								By(mon, emptyFold, EqNeutral))

							b.Show(
								"while the right side is that same empty fold outright, read at the one summand it is taken over",
								By(collapses, emptyFold.At(b.Term("λj:C. iterated_op(op, s, λi:A. f(i, j))"))))
						})),

					Case(
						"insert: the new point comes out of every inner "+
							"fold on the left and off the outer fold on the right",
						Derive(func(b *Argument) {
							// The rule's own binders spell `x` and `s` at the
							// second index type; `s` is the section's, so both
							// are NAMED — the point y, the smaller set v.
							b.FixAs[C]("y")
							b.FixAs[Set[C]]("v")
							carried := b.Assume() // the swap at v, y ∉ v, and finite(v)

							oneTurn := b.Have(
								"one turn of the recursion at the new point: any summand "+
									"over the second index set gives up its value there",
								"∀h:(C → B). iterated_op(op, insert(y, v), h) = op(h(y), iterated_op(op, v, h))",
								By(mon, carried, OneTurn))

							b.Show(
								"so the new point leaves the inner folds, splits the outer one, and goes back on the other side",
								CalcEq(
									Leg(
										b.Term("iterated_op(op, s, λi:A. op(f(i, y), iterated_op(op, v, f(i))))"),
										"the point leaves every inner fold, and the outer fold cannot "+
											"tell two summands apart that agree at each of its points",
										By(mon, oneTurn, Congruence)),
									Leg(
										b.Term("op(iterated_op(op, s, λi:A. f(i, y)), iterated_op(op, s, λi:A. iterated_op(op, v, f(i))))"),
										"what is left is a summand assembled pointwise from "+
											"two others, and the fold distributes over such a one",
										By(mon, finiteS, Pointwise)),
									Leg(
										b.Term(
											"op(iterated_op(op, s, λi:A. f(i, y)), "+
												"    iterated_op(op, v, λj:C. iterated_op(op, s, λi:A. f(i, j))))"),
										"the induction hypothesis swaps the two folds in the right-hand factor",
										// Normalized: the leg is the hypothesis under one
										// common factor, so simplifying against it is the
										// whole step — the refuter is never wanted here.
										By(carried)),
									FinalLeg(
										"and the recursion clause, read backwards, lays the point back into the second index set",
										By(oneTurn.At(b.Term("λj:C. iterated_op(op, s, λi:A. f(i, j))"))))))
						}))))
		}),
})}

// ---------------------------------------------------------------------------
// A fold INHERITS a property of the values it combines
// ---------------------------------------------------------------------------
//
// `Closed` and `ClosedNonempty` carry a property of the summand's
// values up to the fold. They are not the same theorem at two
// hypothesis packages — `ClosedNonempty` asks the STRONGER pointwise
// premise, `x ∈ s ⇒ P(f x)` where `Closed` asks it only where the
// summand is not silent. That is what buys the dropped `P(neutral_elem op)`:
// on any index set with a silent point the stronger premise recovers
// it, and the nonemptiness is what guarantees the fold is not the
// neutral by default.
//
// Both members run the strong finite induction with the pointwise
// premise travelling INSIDE the induction property, and each says why
// its own statement forces that. The homomorphism part above carries the
// habits shared with the homomorphism members — literal claims, and
// naming an induction property whose quantifiers would otherwise
// prenex.

// Closed — a property that holds at the neutral and survives the
// operation is inherited by every fold, provided it holds at each
// factor the summand actually contributes. The premise asks nothing at
// the points the summand is silent at: those contribute the neutral,
// which the first hypothesis already covers.
//
// No finiteness is asked, and that is what shapes the proof: the
// definition's own case analysis is the split. On an infinite support
// the fold IS the neutral and there is nothing to carry; on a finite
// one the fold is reached from ∅ one point at a time, which is an
// induction the two closure hypotheses are exactly the obligations of
// — the neutral answers the empty fold, and crossing the operation
// answers the point laid in.
//
// The pointwise premise travels INSIDE the induction property rather
// than beside it, and that is forced: the induction ranges over every
// finite set, not only over subsets of the support, so nothing outside
// it knows P at the factors an arbitrary set contributes.
//
// `Related` (above) is this member's RELATIONAL companion: the
// same transfer architecture at a relation the operation respects,
// where this one carries a property it survives.
var Closed = closedThm{family.Add(registry.ProofEntry{
	Name: "Closed",
	Key:  "prop_d2efe1d5478cb71c",
	Build: MonoidalOp.Law(
		Statement{
			Binders: "∀P:(B → bool). ∀s:set(A). ∀f:(A → B).",
			Hypotheses: []string{
				"P(neutral_elem(op))",
				"∀x y:B. P(x) ∧ P(y) ⇒ P(op(x, y))",
				"∀x:A. x ∈ s ∧ f(x) ≠ neutral_elem(op) ⇒ P(f(x))",
			},
			Conclusion: "P(iterated_op(op, s, f))",
		},
		func(
			a *Argument,
			op *Arrow2[carrier, carrier, carrier],
			mon Fact,
			P *Arrow[carrier, Bool],
			s *Expr[indexSet],
			f *Arrow[index, carrier],
			atNeutral, acrossOp, live Fact,
		) {
			v := ops(a.Ctx())

			// The set the fold really runs over. The split below is on
			// its finiteness as a TERM, which is why `finite` carries a
			// build handle in the chapter vocabulary.
			common := v.OpSupport.Apply(op, f, s)

			closedOn := a.TermAs[Fun[indexSet, Bool]](
				"λu:set(A). (∀y:A. y ∈ u ⇒ P(f(y))) ⇒ P(iterated_op(op, u, f))")

			finite := a.Assuming(
				v.Finite.Apply(common),
				"an infinite support: the definition returns the neutral, and P holds there by hypothesis",
				Given(func(b *Argument, infinite Fact) {
					b.Show(
						"so the fold is the else branch of the definition's own case analysis",
						// Normalized: the guard is resolved by simplification
						// against the resident ¬finite, which is what leaves
						// the neutral standing on the right.
						By(Normalized, infinite, atNeutral, At(ExpandCases, s, f, op)))
				}))

			goodOnSupport := a.Have(
				"P holds at every factor the fold can see: a point "+
					"of the support is a point of s the summand speaks at",
				"∀y:A. y ∈ op_support(op, f, s) ⇒ P(f(y))",
				// InSupport is cited BARE: the point the premise is wanted
				// at is the one the negated claim names, which nothing here
				// spells.
				By(live, InSupport))

			overSupport := a.Have(
				"so the induction carries P to the fold over the support, one point at a time",
				"P(iterated_op(op, op_support(op, f, s), f))",
				// The principle is taken at the set it concludes about as
				// well as at the property, which pins the property without
				// naming it (file header). `finite` discharges the
				// principle's own guard, `goodOnSupport` the property's.
				ByInduction(At(finite_set.FiniteInductFresh, closedOn, common), finite, goodOnSupport,

					Case(
						"∅: the fold of nothing is the neutral, which P holds at outright",
						// The property's own premise says nothing about ∅ and
						// is spent nowhere in this case.
						By(mon, atNeutral, Clauses)),

					Case(
						"insert: the point laid in contributes one more factor, laid onto a fold P already holds of",
						Derive(func(b *Argument) {
							// The principle's own set binder is `s`, which the
							// section holds — so the induction set is NAMED.
							x := b.FixAs[index]()
							u := b.FixAs[indexSet]("u")
							carried := b.Assume() // the property at u, x ∉ u, and finite(u)
							agree := b.Assume()   // P at every factor insert(x, u) contributes

							here := b.Have(
								"P holds at the factor the new point contributes",
								"P(f(x))",
								By(agree.At(x), At(set_basic.InInsert, u, x, x)))

							below := b.Have(
								"and at every factor u was already contributing",
								"∀y:A. y ∈ u ⇒ P(f(y))",
								// Bare, for the same reason InSupport is above.
								By(agree, set_basic.InInsert))

							smaller := b.Have(
								"so the property does apply at u, and P survives the smaller fold",
								"P(iterated_op(op, u, f))",
								By(carried, below))

							split := b.Have(
								"while the recursion clause peels the new point's factor off the enlarged fold",
								"iterated_op(op, insert(x, u), f) = op(f(x), iterated_op(op, u, f))",
								By(mon, carried, OneTurn))

							b.Show(
								"and P crosses the operation between those two factors",
								// Normalized: the grounded closure hypothesis is an
								// implication whose two antecedents are `here` and
								// `smaller`, discharged by simplification.
								By(
									Normalized,
									acrossOp.At(b.TermAs[carrier]("f(x)"), b.TermAs[carrier]("iterated_op(op, u, f)")),
									here,
									smaller,
									split))
						}))))

			a.Show(
				"and on a finite support the definition's case analysis returns exactly that fold",
				// Normalized: the guard is resolved by simplification against
				// the resident finite, leaving the fold over the support.
				By(Normalized, finite, overSupport, At(ExpandCases, s, f, op)))
		}),
})}

// ClosedNonempty — a property closed under the operation, and holding
// at every summand value on the index set, holds at the fold, provided
// that set is finite and NOT empty.
//
// The nonemptiness is not a convenience: a fold over nothing is the
// neutral, and nothing assumed here says the property holds THERE, so
// the empty set has to be excluded rather than proved — and that
// exclusion shapes the whole argument. The induction is
// the strong one over finite sets, run on the property "nonempty, and
// good at every point ⇒ the fold is good"; at ∅ that property is
// vacuous, its guard being exactly the case being ruled out. So the
// induction does no work at its own base, and the argument's real base
// has moved one step inward: inside the insert case, when what the new
// point is laid into is still empty, the set is a single point and the
// fold reads the summand there. Past that the recursion clause splits
// off the new point's factor and closure carries the property across
// it.
//
// Both of the theorem's conditions on the index set travel INSIDE the
// induction property rather than beside it, for two different reasons.
// The summand's goodness has to be RE-READ at the smaller set, and the
// enlarged set's copy of it says everything needed. The nonemptiness
// cannot be re-read at all — an enlarged set is nonempty whatever it
// was enlarged from — so the step has to settle that question itself,
// and the case where it fails is precisely the singleton.
var ClosedNonempty = closedNonemptyThm{family.Add(registry.ProofEntry{
	Name: "ClosedNonempty",
	Key:  "prop_688920cd0c60f54b",
	Build: MonoidalOp.Law(
		Statement{
			Binders: "∀P:(B → bool). ∀s:set(A). ∀f:(A → B).",
			Hypotheses: []string{
				"∀x y:B. P(x) ∧ P(y) ⇒ P(op(x, y))",
				"finite(s) ∧ s ≠ ∅ ∧ ∀x:A. x ∈ s ⇒ P(f(x))",
			},
			Conclusion: "P(iterated_op(op, s, f))",
		},
		func(a *Argument, op *Arrow2[carrier, carrier, carrier], mon Fact, P *Arrow[carrier, Bool],
			s *Expr[indexSet], f *Arrow[index, carrier], closure, onIndex Fact) {
			v := ops(a.Ctx())

			// `onIndex` carries all three conditions on the index set —
			// finite, nonempty, and the summand good at every one of its
			// points — and is spent once, at the very end, against the
			// induction's conclusion.

			reaches := a.Have(
				"the property carries to every finite index set",
				"∀v:set(A). finite(v) ⇒ v ≠ empty_set ⇒ (∀y:A. y ∈ v ⇒ P(f(y))) ⇒ P(iterated_op(op, v, f))",
				// The claim IS the principle's conclusion, so its property
				// is read off the claim (file header), and the two
				// obligations ride along beside it.
				ByInduction(finite_set.FiniteInductFresh,
					Case(
						"∅ is excluded rather than proved: the property's own "+
							"guard fails there, so its base case carries no content",
						TrivialNormalized()),

					Case(
						"insert: the point laid in is either the whole set by itself, "+
							"or one more factor on the fold of what was there already",
						Derive(func(b *Argument) {
							// The principle's own set binder is `s`, which the
							// section holds — so the induction set is NAMED.
							x := b.FixAs[index]()
							u := b.FixAs[indexSet]("u")
							carried := b.Assume() // the property at u, x ∉ u, and finite(u)
							b.Assume()            // insert(x, u) ≠ ∅ — granted here, and never spent
							agree := b.Assume()   // the summand is good everywhere on insert(x, u)

							here := b.Have(
								"the point laid in has a good summand value",
								"P(f(x))",
								By(agree.At(x), At(set_basic.InInsert, u, x, x)))

							nonempty := b.Unless(
								Equal(u, v.EmptySet),
								"nothing was there yet: the set is the single point x, and a one-point "+
									"fold reads its summand — this, not ∅, is where the induction really starts",
								Given(func(c *Argument, wasEmpty Fact) {
									singleton := c.Have(
										"a fold over one point is the summand's value there",
										"iterated_op(op, insert(x, empty_set), f) = f(x)",
										By(mon, At(Sing, op, f, x)))
									c.Show(
										"so the fold collapses to that value, which is good",
										wasEmpty.Rw(),
										singleton.Rw(),
										By(here))
								}))

							below := b.Have(
								"the summand is good at every point u already held",
								"∀y:A. y ∈ u ⇒ P(f(y))",
								// Bare, as in `Closed`'s matching descent: the
								// point is the one the negated claim names, which
								// nothing here spells.
								By(agree, set_basic.InInsert))

							smaller := b.Have(
								"so the property does apply at u — nonempty on this side of the split, and good all over",
								"P(iterated_op(op, u, f))",
								// Normalized: both of the carried property's
								// antecedents are discharged by simplification
								// against the two facts beside it.
								By(carried, nonempty, below))

							split := b.Have(
								"and the recursion clause pulls the new point back out: "+
									"it is genuinely new, and what it is laid into is finite",
								"iterated_op(op, insert(x, u), f) = op(f(x), iterated_op(op, u, f))",
								By(mon, carried, OneTurn))

							b.Show(
								"leaving a product of two good factors, and the property is closed under op",
								split.Rw(),
								By(
									closure.At(b.TermAs[carrier]("f(x)"), b.TermAs[carrier]("iterated_op(op, u, f)")),
									here,
									smaller))
						}))))

			a.Show(
				"and the index set in hand is one of them — finite, nonempty, and good all over",
				By(onIndex, reaches.At(s)))
		}),
})}

// ---------------------------------------------------------------------------
// Carrying a fold from one index set to another
// ---------------------------------------------------------------------------
//
// Every member here answers the same question: given a map between two
// index sets, when does a fold over one equal a fold over the other?
// The answer always needs the map to lose nothing — no two points of the
// source may be identified unless what they contribute is invisible —
// and the members differ in how that faithfulness is presented.
//
// `Image` takes it as injectivity and reads the fold along `image(f, s)`.
// `ImageOffSupport` weakens injectivity to the honest minimum: points may
// collide where the summand is the neutral, since a collapsed point
// contributes nothing. `Bijection` and `Injection` are the endomorphism
// cases — a map of `s` into itself, presented as a permutation and as an
// injection on a finite set, which for a finite set are the same thing.
// `ReindexGeneral` states the general correspondence between two distinct
// sets, and `Reindex` gives it again with the inverse written down, which
// is the form consumers actually have.
//
// `Restrict` and `Fibres` are the two special cases where the second set
// is built FROM the first. Restricting to the points a test accepts is
// the same as silencing the summand off them; grouping along a map's
// fibres and folding each group is the same as folding the whole. Both
// have no induction: they are the transport laws read at a decomposition
// the member builds itself.
//
// Three of these carry TWO index types, so their letters depart from the
// chapter's: `A` and `B` are the two index types and the carrier moves to
// `C`. Each says so in its own doc.

// Image — where `f` tells the points of `s` apart, the image is a
// faithful copy of `s`, so folding `g` over the image is folding `g`
// after `f` over `s`.
//
// This member has TWO index types, `A` for the source and `C` for the
// image, the carrier staying at the chapter's `B` — `Swap`'s
// arrangement.
//
// Nothing is asked of `s` but that `f` separates it, and that absence
// shapes the whole proof — as it does in `Closed`, and by the same
// mechanism: with no finiteness in hand the definition's own case
// analysis is the split, and the fold is decided by its SUPPORT rather
// than by its index set.
//
// So the argument is in two parts. The finite one is the mathematics:
// reached from ∅ one point at a time, the image grows by exactly one
// point at each step, because a point of what is already there sent to
// the same place would be one `f` cannot tell from the new one. That
// makes one turn of the recursion available on each side, shedding the
// same factor and leaving the transport at the smaller set.
//
// The general one turns on a single support fact — the image's support
// is the image of the source's, `f` composing into the summand as it
// goes. The two sides therefore run over `t` and `image(f, t)` for one
// and the same `t`; `f` still separates `t`, so the two are finite
// together, and the definition's guard is decided once for both. Where
// it fails both folds are the neutral; where it holds, the finite part
// answers.
var Image = imageThm{family.Add(registry.ProofEntry{
	Name: "Image",
	Key:  "prop_db95352e585b7d98",
	Build: MonoidalOp.Law(Statement{
		Binders: "∀f:(A → C). ∀g:(C → B). ∀s:set(A).",
		Hypotheses: []string{
			"injective_on(s, f)",
		},
		Conclusion: "iterated_op(op, image(f, s), g) = iterated_op(op, s, o(g, f))",
	},
		func(
			a *Argument,
			op *Arrow2[B, B, B],
			mon Fact,
			f *Arrow[A, C],
			g *Arrow[C, B],
			s *Expr[Set[A]],
			inj Fact,
		) {
			// The composite summand the source side folds, as a term for
			// the ground cites below.
			composite := a.Term("o(g, f)")

			reaches := a.Have(
				"the transport reaches every index set the recursion can walk",
				Statement{
					Binders: "∀u:set(A).",
					Hypotheses: []string{
						"finite(u)",
						"injective_on(u, f)",
					},
					Conclusion: "iterated_op(op, image(f, u), g) = iterated_op(op, u, o(g, f))",
				},
				// The claim IS the principle's conclusion, so its property
				// is read off the claim (file header), and the two
				// obligations ride along beside it.
				ByInduction(finite_set.FiniteInductFresh,
					Case(
						"∅: the image of nothing is nothing, and a fold over "+
							"nothing is the neutral — the same neutral on either side",
						Derive(func(b *Argument) {
							vanishes := b.Have(
								"the image of the empty index set is empty",
								"image(f, empty_set) = «emptySecond»",
								By(set_image.ImageClauses))

							// The empty fold is asked for twice, once per index
							// type — the one place where having two index types
							// costs something, the ∅ clause being stated at a
							// single one.
							atSource := b.Have(
								"a fold over nothing is the neutral, whatever the summand — at the source index type",
								"∀h:(A → B). iterated_op(op, empty_set, h) = neutral_elem(op)",
								By(mon, Clauses))

							atImage := b.Have(
								"and at the image index type",
								"∀h:(C → B). iterated_op(op, «emptySecond», h) = neutral_elem(op)",
								By(mon, Clauses))

							b.Show(
								"so both sides come to that one neutral, and separating ∅ was never asked for",
								// Normalized: with the image collapsed the two sides
								// are the same empty fold read at two summands, so
								// simplifying against the three equations is the whole
								// step — measured, dropping this sends the leaf to the
								// refuter and records a key.
								By(Normalized, vanishes, atSource.At(composite), atImage.At(g)))
						})),

					Case(
						"insert: the point laid in is sent somewhere the image has "+
							"not been, so one turn of the recursion answers each side",
						Derive(func(b *Argument) {
							// The principle's own set binder is `s`, which the
							// section holds — so the induction set is NAMED.
							b.FixAs[A]() // x — the claims below spell it by name
							u := b.FixAs[Set[A]]("u")
							carried := b.Assume()  // the transport at u, x ∉ u, and finite(u)
							faithful := b.Assume() // f separates the points of insert(x, u)
							// …read at its pairs of points, which is how both
							// facts below spend it.
							faithfulAtPoints := b.Unfolded(faithful, functions.InjectiveOnDef)

							widens := b.Have(
								"the image grows by exactly the new point's image",
								"image(f, insert(x, u)) = insert(f(x), image(f, u))",
								By(set_image.ImageClauses))

							fresh := b.Have(
								"and that image point is new: a point of u sent there "+
									"would be one f cannot tell from x, which x ∉ u forbids",
								"f(x) ∉ image(f, u)",
								BySets(faithfulAtPoints, carried))

							below := b.Have(
								"f separates what u already held, that being part of what it separates now",
								"injective_on(u, f)",
								Simp(Fwd(functions.InjectiveOnDef.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[C]()))),
								BySets(faithfulAtPoints))

							smaller := b.Have(
								"so the transport does apply at u",
								"iterated_op(op, image(f, u), g) = iterated_op(op, u, o(g, f))",
								By(carried, below))

							onImage := b.Have(
								"one turn of the recursion on the image side, the "+
									"new image point being new over a finite index set",
								"iterated_op(op, insert(f(x), image(f, u)), g) = op(g(f(x)), iterated_op(op, image(f, u), g))",
								By(mon, carried, At(finite_set.FiniteImage, f, u), fresh, OneTurn))

							onSource := b.Have(
								"and one on the source side, where the factor handed back is the very same one",
								"iterated_op(op, insert(x, u), o(g, f)) = op(g(f(x)), iterated_op(op, u, o(g, f)))",
								CalcEq(
									Leg(
										b.Term("op(o(g, f)(x), iterated_op(op, u, o(g, f)))"),
										"the recursion clause hands back the composite summand's value at the point laid in",
										By(mon, carried, OneTurn)),
									FinalLeg(
										"which is g's value at f's, the composite being read at a point",
										By(functions.ComposeApply))))

							b.Show(
								"so both sides shed that one factor, and what is left under it is the transport at u",
								By(widens, onImage, smaller, onSource))
						}))))

			// The set the source side's fold really runs over is
			// op_support(op, o(g, f), s); the image side's is that same set
			// carried across f — which is the whole point of what follows.
			common := a.Term("op_support(op, o(g, f), s)")

			pullsBack := a.Have(
				"the image's support is the image of the source's — f composes into the summand as it pulls back",
				"op_support(op, g, image(f, s)) = image(f, op_support(op, o(g, f), s))",
				// SupportClauses is read at op with all nine of its type
				// letters bound: the carrier I at B, the image clause's H
				// and G at the index types A and C, and the six clauses
				// this step does not read at A.
				By(SupportClauses.At[B, A, A, A, A, A, A, A, C](op)))

			onSupport := a.Have(
				"and f separates the support's points too, those being points of s",
				"injective_on(op_support(op, o(g, f), s), f)",
				// InSupport likewise bare: the pair of points the premise is
				// wanted at is the one the negated claim names, which nothing
				// here spells.
				Simp(Fwd(functions.InjectiveOnDef.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[C]()))),
				By(a.Unfolded(inj, functions.InjectiveOnDef), InSupport))

			together := a.Have(
				"so the two sides' supports are finite together — "+
					"a faithful copy is exactly as big as its original",
				"finite(image(f, op_support(op, o(g, f), s))) ⇔ finite(op_support(op, o(g, f), s))",
				By(onSupport, At(finite_set.FiniteImageInjEq, f, common)))

			sourceCases := a.Have(
				"the source side, read through the definition's own case analysis",
				"iterated_op(op, s, o(g, f)) = "+
					"COND(finite(op_support(op, o(g, f), s)), "+
					"    iterated_op(op, op_support(op, o(g, f), s), o(g, f)), "+
					"    neutral_elem(op))",
				By(ExpandCases))

			imageCases := a.Have(
				"and the image side likewise, its guard and its fold alike taken at the image of that same support",
				"iterated_op(op, image(f, s), g) = "+
					"COND(finite(image(f, op_support(op, o(g, f), s))), "+
					"    iterated_op(op, image(f, op_support(op, o(g, f), s)), g), "+
					"    neutral_elem(op))",
				CalcEq(
					Leg(
						a.Term("COND(finite(op_support(op, g, image(f, s))), "+
							"    iterated_op(op, op_support(op, g, image(f, s)), g), "+
							"    neutral_elem(op))"),
						"the case analysis, read at the image",
						By(ExpandCases)),
					FinalLeg(
						"whose support the pull-back rewrites",
						By(pullsBack))))

			finite := a.Assuming(
				a.Term("finite(op_support(op, o(g, f), s))"),
				"an infinite support: neither fold reaches the recursion at "+
					"all, and the definition answers the neutral on both sides",
				Given(func(b *Argument, infinite Fact) {
					b.Show(
						"so both case analyses take their else branch, the one guard deciding both",
						By(infinite, together, sourceCases, imageCases))
				}))

			a.Show(
				"and where the guard holds, the two case analyses "+
					"return the two folds the induction has already matched",
				By(finite, together, sourceCases, imageCases, onSupport, reaches.At(common)))
		}),
})}

// ImageOffSupport — collisions do not change a fold when the summand is
// neutral at every collision. On the summand's support the map is injective,
// so Image transports the fold there and OnSupport restores both index sets.
var ImageOffSupport = imageOffSupportThm{family.Add(registry.ProofEntry{
	Name: "ImageOffSupport",
	Key:  "prop_d6a67acee0f6bc7e",
	Build: MonoidalOp.Law(Statement{
		Binders: "∀g:(C → B). ∀f:(A → C). ∀s:set(A).",
		Hypotheses: []string{
			"∀x y:A. x ∈ s ∧ y ∈ s ∧ x ≠ y ∧ f(x) = f(y) ⇒ g(f(x)) = neutral_elem(op)",
		},
		Conclusion: "iterated_op(op, image(f, s), g) = iterated_op(op, s, o(g, f))",
		Abbrev: Abbrev{
			{Name: "sourceSupport", Text: "op_support(op, o(g, f), s)"},
		},
	},
		func(
			a *Argument,
			op *Arrow2[B, B, B],
			mon Fact,
			g *Arrow[C, B],
			f *Arrow[A, C],
			s *Expr[Set[A]],
			collisions Fact,
		) {
			support := a.TermAs[Set[A]]("«sourceSupport»")
			composite := a.TermAs[Fun[A, B]]("o(g, f)")
			image := a.TermAs[Set[C]]("image(f, s)")
			faithful := a.Have(
				"a collision would make its value neutral, so distinct support points cannot collide",
				"injective_on(«sourceSupport», f)",
				Simp(Fwd(functions.InjectiveOnDef.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[C]()))),
				Simp(Fwd(OpSupportDef)),
				BySets(collisions, functions.ComposeApply.At(g, f)))
			pullsBack := a.Have(
				"the image's support is the image of the composite summand's support",
				"op_support(op, g, image(f, s)) = image(f, «sourceSupport»)",
				By(SupportClauses.At[B, A, A, A, A, A, A, A, C](op)))
			a.Show(
				"transport over the support and ignore the neutral values on either side",
				CalcEq(
					Leg(
						a.TermAs[B]("iterated_op(op, image(f, «sourceSupport»), g)"),
						"the image fold only sees the image of the support",
						By(pullsBack, OnSupport.At(image, g, op))),
					Leg(
						a.TermAs[B]("iterated_op(op, «sourceSupport», o(g, f))"),
						"the map is injective on the support",
						By(faithful, Image.Read(mon).At(f, g, support))),
					FinalLeg(
						"the source fold only sees its support",
						By(OnSupport.At(s, composite, op)))))
		}),
})}

// Bijection — rearranging a fold's index set among itself leaves the
// fold where it was. `p` sends `s` into itself and every point of `s` is
// reached from exactly one point of `s`, so nothing is dropped and
// nothing is counted twice, and the fold cannot tell the two readings
// apart.
//
// This is `Image` at the one reindexing whose image is its own source,
// and the whole proof is reading the hypothesis twice. `Image` asks that
// the reindexing separate the points it is applied to, and it delivers
// the fold over the image; a permutation answers both at once — the
// uniqueness of preimages is injectivity, and their existence is what
// makes the image the whole of `s` again.
//
// The set equation is the whole membership argument: `y ∈ image(p, s)`
// says that `y` is `p` at a point of `s`, and the hypothesis' two halves
// answer exactly that, one in each direction. Being membership it goes
// to the set driver, this chapter's usual course, and the extensionality
// and image-membership laws the seed took it apart with are not wanted.
var Bijection = bijectionThm{family.Add(registry.ProofEntry{
	Name: "Bijection",
	Key:  "prop_96c85bb0fe765d67",
	Build: MonoidalOp.Law(
		Statement{
			Binders: "∀f:(A → B). ∀p:(A → A). ∀s:set(A).",
			Hypotheses: []string{
				"∀x:A. x ∈ s ⇒ p(x) ∈ s",
				"∀y:A. y ∈ s ⇒ ∃!x:A. x ∈ s ∧ p(x) = y",
			},
			Conclusion: "iterated_op(op, s, f) = iterated_op(op, s, o(f, p))",
		},
		func(
			a *Argument,
			op *Arrow2[carrier, carrier, carrier],
			mon Fact,
			f *Arrow[index, carrier],
			p *Arrow[index, index],
			s *Expr[indexSet],
			bij Fact,
		) {
			rearranges := a.Have(
				"p leaves s where it is: it lands inside s, and the preimages "+
					"reach every point of s, so the image is s over again",
				"image(p, s) = s",
				BySets(bij))

			separates := a.Have(
				"and it tells the points of s apart — two of them sent to one "+
					"place are two preimages of a point of s, which has only one",
				"injective_on(s, p)",
				Simp(Fwd(functions.InjectiveOnDef.Inst(TypeBinder.BindA[index](), TypeBinder.BindB[index]()))),
				By(bij))

			// The transport across p of the summand f at s — Image's own
			// headline read at this member's reindexing.
			transported := a.Have(
				"so Image transports the fold across p — separating the points "+
					"it is applied to is the one thing that law asks of a reindexing",
				"iterated_op(op, image(p, s), f) = iterated_op(op, s, o(f, p))",
				By(mon, separates, Image))

			// Normalized: the goal is the transport with its image rewritten
			// by the equation already resident, so simplifying against the
			// two is the whole step. It is the member's one shaping —
			// measured, it removes a key here, and at each of the three
			// closes above it removes nothing, so none of them carries one.
			a.Show(
				"and the image being s over again, the fold it transports is the fold the theorem starts from",
				By(Normalized, rearranges, transported))
		}),
})}

// Injection — a fold over a finite index set is blind to a reindexing
// that stays inside the set and tells the set's points apart.
//
// `Bijection` already says this of a rearrangement, and it asks to be
// shown one: every point of `s` reached from exactly one point of `s`.
// Only the "at most one" half is given here. Finiteness supplies the
// other half for nothing, and that is the whole content of this member:
// a map of a finite set into itself is filling as many places as it has
// points to place, so leaving a place empty would make two points share
// one, which telling them apart forbids. That is
// `cardinality.SurjectiveIffInjective`, read in the direction that
// trades separation for reach.
//
// So the argument has one turn — strengthen the hypothesis into the one
// `Bijection` wants, then cite it — and finiteness, which the counting
// law needs and `Bijection` does not, is exactly what this headline adds
// over its own.
//
// The containment that law asks for is membership, so it goes to the set
// driver, this chapter's usual course, and the image-membership row the
// seed took it apart with is not wanted.
var Injection = injectionThm{family.Add(registry.ProofEntry{
	Name: "Injection",
	Key:  "prop_ec5730fd0906f6db",
	Build: MonoidalOp.Law(
		Statement{
			Binders: "∀f:(A → B). ∀p:(A → A). ∀s:set(A).",
			Hypotheses: []string{
				"finite(s)",
				"(∀x:A. x ∈ s ⇒ p(x) ∈ s) ∧ injective_on(s, p)",
			},
			Conclusion: "iterated_op(op, s, o(f, p)) = iterated_op(op, s, f)",
		},
		func(
			a *Argument,
			op *Arrow2[carrier, carrier, carrier],
			mon Fact,
			f *Arrow[index, carrier],
			p *Arrow[index, index],
			s *Expr[indexSet],
			injectiveSelfMap Fact,
		) {
			// The preimage condition below appears at the two strengths the
			// argument passes through: some point of s is sent to y, and —
			// once p is known to separate points — exactly one is. The
			// second reading is what `Bijection` asks for.
			inside := a.Have(
				"nothing s is carried to lies outside s — the standing self-map condition, in containment form",
				"image(p, s) ⊆ s",
				BySets(injectiveSelfMap))

			onto := a.Have(
				"and a separating self-map of a finite set must reach all of it: "+
					"as many places to fill as points to place, so none is left over",
				"∀y:A. y ∈ s ⇒ ∃x:A. x ∈ s ∧ p(x) = y",
				// The counting law at (s, p): its set slot filled by s, its
				// map slot by p, the order its own statement binds them in.
				// The finiteness it asks for, and the separation it trades
				// against, both come from the standing hypothesis; the
				// containment is what `inside` recast for it.
				//
				// Its equivalence is not taken apart: the arm standing here
				// is one of the two, the arm wanted is the other, so one
				// citation carries the trade.
				By(inside, injectiveSelfMap, At(cardinality.SurjectiveIffInjective, s, p)))

			permutes := a.Have(
				"so every point of s is reached, and reached from one "+
					"point only, p telling its preimages apart: p rearranges s",
				"∀y:A. y ∈ s ⇒ ∃!x:A. x ∈ s ∧ p(x) = y",
				By(onto, a.Unfolded(injectiveSelfMap, functions.InjectiveOnDef)))

			// Bijection at (op, f, p, s), its headline's own binder order.
			//
			// That law delivers the equation the other way round from the
			// one stated here, and no flip step stands between them: an
			// equation and its reverse are one proposition, so the two
			// spellings reach the same place.
			a.Show(
				"and a fold over s cannot tell s rearranged from s",
				By(mon, permutes, injectiveSelfMap, At(Bijection, op, f, p, s)))
		}),
})}

// What this file means by a matching is two clauses — every point of
// `t` has exactly one preimage in `s`, and `h` sends `s` into `t`
// taking `f`'s value at a point to `g`'s value at its partner.
// `ReindexGeneral` states them, `Reindex` produces them from an
// inverse in the same words — the claim there is proved in the phrase
// this law will be handed.
//
// ReindexGeneral — two folds agree when a matching pairs their index
// sets point for point and carries one summand to the other. `h` is the
// matching: every point of `t` has exactly one preimage in `s`, and `h`
// sends `s` into `t` taking `f`'s value at a point to `g`'s value at its
// partner.
//
// Like `Image` and `Swap`, this member has TWO index types — `A` for the
// set folded over on the left, `C` for the one on the right — with the
// carrier at the chapter's `B`.
//
// The hypothesis is what the word "matching" means, and its two halves
// between them say that `h` is a bijection of `s` onto `t`. Nothing in
// `t` is missed, because each of its points has a preimage; nothing
// outside `t` is hit, because `h` sends `s` into `t`; and no point of
// `t` is hit twice, because a second preimage is exactly what "exactly
// one" forbids. That last reading is the one worth pausing on — the
// uniqueness clause is doing the work of an injectivity hypothesis, and
// it is `Image`'s whole precondition.
//
// So the set-theoretic content of the theorem is one fact, and the
// membership driver reads it off the hypothesis in one call. After it
// the argument is a chain of two transports already in the chapter:
// `Congruence` exchanges `f` for `g` after `h`, the two agreeing at
// every point of `s` because the matching says so, and `Image` carries
// that composite fold onto the set `h` reaches — which the matching has
// already named as `t`.
var ReindexGeneral = reindexGeneralThm{family.Add(registry.ProofEntry{
	Name: "ReindexGeneral",
	Key:  "prop_b0991068729ab7e5",
	Build: MonoidalOp.Law(
		Statement{
			Binders: "∀s:set(A). ∀t:set(C). ∀f:(A → B). ∀g:(C → B). ∀h:(A → C).",
			Hypotheses: []string{
				"∀y:C. y ∈ t ⇒ ∃!x:A. x ∈ s ∧ h(x) = y",
				"∀x:A. x ∈ s ⇒ h(x) ∈ t ∧ g(h(x)) = f(x)",
			},
			Conclusion: "iterated_op(op, s, f) = iterated_op(op, t, g)",
		},
		func(
			a *Argument,
			op *Arrow2[B, B, B],
			mon Fact,
			s *Expr[Set[A]],
			t *Expr[Set[C]],
			f *Arrow[A, B],
			g *Arrow[C, B],
			h *Arrow[A, C],
			corr Fact,
		) {
			// The summand the left side is carried onto — `g` read after
			// the matching — as a term for the Congruence cite below.
			composite := a.Term("o(g, h)")

			// One fact and not two: being a bijection of `s` onto `t` is a
			// single condition on `h`, and the two clauses are its two
			// halves — the second is `Image`'s own precondition, in that
			// member's phrase, the first what names the set it produces.
			// Asking the driver for them together also costs one key where
			// asking separately costs two.
			matching := a.Have(
				"h matches s with t point for point: t is exactly what "+
					"h reaches from s, and h reaches no point of it twice",
				"t = image(h, s) ∧ injective_on(s, h)",
				Simp(Fwd(functions.InjectiveOnDef.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[C]()))),
				BySets(corr))

			agree := a.Have(
				"and on s, f is g read after h — the matching's other promise, with the composite read at a point",
				"∀x:A. x ∈ s ⇒ f(x) = o(g, h)(x)",
				By(Normalized, corr, functions.ComposeApply))

			a.Do(CalcEq(
				Leg(
					a.Term("iterated_op(op, s, o(g, h))"),
					"exchange the summand for g after h — a fold sees no "+
						"more of a summand than its values on the index set",
					By(mon, agree, At(Congruence, op, s, f, composite))),
				Leg(
					a.Term("iterated_op(op, image(h, s), g)"),
					"and carry that fold onto the set h reaches, the matching losing nothing on the way",
					By(mon, matching, At(Image, op, h, g, s))),
				// Normalized: the set h reaches is already known to be t, so
				// this last step is simplification against a resident
				// equation and no refutation is wanted — measured, and the
				// only site in the member where the shaping earns anything.
				FinalLeg(
					"and that set is t",
					By(Normalized, matching)),
			))
		}),
})}

// Reindex — the same theorem with the matching given by an explicit
// inverse. `k` returns each point of `t` to a point of `s` that `h`
// sends back to it, `h` sends each point of `s` to a point of `t` that
// `k` returns to it, and `g` after `h` is `f`. That is how a matching
// usually comes to hand: one names the correspondence together with the
// way back, rather than asserting that a preimage is unique.
//
// Like `ReindexGeneral`, `Image` and `Swap`, this member has THREE type
// variables — `A` the index set folded over on the left, `C` the one on
// the right, `B` the carrier as everywhere in the chapter.
//
// All the content is that the way back delivers the matching
// `ReindexGeneral` asks for, and delivers every part of it at once:
// `k(y)` is a preimage of `y`, so each point of `t` has one; `k` sends
// every point of `s` back to itself through `h`, so that preimage is the
// only one; and `g` after `h` is `f` by assumption. The membership driver
// reads all three off the hypothesis in a single call, after which the
// inverse is spent — and what is left standing IS the general law, so the
// proof closes by citing it rather than by deducing anything.
var Reindex = reindexThm{family.Add(registry.ProofEntry{
	Name: "Reindex",
	Key:  "prop_c439c0a8fea6e13e",
	Build: MonoidalOp.Law(
		Statement{
			Binders: "∀s:set(A). ∀t:set(C). ∀f:(A → B). ∀g:(C → B). ∀h:(A → C). ∀k:(C → A).",
			Hypotheses: []string{
				"∀y:C. y ∈ t ⇒ k(y) ∈ s ∧ h(k(y)) = y",
				"∀x:A. x ∈ s ⇒ h(x) ∈ t ∧ k(h(x)) = x ∧ g(h(x)) = f(x)",
			},
			Conclusion: "iterated_op(op, s, f) = iterated_op(op, t, g)",
		},
		func(
			a *Argument,
			op *Arrow2[B, B, B],
			mon Fact,
			s *Expr[Set[A]],
			t *Expr[Set[C]],
			f *Arrow[A, B],
			g *Arrow[C, B],
			h *Arrow[A, C],
			k *Arrow[C, A],
			inv Fact,
		) {
			// One fact and not two, as in `ReindexGeneral`: being a matching
			// of s with t is a single condition on h, and the two clauses
			// are two readings of it. Each is asked for in the phrase that
			// law states it in, so what is proved here is what it will be
			// handed. Asking the driver for both at once also costs one key
			// where asking separately costs two — measured; and the driver
			// declines this leaf outright if its context is shaped first.
			a.Have(
				"h matches s with t: k(y) is a preimage of each point of "+
					"t, k(h(x)) = x leaves it the only one, and g after h is f",
				"(∀y:C. y ∈ t ⇒ ∃!x:A. x ∈ s ∧ h(x) = y) ∧ (∀x:A. x ∈ s ⇒ h(x) ∈ t ∧ g(h(x)) = f(x))",
				BySets(inv))

			// The inverse is now spent: it was wanted for the matching and
			// the law asks nothing further of it, so it goes. What that
			// leaves — monoidal_op(op), the matching, and the equation — is
			// what `ReindexGeneral` states at these binders, so the close is
			// that one citation and not a deduction. Dropping the inverse is
			// what makes the leaf coincide with the law; kept, it is an extra
			// premise the law does not carry, and a premise list cannot say
			// "and nothing else" while still closing by citation.
			a.Show(
				"so h is a matching of s with t, and the general law is already that statement",
				Clear(inv),
				Cite(ReindexGeneral))
		}),
})}

// The index set is bound BEFORE the test, which is the twin's own order
// and is load-bearing for citers: a ground cite's tuple
// is reordered onto the install prefix BY NAME, and `Normalize` renames
// this statement's test binder, so the name map misses and the tuple
// falls through positionally. With the stated order matching the install
// prefix that fallthrough is harmless; with the two swapped it silently
// produced a type-correct wrong instance.
//
// Restrict — narrowing a fold's index set to the points a test accepts,
// and silencing its summand off those points, come to the same thing.
// The rejected points contribute the neutral either way: the first
// reading never reaches them, the second reaches them and finds nothing
// there.
//
// The index half is `acceptedHalf` from the homomorphism part rather than a second
// spelling of it. `Split` cuts an index set at a test where this member
// restricts one to a test, so it is literally the same set, and the two
// headlines should not be able to disagree about it.
//
// No finiteness is asked, and here — unlike `Closed` and `Congruence`,
// the chapter's other two finiteness-free members — that costs nothing,
// so there is no split on a support. Both laws spent below are
// themselves finiteness-free, `Congruence` because it has already paid
// for that split and `Superset` because it is the support tier read
// through the fold, so the absent hypothesis is never wanted.
//
// The argument reads the accepted half twice, and it is the midpoint of
// the theorem. Over it the silencing never fires, so the two summands
// agree there and `Congruence` exchanges one for the other; outside it
// the silenced summand is the neutral, so `Superset` widens the index
// set back to `s` without the fold moving. Composing those two steps is
// the whole proof.
//
// Both facts they ask for are membership, and each closes under a bare
// set driver: what `x ∈ {x | x ∈ s ∧ P(x)}` says is that `x` lies in `s`
// and answers the test, which decides the summand's `COND` at the same
// time.
var Restrict = restrictThm{family.Add(registry.ProofEntry{
	Name: "Restrict",
	Key:  "prop_f8fa54a4e8347b28",
	Build: MonoidalOp.Law(Statement{
		Binders:    "∀s:set(A). ∀P:(A → bool). ∀f:(A → B).",
		Conclusion: "iterated_op(op, «acceptedHalf», f) = iterated_op(op, s, «silencedSummand»)",
		Abbrev: Abbrev{
			{Name: "silencedSummand", Text: "λx:A. COND(P(x), f(x), neutral_elem(op))"},
		},
	},
		func(
			a *Argument,
			op *Arrow2[carrier, carrier, carrier],
			mon Fact,
			s, P *Expr[indexSet],
			f *Arrow[index, carrier],
		) {
			ctx := a.Ctx()

			// The accepted half as a comprehension, and the summand the
			// fold laws carry over it — the two spellings the headline is
			// built from.
			acceptedSet := a.Term("«acceptedHalf»")
			silenced := a.Term("«silencedSummand»")

			// The name the half carries from the midpoint on — declared
			// here as the typed witness the cites below want (`Denote`
			// registers the spelling too, idempotently).
			accepted := ctx.VarAs[indexSet]("accepted")

			// The two facts below are each read TWICE — at the
			// comprehension here, and again at the name the half is given
			// halfway through; a drift between the readings fails loudly
			// at the Hyp lookup.
			//
			// One fact per law, not one per clause: what `Superset` asks of
			// an enlargement is a single mathematical condition, and asking
			// the driver for it whole reads better at no cost — measured,
			// splitting it in two records the same keys.
			a.Have(
				"on the accepted half the test holds, so the silencing "+
					"never fires and the two summands are one there",
				"∀y:A. y ∈ «acceptedHalf» ⇒ f(y) = COND(P(y), f(y), neutral_elem(op))",
				BySets())

			a.Have(
				"while the enlargement back to s is invisible: the half lies "+
					"inside s, and every point s adds is one the test rejects",
				"«acceptedHalf» ⊆ s ∧ "+
					"(∀y:A. y ∈ s ∧ ¬(y ∈ «acceptedHalf») ⇒ COND(P(y), f(y), neutral_elem(op)) = neutral_elem(op))",
				BySets())

			// Everything the comprehension was needed for has now been
			// said, so the half is named and never opened again.
			//
			// The naming is load-bearing rather than cosmetic. A
			// comprehension still standing in a leaf the refuter reaches
			// gets opened into its ∃/comprehension_spec form and searched there, and
			// the search does not come back — measured on the congruence
			// step below, which does not close inside a five-second budget
			// at the comprehension and closes at once at the name.
			// Membership is the set driver's business and it reads
			// comprehensions natively; the refuter is not asked to.
			a.Denote("accepted", acceptedSet)

			// The two facts again, at the name. A denote rewrites every
			// hypothesis in one step, which leaves no fact handle a unique
			// successor to follow, so each is named afresh on this side.
			agrees := a.Hyp("∀y:A. y ∈ accepted ⇒ f(y) = COND(P(y), f(y), neutral_elem(op))")
			enlargement := a.Hyp(
				"accepted ⊆ s ∧ " +
					"(∀y:A. y ∈ s ∧ y ∉ accepted ⇒ COND(P(y), f(y), neutral_elem(op)) = neutral_elem(op))")

			sameSummand := a.Have(
				"so across that half the two summands fold alike — agreeing "+
					"at each of its points is all a fold can see of a summand",
				"iterated_op(op, accepted, f) = iterated_op(op, accepted, «silencedSummand»)",
				By(mon, agrees, At(Congruence, op, accepted, f, silenced)))

			widened := a.Have(
				"and the points s adds back around the half are "+
					"exactly the silent ones, which a fold cannot see either",
				"iterated_op(op, accepted, «silencedSummand») = iterated_op(op, s, «silencedSummand»)",
				By(enlargement, At(Superset, op, accepted, s, silenced)))

			// Naming the half puts the spine in ⊥-form — the conclusion is
			// negated into the hypotheses, as after a "suppose not" — so
			// the close is a refutation, and the supposition is one of its
			// named premises.
			differ := a.Hyp("iterated_op(op, accepted, f) ≠ iterated_op(op, s, «silencedSummand»)")

			a.Show(
				"so the restricted fold reaches the silenced one in two "+
					"steps through that half, and the supposition cannot stand",
				By(differ, sameSummand, widened))
		}),
})}

// Fibres — folding `g` over an index set agrees with folding, over each
// point of that set's image under `f`, the fold of `g` over the fibre
// there. The fibres partition the index set, so each point is counted
// exactly once on either side.
//
// This member has TWO index types, `A` for the source and `C` for the
// target where the fibres are indexed, the carrier staying at the
// chapter's `B` — `Swap`'s and `Image`'s arrangement.
//
// The whole argument turns on ONE device, read in its two directions.
// Fix a point p of the index set and consider the summand over the
// TARGET index that is g(p) at f(p) and the neutral elsewhere: folding
// it over the whole image returns g(p), because the image is silent
// away from that single point. Fix instead a point q of the target and
// read the SAME two-place summand along its other argument: it is g
// where f lands on q and the neutral elsewhere, so folding it over the
// source index set is folding g over q's fibre. Between those two
// readings sits one double fold, and `Swap` exchanges its two index
// sets — which is the whole proof, and where the theorem's finiteness
// is spent.
//
// So the chain is: concentrate each point's value into a fold over the
// image, exchange the two folds, and collect each target point's fibre.
// Both outer moves are `Congruence`, the fold being unable to tell two
// summands apart that agree at each point of its index set; both inner
// ones are `Restrict`, silencing a summand off a test being the same as
// narrowing the index set to it. `Sing` evaluates the one-point fold
// the first move leaves, and the single membership fact the proof needs
// says which point that is.
var Fibres = fibresThm{family.Add(registry.ProofEntry{
	Name: "Fibres",
	Key:  "prop_53d2b6d5fa0ab964",

	Build: MonoidalOp.Law(Statement{
		Binders: "∀f:(A → C). ∀g:(A → B). ∀s:set(A).",
		Hypotheses: []string{
			"finite(s)",
		},
		Conclusion: "iterated_op(op, s, g) = " +
			"iterated_op(op, image(f, s), λy:C. iterated_op(op, {x | x ∈ s ∧ f(x) = y}, g))",
	},
		func(a *Argument, op *Arrow2[B, B, B], mon Fact, f *Arrow[A, C],
			g *Arrow[A, B], s *Expr[Set[A]], sFinite Fact) {

			// The chapter's laws at THIS member's letters: the index is
			// `A` on the source side and `C` on the target side — the
			// parameter types above say so once, and every ground cite
			// below re-derives its own instantiation from its typed
			// witnesses (the At/Cite forms). Only the one BARE premise,
			// having no witnesses to infer from, still spells its types
			// (Congruence.Inst at the final leg, read at the target index).

			// Every ground cite of one of those laws below is followed by a
			// normalization and by nothing else. Each arrives as a single
			// clause with its guards — `monoidal_op(op)`, and for the exchange
			// the two finiteness conditions — negated into it, and every
			// guard is settled by a resident fact, so what closes such a
			// leaf is simplification. Reaching for a refutation instead is
			// not merely wasteful: the two `Restrict` leaves still carry a
			// comprehension, and the refuter opens one into its ∃/comprehension_spec
			// form and does not come back.

			// The image as a typed term, for the exchange's witness tuple.
			image := a.TermAs[Set[C]]("image(f, s)")

			// The device, in its two readings. The CONCENTRATED summand at
			// a point p of s lives over the TARGET index, carrying g's
			// value at p to f(p) and the neutral everywhere else; the
			// SIFTED summand at a target point q lives over the SOURCE
			// index, carrying g where f lands on q and the neutral
			// everywhere else. They are one two-place summand read along
			// its two arguments — which is exactly what `Swap` needs, and
			// why `bothWays` is that summand itself.
			bothWays := a.TermAs[Fun2[A, C, B]]("λx:A. λy:C. COND(f(x) = y, g(x), neutral_elem(op))")

			// Spent by being resident: the exchange below carries both
			// finiteness guards inside the one clause it arrives as, and
			// normalization settles them against this and the theorem's own
			// hypothesis without either being named.
			a.Have(
				"the image of a finite index set is finite, so the "+
					"exchange below has finiteness on both its index sets",
				"finite(image(f, s))",
				By(sFinite, finite_set.FiniteImage.At(f, s)))

			concentrates := a.Have(
				"at each point of s, folding that point's concentrated "+
					"summand over the whole image returns g's value there",
				"∀p:A. p ∈ s ⇒ g(p) = iterated_op(op, image(f, s), λy:C. COND(f(p) = y, g(p), neutral_elem(op)))",
				Derive(func(b *Argument) {
					b.FixAs[A]() // p — the claims below spell it by name
					inS := b.Assume()

					// The concentrated summand's test and its value, at the
					// point just fixed — the two terms the laws below are
					// grounded at, and the same two the claims are stated
					// over.
					lands := b.TermAs[Set[C]]("λy:C. f(p) = y")
					value := b.TermAs[Fun[C, B]]("λy:C. g(p)")

					// The narrowing comes FIRST, and not only because it reads
					// that way: the membership fact below is an equation
					// between two sets, and once resident it rewrites this
					// claim's comprehension into the one-point set before the
					// law can be cited at it.
					//
					// The comprehension's binder carries its type: it ranges
					// over the TARGET index, which the parser types left to
					// right and so cannot read off the membership that
					// follows.
					narrows := b.Have(
						"silencing that summand off the point is the same as "+
							"narrowing the fold onto the points the test picks out",
						"iterated_op(op, {y:C | y ∈ image(f, s) ∧ f(p) = y}, λy:C. g(p)) = "+
							"iterated_op(op, image(f, s), λy:C. COND(f(p) = y, g(p), neutral_elem(op)))",
						Cite(Restrict, op, image, lands, value))

					// Membership is the set driver's business and it reads
					// comprehensions natively, so it is asked here and the
					// fold laws never see one again. The one-point set lives
					// at the TARGET index type, which neither constructor's
					// chapter declaration can see — insert is carried across
					// by an explicit pin, ∅ by `emptySecond`, the homomorphism part's
					// spelling of the same move.
					hit := b.Have(
						"and inside the image the test picks out the single point "+
							"f(p) — p itself is why that point is in the image at all",
						"{y:C | y ∈ image(f, s) ∧ f(p) = y} = insert⟨A:var:C⟩(f(p), «emptySecond»)",
						BySets(inS))

					b.Show(
						"so what is left is a fold over one point, which is that point's value",
						CalcEq(
							Leg(
								b.Term("iterated_op(op, insert⟨A:var:C⟩(f(p), «emptySecond»), λy:C. g(p))"),
								"a fold over one point gives back the summand's value there, read backwards",
								Cite(Sing, op, value, b.TermAs[C]("f(p)")),
								TrivialNormalized()),
							FinalLeg(
								"and that one point is what the test picked out, so the narrowing already reaches the whole image",
								By(narrows, hit))))
				}))

			fibres := a.Have(
				"and at each point of the target, sifting the whole index "+
					"set by where f lands is folding over that point's fibre",
				"∀q:C. "+
					"    iterated_op(op, s, λx:A. COND(f(x) = q, g(x), neutral_elem(op))) = "+
					"    iterated_op(op, {x | x ∈ s ∧ f(x) = q}, g)",
				Derive(func(b *Argument) {
					b.FixAs[C]() // q — the cite below spells it by name
					b.Show(
						"the restriction law, read at the test that f lands on q",
						Cite(Restrict, op, s,
							b.TermAs[Set[A]]("λx:A. f(x) = q"), g),
						TrivialNormalized())
				}))

			a.Show(
				"so the fold is read through the image in three moves: concentrate, exchange, collect",
				CalcEq(
					Leg(
						a.Term(
							"iterated_op(op, "+
								"    s, "+
								"    λx:A. iterated_op(op, image(f, s), λy:C. COND(f(x) = y, g(x), neutral_elem(op))))"),
						"each point's value becomes the fold of its concentrated summand over "+
							"the image — folds cannot tell two summands apart that agree pointwise",
						By(
							mon,
							concentrates,
							Congruence.At(op, s, g,
								a.TermAs[Fun[A, B]](
									"λx:A. iterated_op(op, image(f, s), λy:C. COND(f(x) = y, g(x), neutral_elem(op)))")))),

					Leg(
						a.Term(
							"iterated_op(op, "+
								"    image(f, s), "+
								"    λy:C. iterated_op(op, s, λx:A. COND(f(x) = y, g(x), neutral_elem(op))))"),
						"and a double fold does not care which of its two index sets is taken first, both being finite",
						// The cite's guards — monoidal_op(op) and both finiteness
						// facts — are in hand, so its instance is the leg.
						Cite(Swap, op, s, image, bothWays)),

					FinalLeg(
						"leaving at each point of the image the sifted fold "+
							"over s, which is the fold over that point's fibre",
						By(mon, fibres, Congruence.Inst(TypeBinder.BindB[B](), TypeBinder.BindA[C]())))))
		}),
})}

// Regroup — fold the fibres of a finite index set over any set covering
// its image. Unreached points have empty fibres and contribute the neutral.
var Regroup = regroupThm{family.Add(registry.ProofEntry{
	Name: "Regroup",
	Key:  "prop_63b23c35eaef82cc",
	Build: MonoidalOp.Law(Statement{
		Binders: "∀f:(A → C). ∀g:(A → B). ∀s:set(A). ∀t:set(C).",
		Hypotheses: []string{
			"finite(s)",
			"image(f, s) ⊆ t",
		},
		Conclusion: "iterated_op(op, t, «fibreTotals») = iterated_op(op, s, g)",
		Abbrev: Abbrev{
			{Name: "fibreTotals", Text: "λy:C. iterated_op(op, {x:A | x ∈ s ∧ f(x) = y}, g)"},
		},
	},
		func(a *Argument, op *Arrow2[B, B, B], mon Fact, f *Arrow[A, C],
			g *Arrow[A, B], s *Expr[Set[A]], t *Expr[Set[C]], finiteAndCovered Fact) {
			vanishes := a.Have(
				"an unreached point has an empty fibre, whose fold is neutral",
				"∀y:C. y ∈ t ∧ y ∉ image(f, s) ⇒ iterated_op(op, {x:A | x ∈ s ∧ f(x) = y}, g) = neutral_elem(op)",
				Derive(func(b *Argument) {
					b.FixAs[C]("y")
					offImage := b.Assume()
					fibre := b.TermAs[Set[A]]("{x:A | x ∈ s ∧ f(x) = y}")
					b.Show(
						"no point of s reaches y, so the summand is neutral on its fibre vacuously",
						BySets(offImage, EqNeutral.Read(mon).At(fibre, g)))
				}))
			image := a.TermAs[Set[C]]("image(f, s)")
			fibreTotals := a.TermAs[Fun[C, B]]("«fibreTotals»")
			widened := a.Have(
				"adding the unreached points does not change the fold of fibre totals",
				"iterated_op(op, image(f, s), «fibreTotals») = iterated_op(op, t, «fibreTotals»)",
				By(vanishes, finiteAndCovered, Superset.At(op, image, t, fibreTotals)))
			a.Show(
				"over the image the fibre totals recover the original fold",
				By(widened, finiteAndCovered, Fibres.Read(mon).At(f, g, s)))
		}),
})}

// ---------------------------------------------------------------------------
// Folding a doubly-indexed family, one index at a time or both at once
// ---------------------------------------------------------------------------
//
// The outer index has type A, the inner index C, and the carrier B.

// Fubini — fold a finite family of finite fibres either one fibre at a
// time or over all index pairs. Each fibre is transported by j ↦ (y, j),
// and Regroup gathers the pair fold along the first coordinate.
var Fubini = fubiniThm{family.Add(registry.ProofEntry{
	Name: "Fubini",
	Key:  "prop_f1843c8841ab2990",
	Build: MonoidalOp.Law(Statement{
		Binders: "∀s:set(A). ∀t:(A → set(C)). ∀x:(A → C → B).",
		Hypotheses: []string{
			"finite(s)",
			"∀i. i ∈ s ⇒ finite(t(i))",
		},
		Conclusion: "iterated_op(op, s, λi:A. iterated_op(op, t(i), x(i))) = " +
			"«pairIterate»(op, «pairIndexSet», «pairedSummand»)",
		Abbrev: Abbrev{
			{Name: "pairIndexSet", Text: "{(i, j) | i:A, j:C | i ∈ s ∧ j ∈ t(i)}"},
			{Name: "pairIterate", Text: "iterated_op⟨A:prod(var:A,var:C)⟩"},
			{Name: "pairsAtY", Text: "{p:prod(A, C) | p ∈ «pairIndexSet» ∧ fst(p) = y}"},
			{Name: "pairedSummand", Text: "λ(i, j). x(i, j)"},
			{Name: "perFibre", Text: "λy:A. " +
				"    «pairIterate»(op, {p:prod(A, C) | p ∈ «pairIndexSet» ∧ fst(p) = y}, «pairedSummand»)"},
		},
	},
		func(
			a *Argument,
			op *Arrow2[B, B, B],
			mon Fact,
			s *Expr[Set[A]],
			t *Arrow[A, Set[C]],
			x *Arrow2[A, C, B],
			hyps Fact,
		) {
			ctx := a.Ctx()
			carrier, pairIndex := MakeVarType("B"), pairs.ProdType(MakeVarType("A"), MakeVarType("C"))
			ctx.Const(
				"pattern_abstraction",
				MakeFun(MakeFun(MakeFun(pairIndex, carrier), TypeBool), MakeFun(pairIndex, carrier)))
			fst, _ := pairs.ProjectionsAt(ctx, MakeVarType("A"), MakeVarType("C"))
			transportOntoPairs := Image.Inst(
				TypeBinder.BindB[B](), TypeBinder.BindA[C](), TypeBinder.BindC[Prod[A, C]]())
			regroupOverPairs := Regroup.Inst(
				TypeBinder.BindB[B](), TypeBinder.BindA[Prod[A, C]](), TypeBinder.BindC[A]())
			pairsTerm := a.TermAs[Set[Prod[A, C]]]("«pairIndexSet»")
			innerTerm := a.TermAs[Fun[A, B]]("λi:A. iterated_op(op, t(i), x(i))")
			perFibreTerm := a.TermAs[Fun[A, B]]("«perFibre»")

			// Keep the raw implication so conditional rewriting matches the
			// pair constructor and discharges finiteness from hyps.
			productFinite := ctx.AtTypeVars(ctx.Dep(finite_set.FiniteProductDependent),
				TypeBinder.BindA[A](), TypeBinder.BindB[C](), TypeBinder.BindC[Prod[A, C]]()).Reference()

			pairFinite := a.Have(
				"a finite base, each point with a finite fibre — so the index pairs are finitely many",
				"finite(«pairIndexSet»)",
				By(hyps, productFinite))

			imgSub := a.Have(
				"every first coordinate the pairs take lies in the base",
				"image(fst, «pairIndexSet») ⊆ s",
				BySets(pairs.Fst))

			groupAlongFst := a.Have(
				"regrouping the pair fold along its first coordinate folds the fibres over the whole base",
				"∀h:(prod(A, C) → B). "+
					"    iterated_op(op, "+
					"        s, "+
					"        λy:A. «pairIterate»(op, {p:prod(A, C) | p ∈ «pairIndexSet» ∧ fst(p) = y}, h)) = "+
					"    «pairIterate»(op, «pairIndexSet», h)",
				Derive(func(b *Argument) {
					h := b.FixAs[Fun[Prod[A, C], B]]()
					b.Show(
						"the pair set is finite and all its first coordinates lie in s",
						By(mon, pairFinite, imgSub, At(regroupOverPairs, op, fst, h, pairsTerm, s)))
				}))

			innerFolds := a.Have(
				"at each base point, the inner fold is the paired summand folded over the pairs there",
				Statement{
					Binders: "∀y:A.",
					Hypotheses: []string{
						"y ∈ s",
					},
					Conclusion: "iterated_op(op, t(y), x(y)) = " +
						"«pairIterate»(op, {p:prod(A, C) | p ∈ «pairIndexSet» ∧ fst(p) = y}, «pairedSummand»)",
				},
				Derive(func(b *Argument) {
					b.FixAs[A]() // y — the claims below spell it by name
					inBase := b.Assume()

					pairingTerm, fibreTerm := b.Term("λj:C. (y, j)"), b.Term("t(y)")

					pairsAt := b.Have(
						"the pairs over the point are its own fibre, carried across by the pairing",
						"«pairsAtY» = image(λj:C. (y, j), t(y))",
						BySets(inBase, pairs.Fst))

					faithful := b.Have(
						"pairing the point with each fibre point loses nothing — a pairing determines its components",
						"injective_on(t(y), λj:C. (y, j))",
						Simp(Fwd(functions.InjectiveOnDef.Inst(TypeBinder.BindA[C](), TypeBinder.BindB[Prod[A, C]]()))),
						BySets(pairs.PairEq))

					pairedLambda := ctx.AtTypeVars(ctx.Dep(pairs.PairedLambda),
						TypeBinder.BindA[A](), TypeBinder.BindB[C](), TypeBinder.BindC[B]())

					composed := b.Have(
						"and reading the paired summand after that pairing is reading x at the point",
						"o⟨A:var:C,B:prod(var:A,var:C),C:var:B⟩(«pairedSummand», λj:C. (y, j)) = x(y)",
						Funext(),
						StripQuant(),
						Unfold(functions.ComposeApply),
						Expect(LeanRw(pairedLambda.Reference()),
							Case(
								"what a paired abstraction of a two-argument summand does: project, then apply",
								Cite(pairedLambda)),
							Case(
								"so at a literal pairing the projections take back the two components they were given",
								pairs.Collapse(ctx))))

					transports := b.Have(
						"the slice is a faithful copy of the fibre, so a fold "+
							"over it pulls back along the pairing — whatever it folds",
						"∀g:(prod(A, C) → B). "+
							"    «pairIterate»(op, image(λj:C. (y, j), t(y)), g) = "+
							"    iterated_op(op, t(y), o⟨A:var:C,B:prod(var:A,var:C),C:var:B⟩(g, λj:C. (y, j)))",
						Derive(func(c *Argument) {
							g := c.FixAs[Fun[Prod[A, C], B]]()
							c.Show(
								"the transport law, read along the pairing",
								By(mon, faithful, At(transportOntoPairs, op, pairingTerm, g, fibreTerm)))
						}))

					b.Have(
						"so the slice's fold is the fold of x at the point over that point's fibre",
						"«pairIterate»(op, image(λj:C. (y, j), t(y)), «pairedSummand») = iterated_op(op, t(y), x(y))",
						CalcEq(
							Leg(
								b.Term(
									"iterated_op(op, t(y), o⟨A:var:C,B:prod(var:A,var:C),C:var:B⟩(«pairedSummand», λj:C. (y, j)))"),
								"the slice being a faithful copy, the fold pulls back along the pairing",
								By(transports)),
							FinalLeg(
								"and the summand it pulls back is x at the point, by the equation just proved",
								composed.Rw(),
								Basic())))

					b.Show(
						"substitute the fibre's copy for the pairs over the point, and the two folds meet",
						pairsAt.Rw(), // ↦ the slice's fold, read the other way round
						Symm(),
						Assumption())
				}))

			a.Show(
				"replace each inner fold by its pair fibre and regroup the pair fold along fst",
				CalcEq(
					Leg(
						a.TermAs[B]("iterated_op(op, s, «perFibre»)"),
						"each original fibre and its paired copy have the same fold",
						By(innerFolds, Congruence.Read(mon).At(s, innerTerm, perFibreTerm))),
					FinalLeg(
						"regrouping along the first coordinate recovers the fold over all pairs",
						By(groupAlongFst))))
		}),
})}
