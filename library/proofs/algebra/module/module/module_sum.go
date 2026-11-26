// module_sum.go — finite sums in a module on a set: the fold of a
// family over a finite index set under the module's addition, from
// the module's zero. The whole-type iterated operation
// (iterate/monoidal) takes its neutral element from the type; a module
// on a set names its own, so the sum is its own definition. The fold's
// step reads the family on the index set only — off it the step is
// the identity — so a sum is determined by the family's values on its
// indices, and the fold's laws hold for a step closed and
// left-commutative on the carrier (cardinality's fold laws within a
// set), which a family valued in the carrier supplies.

package module

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_algebra"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/registry"
)

// ModuleSumDef — `module_sum(add, zero, s, F)`: the sum of F(x) over x
// in s under the addition add, folded from zero; an index off s
// contributes nothing. A module's sum is `module_sum(M.add, M.zero, s,
// F)`, a ring's `module_sum(R.add, R.zero, s, F)`.
var ModuleSumDef = moduleSumDefThm{family.Define(registry.DefEntry{
	Name:  "ModuleSumDef",
	Key:   "prop_58b48b83a303e625",
	Const: "module_sum",
	Type:  "(B → B → B) → B → set(D) → (D → B) → B",
	Equations: []string{
		"∀add:(B → B → B). ∀zero:B. ∀s:set(D). ∀F:(D → B). " +
			"    module_sum(add, zero, s, F) = set_fold((λx:D. λa:B. COND(x ∈ s, add(F(x), a), a)), s, zero)",
	},
})}

// ModuleSumEmpty — the empty sum is the fold over ∅ of a step that acts
// at no index, so it returns its start untouched.
var ModuleSumEmpty = moduleSumEmptyThm{family.Add(registry.ProofEntry{
	Name: "ModuleSumEmpty",
	Key:  "prop_33561642a5bcdcf0",
	Build: family.Theorem("∀add:(B → B → B). ∀zero:B. ∀F:(D → B). module_sum(add, zero, ∅, F) = zero",
		func(a *Argument, add *Arrow2[B, B, B], zero *Expr[B], F *Arrow[D, B]) {
			a.Show(
				"no index lies in ∅: the step is the identity, and the fold over ∅ is zero",
				Unfold(ModuleSumDef),
				Simp(Fwd(set_basic.NotInEmpty.Inst[D]())),
				By(cardinality.FiniteRecursion))
		}),
})}

// ModuleSumCongruence — a sum reads its family on the index set only:
// the two folds run one step function, so they are one fold.
var ModuleSumCongruence = moduleSumCongruenceThm{family.Add(registry.ProofEntry{
	Name: "ModuleSumCongruence",
	Key:  "prop_b00f87ee0df34e62",
	Build: family.Theorem(Statement{
		Binders: "∀add:(B → B → B). ∀zero:B. ∀s:set(D). ∀F G:(D → B).",
		Hypotheses: []string{
			"∀x:D. x ∈ s ⇒ F(x) = G(x)",
		},
		Conclusion: "module_sum(add, zero, s, F) = module_sum(add, zero, s, G)",
	},
		func(
			a *Argument,
			add *Arrow2[B, B, B],
			zero *Expr[B],
			s *Expr[Set[D]],
			F, G *Arrow[D, B],
			agree Fact,
		) {
			a.Do(Unfold(ModuleSumDef))
			steps := a.Have(
				"the two steps are one function",
				"(λx:D. λa:B. COND(x ∈ s, add(F(x), a), a)) = (λx:D. λa:B. COND(x ∈ s, add(G(x), a), a))",
				Derive(func(b *Argument) {
					b.Do(Funext())
					x := b.FixAs[D]()
					b.FixAs[B]()
					b.Cases(b.Term("x ∈ s"))
					b.When(
						"on s the families agree",
						func(c *Argument, inS Fact) {
							c.Show(
								"both steps add the same term",
								By(Normalized, agree.At(x), inS))
						})
					b.Otherwise(
						"off s both steps return the accumulator",
						func(c *Argument, offS Fact) {
							c.Show(
								"both steps are the identity",
								By(offS))
						})
				}))
			a.Show(
				"so the two folds over s from zero are one fold",
				steps.Rw(),
				Basic())
		}),
})}

// ---------------------------------------------------------------------------
// The fold of a commutative monoid on a set
// ---------------------------------------------------------------------------

// A module's sum is this fold at the monoid of its vectors under +
// (AddMonoidOn), and a ring's finite product at the ring's monoid under *
// (comm_ring.MulMonoidOn).

// ModuleSumInsertMonoid — the fold's insert law under a commutative
// monoid on c: one more index x combines its term F(x) with the fold
// over the indices before it. The step of an index set on which F lies
// in c keeps c, and left-commutes there since op associates and
// commutes on c; so the fold over insert(x, s) applies its step at the
// new index x last, which combines F(x), and over s that step agrees
// with the step of s index by index, so the two fold alike.
var ModuleSumInsertMonoid = moduleSumInsertMonoidThm{family.Add(registry.ProofEntry{
	Name: "ModuleSumInsertMonoid",
	Key:  "prop_cf08261e71e93380",
	Reading: "Only the monoid's laws on c are read — closure, associativity, commutativity and e " +
		"∈ c — so a ring's product folds by it: comm_monoid_on(R.carrier, R.mul, R.one) holds in " +
		"every commutative ring, the zero ring included. F is asked to lie in c at x and on s only; " +
		"off insert(x, s) it is not read. F(x) ∈ c is load-bearing: with op(u, v) = u, a commutative " +
		"monoid on c = {e}, F(y) = e and F(x) = a ≠ e, the two orders fold {x, y} to a and to e, " +
		"SetFoldDef's specification is unsatisfiable and module_sum is the ε's arbitrary value. " +
		"Inside c the guarded step is closed and left-commutative, all FiniteRecursionWithin reads.",
	Build: comm_monoid.CommMonoidOn.Law(Statement{
		Binders: "∀s:set(D). ∀x:D. ∀F:(D → A).",
		Hypotheses: []string{
			"finite(s)",
			"x ∉ s",
			"F(x) ∈ c",
			"∀y:D. y ∈ s ⇒ F(y) ∈ c",
		},
		Conclusion: "module_sum(op, e, insert(x, s), F) = op(F(x), module_sum(op, e, s, F))",
	},
		func(
			a *Argument,
			monoid comm_monoid.CommMonoidFact[on.C],
			s *Expr[Set[D]],
			x *Expr[D],
			_ *Arrow[D, A],
			hypotheses Fact,
		) {
			parts := a.Conjuncts(
				hypotheses,
				"s is finite",
				"x is not an index of s",
				"F(x) lies in c",
				"F lies in c on s")
			finite, notIn, fxIn, onS := parts[0], parts[1], parts[2], parts[3]
			identityIn := a.Have(
				"the folds start in c",
				"e ∈ c",
				By(comm_monoid.IdentityIn.Read(monoid)))
			onInsert := a.Have(
				"F lies in c on insert(x, s)",
				"∀y:D. y ∈ insert(x, s) ⇒ F(y) ∈ c",
				By(fxIn, onS, set_basic.ForallInInsert.At(a.TermAs[Set[D]]("λy:D. F(y) ∈ c"), x, s)))

			stepDef := a.Let("step", a.Term("λt:set(D). λy:D. λz:A. COND(y ∈ t, op(F(y), z), z)"))
			foldIsSetFold := a.Have(
				"a fold over t is the set fold of the step of t",
				"∀t:set(D). module_sum(op, e, t, F) = set_fold(step(t), t, e)",
				stepDef.Rw(),
				Unfold(ModuleSumDef))
			keeps := a.Have(
				"the step of an index set on which F lies in c keeps c",
				"∀t:set(D). (∀y:D. y ∈ t ⇒ F(y) ∈ c) ⇒ ∀y:D. ∀z:A. z ∈ c ⇒ step(t, y, z) ∈ c",
				Derive(func(b *Argument) {
					b.FixAs[Set[D]]("t")
					onT := b.Assume()
					y := b.FixAs[D]("y")
					z := b.FixAs[A]("z")
					zIn := b.Assume()
					b.Cases(b.Term("y ∈ t"))
					b.When(
						"at an index of t the step combines F(y), a member of c, with z",
						func(d *Argument, inT Fact) {
							u := d.MemberOf[on.C](d.TermAs[A]("F(y)"), d.Have(
								"F(y) lies in c",
								"F(y) ∈ c",
								By(onT.At(y), inT)))
							d.Show(
								"c is closed under op",
								stepDef.Rw(),
								By(inT, comm_monoid.OpIn.Read(monoid).At(u, d.MemberOf[on.C](z, zIn))))
						})
					b.Otherwise(
						"off t the step returns z",
						func(d *Argument, offT Fact) {
							d.Show(
								"which lies in c",
								stepDef.Rw(),
								By(offT, zIn))
						})
				}))
			leftComm := a.Have(
				"and left-commutes there",
				"∀t:set(D). "+
					"    (∀y:D. y ∈ t ⇒ F(y) ∈ c) ⇒ "+
					"    ∀y₁ y₂:D. ∀z:A. z ∈ c ⇒ step(t, y₁, step(t, y₂, z)) = step(t, y₂, step(t, y₁, z))",
				Derive(func(b *Argument) {
					b.FixAs[Set[D]]("t")
					onT := b.Assume()
					y1 := b.FixAs[D]("y₁")
					y2 := b.FixAs[D]("y₂")
					z := b.FixAs[A]("z")
					zIn := b.Assume()
					b.Cases(b.Term("y₁ ∈ t ∧ y₂ ∈ t"))
					b.When(
						"at two indices of t the steps combine F(y₁) and F(y₂) with z, in either order",
						func(d *Argument, both Fact) {
							u := d.MemberOf[on.C](d.TermAs[A]("F(y₁)"), d.Have(
								"F(y₁) lies in c",
								"F(y₁) ∈ c",
								By(onT.At(y1), both)))
							v := d.MemberOf[on.C](d.TermAs[A]("F(y₂)"), d.Have(
								"so does F(y₂)",
								"F(y₂) ∈ c",
								By(onT.At(y2), both)))
							d.Show(
								"F(y₁) and F(y₂) pass each other in front of z, op associating and commuting on c",
								stepDef.Rw(),
								By(both, comm_monoid.LeftCommOn.Read(monoid).At(u, v, d.MemberOf[on.C](z, zIn))))
						})
					b.Otherwise(
						"one of the two steps is the identity, and both sides apply the other",
						func(d *Argument, notBoth Fact) {
							d.Show(
								"both sides are the other step at z",
								stepDef.Rw(),
								By(notBoth))
						})
				}))

			ins := a.TermAs[Set[D]]("insert(x, s)")
			stepIns := a.TermAs[Fun2[D, A, A]]("step(insert(x, s))")
			stepS := a.TermAs[Fun2[D, A, A]]("step(s)")
			identity := a.TermAs[A]("e")
			carrier := a.TermAs[Set[A]]("c")
			agree := a.Have(
				"at an index of s both steps combine F(y)",
				"∀y:D. y ∈ s ⇒ step(insert(x, s), y) = step(s, y)",
				Derive(func(b *Argument) {
					y := b.FixAs[D]("y")
					inS := b.Assume()
					b.Show(
						"an index of s lies in insert(x, s)",
						stepDef.Rw(),
						By(inS, set_basic.InInsert.At(s, x, y)))
				}))
			foldsAgree := a.Have(
				"so the two steps fold alike over s",
				"set_fold(step(insert(x, s)), s, e) = set_fold(step(s), s, e)",
				By(
					cardinality.FoldOfAgreeingStepsWithin.At(s, stepIns, stepS, identity, carrier),
					finite,
					identityIn,
					agree,
					onInsert,
					onS,
					keeps.At(ins),
					keeps.At(s),
					leftComm.At(ins),
					leftComm.At(s)))
			a.Show(
				"the fold over insert(x, s) is F(x) combined with the fold over s",
				CalcEq(
					Leg(
						a.TermAs[A]("set_fold(step(insert(x, s)), insert(x, s), e)"),
						"a fold is the set fold of its step",
						By(foldIsSetFold.At(ins))),
					Leg(
						a.TermAs[A]("step(insert(x, s), x, set_fold(step(insert(x, s)), s, e))"),
						"x is a new index: the fold applies the step at x last",
						By(
							cardinality.FiniteRecursionWithin.At(stepIns, identity, carrier),
							finite,
							notIn,
							identityIn,
							onInsert,
							keeps.At(ins),
							leftComm.At(ins))),
					Leg(
						a.TermAs[A]("op(F(x), set_fold(step(insert(x, s)), s, e))"),
						"x lies in insert(x, s), so the step at x combines F(x)",
						stepDef.Rw(),
						By(set_basic.InInsert.At(s, x, x))),
					Leg(
						a.TermAs[A]("op(F(x), set_fold(step(s), s, e))"),
						"the two steps fold alike over s",
						By(Normalized, foldsAgree)),
					FinalLeg(
						"which is the fold over s",
						By(Normalized, foldIsSetFold.At(s))),
				))
		}),
})}

// ModuleSumDeleteMonoid — the fold's delete law under a commutative
// monoid on c: an index x of s splits its term off the fold. s is x laid
// back into delete(s, x), where x is a new index (InsertDelete, InDelete),
// so the fold over s combines F(x) with the fold over delete(s, x)
// (ModuleSumInsertMonoid).
var ModuleSumDeleteMonoid = moduleSumDeleteMonoidThm{family.Add(registry.ProofEntry{
	Name: "ModuleSumDeleteMonoid",
	Key:  "prop_8f8882b4f69c8b8f",
	Build: comm_monoid.CommMonoidOn.Law(Statement{
		Binders: "∀s:set(D). ∀x:D. ∀F:(D → A).",
		Hypotheses: []string{
			"finite(s)",
			"x ∈ s",
			"∀y:D. y ∈ s ⇒ F(y) ∈ c",
		},
		Conclusion: "module_sum(op, e, s, F) = op(F(x), module_sum(op, e, delete(s, x), F))",
	},
		func(
			a *Argument,
			monoid comm_monoid.CommMonoidFact[on.C],
			s *Expr[Set[D]],
			x *Expr[D],
			F *Arrow[D, A],
			hypotheses Fact,
		) {
			parts := a.Conjuncts(
				hypotheses,
				"s is finite",
				"x is an index of s",
				"F lies in c on s")
			finS, xIn, onS := parts[0], parts[1], parts[2]
			rest := a.TermAs[Set[D]]("delete(s, x)")
			onRest := a.Have(
				"F lies in c on delete(s, x), a part of s",
				"∀y:D. y ∈ delete(s, x) ⇒ F(y) ∈ c",
				a.ForEach(func(y *Expr[D]) Action {
					return By(onS.At(y), set_basic.InDelete.At(s, y, x))
				}))
			a.Show(
				"the fold over s is the fold over insert(x, delete(s, x))",
				CalcEq(
					Leg(
						a.TermAs[A]("module_sum(op, e, insert(x, delete(s, x)), F)"),
						"x laid back into delete(s, x) is s",
						By(Normalized, xIn, set_algebra.InsertDelete.At(s, x))),
					FinalLeg(
						"x is a new index of delete(s, x)",
						By(
							finS,
							finite_set.FiniteDeleteImp.At(s, x),
							set_basic.InDelete.At(s, x, x),
							onS.At(x),
							xIn,
							onRest,
							ModuleSumInsertMonoid.Read(monoid).At(rest, x, F))),
				))
		}),
})}

// ModuleSumInMonoid — a fold under a commutative monoid on c of a
// family valued in c on a finite index set lies in c: by induction on
// the index set, the empty fold is e, a member of c, and a new index
// combines its term with the fold over the indices before it, two
// members of c, which op keeps in c.
var ModuleSumInMonoid = moduleSumInMonoidThm{family.Add(registry.ProofEntry{
	Name: "ModuleSumInMonoid",
	Key:  "prop_685fd980bb62f026",
	Reading: "Finiteness is load-bearing: over an infinite index set " +
		"the fold is unspecified. Over ∅ the fold is e, which lies in c.",
	Build: comm_monoid.CommMonoidOn.Law(Statement{
		Binders: "∀s:set(D). ∀F:(D → A).",
		Hypotheses: []string{
			"finite(s)",
			"∀x:D. x ∈ s ⇒ F(x) ∈ c",
		},
		Conclusion: "module_sum(op, e, s, F) ∈ c",
	},
		func(
			a *Argument,
			monoid comm_monoid.CommMonoidFact[on.C],
			s *Expr[Set[D]],
			F *Arrow[D, A],
			hypotheses Fact,
		) {
			a.Show(
				"the induction carries membership to every finite index set on which F lies in c, s among them",
				ByInduction(finite_set.FiniteInductFreshOn, hypotheses,
					Case(
						"the empty fold is e, a member of c",
						By(comm_monoid.IdentityIn.Read(monoid), ModuleSumEmpty)),
					Case(
						"one more index combines a member of c with a member of c",
						Derive(func(b *Argument) {
							x := b.FixAs[D]()
							t := b.FixAs[Set[D]]()
							carried := b.Conjuncts(
								b.Assume(),
								"the fold over t lies in c",
								"x is a new index of t",
								"t is finite",
								"F(x) lies in c",
								"F lies in c on t")
							rest, notIn, finT, fxIn, onT := carried[0], carried[1], carried[2], carried[3], carried[4]
							peel := b.Have(
								"x is a new index: the fold over insert(x, t) combines F(x) with the fold over t",
								"module_sum(op, e, insert(x, t), F) = op(F(x), module_sum(op, e, t, F))",
								By(notIn, finT, fxIn, onT, ModuleSumInsertMonoid.Read(monoid).At(t, x, F)))
							b.Show(
								"op keeps two members of c in c",
								By(
									peel,
									comm_monoid.OpIn.Read(monoid).At(
										b.MemberOf[on.C](F.Apply(x), fxIn),
										b.MemberOf[on.C](b.TermAs[A]("module_sum(op, e, t, F)"), rest))))
						}))))
		}),
})}

// ModuleSumImageMonoid — under a commutative monoid on c, the fold over
// the image of a map g injective on the index set is the fold of the
// composite over the index set: by induction on the index set, the image
// of ∅ is ∅, and both empty folds are e; a new index x of t sends g(x)
// to a new point of the image of t, since a source of g(x) in t would be
// x itself by injectivity on insert(x, t), so the image of insert(x, t)
// is the image of t with g(x) added, and both folds over the enlarged
// sets peel the same term F(g(x)) off the claim carried to t.
var ModuleSumImageMonoid = moduleSumImageMonoidThm{family.Add(registry.ProofEntry{
	Name: "ModuleSumImageMonoid",
	Key:  "prop_810620a2d79cc3f8",
	Reading: "Injectivity on s is load-bearing: two indices with one " +
		"image would fold their term twice on the right and once on the left. " +
		"F is read at the images of s only, where it is asked to lie in c.",
	Build: comm_monoid.CommMonoidOn.Law(Statement{
		Binders: "∀s:set(D). ∀g:(D → E). ∀F:(E → A).",
		Hypotheses: []string{
			"finite(s)",
			"injective_on(s, g)",
			"∀x:D. x ∈ s ⇒ F(g(x)) ∈ c",
		},
		Conclusion: "module_sum(op, e, image(g, s), F) = module_sum(op, e, s, λx:D. F(g(x)))",
	},
		func(
			a *Argument,
			monoid comm_monoid.CommMonoidFact[on.C],
			s *Expr[Set[D]],
			g *Arrow[D, E],
			F *Arrow[E, A],
			finiteS, injective, imagesInC Fact,
		) {
			composite := a.TermAs[Fun[D, A]]("λx:D. F(g(x))")
			a.Show(
				"the induction carries the equation to every finite "+
					"index set on which F ∘ g lies in c, s among them",
				ByInduction(finite_set.FiniteInductFreshOn, finiteS, imagesInC, Generalizing(injective),
					Case(
						"the image of ∅ is ∅, and both empty folds are e",
						Derive(func(b *Argument) {
							emptyImage := b.Have(
								"g carries nothing out of ∅",
								"image(g, ∅) = ∅",
								By(set_image.ImageEqEmpty.At(g, b.TermAs[Set[D]]("∅⟨A:D⟩"))))
							b.Show(
								"both folds are over ∅",
								By(emptyImage, ModuleSumEmpty))
						})),
					Case(
						"one more index x sends g(x) to a new point of the image, and both folds peel off F(g(x))",
						Derive(func(b *Argument) {
							x := b.FixAs[D]()
							t := b.FixAs[Set[D]]()
							carried := b.Conjuncts(
								b.Assume(),
								"the equation over t, for g injective on t",
								"x is a new index of t",
								"t is finite",
								"F(g(x)) lies in c",
								"F(g(y)) lies in c at every index y of t")
							claimT, notIn, finT, fgxIn, onT := carried[0], carried[1], carried[2], carried[3], carried[4]
							injective := b.Assume() // g is injective on insert(x, t)
							gx := g.Apply(x)
							imageT := b.TermAs[Set[E]]("image(g, t)")
							injectiveT := b.Have(
								"g is injective on t, a part of insert(x, t)",
								"injective_on(t, g)",
								BySets(injective, functions.InjectiveOnSubset.At(g, t, b.TermAs[Set[D]]("insert(x, t)"))))
							fresh := b.Have(
								"g(x) is a new point of the image of t",
								"g(x) ∉ image(g, t)",
								Derive(func(c *Argument) {
									inImage := c.SupposeNot()
									y, source := c.ObtainAs[D](
										"then g(x) is g(y) for some y in t",
										"∃y:D. g(x) = g(y) ∧ y ∈ t",
										By(inImage, set_basic.InImage.At(g, t, gx)))
									same := c.Have(
										"x and y lie in insert(x, t), where g identifies only equal points",
										"x = y",
										By(
											source,
											c.Unfolded(injective, functions.InjectiveOnDef).At(x, y),
											set_basic.InInsert.At(t, x, x),
											set_basic.InInsert.At(t, x, y)))
									c.Show(
										"so x, being y, lies in t, and x is a new index of t",
										By(Normalized, same, source, notIn))
								}))
							onImage := b.Have(
								"F lies in c on the image of t",
								"∀z:E. z ∈ image(g, t) ⇒ F(z) ∈ c",
								By(onT, set_image.ForallInImage.At(g, t, b.TermAs[Set[E]]("λz:E. F(z) ∈ c"))))
							b.Show(
								"the fold over the image of insert(x, t) is the fold of the composite over insert(x, t)",
								CalcEq(
									Leg(
										b.TermAs[A]("module_sum(op, e, insert(g(x), image(g, t)), F)"),
										"the image of insert(x, t) is the image of t with g(x) added",
										By(Normalized, set_image.ImageClauses.At(g, x, t))),
									Leg(
										b.TermAs[A]("op(F(g(x)), module_sum(op, e, image(g, t), F))"),
										"g(x) is a new point of the image of t",
										By(
											finT,
											finite_set.FiniteImage.At(g, t),
											fresh,
											fgxIn,
											onImage,
											ModuleSumInsertMonoid.Read(monoid).At(imageT, gx, F))),
									Leg(
										b.TermAs[A]("op(F(g(x)), module_sum(op, e, t, λy:D. F(g(y))))"),
										"the claim carried to t",
										By(claimT, injectiveT)),
									FinalLeg(
										"x is a new index of t, and F(g(x)) the term it adds to the fold of the composite",
										By(finT, notIn, fgxIn, onT, ModuleSumInsertMonoid.Read(monoid).At(t, x, composite))),
								))
						}))))
		}),
})}

// ModuleSumReindex — a sum over the indices below n is unchanged when an
// injective self-map σ of those indices is applied to them first. An
// injective self-map of the indices below n is onto them, and summing G over
// the image of an injective σ is summing G ∘ σ.
var ModuleSumReindex = moduleSumReindexThm{family.Add(registry.ProofEntry{
	Name: "ModuleSumReindex",
	Key:  "prop_79333d54ad45778b",
	Build: comm_monoid.CommMonoidOn.Law(Statement{
		Binders: "∀n:num. ∀σ:(num → num). ∀G:(num → A).",
		Hypotheses: []string{
			"∀a:num. a < n ⇒ σ(a) < n",
			"injective_on({a:num | a < n}, σ)",
			"∀a:num. a < n ⇒ G(a) ∈ c",
		},
		Conclusion: "module_sum(op, e, {a:num | a < n}, λa:num. G(σ(a))) = " +
			"module_sum(op, e, {a:num | a < n}, G)",
	},
		func(
			arg *Argument,
			monoid comm_monoid.CommMonoidFact[on.C],
			n *Expr[Nat],
			σ *Arrow[Nat, Nat],
			G *Arrow[Nat, A],
			into, injective, inC Fact,
		) {
			below := arg.TermAs[Set[Nat]]("{a:num | a < n}")
			onto := arg.Have(
				"every index below n is σ of one, σ being injective on them",
				"∀j:num. j < n ⇒ ∃i:num. i < n ∧ σ(i) = j",
				By(into, injective, functions.InjectiveOnDef, num_segment.BelowStrictInjectiveOnto))
			image := arg.Have(
				"so σ maps the indices below n onto themselves",
				"image(σ, {a:num | a < n}) = {a:num | a < n}",
				BySets(onto, into))
			arg.Show(
				"the sum of G ∘ σ is the sum of G over the image of σ, which is all of them",
				CalcEq(
					Leg(
						arg.TermAs[A]("module_sum(op, e, image(σ, {a:num | a < n}), G)"),
						"σ is injective, so summing G over its image is summing G ∘ σ",
						By(
							into,
							inC,
							injective,
							ModuleSumImageMonoid.Read(monoid).At(below, σ, G),
							num_segment.FiniteBelowStrict.At(n))),
					FinalLeg(
						"the image is all the indices below n",
						By(image))))
		}),
})}

// ModuleSumMonoidHomomorphism — a map h that keeps the identity and
// carries the operation of a commutative monoid on c to a second
// operation carries a fold of a family valued in c to the fold of its
// images under the second operation, from the second identity. The
// images of c are a commutative monoid under op₂ with identity e₂, as
// the homomorphic image of one (comm_monoid.ImageCommMonoidOn). Then
// induction on the finite index set: both empty folds are e₂ = h(e); a
// new index x peels F(x) off the fold over c, h splits op(F(x), rest),
// the rest lying in c, and h(F(x)) peels off the fold of the images
// under the monoid on the images.
var ModuleSumMonoidHomomorphism = moduleSumMonoidHomomorphismThm{family.Add(registry.ProofEntry{
	Name: "ModuleSumMonoidHomomorphism",
	Key:  "prop_139f745afe1ec38e",
	Reading: "Nothing is asked of op₂ beyond what h carries: it is read at " +
		"images of c only. h(e) = e₂ is load-bearing at s = ∅, and h is asked to " +
		"carry op to op₂ on c only. A ring map's multiplicative part is such an " +
		"h, at the monoid comm_monoid_on(R.carrier, R.mul, R.one) of its source.",
	Build: comm_monoid.CommMonoidOn.Law(Statement{
		Binders: "∀op₂:(B → B → B). ∀e₂:B. ∀h:(A → B). ∀s:set(D). ∀F:(D → A).",
		Hypotheses: []string{
			"h(e) = e₂",
			"∀u v:A. u ∈ c ∧ v ∈ c ⇒ h(op(u, v)) = op₂(h(u), h(v))",
			"finite(s)",
			"∀x:D. x ∈ s ⇒ F(x) ∈ c",
		},
		Conclusion: "h(module_sum(op, e, s, F)) = module_sum(op₂, e₂, s, λx:D. h(F(x)))",
	},
		func(
			a *Argument,
			c *Expr[Set[A]],
			op *Arrow2[A, A, A],
			e *Expr[A],
			monoid comm_monoid.CommMonoidFact[on.C],
			op2 *Arrow2[B, B, B],
			e2 *Expr[B],
			h *Arrow[A, B],
			s *Expr[Set[D]],
			F *Arrow[D, A],
			hypotheses Fact,
		) {
			parts := a.Conjuncts(
				hypotheses,
				"h keeps the identity",
				"h carries op to op₂ on c",
				"s is finite",
				"F lies in c on s")
			keepsE, keepsOp, finS, onS := parts[0], parts[1], parts[2], parts[3]
			images := a.TermAs[Set[B]]("image(h, c)")
			imageMonoid := a.Have(
				"the images of c are a commutative monoid under op₂, with identity e₂",
				"comm_monoid_on(image(h, c), op₂, e₂)",
				By(comm_monoid.ImageCommMonoidOn.Read(monoid).At(op2, e2, images, h), keepsOp, keepsE))
			imagesOfF := a.TermAs[Fun[D, B]]("λx:D. h(F(x))")
			a.Show(
				"the induction carries the equation to every finite index set on which F lies in c, s among them",
				ByInduction(finite_set.FiniteInductFreshOn, finS, onS,
					Case(
						"both empty folds are e₂ = h(e)",
						By(Normalized, keepsE, ModuleSumEmpty.At(op, e, F), ModuleSumEmpty.At(op2, e2, imagesOfF))),
					Case(
						"one more index x: F(x) peels off the fold over c, h "+
							"splits op, and h(F(x)) peels off the fold of the images",
						Derive(func(b *Argument) {
							x := b.FixAs[D]()
							t := b.FixAs[Set[D]]()
							carried := b.Conjuncts(
								b.Assume(),
								"h carries the fold over t to the fold of the images",
								"x is a new index of t",
								"t is finite",
								"F(x) lies in c",
								"F lies in c on t")
							rest, notIn, finT, fxIn, onT := carried[0], carried[1], carried[2], carried[3], carried[4]
							fx, foldT := F.Apply(x), b.TermAs[A]("module_sum(op, e, t, F)")
							foldIn := b.Have(
								"the fold over t lies in c",
								"module_sum(op, e, t, F) ∈ c",
								By(finT, onT, ModuleSumInMonoid.Read(monoid).At(t, F)))
							imagesOnT := b.Have(
								"h(F(y)) is an image at every index y of t",
								"∀y:D. y ∈ t ⇒ h(F(y)) ∈ image(h, c)",
								b.ForEach(func(y *Expr[D]) Action {
									return By(onT.At(y), set_image.FunInImage.At(h, c, F.Apply(y)))
								}))
							b.Show(
								"h of the fold over insert(x, t) is the fold of the images over insert(x, t)",
								CalcEq(
									Leg(
										b.TermAs[B]("h(op(F(x), module_sum(op, e, t, F)))"),
										"x is a new index of t: F(x) peels off the fold over c",
										By(finT, notIn, fxIn, onT, ModuleSumInsertMonoid.Read(monoid).At(t, x, F))),
									Leg(
										b.TermAs[B]("op₂(h(F(x)), h(module_sum(op, e, t, F)))"),
										"F(x) and the fold over t lie in c, where h carries op to op₂",
										By(fxIn, foldIn, keepsOp.At(fx, foldT))),
									Leg(
										b.TermAs[B]("op₂(h(F(x)), module_sum(op₂, e₂, t, λy:D. h(F(y))))"),
										"the claim carried to t",
										By(rest)),
									FinalLeg(
										"x is a new index of t: h(F(x)) peels off the fold of the images, under the monoid on the images",
										By(
											finT,
											notIn,
											fxIn,
											set_image.FunInImage.At(h, c, fx),
											imagesOnT,
											ModuleSumInsertMonoid.Read(imageMonoid).At(t, x, imagesOfF))),
								))
						}))))
		}),
})}

// ModuleSumConstantMonoid — under a commutative monoid on c, a fold of
// one member a of c over a finite index set is a combined with itself as
// many times as the set has members: by induction on the index set, the
// empty fold is e, which is a ^ 0, and a new index combines one more a
// with the fold before it while the count grows by one.
var ModuleSumConstantMonoid = moduleSumConstantMonoidThm{family.Add(registry.ProofEntry{
	Name: "ModuleSumConstantMonoid",
	Key:  "prop_a9bc63ef1e3f4a8b",
	Build: comm_monoid.CommMonoidOn.Law(Statement{
		Binders: "∀s:set(D). ∀a:A.",
		Hypotheses: []string{
			"finite(s)",
			"a ∈ c",
		},
		Conclusion: "module_sum(op, e, s, λx:D. a) = a ^ card(s)",
	},
		func(
			arg *Argument,
			monoid comm_monoid.CommMonoidFact[on.C],
			s *Expr[Set[D]],
			a *Expr[A],
			hypotheses Fact,
		) {
			parts := arg.Conjuncts(
				hypotheses,
				"s is finite",
				"a lies in c")
			finS, aIn := parts[0], parts[1]
			constant := arg.TermAs[Fun[D, A]]("λx:D. a")
			arg.Show(
				"the induction carries the count to every finite index set, s among them",
				ByInduction(finite_set.FiniteInductFresh, finS,
					Case(
						"the empty fold is e, which is a ^ 0, ∅ having no members",
						Simp(Fwd(ModuleSumEmpty), Fwd(cardinality.CardClauses), Fwd(comm_monoid.MonoidPowDef)),
						Basic()),
					Case(
						"a new index combines one more a with the fold, and the count grows by one",
						Derive(func(b *Argument) {
							x := b.FixAs[D]("x")
							t := b.FixAs[Set[D]]("t")
							carried := b.Conjuncts(
								b.Assume(),
								"the fold over t counts t",
								"x is a new index of t",
								"t is finite")
							rest, notIn, finT := carried[0], carried[1], carried[2]
							onT := b.Have(
								"a lies in c at every index of t",
								"∀y:D. y ∈ t ⇒ a ∈ c",
								b.ForEach(func(_ *Expr[D]) Action { return By(aIn) }))
							b.Show(
								"the fold over insert(x, t) is a combined with itself card(insert(x, t)) times",
								CalcEq(
									Leg(
										b.TermAs[A]("op(a, module_sum(op, e, t, λx:D. a))"),
										"x is a new index of t, where the fold combines one more a",
										By(finT, notIn, aIn, onT, ModuleSumInsertMonoid.Read(monoid).At(t, x, constant))),
									Leg(
										b.TermAs[A]("op(a, a ^ card(t))"),
										"the claim carried to t",
										By(Normalized, rest)),
									Leg(
										b.TermAs[A]("a ^ suc(card(t))"),
										"one more factor of a is the next power",
										Simp(Fwd(comm_monoid.MonoidPowDef)),
										Basic()),
									FinalLeg(
										"and insert(x, t) has one member more than t",
										By(Normalized, finT, notIn, cardinality.InsertCountsOneMore.At(t, x))),
								))
						}))))
		}),
})}

// ModuleSumIdentityMonoid — under a commutative monoid on c, a fold of a
// family that is e at every index of a finite set is e: the family is
// the constant e on the index set, the fold of a constant is its power to
// the count (ModuleSumConstantMonoid), and every power of e is e.
var ModuleSumIdentityMonoid = moduleSumIdentityMonoidThm{family.Add(registry.ProofEntry{
	Name: "ModuleSumIdentityMonoid",
	Key:  "prop_ca6515f17b768e53",
	Build: comm_monoid.CommMonoidOn.Law(Statement{
		Binders: "∀s:set(D). ∀F:(D → A).",
		Hypotheses: []string{
			"finite(s)",
			"∀x:D. x ∈ s ⇒ F(x) = e",
		},
		Conclusion: "module_sum(op, e, s, F) = e",
	},
		func(
			a *Argument,
			monoid comm_monoid.CommMonoidFact[on.C],
			s *Expr[Set[D]],
			F *Arrow[D, A],
			hypotheses Fact,
		) {
			parts := a.Conjuncts(
				hypotheses,
				"s is finite",
				"F is e on s")
			finS, identityOnS := parts[0], parts[1]
			op, identity := a.TermAs[Op[A]]("op"), a.TermAs[A]("e")
			identityIn := a.MemberOf[on.C](identity, comm_monoid.IdentityIn.Read(monoid))
			a.Show(
				"the fold of F is the fold of the constant e, card(s) copies of e, which combine to e",
				CalcEq(
					Leg(
						a.TermAs[A]("module_sum(op, e, s, λx:D. e)"),
						"F is e at every index of s",
						By(identityOnS, ModuleSumCongruence.At(op, identity, s, F, a.TermAs[Fun[D, A]]("λx:D. e")))),
					Leg(
						a.TermAs[A]("e ^ card(s)"),
						"a fold of the constant e counts the index set",
						By(finS, ModuleSumConstantMonoid.Read(monoid).At(s, identityIn))),
					FinalLeg(
						"and every power of e is e",
						By(comm_monoid.IdentityPowOn.Read(monoid).At(a.TermAs[Nat]("card(s)")))),
				))
		}),
})}

// ModuleSumAddMonoid — under a commutative monoid on c, the fold of the
// termwise combination of two families valued in c combines their folds:
// by induction on the index set, both sides are e over ∅; a new index x
// puts op(F(x), G(x)) in front of the fold over the indices before it,
// which the claim carried there splits, and the four members of c regroup
// into F(x) before the fold of F and G(x) before the fold of G.
var ModuleSumAddMonoid = moduleSumAddMonoidThm{family.Add(registry.ProofEntry{
	Name: "ModuleSumAddMonoid",
	Key:  "prop_41ac3003e2d81720",
	Build: comm_monoid.CommMonoidOn.Law(Statement{
		Binders: "∀s:set(D). ∀F G:(D → A).",
		Hypotheses: []string{
			"finite(s)",
			"∀x:D. x ∈ s ⇒ F(x) ∈ c ∧ G(x) ∈ c",
		},
		Conclusion: "module_sum(op, e, s, λx:D. op(F(x), G(x))) = " +
			"op(module_sum(op, e, s, F), module_sum(op, e, s, G))",
	},
		func(
			a *Argument,
			monoid comm_monoid.CommMonoidFact[on.C],
			s *Expr[Set[D]],
			F, G *Arrow[D, A],
			hypotheses Fact,
		) {
			identity := a.MemberOf[on.C](a.TermAs[A]("e"), comm_monoid.IdentityIn.Read(monoid))
			termwise := a.TermAs[Fun[D, A]]("λx:D. op(F(x), G(x))")
			a.Show(
				"the induction carries the equation to every finite "+
					"index set on which F and G lie in c, s among them",
				ByInduction(finite_set.FiniteInductFreshOn, hypotheses,
					Case(
						"both empty folds are e, and e combined with e is e",
						By(ModuleSumEmpty, comm_monoid.LeftIdentityOn.Read(monoid).At(identity))),
					Case(
						"one more index x puts op(F(x), G(x)) in front, and the four members of c regroup",
						Derive(func(b *Argument) {
							x := b.FixAs[D]()
							t := b.FixAs[Set[D]]()
							carried := b.Conjuncts(
								b.Assume(),
								"the termwise fold over t splits",
								"x is a new index of t",
								"t is finite",
								"F(x) lies in c",
								"so does G(x)",
								"F and G lie in c on t")
							rest, notIn, finT, fxIn, gxIn, onT :=
								carried[0], carried[1], carried[2], carried[3], carried[4], carried[5]
							onTF := b.Have(
								"F lies in c on t",
								"∀y:D. y ∈ t ⇒ F(y) ∈ c",
								b.ForEach(func(y *Expr[D]) Action { return By(onT.At(y)) }))
							onTG := b.Have(
								"so does G",
								"∀y:D. y ∈ t ⇒ G(y) ∈ c",
								b.ForEach(func(y *Expr[D]) Action { return By(onT.At(y)) }))
							onTTermwise := b.Have(
								"and so does the termwise combination, c being closed under op",
								"∀y:D. y ∈ t ⇒ op(F(y), G(y)) ∈ c",
								b.ForEach(func(y *Expr[D]) Action {
									return By(onT.At(y), comm_monoid.OpIn.Read(monoid))
								}))
							fx := b.MemberOf[on.C](F.Apply(x), fxIn)
							gx := b.MemberOf[on.C](G.Apply(x), gxIn)
							foldF := b.MemberOf[on.C](b.TermAs[A]("module_sum(op, e, t, F)"),
								b.Have(
									"the fold of F over t lies in c",
									"module_sum(op, e, t, F) ∈ c",
									By(finT, onTF, ModuleSumInMonoid.Read(monoid).At(t, F))))
							foldG := b.MemberOf[on.C](b.TermAs[A]("module_sum(op, e, t, G)"),
								b.Have(
									"so does the fold of G",
									"module_sum(op, e, t, G) ∈ c",
									By(finT, onTG, ModuleSumInMonoid.Read(monoid).At(t, G))))
							// c is closed under op: the combinations the regrouping passes through are members.
							fgx := comm_monoid.OpIn.Read(monoid).At(fx, gx)
							folds := comm_monoid.OpIn.Read(monoid).At(foldF, foldG)
							gxFoldG := comm_monoid.OpIn.Read(monoid).At(gx, foldG)
							b.Show(
								"the termwise fold over insert(x, t) combines the folds of F and of G over insert(x, t)",
								CalcEq(
									Leg(
										b.TermAs[A]("op(op(F(x), G(x)), module_sum(op, e, t, λy:D. op(F(y), G(y))))"),
										"x is a new index of t, and op(F(x), G(x)) the term it adds",
										By(finT, notIn, fgx, onTTermwise, ModuleSumInsertMonoid.Read(monoid).At(t, x, termwise))),
									Leg(
										b.TermAs[A]("op(op(F(x), G(x)), op(module_sum(op, e, t, F), module_sum(op, e, t, G)))"),
										"the claim carried to t",
										By(rest)),
									Leg(
										b.TermAs[A]("op(op(F(x), module_sum(op, e, t, F)), op(G(x), module_sum(op, e, t, G)))"),
										"G(x) passes the fold of F, op associating and commuting on c",
										By(
											comm_monoid.AssocOn.Read(monoid).At(fx, gx, folds),
											comm_monoid.LeftCommOn.Read(monoid).At(gx, foldF, foldG),
											comm_monoid.AssocOn.Read(monoid).At(fx, foldF, gxFoldG))),
									FinalLeg(
										"x is a new index of t for F and for G",
										By(
											finT,
											notIn,
											fxIn,
											gxIn,
											onTF,
											onTG,
											ModuleSumInsertMonoid.Read(monoid).At(t, x, F),
											ModuleSumInsertMonoid.Read(monoid).At(t, x, G))),
								))
						}))))
		}),
})}

// ModuleSumIteratedOp — under a commutative monoid on the whole type, the
// fold from the monoid's identity is the mechanism's iterated operation:
// by induction on the index set, both empty folds are the identity, which
// is the operation's neutral element, and a new index combines its term
// with the fold before it on both sides.
var ModuleSumIteratedOp = moduleSumIteratedOpThm{family.Add(registry.ProofEntry{
	Name: "ModuleSumIteratedOp",
	Key:  "prop_a5d173f84aee97f2",
	Build: comm_monoid.CommMonoid.Law(Statement{
		Binders:    "∀s:set(D). ∀F:(D → A).",
		Hypotheses: []string{"finite(s)"},
		Conclusion: "module_sum(op, e, s, F) = iterated_op(op, s, F)",
	},
		func(a *Argument, monoid Fact, s *Expr[Set[D]], F *Arrow[D, A], finS Fact) {
			op, e := a.TermAs[Op[A]]("op"), a.TermAs[A]("e")
			onUniverse := a.Have(
				"the monoid is the monoid on its whole carrier",
				"comm_monoid_on(𝕌, op, e)",
				By(comm_monoid.CommMonoidOnUniverse.At(op, e), monoid))
			folding := comm_monoid.Monoidal.Read(monoid)
			a.Show(
				"the two folds agree by induction on their index set",
				ByInduction(finite_set.FiniteInductFresh, finS,
					Case(
						"both empty folds are the identity",
						By(ModuleSumEmpty.At(op, e, F), monoidal.Clauses.Read(folding), comm_monoid.Neutral.Read(monoid))),
					Case(
						"a fresh index contributes the same new term",
						Derive(func(b *Argument) {
							x := b.FixAs[D]("x")
							t := b.FixAs[Set[D]]("t")
							induction := b.Assume()
							b.Show(
								"the insertion clauses agree by the induction hypothesis",
								By(
									induction,
									ModuleSumInsertMonoid.Read(onUniverse).At(t, x, F),
									monoidal.OneTurn.Read(folding).At(t, x, F),
									set_basic.InUniv))
						}))))
		}),
})}

// ---------------------------------------------------------------------------
// Sums in a module
// ---------------------------------------------------------------------------

// ModuleSumInsert — one more index adds its term to the sum:
// ModuleSumInsertMonoid at the monoid of the vectors under + (AddMonoidOn).
var ModuleSumInsert = moduleSumInsertThm{family.Add(registry.ProofEntry{
	Name: "ModuleSumInsert",
	Key:  "prop_201786d9ea1e6bce",
	Build: ModuleOn.Law(Statement{
		Binders: "∀s:set(D). ∀x:D. ∀F:(D → B).",
		Hypotheses: []string{
			"finite(s)",
			"x ∉ s",
			"F(x) ∈ M.carrier",
			"∀y:D. y ∈ s ⇒ F(y) ∈ M.carrier",
		},
		Conclusion: "module_sum(M.add, M.zero, insert(x, s), F) = F(x) + module_sum(M.add, M.zero, s, F)",
	},
		func(
			a *Argument,
			module ModuleFact[on.R, on.M],
			s *Expr[Set[D]],
			x *Expr[D],
			F *Arrow[D, B],
			hypotheses Fact,
		) {
			a.Show(
				"the vectors are a commutative monoid under +, where "+
					"one more index combines its term with the fold before it",
				By(hypotheses, ModuleSumInsertMonoid.Read(AddMonoidOn.Read(module)).At(s, x, F)))
		}),
})}

// ModuleSumDelete — an index x of s splits off the sum: s is x laid back
// into delete(s, x), where x is a new index (InsertDelete, InDelete), so
// the sum over s is F(x) plus the sum over delete(s, x) (ModuleSumInsert).
var ModuleSumDelete = moduleSumDeleteThm{family.Add(registry.ProofEntry{
	Name: "ModuleSumDelete",
	Key:  "prop_ace5422faa564523",
	Build: ModuleOn.Law(Statement{
		Binders: "∀s:set(D). ∀x:D. ∀F:(D → B).",
		Hypotheses: []string{
			"finite(s)",
			"x ∈ s",
			"∀y:D. y ∈ s ⇒ F(y) ∈ M.carrier",
		},
		Conclusion: "module_sum(M.add, M.zero, s, F) = F(x) + module_sum(M.add, M.zero, delete(s, x), F)",
	},
		func(
			a *Argument,
			module ModuleFact[on.R, on.M],
			s *Expr[Set[D]],
			x *Expr[D],
			F *Arrow[D, B],
			hypotheses Fact,
		) {
			parts := a.Conjuncts(
				hypotheses,
				"s is finite",
				"x is an index of s",
				"F lies in M on s")
			finS, xIn, onS := parts[0], parts[1], parts[2]
			rest := a.TermAs[Set[D]]("delete(s, x)")
			onRest := a.Have(
				"F lies in M on delete(s, x), a part of s",
				"∀y:D. y ∈ delete(s, x) ⇒ F(y) ∈ M.carrier",
				a.ForEach(func(y *Expr[D]) Action {
					return By(onS.At(y), set_basic.InDelete.At(s, y, x))
				}))
			a.Show(
				"the sum over s is the sum over insert(x, delete(s, x))",
				CalcEq(
					Leg(
						a.TermAs[B]("module_sum(M.add, M.zero, insert(x, delete(s, x)), F)"),
						"x laid back into delete(s, x) is s",
						By(Normalized, xIn, set_algebra.InsertDelete.At(s, x))),
					FinalLeg(
						"x is a new index of delete(s, x)",
						By(
							finS,
							finite_set.FiniteDeleteImp.At(s, x),
							set_basic.InDelete.At(s, x, x),
							onS.At(x),
							xIn,
							onRest,
							ModuleSumInsert.Read(module).At(rest, x, F))),
				))
		}),
})}

// ModuleSumIn — a sum of vectors is a vector: ModuleSumInMonoid at the
// monoid of the vectors under + (AddMonoidOn).
var ModuleSumIn = moduleSumInThm{family.Add(registry.ProofEntry{
	Name: "ModuleSumIn",
	Key:  "prop_de6c6d92bf4f1dfb",
	Build: ModuleOn.Law(Statement{
		Binders: "∀s:set(D). ∀F:(D → B).",
		Hypotheses: []string{
			"finite(s)",
			"∀x:D. x ∈ s ⇒ F(x) ∈ M.carrier",
		},
		Conclusion: "module_sum(M.add, M.zero, s, F) ∈ M.carrier",
	},
		func(a *Argument, module ModuleFact[on.R, on.M], s *Expr[Set[D]], F *Arrow[D, B], hypotheses Fact) {
			a.Show(
				"the vectors are a commutative monoid under +, and "+
					"a fold of its members over a finite set is a member",
				By(hypotheses, ModuleSumInMonoid.Read(AddMonoidOn.Read(module)).At(s, F)))
		}),
})}

// ModuleSumBelowClauses — the sum over the naturals below a bound, as
// the bound grows by one: below 0 there is nothing, and raising the
// bound from k to suc k adds the term at k, on the right as in the
// whole-type sums' clauses. The range below suc k is the range below k
// with the new index k laid in (BelowStrictClauses), where
// ModuleSumInsert adds F(k) on the left; the two vectors commute.
var ModuleSumBelowClauses = moduleSumBelowClausesThm{family.Add(registry.ProofEntry{
	Name: "ModuleSumBelowClauses",
	Key:  "prop_f949d726fdddeaff",
	Reading: "The terms are asked to lie in M only below suc(k): off the range the family " +
		"is not read. The clause at 0 needs no module law — the sum over ∅ is the fold's start.",
	Build: ModuleOn.Law("∀F:(num → B). "+
		"    module_sum(M.add, M.zero, {i:num | i < 0}, F) = M.zero ∧ "+
		"    (∀k:num. "+
		"        (∀i:num. i < suc(k) ⇒ F(i) ∈ M.carrier) ⇒ "+
		"        module_sum(M.add, M.zero, {i:num | i < suc(k)}, F) = "+
		"        module_sum(M.add, M.zero, {i:num | i < k}, F) + F(k))",
		func(a *Argument, module ModuleFact[on.R, on.M], F *Arrow[Nat, B]) {
			a.Do(SplitConj(
				Case(
					"below 0: the range is ∅, and the empty sum is M.zero",
					Derive(func(b *Argument) {
						noneBelow := b.Have(
							"no natural stands below 0",
							"{i:num | i < 0} = ∅",
							Cite(num_segment.BelowStrictClauses))
						b.Show(
							"and the sum over ∅ is the fold's start",
							noneBelow.Rw(),
							Cite(ModuleSumEmpty, b.TermAs[Op[B]]("M.add"), b.TermAs[B]("M.zero"), F))
					})),
				Case(
					"below suc k: one new index, k, is laid into the finite range below k",
					Derive(func(b *Argument) {
						k := b.FixAs[Nat]("k")
						terms := b.Assume()
						below := b.TermAs[Set[Nat]]("{i:num | i < k}")
						oneMore := b.Have(
							"the range below suc k is the range below k with k laid in",
							"{i:num | i < suc(k)} = insert(k, {i:num | i < k})",
							Cite(num_segment.BelowStrictClauses))
						fresh := b.Have(
							"and k is not among them, nothing being below itself",
							"k ∉ {i:num | i < k}",
							BySets(nat_order.LessThanIrrefl.At(k)))
						top := b.MemberOf[on.M](F.Apply(k), b.Have(
							"F(k) lies in M",
							"F(k) ∈ M.carrier",
							ByArith(terms.At(k))))
						lower := b.Have(
							"and so do the terms below k",
							"∀i:num. i ∈ {i:num | i < k} ⇒ F(i) ∈ M.carrier",
							b.ForEach(func(i *Expr[Nat]) Action { return ByArith(terms.At(i)) }))
						finite := num_segment.FiniteBelowStrict.At(k)
						sum := b.MemberOf[on.M](b.TermAs[B]("module_sum(M.add, M.zero, {i:num | i < k}, F)"),
							b.Have(
								"so the sum below k lies in M",
								"module_sum(M.add, M.zero, {i:num | i < k}, F) ∈ M.carrier",
								By(finite, lower, ModuleSumIn.Read(module).At(below, F))))
						b.Show(
							"the sum below suc k is F(k) plus the sum below k",
							CalcEq(
								Leg(
									b.TermAs[B]("F(k) + module_sum(M.add, M.zero, {i:num | i < k}, F)"),
									"k is a new index of the range below k",
									By(oneMore, finite, fresh, top, lower, ModuleSumInsert.Read(module).At(below, k, F))),
								FinalLeg(
									"and the two vectors commute",
									By(AddComm.Read(module).At(top, sum))),
							))
					})),
			))
		}),
})}

// GeometricSum — in a commutative ring, w − 1 times the sum of w⁰, …, wⁿ⁻¹
// is wⁿ − 1. By induction on n: the sum below suc(n) adds wⁿ to the sum
// below n, and (w − 1)·wⁿ = wⁿ⁺¹ − wⁿ telescopes.
var GeometricSum = geometricSumThm{family.Add(registry.ProofEntry{
	Name: "GeometricSum",
	Key:  "prop_89fe7df16a1f0eb6",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀w:A. ∀n:num.",
		Hypotheses: []string{
			"w ∈ R.carrier",
		},
		Conclusion: "(w - R.one) * " +
			"module_sum(R.add, R.zero, {a:num | a < n}, λa:num. monoid_pow(R.mul, R.one, w, a)) = " +
			"monoid_pow(R.mul, R.one, w, n) - R.one",
	},
		func(arg *Argument, ring comm_ring.CommRingFact[on.R], w *Member[A, on.R], n *Expr[Nat]) {
			powersIn := comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(ring))
			regular := RegularModuleOn.Read(ring)
			arg.Induct(n)
			arg.Base(
				"the empty sum is zero and w⁰ is one",
				Simp(Fwd(num_segment.BelowStrictClauses), Fwd(ModuleSumEmpty), Fwd(comm_monoid.MonoidPowDef)),
				ByArith(ring, w))
			arg.Step(
				"the sum below suc(n) adds wⁿ, and (w − 1)·wⁿ is wⁿ⁺¹ − wⁿ",
				func(b *Argument, ih Fact) {
					last := b.Have(
						"the sum below suc(n) is the sum below n plus wⁿ",
						"module_sum(R.add, R.zero, {a:num | a < suc(n)}, λa:num. monoid_pow(R.mul, R.one, w, a)) = "+
							"module_sum(R.add, R.zero, {a:num | a < n}, λa:num. monoid_pow(R.mul, R.one, w, a)) + "+
							"monoid_pow(R.mul, R.one, w, n)",
						By(ModuleSumBelowClauses.Read(regular), powersIn, w))
					partialIn := b.Have(
						"the sum below n lies in the ring",
						"module_sum(R.add, R.zero, {a:num | a < n}, λa:num. monoid_pow(R.mul, R.one, w, a)) ∈ R.carrier",
						By(
							ModuleSumIn.Read(regular).At(
								b.TermAs[Set[Nat]]("{a:num | a < n}"),
								b.TermAs[Fun[Nat, A]]("λa:num. monoid_pow(R.mul, R.one, w, a)")),
							num_segment.FiniteBelowStrict,
							powersIn,
							w))
					b.Show(
						"(w − 1)·(Σ_{a<n} wᵃ + wⁿ) is wⁿ − 1 + wⁿ⁺¹ − wⁿ",
						Simp(Fwd(comm_monoid.MonoidPowDef)),
						last.Rw(),
						ByArith(ring, ih, w, partialIn))
				})
		}),
})}

// ModuleSumImage — a sum over the image of a map injective on the index
// set is the sum of the composite: ModuleSumImageMonoid at the monoid of
// the vectors under + (AddMonoidOn).
var ModuleSumImage = moduleSumImageThm{family.Add(registry.ProofEntry{
	Name: "ModuleSumImage",
	Key:  "prop_5043019c5bf4d1ba",
	Build: ModuleOn.Law(Statement{
		Binders: "∀s:set(D). ∀g:(D → E). ∀F:(E → B).",
		Hypotheses: []string{
			"finite(s)",
			"injective_on(s, g)",
			"∀x:D. x ∈ s ⇒ F(g(x)) ∈ M.carrier",
		},
		Conclusion: "module_sum(M.add, M.zero, image(g, s), F) = " +
			"module_sum(M.add, M.zero, s, λx:D. F(g(x)))",
	},
		func(
			a *Argument,
			module ModuleFact[on.R, on.M],
			s *Expr[Set[D]],
			g *Arrow[D, E],
			F *Arrow[E, B],
			hypotheses Fact,
		) {
			a.Show(
				"the vectors are a commutative monoid under +, where a "+
					"fold over an injective image is the fold of the composite",
				By(hypotheses, ModuleSumImageMonoid.Read(AddMonoidOn.Read(module)).At(s, g, F)))
		}),
})}

// ModuleSumConstant — a sum of one vector over a finite index set is that
// vector scaled by the size of the set, the size being the ring's one
// added to itself: v is R.one • v at every index, the sum of these scales
// v by the sum of the ones (ModuleSumSmulRight), and the sum of the ones
// is a constant fold in the scalars' additive monoid.
var ModuleSumConstant = moduleSumConstantThm{family.Add(registry.ProofEntry{
	Name: "ModuleSumConstant",
	Key:  "prop_c9ecf9166e94fa07",
	Build: ModuleOn.Law(Statement{
		Binders: "∀s:set(D). ∀v:B.",
		Hypotheses: []string{
			"finite(s)",
			"v ∈ M.carrier",
		},
		Conclusion: "module_sum(M.add, M.zero, s, λi:D. v) = monoid_pow(R.add, R.zero, R.one, card(s)) • v",
	},
		func(a *Argument, module ModuleFact[on.R, on.M], s *Expr[Set[D]], v *Expr[B], hypotheses Fact) {
			parts := a.Conjuncts(
				hypotheses,
				"s is finite",
				"v is a vector")
			finS, vIn := parts[0], parts[1]
			vM := a.MemberOf[on.M](v, vIn)
			ring := RingOn.Read(module)
			oneIn := comm_ring.OneIn.Read(ring)
			a.Show(
				"write v as R.one • v, factor it out, and count the scalar ones",
				CalcEq(
					Leg(
						a.TermAs[B]("module_sum(M.add, M.zero, s, λi:D. R.one • v)"),
						"the ring's one scales v to v",
						By(SmulOne.Read(module).At(vM), ModuleSumCongruence)),
					Leg(
						a.TermAs[B]("module_sum(R.add, R.zero, s, λi:D. R.one) • v"),
						"a sum of scalars scales v to the sum of its multiples",
						By(
							finS,
							vIn,
							oneIn,
							ModuleSumSmulRight.Read(module).AsFact().At(s, a.TermAs[Fun[D, A]]("λi:D. R.one"), v))),
					FinalLeg(
						"the sum of the ones over s is one taken card(s) times",
						By(
							finS,
							oneIn,
							ModuleSumConstantMonoid.Read(comm_ring.AddMonoidOn.Read(ring)).AsFact().At(
								s, a.TermAs[A]("R.one"))))))
		}),
})}

// PowNatSum — a member x of a commutative monoid raised to a finite sum of
// naturals is the product of its powers at the summands: k ↦ x ^ k takes
// zero to the identity and a sum of exponents to the product of the powers
// (PowAddOn), so it carries the finite sum, which is the fold of the
// naturals under +, to the fold of the powers
// (ModuleSumMonoidHomomorphism).
var PowNatSum = powNatSumThm{family.Add(registry.ProofEntry{
	Name: "PowNatSum",
	Key:  "prop_139624f9a100d1a5",
	Build: comm_monoid.CommMonoidOn.Law(Statement{
		Binders: "∀x:A. ∀s:set(D). ∀m:(D → num).",
		Hypotheses: []string{
			"x ∈ c",
			"finite(s)",
		},
		Conclusion: "x ^ nat_sum(s, m) = module_sum(op, e, s, λi:D. x ^ m(i))",
	},
		func(
			a *Argument,
			monoid comm_monoid.CommMonoidFact[on.C],
			x *Member[A, on.C],
			s *Expr[Set[D]],
			m *Arrow[D, Nat],
			finite Fact,
		) {
			plus := a.TermAs[Op[Nat]]("(+)")
			op := a.TermAs[Op[A]]("op")
			identity := a.TermAs[A]("e")
			power := a.TermAs[Fun[Nat, A]]("λj:num. x ^ j")
			asFold := a.Have(
				"the finite sum of naturals is the fold of the naturals under +",
				"nat_sum(s, m) = module_sum((+), 0, s, m)",
				By(
					Normalized,
					finite,
					nat_sum.CommMonoidNatAdd,
					nat_sum.NatSumDef,
					ModuleSumIteratedOp.At(plus, a.TermAs[Nat]("0"), s, m)))
			zero := a.Have(
				"the zeroth power is the identity",
				"x ^ 0 = e",
				By(comm_monoid.MonoidPowDef))
			additive := a.Have(
				"the power at a sum of exponents is the product of the powers",
				"∀u v:num. x ^ (u + v) = op(x ^ u, x ^ v)",
				By(x, comm_monoid.PowAddOn.Read(monoid)))
			naturals := a.Have(
				"the naturals are a commutative monoid under + on the whole type",
				"comm_monoid_on(𝕌, (+), 0)",
				By(nat_sum.CommMonoidNatAdd, comm_monoid.CommMonoidOnUniverse))
			a.Show(
				"so k ↦ x ^ k carries the fold of the naturals to the fold of the powers",
				By(
					asFold,
					zero,
					additive,
					finite,
					set_basic.InUniv,
					ModuleSumMonoidHomomorphism.Read(naturals).At(op, identity, power, s, m)))
		}),
})}

// NatSumNumeral — the numeral of a finite sum of naturals is the sum of
// their numerals: the numeral of n is the ring's one added to itself n
// times, a power of one in the additive monoid (PowNatSum).
var NatSumNumeral = natSumNumeralThm{family.Add(registry.ProofEntry{
	Name: "NatSumNumeral",
	Key:  "prop_49e9a8152aaee487",
	Build: comm_ring.CommRingOn.Law(Statement{
		Binders: "∀s:set(D). ∀m:(D → num).",
		Hypotheses: []string{
			"finite(s)",
		},
		Conclusion: "monoid_pow(R.add, R.zero, R.one, nat_sum(s, m)) = " +
			"module_sum(R.add, R.zero, s, λi:D. monoid_pow(R.add, R.zero, R.one, m(i)))",
	},
		func(
			a *Argument,
			ring comm_ring.CommRingFact[on.R],
			s *Expr[Set[D]],
			m *Arrow[D, Nat],
			finite Fact,
		) {
			a.Show(
				"the ring's one, a member of its additive monoid, raised to the sum",
				By(
					finite,
					comm_ring.OneIn.Read(ring),
					PowNatSum.Read(comm_ring.AddMonoidOn.Read(ring)).AsFact().At(a.TermAs[A]("R.one"), s, m)))
		}),
})}

// ModuleSumZero — a sum of zeros is zero: ModuleSumIdentityMonoid at the
// monoid of the vectors under + (AddMonoidOn).
var ModuleSumZero = moduleSumZeroThm{family.Add(registry.ProofEntry{
	Name: "ModuleSumZero",
	Key:  "prop_b7a0f72dacdcd428",
	Build: ModuleOn.Law(Statement{
		Binders: "∀s:set(D). ∀F:(D → B).",
		Hypotheses: []string{
			"finite(s)",
			"∀x:D. x ∈ s ⇒ F(x) = M.zero",
		},
		Conclusion: "module_sum(M.add, M.zero, s, F) = M.zero",
	},
		func(a *Argument, module ModuleFact[on.R, on.M], s *Expr[Set[D]], F *Arrow[D, B], hypotheses Fact) {
			a.Show(
				"the vectors are a commutative monoid under +, where a fold of the identity is the identity",
				By(hypotheses, ModuleSumIdentityMonoid.Read(AddMonoidOn.Read(module)).At(s, F)))
		}),
})}

// ModuleSumAdd — the sum of two families is the sum of their sums:
// ModuleSumAddMonoid at the monoid of the vectors under + (AddMonoidOn).
var ModuleSumAdd = moduleSumAddThm{family.Add(registry.ProofEntry{
	Name: "ModuleSumAdd",
	Key:  "prop_7617ec335d716bb1",
	Build: ModuleOn.Law(Statement{
		Binders: "∀s:set(D). ∀F G:(D → B).",
		Hypotheses: []string{
			"finite(s)",
			"∀x:D. x ∈ s ⇒ F(x) ∈ M.carrier ∧ G(x) ∈ M.carrier",
		},
		Conclusion: "module_sum(M.add, M.zero, s, λx:D. F(x) + G(x)) = " +
			"module_sum(M.add, M.zero, s, F) + module_sum(M.add, M.zero, s, G)",
	},
		func(
			a *Argument,
			module ModuleFact[on.R, on.M],
			s *Expr[Set[D]],
			F, G *Arrow[D, B],
			hypotheses Fact,
		) {
			a.Show(
				"the vectors are a commutative monoid under +, where "+
					"the fold of a termwise sum is the sum of the folds",
				By(hypotheses, ModuleSumAddMonoid.Read(AddMonoidOn.Read(module)).At(s, F, G)))
		}),
})}

// ModuleSumSmul — induction on the finite index set: both empty sums are
// M.zero, which every scalar fixes; a new index x adds F(x) to the sum
// over the indices before it, c distributes over the two members of M,
// the claim carried there scales the rest, and c • F(x), again a member
// of M, is the term x adds to the scaled sum.
var ModuleSumSmul = moduleSumSmulThm{family.Add(registry.ProofEntry{
	Name: "ModuleSumSmul",
	Key:  "prop_71af3528e91abba0",
	Build: ModuleOn.Law(Statement{
		Binders: "∀s:set(D). ∀c:A. ∀F:(D → B).",
		Hypotheses: []string{
			"finite(s)",
			"c ∈ R.carrier",
			"∀x:D. x ∈ s ⇒ F(x) ∈ M.carrier",
		},
		Conclusion: "c • module_sum(M.add, M.zero, s, F) = module_sum(M.add, M.zero, s, λx:D. c • F(x))",
	},
		func(
			a *Argument,
			module ModuleFact[on.R, on.M],
			s *Expr[Set[D]],
			c *Expr[A],
			F *Arrow[D, B],
			hypotheses Fact,
		) {
			parts := a.Conjuncts(
				hypotheses,
				"s is finite",
				"c is a scalar",
				"F lies in M on s")
			finS, scalar, onS := parts[0], parts[1], parts[2]
			cR := a.MemberOf[on.R](c, scalar)
			scaled := a.TermAs[Fun[D, B]]("λx:D. c • F(x)")
			a.Show(
				"the induction carries the equation to every finite index set on which F lies in M, s among them",
				ByInduction(finite_set.FiniteInductFreshOn, finS, onS,
					Case(
						"both empty sums are M.zero, which every scalar fixes",
						By(SmulZero.Read(module).At(cR), ModuleSumEmpty)),
					Case(
						"one more index x: c distributes over F(x) and the sum "+
							"before it, and c • F(x) is the term x adds to the scaled sum",
						Derive(func(b *Argument) {
							x := b.FixAs[D]()
							t := b.FixAs[Set[D]]()
							carried := b.Conjuncts(
								b.Assume(),
								"c scales the sum over t termwise",
								"x is a new index of t",
								"t is finite",
								"F(x) lies in M",
								"F lies in M on t")
							rest, notIn, finT, fxIn, onT := carried[0], carried[1], carried[2], carried[3], carried[4]
							fx := b.MemberOf[on.M](F.Apply(x), fxIn)
							sumT := b.MemberOf[on.M](b.TermAs[B]("module_sum(M.add, M.zero, t, F)"),
								b.Have(
									"the sum over t lies in M",
									"module_sum(M.add, M.zero, t, F) ∈ M.carrier",
									By(finT, onT, ModuleSumIn.Read(module).At(t, F))))
							scaledFx := SmulIn.Read(module).At(cR, fx) // c • F(x): M is closed under scaling
							scaledOnT := b.Have(
								"and so does c • F(y) at every index y of t",
								"∀y:D. y ∈ t ⇒ c • F(y) ∈ M.carrier",
								b.ForEach(func(y *Expr[D]) Action {
									return By(onT.At(y), scalar, SmulIn.Read(module))
								}))
							b.Show(
								"c times the sum over insert(x, t) is the scaled sum over insert(x, t)",
								CalcEq(
									Leg(
										b.TermAs[B]("c • (F(x) + module_sum(M.add, M.zero, t, F))"),
										"x is a new index of t",
										By(finT, notIn, fxIn, onT, ModuleSumInsert.Read(module).At(t, x, F))),
									Leg(
										b.TermAs[B]("c • F(x) + c • module_sum(M.add, M.zero, t, F)"),
										"c distributes over a sum of two members of M",
										By(SmulAddLeft.Read(module).At(cR, fx, sumT))),
									Leg(
										b.TermAs[B]("c • F(x) + module_sum(M.add, M.zero, t, λy:D. c • F(y))"),
										"the claim carried to t",
										By(rest)),
									FinalLeg(
										"x is a new index of t, and c • F(x) the term it adds to the scaled sum",
										By(finT, notIn, scaledFx, scaledOnT, ModuleSumInsert.Read(module).At(t, x, scaled))),
								))
						}))))
		}),
})}

// ModuleSumSmulRight — induction on the finite index set: both empty
// sums are a zero, and the ring's zero scales v to M.zero; a new index x
// adds a(x) to the ring's sum over the indices before it, the sum of two
// scalars distributes over v, the claim carried there scales v by the
// rest, and a(x) • v, a member of M, is the term x adds to the module's
// sum. The ring's sum is the fold of the scalars' monoid under +, where
// the fold laws are read.
var ModuleSumSmulRight = moduleSumSmulRightThm{family.Add(registry.ProofEntry{
	Name: "ModuleSumSmulRight",
	Key:  "prop_92723e741d8b6dc8",
	Build: ModuleOn.Law(Statement{
		Binders: "∀s:set(D). ∀a:(D → A). ∀v:B.",
		Hypotheses: []string{
			"finite(s)",
			"∀x:D. x ∈ s ⇒ a(x) ∈ R.carrier",
			"v ∈ M.carrier",
		},
		Conclusion: "module_sum(R.add, R.zero, s, a) • v = module_sum(M.add, M.zero, s, λx:D. a(x) • v)",
	},
		func(
			arg *Argument,
			module ModuleFact[on.R, on.M],
			s *Expr[Set[D]],
			a *Arrow[D, A],
			v *Expr[B],
			hypotheses Fact,
		) {
			parts := arg.Conjuncts(
				hypotheses,
				"s is finite",
				"a is a scalar on s",
				"v is a vector")
			finS, onS, vIn := parts[0], parts[1], parts[2]
			vM := arg.MemberOf[on.M](v, vIn)
			scalars := comm_ring.AddMonoidOn.Read(RingOn.Read(module))
			ringAdd, ringZero := arg.TermAs[Op[A]]("R.add"), arg.TermAs[A]("R.zero")
			vecAdd, vecZero := arg.TermAs[Op[B]]("M.add"), arg.TermAs[B]("M.zero")
			scaled := arg.TermAs[Fun[D, B]]("λx:D. a(x) • v")
			arg.Show(
				"the induction carries the equation to every finite index set on which a is a scalar, s among them",
				ByInduction(finite_set.FiniteInductFreshOn, finS, onS,
					Case(
						"both empty sums are a zero, and the ring's zero scales v to M.zero",
						By(
							ZeroSmul.Read(module).At(vM),
							ModuleSumEmpty.At(ringAdd, ringZero, a),
							ModuleSumEmpty.At(vecAdd, vecZero, scaled))),
					Case(
						"one more index x: a(x) plus the ring's sum before it distributes "+
							"over v, and a(x) • v is the term x adds to the module's sum",
						Derive(func(b *Argument) {
							x := b.FixAs[D]()
							t := b.FixAs[Set[D]]()
							carried := b.Conjuncts(
								b.Assume(),
								"the ring's sum over t scales v to the module's",
								"x is a new index of t",
								"t is finite",
								"a(x) is a scalar",
								"a is a scalar on t")
							rest, notIn, finT, axIn, onT := carried[0], carried[1], carried[2], carried[3], carried[4]
							ax := b.MemberOf[on.R](a.Apply(x), axIn)
							sumT := b.MemberOf[on.R](b.TermAs[A]("module_sum(R.add, R.zero, t, a)"),
								b.Have(
									"the ring's sum over t is a scalar",
									"module_sum(R.add, R.zero, t, a) ∈ R.carrier",
									By(finT, onT, ModuleSumInMonoid.Read(scalars).At(t, a))))
							axv := SmulIn.Read(module).At(ax, vM) // a(x) • v: M is closed under scaling
							scaledOnT := b.Have(
								"and so does a(y) • v at every index y of t",
								"∀y:D. y ∈ t ⇒ a(y) • v ∈ M.carrier",
								b.ForEach(func(y *Expr[D]) Action {
									return By(onT.At(y), vIn, SmulIn.Read(module))
								}))
							b.Show(
								"the ring's sum over insert(x, t) scales v to the module's sum over insert(x, t)",
								CalcEq(
									Leg(
										b.TermAs[B]("(a(x) + module_sum(R.add, R.zero, t, a)) • v"),
										"x is a new index of t for the ring's sum",
										By(finT, notIn, axIn, onT, ModuleSumInsertMonoid.Read(scalars).At(t, x, a))),
									Leg(
										b.TermAs[B]("a(x) • v + module_sum(R.add, R.zero, t, a) • v"),
										"a sum of two scalars distributes over v",
										By(SmulAddRight.Read(module).At(ax, sumT, vM))),
									Leg(
										b.TermAs[B]("a(x) • v + module_sum(M.add, M.zero, t, λy:D. a(y) • v)"),
										"the claim carried to t",
										By(rest)),
									FinalLeg(
										"x is a new index of t, and a(x) • v the term it adds to the module's sum",
										By(finT, notIn, axv, scaledOnT, ModuleSumInsert.Read(module).At(t, x, scaled))),
								))
						}))))
		}),
})}

// ModuleSumSupport — s is t together with s ∖ t, two disjoint finite
// sets, so the sum over s is the sum over t plus the sum over s ∖ t;
// F is M.zero on s ∖ t, so the second sum is M.zero, the unit of +.
var ModuleSumSupport = moduleSumSupportThm{family.Add(registry.ProofEntry{
	Name: "ModuleSumSupport",
	Key:  "prop_4eb8368b7ebd2107",
	Build: ModuleOn.Law(Statement{
		Binders: "∀s t:set(D). ∀F:(D → B).",
		Hypotheses: []string{
			"finite(s)",
			"t ⊆ s",
			"∀x:D. x ∈ s ⇒ F(x) ∈ M.carrier",
			"∀x:D. x ∈ s ∧ x ∉ t ⇒ F(x) = M.zero",
		},
		Conclusion: "module_sum(M.add, M.zero, s, F) = module_sum(M.add, M.zero, t, F)",
	},
		func(
			a *Argument,
			module ModuleFact[on.R, on.M],
			s, t *Expr[Set[D]],
			F *Arrow[D, B],
			hypotheses Fact,
		) {
			parts := a.Conjuncts(
				hypotheses,
				"s is finite",
				"t is a part of s",
				"F lies in M on s",
				"F is M.zero on s off t")
			finS, tSub, onS, offT := parts[0], parts[1], parts[2], parts[3]
			additive := AddGroupOn.Read(module)
			outside := a.TermAs[Set[D]]("s ∖ t")
			finT := a.Have(
				"t, a part of a finite set, is finite",
				"finite(t)",
				By(finS, tSub, finite_set.FiniteSubset.At(t, s)))
			finOutside := a.Have(
				"and so is s ∖ t",
				"finite(s ∖ t)",
				By(finS, finite_set.FiniteDiff.At(s, t)))
			split := a.Have(
				"s is t together with the rest of s",
				"s = t ∪ (s ∖ t)",
				BySets(tSub))
			disjoint := a.Have(
				"t and the rest of s are disjoint",
				"disjoint(t, s ∖ t)",
				BySets())
			onParts := a.Have(
				"F lies in M on t and on s ∖ t, two parts of s",
				"∀x:D. x ∈ t ∨ x ∈ s ∖ t ⇒ F(x) ∈ M.carrier",
				a.ForEach(func(x *Expr[D]) Action { return BySets(tSub, onS.At(x)) }))
			onT := a.Have(
				"in particular on t",
				"∀x:D. x ∈ t ⇒ F(x) ∈ M.carrier",
				a.ForEach(func(x *Expr[D]) Action { return By(onParts.At(x)) }))
			zeroRest := a.Have(
				"F is M.zero on s ∖ t",
				"∀x:D. x ∈ s ∖ t ⇒ F(x) = M.zero",
				a.ForEach(func(x *Expr[D]) Action {
					return By(offT.At(x), set_basic.InDiff.At(s, t, x))
				}))
			sumT := a.MemberOf[on.M](a.TermAs[B]("module_sum(M.add, M.zero, t, F)"),
				a.Have(
					"so the sum over t lies in M",
					"module_sum(M.add, M.zero, t, F) ∈ M.carrier",
					By(finT, onT, ModuleSumIn.Read(module).At(t, F))))
			a.Show(
				"the sum over s is the sum over t",
				CalcEq(
					Leg(
						a.TermAs[B]("module_sum(M.add, M.zero, t ∪ (s ∖ t), F)"),
						"s is t together with the rest of s",
						By(Normalized, split)),
					Leg(
						a.TermAs[B]("module_sum(M.add, M.zero, t, F) + module_sum(M.add, M.zero, s ∖ t, F)"),
						"t and s ∖ t are disjoint finite sets",
						By(finT, finOutside, disjoint, onParts, ModuleSumDisjointUnion.Read(module).At(t, outside, F))),
					Leg(
						a.TermAs[B]("module_sum(M.add, M.zero, t, F) + M.zero"),
						"F is M.zero on s ∖ t, so its sum there is M.zero",
						By(finOutside, zeroRest, ModuleSumZero.Read(module).At(outside, F))),
					FinalLeg(
						"M.zero is the unit of +",
						By(group.RightIdentityOn.Read(additive).At(sumT))),
				))
		}),
})}

// ModuleSumSingle — a sum whose terms vanish off one index x is its term
// there: F is M.zero on s off {x}, so the sum over s is the sum over {x}
// (ModuleSumSupport), and {x} is x laid into the empty set, so that sum
// is F(x) plus the empty sum, M.zero.
var ModuleSumSingle = moduleSumSingleThm{family.Add(registry.ProofEntry{
	Name: "ModuleSumSingle",
	Key:  "prop_7c260ced4fbcc4b2",
	Build: ModuleOn.Law(Statement{
		Binders: "∀s:set(D). ∀x:D. ∀F:(D → B).",
		Hypotheses: []string{
			"finite(s)",
			"x ∈ s",
			"∀y:D. y ∈ s ⇒ F(y) ∈ M.carrier",
			"∀y:D. y ∈ s ∧ y ≠ x ⇒ F(y) = M.zero",
		},
		Conclusion: "module_sum(M.add, M.zero, s, F) = F(x)",
	},
		func(
			a *Argument,
			module ModuleFact[on.R, on.M],
			s *Expr[Set[D]],
			x *Expr[D],
			F *Arrow[D, B],
			hypotheses Fact,
		) {
			parts := a.Conjuncts(
				hypotheses,
				"s is finite",
				"x is an index of s",
				"F lies in M on s",
				"F is M.zero on s off x")
			finS, xIn, onS, offX := parts[0], parts[1], parts[2], parts[3]
			single, empty := a.TermAs[Set[D]]("{x}"), a.TermAs[Set[D]]("∅")
			offSingle := a.Have(
				"F is M.zero on s off {x}",
				"∀y:D. y ∈ s ∧ y ∉ {x} ⇒ F(y) = M.zero",
				a.ForEach(func(y *Expr[D]) Action {
					return By(offX.At(y), set_basic.InSing.At(y, x))
				}))
			fx := a.MemberOf[on.M](F.Apply(x), a.Have(
				"F(x) lies in M",
				"F(x) ∈ M.carrier",
				By(onS.At(x), xIn)))
			onEmpty := a.Have(
				"F lies in M at each index of ∅, there being none",
				"∀y:D. y ∈ ∅ ⇒ F(y) ∈ M.carrier",
				By(set_basic.NotInEmpty))
			a.Show(
				"the sum over s is its term at x",
				CalcEq(
					Leg(
						a.TermAs[B]("module_sum(M.add, M.zero, {x}, F)"),
						"F vanishes on s off x, so the sum over s shrinks to {x}",
						By(
							finS,
							set_order.SingSubset.At(s, x),
							xIn,
							onS,
							offSingle,
							ModuleSumSupport.Read(module).At(s, single, F))),
					Leg(
						a.TermAs[B]("F(x) + module_sum(M.add, M.zero, ∅, F)"),
						"{x} is x laid into the empty set",
						By(
							finite_set.FiniteRules,
							set_basic.NotInEmpty.At(x),
							fx,
							onEmpty,
							ModuleSumInsert.Read(module).At(empty, x, F))),
					FinalLeg(
						"the empty sum is M.zero, the unit of +",
						By(ModuleSumEmpty, group.RightIdentityOn.Read(AddGroupOn.Read(module)).At(fx))),
				))
		}),
})}

// ModuleSumSwap — two finite sums interchange. Each double sum is a sum
// over a product of the index sets, the first over s × t and the second
// over t × s (ModuleSumCross). s × t is the image of t × s under the swap
// of a pair's components (CrossSwap), which tells the pairs apart, so the
// sum over s × t is the sum over t × s of the summand at the swapped pair
// (ModuleSumImage), which the projections read as the second double
// sum's summand.
var ModuleSumSwap = moduleSumSwapThm{family.Add(registry.ProofEntry{
	Name: "ModuleSumSwap",
	Key:  "prop_3f635902ad93cac0",
	Build: ModuleOn.Law(Statement{
		Binders: "∀s:set(D). ∀t:set(E). ∀F:(D → E → B).",
		Hypotheses: []string{
			"finite(s)",
			"finite(t)",
			"∀x:D. ∀y:E. x ∈ s ∧ y ∈ t ⇒ F(x, y) ∈ M.carrier",
		},
		Conclusion: "module_sum(M.add, M.zero, s, λx:D. module_sum(M.add, M.zero, t, λy:E. F(x, y))) = " +
			"module_sum(M.add, M.zero, t, λy:E. module_sum(M.add, M.zero, s, λx:D. F(x, y)))",
	},
		func(
			a *Argument,
			module ModuleFact[on.R, on.M],
			s *Expr[Set[D]],
			t *Expr[Set[E]],
			F *Arrow2[D, E, B],
			hypotheses Fact,
		) {
			parts := a.Conjuncts(
				hypotheses,
				"s is finite",
				"t is finite",
				"F lies in M on s × t")
			finS, finT, onST := parts[0], parts[1], parts[2]
			swap := a.TermAs[Fun[Prod[E, D], Prod[D, E]]]("λq:prod(E, D). (snd(q), fst(q))")
			pairsTS := a.TermAs[Set[Prod[E, D]]]("set_cross(t, s)")
			summand := a.TermAs[Fun[Prod[D, E], B]]("λp:prod(D, E). F(fst(p), snd(p))")
			transposed := a.TermAs[Fun2[E, D, B]]("λy:E. λx:D. F(x, y)")
			projectFirst := pairs.Fst.Inst(TypeBinder.BindA[D](), TypeBinder.BindB[E]())
			projectSecond := pairs.Snd.Inst(TypeBinder.BindA[D](), TypeBinder.BindB[E]())

			injective := a.Have(
				"the swap tells the pairs of t × s apart",
				"injective_on(set_cross(t, s), λq:prod(E, D). (snd(q), fst(q)))",
				Unfold(functions.InjectiveOnDef),
				Derive(func(b *Argument) {
					u := b.FixAs[Prod[E, D]]("u")
					v := b.FixAs[Prod[E, D]]("v")
					b.Show(
						"equal swaps have equal components, and a pair is its two components",
						By(
							pairs.PairEq.At(
								b.TermAs[D]("snd(u)"), b.TermAs[E]("fst(u)"), b.TermAs[D]("snd(v)"), b.TermAs[E]("fst(v)")),
							pairs.PairEta.At(u),
							pairs.PairEta.At(v)))
				}))
			finTS := a.Have(
				"t × s is finite",
				"finite(set_cross(t, s))",
				By(finT, finS, finite_set.FiniteProduct.At(t, s)))
			onSwaps := a.Have(
				"at the swap of a pair q in t × s the summand is F(snd(q), fst(q)), in M",
				"∀q:prod(E, D). q ∈ set_cross(t, s) ⇒ F(fst((snd(q), fst(q))), snd((snd(q), fst(q)))) ∈ M.carrier",
				Simp(Fwd(projectFirst), Fwd(projectSecond)),
				Derive(func(b *Argument) {
					q := b.FixAs[Prod[E, D]]("q")
					b.Show(
						"q lies in t × s exactly when snd(q) lies in s and fst(q) in t",
						By(
							set_product.InCrossProjections.At(t, s, q),
							onST.At(b.TermAs[D]("snd(q)"), b.TermAs[E]("fst(q)"))))
				}))
			a.Show(
				"both double sums are the sum of F over the pairs, read through the swap",
				CalcEq(
					Leg(
						a.TermAs[B]("module_sum(M.add, M.zero, set_cross(s, t), λp:prod(D, E). F(fst(p), snd(p)))"),
						"the double sum over s and t is the sum over s × t",
						By(finS, finT, onST, ModuleSumCross.Read(module).At(s, t, F))),
					Leg(
						a.TermAs[B](
							"module_sum(M.add, "+
								"    M.zero, "+
								"    image(λq:prod(E, D). (snd(q), fst(q)), set_cross(t, s)), "+
								"    λp:prod(D, E). F(fst(p), snd(p)))"),
						"s × t is the swap of t × s",
						By(set_product.CrossSwap.At(s, t))),
					Leg(
						a.TermAs[B](
							"module_sum(M.add, "+
								"    M.zero, "+
								"    set_cross(t, s), "+
								"    λq:prod(E, D). F(fst((snd(q), fst(q))), snd((snd(q), fst(q)))))"),
						"the swap is injective on t × s: the sum over its image is the sum of the summand at the swaps",
						By(finTS, injective, onSwaps, ModuleSumImage.Read(module).At(pairsTS, swap, summand))),
					Leg(
						a.TermAs[B]("module_sum(M.add, M.zero, set_cross(t, s), λq:prod(E, D). F(snd(q), fst(q)))"),
						"the projections undo the pairing",
						Simp(Fwd(projectFirst), Fwd(projectSecond)),
						Basic()),
					FinalLeg(
						"the sum over t × s is the double sum over t and s of F, its arguments transposed",
						By(finT, finS, onST, ModuleSumCross.Read(module).At(t, s, transposed))),
				))
		}),
})}

// ModuleSumFibres — a finite sum is the sum of its sums over the fibres
// of a map. The mask G(i, z), which is F(i) where f(i) = z and M.zero
// elsewhere, sums over the image to F(i), only the value f(i) contributing
// (ModuleSumSingle), and over S to the sum over the fibre at z, off which
// it vanishes (ModuleSumSupport); the two sums of the mask interchange
// (ModuleSumSwap).
var ModuleSumFibres = moduleSumFibresThm{family.Add(registry.ProofEntry{
	Name: "ModuleSumFibres",
	Key:  "prop_24e90fd7305ad93b",
	Build: ModuleOn.Law(Statement{
		Binders: "∀S:set(D). ∀f:(D → E). ∀F:(D → B).",
		Hypotheses: []string{
			"finite(S)",
			"∀i:D. i ∈ S ⇒ F(i) ∈ M.carrier",
		},
		Conclusion: "module_sum(M.add, M.zero, S, F) = " +
			"module_sum(M.add, " +
			"    M.zero, " +
			"    image(f, S), " +
			"    λz:E. module_sum(M.add, M.zero, {i:D | i ∈ S ∧ f(i) = z}, F))",
	},
		func(
			a *Argument,
			module ModuleFact[on.R, on.M],
			S *Expr[Set[D]],
			f *Arrow[D, E],
			F *Arrow[D, B],
			hypotheses Fact,
		) {
			parts := a.Conjuncts(
				hypotheses,
				"S is finite",
				"F lies in M on S")
			finS, onS := parts[0], parts[1]
			zeroIn := group.OneIn.Read(AddGroupOn.Read(module))
			U, imageDef := a.LetAs[Set[E]]("U", "image(f, S)")
			G, maskDef := a.LetAs[Fun2[D, E, B]]("G", "λi:D. λz:E. COND(f(i) = z, F(i), M.zero)")
			finU := a.Have(
				"the image of the finite index set is finite",
				"finite(U)",
				By(Normalized, finS, imageDef, finite_set.FiniteImage.At(f, S)))
			masked := a.Have(
				"the mask lies in M on S × U",
				"∀i:D. ∀z:E. i ∈ S ∧ z ∈ U ⇒ G(i, z) ∈ M.carrier",
				maskDef.Rw(),
				BySets(onS, zeroIn))
			rows := a.Have(
				"summing the mask over the image recovers each original summand",
				"∀i:D. i ∈ S ⇒ module_sum(M.add, M.zero, U, λz:E. G(i, z)) = F(i)",
				Derive(func(b *Argument) {
					i := b.FixAs[D]("i")
					inS := b.Assume()
					b.Show(
						"only the image value f(i) contributes",
						maskDef.Rw(),
						BySets(
							finU,
							imageDef,
							inS,
							onS,
							zeroIn,
							ModuleSumSingle.Read(module).At(
								U, f.Apply(i), b.TermAs[Fun[E, B]]("λz:E. COND(f(i) = z, F(i), M.zero)"))))
				}))
			columns := a.Have(
				"summing the mask over the original indices gives the fibre sum",
				Statement{
					Binders:    "∀z:E.",
					Hypotheses: []string{"z ∈ U"},
					Conclusion: "module_sum(M.add, M.zero, S, λi:D. G(i, z)) = " +
						"module_sum(M.add, M.zero, {i:D | i ∈ S ∧ f(i) = z}, F)",
				},
				Derive(func(b *Argument) {
					b.FixAs[E]("z")
					b.Assume()
					b.Show(
						"restrict to the fibre and remove the mask there",
						maskDef.Rw(),
						CalcEq(
							Leg(
								b.TermAs[B](
									"module_sum(M.add, M.zero, {i:D | i ∈ S ∧ f(i) = z}, λi:D. COND(f(i) = z, F(i), M.zero))"),
								"the summand vanishes outside this fibre",
								BySets(
									finS,
									onS,
									zeroIn,
									ModuleSumSupport.Read(module).At(
										S,
										b.TermAs[Set[D]]("{i:D | i ∈ S ∧ f(i) = z}"),
										b.TermAs[Fun[D, B]]("λi:D. COND(f(i) = z, F(i), M.zero)")))),
							FinalLeg(
								"the mask equals the original summand on the fibre",
								BySets(ModuleSumCongruence))))
				}))
			a.Show(
				"interchange the masked sums and identify the fibre sums",
				CalcEq(
					Leg(
						a.TermAs[B]("module_sum(M.add, M.zero, S, λi:D. module_sum(M.add, M.zero, U, λz:E. G(i, z)))"),
						"replace each summand by its masked row",
						By(rows, ModuleSumCongruence)),
					Leg(
						a.TermAs[B]("module_sum(M.add, M.zero, U, λz:E. module_sum(M.add, M.zero, S, λi:D. G(i, z)))"),
						"interchange the two finite sums",
						By(finS, finU, masked, ModuleSumSwap.Read(module).At(S, U, G))),
					FinalLeg(
						"replace each column by its fibre sum",
						By(columns, ModuleSumCongruence))))
		}),
})}

// ModuleSumTriangleSwap — a finite sum over the triangle i ≤ k ≤ n,
// grouped by k, is the same sum grouped by i, the second index running
// as k = i + j over j ≤ n - i. Padded by M.zero off the triangle, G fills
// the square i, k ≤ n, where the two sums interchange (ModuleSumSwap).
// The padded row at k sums to the row of the triangle, the padding adding
// nothing beyond k; the padded column at i sums to the column read from
// the diagonal, the padding adding nothing below i, and the indices from
// i to n being the shifts i + j of the offsets j ≤ n - i, which adding i
// tells apart.
var ModuleSumTriangleSwap = moduleSumTriangleSwapThm{family.Add(registry.ProofEntry{
	Name: "ModuleSumTriangleSwap",
	Key:  "prop_945362d7c3081038",
	Build: ModuleOn.Law(Statement{
		Binders: "∀n:num. ∀G:(num → num → B).",
		Hypotheses: []string{
			"∀i k:num. i ≤ k ∧ k ≤ n ⇒ G(i, k) ∈ M.carrier",
		},
		Conclusion: "module_sum(M.add, " +
			"    M.zero, " +
			"    {k:num | k ≤ n}, " +
			"    λk:num. module_sum(M.add, M.zero, {i:num | i ≤ k}, λi:num. G(i, k))) = " +
			"module_sum(M.add, " +
			"    M.zero, " +
			"    {i:num | i ≤ n}, " +
			"    λi:num. module_sum(M.add, M.zero, {j:num | j ≤ n - i}, λj:num. G(i, i + j)))",
	},
		func(
			a *Argument,
			module ModuleFact[on.R, on.M],
			n *Expr[Nat],
			G *Arrow2[Nat, Nat, B],
			onTriangle Fact,
		) {
			upToN := a.TermAs[Set[Nat]]("{k:num | k ≤ n}")
			padded := a.Have(
				"padded by M.zero off the triangle, G lies in M on the whole square k, i ≤ n",
				"∀k i:num. k ∈ {k:num | k ≤ n} ∧ i ∈ {i:num | i ≤ n} ⇒ COND(i ≤ k, G(i, k), M.zero) ∈ M.carrier",
				BySets(onTriangle, group.OneIn.Read(AddGroupOn.Read(module))))
			rows := a.Have(
				"the row of the triangle at k ≤ n is the padded row summed over i ≤ n",
				Statement{
					Binders: "∀k:num.",
					Hypotheses: []string{
						"k ∈ {k:num | k ≤ n}",
					},
					Conclusion: "module_sum(M.add, M.zero, {i:num | i ≤ k}, λi:num. G(i, k)) = " +
						"module_sum(M.add, M.zero, {i:num | i ≤ n}, λi:num. COND(i ≤ k, G(i, k), M.zero))",
				},
				Derive(func(b *Argument) {
					b.FixAs[Nat]("k")
					among := b.Assume()
					kBound := b.Have(
						"so k is at most n",
						"k ≤ n",
						BySets(among))
					upToK, row :=
						b.TermAs[Set[Nat]]("{i:num | i ≤ k}"), b.TermAs[Fun[Nat, B]]("λi:num. COND(i ≤ k, G(i, k), M.zero)")
					bounded := b.Have(
						"an index up to k is at most n",
						"∀i:num. i ≤ k ⇒ i ≤ n",
						ByArith(kBound))
					inside := b.Have(
						"so the indices up to k are among those up to n",
						"{i:num | i ≤ k} ⊆ {i:num | i ≤ n}",
						BySets(bounded))
					onRow := b.Have(
						"the padded row lies in M",
						"∀i:num. i ∈ {i:num | i ≤ n} ⇒ COND(i ≤ k, G(i, k), M.zero) ∈ M.carrier",
						BySets(padded, among))
					beyond := b.Have(
						"and is M.zero beyond k",
						"∀i:num. i ∈ {i:num | i ≤ n} ∧ i ∉ {i:num | i ≤ k} ⇒ COND(i ≤ k, G(i, k), M.zero) = M.zero",
						BySets())
					b.Show(
						"the padding adds nothing to the row",
						CalcEq(
							Leg(
								b.TermAs[B]("module_sum(M.add, M.zero, {i:num | i ≤ k}, λi:num. COND(i ≤ k, G(i, k), M.zero))"),
								"up to k the padded row is the row",
								BySets(ModuleSumCongruence)),
							FinalLeg(
								"and beyond k it is M.zero",
								By(
									inside,
									onRow,
									beyond,
									num_segment.FiniteBelow.At(n),
									ModuleSumSupport.Read(module).At(upToN, upToK, row))),
						))
				}))
			columns := a.Have(
				"the padded column at i ≤ n, summed over k ≤ n, is "+
					"the column of the triangle read from the diagonal",
				Statement{
					Binders: "∀i:num.",
					Hypotheses: []string{
						"i ∈ {i:num | i ≤ n}",
					},
					Conclusion: "module_sum(M.add, M.zero, {k:num | k ≤ n}, λk:num. COND(i ≤ k, G(i, k), M.zero)) = " +
						"module_sum(M.add, M.zero, {j:num | j ≤ n - i}, λj:num. G(i, i + j))",
				},
				Derive(func(b *Argument) {
					b.FixAs[Nat]("i")
					among := b.Assume()
					iBound := b.Have(
						"so i is at most n",
						"i ≤ n",
						BySets(among))
					offsets, shift :=
						b.TermAs[Set[Nat]]("{j:num | j ≤ n - i}"), b.TermAs[Fun[Nat, Nat]]("λj:num. i + j")
					shifts := b.TermAs[Set[Nat]]("image(λj:num. i + j, {j:num | j ≤ n - i})")
					column := b.TermAs[Fun[Nat, B]]("λk:num. COND(i ≤ k, G(i, k), M.zero)")
					forth := b.Have(
						"the shift i + j of an offset j ≤ n - i is at most n",
						"∀j:num. j ≤ n - i ⇒ i + j ≤ n",
						ByArith(iBound))
					back := b.Have(
						"and every k between i and n is i + (k - i), its offset at most n - i",
						"∀k:num. i ≤ k ∧ k ≤ n ⇒ k - i ≤ n - i ∧ i + (k - i) = k",
						ByArith())
					inside := b.Have(
						"so the shifts of the offsets are among the indices up to n",
						"image(λj:num. i + j, {j:num | j ≤ n - i}) ⊆ {k:num | k ≤ n}",
						BySets(forth))
					onColumn := b.Have(
						"the padded column lies in M",
						"∀k:num. k ∈ {k:num | k ≤ n} ⇒ COND(i ≤ k, G(i, k), M.zero) ∈ M.carrier",
						BySets(padded, among))
					below := b.Have(
						"and is M.zero at an index up to n that is no shift, the index lying below i",
						Statement{
							Binders: "∀k:num.",
							Hypotheses: []string{
								"k ∈ {k:num | k ≤ n}",
								"k ∉ image(λj:num. i + j, {j:num | j ≤ n - i})",
							},
							Conclusion: "COND(i ≤ k, G(i, k), M.zero) = M.zero",
						},
						BySets(back))
					apart := b.Have(
						"adding i tells the offsets apart",
						"injective_on({j:num | j ≤ n - i}, λj:num. i + j)",
						BySets(functions.InjectiveOnDef, nat_arith.AddEqLCancel))
					atShifts := b.Have(
						"the padded column lies in M at every shift",
						"∀j:num. j ∈ {j:num | j ≤ n - i} ⇒ COND(i ≤ i + j, G(i, i + j), M.zero) ∈ M.carrier",
						BySets(padded, forth, among))
					b.Show(
						"the padding adds nothing to the column, read from the diagonal",
						CalcEq(
							Leg(
								b.TermAs[B](
									"module_sum(M.add, "+
										"    M.zero, "+
										"    image(λj:num. i + j, {j:num | j ≤ n - i}), "+
										"    λk:num. COND(i ≤ k, G(i, k), M.zero))"),
								"below i the padded column is M.zero, and the indices from i to n are the shifts",
								By(
									inside,
									onColumn,
									below,
									num_segment.FiniteBelow.At(n),
									ModuleSumSupport.Read(module).At(upToN, shifts, column))),
							Leg(
								b.TermAs[B](
									"module_sum(M.add, M.zero, {j:num | j ≤ n - i}, λj:num. COND(i ≤ i + j, G(i, i + j), M.zero))"),
								"reindex along the shift, which tells the offsets apart",
								By(
									apart,
									atShifts,
									num_segment.FiniteBelow.At(b.TermAs[Nat]("n - i")),
									ModuleSumImage.Read(module).At(offsets, shift, column))),
							FinalLeg(
								"i ≤ i + j, so at every shift the padded column is G itself",
								BySets(nat_order.LessEqAdd)),
						))
				}))
			square := a.TermAs[Fun2[Nat, Nat, B]]("λk:num. λi:num. COND(i ≤ k, G(i, k), M.zero)")
			a.Show(
				"both sides sum the padding over the square, by rows and by columns",
				CalcEq(
					Leg(
						a.TermAs[B](
							"module_sum(M.add, "+
								"    M.zero, "+
								"    {k:num | k ≤ n}, "+
								"    λk:num. module_sum(M.add, M.zero, {i:num | i ≤ n}, λi:num. COND(i ≤ k, G(i, k), M.zero)))"),
						"pad every row",
						By(rows, ModuleSumCongruence)),
					Leg(
						a.TermAs[B](
							"module_sum(M.add, "+
								"    M.zero, "+
								"    {i:num | i ≤ n}, "+
								"    λi:num. module_sum(M.add, M.zero, {k:num | k ≤ n}, λk:num. COND(i ≤ k, G(i, k), M.zero)))"),
						"the two sums over the square interchange",
						By(padded, num_segment.FiniteBelow.At(n), ModuleSumSwap.Read(module).At(upToN, upToN, square))),
					FinalLeg(
						"and every padded column is the column read from the diagonal",
						By(columns, ModuleSumCongruence)),
				))
		}),
})}

// ModuleSumDisjointUnion — induction on the finite index set t, s held
// fixed: over ∅ the union is s and the empty sum is M.zero, the unit of +;
// an index x added to t lies outside s by disjointness, so x is new to
// s ∪ t as well as to t, and peeling F(x) off both sides leaves the
// claim carried to t, regrouped by associativity and commutativity on M.
var ModuleSumDisjointUnion = moduleSumDisjointUnionThm{family.Add(registry.ProofEntry{
	Name: "ModuleSumDisjointUnion",
	Key:  "prop_3a9120a2e3621dfb",
	Build: ModuleOn.Law(Statement{
		Binders: "∀s t:set(D). ∀F:(D → B).",
		Hypotheses: []string{
			"finite(s)",
			"finite(t)",
			"disjoint(s, t)",
			"∀x:D. x ∈ s ∨ x ∈ t ⇒ F(x) ∈ M.carrier",
		},
		Conclusion: "module_sum(M.add, M.zero, s ∪ t, F) = " +
			"module_sum(M.add, M.zero, s, F) + module_sum(M.add, M.zero, t, F)",
	},
		func(
			a *Argument,
			module ModuleFact[on.R, on.M],
			s, t *Expr[Set[D]],
			F *Arrow[D, B],
			hypotheses Fact,
		) {
			parts := a.Conjuncts(
				hypotheses,
				"s is finite",
				"t is finite",
				"s and t are disjoint",
				"F lies in M on s and on t")
			finS, finT, disjointST, onST := parts[0], parts[1], parts[2], parts[3]
			additive := AddGroupOn.Read(module)
			onS := a.Have(
				"F lies in M on s",
				"∀x:D. x ∈ s ⇒ F(x) ∈ M.carrier",
				a.ForEach(func(x *Expr[D]) Action { return By(onST.At(x)) }))
			onT := a.Have(
				"and on t",
				"∀x:D. x ∈ t ⇒ F(x) ∈ M.carrier",
				a.ForEach(func(x *Expr[D]) Action { return By(onST.At(x)) }))
			sumS := a.MemberOf[on.M](a.TermAs[B]("module_sum(M.add, M.zero, s, F)"),
				a.Have(
					"so the sum over s lies in M",
					"module_sum(M.add, M.zero, s, F) ∈ M.carrier",
					By(finS, onS, ModuleSumIn.Read(module).At(s, F))))
			a.Show(
				"the induction carries the split to every finite index "+
					"set disjoint from s on which F lies in M, t among them",
				ByInduction(finite_set.FiniteInductFreshOn, finT, onT, Generalizing(disjointST),
					Case(
						"over ∅ the union is s, and the empty sum is M.zero, the unit of +",
						Derive(func(b *Argument) {
							emptyUnion := b.Have(
								"∅ adds no index to s",
								"s ∪ ∅ = s",
								BySets())
							b.Show(
								"the sum over s is itself plus M.zero",
								By(emptyUnion, ModuleSumEmpty, group.RightIdentityOn.Read(additive).At(sumS)))
						})),
					Case(
						"one more index x lies outside s, and adds F(x) to both sides",
						Derive(func(b *Argument) {
							x := b.FixAs[D]()
							r := b.FixAs[Set[D]]("r")
							carried := b.Conjuncts(
								b.Assume(),
								"the split over r, for r disjoint from s",
								"x is a new index of r",
								"r is finite",
								"F(x) lies in M",
								"F lies in M on r")
							claimR, notIn, finR, fxIn, onR := carried[0], carried[1], carried[2], carried[3], carried[4]
							disjoint := b.Assume() // s and insert(x, r) are disjoint
							disjointR := b.Have(
								"s and r, a part of insert(x, r), are disjoint",
								"disjoint(s, r)",
								BySets(disjoint))
							sumR := b.MemberOf[on.M](b.TermAs[B]("module_sum(M.add, M.zero, r, F)"),
								b.Have(
									"the sum over r lies in M",
									"module_sum(M.add, M.zero, r, F) ∈ M.carrier",
									By(finR, onR, ModuleSumIn.Read(module).At(r, F))))
							fresh := b.Have(
								"x lies in insert(x, r), which s misses, and not in r: x is a new index of s ∪ r",
								"x ∉ s ∪ r",
								BySets(disjoint, notIn))
							finUnion := b.Have(
								"s ∪ r is finite",
								"finite(s ∪ r)",
								By(finS, finR, finite_set.FiniteUnion.At(s, r)))
							onUnion := b.Have(
								"F lies in M on s ∪ r",
								"∀y:D. y ∈ s ∪ r ⇒ F(y) ∈ M.carrier",
								b.ForEach(func(y *Expr[D]) Action {
									return BySets(onS.At(y), onR.At(y))
								}))
							reindex := b.Have(
								"adding x to r adds it to s ∪ r",
								"s ∪ insert(x, r) = insert(x, s ∪ r)",
								BySets())
							peelUnion := b.Have(
								"x is a new index of s ∪ r: the sum over insert(x, s ∪ r) is F(x) plus the sum over s ∪ r",
								"module_sum(M.add, M.zero, insert(x, s ∪ r), F) = F(x) + module_sum(M.add, M.zero, s ∪ r, F)",
								By(
									finUnion,
									fresh,
									fxIn,
									onUnion,
									ModuleSumInsert.Read(module).At(b.TermAs[Set[D]]("s ∪ r"), x, F)))
							peelR := b.Have(
								"and of r: the sum over insert(x, r) is F(x) plus the sum over r",
								"module_sum(M.add, M.zero, insert(x, r), F) = F(x) + module_sum(M.add, M.zero, r, F)",
								By(finR, notIn, fxIn, onR, ModuleSumInsert.Read(module).At(r, x, F)))
							fx := b.MemberOf[on.M](F.Apply(x), fxIn)
							b.Show(
								"the sum over s ∪ insert(x, r) is the sum over s plus the sum over insert(x, r)",
								CalcEq(
									Leg(
										b.TermAs[B]("module_sum(M.add, M.zero, insert(x, s ∪ r), F)"),
										"adding x to r adds it to s ∪ r",
										By(Normalized, reindex)),
									Leg(
										b.TermAs[B]("F(x) + module_sum(M.add, M.zero, s ∪ r, F)"),
										"x is a new index of s ∪ r",
										By(peelUnion)),
									Leg(
										b.TermAs[B]("F(x) + (module_sum(M.add, M.zero, s, F) + module_sum(M.add, M.zero, r, F))"),
										"the claim carried to r",
										By(claimR, disjointR)),
									Leg(
										b.TermAs[B]("F(x) + module_sum(M.add, M.zero, s, F) + module_sum(M.add, M.zero, r, F)"),
										"+ associates on M",
										By(group.AssocOn.Read(additive).At(fx, sumS, sumR))),
									Leg(
										b.TermAs[B]("module_sum(M.add, M.zero, s, F) + F(x) + module_sum(M.add, M.zero, r, F)"),
										"F(x) and the sum over s commute",
										By(AddComm.Read(module).At(fx, sumS))),
									Leg(
										b.TermAs[B]("module_sum(M.add, M.zero, s, F) + (F(x) + module_sum(M.add, M.zero, r, F))"),
										"+ associates on M",
										By(group.AssocOn.Read(additive).At(sumS, fx, sumR))),
									FinalLeg(
										"x is a new index of r",
										By(peelR)),
								))
						}))))
		}),
})}

// ModuleSumNeg — induction on the finite index set: both empty sums are
// M.zero, which is its own negative; a new index x adds -F(x) to the sum
// of the negatives over the indices before it, the negative of their sum
// by the claim carried there, and -F(x) + -rest is -(F(x) + rest), the
// vectors being an abelian group.
var ModuleSumNeg = moduleSumNegThm{family.Add(registry.ProofEntry{
	Name: "ModuleSumNeg",
	Key:  "prop_12d07f71c953239d",
	Build: ModuleOn.Law(Statement{
		Binders: "∀s:set(D). ∀F:(D → B).",
		Hypotheses: []string{
			"finite(s)",
			"∀x:D. x ∈ s ⇒ F(x) ∈ M.carrier",
		},
		Conclusion: "module_sum(M.add, M.zero, s, λx:D. -F(x)) = -module_sum(M.add, M.zero, s, F)",
	},
		func(a *Argument, module ModuleFact[on.R, on.M], s *Expr[Set[D]], F *Arrow[D, B], hypotheses Fact) {
			additive := AddGroupOn.Read(module)
			negatives := a.TermAs[Fun[D, B]]("λx:D. -F(x)")
			a.Show(
				"the induction carries the equation to every finite index set on which F lies in M, s among them",
				ByInduction(finite_set.FiniteInductFreshOn, hypotheses,
					Case(
						"both empty sums are M.zero, which is its own negative",
						By(group.InvOneOn.Read(additive), ModuleSumEmpty)),
					Case(
						"one more index adds -F(x) to the sum of the negatives and F(x) under the negative of the sum",
						Derive(func(b *Argument) {
							x := b.FixAs[D]()
							t := b.FixAs[Set[D]]()
							carried := b.Conjuncts(
								b.Assume(),
								"the sum of the negatives over t is the negative of the sum",
								"x is a new index of t",
								"t is finite",
								"F(x) lies in M",
								"F lies in M on t")
							rest, notIn, finT, fxIn, onT := carried[0], carried[1], carried[2], carried[3], carried[4]
							restIn := b.Have(
								"the sum of F over t lies in M",
								"module_sum(M.add, M.zero, t, F) ∈ M.carrier",
								By(finT, onT, ModuleSumIn.Read(module).At(t, F)))
							u := b.MemberOf[on.M](F.Apply(x), fxIn)
							v := b.MemberOf[on.M](b.TermAs[B]("module_sum(M.add, M.zero, t, F)"), restIn)
							negFxIn := b.Have(
								"M is closed under negation: -F(x) lies in M",
								"-F(x) ∈ M.carrier",
								By(group.InvIn.Read(additive).At(u)))
							peel := b.Have(
								"x is a new index: the sum of F over insert(x, t) is F(x) plus the sum over t",
								"module_sum(M.add, M.zero, insert(x, t), F) = F(x) + module_sum(M.add, M.zero, t, F)",
								By(notIn, finT, fxIn, onT, ModuleSumInsert.Read(module).At(t, x, F)))
							peelNeg := b.Have(
								"and the sum of the negatives, members of M, is -F(x) plus their sum over t",
								"module_sum(M.add, M.zero, insert(x, t), λy:D. -F(y)) = "+
									"-F(x) + module_sum(M.add, M.zero, t, λy:D. -F(y))",
								By(
									group.InvIn.Read(additive),
									notIn,
									finT,
									negFxIn,
									onT,
									ModuleSumInsert.Read(module).At(t, x, negatives)))
							b.Show(
								"the sum of the negatives over insert(x, t) is the negative of the sum",
								CalcEq(
									Leg(
										b.TermAs[B]("-F(x) + module_sum(M.add, M.zero, t, λy:D. -F(y))"),
										"x is a new index of the negatives",
										By(peelNeg)),
									Leg(
										b.TermAs[B]("-F(x) + -module_sum(M.add, M.zero, t, F)"),
										"the claim carried to t",
										By(rest)),
									Leg(
										b.TermAs[B]("-(F(x) + module_sum(M.add, M.zero, t, F))"),
										"the negative of a sum of two members of M is the sum of their negatives",
										By(abelian_group.NegAddOn.Read(AddAbelianGroupOn.Read(module)).At(u, v))),
									FinalLeg(
										"which is the negative of the sum of F over insert(x, t)",
										By(peel)),
								))
						}))))
		}),
})}

// ModuleSumCross — induction on the finite index set s. Over ∅ there is
// no row and no pair, and both sums are M.zero. A new index x adds its
// row, the sum over t of F(x, ·), to the sum of the rows; on the right,
// the pairs over insert(x, s) are the pairs (x, y), y in t, together with
// the pairs over s, two disjoint finite sets, and the sum over the pairs
// (x, y) is the row of x, since y ↦ (x, y) is injective and the
// projections undo the pairing.
var ModuleSumCross = moduleSumCrossThm{family.Add(registry.ProofEntry{
	Name: "ModuleSumCross",
	Key:  "prop_9f8b2d2a0e1228f5",
	Build: ModuleOn.Law(Statement{
		Binders: "∀s:set(D). ∀t:set(E). ∀F:(D → E → B).",
		Hypotheses: []string{
			"finite(s)",
			"finite(t)",
			"∀x:D. ∀y:E. x ∈ s ∧ y ∈ t ⇒ F(x, y) ∈ M.carrier",
		},
		Conclusion: "module_sum(M.add, M.zero, s, λx:D. module_sum(M.add, M.zero, t, λy:E. F(x, y))) = " +
			"module_sum(M.add, M.zero, set_cross(s, t), λp:prod(D, E). F(fst(p), snd(p)))",
	},
		func(
			a *Argument,
			module ModuleFact[on.R, on.M],
			s *Expr[Set[D]],
			t *Expr[Set[E]],
			_ *Arrow2[D, E, B],
			hypotheses Fact,
		) {
			parts := a.Conjuncts(
				hypotheses,
				"s is finite",
				"t is finite",
				"F lies in M on s × t")
			finS, finT, onST := parts[0], parts[1], parts[2]
			summand := a.TermAs[Fun[Prod[D, E], B]]("λp:prod(D, E). F(fst(p), snd(p))")
			projectFirst := pairs.Fst.Inst(TypeBinder.BindA[D](), TypeBinder.BindB[E]())
			projectSecond := pairs.Snd.Inst(TypeBinder.BindA[D](), TypeBinder.BindB[E]())
			crossSums := a.TermAs[Set[Set[D]]](
				"λr:set(D). " +
					"    module_sum(M.add, M.zero, r, λx:D. module_sum(M.add, M.zero, t, λy:E. F(x, y))) = " +
					"    module_sum(M.add, M.zero, set_cross(r, t), λp:prod(D, E). F(fst(p), snd(p)))")
			rowInM := a.TermAs[Set[D]]("λx:D. ∀y:E. y ∈ t ⇒ F(x, y) ∈ M.carrier")
			a.Show(
				"the induction carries the equation to every finite index set whose rows lie in M, s among them",
				ByInduction(finite_set.FiniteInductFreshOn.At(crossSums, rowInM, s), finS, onST,
					Case(
						"over ∅ there is no row and no pair, and both sums are M.zero",
						Derive(func(b *Argument) {
							emptyCross := b.Have(
								"no pair has its first component in ∅",
								"set_cross(∅⟨A:D⟩, t) = ∅",
								BySets(set_product.CrossEmptyIff.At(b.TermAs[Set[D]]("∅⟨A:D⟩"), t)))
							b.Show(
								"both sums are over ∅",
								By(emptyCross, ModuleSumEmpty))
						})),
					Case(
						"one more index x adds its row on the left and the pairs (x, y), y in t, on the right",
						Derive(func(b *Argument) {
							x := b.FixAs[D]()
							r := b.FixAs[Set[D]]("r")
							carried := b.Conjuncts(
								b.Assume(),
								"the equation over r",
								"x is a new index of r",
								"r is finite",
								"F(x, y) lies in M for every y in t",
								"F lies in M on r × t")
							claimR, notIn, finR, onRow, onR := carried[0], carried[1], carried[2], carried[3], carried[4]
							row := b.TermAs[Fun[E, B]]("λy:E. F(x, y)")
							rows := b.TermAs[Fun[D, B]]("λz:D. module_sum(M.add, M.zero, t, λy:E. F(z, y))")
							rowIn := b.Have(
								"so the row of x, a finite sum of members of M, lies in M",
								"module_sum(M.add, M.zero, t, λy:E. F(x, y)) ∈ M.carrier",
								By(finT, onRow, ModuleSumIn.Read(module).At(t, row)))
							rowsIn := b.Have(
								"and so does the row of every index of r",
								"∀z:D. z ∈ r ⇒ module_sum(M.add, M.zero, t, λy:E. F(z, y)) ∈ M.carrier",
								By(finT, onR, ModuleSumIn.Read(module)))
							pairing := b.TermAs[Fun[E, Prod[D, E]]]("λy:E. (x, y)")
							pairsAtX := b.TermAs[Set[Prod[D, E]]]("image(λy:E. (x, y), t)")
							pairsOverR := b.TermAs[Set[Prod[D, E]]]("set_cross(r, t)")
							split := b.Have(
								"a pair over insert(x, r) has first component x or one in r",
								"set_cross(insert(x, r), t) = image(λy:E. (x, y), t) ∪ set_cross(r, t)",
								Unfold(set_product.SetCrossDef),
								BySets())
							disjoint := b.Have(
								"x is not in r, so no pair (x, y) lies over r",
								"disjoint(image(λy:E. (x, y), t), set_cross(r, t))",
								BySets(notIn, set_product.InCross))
							finAtX := b.Have(
								"the pairs (x, y), y in t, are finitely many",
								"finite(image(λy:E. (x, y), t))",
								By(finT, finite_set.FiniteImage.At(pairing, t)))
							finOverR := b.Have(
								"and so are the pairs over r",
								"finite(set_cross(r, t))",
								By(finR, finT, finite_set.FiniteProduct.At(r, t)))
							onParts := b.Have(
								"both parts lie in insert(x, r) × t, where the summand lies in M",
								"∀p:prod(D, E). p ∈ image(λy:E. (x, y), t) ∨ p ∈ set_cross(r, t) ⇒ F(fst(p), snd(p)) ∈ M.carrier",
								BySets(onRow, onR, split, set_product.InCrossProjections))
							injective := b.Have(
								"y ↦ (x, y) is injective, pairs being equal componentwise",
								"injective_on(t, λy:E. (x, y))",
								Unfold(functions.InjectiveOnDef),
								b.ForEach(func(u *Expr[E]) Action {
									return b.ForEach(func(v *Expr[E]) Action { return By(pairs.PairEq.At(x, u, x, v)) })
								}))
							onImage := b.Have(
								"at the pair (x, y) the summand is F(x, y), in M for y in t",
								"∀y:E. y ∈ t ⇒ F(fst((x, y)), snd((x, y))) ∈ M.carrier",
								Simp(Fwd(projectFirst), Fwd(projectSecond)),
								By(onRow))
							imageSum := b.Have(
								"so the sum over the pairs (x, y) is the sum over t of the summand at (x, y)",
								"module_sum(M.add, M.zero, image(λy:E. (x, y), t), λp:prod(D, E). F(fst(p), snd(p))) = "+
									"module_sum(M.add, M.zero, t, λy:E. F(fst((x, y)), snd((x, y))))",
								By(finT, injective, onImage, ModuleSumImage.Read(module).At(t, pairing, summand)))
							b.Show(
								"the sum of the rows over insert(x, r) is the sum over insert(x, r) × t",
								CalcEq(
									Leg(
										b.TermAs[B](
											"module_sum(M.add, M.zero, t, λy:E. F(x, y)) + "+
												"module_sum(M.add, M.zero, r, λz:D. module_sum(M.add, M.zero, t, λy:E. F(z, y)))"),
										"x is a new index of r: its row comes off the sum of the rows",
										By(finR, notIn, rowIn, rowsIn, ModuleSumInsert.Read(module).At(r, x, rows))),
									Leg(
										b.TermAs[B](
											"module_sum(M.add, M.zero, t, λy:E. F(x, y)) + "+
												"module_sum(M.add, M.zero, set_cross(r, t), λp:prod(D, E). F(fst(p), snd(p)))"),
										"the equation carried to r",
										By(claimR)),
									Leg(
										b.TermAs[B](
											"module_sum(M.add, M.zero, t, λy:E. F(fst((x, y)), snd((x, y)))) + "+
												"module_sum(M.add, M.zero, set_cross(r, t), λp:prod(D, E). F(fst(p), snd(p)))"),
										"the projections undo the pairing",
										Simp(Fwd(projectFirst), Fwd(projectSecond)),
										Basic()),
									Leg(
										b.TermAs[B](
											"module_sum(M.add, M.zero, image(λy:E. (x, y), t), λp:prod(D, E). F(fst(p), snd(p))) + "+
												"module_sum(M.add, M.zero, set_cross(r, t), λp:prod(D, E). F(fst(p), snd(p)))"),
										"the row of x is the sum over the pairs (x, y)",
										By(imageSum)),
									Leg(
										b.TermAs[B](
											"module_sum(M.add, "+
												"    M.zero, "+
												"    image(λy:E. (x, y), t) ∪ set_cross(r, t), "+
												"    λp:prod(D, E). F(fst(p), snd(p)))"),
										"the two parts are disjoint finite sets",
										By(
											finAtX,
											finOverR,
											disjoint,
											onParts,
											ModuleSumDisjointUnion.Read(module).At(pairsAtX, pairsOverR, summand))),
									FinalLeg(
										"together they are the pairs over insert(x, r)",
										By(split)),
								))
						}))))
		}),
})}

// ModuleSumSupportMonoid — a fold over a finite set does not see the indices
// where its term is the identity: over a commutative monoid on c, one such
// index at a time joins the part t, each combining e with the fold before it.
var ModuleSumSupportMonoid = moduleSumSupportMonoidThm{family.Add(registry.ProofEntry{
	Name: "ModuleSumSupportMonoid",
	Key:  "prop_57478d8ea0c0e8fa",
	Build: comm_monoid.CommMonoidOn.Law(Statement{
		Binders: "∀s t:set(D). ∀F:(D → A).",
		Hypotheses: []string{
			"finite(s)",
			"t ⊆ s",
			"∀x:D. x ∈ s ⇒ F(x) ∈ c",
			"∀x:D. x ∈ s ∧ x ∉ t ⇒ F(x) = e",
		},
		Conclusion: "module_sum(op, e, s, F) = module_sum(op, e, t, F)",
	},
		func(
			a *Argument,
			monoid comm_monoid.CommMonoidFact[on.C],
			s, t *Expr[Set[D]],
			F *Arrow[D, A],
			hypotheses Fact,
		) {
			parts := a.Conjuncts(
				hypotheses,
				"s is finite",
				"t is a part of s",
				"F lies in c on s",
				"F is e on s off t")
			finS, tSub, onS, offT := parts[0], parts[1], parts[2], parts[3]
			finT := a.Have(
				"t, a part of a finite set, is finite",
				"finite(t)",
				By(finS, tSub, finite_set.FiniteSubset.At(t, s)))
			onT := a.Have(
				"F lies in c on t",
				"∀x:D. x ∈ t ⇒ F(x) ∈ c",
				a.ForEach(func(x *Expr[D]) Action { return BySets(tSub, onS.At(x)) }))
			foldT := a.MemberOf[on.C](a.TermAs[A]("module_sum(op, e, t, F)"),
				a.Have(
					"so the fold over t lies in c",
					"module_sum(op, e, t, F) ∈ c",
					By(finT, onT, ModuleSumInMonoid.Read(monoid).At(t, F))))
			rest := a.Have(
				"the rest of s is finite, and each of its indices lies off t with term e, a member of c",
				"finite(s ∖ t) ∧ (∀x:D. x ∈ s ∖ t ⇒ x ∉ t ∧ F(x) ∈ c ∧ F(x) = e)",
				By(finS, onS, offT, finite_set.FiniteDiff.At(s, t), set_basic.InDiff))
			enlarged := a.Have(
				"joining the rest of s to t leaves the fold unchanged",
				"module_sum(op, e, (s ∖ t) ∪ t, F) = module_sum(op, e, t, F)",
				ByInduction(
					finite_set.FiniteInductFreshOn.At(
						a.TermAs[Set[Set[D]]]("λu:set(D). module_sum(op, e, u ∪ t, F) = module_sum(op, e, t, F)"),
						a.TermAs[Set[D]]("λx:D. x ∉ t ∧ F(x) ∈ c ∧ F(x) = e"),
						a.TermAs[Set[D]]("s ∖ t")),
					rest,
					Case(
						"joining nothing changes nothing",
						Simp(Fwd(set_algebra.UnionEmpty)),
						Refl()),
					Case(
						"one more index contributes e in front of the fold before it",
						Derive(func(b *Argument) {
							x := b.FixAs[D]("x")
							u := b.FixAs[Set[D]]("u")
							carried := b.Conjuncts(
								b.Assume(),
								"joining u leaves the fold unchanged",
								"x is a new index of u",
								"u is finite",
								"x lies off t",
								"F(x) lies in c",
								"F(x) is e",
								"the indices of u lie off t with term e")
							ih, notInU, finU, offTx, fxIn, fxUnit, onU :=
								carried[0], carried[1], carried[2], carried[3], carried[4], carried[5], carried[6]
							joined := b.TermAs[Set[D]]("u ∪ t")
							finJoined := b.Have(
								"u ∪ t is finite",
								"finite(u ∪ t)",
								By(finU, finT, finite_set.FiniteUnion.At(u, t)))
							notInJoined := b.Have(
								"x is a new index of u ∪ t",
								"x ∉ u ∪ t",
								BySets(notInU, offTx))
							onJoined := b.Have(
								"F lies in c on u ∪ t",
								"∀y:D. y ∈ u ∪ t ⇒ F(y) ∈ c",
								b.ForEach(func(y *Expr[D]) Action {
									return BySets(onT.At(y), onU.At(y))
								}))
							b.Show(
								"the fold over insert(x, u ∪ t) puts e in front of the fold over t",
								Simp(Rev(set_algebra.InsertUnionEq)),
								By(
									ih,
									fxUnit,
									fxIn,
									finJoined,
									notInJoined,
									onJoined,
									ModuleSumInsertMonoid.Read(monoid).At(joined, x, F),
									comm_monoid.LeftIdentityOn.Read(monoid).At(foldT)))
						}))))
			split := a.Have(
				"s is the rest of s together with t",
				"s = (s ∖ t) ∪ t",
				BySets(tSub))
			a.Show(
				"the fold over s is the fold over t",
				CalcEq(
					Leg(
						a.TermAs[A]("module_sum(op, e, (s ∖ t) ∪ t, F)"),
						"s is the rest of s together with t",
						By(Normalized, split)),
					FinalLeg(
						"and joining that rest changes nothing",
						By(enlarged))))
		}),
})}

// ModuleSumSingleMonoid — a fold over a part t of {x} is F(x), when F(x) is e
// should x lie off t: the fold over t is the fold over {x}, one term before
// the empty fold.
var ModuleSumSingleMonoid = moduleSumSingleMonoidThm{family.Add(registry.ProofEntry{
	Name: "ModuleSumSingleMonoid",
	Key:  "prop_388c00e860c34814",
	Build: comm_monoid.CommMonoidOn.Law(Statement{
		Binders: "∀t:set(D). ∀x:D. ∀F:(D → A).",
		Hypotheses: []string{
			"t ⊆ {x}",
			"F(x) ∈ c",
			"x ∉ t ⇒ F(x) = e",
		},
		Conclusion: "module_sum(op, e, t, F) = F(x)",
	},
		func(
			a *Argument,
			monoid comm_monoid.CommMonoidFact[on.C],
			t *Expr[Set[D]],
			x *Expr[D],
			F *Arrow[D, A],
			hypotheses Fact,
		) {
			parts := a.Conjuncts(
				hypotheses,
				"t is a part of {x}",
				"F(x) lies in c",
				"F(x) is e should x lie off t")
			tSub, inC, offT := parts[0], parts[1], parts[2]
			single := a.TermAs[Set[D]]("{x}")
			onSingle := a.Have(
				"F lies in c on {x}",
				"∀y:D. y ∈ {x} ⇒ F(y) ∈ c",
				a.ForEach(func(y *Expr[D]) Action {
					return By(Normalized, inC, set_basic.InSing.At(y, x))
				}))
			offPart := a.Have(
				"and is e on {x} off t",
				"∀y:D. y ∈ {x} ∧ y ∉ t ⇒ F(y) = e",
				a.ForEach(func(y *Expr[D]) Action { return By(offT, set_basic.InSing.At(y, x)) }))
			emptyFinite := a.Have(
				"∅ is finite",
				"finite(∅⟨A:D⟩)",
				By(finite_set.FiniteRules))
			nothingInEmpty := a.Have(
				"and F lies in c at every index of ∅",
				"∀y:D. y ∈ ∅ ⇒ F(y) ∈ c",
				a.ForEach(func(y *Expr[D]) Action { return By(set_basic.NotInEmpty.At(y)) }))
			a.Show(
				"the fold over t is the fold over {x}, which is F(x)",
				CalcEq(
					Leg(
						a.TermAs[A]("module_sum(op, e, {x}, F)"),
						"the indices of {x} off t have term e",
						By(
							finite_set.FiniteSing.At(x),
							tSub,
							onSingle,
							offPart,
							ModuleSumSupportMonoid.Read(monoid).At(single, t, F))),
					Leg(
						a.TermAs[A]("op(F(x), module_sum(op, e, ∅, F))"),
						"x is a new index of the empty set",
						By(
							emptyFinite,
							inC,
							nothingInEmpty,
							set_basic.NotInEmpty.At(x),
							ModuleSumInsertMonoid.Read(monoid).At(a.TermAs[Set[D]]("∅"), x, F))),
					Leg(
						a.TermAs[A]("op(F(x), e)"),
						"the empty fold is e",
						By(ModuleSumEmpty)),
					FinalLeg(
						"e is the unit",
						By(inC, comm_monoid.RightIdentityOn.Read(monoid).AsFact().At(F.Apply(x))))))
		}),
})}

// SupportSumAdditive — a sum over the support of a divisor, each point
// reading its coefficient through a map that carries add to the monoid's
// operation, is additive in the divisor: all three sums run over one
// finite set holding the supports, where the terms split. The
// coefficients ask for no structure beyond zero added to itself being
// zero, which puts the support of the sum inside that set; a divisor's
// integers under addition are the instance.
var SupportSumAdditive = supportSumAdditiveThm{family.Add(registry.ProofEntry{
	Name: "SupportSumAdditive",
	Key:  "prop_235b967b7fa30a79",
	Build: comm_monoid.CommMonoidOn.Law(Statement{
		Binders: "∀s:set(B). ∀add:(C → C → C). ∀zero:C. ∀D E:(B → C). ∀F:(B → C → A).",
		Hypotheses: []string{
			"add(zero, zero) = zero",
			"finite(s)",
			"∀P:B. D(P) ≠ zero ⇒ P ∈ s",
			"∀P:B. E(P) ≠ zero ⇒ P ∈ s",
			"∀P:B. " +
				"    P ∈ s ⇒ " +
				"    (∀n:C. F(P, n) ∈ c) ∧ F(P, zero) = e ∧ (∀i j:C. F(P, add(i, j)) = op(F(P, i), F(P, j)))",
		},
		Conclusion: "«supportSum»(λP:B. add(D(P), E(P))) = op(«supportSum»(D), «supportSum»(E))",
		Abbrev: Abbrev{
			{Name: "supportSum", Text: "λG:(B → C). module_sum(op, e, fun_support(zero, G), λP:B. F(P, G(P)))"},
		},
	},
		func(
			a *Argument,
			monoid comm_monoid.CommMonoidFact[on.C],
			s *Expr[Set[B]],
			add *Arrow2[C, C, C],
			zero *Expr[C],
			D, E *Arrow[B, C],
			F *Arrow2[B, C, A],
			hypotheses Fact,
		) {
			parts := a.Conjuncts(
				hypotheses,
				"zero added to zero is zero",
				"s is finite",
				"s holds the support of D",
				"s holds the support of E",
				"F carries add to op at each point of s")
			idempotent, finS, inSD, inSE, laws := parts[0], parts[1], parts[2], parts[3], parts[4]
			members := a.Have(
				"F lies in c at each point of s",
				"∀P:B. ∀n:C. P ∈ s ⇒ F(P, n) ∈ c",
				Derive(func(b *Argument) {
					P := b.FixAs[B]("P")
					b.FixAs[C]("n")
					inS := b.Assume()
					b.Show(
						"the first law at P",
						By(Normalized, inS, laws.At(P)))
				}))
			unit := a.Have(
				"F at zero is e at each point of s",
				"∀P:B. P ∈ s ⇒ F(P, zero) = e",
				Derive(func(b *Argument) {
					P := b.FixAs[B]("P")
					inS := b.Assume()
					b.Show(
						"the second law at P",
						By(inS, laws.At(P)))
				}))
			splits := a.Have(
				"F carries add to op at each point of s",
				"∀P:B. ∀i j:C. P ∈ s ⇒ F(P, add(i, j)) = op(F(P, i), F(P, j))",
				Derive(func(b *Argument) {
					P := b.FixAs[B]("P")
					b.FixAs[C]("i")
					b.FixAs[C]("j")
					inS := b.Assume()
					b.Show(
						"the third law at P",
						By(Normalized, inS, laws.At(P)))
				}))
			enlarge := a.Have(
				"a sum over a support held by s is the sum over s",
				Statement{
					Binders:    "∀G:(B → C).",
					Hypotheses: []string{"∀P:B. G(P) ≠ zero ⇒ P ∈ s"},
					Conclusion: "module_sum(op, e, s, λP:B. F(P, G(P))) = «supportSum»(G)",
				},
				Derive(func(b *Argument) {
					b.FixAs[Fun[B, C]]("G")
					inS := b.Assume()
					part := b.Have(
						"the support of G is a part of s",
						"fun_support(zero, G) ⊆ s",
						BySets(inS))
					onS := b.Have(
						"the term lies in c on s",
						"∀P:B. P ∈ s ⇒ F(P, G(P)) ∈ c",
						Derive(func(c *Argument) {
							P := c.FixAs[B]("P")
							inS := c.Assume()
							c.Show(
								"F lies in c at P",
								By(inS, members.At(P, c.TermAs[C]("G(P)"))))
						}))
					offSupport := b.Have(
						"off the support the term is F at zero, which is e",
						"∀P:B. P ∈ s ∧ P ∉ fun_support(zero, G) ⇒ F(P, G(P)) = e",
						Derive(func(c *Argument) {
							P := c.FixAs[B]("P")
							off := c.Conjuncts(
								c.Assume(),
								"P lies in s",
								"G vanishes at P")
							vanishes := c.Have(
								"G vanishes at P",
								"G(P) = zero",
								BySets(off[1]))
							c.Show(
								"F at zero is e at P",
								vanishes.Rw(),
								By(off[0], unit.At(P)))
						}))
					b.Show(
						"the sum over s drops the indices with term e",
						By(
							finS,
							part,
							onS,
							offSupport,
							At(ModuleSumSupportMonoid.Read(monoid),
								s,
								b.TermAs[Set[B]]("fun_support(zero, G)"),
								b.TermAs[Fun[B, A]]("λP:B. F(P, G(P))"))))
				}))
			inSSum := a.Have(
				"s holds the support of the sum of D and E",
				"∀P:B. add(D(P), E(P)) ≠ zero ⇒ P ∈ s",
				Derive(func(b *Argument) {
					P := b.FixAs[B]("P")
					nonzero := b.Assume()
					off := b.SupposeNot()
					b.Show(
						"off s both coefficients are zero, and zero added to zero is zero",
						By(Normalized, nonzero, off, inSD.At(P), inSE.At(P), idempotent))
				}))
			product := a.TermAs[Fun2[A, A, A]]("op")
			unitElement := a.TermAs[A]("e")
			termD := a.TermAs[Fun[B, A]]("λP:B. F(P, D(P))")
			termE := a.TermAs[Fun[B, A]]("λP:B. F(P, E(P))")
			a.Show(
				"all three sums run over s, where the terms split",
				CalcEq(
					Leg(
						a.TermAs[A]("module_sum(op, e, s, λP:B. F(P, add(D(P), E(P))))"),
						"s holds the support of the sum",
						By(inSSum, enlarge.At(a.TermAs[Fun[B, C]]("λP:B. add(D(P), E(P))")))),
					Leg(
						a.TermAs[A]("module_sum(op, e, s, λP:B. op(F(P, D(P)), F(P, E(P))))"),
						"the terms split at each point of s",
						By(
							splits,
							ModuleSumCongruence.At(
								product,
								unitElement,
								s,
								a.TermAs[Fun[B, A]]("λP:B. F(P, add(D(P), E(P)))"),
								a.TermAs[Fun[B, A]]("λP:B. op(F(P, D(P)), F(P, E(P)))")))),
					Leg(
						a.TermAs[A]("op(module_sum(op, e, s, λP:B. F(P, D(P))), module_sum(op, e, s, λP:B. F(P, E(P))))"),
						"the sum of the products is the product of the sums",
						By(finS, members, ModuleSumAddMonoid.Read(monoid).At(s, termD, termE))),
					FinalLeg(
						"each of the two is its sum over its support",
						By(inSD, inSE, enlarge.At(D), enlarge.At(E)))))
		}),
})}
